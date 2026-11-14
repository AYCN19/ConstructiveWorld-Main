#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""rocqwash_triage.py - Main CI furnace red triage via the local rocqwash MCP
server (workflow rocqwash-triage.yml companion driver, 20261114).

Purpose.  When the Main CI 9.3 furnace goes red, this driver speaks MCP over
stdio to the resident rocqwash MCP server and asks it to triage the failed
run, then records the verdict in the rocqwash experience ledger.  It writes
three artifact files for upload and optionally mirrors them into the desk
inbox directory on this machine (the runner is the desk machine itself).

MCP conversation (newline-delimited JSON-RPC 2.0):
    initialize -> notifications/initialized
    tools/call ci_triage   {repo, run}          -> triage report text
    tools/call exp_append  {tool, points, ...}  -> ledger entry id text

The ci_triage tool fetches the failed run's job logs itself (read-only GET,
token from the machine ~/.netrc github.com line).  It is net-gated at the
tool level, so the server is launched with ROCQWASH_MCP_ALLOW_NET=1, the
same wiring as the user-level MCP config.

Verdict handling.  A red verdict is data, not a tool failure: the driver
exits 0 whenever a triage report was obtained.  Non-zero exits mean the
watch leg itself is broken (wiring, protocol, or the triage tool returned
a failed result) so the job shows red and the desk sees it.

Exit codes.  0 = triage report obtained; 2 = MCP wiring or protocol
failure; 3 = triage tool returned a failed result; 4 = usage error.

Config surface (env overrides, defaults mirror the user-level MCP config):
    ROCQWASH_HOME        root handed to the server (default D:/ComplexAnalysis/rocqwash)
    ROCQWASH_PYTHON      interpreter for the server (default C:\\Program Files\\Python313\\python.exe)
    ROCQWASH_SERVER      server script path (default <HOME>/tools/mcp_server.py)
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import queue
import urllib.error
import urllib.request

SCHEMA = "rocqwash-watch/1"

DEFAULT_HOME = r"D:/ComplexAnalysis/rocqwash"
DEFAULT_PYTHON = r"C:\Program Files\Python313\python.exe"
DEFAULT_MIRROR = r"D:/ComplexAnalysis/ConstructiveWorld-Main"

INIT_RESULT_ID = 1
TRIAGE_RESULT_ID = 2
LEDGER_RESULT_ID = 3
HEAL_LEDGER_RESULT_ID = 4

VERDICT_RE = re.compile(r"RUN VERDICT: family=(\S+) .*? action=(\S+)")

# Families the heal leg may act on: rerun-safe transient classes only.
# Content reds (family A) and toolchain breaks stay human-gated.
HEAL_ACTIONS = {"rerun-after-stable-window"}
HEAL_FAMILIES = {"runner-lost", "E-runner-lost"}
HEAL_BUDGET_PER_RUN = 1


def log(msg):
    sys.stdout.write("[triage] %s\n" % msg)
    sys.stdout.flush()


class McpClient(object):
    """Minimal newline-delimited JSON-RPC 2.0 client over stdin/stdout."""

    def __init__(self, python_exe, server_script, home, timeout_s):
        env = dict(os.environ)
        env["ROCQWASH_HOME"] = home
        env["ROCQWASH_MCP_ALLOW_NET"] = "1"
        env.setdefault("PYTHONIOENCODING", "utf-8")
        self.proc = subprocess.Popen(
            [python_exe, "-I", server_script],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
        self.timeout_s = timeout_s
        self.deadline = time.time() + timeout_s
        self.lines = queue.Queue()
        self.stderr_chunks = []
        self._reader = threading.Thread(target=self._pump, daemon=True)
        self._reader.start()
        self._errpump = threading.Thread(target=self._pump_err, daemon=True)
        self._errpump.start()
        self._next_id = 0

    def _pump(self):
        for raw in self.proc.stdout:
            self.lines.put(raw.decode("utf-8", errors="replace").strip())

    def _pump_err(self):
        for raw in self.proc.stderr:
            self.stderr_chunks.append(raw.decode("utf-8", errors="replace"))

    def _send(self, obj):
        self.proc.stdin.write((json.dumps(obj) + "\n").encode("utf-8"))
        self.proc.stdin.flush()

    def request(self, method, params, result_id):
        self._send({"jsonrpc": "2.0", "id": result_id, "method": method,
                    "params": params})
        while True:
            remaining = self.deadline - time.time()
            if remaining <= 0:
                raise RuntimeError("MCP deadline exceeded (%ds)" % self.timeout_s)
            try:
                line = self.lines.get(timeout=remaining)
            except queue.Empty:
                raise RuntimeError("MCP deadline exceeded while waiting for id=%d" % result_id)
            if not line:
                continue
            try:
                msg = json.loads(line)
            except ValueError:
                continue  # not a JSON line; skip
            if msg.get("id") != result_id:
                continue  # not our response
            if "error" in msg:
                raise RuntimeError("MCP error for %s: %s" % (method, msg["error"]))
            return msg.get("result") or {}

    def notify(self, method):
        self._send({"jsonrpc": "2.0", "method": method})

    def close(self):
        try:
            self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=15)
        except Exception:
            self.proc.kill()

    def stderr_text(self):
        return "".join(self.stderr_chunks)


def call_tool(client, name, arguments, result_id):
    result = client.request("tools/call",
                            {"name": name, "arguments": arguments}, result_id)
    is_error = bool(result.get("isError"))
    parts = []
    for item in result.get("content") or []:
        if isinstance(item, dict) and item.get("type") == "text":
            parts.append(item.get("text") or "")
    return is_error, "\n".join(parts)


def write_artifacts(out_dir, files):
    os.makedirs(out_dir, exist_ok=True)
    for name, text in files:
        with open(os.path.join(out_dir, name), "w", encoding="utf-8",
                  newline="\n") as fh:
            fh.write(text)


def git_out(mirror, argv, timeout=120):
    return subprocess.run(
        ["git", "-C", mirror, "-c", "gc.auto=0"] + argv,
        capture_output=True, text=True, timeout=timeout)


def mirror_ff_sync(mirror):
    """Fast-forward the bridge mirror main to origin/main, guarded.

    The 20261114 run #69 checkout red: another seat pushed to the real shore
    and the mirror synced ~3 minutes later - the furnace checkout raced the
    sync window ("not our ref").  Guards: clean tree only, strictly
    fast-forward only, fail-soft verdict string either way.
    """
    if not os.path.isdir(mirror):
        return "no-mirror:" + mirror
    if not os.path.isdir(os.path.join(mirror, ".git")):
        return "not-a-worktree:" + mirror
    st = git_out(mirror, ["status", "--porcelain"])
    if st.returncode != 0:
        return "status-failed"
    if st.stdout.strip():
        return "dirty-tree"
    f = git_out(mirror, ["fetch", "--no-tags", "origin", "main"])
    if f.returncode != 0:
        return "fetch-failed"
    cur = git_out(mirror, ["rev-parse", "refs/heads/main"])
    new = git_out(mirror, ["rev-parse", "refs/remotes/origin/main"])
    if cur.returncode != 0 or new.returncode != 0:
        return "revparse-failed"
    if cur.stdout.strip() == new.stdout.strip():
        return "up-to-date"
    anc = git_out(mirror, ["merge-base", "--is-ancestor",
                           "refs/heads/main", "refs/remotes/origin/main"])
    if anc.returncode != 0:
        return "not-fast-forward"
    m = git_out(mirror, ["merge", "--ff-only", "refs/remotes/origin/main"])
    if m.returncode != 0:
        return "merge-failed"
    return "ff->" + new.stdout.strip()[:7]


def heal_state_load(state_dir):
    path = os.path.join(state_dir, "heal_state.json")
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh), path
    except Exception:
        return {}, path


def heal_state_bump(path, state, run_id):
    state[str(run_id)] = state.get(str(run_id), 0) + 1
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(state, fh, sort_keys=True)
    os.replace(tmp, path)


def try_heal(args, family, action, run_id, repo):
    """Auto-heal leg: mirror sync + rerun-failed-jobs for rerun-safe reds.

    Best effort and budget-capped; every outcome lands in the returned
    verdict string and the artifacts, so a silent heal is impossible.
    Returns (verdict, detail) - verdict for the summary line, detail for
    the heal-note artifact and the ledger entry.
    """
    if not args.heal:
        return "skipped(disabled)", "heal leg disabled (no --heal)"
    if action not in HEAL_ACTIONS and family not in HEAL_FAMILIES:
        return ("skipped(family-not-healable)",
                "family=%s action=%s not in heal whitelist %s / %s"
                % (family, action, sorted(HEAL_ACTIONS), sorted(HEAL_FAMILIES)))
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        return "skipped(no-token)", "GITHUB_TOKEN absent (local run?)"
    state_dir = args.state_dir or args.inbox
    if not state_dir:
        return "skipped(no-state-dir)", "no state dir for heal budget"
    os.makedirs(state_dir, exist_ok=True)
    state, path = heal_state_load(state_dir)
    used = int(state.get(str(run_id), 0))
    if used >= HEAL_BUDGET_PER_RUN:
        return ("skipped(budget)",
                "heal budget %d already used for run %d"
                % (used, run_id))

    log("heal: stable-window delay %ds before rerun" % args.heal_delay)
    time.sleep(args.heal_delay)

    sync = mirror_ff_sync(args.mirror)
    log("heal: mirror=%s" % sync)
    if sync.startswith(("no-mirror", "not-a-worktree", "status-failed",
                        "dirty-tree", "fetch-failed", "revparse-failed",
                        "not-fast-forward", "merge-failed")):
        return "skipped(mirror-sync:" + sync + ")", "mirror sync failed: " + sync

    url = ("https://api.github.com/repos/%s/actions/runs/%d/rerun-failed-jobs"
           % (repo, run_id))
    req = urllib.request.Request(url, method="POST", data=b"", headers={
        "Authorization": "Bearer " + token,
        "Accept": "application/vnd.github+json",
        "User-Agent": "rocqwash-triage-watch",
    })
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            code = resp.status
    except urllib.error.HTTPError as exc:
        code = exc.code
        detail = "heal rerun HTTP %d: %s" % (code, exc.reason)
        return "refused(http-%d)" % code, detail
    except Exception as exc:
        return "failed(exception)", "heal rerun error: %r" % exc

    try:
        heal_state_bump(path, state, run_id)
    except Exception as exc:
        log("heal: state bump failed: %r" % exc)
    detail = ("heal rerun dispatched: HTTP %d, mirror=%s, budget now %d/%d "
              "for run %d" % (code, sync,
                              used + 1, HEAL_BUDGET_PER_RUN, run_id))
    return "dispatched(http-%d)" % code, detail


def main():
    ap = argparse.ArgumentParser(description="rocqwash MCP triage driver")
    ap.add_argument("--repo", required=True, help="ORG/REPO slug")
    ap.add_argument("--run", required=True, type=int, help="CI run id")
    ap.add_argument("--out", required=True, help="artifact output directory")
    ap.add_argument("--inbox", default=None,
                    help="optional desk inbox directory to mirror artifacts into")
    ap.add_argument("--batch", default="main-ci93-watch",
                    help="experience ledger batch label")
    ap.add_argument("--heal", action="store_true",
                    help="enable the auto-heal leg (mirror sync + rerun for "
                         "rerun-safe families)")
    ap.add_argument("--heal-delay", type=int, default=90,
                    help="stable-window seconds to wait before a heal rerun")
    ap.add_argument("--mirror", default=DEFAULT_MIRROR,
                    help="bridge mirror worktree path for the heal sync")
    ap.add_argument("--state-dir", default=None,
                    help="heal budget state dir (defaults to the inbox dir)")
    ap.add_argument("--timeout", type=int, default=900,
                    help="whole MCP conversation deadline in seconds")
    args = ap.parse_args()

    home = os.environ.get("ROCQWASH_HOME", DEFAULT_HOME)
    python_exe = os.environ.get("ROCQWASH_PYTHON", DEFAULT_PYTHON)
    server = os.environ.get("ROCQWASH_SERVER",
                            os.path.join(home, "tools", "mcp_server.py"))
    if not os.path.isfile(server):
        sys.stderr.write("server script missing: %s\n" % server)
        return 2

    client = McpClient(python_exe, server, home, args.timeout)
    try:
        client.request("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "rocqwash-triage-watch", "version": "1"},
        }, INIT_RESULT_ID)
        client.notify("notifications/initialized")

        err, report = call_tool(client, "ci_triage",
                                {"repo": args.repo, "run": args.run},
                                TRIAGE_RESULT_ID)
        if err:
            write_artifacts(args.out, [
                ("triage-report.txt", report or "(empty failed result)"),
                ("triage-summary.txt",
                 "verdict=TOOL-FAILED run=%d repo=%s" % (args.run, args.repo)),
                ("server-stderr.log", client.stderr_text()),
            ])
            sys.stderr.write("ci_triage returned a failed result:\n%s\n"
                             % (report or "(no text)"))
            return 3

        m = VERDICT_RE.search(report)
        family, action = (m.group(1), m.group(2)) if m else ("unknown", "unknown")

        try:
            heal_verdict, heal_detail = try_heal(args, family, action,
                                                 args.run, args.repo)
        except Exception as exc:  # heal must never mask the triage verdict
            heal_verdict, heal_detail = "failed(exception)", repr(exc)
        log("heal: %s" % heal_verdict)

        points = ("Main CI 9.3 red run %d: family=%s action=%s (auto triage "
                  "by rocqwash-triage workflow)" % (args.run, family, action))
        evidence = "https://github.com/%s/actions/runs/%d" % (args.repo, args.run)
        lerr, ledger = call_tool(client, "exp_append",
                                 {"tool": "ci_triage", "points": points,
                                  "evidence": evidence, "batch": args.batch},
                                 LEDGER_RESULT_ID)
        if heal_verdict.startswith(("dispatched", "refused", "failed")):
            herr, hledger = call_tool(
                client, "exp_append",
                {"tool": "watch-heal",
                 "points": "run %d heal=%s: %s" % (args.run, heal_verdict,
                                                   heal_detail),
                 "evidence": evidence, "batch": args.batch},
                HEAL_LEDGER_RESULT_ID)
        else:
            herr, hledger = False, "heal not attempted: " + heal_verdict
    finally:
        client.close()

    files = [
        ("triage-report.txt", report),
        ("ledger-entry.txt",
         ("failed result:\n%s" % ledger) if lerr else ledger),
        ("heal-note.txt", heal_verdict + "\n" + heal_detail + "\n"
         + (("failed result:\n%s" % hledger) if herr else hledger)),
        ("triage-summary.txt",
         "verdict=OBTAINED run=%d repo=%s family=%s action=%s heal=%s"
         % (args.run, args.repo, family, action, heal_verdict)),
        ("server-stderr.log", client.stderr_text()),
    ]
    write_artifacts(args.out, files)

    if args.inbox:
        inbox_run = os.path.join(args.inbox, "run%d" % args.run)
        write_artifacts(inbox_run, files)

    log("run=%d family=%s action=%s heal=%s artifacts=%s%s"
        % (args.run, family, action, heal_verdict, args.out,
           (" inbox=%s" % args.inbox) if args.inbox else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
