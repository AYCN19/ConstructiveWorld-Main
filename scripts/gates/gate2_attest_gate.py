#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""gate2_attest_gate.py - gate2 certification-mode branch arbiter (ATT-RECON 20261029).

Decision input: a partial log (only a subset is sent for checking in this
round) + archive-coverage assertions = green may be judged (ATTESTED_CLEAN);
missing any one assertion means red (no downgrade). FULL mode (empty skip
list) is byte-for-byte equivalent in semantics to the previous gate2: the
parser verdict is final.

Assertion set (all must hold to judge ATTESTED_CLEAN; any single breach ->
exit 1 red with reasons listed):
  R1 state consistency    mode==ATTESTED iff the log appendix is present;
                mode==FULL iff the appendix is absent
                (an appendix without reconciliation backing = broken evidence
                chain, red; skips present but no appendix = equally red).
  R2 appendix=list    the appendix ATTEST-SKIP entry set == the reconciliation
                step's skipped set, and the count line == the set size.
  R3 archive fingerprint    the appendix ATTEST-ARCHIVE == the reconciliation
                step's archive_tree_sha256 (a green verdict is bound to the
                archive identity).
  R4 coverage partition    skipped union sent_to_chk == cert_surface with an
                empty intersection (self-consistent inside the reconciliation
                report, and doubly guarded by parallel_chk's union assertion /
                the PCHK-SKIP-UNKNOWN guard).
  R5 archive validity    the reconciliation step's archive_valid=true (contract
                structure + tree_sha256 self-consistency already passed).
  R6 parse verdict    gate2_axioms_parser verdict CLEAN (empty axioms + non-empty
                sections + complete log tail line - this arbiter re-derives the
                same verdict from the parser JSON; parser codes 1/2/3 are
                unrecoverable and always red).
  R7 banner generation pin    the banner Chicken 9.1.0 is guarded by a grep that
                runs before this step in the yml (this arbiter does not
                re-check; on record).

Exit codes: 0 = green (CLEAN / ATTESTED_CLEAN, see gate2_attest.json verdict);
1 = red (reasons lists the broken assertions).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

GATE_SCHEMA = "cw.gate2att/v1"

APPENDIX_BEGIN = "=== ATTEST-SKIP APPENDIX BEGIN"
APPENDIX_END = "=== ATTEST-SKIP APPENDIX END"


def parse_appendix(log_path: Path) -> dict:
    """Extract the certification appendix from _chk_all.log. Returns {present, count, archive, modules}."""
    out = {"present": False, "count": None, "archive": None, "modules": []}
    try:
        lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return out
    inside = False
    for line in lines:
        if APPENDIX_BEGIN in line:
            inside = True
            out["present"] = True
            out["modules"] = []
            continue
        if APPENDIX_END in line:
            inside = False
            continue
        if inside and line.startswith("ATTEST-SKIP-COUNT "):
            try:
                out["count"] = int(line.split(None, 1)[1])
            except (IndexError, ValueError):
                out["count"] = None
        elif inside and line.startswith("ATTEST-ARCHIVE "):
            out["archive"] = line.split(None, 1)[1].strip()
        elif inside and line.startswith("ATTEST-SKIP "):
            out["modules"].append(line.split(None, 1)[1].strip())
    return out


def parser_verdict(parser_json_path: Path) -> tuple[int, dict]:
    """Re-derive the verdict from gate2_axioms_parser's JSON output (same
    criteria as its verdict()).

    Returns (code, {complete, sections, axioms}); code in {0,1,2,3};
    missing/broken JSON -> (2, {unparseable: true}) (= the NO_AXIOMS level;
    undecidable means red).
    """
    try:
        docs = json.loads(parser_json_path.read_text(encoding="utf-8"))
        if not isinstance(docs, list) or not docs:
            raise ValueError("parser json 非非空数组")
        d = docs[0]  # single-log scope (the yml feeds only _chk_all.log)
        sections = d.get("sections")
        complete = bool(d.get("complete"))
        axioms = d.get("axioms")
        if not isinstance(sections, list) or not isinstance(axioms, list):
            raise ValueError("parser json 字段形不符")
    except (OSError, ValueError, json.JSONDecodeError):
        return 2, {"unparseable": True}
    code = 2
    if sections:
        code = 3
        if complete:
            code = 1
            if not axioms:
                code = 0
    return code, {
        "complete": complete if sections else None,
        "sections": len(sections) if isinstance(sections, list) else None,
        "axioms": len(axioms) if isinstance(axioms, list) else None,
    }


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="gate2 认证态分支裁定（部分日志+覆盖断言）")
    ap.add_argument("--log", type=Path, required=True)
    ap.add_argument("--parser-json", type=Path, required=True)
    ap.add_argument("--reconcile-json", type=Path, required=True)
    ap.add_argument("--json", dest="jsonout", type=Path, required=True)
    args = ap.parse_args()

    reasons: list[str] = []
    try:
        recon = json.loads(args.reconcile_json.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        recon = None
        reasons.append(f"对账报告不可读（证据链断）: {exc}")

    mode = (recon or {}).get("mode", "FULL")
    skipped = set((recon or {}).get("skipped") or [])
    surface = set((recon or {}).get("cert_surface") or [])
    sent = set((recon or {}).get("sent_to_chk") or [])
    arch_sha = (recon or {}).get("archive_tree_sha256")
    arch_valid = bool((recon or {}).get("archive_valid"))
    pcode, pinfo = parser_verdict(args.parser_json)
    appendix = parse_appendix(args.log)

    # R4 coverage partition (self-consistency of the reconciliation report)
    partition_ok = (
        bool(surface)
        and skipped <= surface
        and sent == surface - skipped
        and not (skipped & sent)
    )
    if recon is not None and not partition_ok:
        reasons.append("R4 覆盖划分破: skipped∪sent != surface 或交集非空或面空")

    if mode == "FULL":
        # Legacy semantics: the parser verdict is final; an appendix present = forged evidence without reconciliation backing, red.
        if appendix["present"]:
            reasons.append("R1 状态一致破: FULL 模式下日志含认证附页（无对账背书）")
        green = (pcode == 0) and not reasons
        verdict = "CLEAN" if green else "RED"
    else:
        # Certification mode (ATTESTED): ATTESTED_CLEAN requires all of R1-R6 to hold.
        if not appendix["present"]:
            reasons.append("R1 状态一致破: ATTESTED 模式下日志无认证附页（证据链断）")
        appendix_set = set(appendix["modules"])
        if appendix_set != skipped:
            reasons.append(
                f"R2 附页=清单破: 附页 {len(appendix_set)} 项 vs 对账 skipped {len(skipped)} 项"
                f"（差集样本 {sorted(appendix_set ^ skipped)[:5]}）"
            )
        if appendix["count"] != len(appendix_set) or appendix["count"] is None:
            reasons.append("R2 计数行不符: ATTEST-SKIP-COUNT != 附页集合大小")
        if appendix["archive"] != arch_sha:
            reasons.append(f"R3 档案指纹不符: 附页 {appendix['archive']} vs 对账 {arch_sha}")
        if not arch_valid:
            reasons.append("R5 档案无效: 对账步 archive_valid=false（坏档/自洽破）")
        if pcode != 0:
            reasons.append(f"R6 解析判定非 CLEAN: parser code={pcode} {pinfo}")
        green = not reasons
        verdict = "ATTESTED_CLEAN" if green else "RED"

    doc = {
        "schema": GATE_SCHEMA,
        "mode": mode,
        "verdict": verdict,
        "green": green,
        "parser_code": pcode,
        "parser_info": pinfo,
        "appendix": {
            "present": appendix["present"],
            "count": appendix["count"],
            "archive": appendix["archive"],
            "modules_n": len(appendix["modules"]),
        },
        "reconcile": {
            "mode": mode,
            "archive_valid": arch_valid,
            "archive_tree_sha256": arch_sha,
            "surface_n": len(surface),
            "skipped_n": len(skipped),
            "sent_to_chk_n": len(sent),
            "partition_ok": partition_ok,
        },
        "reasons": reasons,
    }
    args.jsonout.write_text(
        json.dumps(doc, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"[gate2-attest] mode={mode} verdict={verdict} parser_code={pcode}")
    for r in reasons:
        print(f"  !! {r}")
    return 0 if green else 1


if __name__ == "__main__":
    sys.exit(main())
