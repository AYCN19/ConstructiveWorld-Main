#!/usr/bin/env python3
"""y_sort_closure.py deps.mk order.txt -- topological sort of Rocq 9.3 coqdep output.

Rocq 9.3 coqdep emits multi-target makefile lines:

  X.vo X.glob X.v.beautified X.required_vo: X.v ../root/A.vo ./B.vo D\\:...junk

so this parser: splits targets on whitespace and derives each target's source
(.vo -> .v; .v.beautified -> .v; .glob/.required_vo -> skip), converts .vo deps
to their .v sources, drops junk tokens, merges rules per source basename, and
DFS-sorts deps-before-targets with cycle tolerance. Live-relative dep paths
(../) are preserved verbatim so the build loop can find them; node-local stems
are emitted as bare basenames for the loop's cwd fallback.
"""
import os
import sys


def source_of(token):
    if token.endswith(".v.beautified"):
        return token[: -len(".beautified")]
    if token.endswith(".vo"):
        return token[:-3] + ".v"
    if token.endswith(".v"):
        return token
    return None  # .glob / .required_vo / junk (rocqworker etc.)


def main(deps_path, out_path):
    rules = {}  # source path -> set of dep source paths
    for line in open(deps_path, encoding="utf-8", errors="replace"):
        if ":" not in line:
            continue
        head, tail = line.split(":", 1)
        targets = [source_of(t) for t in head.split()]
        targets = [t for t in targets if t]
        dep_srcs = []
        for t in tail.split():
            s = source_of(t)
            if s and not s.endswith("rocqworker.exe"):
                dep_srcs.append(s)
        if not targets:
            continue
        for t in targets:
            rules.setdefault(os.path.normpath(t), set())
            for d in dep_srcs:
                if os.path.normpath(d) != os.path.normpath(t):
                    rules[os.path.normpath(t)].add(os.path.normpath(d))

    order, done = [], set()

    def visit(src, chain):
        key = os.path.normpath(src).lower()
        if key in done:
            return
        if key in chain:
            return
        chain.add(key)
        for d in rules.get(os.path.normpath(src), ()):
            visit(d, chain)
        chain.discard(key)
        done.add(key)
        order.append(os.path.normpath(src))

    for src in sorted(rules):
        visit(src, set())

    open(out_path, "w", encoding="utf-8", newline="\n").write("\n".join(order))
    print("[sort] closure size:", len(order))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
