#!/usr/bin/env python3
"""y_sort_closure.py deps.mk order.txt -- topologically sort a coqdep makefile.

Basenames both targets and deps (the -Q roots are flat logical namespaces), merges
rules per basename, DFS with cycle tolerance, deps-before-targets order.
"""
import os
import re
import sys


def main(deps_path, out_path):
    deps = {}
    for line in open(deps_path, encoding="utf-8", errors="replace"):
        m = re.match(r"(.+?)\s*:\s*(.*)", line)
        if not m:
            continue
        tgt = os.path.basename(m.group(1).strip())
        dv = [os.path.basename(x) for x in m.group(2).split() if x.endswith(".v")]
        deps.setdefault(tgt, [])
        deps[tgt].extend(dv)

    order, done = [], set()

    def visit(n, chain):
        if n in done or n not in deps:
            return
        if n in chain:
            return
        chain.add(n)
        for d in deps[n]:
            visit(d, chain)
        chain.discard(n)
        done.add(n)
        order.append(n)

    for n in list(deps):
        visit(n, set())

    open(out_path, "w").write("\n".join(order))
    print("[sort] closure size:", len(order))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
