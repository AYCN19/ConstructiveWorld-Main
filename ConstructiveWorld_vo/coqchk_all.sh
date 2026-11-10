#!/bin/bash
# coqchk_all.sh — full-tree kernel certification (shared-closure version: all modules passed in one call, dependencies verified once)
# The old per-module loop was O(n^2) (each module re-verified its whole dependency closure; 99 modules = 3-8h); this version passes everything once, roughly a single full-tree run.
cd "$(dirname "$0")"
K="${COQCHK:-C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe}"
# SW2 retarget (2026-09-15): user-level COQLIB/ROCQLIB pinned to the 9.0 lib overrides the 9.1 coq_environment.txt,
# so export them derived from the K path, keeping bin/lib same-source (E-STAGING-SW2; with a foreign lib silently loaded, 9.1 coqchk reports bad version).
case "$K" in
  */bin/coqchk.exe) export COQLIB ROCQLIB; COQLIB="${K%/coqchk.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
  */bin/coqchk)     export COQLIB ROCQLIB; COQLIB="${K%/coqchk}";     COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
esac
# Certification surface = registered library modules; `_`-prefixed probe/transient .vo files are excluded from the certification
# closure (CI#46 lesson: a stray _z3_g3.vo with a stale digest tore full-tree certification -- Inconsistent assumptions over UpReqAlign4)
# bash-3.2-safe: case-in-$() one-liner requires bash>=4 (Windows Git Bash OK, macOS /bin/bash 3.2 parse-fails)
MODULES=""
for f in *.vo; do
  case "$f" in _*) continue;; esac
  MODULES="$MODULES $(basename "$f" .vo)"
done
[ -n "$MODULES" ] || { echo "no .vo found"; exit 1; }
echo "coqchk batch: $(echo $MODULES | wc -w) modules (shared closure)"
"$K" -o -Q . "" $MODULES > "_chk_all.log" 2>&1
e=$?
tail -5 "_chk_all.log"
if [ $e -eq 0 ] && grep -q "Modules were successfully checked" "_chk_all.log"; then
  echo "COQCHK_ALL_PASS"
  exit 0
fi
echo "COQCHK_FAIL (see _chk_all.log)"
exit 1
