#!/bin/bash
# ConstructiveWorld-Main incremental build: skip when .vo is newer than .v (fingerprint trust-cache semantics)
cd "$(dirname "$0")"
C="${COQC:-C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe}"
# SW2 retarget (2026-09-15): machine-level [user environment variables] COQLIB/ROCQLIB pinned to the 9.0 lib
# override the 9.1 coq_environment.txt -> 9.1 coqc silently loads the 9.0 stdlib and the artifact magic 90001
# is rejected by 9.1 coqchk (bad version, expected 90100). Therefore export them derived from the COQC path,
# keeping bin/lib same-source (E-STAGING-SW2 sandbox evidence: with COQLIB same-source, 90100 roundtrip, coqchk EXIT=0).
case "$C" in
  */bin/coqc.exe) export COQLIB ROCQLIB; COQLIB="${C%/coqc.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
  */bin/coqc)     export COQLIB ROCQLIB; COQLIB="${C%/coqc}";     COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
esac
fail=0
while IFS= read -r f; do
  [ -f "$f" ] || continue
  v="${f%.v}.vo"
  if [ -f "$v" ] && [ "$v" -nt "$f" ]; then
    echo "$f SKIP(vo 新于源)"
    continue
  fi
  # -native-compiler no: avoids a locally measured Rocq 9.0 hang of the coqnative subprocess (E-STAGING-WangWW-native card);
  # kept as a conservative flag after the 9.1 retarget (PROBE91 all-green evidence); logical digest unchanged, coqchk certification unaffected.
  # Only affects runtime native Compute acceleration; logical digest unchanged, coqchk certification unaffected.
  mkdir -p "$(dirname "_${f%.v}.build.log")"
  "$C" -native-compiler no -Q . "" "$f" > "_${f%.v}.build.log" 2>&1
  e=$?
  echo "$f EXIT=$e"
  if [ $e -ne 0 ]; then fail=1; tail -6 "_${f%.v}.build.log"; fi
done < <(tr -d '\r' < order.txt | sed 's/#.*//' | grep '\.v$')
exit $fail
