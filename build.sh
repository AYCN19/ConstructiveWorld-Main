#!/bin/bash
# ConstructiveWorld220 module-tree build (dependency topological order; base served through the 219.vo trust cache)
cd "$(dirname "$0")"
C="C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
fail=0
for f in $(grep -v '^-' _CoqProject | grep '\.v$'); do
  if [ ! -f "${f%.v}.vo" ]; then
    "$C" -noglob -Q . "" "$f" > "_${f%.v}.build.log" 2>&1
    e=$?
    echo "$f EXIT=$e"
    [ $e -ne 0 ] && { fail=1; tail -4 "_${f%.v}.build.log"; }
  else
    echo "$f SKIP(vo 已存在)"
  fi
done
exit $fail
