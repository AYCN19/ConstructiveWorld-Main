# Gamma segment deposit — certification dossier (C1/C2/C3 through V03)

## Scope

62 segment module sources under `attn/kbgamma_20261108/` (seg_C1 18, seg_C2 21 incl. 1 provenance probe, seg_C3 23). Registry landing (wiring into ConstructiveWorld_Live order.txt/_CoqProject with the 35-piece subset) is the separate integration wave; this branch deposits the certified corpus.

## Certification chain (first-hand on this lineage)

1. Dependency-chain compile — coqdep topological order, thermal-guard wrapped: all green.
2. Bytecode furnace per segment — `coqchk -o -bytecode-compiler yes` -> `Modules were successfully checked` + `Axioms: <none>`.
3. Print Assumptions — closed per theorem, zero axiom blocks.
4. Annotation spec card — two-part headers, five fields (Mission./Dependencies./References./Constructivity./Build.), four-domain English, zero confession literals in comments, CJK zero.
5. Canonical gate4 (vendored v2.1 EXT) — HARD 0 / REVIEW 46 (header-length review class only).
6. md5 succession vs prior ledgers recorded (E949 digest cascade from the annotation retrofit); per-file CJK=0 attachments archived.

## Roster position

- C1: 17 nodes certified (re-verified this wave).
- C2: 18 nodes certified (JointCert lineage + this wave's 20-module chain).
- C3: 11/28 nodes closed (P01 P02 P03 P04 P05 P07 V01 V02 Z01 Z02 + born bases); P09 pending Z06/V05; remaining nodes follow the roster pre-chain (Z03 castable next).
- C4 (0/22): next wave after C3 completes; contour-integration gasket reuse from C3 artifacts.

## Integration note

Segment files require the S-series generation of this repo's main tree (S01-S14 boot verified compatible). The registry landing wave will wire the 35-piece subset into order.txt/_CoqProject; `GaC2_03_d_probe.v` rides for provenance only and is excluded at landing.
