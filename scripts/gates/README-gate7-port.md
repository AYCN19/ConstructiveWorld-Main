# gate7 port — extraction-execution gate (red-line law IV, 4a/4b)

Ported from the ConstructiveWorld-Set lineage (`scripts/gates/gate7_extract_run.py` + its census dependency `gate6_statement_census.py`). No source changes: the script reads the tree-relative `ConstructiveWorld_Live/order.txt` registry, which this repo carries in the same layout.

## Usage

1. After a full build step (.vo present for every registry module):
   `python3 scripts/gates/gate7_extract_run.py` (report/census mode, exit 0)
2. Baseline generation (one-off, on this repo's tree):
   `python3 scripts/gates/gate7_extract_run.py --baseline-out scripts/gates/gate7_extract_baseline_main.json`
3. Gate mode on subsequent runs:
   `python3 scripts/gates/gate7_extract_run.py --gate --baseline scripts/gates/gate7_extract_baseline_main.json`
   (red on Obj.magic growth on either face, erasure-candidate growth, driver-rc regression, or a new module born with magic>0 / missing names)

## Main-specific notes

- The Set-side baseline (`gate7_extract_baseline.json`) does NOT transfer: statement sets differ per tree. Generate the Main baseline on THIS repo's compiled tree (Windows delta-furnace side or a local full build).
- Statement-name census (gate6) and the v2 sandbox patches (keyword blacklist + scope-depth tracking) are carried verbatim.
- `gate7_census_justification-*.json` from the Set lineage are per-tree artifacts; regenerate equivalents here as needed.
