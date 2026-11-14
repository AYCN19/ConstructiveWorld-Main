#!/usr/bin/env python3
"""W3 heavy-category exemption filter (20261115 user order).

Narrows the attest skip list to the closed heavy registry
(w3_heavy_exempt.txt: flag / vm_compute-heavy categories) for the
periodic full-tree sweep.  Gate-consistency contract: this rewrites BOTH
the skip file AND the reconcile JSON's skipped/sent_to_chk pair, so
gate2 R2 (appendix set == reconciliation skipped set) and R4 (coverage
partition) hold on the narrowed set.  Fingerprint-changed stems never
enter the skip list (attest_reconcile already excludes them), which is
the "unless fingerprint changed" side of the rule; newly-registered
heavy modules are checked at least once before they can appear in the
archive at all.  On any failure the caller falls back to the legacy
full sweep (empty skip list)."""
import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip", required=True)
    ap.add_argument("--recon", required=True)
    ap.add_argument("--registry", default=str(Path(__file__).with_name("w3_heavy_exempt.txt")))
    a = ap.parse_args()
    reg = {
        l.strip()
        for l in open(a.registry, encoding="utf-8")
        if l.strip() and not l.startswith("#")
    }
    skip_p, recon_p = Path(a.skip), Path(a.recon)
    lines = [l.strip() for l in skip_p.read_text(encoding="utf-8").splitlines() if l.strip()]
    kept = sorted(l for l in lines if l in reg)
    drop = len(lines) - len(kept)
    recon = json.loads(recon_p.read_text(encoding="utf-8"))
    surface = set(recon.get("surface") or [])
    kept_set = set(kept)
    recon["skipped"] = kept
    recon["sent_to_chk"] = sorted(surface - kept_set)
    recon["w3_filter"] = {
        "skip_in": len(lines),
        "kept": len(kept),
        "dropped_from_skip": drop,
        "registry": sorted(reg),
    }
    recon_p.write_text(json.dumps(recon, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    skip_p.write_text("".join(l + "\n" for l in kept), encoding="utf-8", newline="\n")
    print(f"W3-SKIP-FILTER: skip_in={len(lines)} kept={len(kept)} dropped={drop} registry={len(reg)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
