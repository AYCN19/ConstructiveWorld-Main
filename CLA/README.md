# ConstructiveWorld-Main Contributor License Agreement (CLA)

All contributors to ConstructiveWorld-Main must sign a Contributor License Agreement before their pull requests can be merged. This protects both the contributor and the project.

## File Structure

| File | Applies to |
|------|---------|
| `ICLA.md` | Individual contributors (independent developers, students, freelancers) |
| `CCLA.md` | Legal entities (companies, institutions, teams) and their employees |
| `RLA.md` | Licensees of the runtime components (extraction artifacts) — the executable checkers to be released separately in the future |
| `commercial_license_template.md` | Counterparties in commercial license negotiations (template serving as the starting point for negotiation) |

## Signing Process

### Individual Contributors (ICLA)
1. Open `ICLA.md`
2. Fill in the signature block (name, email, GitHub ID, date)
3. Send it to `168888@live.cn`, or attach a scanned copy or screenshot to your first Pull Request

### Legal Entities (CCLA)
1. An authorized representative of the company opens `CCLA.md`
2. Fill in the company information and signature
3. Send it to `168888@live.cn`
4. Each employee who actually contributes code must still sign the ICLA, but may cite the company's CCLA number in the remarks field

## Why Is a CLA Needed?

ConstructiveWorld-Main adopts a dual-licensing model of **Apache 2.0 (public edition) + commercial license (enterprise edition)**. The CLA ensures that:

- Contributors' code can be licensed to users worldwide under Apache 2.0
- Contributors' code can also be included in the commercially licensed edition (licensed to paying customers)
- Contributors retain the copyright in their own code (only a right to use is granted; ownership is not transferred)
- The project is protected against the risk of patent claims

## RLA Track Boundary Statement (2026-10-06)

The Apache-2.0 master license already grants every recipient the right to extract from, use, and commercialize the public source face, including its extraction products (.ml/.mli); the licensable scope of the RLA track is limited to: (i) officially supported and warranted distribution and maintenance services; and (ii) future non-public assets and incremental technical services. The RLA imposes no retroactive commercial restriction on the public source face. For details, see the boundary statement section of `NOTICE.md` in the repository root.

## Upstream Dual-Track Registration (2026-10-06)

`ConstructiveCauchyRealsSep.v` (the escape-window separation engine for the constructive Cauchy reals) has been submitted upstream to rocq-prover/stdlib (PR #313, under review): the copy accepted upstream is governed by the stdlib license (LGPL-2.1); the same-source copies in this repository and those seeded into sandboxes remain under Apache-2.0, with rights and obligations unchanged — same source, dual-track, two licenses coexisting. For the full registration, see Section 2 of `NOTICE.md` in the repository root.

## Legal Effect of the Agreements

A CLA is a legally binding agreement. If you have any doubts, you are advised to consult legal counsel before signing.




