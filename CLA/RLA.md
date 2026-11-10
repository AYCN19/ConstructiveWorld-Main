# ConstructiveWorld-Main Runtime License Agreement

**Agreement No.:** CW-RLA-_______
**Version:** v1.0
**Drafting Date:** 2026-07-10

---

## Parties

| Role | Name | Contact |
|------|------|---------|
| **授权方 (Licensor)** | 王宝军 | 168888@live.cn |
| **Licensee** | _________________________ | _________________________ |

---

## Recitals

- **A.** The Licensor is the copyright holder of ConstructiveWorld-Main, the Constructive World modular formalization library (the "System").
- **B.** The source code of the System is published at https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main under the Apache License 2.0.
- **C.** The source code of the System and the .vo trust cache are freely usable under the Apache License 2.0; the commercial-use authorization of Apache 2.0 does not apply to the executable Runtime Components that the Licensor extracts from the modules and releases in the future.
- **D.** The Licensee wishes to obtain a license to use the Runtime Components.

**Boundary Statement (2026-10-06)** The Apache-2.0 master license already grants every recipient the right to extract from, use, and commercialize the public source face, including its extraction products (.ml/.mli); the licensable scope of this Agreement (the RLA track) is limited to: (i) officially supported and warranted distribution and maintenance services; and (ii) future non-public assets and incremental technical services. This Agreement imposes no retroactive commercial restriction on the public source face.

*(Boundary Statement: the Apache-2.0 master license already grants every recipient the right to extract from, use, and commercialize the public source face, including its extraction products (.ml/.mli). The RLA track only covers (i) officially supported and warranted distribution and maintenance services and (ii) future non-public assets and incremental technical services; it imposes no retroactive commercial restriction on the public source face.)*

---

## Article 1 — Definitions

**1.1 "Runtime Components"** means the OCaml executable checkers that the Licensor extracts from the modules of the System via Coq Extraction and releases in the future, together with their accompanying compiled artifacts and data files. **As of the date of publication of this Agreement template, no component has been released; components will be registered in this table upon the first extraction release.**

| Component | Type | Description |
|------|------|------|
| (No component released yet) | OCaml executable checker extracted via Coq Extraction | To be registered upon the first extraction release (e.g., a module-level reflective checker executable) |

**Status record (2026-10-06):** The extraction products of Coq Extraction (.ml/.mli) currently present in this repository are objects of public audit; they are released together with the source code under the license of the source files (Apache License 2.0) and are not Runtime Components. This table remains empty until an executable Runtime Component is first released separately, at which time it will be registered here.

**Note:** The .vo trust cache in `ConstructiveWorld_vo/` is a development dependency of the System; it is freely usable under the Apache License 2.0, is not a Runtime Component, and is not governed by this Agreement.

**1.2 "The System"** means all software components of ConstructiveWorld-Main, the Constructive World modular formalization library, including the public source code and the Runtime Components.

**1.3 "Non-Commercial Use"** means personal study, academic research, and collaboration on open-source projects, not involving any direct or indirect commercial revenue.

**1.4 "Commercial Use"** means all uses other than those in Section 1.3, including but not limited to: embedding the System in commercial products, offering it as a cloud service, and internal use in production environments.

---

## Article 2 — Grant of License

**2.1 Scope of License.** The Licensor grants the Licensee a non-exclusive, non-transferable, non-sublicensable, worldwide license solely to load and invoke the Runtime Components within the System.

**2.2 Limitations on Use.** The scope of the license depends on the type of Licensee:

| Type | Fee | Commercial use | Redistribution | Reverse engineering | Agreement version |
|------|------|---------|--------|---------|---------|
| Individual/Academic | Free of charge | ❌ | ❌ | ❌ | RLA §1-3 |
| Open-source project | Free of charge | ❌ | ❌ | ❌ | RLA §1-3 |
| Commercial company | Per the commercial license | ✅ | ❌ | ❌ | Commercial license + RLA |

**2.3 Reservation of Rights.** The Licensor reserves all rights not expressly granted in this Agreement.

---

## Article 3 — Restrictions

The Licensee shall not:

- **(a)** reverse engineer, decompile, or disassemble the Runtime Components, or attempt in any manner to derive their source code;
- **(b)** extract, copy, or export seed data, semantic coordinates, or any internal data from the Runtime Components;
- **(c)** use the Runtime Components together with modified source code of the System;
- **(d)** redistribute, rent, lease, lend, or transfer the Runtime Components in any form;
- **(e)** use the Runtime Components in any software or system other than the System;
- **(f)** remove or modify any copyright notice or marking on the Runtime Components.

---

## Article 4 — Term and Termination

**4.1 Term.** This Agreement takes effect on the date the Licensee obtains the Runtime Components and has a term of one year, renewing automatically upon expiry unless either party gives written notice of termination 30 days in advance.

**4.2 Automatic Termination.** If the Licensee breaches any provision of Article 3, this Agreement terminates immediately and automatically, without notice from the Licensor and without any grace period.

**4.3 Effect of Termination.** Upon termination of this Agreement, the Licensee must:
- (a) immediately cease using the Runtime Components;
- (b) destroy all copies of the Runtime Components (including backups);
- (c) confirm in writing that the destruction has been completed.

**4.4 Survival.** Article 3 (Restrictions) and Article 7 (Disclaimer) survive the termination of this Agreement.

---

## Article 5 — Updates and Support

**5.1 Updates.** The Licensor may release updated versions of the Runtime Components from time to time. The Licensee is entitled to obtain such updates during the term of this Agreement.

**5.2 Support.** This Agreement does not include any technical support obligation. Technical support, custom development, and troubleshooting require a separate service agreement.

---

## Article 6 — Intellectual Property

**6.1 Ownership.** All intellectual property rights in the Runtime Components (including but not limited to copyright, patent rights, and trade secrets) belong to the Licensor. This Agreement does not transfer any intellectual property rights.

**6.2 Feedback.** The Licensor is entitled to use, without restriction and without any obligation, any feedback, suggestions, or proposals for improvement provided by the Licensee regarding the Runtime Components.

---

## Article 7 — Disclaimer and Limitation of Liability

**7.1 Disclaimer.** The Runtime Components are provided "AS IS", and the Licensor makes no warranty of any kind, express or implied, including but not limited to warranties of merchantability, fitness for a particular purpose, and non-infringement.

**7.2 Limitation of Liability.** In no event shall the Licensor be liable for any indirect, incidental, special, or consequential damages arising from the use of or inability to use the Runtime Components.

---

## Article 8 — General Provisions

**8.1 Entire Agreement.** This Agreement constitutes the entire agreement between the parties with respect to the Runtime Components and supersedes any prior communications.

**8.2 Severability.** If any provision of this Agreement is held to be invalid or unenforceable, the remaining provisions shall remain in effect.

**8.3 Governing Law.** This Agreement is governed by the laws of the People's Republic of China.

**8.4 Dispute Resolution.** The parties shall resolve any dispute arising out of this Agreement through amicable negotiation; if negotiation fails, the dispute shall be submitted to the China International Economic and Trade Arbitration Commission (CIETAC) for arbitration in accordance with its arbitration rules in effect at that time.

---

## Signature Page

| Licensor | Licensee |
|-------------------|-------------------|
| 王宝军 | _________________________ |
| Signature: ________________ | Signature: ________________ |
| Title: ________________ | Title: ________________ |
| Date: ________________ | Date: ________________ |
| Type of use: □ Individual/Academic □ Open-source project □ Commercial company | Unified Social Credit Code / Registration No.: ________________ |

---

## Annex A — Runtime Components Acquisition Registration Form

*(To be completed by the Licensee and sent to 168888@live.cn; the Licensor will provide a download link upon confirmation.)*

| Field | Content |
|------|------|
| Applicant name | |
| Contact person | |
| Email | |
| Type of use | □ Individual/Academic □ Open-source project □ Commercial company |
| Project/product name | |
| Estimated number of users | |
| Commercial license required | □ Yes □ No |
| Remarks | |



