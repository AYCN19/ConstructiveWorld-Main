# Survey Volume · GaC2_18_ZetaDerivBound (C2.18, sfo slot)

# 勘形卷 · GaC2_18_ZetaDerivBound（C2.18 节点 · sfo 面）

> Ticket: GD-20261115-YCARRIER-01 (y-carrier four-gap survey and construction).
> Routing line: y carrier layer; PR body first line per the standing rule:
> 王小哥（y承载层线·曾栢源席）
> Base commit: `8e70342` (verified: `git rev-parse HEAD` = `8e7034266311d0728092cc7b7fb403177e992759`, `git status --porcelain` empty; zero tree writes, zero git mutations, main untouched).
> Deliverable directory (this volume and every artifact below):
> `D:/ComplexAnalysis/zby_ycarrier_out_20261115/lanes/c18/`

---

## §0 Zeroth step · three mandatory lanes / 第零步三道

| Lane | Execution | Result |
|---|---|---|
| 1. Skills loaded | Skill(cw-deep-mining) + Skill(cw-tail-supply) + Skill(cw-ci-sop) all loaded in full | Deep-mining three-tier discipline (tier downgrade forbidden, wall verdicts need review hooks), tail-supply consumption-site laundering rules, and the CI SOP green-verdict four-piece plus the thermal-wrap rule are all in force for this volume. Zeroth-step evidence is this table; review hooks R1-R10 of the grading volume are carried in §6 below. |
| 2. Card search | Keywords `y-c2-gap-and-e1-outsource-20261108`, `paper-y-series-vs-a-20261108`, `certification-and-gates-iron-laws`, `red-line-law-path-a`, `coq-rocq-pitfall-precedents`, `deep-mining-methodology` searched in the package `techdocs/` and in the working tree | Zero hits on all six keywords (grep over techdocs/ and the Live tree, run this session). Per the standing rule the absence does not stop work; the discipline content is carried by the skill originals plus the grading volume (techdocs/勘定-yE1落岸逐节点分级-20261113.md, read in full) and the SL3 survey template (techdocs/勘形卷模板-SL3形.md) and the SL3 reading volume (techdocs/判读-SL3勘形回执-20261114.md). |
| 3. Technical documents and target | Dispatch spec section one read (工单-y承载层四缺口-工作流版-20261115.md, 73 lines); grading volume read in full; target `GaC2_18_ZetaDerivBound.v` read in full (255 lines, 8 faces); dependency faces read: `GaC2_12_CauchyCoeffEst.v` (Section block + cauchy_chain + cauchy_est_n/cauchy_est_n1), `GaC2_12_CauchyCoeffEst_a.v` (full), `GaC2_10_EtaContinuation.v` (notes + Sections 1-4), `GaC2_16_ZetaVerticalBound.v` (:115-345), `GaC2_17_StripVerticalAsm.v` (:113-238), `GaC2_09_DenomZeroSet.v` (:182-281), `GaC2_09_DenomZeroSet_b.v` (power carrier and lattice faces), `GaC2_18_ZetaDerivBound_cert.v` (full), `CxRealPairCore.v`, `CxRealPairExpLog.v`, plus targeted signature greps in S02/S03/S07 | All in hand with line anchors; findings below cite `path:line` |

Judgment time and base state (staleness anchor rule): 2026-11-15, HEAD = `8e70342`, clean tree, cold build of the full Require closure of the target reproduced green in the sandbox (§5). Any landing that changes the C2-12 slots, the C2-16/17 carrier promotions, or the C2-10(b) row voids the tier verdicts in §4 and triggers §6.

---

## §1 Chain state / 链上现势（已证与缺环逐件）

### 1.1 Machine-proven faces consumed by this node（机检级已证面）

| # | Face | Location | State | Note |
|---|---|---|---|---|
| 1 | `denom_zero_real_dir` | GaC2_09_DenomZeroSet.v:187-268 | Qed | norm of the denominator zero implies real part = 1 (one direction) |
| 2 | `zero_set_membership` | GaC2_09_DenomZeroSet.v:270-281 | Qed | lattice points `s_at k` sit on the unit-vertical line |
| 3 | `denom_nz` / `denom_sq_pos` / `d10_denom_is_d09` | GaC2_10_EtaContinuation.v:221-239 | Qed (machine cluster) | domain predicate, positivity witness, name bond to the C2-09 denominator |
| 4 | `d10_eta_conv` / `zeta_tilde` | GaC2_10_EtaContinuation.v:193-201, :248-254 | Definition + machine cluster | eta value premise carrier; division-free quotient carrier (eta times witness inverse times conjugate denominator) |
| 5 | `gaC12_local_exp_seq` / `gaC12_deriv1` / `gaC12_nth_coeff` | GaC2_12_CauchyCoeffEst_a.v:64-97 | Qed faces | the term-wise differentiation legality carrier: per-point coefficient sequence with quadratic remainder; the first-coefficient projector |
| 6 | `cauchy_est_n1` / `cauchy_est_n` | GaC2_12_CauchyCoeffEst.v:289-327 | Qed inside Section CauchyCoeffEst; discharged with explicit premise arguments | the Cauchy coefficient estimate: `|a_n|^2 <= (2^n * M / R^n)^2`; the n=1 form gives `|a_1|^2 <= (2 M / R)^2`; consumes the three registered slots Hnn / Hmod_gate / Hchain (v:79-106) |
| 7 | `boundary_bounded` | GaC2_11_MaxModulusDisk.v:92-93 | Definition | circle bound carrier consumed by the estimate |
| 8 | `mm_norm_self_opp` / `mm_norm_wd` | GaC2_11_MaxModulusDisk_b.v:52-61 | Qed | norm of `z + (-z)` is zero; norm respects pointwise bond |
| 9 | `d09_c_exp_congr` / `d09_const_mult` / `d09_carrier_norm` | GaC2_09_DenomZeroSet_b.v:314, :82-84, :196 | Qed | exponential congruence, constant algebra, norm-of-power face |
| 10 | `real_square_not_negative` | S02_CauchyComplete.v:812-837 | Qed | negative-form square nonnegativity at the Cauchy real layer |
| 11 | order kit | S02_CauchyComplete.v:468-473, :2400, :2421, :3181, :2317, :1311 | Qed | margin-form `real_lt`; `real_le` is the informative Or (strict or equality); irreflexivity; lt-eq-lt; lt-le-iff; pointwise route into equality; pointwise product projection |
| 12 | inverse kit | S03_QExp.v:6750, :6799; S07_RealSetoidExpLog.v:3498, :3800 | Qed | inverse correctness and positivity, inverse uniqueness, strict inverse antitone |
| 13 | RealSetoid compat faces | S07_RealSetoidExpLog.v:121, :298, :453, :6830, :6845, :6706-6743, :6999, :3772 | Qed | equality-under-operations, order replacement, strict and weak product monotonicity, opposite order faces, product positivity, constant positivity |

### 1.2 Statement-carrier faces with no proof body（语句载体缺证面）

| Face | Location | State |
|---|---|---|
| `r_pos_lower` | GaC2_18_ZetaDerivBound.v:210-221 | Definition carrier; triple sigT witness (positive radius; disk-wide `denom_nz eps_lb`; ball inside the consumer domain). Zero proof body. This construction machine-refutes the minted form at the center point (§2, finding F1). |
| `zeta_deriv_bound` | GaC2_18_ZetaDerivBound.v:239-255 | Definition carrier; squared conclusion `|gaC12_deriv1 g s0|^2 <= (C3 * log^2 T)^2`. Zero proof body. Conditionally closed by this construction (§2, finding F2; §5 deliverable). |
| `zeta_strip_uniform` / `zeta_strip_cover` / `zeta_vert_bound_disj` | GaC2_17_StripVerticalAsm.v:176-238 | carriers (head note :90-97 declares bodies wait for the mother chain) |
| `zeta_vert_mid` / `zeta_vert_near1` | GaC2_16_ZetaVerticalBound.v:320-345 | carriers (the (b)/(c) band faces; C1/C2/c_win explicit constant arguments) |
| `zeta_vert_high` | GaC2_16_ZetaVerticalBound.v:274-309 | PROVEN (the high-band uniform face over partial sums, consuming the Htri slot) |
| `zeta_tilde_agree` / `zeta_tilde_analytic` / `zeta_tilde_unif_bound` | GaC2_10_EtaContinuation.v:269+ | carriers (the (a)/(b)/(c) rows; (b) is the registered breakthrough row) |
| certificate bands | GaC2_18_ZetaDerivBound_cert.v:53-78 | vm_compute samples green (C3 = 4 C2 / c form; radius half-gap form; two-sided imaginary skeleton) |

---

## §2 Quantified distance and the two findings / 量化距离与两项发现

### 2.1 Finding F1 (machine-checked): the minted `r_pos_lower` carrier is refutable at the center point（发现 F1：铸面 r_pos_lower 在中心点被机器证伪）

The consumer domain `consumer_domain` (GaC2_18_ZetaDerivBound.v:172-182) contains the point `s0 = c_one` for every admissible cap: its real part equals 1 and its imaginary part equals 0, both bounds hold. The disk-wide denominator slot inside `r_pos_lower` quantifies over `z` with `|z - s0|^2 <= r^2`; instantiating `z := s0 = c_one` (zero distance) yields `denom_nz eps_lb c_one`. The denominator at the center is `1 - 2^(1-1) = 0` (the k = 0 point of the zero lattice, machine side: `gaC18_two_pow_1ms_at_one` and `gaC18_denom_center_zero`, this construction), so the slot asserts `eps_lb < 0`, against the premise `Hep : 0 < eps_lb`.

Machine evidence: `gaC18_r_pos_lower_refuted` (supply face, PA-Closed, this construction):

```
Lemma gaC18_r_pos_lower_refuted :
  forall T c, 2 <= t_cap T -> 1 < t_cap T -> 0 < log_t T ->
  forall eps_lb, 0 < eps_lb ->
  consumer_domain T c .. c_one ->
  r_pos_lower T c .. eps_lb .. c_one Hdom -> False.
```

Consequence (honest registration): the minted carrier cannot close at any mother-chain integration without a center-positivity premise. The registered card route ("radius = half the zero-set distance") presupposes a center at positive distance from the zero lattice; that presupposition is absent from the minted premise family. This upgrades the grading-volume C2.18 row: the sfo state was registered as "proof routes registered, bodies close at segment-end integration"; for the (a) face that registration is now machine-falsified as stated. The correction travels as the reined carrier `r_pos_lower_reined` in the supply face (adds `Hcen : denom_nz eps_lb s0`); the stem is untouched (zero tree writes; the correction is a sibling file requiring the stem).

### 2.2 Finding F2: the minted `zeta_deriv_bound` is conditionally closable now, unconditionally closable at mother-chain landing（发现 F2：铸面 zeta_deriv_bound 条件闭包今日可达·无条件闭包候母链）

Distance accounting from the minted conclusion to a machine proof, measured premise by premise:

| Step | Content | State |
|---|---|---|
| 1 | `|a1|^2 <= (2 M / r)^2` from the C2-12 estimate at the disk (s0, r) | in tree (`cauchy_est_n1`), consumes 3 registered slots |
| 2 | `M <= C2 * log T` (vertical transfer on the disk sup) | premise slot `HM` (mother chain: C2-16/17 faces, currently carriers) |
| 3 | `1/r <= 2 log T / c` (radius floor `c / (2 log T) <= r`) | premise slot `Hfloor` (mother chain: the reined radius witness) |
| 4 | algebra `(2 M / r) <= (4 C2 / c) * L^2` with `L = log T` | CLOSED by this construction (`gaC18_le_mult_compat_eq`, `gaC18_sq_mono`, `gaC18_inv_floor_transfer`, `gaC18_c3_algebra`, `gaC18_le_eq_swap`) |
| 5 | binding `C3 = 4 * C2 / c` explicit | premise `Hbind : real_eq C3 (gaC18_c3_form C2 c Hc)` (constants-as-arguments; the certified corridor lives in the stem cert, vm_compute samples green) |

So the unconditional closure of `zeta_deriv_bound` waits on exactly four named items: (i) the C2-12 slot discharge (Hnn / Hmod_gate / Hchain, GaC2_12_CauchyCoeffEst.v:79-106), (ii) the vertical face promotion of C2-16/17, (iii) the reined radius witness body (the L26 distance machine), (iv) the C2-10(b) expansion witness for `zeta_tilde` feeding `Hloc`/`Hallign`. Every item has a registered carrier or slot in the tree; none requires new statement architecture. That places the unconditional closure in the breakthrough tier by supply, not by architecture.

### 2.3 The legality face（求导合法面）

In the landed dialect the term-wise differentiation legality face is exactly `gaC12_local_exp_seq` (per-point expansion with quadratic remainder) plus the first-coefficient projector `gaC12_deriv1`, bonded to the C2-11 slot form by `gaC12_slots_of_seq` / `gaC12_deriv1_slots_of_seq` / `cauchy_deriv1_align_c211` (all Qed, GaC2_12_CauchyCoeffEst_a.v:122-151, CauchyCoeffEst.v:333-349). What is NOT closable today and is registered, not attempted: the uniqueness of the first coefficient across expansion witnesses (the classical "the derivative is well defined" leg). The margin-form equality would need an archimedean limit argument on `|a1 - a1'|^2 <= |w|^2 (T+T')^2` over arbitrarily small positive radii; the in-tree negative-form square face (S02:812) is insufficient for the informative-Or `real_le`, and no tightness face exists. Same register as the C2-12 Hnn slot.

---

## §3 Lever inventory / 杠杆清单（树内可用件·判难度前盘点）

| # | Lever | Location | Used by this construction |
|---|---|---|---|
| 1 | `cauchy_est_n1` (discharged) | GaC2_12_CauchyCoeffEst.v:312-327 | yes, the estimate core |
| 2 | `gaC12_deriv1` / `gaC12_local_exp_seq` / `gaC12_rdiv` / `gaC12_sq` / `gaC12_two_pos` | GaC2_12_CauchyCoeffEst_a.v | yes |
| 3 | `boundary_bounded` | GaC2_11_MaxModulusDisk.v:92 | yes (circle-bound slot shape) |
| 4 | `mm_norm_self_opp` / `mm_norm_wd` | GaC2_11_MaxModulusDisk_b.v:52-66 | yes (refutation chain, alignment face) |
| 5 | `denom_nz` / `zeta_tilde` / `d10_denom_is_d09` | GaC2_10_EtaContinuation.v:221-254 | yes (statement shapes) |
| 6 | `two_pow_1ms` / `d09_c_exp_congr` / `d09_const_mult` | GaC2_09_DenomZeroSet_b.v:153, :314, :82 | yes (center refutation chain) |
| 7 | `c_exp_zero` | CxRealPairExpLog.v:125 | yes |
| 8 | `c_plus_opp` / `c_plus_congr` / `c_opp_congr` / `c_scale` | CxRealPairCore.v:209-216, CxRealPairExpLog.v:99-109 | yes |
| 9 | `real_lt_eq_lt` / `real_lt_irrefl` / `real_lt_trans` / `real_lt_le_iff` / `real_le_trans` / `real_le_refl` | S02_CauchyComplete.v | yes |
| 10 | `real_eq_of_zero_diff` / `real_mult_proj` / `real_const_proj` / `d09_const_mult` | S02:2317, :1311, :1323; C2-09_b:82 | yes (the pointwise-ring route that collapsed the C3 algebra) |
| 11 | inverse kit (`real_inv_pos_correct` / `_pos`, `real_inv_lt_contra`, `real_inv_unique`) | S03:6750-6801, S07:3498, :3800 | yes (floor transfer) |
| 12 | RealSetoid kit (`real_le_compat`, `real_eq_mult_compat(_adapt)`, `real_le_mult_compat(_weak)`) | S07:453, :298, :902, :6830, :6845 | yes |
| 13 | `real_mult_positive` / `real_const_pos` / opposite order faces | S07:6999, :3772, :6706-6743 | yes |
| 14 | stem carriers and cert bands | GaC2_18_ZetaDerivBound.v (8 faces), _cert.v | the construction requires the stem and keeps its 8 faces untouched |

Missing levers (named, with review hooks in §6): real-layer positive square nonnegativity / trichotomy machine (blocks component domination and the a1-uniqueness leg); distance-propagation machine for the denominator on a disk; C2-16/17 band promotion; C2-10(b) expansion witness.

---

## §4 Tier verdicts / 三档判定（证据义务递增·禁降档）

| Item | Tier | Evidence duty performed |
|---|---|---|
| Machine refutation of minted `r_pos_lower`; reined carrier statement face | 可及 (done) | compiled, PA-Closed, coqchk Axioms none, extraction magic 0 (§5) |
| Conditional closure of `zeta_deriv_bound` (algebra + estimate assembly) | 可及 (done) | same gates |
| C3 = 4 C2 / c binding algebra and helpers | 可及 (done) | same gates |
| Reined radius witness body (distance propagation of `denom_nz` from a positive-margin center over a disk) | 需突破 | named missing machine: a lower bound of `|1 - 2^(1-z)|^2` in terms of distance to the zero lattice (needs the C2-09 analytic stack beyond `denom_zero_real_dir`, no in-tree precedent; the tree exports only the one-direction vanishing face). Not attempted; no wall verdict claimed, review hooks in §6 |
| Ball-inside-domain geometry (`disk_in_consumer` body) | 需突破 | named missing machine: real-layer positive square nonnegativity / trichotomy (the C2-12 Hnn register); component domination `(Re diff)^2 <= |z-w|^2` needs it, and the square-root-free extraction of the real-part order needs sign reasoning on the same machine. Not attempted |
| Circle-bound supply `M <= C2 log T` on `zeta_tilde` over the disk | 需突破 | waits on C2-16 `zeta_vert_mid`/`zeta_vert_near1` and C2-17 `zeta_strip_uniform` carrier promotions (mother chain), then the Hbond transfer over the disk family |
| C2-12 slot discharge (Hnn / Hmod_gate / Hchain) | 需突破 | the registered C2-12 debts (grading volume C2.12 row); unchanged by this node |
| C2-10(b) Weierstrass expansion witness of `zeta_tilde` (feeds Hloc) | 需突破 | the card-registered breakthrough row; the conditional closure consumes its output through explicit premises only |
| 真墙 | 不判 | W-1 lever inventory performed (§3, fourteen entries, all consumed or named); W-2 no principle-wording verdict: every blocked face cites a named missing machine with an in-tree registration trail, no intuition-grade claim; W-3 review hooks attached per item (§6); W-4 cross-checks: the grading volume C2.18 row (C tier, sfo) and the stem head notes independently register the same mother-boundary; W-5 nothing overturned except F1, which carries machine evidence rather than a verdict flip; W-6 assembled |

---

## §5 Construction slice (reachable segment, delivered) / 施工切片（可及段·已交付）

Deliverable: `lanes/c18/GaC2_18_ZetaDerivBound_supply.v` (630 lines, md5 `6ac91519d5d7f692b41b15549fdebb73`, byte-equal to the sandbox compiled copy). Statement faces delivered (16 named items, all Set-sorted, all Defined transparent per the transparency ruling, zero admits, zero axioms, zero classical lemmas):

> **Repair-round fingerprint note (added at PR assembly, 2026-11-15)**: the
> gate4 comment-fix repair round (five cmtfix compile logs across the four
> lanes, 2026-11-15 21:17:38, all GREEN4_final=True) postdates this volume's
> close; the figures in the paragraph above are the pre-repair values.
> Post-repair on-disk fingerprints, re-pinned at PR assembly: md5
> `6b6ea4cc028358ace778e44ff619d044`, 599 lines, 28,607 bytes. Statement
> names unchanged (gate6 final: files=1, ch1/ch2/ch3 = 0/0/0, names=16).

| Item | Kind | Content |
|---|---|---|
| `gaC18_scale_congr` / `gaC18_scale_zero` | Lemma | scalar-multiple congruence and zero face |
| `gaC18_two_pow_1ms_at_one` | Lemma | `2^(1-1) = 1` at the center (exponential congruence + zero face) |
| `gaC18_denom_center_zero` | Lemma | denominator norm at the center is zero |
| `gaC18_r_pos_lower_refuted` | Lemma | machine refutation of the minted carrier at `s0 = c_one` (finding F1) |
| `r_pos_lower_reined` | Definition (statement carrier, no proof claim) | the minted (a) face with the center-positivity premise restored |
| `gaC18_two_two_four` | Lemma | `2*2 = 4` at the constant layer |
| `gaC18_le_mult_compat_eq` / `gaC18_sq_mono` / `gaC18_le_eq_swap` | Lemma | product/square monotonicity helpers on strictly positive sides |
| `gaC18_inv_floor_transfer` | Lemma | `c * u^-1 <= r` implies `r^-1 <= u * c^-1` (inverse antitone via uniqueness) |
| `gaC18_c3_algebra` | Lemma | the binding identity `2*(C2*L*(2*L*c^-1)) = (4*C2*c^-1)*(L*L)`, closed by the pointwise ring after projection rewrites |
| `gaC18_c3_form` / `gaC18_chain_slot` | Definition | explicit binding form; the C2-12 chain slot restated at (s0, r) |
| `gaC18_deriv_bound_closure` | Lemma | the conditional closure: estimate + vertical transfer + floor + binding close the squared conclusion of the minted (b) face |
| `gaC18_deriv_bound_at_prem` | Lemma | alignment face: closure at the canonical center disk transfers to a caller disk proof through the pointwise bond `Hallign` |

Gate records (all run this session, logs at the lane root):

| Gate | Command | Result |
|---|---|---|
| coqc rc | `coqc -native-compiler no -q -Q . "" GaC2_18_ZetaDerivBound_supply.v` under the thermal guard | rc = 0, log `GaC2_18_ZetaDerivBound_supply.compile.log`, zero Error lines, .vo magic `436f7121000160bc`, .vo newer than .v |
| poison scan | grep over the deliverable for Axiom/Admitted/admit/Abort/Unset/Classical/excluded_middle/FunctionalExtensionality/ProofIrrelevance/Lra/Psatz/Reals/Program/Obligation | zero hits |
| CJK scan | grep `[一-鿿]` over the deliverable | zero hits |
| PA Closed | probe `GaC2_18_supply_pa_probe.v`: `Require Import GaC2_18_ZetaDerivBound_supply.` + `Print Assumptions` over all 16 named items | 16/16 `Closed under the global context`, zero Axiom lines |
| coqchk | `coqchk -o -Q . "" GaC2_18_ZetaDerivBound_supply` | `Modules were successfully checked`, CONTEXT SUMMARY `* Axioms: <none>`, type-in-type `<none>`, unsafe fixpoints `<none>` |
| gate6 census | `py -I gate6_statement_census.py --tree lanes/c18 --text` | files=1, ch1=0 ch2=0 ch3=0, names=16 |
| gate7 extraction | `py -I gate7_extract_run.py --tree _sandbox --order <order> --coqc opam93/bin/coqc.exe --json lanes/c18/gate7_report.json` | modules=1, names=16, rc=0, magic=0/0, missing_candidates=0 |

Closure build record: the full transitive Require closure of the stem was computed mechanically (79 files, 6.6 MB, spanning the S01-S14 base chain, the kbgamma seg_C1/seg_C2 GaC1/GaC2 pieces, and the y_e1 node files) and cold-built in the flat sandbox in dependency order under the thermal guard: 79/79 rc = 0 including `GaC2_18_ZetaDerivBound.v` itself, total wall time about 8 minutes. This resolves, for the base commit `8e70342`, the deposit-time closure uncertainty that the grading volume registered for the P08 node (§7.11 there): the C2.18 closure is complete and buildable.

Environment and thermal registration (honest scope): the canonical thermal protocol trio (`cpu_guard_v3.ps1` and companions) is absent from this workspace; every compile in this construction ran wrapped by the available v2.1-lineage guard copy (`attn/landing_wave/clone/cpu_guard.ps1`, runtime suspend line at 98 C per the standing TL ruling, load pre-gate active, zero runtime suspends observed). Two compiler lanes from sibling sessions were observed running concurrently on this machine; this lane stayed strictly single-flight sequential. All compiles were cold (no vo seed); the Rocq face is 9.3 (vo magic `436f7121000160bc`), consistent inside the sandbox.

---

## §6 Review conditions / 复审条件（W-3·判词有效期至基建变动）

| # | Trigger | Re-evaluation target |
|---|---|---|
| 1 | Any C2-12 slot discharge lands (Hnn norm nonnegativity, Hmod_gate strict maximum modulus, Hchain difference-quotient chain) | the closure premises shrink; `gaC18_chain_slot` and the three slot arguments fold away; re-run gates |
| 2 | C2-16 `zeta_vert_mid`/`zeta_vert_near1` or C2-17 `zeta_strip_uniform` promote from carrier to Lemma (grading volume R2) | the `Hcirc` / `HM` slots become derivable over the disk family through `Hbond`; the conditional closure tightens |
| 3 | C2-10(b) Weierstrass row lands (the expansion witness of `zeta_tilde` on a disk) | `Hloc` becomes constructible for the representative function; `Hallign` in `gaC18_deriv_bound_at_prem` becomes a built lemma from the single witness |
| 4 | A real-layer trichotomy / positive square nonnegativity machine lands (the Hnn register, S02:812 negative form is today's ceiling) | the ball-inside-domain geometry and the a1-uniqueness leg reopen; the reined radius face may become closable |
| 5 | The distance-propagation machine for the denominator (any `|1 - 2^(1-z)|^2` disk lower bound face lands in C2-09 or C2-10) | `r_pos_lower_reined` body construction opens (needs the center premise plus this machine) |
| 6 | Cap carrier re-alignment at mother-chain integration (the stem notes register `t_cap` as the identity-on-cap discharge) | `log_t` / `consumer_domain` shapes re-align; the supply face premises re-point |
| 7 | Grading volume R7 fires (segment interface `GaC2_Iface_VL` lands) | the joint-certification promotion of the stem carriers must consume the supply face findings: the (a) carrier needs the reined premise, otherwise the segment interface inherits a refutable statement |

---

## §7 Honest scope / 诚实面（未跑与不可消解项显式披露）

1. Zero network retrieval this session; all levers are in-tree (fetch-before-cite duty transfers to any consumer of the card route).
2. `r_pos_lower_reined` is a statement carrier with no proof claim; the (b) face closes conditionally; the unconditional closure waits on the four named items of §2.2.
3. The a1-uniqueness leg of differentiation legality is registered as blocked on the trichotomy register (§2.3); no attempt was made, no wall verdict claimed.
4. The grading-volume C2.18 C-tier registration ("proof routes registered") is amended by finding F1 with machine evidence; the stem itself is untouched and the correction travels as the reined carrier plus the refutation lemma.
5. The cold-build record (79/79) covers the base commit `8e70342` snapshot only; later upstream movement re-runs the closure check (§6 hooks).
6. All numeric certificate bands of the stem cert were read but not re-executed this session (they are vm_compute Qed faces of the deposit snapshot; the sandbox build reproduced their module green).

---

## §8 Review-hook carry-over from the grading volume / 复审钩承接（分级卷 §8 R1-R10）

R1 (this wave clears the C2.18 items: done here for the (a) machine refutation plus the (b) conditional closure; the tier re-evaluation is this volume), R2 (mother-chain promotions: hooks 2-3 above), R7 (`GaC2_Iface_VL`: hook 7). R3/R4/R5/R6/R8/R9/R10 concern other nodes and are carried unchanged. Grading-volume hooks are inherited with the judgment time 2026-11-15 and the base state `8e70342` recorded in §0.

---

Deliverables in this lane (single directory, machine-gate scan root):
`GaC2_18_ZetaDerivBound_supply.v` (construction, 630 lines),
`GaC2_18_ZetaDerivBound_supply.compile.log`, `GaC2_18_supply_pa_probe.log`,
`coqchk_supply.log`, `gate7_report.json`, this volume.
Sandbox (compile closure, 79 green modules + supply + probe): `lanes/c18/_sandbox/`.
Tools (closure scan, topological order, drivers): `lanes/c18/_tools/`.
