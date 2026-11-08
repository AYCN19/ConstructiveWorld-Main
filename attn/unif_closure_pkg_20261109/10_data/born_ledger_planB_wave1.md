# planB wave-1 born ledger (lane (B), 20261108)

## Lane adaptation record (provenance, honest disclosure per ruling (c)/(a))
- Form: cpu_guard_v3 duty-cycle -> route-3-style load-gate direct fire.
- Reason: the guard's duty resume silently fails on this box (all threads
  stay Wait:Suspended after NtResumeProcess ntstatus=0); any shot longer
  than one duty window freezes at CPU~0. Documented incident: cpu_guard
  header line 188 (20261002). Reproduced 3x same-form (shots 4b/5/probe),
  rule 同形红>=3 -> stop -> main-agent ruling (c) authorized the direct
  fire with load/thermal double gate; ruling (a) recalibrated the thermal
  fuse 97C -> 99C (canonical authorization-block form, three consecutive
  >= 99C stop) because this box's documented idle clamp IS 96-97C
  (cpu_guard header 20261002 adjudication; every sentinel write tonight
  read G3 96-97C).
- Gates in force per shot: fresh Get-Counter machine load < 50%; thermal
  fuse (single >= 99C skip-round, consecutive-3 >= 99C stop-escalate);
  serial single lane; shot spacing >= 120 s; single-shot wall cap 10 min
  (stop own PID only); on-disk artifact truth judging (.vo exists + md5);
  neighbor build zero contact.

## Shot ledger
- shots 1-3 (02:41-02:43): smoke_api_probe.v rc=0 (API pins; shot 1 rc=1
  Qmult_le_compat_l absent -> replaced by comm-rewrites; shot 2 rc=1
  Qlt_le_trans needs explicit instantiation -> fixed; shot 3 clean).
- shot 4 (02:51): foreground attempt killed by tool timeout mid-freeze
  (guard duty-cycle). shot 4b/5 (03:00-03:30): frozen at CPU~0, evidence
  logged, lane stopped per 同形红>=3, escalated -> ruling (a)/(c).
- shot 6 (05:19, load 28.4%): REAL error, fail-loud: vm_compute on unary
  nat 20^7 (1.28e9 successors) stack overflow (line 137) -> anchors
  re-carried in Z (bracket.v:164 slope-cert precedent).
- shot 7 (05:26, load 27.6%): REAL error, fail-loud: Z.lt is a
  compare-EQUALITY ((a ?= b) = Lt) -> a Z '<' face closes by
  vm_compute; reflexivity, not discriminate (line 143) -> fixed.
- shot 8 (05:29): REFUSED by the then-97C fuse (3 consecutive 97C reads)
  -> escalated -> ruling (a) recalibrated fuse to 99C canonical.
- shot 9-19 (05:30-06:44, foreground lane after the detached-startup freezes
  at 05:45/05:57; foreground+coqc probes proved healthy): piece 1 compile
  iterated to rc=0. Fail-loud fixes en route (all real errors, recorded):
  (a) vm_compute on unary nat 20^7 stack overflow -> Z-carried anchors;
  (b) Z.lt is a compare-equality -> Z '<' faces close by reflexivity;
  (c) replace-by-vm_compute leaves the trivial eq -> add reflexivity;
  (d) Nat.pow_add_r needs the exponent syntactically split (34*1 ->
      28+6 before the rewrite);
  (e) Nat.pow_mul_r direction: forward rewrite turns 2^(L*17) into (2^L)^17;
  (f) nat ring with big literal powers explodes (isolated rc=124) ->
      lemma-chain reorder (mul_assoc/mul_comm);
  (g) nia cannot close 4-atom monomial reorder -> same lemma-chain;
  (h) Qmult_lt_compat_l / Qmult_le_compat_l do not exist in this stdlib ->
      comm + compat_r forms;
  (i) Q replace-by-ring: replace's side-goal is Eq, ring proves Qeq ->
      Qeq asserts + setoid rewrites;
  (j) Qpower_plus metavariable setoid rewrite fails on bare Qeq goals ->
      explicit instances (isolated: qp_test5 GOAL print + explicit rc=0);
  (k) lra not loaded (Lia-only import) -> lia-friendly unfold form;
  (l) (- p) inside a %Q-scope expression needs (- p)%Z;
  (m) qmult_le_compat_l takes explicit x y z args.
- PIECE 1 GATES (06:44): compile rc=0; named-item census 47; Print
  Assumptions 8/8 "Closed under the global context"; coqchk
  -bytecode-compiler yes rc=0, Axioms: <none>. md5: .v
  0be703c84f5ad39d352e196c92fe31a2, .vo
  a4da411cb65c11e1fd0e02ffe845fe02.
- PIECE 2 GATES (06:52): compile rc=0; census 14; PA 11/11 Closed; coqchk
  -bytecode-compiler yes rc=0 (3000s lane, ~15min wall) Axioms: <none>.
  md5: .v 728adc8fbb0165460023c530a1a7aced, .vo d09adbd20a8e3e9089e9f1e3a9e8b370.
  Fail-loud fixes: replace-by-ring Eq/Qeq ×3 (comm asserts); q1 window face
  ground Q-order closes by intro+discriminate (vm_compute reduces Qle to
  the (Lt = Gt) -> False compare form on this toolchain).
- PIECE 3 CALIB GATES (07:25): generator single-source (md5 of the JSON
  097fda87c872c75bacbc63c5239940bd re-verified at emit time); compile rc=0;
  census 18; PA 12/12 Closed; coqchk -bytecode-compiler yes rc=0,
  Axioms: <none>. md5: .v d671d0a9d17576798109bdd03eebb52d, .vo
  863f378c577b86d3348d03e986a4aa6b. Fail-loud fixes: QArith import dropped
  (it opens Q_scope -> nat match-table numeral patterns parse as Q
  constructors); generated comment nesting (straddles_zero pair); Z-order
  faces close by discriminate (<=) / reflexivity (<).
- PIECE 3 DESIGN GATES (07:30): compile rc=0; census 11; PA 5/5 Closed;
  coqchk -bytecode-compiler yes rc=0, Axioms: <none>. md5: .v
  72da5df22e98070607495265a94f2537, .vo cd9821e29daba90e857a9e585987ebf1.
  Fail-loud fixes: (- p)%Z scope inside %Q expressions ×2; End G2_DESIGN
  placement (anchor_one was inside the Section, xpi implicit ->
  (1#1)%Q hit a Z slot).

## Statement-face census with consumption classification (rules pkg doc 03 form)
- planb1_hcage_zerotouch_prescription.v (47 named): Section 1 pin block
  (7 Definitions + 10 Examples, data-carrying numeric faces, vm_compute-
  closed); Section 2 calibration anchors (9 Examples, Z-carried EXACT);
  Section 3 witness + E1/E3 (1 Definition + 2 Lemmas, data-carrying escape
  faces - the Hesc@17 premise-discharge supply); Section 4 Q bridges
  (5 Lemmas, proof-bridge class - consumed inside this unit's proofs only,
  no external consumers yet -> registry entry not required, consumer
  evidence = this file's own proof bodies); Section 5 dance + slot-11
  (2 Lemmas, data-carrying - the 4d ladder's rate-slot consumption faces);
  Section 6 zero-touch (3 Definitions + 1 Theorem, data-carrying - the
  Hcage-free five-premise consumption face). Path-A: all conclusion faces
  informative-sorted (QleT'/QleT/ZleT/and2/and3/sigT/S02 QleT'); zero
  new-cast Prop surface.
- planb2_hesc_limb_impl.v (14 named): 3 Definitions (Route-A bounds shape =
  未消费-supply positional premises, honest census in header; theta_at +
  window face = data-carrying); 5 Lemmas (window<->limb1 adaptation both
  directions + nescD twin, data-carrying); 3 Theorems (arbitrary-witness
  assembly - the window premise LOAD-BEARING variant; Route-A chain-through
  with extracted nonvanishing limb; contract re-pin); 3 Examples (q1 window
  EXACT + bracket reuse faces slope/q1_anchor - real in-tree supplies).
- planb3_g1_calib.v (18 named, GENERATED): 4 table Definitions (A/B/L/Phi,
  data-carrying KB41 calibration face, domain 1..40 + 0 fallback, no claim
  outside); dom face + allb_nz Fixpoint (b-channel nonzero census over the
  domain, straddles_zero=false column re-checked EXACT in-tree); 12
  Examples (spot anchors A/B n=1,2,5 + L5/Phi5 + domain honesty + B5
  Hcoef@17 FIT + A5 Hcoef@17 TENSION - the honest non-claim).
- planb3_g1_g2_design.v (11 named): 2 Lemmas (qabs_inj_nat + inj_zabs_qabs
  bridges, proof-bridge class); planb3_dv Definition + dv_hp + dv_htri
  (data-carrying: the informative carrier with Hp AND Htri DISCHARGED by
  construction - the ec_epos_pos precedent honored); Section G2_DESIGN
  (xpi/xL slots + anchor Definition + 3 design-obligation faces + anchor
  one-consistency Lemma - born statements honestly unproven, the G2 3/4
  debts + the Hval slot); 1 hcoef17 face Definition (born, unproven - the
  N2c chain debt, the n=5 A-side tension certifies why).

## Promotion state
All four .vo born in-sandbox (零树写零 push): promotion to any canonical
location awaits the user's order. Consumer wiring (bridge_rateslot/
bridge_real/uncond_zz 35-line migration, tight_bound 0-line) NOT touched -
those are the (B)-migration downstream faces, outside this ask's three-
piece scope.
