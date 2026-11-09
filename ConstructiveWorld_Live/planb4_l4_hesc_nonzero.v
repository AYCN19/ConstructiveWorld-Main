(* ConstructiveWorld-Main - planB wave-1 piece 4: L4 engineering adaptation
   face for the Hesc limb-2 nonvanishing slot (UPSTREAM-WAITING FORM). *)

(** * planb4_l4_hesc_nonzero: the L4 lane deliverable over the nescD chain.

    Mission.  The L4 lane (workorder 01, section 1-L4) targeted the KB41f
      P3 debt: closing the nonvanishing premise of the escwin_nescD chain
      (limb 2) by adapting the padic_clearing integer core into
      planb2_hesc_limb_impl.  The 2026-11-09 read-only survey (three .v
      masters + KB41h receipt + workorder + Route-A survey) escalated
      under the math-wall clause with a three-column report; the ruling
      re-declared the lane as the UPSTREAM-WAITING FORM: the nontrivial
      limb-2 supply body (G1 slices 2-3 concrete (A,B) casting + ZZ2020
      Lemma-2-v2 body + B-side growth account) is owned by upstream lanes
      and is NOT recast here - no downgrade, no Admitted, no assumption
      slots smuggled.  What THIS piece delivers is the engineering
      adaptation face, three parts:
      (a) the nescD THREE-LIMB ASSEMBLY at the pinned witness
          n = piu_zz_ec_nescD q, as a bare sigT readout, with the
          window-supplied limbs 1+3 (N5 unit) and limb 2 as the explicit
          premise - the debt position carried honestly, fail-loud;
      (b) the CONTRACT TRANSMISSION faces re-pinned at lane level
          (piu_zz_ec_HescD_of_window / planb2 conclusion twin verbatim)
          plus the three limb PROJECTION lemmas out of the assembled
          HescD face (new: L6 consumers read limbs out, not just in);
      (c) the SPOT ARITHMETIC KERNEL faces: window spot certificates at
          q = 1, 2 (born faces consumed verbatim) and q = 3 (new in-tree
          point), and the zzm1b layer-2 nonvanishing arithmetic core
          (N(-5) = 5^{3n} * 2^{7n-1} <> 0, n = 1 anchor) consumed
          verbatim - the in-tree arithmetic kernel of the limb-2 body,
          whose Laurent assembly stays upstream (zzm1b slices 2-3).
    Upstream-waiting registration (honest, per ruling).  The limb-2
      nonvanishing BODY = upstream: (i) G1 concrete A,B : nat -> Z
      casting (zero in tree; kernel_sum piu_zz_Aj is the Q-typed moment
      face, zzm1b carries n=1..6 literal tables; (A_n,B_n) extraction =
      zzm slices 2-3, in progress in the L1 lane, merge point = L6);
      (ii) ZZ2020 Lemma 2 v2 body (p | j -> p | A_j) = constants.v
      section 7 statement-only (v1 T(m) claim retracted by the authors;
      padic_clearing consumes it as the Hclear hypothesis slot);
      (iii) B-side growth account (sigma_decay.v:68-72/:86, G4) needed
      for the pinned-witness root-line dodge.  Until those land, limb 2
      is transmitted as an explicit premise - exactly the KB41f P3 debt
      position, unchanged by this piece.
    Dependencies.  S02_CauchyComplete; piu_mu_criterion;
      piu_zz_ec_escwin_nescD; piu_zz_ec_escwin_bracket;
      planb2_hesc_limb_impl; zzm1b_linform_bridge; stdlib QArith.ZArith
      Arith Lia.
    Constructivity.  Every named statement is carried in Set (sigT /
      piu_mu_and2 / piu_mu_and3 / piu_mu_QleT / piu_mu_ZleT / zzId /
      Type-level and for the spot conjunctions, escwin born precedent);
      propositional reasoning only inside proofs; statements touch no
      existing name or type (statement faces zero-touch); all proofs are
      admission-free and close under the global context.
    Build.  coqc (opam93 9.3.0) wrapped by 50_toolkit/cpu_guard_v3.ps1
      (-AllowG3 -TempLimit 93 -LoadLimit 60 -CoreN 2), in
      ConstructiveWorld_Live:
      coqc -native-compiler no -q -Q . "" planb4_l4_hesc_nonzero.v
    References.  escwin_nescD.v:388-414 (face + window contract);
      planb2_hesc_limb_impl.v:111-173 (adaptation + conclusion twins);
      padic_clearing.v:210/:225/:257-274/:347-380/:782-912 (integer core);
      constants.v:501-529 (three ZZ lemmas, statement-only);
      zzm1b_linform_bridge.v:237-283 (nonvanishing arithmetic core). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_ec_escwin_nescD.
Require Import piu_zz_ec_escwin_bracket.
Require Import planb2_hesc_limb_impl.
Require Import zzm1_gauss.
Require Import zzm1b_linform_bridge.

(* ================================================================== *)
(* Section 1. The nescD three-limb assembly (bare sigT readout at the *)
(*            pinned witness; limb 2 explicit, fail-loud).            *)
(* ================================================================== *)

(* The assembly face: EXISTS witness n (supplied = piu_zz_ec_nescD q)  *)
(* with all three HescD limbs.  Limb 1 + limb 3 come from the N5 window*)
(* unit (piu_zz_ec_escwin_limb1_Q / limb3_Q); limb 2 - the nonvanishing *)
(* limb, KB41f P3 debt - enters as the explicit positional premise.     *)
Theorem planb4_three_limbs_at_nescD :
  forall (A B : nat -> Z) (p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n))
                  (1 # 2)%Q)
    (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
    (piu_mu_QleT (piu_mu_epos (17 * n))
      (piu_zz_ec_kappaD * Qpower (inject_Z (Z.of_nat q))
         (Z.of_nat 7))%Q)).
Proof.
  intros A B p q Hq H2.
  exists (piu_zz_ec_nescD q). apply piu_mu_and3_i.
  - exact (piu_zz_ec_escwin_limb1_Q q Hq).
  - exact H2.
  - exact (piu_zz_ec_escwin_limb3_Q q Hq).
Qed.

(* ================================================================== *)
(* Section 2. Limb projections out of the assembled HescD face (the   *)
(*            L6 consumption direction: read limbs out, not just in). *)
(* ================================================================== *)

Definition planb4_limb1_at (A B : nat -> Z) (p : Z) (q : nat) : Set :=
  sigT (fun n : nat => piu_mu_QleT
    (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n)) (1 # 2)%Q).

Definition planb4_limb2_at (A B : nat -> Z) (p : Z) (q : nat) : Set :=
  sigT (fun n : nat => piu_mu_ZleT 1
    (Z.abs (A n * Z.of_nat q + B n * p))).

Definition planb4_limb3_at (A B : nat -> Z) (p : Z) (q : nat) : Set :=
  sigT (fun n : nat => piu_mu_QleT (piu_mu_epos (17 * n))
    (piu_zz_ec_kappaD * Qpower (inject_Z (Z.of_nat q))
       (Z.of_nat 7))%Q).

Lemma planb4_face_limb1 : forall (A B : nat -> Z) (p : Z) (q : nat),
  piu_zz_ec_HescD_face A B p q -> planb4_limb1_at A B p q.
Proof.
  intros A B p q [n H]. destruct H as [H1 _]. exists n. exact H1.
Qed.

Lemma planb4_face_limb2 : forall (A B : nat -> Z) (p : Z) (q : nat),
  piu_zz_ec_HescD_face A B p q -> planb4_limb2_at A B p q.
Proof.
  intros A B p q [n H]. destruct H as [_ H2 _]. exists n. exact H2.
Qed.

Lemma planb4_face_limb3 : forall (A B : nat -> Z) (p : Z) (q : nat),
  piu_zz_ec_HescD_face A B p q -> planb4_limb3_at A B p q.
Proof.
  intros A B p q [n H]. destruct H as [_ _ H3]. exists n. exact H3.
Qed.

(* ================================================================== *)
(* Section 3. Contract transmission faces (the KB41f P3 debt position *)
(*            re-pinned at lane level; unchanged by this piece).      *)
(* ================================================================== *)

Theorem planb4_contract_transmit :
  forall (A B : nat -> Z) (p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_zz_ec_HescD_face A B p q.
Proof. exact piu_zz_ec_HescD_of_window. Qed.

Theorem planb4_conclusion_limb_via_nescD :
  forall (A B : nat -> Z) (p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_mu_and2 (piu_zz_ec_HescD_face A B p q)
    (piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                              + B (piu_zz_ec_nescD q) * p))).
Proof. exact planb2_hesc_conclusion_nescD. Qed.

(* ================================================================== *)
(* Section 4. Spot resolution faces: the window spot certificates at  *)
(*            q = 1..3 feed the contract at the same pinned witness.  *)
(* ================================================================== *)

(* spot resolution at q = 1 (the born q = 1 anchor band): the contract *)
(* closes the full face from the limb-2 premise alone. *)
Theorem planb4_spot_resolution_q1 :
  forall (A B : nat -> Z) (p : Z),
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD 1) * Z.of_nat 1
                          + B (piu_zz_ec_nescD 1) * p)) ->
  piu_mu_and2 (piu_zz_ec_HescD_face A B p 1)
    (piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD 1) * Z.of_nat 1
                              + B (piu_zz_ec_nescD 1) * p))).
Proof.
  intros A B p H2.
  exact (planb2_hesc_conclusion_nescD A B p 1 (le_n 1) H2).
Qed.

(* spot resolution at q = 2 (the born q = 2 discrimination band). *)
Theorem planb4_spot_resolution_q2 :
  forall (A B : nat -> Z) (p : Z),
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD 2) * Z.of_nat 2
                          + B (piu_zz_ec_nescD 2) * p)) ->
  piu_mu_and2 (piu_zz_ec_HescD_face A B p 2)
    (piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD 2) * Z.of_nat 2
                              + B (piu_zz_ec_nescD 2) * p))).
Proof.
  intros A B p H2.
  assert (Hq : (1 <= 2)%nat) by lia.
  exact (planb2_hesc_conclusion_nescD A B p 2 Hq H2).
Qed.

(* spot resolution at q = 3 (beyond the born q = 1/2 faces; the N5     *)
(* bite-shape window certificates are recomputed in-tree at q = 3). *)
Theorem planb4_spot_resolution_q3 :
  forall (A B : nat -> Z) (p : Z),
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD 3) * Z.of_nat 3
                          + B (piu_zz_ec_nescD 3) * p)) ->
  piu_mu_and2 (piu_zz_ec_HescD_face A B p 3)
    (piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD 3) * Z.of_nat 3
                              + B (piu_zz_ec_nescD 3) * p))).
Proof.
  intros A B p H2.
  assert (Hq : (1 <= 3)%nat) by lia.
  exact (planb2_hesc_conclusion_nescD A B p 3 Hq H2).
Qed.

(* ================================================================== *)
(* Section 5. Spot arithmetic kernel faces (window spots + the zzm1b  *)
(*            nonvanishing arithmetic core, consumed verbatim).       *)
(* ================================================================== *)

(* window spot at q = 3: new in-tree point (born q = 1 at escwin:453,  *)
(* q = 2 at escwin:444; q = 3 recomputed here in the same bite shape). *)
Lemma planb4_window_spot_q3 :
  (2 * 3 * 3 ^ piu_zz_ec_nescD 3 <= 20 ^ piu_zz_ec_nescD 3)%nat
  /\ (2 ^ (Z.of_nat (17 * piu_zz_ec_nescD 3)) <= 35831808 * 3 ^ 7)%Z.
Proof. split; vm_compute; [lia | discriminate]. Qed.

(* window spots at q = 1 and q = 2: born faces consumed verbatim. *)
Example planb4_window_spot_q1_reuse :
  (2 * 1 * 3 ^ piu_zz_ec_nescD 1 <= 20 ^ piu_zz_ec_nescD 1)%nat
  /\ (2 ^ (Z.of_nat (17 * piu_zz_ec_nescD 1)) <= 35831808 * 1 ^ 7)%Z.
Proof. exact piu_zz_ec_nescD_accepts_q1. Qed.

Example planb4_window_spot_q2_reuse :
  (2 * 2 * 3 ^ piu_zz_ec_nescD 2 <= 20 ^ piu_zz_ec_nescD 2)%nat
  /\ (2 ^ (Z.of_nat (17 * piu_zz_ec_nescD 2)) <= 35831808 * 2 ^ 7)%Z.
Proof. exact piu_zz_ec_nescD_accepts_q2. Qed.

(* the zzm1b layer-2 nonvanishing ARITHMETIC CORE (zzm1b:237-283):     *)
(* N(-5) = 5 * 4000^(2n) = 5^{3n} * 2^{7n-1} <> 0 - the leading-       *)
(* Laurent-coefficient kernel of the limb-2 body.  The Laurent         *)
(* assembly that lifts this kernel to the linear-form coefficients     *)
(* stays UPSTREAM (zzm slices 2-3, L1 lane); this piece transmits the  *)
(* born kernel faces verbatim, n = 1 anchors.                          *)
Example planb4_nz_core_n1 : zzId (Z.eqb ((5 * 4000 ^ 2)%Z) (80000000)%Z) true.
Proof. exact zz_nz_core_1. Qed.

Example planb4_nz_closed_n1 : zzId (Z.eqb ((5 ^ 3 * 2 ^ 6)%Z) (8000)%Z) true.
Proof. exact zz_closed_1. Qed.

(* ================================================================== *)
(* Section 6. Assumption audit (expected: all Closed under the global *)
(*            context; the upstream-waiting form carries no axioms).  *)
(* ================================================================== *)

Print Assumptions planb4_three_limbs_at_nescD.
Print Assumptions planb4_face_limb1.
Print Assumptions planb4_face_limb2.
Print Assumptions planb4_face_limb3.
Print Assumptions planb4_contract_transmit.
Print Assumptions planb4_conclusion_limb_via_nescD.
Print Assumptions planb4_spot_resolution_q1.
Print Assumptions planb4_spot_resolution_q2.
Print Assumptions planb4_spot_resolution_q3.
Print Assumptions planb4_window_spot_q3.
Print Assumptions planb4_window_spot_q1_reuse.
Print Assumptions planb4_window_spot_q2_reuse.
Print Assumptions planb4_nz_core_n1.
Print Assumptions planb4_nz_closed_n1.
