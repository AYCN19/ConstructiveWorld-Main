(* ========================================================================= *)
(* Mission      : planB wave-1 piece (2/3) - the Hesc limb implementation:  *)
(*                the nescD/bracket chain adapted to the 2*theta' window     *)
(*                premise, chained through to the Hesc conclusion limb       *)
(*                (1 <= |A n * q + B n * p|).                                *)
(*                Structure: (a) the Route-A probe premise shape is cast     *)
(*                as an explicit positional premise pair S7 > 3/4,           *)
(*                S6 < 5/6 (QltT-carried); HONEST SUPPLY CENSUS: no tree     *)
(*                piece named S7/S6 or proving these bounds exists - the     *)
(*                routeA_probe_20261107 sandbox carries                     *)
(*                probe_hcage_detour_firststep.v (the Hcage-detour probe,    *)
(*                no theta' content), gen_probe.py and kb41m_asm_rb.json     *)
(*                only; a full-tree grep for S7/S6/(3/4)/(5/6) Q-bound       *)
(*                pairs in the escwin chain returns zero hits. The bounds    *)
(*                therefore enter as explicit premises (fail-loud), NOT as   *)
(*                claimed supply. (b) the window premise face 2*theta' <= 1  *)
(*                (the escwin limb-1 reading 2q(3/20)^n <= 1, nescD.v:390-  *)
(*                391) is cast at the nescD witness and proven EQUIVALENT   *)
(*                to the escwin limb-1 face both directions; (c) the Hesc   *)
(*                face is assembled at an ARBITRARY witness from the        *)
(*                window-derived limb 1 + the explicit limb 2 + the nescD   *)
(*                limb 3, so the window premise is load-bearing; (d) the    *)
(*                chain-through theorem extracts the nonvanishing limb      *)
(*                alongside the assembled face; (e) the nescD-supplied       *)
(*                (Route-A-free) twin closes the same face with the          *)
(*                unconditional window. The bracket unit's born faces       *)
(*                (slope certificate, q=1 anchor) are consumed as reuse      *)
(*                faces - these ARE in-tree supplies.                        *)
(* Dependencies : S02_CauchyComplete, piu_mu_criterion,                      *)
(*                piu_zz_ec_escwin_nescD (the N5 window unit: witness,       *)
(*                limb1_Q/limb3_Q, HescD face + supply contract),            *)
(*                piu_zz_ec_escwin_bracket (the N6'-b unit: slope cert,      *)
(*                q=1 anchor, Hcage draft faces); stdlib QArith, ZArith,     *)
(*                Arith, Lia, Qpower.                                        *)
(* References   : nescD.v:384-414 (the (D) HescD premise slot + supply      *)
(*                contract, KB41f P3 debt position), :293-345 (limb Q       *)
(*                supplies), :401-412 (of_window); bracket.v:159-185        *)
(*                (slope certificate, q=1 anchor, witness-forcing face);    *)
(*                e_carrier.v:633-642 (the Section EC Hesc slot the         *)
(*                adaptation feeds); KB41f P3 (the limb-2 p-adic clearing   *)
(*                gap debt, architecture unchanged); planB wave-1 workorder *)
(*                (the Route-A S7/S6 name-list - unresolvable in-tree,      *)
(*                registered in the header census above).                   *)
(* Constructivity: every named statement is Set-carried (piu_mu_QleT/ZleT/ *)
(*                QltT/and2, sigT, S02 QleT'); no Axiom, no Parameter, no   *)
(*                Admitted, no Abort; the S7/S6 premises are explicit       *)
(*                positional arguments (discharged shape), never global     *)
(*                assumptions; every named statement closes under the       *)
(*                global context. Path-A compliant (informative carriers).  *)
(* Build        : coqc -native-compiler no -q -Q . "" -Q <green9 cache> ""  *)
(*                planb2_hesc_limb_impl.v, Rocq 9.3.0, serial single lane   *)
(*                under cpu_guard_v3 (-TempLimit 98 -AllowG3), shot spacing *)
(*                >= 120 s; coqchk MUST carry -bytecode-compiler yes.       *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_ec_escwin_nescD.
Require Import piu_zz_ec_escwin_bracket.

(* ================================================================== *)
(* Section 1. The Route-A probe premise shape (explicit positional    *)
(*            premises; supply absence registered fail-loud).         *)
(* ================================================================== *)

(* The Route-A probe bound pair as named in the workorder: S7 > 3/4    *)
(* and S6 < 5/6. NO in-tree supply proves these bounds (census in the *)
(* header); they are carried as explicit positional premises of the    *)
(* adaptation theorems below - never discharged, never assumed         *)
(* globally.                                                           *)
Definition planb2_routeA_bounds (s7 s6 : Q) : Set :=
  piu_mu_and2 (piu_mu_QltT (3 # 4)%Q s7) (piu_mu_QltT s6 (5 # 6)%Q).

(* theta' at the nescD witness: theta'(q) = q * (3/20)^nescD(q) - the  *)
(* (D)-window residual whose doubled form is the window premise.       *)
Definition planb2_theta_at (q : nat) : Q :=
  inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat (piu_zz_ec_nescD q)).

(* the 2*theta' window premise face (QleT'-carried, vm_compute-        *)
(* decidable): 2 * theta' <= 1 - the escwin limb-1 reading             *)
(* 2q(3/20)^n <= 1 (nescD.v:390-391).                                  *)
Definition planb2_theta_window_face (t : Q) : Set :=
  S02_CauchyComplete.QleT' ((2 # 1) * t)%Q (1 # 1)%Q.

(* ================================================================== *)
(* Section 2. The adaptation: window premise <-> escwin limb 1        *)
(*            (both directions, so either supply feeds the chain).    *)
(* ================================================================== *)

Lemma planb2_window_from_limb1 : forall t : Q,
  piu_mu_QleT t (1 # 2)%Q -> planb2_theta_window_face t.
Proof.
  intros t H. destruct H as [H].
  apply S02_CauchyComplete.Qle_to_QleT'.
  assert (Hh : ((2 # 1) * t <= (2 # 1) * (1 # 2))%Q).
  { rewrite (Qmult_comm (2 # 1) t), (Qmult_comm (2 # 1) (1 # 2)).
    apply Qmult_le_compat_r; [exact H | unfold Qle; cbn; lia]. }
  assert (Hc2 : ((2 # 1) * (1 # 2))%Q == (1 # 1)%Q) by ring.
  rewrite Hc2 in Hh.
  exact Hh.
Qed.

Lemma planb2_limb1_from_window : forall t : Q,
  planb2_theta_window_face t -> piu_mu_QleT t (1 # 2)%Q.
Proof.
  intros t H.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ H) as H2.
  apply piu_mu_QleT_i.
  assert (Hh : ((1 # 2) * ((2 # 1) * t) <= (1 # 2) * (1 # 1))%Q).
  { rewrite (Qmult_comm (1 # 2) ((2 # 1) * t)),
      (Qmult_comm (1 # 2) (1 # 1)).
    apply Qmult_le_compat_r; [exact H2 | unfold Qle; cbn; lia]. }
  assert (Hc3 : ((1 # 2) * ((2 # 1) * t))%Q == t%Q) by ring.
  assert (Hc4 : ((1 # 2) * (1 # 1))%Q == (1 # 2)%Q) by ring.
  rewrite Hc3, Hc4 in Hh.
  exact Hh.
Qed.

(* the window face holds unconditionally at the nescD witness (the     *)
(* Route-A-free twin of the premise, from the N5 unit's limb-1).       *)
Lemma planb2_window_nescD : forall q : nat, (1 <= q)%nat ->
  planb2_theta_window_face (planb2_theta_at q).
Proof.
  intros q Hq. apply planb2_window_from_limb1.
  exact (piu_zz_ec_escwin_limb1_Q q Hq).
Qed.

(* ================================================================== *)
(* Section 3. The Hesc face assembled at an ARBITRARY witness (the    *)
(*            adaptation target: the window premise is load-bearing). *)
(* ================================================================== *)

Theorem planb2_hesc_face_of_window_general :
  forall (A B : nat -> Z) (p : Z) (q n : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n))
              (1 # 2)%Q ->
  piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)) ->
  piu_mu_QleT (piu_mu_epos (17 * n))
    (piu_zz_ec_kappaD * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat 7))%Q ->
  piu_zz_ec_HescD_face A B p q.
Proof.
  intros A B p q n Hq H1 H2 H3.
  exists n. apply piu_mu_and3_i; assumption.
Qed.

(* ================================================================== *)
(* Section 4. The chain-through: Route-A window premise + limb-2      *)
(*            premise -> the Hesc face AND the extracted conclusion   *)
(*            limb (1 <= |A n q + B n p|).                            *)
(* ================================================================== *)

Theorem planb2_hesc_conclusion_via_routeA :
  forall (A B : nat -> Z) (s7 s6 : Q) (p : Z) (q : nat), (1 <= q)%nat ->
  planb2_routeA_bounds s7 s6 ->
  planb2_theta_window_face (planb2_theta_at q) ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_mu_and2 (piu_zz_ec_HescD_face A B p q)
    (piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                              + B (piu_zz_ec_nescD q) * p))).
Proof.
  intros A B s7 s6 p q Hq Hbounds Hw H2. split.
  - apply (planb2_hesc_face_of_window_general A B p q (piu_zz_ec_nescD q) Hq).
    + (* limb 1 FROM the window premise (load-bearing) *)
      exact (planb2_limb1_from_window (planb2_theta_at q) Hw).
    + exact H2.
    + (* limb 3 from the N5 window unit *)
      exact (piu_zz_ec_escwin_limb3_Q q Hq).
  - (* the extracted nonvanishing limb *)
    exact H2.
Qed.

(* the Route-A-free twin: the window supplied by the N5 unit itself. *)
Theorem planb2_hesc_conclusion_nescD :
  forall (A B : nat -> Z) (p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_mu_and2 (piu_zz_ec_HescD_face A B p q)
    (piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                              + B (piu_zz_ec_nescD q) * p))).
Proof.
  intros A B p q Hq H2. split.
  - exact (piu_zz_ec_HescD_of_window A B p q Hq H2).
  - exact H2.
Qed.

(* the of_window contract face re-exported at the implementation level *)
(* (the KB41f P3 debt position is unchanged: limb 2 stays the explicit *)
(* premise; this piece adds the window adaptation AROUND it).          *)
Theorem planb2_hesc_contract_pinned :
  forall (A B : nat -> Z) (p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_zz_ec_HescD_face A B p q.
Proof. exact piu_zz_ec_HescD_of_window. Qed.

(* ================================================================== *)
(* Section 5. Numeric spot faces and the bracket-unit reuse faces.    *)
(* ================================================================== *)

(* the window face at q = 1 computes EXACT: 2*1*(3/20)^1 = 3/10 <= 1. *)
Example planb2_q1_window_face :
  planb2_theta_window_face (planb2_theta_at 1).
Proof.
  unfold planb2_theta_window_face, planb2_theta_at.
  apply S02_CauchyComplete.Qle_to_QleT'.
  vm_compute. intro Hc. discriminate Hc.
Qed.

(* reuse face: the N6'-b slope certificate consumed verbatim (this IS  *)
(* an in-tree supply, unlike the S7/S6 pair). *)
Example planb2_slope_reuse : (20 ^ 7 > 2 ^ 17 * 3 ^ 7)%Z.
Proof. exact piu_zz_ec_slope_cert. Qed.

(* reuse face: the q = 1 witness-forcing anchor consumed verbatim. *)
Example planb2_q1_anchor_reuse : (2 ^ 17 <= 35831808 < 2 ^ 34)%Z.
Proof. exact piu_zz_ec_q1_anchor. Qed.

(* the witness landing spot at the first two heights (vm_compute      *)
(* anchors of the adapted chain's witness). *)
Example planb2_witness_spots :
  piu_zz_ec_nescD 1 = 1%nat /\ piu_zz_ec_nescD 2 = 1%nat.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(* Section 6. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb2_window_from_limb1.
Print Assumptions planb2_limb1_from_window.
Print Assumptions planb2_window_nescD.
Print Assumptions planb2_hesc_face_of_window_general.
Print Assumptions planb2_hesc_conclusion_via_routeA.
Print Assumptions planb2_hesc_conclusion_nescD.
Print Assumptions planb2_hesc_contract_pinned.
Print Assumptions planb2_q1_window_face.
Print Assumptions planb2_slope_reuse.
Print Assumptions planb2_q1_anchor_reuse.
Print Assumptions planb2_witness_spots.
