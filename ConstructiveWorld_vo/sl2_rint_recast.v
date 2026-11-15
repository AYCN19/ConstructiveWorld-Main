(* sl2_rint_recast.v - SL2 table-side machine evidence and the recast   *)
(* route registration for the |I_n| decay ticket.                        *)
(* Mission. Three parts. (1) The x = 1 cage refutation: 40 negative     *)
(*  anchors, the (13/400)^n cage dead at every frozen-table index on    *)
(*  the x = 1 carrier (machine support for the fourslots hcage-slot     *)
(*  carrier swap, see References). (2) The 3/20-band falsification:     *)
(*  the 14 failing indices pinned at the anchor carrier (the survey     *)
(*  band row reproduced first-hand; the 3/20 face itself is forbidden   *)
(*  to pin, slot draft 2.2). (3) The envelope route: the U(a,b)         *)
(*  carrier of the slot-draft route note, its positivity lemma, and     *)
(*  the statement-only decay target (route debt, not claimed).          *)
(* Dependencies. Slot-draft section 0 block plus sl2_anchor_carrier    *)
(*  (the pinned anchor carrier).                                       *)
(* References. [1] slot draft SL12 sections 2.2-2.3. [2] CARRIER-SWAP  *)
(*  ANNOTATION (interface-change obligation): the fourslots hcage-slot *)
(*  face (planb4_l4_hcage_slot, x = 1 l2_dv carrier, (13/400)^n) is    *)
(*  NOT re-cast here and must not be discharged; its carrier swap      *)
(*  belongs to the landing step with the migration ledger (this        *)
(*  sandbox ticket does not touch the tree); the Section 1 anchors     *)
(*  are the machine support: the old face is dead 40/40 on the frozen  *)
(*  tables. [3] Survey rows: Hval-direct passes 40/40 (see             *)
(*  sl2_anchor_carrier.v), 3/20 fails 14/40 (Section 2), the 13/400    *)
(*  cage fails 40/40 (Section 1); the cited worst-index cage figure is *)
(*  not reproduced under this seat's ratio normalization (exact ratio  *)
(*  peaks at index 40); unresolved, non-blocking. Provenance ledger    *)
(*  kept with the seat receipt, not in this file. Constructivity:      *)
(*  postulate-free, Set-carried negative pins, zero new Prop           *)
(*  statements; envelope positivity Defined. Build: coqc               *)
(*  -native-compiler no -q (Rocq 9.3.0, E952 form; needs               *)
(*  sl2_anchor_carrier.vo on the load path). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_e_carrier.
Require Import planb4_g1_witness.
Require Import planb4_l2_dv_cast.
Require Import planb3_g1_g2_design.
Require Import planb1_hcage_zerotouch_prescription.
Require Import planb3_g1_calib.
Require Import sl2_anchor_carrier.

(* ==== Section 1: the x = 1 cage refutation over the frozen tables.    ==== *)

(* l2_dv = planb3_dv = |a + b| (the x = 1 anchor carrier). The cage    *)
(* face would demand |A_n + B_n| <= (13/400)^n for all n; each anchor  *)
(* below pins the failure at one frozen-table index (exact, vm_compute; *)
(* the full set is 40/40, the survey's falsified-cage row). *)
Example sl12_cage_dead_1 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 1%nat))
    (l2_dv (planb3_g1_A 1%nat) (planb3_g1_B 1%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_2 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 2%nat))
    (l2_dv (planb3_g1_A 2%nat) (planb3_g1_B 2%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_3 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 3%nat))
    (l2_dv (planb3_g1_A 3%nat) (planb3_g1_B 3%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_4 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 4%nat))
    (l2_dv (planb3_g1_A 4%nat) (planb3_g1_B 4%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_5 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 5%nat))
    (l2_dv (planb3_g1_A 5%nat) (planb3_g1_B 5%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_6 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 6%nat))
    (l2_dv (planb3_g1_A 6%nat) (planb3_g1_B 6%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_7 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 7%nat))
    (l2_dv (planb3_g1_A 7%nat) (planb3_g1_B 7%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_8 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 8%nat))
    (l2_dv (planb3_g1_A 8%nat) (planb3_g1_B 8%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_9 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 9%nat))
    (l2_dv (planb3_g1_A 9%nat) (planb3_g1_B 9%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_10 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 10%nat))
    (l2_dv (planb3_g1_A 10%nat) (planb3_g1_B 10%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_11 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 11%nat))
    (l2_dv (planb3_g1_A 11%nat) (planb3_g1_B 11%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_12 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 12%nat))
    (l2_dv (planb3_g1_A 12%nat) (planb3_g1_B 12%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_13 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 13%nat))
    (l2_dv (planb3_g1_A 13%nat) (planb3_g1_B 13%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_14 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 14%nat))
    (l2_dv (planb3_g1_A 14%nat) (planb3_g1_B 14%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_15 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 15%nat))
    (l2_dv (planb3_g1_A 15%nat) (planb3_g1_B 15%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_16 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 16%nat))
    (l2_dv (planb3_g1_A 16%nat) (planb3_g1_B 16%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_17 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 17%nat))
    (l2_dv (planb3_g1_A 17%nat) (planb3_g1_B 17%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_18 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 18%nat))
    (l2_dv (planb3_g1_A 18%nat) (planb3_g1_B 18%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_19 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 19%nat))
    (l2_dv (planb3_g1_A 19%nat) (planb3_g1_B 19%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_20 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 20%nat))
    (l2_dv (planb3_g1_A 20%nat) (planb3_g1_B 20%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_21 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 21%nat))
    (l2_dv (planb3_g1_A 21%nat) (planb3_g1_B 21%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_22 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 22%nat))
    (l2_dv (planb3_g1_A 22%nat) (planb3_g1_B 22%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_23 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 23%nat))
    (l2_dv (planb3_g1_A 23%nat) (planb3_g1_B 23%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_24 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 24%nat))
    (l2_dv (planb3_g1_A 24%nat) (planb3_g1_B 24%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_25 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 25%nat))
    (l2_dv (planb3_g1_A 25%nat) (planb3_g1_B 25%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_26 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 26%nat))
    (l2_dv (planb3_g1_A 26%nat) (planb3_g1_B 26%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_27 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 27%nat))
    (l2_dv (planb3_g1_A 27%nat) (planb3_g1_B 27%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_28 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 28%nat))
    (l2_dv (planb3_g1_A 28%nat) (planb3_g1_B 28%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_29 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 29%nat))
    (l2_dv (planb3_g1_A 29%nat) (planb3_g1_B 29%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_30 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 30%nat))
    (l2_dv (planb3_g1_A 30%nat) (planb3_g1_B 30%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_31 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 31%nat))
    (l2_dv (planb3_g1_A 31%nat) (planb3_g1_B 31%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_32 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 32%nat))
    (l2_dv (planb3_g1_A 32%nat) (planb3_g1_B 32%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_33 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 33%nat))
    (l2_dv (planb3_g1_A 33%nat) (planb3_g1_B 33%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_34 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 34%nat))
    (l2_dv (planb3_g1_A 34%nat) (planb3_g1_B 34%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_35 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 35%nat))
    (l2_dv (planb3_g1_A 35%nat) (planb3_g1_B 35%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_36 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 36%nat))
    (l2_dv (planb3_g1_A 36%nat) (planb3_g1_B 36%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_37 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 37%nat))
    (l2_dv (planb3_g1_A 37%nat) (planb3_g1_B 37%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_38 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 38%nat))
    (l2_dv (planb3_g1_A 38%nat) (planb3_g1_B 38%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_39 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 39%nat))
    (l2_dv (planb3_g1_A 39%nat) (planb3_g1_B 39%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_cage_dead_40 :
  piu_mu_QltT (Qpower (13 # 400)%Q (Z.of_nat 40%nat))
    (l2_dv (planb3_g1_A 40%nat) (planb3_g1_B 40%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

(* ==== Section 2: the 3/20-band falsification at the anchor carrier.   ==== *)

(* The decay face at crho = 3/20 would demand |A_n + B_n*xpi| <=      *)
(* (3/20)^n; each anchor below pins the failure at one of the 14      *)
(* failing indices over n = 1..40 (exact, vm_compute; the survey      *)
(* band row reproduced first-hand at the pinned anchor carrier). The  *)
(* 3/20 decay face itself is FORBIDDEN to pin (slot draft 2.2). *)
Example sl12_band320_dead_5 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 5%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 5%nat) (planb3_g1_B 5%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_8 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 8%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 8%nat) (planb3_g1_B 8%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_13 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 13%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 13%nat) (planb3_g1_B 13%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_14 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 14%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 14%nat) (planb3_g1_B 14%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_16 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 16%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 16%nat) (planb3_g1_B 16%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_20 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 20%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 20%nat) (planb3_g1_B 20%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_21 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 21%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 21%nat) (planb3_g1_B 21%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_23 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 23%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 23%nat) (planb3_g1_B 23%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_26 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 26%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 26%nat) (planb3_g1_B 26%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_28 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 28%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 28%nat) (planb3_g1_B 28%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_29 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 29%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 29%nat) (planb3_g1_B 29%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_32 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 32%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 32%nat) (planb3_g1_B 32%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_33 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 33%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 33%nat) (planb3_g1_B 33%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

Example sl12_band320_dead_35 :
  piu_mu_QltT (Qpower (3 # 20)%Q (Z.of_nat 35%nat))
    (sl12_dval_pi sl12_xpi_pi_bracket (planb3_g1_A 35%nat) (planb3_g1_B 35%nat)).
Proof. apply piu_mu_QltT_i. vm_compute. reflexivity. Defined.

(* ==== Section 3: the envelope-carrier route registration.             ==== *)

(* The envelope carrier of the slot-draft route note:                 *)
(*   U(a, b) = |a + b*xL_m| + |b|*e_m,                                 *)
(* with the xL-bridge midpoint slot and the envelope error slot kept  *)
(* as parameters. The decay target below is the route debt -          *)
(* statement only, NOT claimed (the transfer from the xL convergence  *)
(* face is the registered route item). *)
Section SL12_ENVELOPE.

Context (xLm em : Q).

Definition sl12_env_U (a b : Z) : Q :=
  Qabs (inject_Z a + inject_Z b * xLm)%Q + Qabs (inject_Z b) * em.

(* the envelope-route decay target over the frozen tables (route      *)
(* debt, statement only). *)
Definition sl12_env_decay_face (crho : Q) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (sl12_env_U (planb3_g1_A n) (planb3_g1_B n))
      (Qpower crho (Z.of_nat n)).

End SL12_ENVELOPE.

(* positivity of the envelope carrier on the nonneg error half-line    *)
(* (em >= 0): the sum of two nonneg terms. *)
Lemma sl12_env_hp :
  forall (xLm em : Q), (0 <= em)%Q ->
  forall (a b : Z), piu_mu_QleT 0 (sl12_env_U xLm em a b).
Proof.
  intros xLm em Hem a b. apply piu_mu_QleT_i. unfold sl12_env_U.
  assert (Hb : (0 <= Qabs (inject_Z b) * em)%Q).
  { apply Qmult_le_0_compat; [apply Qabs_nonneg | exact Hem]. }
  pose proof (Qabs_nonneg (inject_Z a + inject_Z b * xLm)%Q) as Ha.
  assert (Hsum : (0 + 0 <= Qabs (inject_Z a + inject_Z b * xLm)
                          + Qabs (inject_Z b) * em)%Q).
  { apply Qplus_le_compat; assumption. }
  rewrite Qplus_0_l in Hsum. exact Hsum.
Defined.

(* ==== Section 4: assumption audit. ==== *)

Print Assumptions sl12_env_U.
Print Assumptions sl12_env_decay_face.
Print Assumptions sl12_env_hp.
Print Assumptions sl12_cage_dead_1.
Print Assumptions sl12_cage_dead_2.
Print Assumptions sl12_cage_dead_3.
Print Assumptions sl12_cage_dead_4.
Print Assumptions sl12_cage_dead_5.
Print Assumptions sl12_cage_dead_6.
Print Assumptions sl12_cage_dead_7.
Print Assumptions sl12_cage_dead_8.
Print Assumptions sl12_cage_dead_9.
Print Assumptions sl12_cage_dead_10.
Print Assumptions sl12_cage_dead_11.
Print Assumptions sl12_cage_dead_12.
Print Assumptions sl12_cage_dead_13.
Print Assumptions sl12_cage_dead_14.
Print Assumptions sl12_cage_dead_15.
Print Assumptions sl12_cage_dead_16.
Print Assumptions sl12_cage_dead_17.
Print Assumptions sl12_cage_dead_18.
Print Assumptions sl12_cage_dead_19.
Print Assumptions sl12_cage_dead_20.
Print Assumptions sl12_cage_dead_21.
Print Assumptions sl12_cage_dead_22.
Print Assumptions sl12_cage_dead_23.
Print Assumptions sl12_cage_dead_24.
Print Assumptions sl12_cage_dead_25.
Print Assumptions sl12_cage_dead_26.
Print Assumptions sl12_cage_dead_27.
Print Assumptions sl12_cage_dead_28.
Print Assumptions sl12_cage_dead_29.
Print Assumptions sl12_cage_dead_30.
Print Assumptions sl12_cage_dead_31.
Print Assumptions sl12_cage_dead_32.
Print Assumptions sl12_cage_dead_33.
Print Assumptions sl12_cage_dead_34.
Print Assumptions sl12_cage_dead_35.
Print Assumptions sl12_cage_dead_36.
Print Assumptions sl12_cage_dead_37.
Print Assumptions sl12_cage_dead_38.
Print Assumptions sl12_cage_dead_39.
Print Assumptions sl12_cage_dead_40.
Print Assumptions sl12_band320_dead_5.
Print Assumptions sl12_band320_dead_8.
Print Assumptions sl12_band320_dead_13.
Print Assumptions sl12_band320_dead_14.
Print Assumptions sl12_band320_dead_16.
Print Assumptions sl12_band320_dead_20.
Print Assumptions sl12_band320_dead_21.
Print Assumptions sl12_band320_dead_23.
Print Assumptions sl12_band320_dead_26.
Print Assumptions sl12_band320_dead_28.
Print Assumptions sl12_band320_dead_29.
Print Assumptions sl12_band320_dead_32.
Print Assumptions sl12_band320_dead_33.
Print Assumptions sl12_band320_dead_35.
Print Assumptions sl12_xpi_above_lb.
Print Assumptions sl12_xpi_below_ub.
