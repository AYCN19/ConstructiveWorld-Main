(* ConstructiveWorld-Main - numeric certificate anchors of the Pade
   tail positivity slice. *)

(** * UpReqPadeTailPos_cert: rational cross-checks of the tail
      positivity slice.

    Mission.  The seventeen numeric anchors of the tail positivity
      slice, moved verbatim under the certificate separation rule:
      the closed values of beta_m at n = 1 (m = 0,1,2), the anchor
      family ptp_beta over n = 1,2 and small m, the leading-term
      closed forms, the polynomial-identity values at y = 1/2, and
      the carrier sentinels of the n = 1 tail identity (both sides
      -(7/512)).  Each proof is a single vm_compute reduction,
      followed where needed by the Qeq unfolding and a linear check.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,
      UpReqPadeQLeg, UpReqPadeExp, the sibling pieces
      UpReqPadeTailPos_a and UpReqPadeTailPos_b; Stdlib QArith,
      Arith, Lia, Setoid.
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeTailPos; companion of the five edition pieces
      UpReqPadeTailPos_a through UpReqPadeTailPos_e.
    Constructivity.  Pure Set-level rational equalities decided by
      machine reduction; no axioms; every audited name is Closed
      under the global context.
    Build.  coqc -q -native-compiler no with the l0_local face plus
      the node build face, Coq 9.3.0, wrapped by the temperature
      guard.
*)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
Require Import UpReqPadeTailPos_a.
Require Import UpReqPadeTailPos_b.
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* beta anchors at n = 1 *)
Lemma pbp_beta_1_0 : pbp_beta 1%nat 0%nat == (1#6)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_1 : pbp_beta 1%nat 1%nat == (1#12)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_2 : pbp_beta 1%nat 2%nat == (1#20)%Q.
Proof. vm_compute. reflexivity. Qed.

(* beta anchor family over n = 1,2 *)
Lemma ptp_beta_n1_0 : ptp_beta 1 0%nat == (1#6).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_1 : ptp_beta 1 1%nat == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_2 : ptp_beta 1 2%nat == (1#20).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_3 : ptp_beta 1 3%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_4 : ptp_beta 1 4%nat == (1#42).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_0 : ptp_beta 2 0%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_1 : ptp_beta 2 1%nat == (1#60).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_2 : ptp_beta 2 2%nat == (1#105).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* leading-term closed form instances *)
Lemma ptp_beta_n1_first : ptp_beta 1 0%nat / q_fact 2 == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_first : ptp_beta 2 0%nat / q_fact 4 == (1#720).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* polynomial identity values at y = 1/2 *)
Lemma ptp_sentinel_n1_half :
  exp_partial 4 (1#2) * pade_den 1 (1#2) - pade_num 1 (1#2) == - (7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_sentinel_n2_half :
  exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2)
  == (1#720)*(1#32) + (1#1440)*(1#64) + (1#8640)*(1#256).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* carrier sentinels of the n = 1 tail identity *)
Lemma ptp_tail_sentinel_F_half : ptp_F 1 (1#2) == -(7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_sentinel_G_half : ptp_G 1 (1#2) == -(7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.
