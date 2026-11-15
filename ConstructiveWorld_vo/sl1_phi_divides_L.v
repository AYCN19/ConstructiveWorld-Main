(* sl1_phi_divides_L.v - the Phi-window product divides the lcm band.
   Ticket: SL12 ticket SL1 (psi band + Phi window construction seat).
   Mission: supply the divisibility bridge the slot draft flags as the
   supply-side prerequisite of the main L_n face: planb4_Phi n divides
   planb4_L n for every n, with a Set-carried quotient witness, the
   exact-quotient identity lifted to Q, and positivity faces. The
   route reuses the padic-clearing machine (zz_prodf_divides,
   zz_Pn_bounded, zz_j_div_lcm_P, zz_prodf_pos) and connects the two
   lcm/product encodings by extensionality lemmas, so the planb4 faces
   inherit theorems B7-B9 of the ZZ2020 Lemma-3 chain verbatim.
   Inventory: 1 Theorem (the sigT/Bid divisibility witness) + 14
   auxiliary lemmas, all Defined.
   Dependencies: piu_zz_padic_clearing; planb4_g1_witness;
   S02_CauchyComplete; stdlib ZArith, Znumtheory, QArith, Qpower,
   List, Lia.
   References: slot statement draft SL12 section 1.1 note; ZZ2020
   Lemma 3 chain realized as theorems B7-B9 in piu_zz_padic_clearing;
   ground-truth table tools/sl1_ground_truth.py (Phi | L over 0..600).
   Constructivity: the witness is sigT over Bid (Set end to end); zero
   global assumptions; lia only on nat/Z linear side conditions inside
   bodies, never as a closer.
   Build: coqc -native-compiler no -q -Q world "" -Q out_sl1 ""
   sl1_phi_divides_L.v (E952 script form; independent of the faces
   unit). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
From Stdlib Require Import Znumtheory.
Import ListNotations.
Require Import S02_CauchyComplete.
Require Import piu_zz_padic_clearing.
Require Import planb4_g1_witness.

(* ==== Section 1: the two lcm encodings agree ==== *)

Lemma sl1_lcm_upto_range_eq :
  forall K : nat, zz_lcm_range K = planb4_lcm_upto K.
Proof.
  intro K. induction K as [|K IH].
  - reflexivity.
  - cbn [zz_lcm_range].
    replace (planb4_lcm_upto (S K))
      with (Z.lcm (planb4_lcm_upto K) (Z.of_nat (S K))).
    2:{ unfold planb4_lcm_upto.
        rewrite seq_S, map_app, fold_left_app.
        cbn [map fold_left]. reflexivity. }
    rewrite IH. reflexivity.
Defined.

(* ==== Section 2: the prodf recursion equals the filtered fold ==== *)

Definition sl1_prodf_fold (n K : nat) : Z :=
  fold_right (fun p acc => acc * Z.of_nat p) 1 (filter (zz_in_Pn n) (seq 1 K)).

Lemma sl1_fold_unit_scale :
  forall (F : list nat) (c : Z),
    fold_right (fun p acc => acc * Z.of_nat p) c F
    = fold_right (fun p acc => acc * Z.of_nat p) 1%Z F * c.
Proof.
  intros F c. induction F as [|x F IH].
  - cbn [fold_right]. rewrite Z.mul_1_l. reflexivity.
  - cbn [fold_right].
    rewrite IH.
    rewrite <- !Z.mul_assoc.
    rewrite (Z.mul_comm c (Z.of_nat x)). reflexivity.
Defined.

Lemma sl1_prodf_fold_eq : forall n K : nat, zz_prodf n K = sl1_prodf_fold n K.
Proof.
  intros n K. induction K as [|K IH].
  - reflexivity.
  - cbn [zz_prodf].
    unfold sl1_prodf_fold.
    rewrite seq_S.
    replace (1 + K)%nat with (S K)%nat by reflexivity.
    rewrite filter_app, fold_right_app.
    cbn [filter].
    destruct (zz_in_Pn n (S K)) eqn:E.
    + rewrite sl1_fold_unit_scale.
      rewrite IH. cbn [fold_right].
      rewrite Z.mul_1_l. reflexivity.
    + cbn [fold_right]. exact IH.
Defined.

(* ==== Section 3: no window members beyond 2n (zz_Pn_bounded) ==== *)

Lemma sl1_prodf_const_beyond :
  forall n m : nat, zz_prodf n (2 * n + m) = zz_prodf n (2 * n).
Proof.
  intros n m. induction m as [|m IH].
  - replace (2 * n + 0)%nat with (2 * n)%nat by lia. reflexivity.
  - replace (2 * n + S m)%nat with (S (2 * n + m))%nat by lia.
    cbn [zz_prodf].
    destruct (zz_in_Pn n (S (2 * n + m))) eqn:E.
    + exfalso.
      assert (Hb : BidT (zz_in_Pn n (S (2 * n + m)))) by (apply BidT_intro; exact E).
      pose proof (zz_Pn_bounded n (S (2 * n + m)) Hb) as Hb2.
      apply BidT_elim in Hb2.
      apply (proj1 (Nat.leb_le (S (2 * n + m)) (2 * n))) in Hb2.
      lia.
    + exact IH.
Defined.

Lemma sl1_planb4_Phi_eq_zz_Phi :
  forall n : nat, planb4_Phi n = zz_Phi n.
Proof.
  intro n.
  change (sl1_prodf_fold n (4 * n) = zz_prodf n (2 * n)).
  replace (4 * n)%nat with (2 * n + (2 * n))%nat by lia.
  rewrite <- sl1_prodf_fold_eq.
  apply sl1_prodf_const_beyond.
Defined.

(* ==== Section 4: the divisibility theorem ==== *)

Definition sl1_phi_divides_L_witness : Set :=
  forall n : nat,
    sigT (fun q : Z => Bid Z (q * planb4_Phi n) (planb4_L n)).

Theorem sl1_phi_divides_L : sl1_phi_divides_L_witness.
Proof.
  intro n.
  assert (Hphi : planb4_Phi n = zz_Phi n)
    by (apply sl1_planb4_Phi_eq_zz_Phi).
  assert (HL : planb4_L n = zz_lcm_range (4 * n)%nat).
  { unfold planb4_L. symmetry. apply sl1_lcm_upto_range_eq. }
  assert (Hpos : (0 < zz_Phi n)%Z).
  { unfold zz_Phi.
    apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  assert (HdP : Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat)).
  { apply (zz_prodf_divides_P n (2 * n)%nat).
    intros k Hk Hinp. apply zz_j_div_lcm_P.
    - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
      pose proof (zz_primeb_prime k Hpk) as Hk1.
      apply (proj1 (Nat.ltb_lt 1 k)) in Hk1. lia.
    - assert (Hb : BidT (Nat.leb k (2 * n)%nat))
        by (apply zz_Pn_bounded; exact Hinp).
      apply BidT_elim in Hb.
      apply (proj1 (Nat.leb_le k (2 * n)%nat)) in Hb.
      lia. }
  rewrite Hphi, HL.
  destruct HdP as [e He]. apply Bid_elim in He.
  exists (Z.div (zz_lcm_range (4 * n)%nat) (zz_Phi n)).
  apply Bid_intro.
  replace (zz_lcm_range (4 * n)%nat) with (e * zz_Phi n)
    by (rewrite Z.mul_comm; exact He).
  rewrite Z.div_mul by lia.
  reflexivity.
Defined.

(* ==== Section 5: the exact-quotient identity lifted to Q ==== *)

Lemma sl1_inject_Z_mult :
  forall a b : Z, inject_Z (a * b) == inject_Z a * inject_Z b.
Proof.
  intros a b.
  unfold Qeq, Qeq_bool, inject_Z, Qmult.
  cbn [Qnum Qden].
  lia.
Defined.

Lemma sl1_inject_Z_eq :
  forall a b : Z, inject_Z a == inject_Z b -> a = b.
Proof.
  intros a b H.
  unfold Qeq, Qeq_bool, inject_Z in H.
  cbn [Qnum Qden] in H.
  lia.
Defined.

Lemma sl1_lzn_exact :
  forall n : nat,
    inject_Z (planb4_LZn n)
    == inject_Z (planb4_L n) / inject_Z (planb4_Phi n).
Proof.
  intro n.
  destruct (sl1_phi_divides_L n) as [q Hbid].
  apply Bid_elim in Hbid.
  assert (Hphi1 : (1 <= planb4_Phi n)%Z).
  { pose proof (zz_prodf_pos n (2 * n)%nat) as Hp.
    apply (proj1 (Z.ltb_lt 0 (zz_Phi n))) in Hp.
    rewrite <- sl1_planb4_Phi_eq_zz_Phi in Hp. lia. }
  assert (Hdivq : planb4_L n / planb4_Phi n = q).
  { symmetry. apply (Z.div_unique (planb4_L n) (planb4_Phi n) q 0).
    - left. lia.
    - rewrite Z.mul_comm. lia. }
  assert (HInj : inject_Z (planb4_L n) == inject_Z q * inject_Z (planb4_Phi n)).
  { rewrite <- Hbid. rewrite sl1_inject_Z_mult. reflexivity. }
  unfold planb4_LZn.
  rewrite Hdivq, HInj.
  unfold Qdiv.
  rewrite <- Qmult_assoc.
  rewrite (Qmult_inv_r (inject_Z (planb4_Phi n)))
    by (intro Hz; apply sl1_inject_Z_eq in Hz; lia).
  rewrite Qmult_1_r. reflexivity.
Defined.

(* ==== Section 6: positivity faces ==== *)

Lemma sl1_zz_lcm_range_pos : forall K : nat, (1 <= zz_lcm_range K)%Z.
Proof.
  intro K. induction K as [|K IH].
  - cbn [zz_lcm_range]. lia.
  - cbn [zz_lcm_range].
    pose proof (Z.divide_lcm_r (zz_lcm_range K) (Z.of_nat (S K))) as Hdr.
    pose proof (Z.lcm_nonneg (zz_lcm_range K) (Z.of_nat (S K))) as Hnn.
    assert (Hnz : (Z.lcm (zz_lcm_range K) (Z.of_nat (S K)))%Z <> 0).
    { intro Hz.
      apply (proj1 (Z.lcm_eq_0 (zz_lcm_range K) (Z.of_nat (S K)))) in Hz.
      lia. }
    pose proof (Z.divide_pos_le (Z.of_nat (S K))
                  (Z.lcm (zz_lcm_range K) (Z.of_nat (S K)))
                  ltac:(lia) Hdr) as Hle.
    lia.
Defined.

Lemma sl1_qltT0_of_Z1 :
  forall x : Z, (1 <= x)%Z -> S02_CauchyComplete.QltT 0 (inject_Z x).
Proof.
  intros x Hx. apply S02_CauchyComplete.Qlt_to_QltT.
  cbv [Qlt inject_Z]. cbn. lia.
Defined.

Lemma sl1_qle0_of_Z :
  forall x : Z, (0 <= x)%Z -> S02_CauchyComplete.QleT' 0 (inject_Z x).
Proof.
  intros x Hx. apply S02_CauchyComplete.Qle_to_QleT'.
  unfold Qle, inject_Z. cbn. lia.
Defined.

Lemma sl1_lcm_pos :
  forall n : nat, S02_CauchyComplete.QltT 0 (inject_Z (planb4_L n)).
Proof.
  intro n. apply sl1_qltT0_of_Z1.
  replace (planb4_L n) with (zz_lcm_range (4 * n)%nat)
    by (unfold planb4_L; apply sl1_lcm_upto_range_eq).
  apply sl1_zz_lcm_range_pos.
Defined.

Lemma sl1_phi_pos :
  forall n : nat,
    S02_CauchyComplete.QltT 0 (inject_Z (planb4_Phi n)).
Proof.
  intro n.
  pose proof (zz_prodf_pos n (2 * n)%nat) as Hp.
  apply (proj1 (Z.ltb_lt 0 (zz_Phi n))) in Hp.
  rewrite <- sl1_planb4_Phi_eq_zz_Phi in Hp.
  apply sl1_qltT0_of_Z1. lia.
Defined.

Lemma sl1_lzn_pos :
  forall n : nat,
    S02_CauchyComplete.QltT 0 (inject_Z (planb4_LZn n)).
Proof.
  intro n.
  destruct (sl1_phi_divides_L n) as [q Hbid].
  apply Bid_elim in Hbid.
  assert (Hphi1 : (1 <= planb4_Phi n)%Z).
  { pose proof (zz_prodf_pos n (2 * n)%nat) as Hp.
    apply (proj1 (Z.ltb_lt 0 (zz_Phi n))) in Hp.
    rewrite <- sl1_planb4_Phi_eq_zz_Phi in Hp. lia. }
  assert (HLZ : (0 < planb4_L n)%Z).
  { replace (planb4_L n) with (zz_lcm_range (4 * n)%nat)
      by (unfold planb4_L; apply sl1_lcm_upto_range_eq).
    pose proof (sl1_zz_lcm_range_pos (4 * n)%nat). lia. }
  assert (Hq1 : (1 <= q)%Z).
  { assert (Hle : (planb4_Phi n <= planb4_L n)%Z).
    { apply Z.divide_pos_le; [lia |].
      exists q. lia. }
    nia. }
  assert (Hdivq : planb4_L n / planb4_Phi n = q).
  { symmetry. apply (Z.div_unique (planb4_L n) (planb4_Phi n) q 0).
    - left. lia.
    - rewrite Z.mul_comm. lia. }
  apply sl1_qltT0_of_Z1.
  unfold planb4_LZn.
  rewrite Hdivq.
  lia.
Defined.

Lemma sl1_lcm_ge1 : forall n : nat, (1 <= planb4_L n)%Z.
Proof.
  intro n.
  replace (planb4_L n) with (zz_lcm_range (4 * n)%nat)
    by (unfold planb4_L; apply sl1_lcm_upto_range_eq).
  apply sl1_zz_lcm_range_pos.
Defined.

Lemma sl1_lzn_ge1 : forall n : nat, (1 <= planb4_LZn n)%Z.
Proof.
  intro n.
  destruct (sl1_phi_divides_L n) as [q Hbid].
  apply Bid_elim in Hbid.
  assert (Hphi1 : (1 <= planb4_Phi n)%Z).
  { pose proof (zz_prodf_pos n (2 * n)%nat) as Hp.
    apply (proj1 (Z.ltb_lt 0 (zz_Phi n))) in Hp.
    rewrite <- sl1_planb4_Phi_eq_zz_Phi in Hp. lia. }
  assert (HLZ : (0 < planb4_L n)%Z).
  { replace (planb4_L n) with (zz_lcm_range (4 * n)%nat)
      by (unfold planb4_L; apply sl1_lcm_upto_range_eq).
    pose proof (sl1_zz_lcm_range_pos (4 * n)%nat). lia. }
  assert (Hq1 : (1 <= q)%Z).
  { assert (Hle : (planb4_Phi n <= planb4_L n)%Z).
    { apply Z.divide_pos_le; [lia |].
      exists q. lia. }
    nia. }
  assert (Hdivq : planb4_L n / planb4_Phi n = q).
  { symmetry. apply (Z.div_unique (planb4_L n) (planb4_Phi n) q 0).
    - left. lia.
    - rewrite Z.mul_comm. lia. }
  unfold planb4_LZn. rewrite Hdivq. lia.
Defined.

(* ==== Section 7: Z-to-Q nonnegativity bridges ==== *)

Lemma sl1_abs_L_nonneg :
  forall n : nat,
    S02_CauchyComplete.QleT' 0 (inject_Z (Z.abs (planb4_L n))).
Proof.
  intro n. apply sl1_qle0_of_Z. apply Z.abs_nonneg.
Defined.

Lemma sl1_abs_LZn_nonneg :
  forall n : nat,
    S02_CauchyComplete.QleT' 0 (inject_Z (Z.abs (planb4_LZn n))).
Proof.
  intro n. apply sl1_qle0_of_Z. apply Z.abs_nonneg.
Defined.

Print Assumptions sl1_lcm_upto_range_eq.
Print Assumptions sl1_prodf_fold_eq.
Print Assumptions sl1_prodf_const_beyond.
Print Assumptions sl1_planb4_Phi_eq_zz_Phi.
Print Assumptions sl1_phi_divides_L.
Print Assumptions sl1_lzn_exact.
Print Assumptions sl1_zz_lcm_range_pos.
Print Assumptions sl1_lcm_ge1.
Print Assumptions sl1_lzn_ge1.
Print Assumptions sl1_qltT0_of_Z1.
Print Assumptions sl1_qle0_of_Z.
Print Assumptions sl1_lcm_pos.
Print Assumptions sl1_phi_pos.
Print Assumptions sl1_lzn_pos.
Print Assumptions sl1_abs_L_nonneg.
Print Assumptions sl1_abs_LZn_nonneg.
