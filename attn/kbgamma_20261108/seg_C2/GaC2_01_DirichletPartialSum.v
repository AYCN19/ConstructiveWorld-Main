(* ConstructiveWorld-Main - the finite Dirichlet partial-sum face of the
   zeta series on the complex pair carrier. *)
(** * GaC2_01_DirichletPartialSum: the Dirichlet partial sums of n^{-s}.
    Mission.  The finite Dirichlet partial-sum face of the zeta series:
      the term n^{-s} := c_exp(-s * ln n) on the pair carrier [Cx] as
      [c_powq], the partial sum [c_zeta_part], the blocked tail
      [c_tail], the exponential addition law for the term
      [c_powq_plus_law], the squared-modulus formula
      |n^{-s}|^2 = n^{-2sig} carried by [c_norm_sq] with zero
      square-root dependence ([c_powq_norm_sq]), the tail difference
      identity [c_zeta_part_tail_eq], and the positive-inverse witness
      [c_inv_wit]/[c_inv_wit_correct].
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith].  Requires [S01_BaseRing] (selective [NatLe]
      import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore], and
      [CxRealPairExpLog] of this development.
    References.  F8 RiemZeta.lean zeta_eq_tsum_one_div_nat_add_one_cpow
      and F6 EulDirich.lean summable_riemannZetaSummand
      (statement-face alignment only, zero proof-body transplant,
      absorption coeff 0.30); blueprint drafts_C2.md C2.01 draft-2
      statement shapes, with four statement-shape corrections:
      (i) the tail identity gains the Set-sorted [NatLe] M N bound the
      blueprint statement lacked (without it the statement is false
      for M > N); (ii) nat bounds are carried by [NatLe] (S01,
      Set-sorted) instead of stdlib Prop [le], per red-line A;
      (iii) the Section variable [Hnpos] is the premise-parametrised
      positivity face  forall n, NatLe 1 n -> 0 < nat_real n  (the
      blueprint's unconditional form was unsatisfiable at n = 0);
      [c_powq] and its two laws gain the explicit [NatLe 1 n]
      argument, while [c_zeta_part]/[c_tail] build the witness
      [NatLe_one_S] internally; (iv) the discrimination faces
      [NatLe_one_S] (true at S n) and [NatLe_1_zero_empty] (empty at 0)
      are cast here as the consumer-side instantiation anchors.
    Constructivity.  Every named construction is carried by [Set]; all
      predicates are Set-sorted ([c_eq], [real_eq], [real_lt],
      [QltT], [NatLe]); no new Prop statements; every proof closes
      under the global context; [coqchk] reports zero assumed
      constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_01_DirichletPartialSum.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98
      -AllowG3 -GearForce 0 -CoreN 2). *)

Require S01_BaseRing.
(* Selective import: S01's StateSpace class projects a field named S which
   shadows the nat constructor S under a full import (shadow reproduced and
   pinned in session); only the Set-sorted nat bound face is consumed. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.

(* ==== Section 1. Embedding faces ==== *)

Definition c_of_real (r : Real) : Cx := (r, real_zero).

Definition nat_real (n : nat) : Real := real_const (Z.of_nat n # 1)%Q.

(* NatLe 1 n discrimination faces: NatLe 1 0 is empty                      *)
(* (leb 1 0 = false <> true) and NatLe 1 (S n) holds by leb 1 (S n) =      *)
(* true; these are the instantiation anchors of the Hnpos premise family.  *)
Lemma NatLe_one_S : forall n : nat, NatLe 1 (S n).
Proof.
  intro n. apply NatLe_lift. apply le_n_S. apply Nat.le_0_l.
Qed.

Lemma NatLe_1_zero_empty : NatLe 1 0 -> Empty_set.
Proof.
  intro H. destruct (Nat.nle_succ_0 0 (NatLe_drop _ _ H)).
Qed.

(* ==== Section 2. Congruence and algebra helpers (node-internal faces) ==== *)

Lemma cRe_wd : forall z w : Cx, c_eq z w -> real_eq (cRe z) (cRe w).
Proof.
  intros z w H. unfold c_eq in H. destruct H as [Hr Hi]. exact Hr.
Qed.

Lemma c_scale_wd : forall (a : Real) (z w : Cx),
  c_eq z w -> c_eq (c_scale a z) (c_scale a w).
Proof.
  intros a z w H. unfold c_eq in H. destruct H as [Hr Hi].
  unfold c_eq, c_scale, cRe, cIm. split.
  - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact Hr].
  - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact Hi].
Qed.

Lemma c_exp_wd : forall z w : Cx, c_eq z w -> c_eq (c_exp z) (c_exp w).
Proof.
  intros z w H. unfold c_eq in H. destruct H as [Hr Hi].
  assert (He : real_eq (cauchy_real_exp (cRe z)) (cauchy_real_exp (cRe w)))
    by (apply cauchy_real_exp_wd; exact Hr).
  assert (Hc : real_eq (cauchy_real_cos (cIm z)) (cauchy_real_cos (cIm w)))
    by (apply real_cos_eq_compat; exact Hi).
  assert (Hs : real_eq (cauchy_real_sin (cIm z)) (cauchy_real_sin (cIm w)))
    by (apply real_sin_eq_compat; exact Hi).
  unfold c_exp, c_eq, cRe, cIm. split.
  - apply RealSetoid.real_eq_mult_compat; [exact He | exact Hc].
  - apply RealSetoid.real_eq_mult_compat; [exact He | exact Hs].
Qed.

Lemma c_norm_sq_via_conj : forall z : Cx,
  real_eq (c_norm_sq z) (cRe (c_mult z (c_conj z))).
Proof.
  intros [a b]. destruct a as [ua Ha]. destruct b as [ub Hb].
  apply real_eq_of_zero_diff. intro n.
  unfold c_norm_sq, c_mult, c_conj, cRe, cIm, c_plus, c_opp. simpl. ring.
Qed.

Lemma c_plus_conj_real : forall z : Cx,
  c_eq (c_plus z (c_conj z)) (c_of_real (real_plus (cRe z) (cRe z))).
Proof.
  intros [a b]. destruct a as [ua Ha]. destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n;
    unfold c_plus, c_conj, c_of_real, cRe, cIm, c_opp; simpl; ring.
Qed.

Lemma c_scale_plus : forall (a : Real) (z w : Cx),
  c_eq (c_plus (c_scale a z) (c_scale a w)) (c_scale a (c_plus z w)).
Proof.
  intros a [p q] [r s].
  destruct a as [ua Ha]. destruct p as [up Hp]. destruct q as [uq Hq].
  destruct r as [ur Hr]. destruct s as [us Hs].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n;
    unfold c_plus, c_scale, cRe, cIm; simpl; ring.
Qed.

Lemma c_mult_distrib_l : forall z w u : Cx,
  c_eq (c_mult (c_plus z w) u) (c_plus (c_mult z u) (c_mult w u)).
Proof.
  intros z w u.
  apply (c_eq_trans _ (c_mult u (c_plus z w))).
  - apply c_mult_comm.
  - apply (c_eq_trans _ (c_plus (c_mult u z) (c_mult u w))).
    + apply c_distrib.
    + apply c_plus_congr; apply c_mult_comm.
Qed.

Lemma cRe_mult_wd : forall z1 z2 w1 w2 : Cx,
  c_eq z1 z2 -> c_eq w1 w2 ->
  real_eq (cRe (c_mult z1 w1)) (cRe (c_mult z2 w2)).
Proof.
  intros z1 z2 w1 w2 Hz Hw. apply cRe_wd. apply c_mult_congr; assumption.
Qed.

Lemma c_plus_zero_r : forall z : Cx, c_eq (c_plus z c_zero) z.
Proof.
  intros [a b]. destruct a as [ua Ha]. destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n;
    unfold c_plus, cRe, cIm; simpl; ring.
Qed.

(* The polar-argument face: -1 * (s * (l,0)) doubled in the real part is
   the scaled argument of the doubled-exponent term; imaginary part 0.
   l is an abstract positive real, so no pointwise contact with real_log. *)
Lemma c_powq_arg_face : forall (s : Cx) (l : Real),
  c_eq (c_of_real (real_plus
         (cRe (c_scale (real_opp real_one) (c_mult s (c_of_real l))))
         (cRe (c_scale (real_opp real_one) (c_mult s (c_of_real l))))))
       (c_scale (real_opp real_one)
          (c_mult (c_of_real (real_plus (cRe s) (cRe s))) (c_of_real l))).
Proof.
  intros s l.
  destruct s as [p q]. destruct p as [up Hp]. destruct q as [uq Hq].
  destruct l as [ul Hl].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n;
    unfold c_of_real, cRe, cIm, c_scale, c_mult, c_plus, c_opp; simpl; ring.
Qed.

(* ==== Section 3. The Dirichlet partial-sum carrier ==== *)

Section DirichletPartialSum.

(* Premise-parametrised positivity face: inhabited exactly
   on n >= 1, hence satisfiable (consumer witness: nat_real_pos of C2.02-a,
   or any Set-sorted positivity face of the embedded naturals). *)
Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).

(* n^{-s} := c_exp(-s * ln n); ln n is the tree real_log (= cw_log, S07:7881);
   the NatLe 1 n argument feeds the positivity premise of the log. *)
Definition c_powq (n : nat) (Hn : NatLe 1 n) (s : Cx) : Cx :=
  c_exp (c_scale (real_opp real_one)
           (c_mult s (c_of_real (real_log (nat_real n) (Hnpos n Hn))))).

Fixpoint c_zeta_part (N : nat) (s : Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (c_zeta_part m s) (c_powq (S m) (NatLe_one_S m) s)
  end.

Fixpoint c_tail (M N : nat) (s : Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (c_tail M m s)
             (if Nat.ltb M (S m) then c_powq (S m) (NatLe_one_S m) s else c_zero)
  end.

(* (a) exponential addition law for the term. *)
Lemma c_powq_plus_law : forall (n : nat) (Hn : NatLe 1 n) (s w : Cx),
  c_eq (c_mult (c_powq n Hn s) (c_powq n Hn w)) (c_powq n Hn (c_plus s w)).
Proof.
  intros n Hn s w. unfold c_powq.
  set (l := real_log (nat_real n) (Hnpos n Hn)).
  set (A := c_scale (real_opp real_one) (c_mult s (c_of_real l))).
  set (B := c_scale (real_opp real_one) (c_mult w (c_of_real l))).
  apply (c_eq_trans _ (c_exp (c_plus A B))).
  - apply c_eq_sym. apply c_exp_plus.
  - apply c_exp_wd.
    apply (c_eq_trans _ (c_scale (real_opp real_one)
              (c_plus (c_mult s (c_of_real l)) (c_mult w (c_of_real l))))).
    + apply c_scale_plus.
    + apply c_scale_wd.
      apply (c_eq_trans _ (c_mult (c_plus s w) (c_of_real l))).
      * apply c_eq_sym. apply c_mult_distrib_l.
      * apply c_eq_refl.
Qed.

(* (b) squared-modulus formula |n^{-s}|^2 = n^{-2 sig} carried by c_norm_sq;
       zero square-root dependence. *)
Lemma c_powq_norm_sq : forall (n : nat) (Hn : NatLe 1 n) (s : Cx),
  real_eq (c_norm_sq (c_powq n Hn s))
          (cRe (c_powq n Hn (c_of_real (real_plus (cRe s) (cRe s))))).
Proof.
  intros n Hn s. unfold c_powq.
  set (l := real_log (nat_real n) (Hnpos n Hn)).
  set (Z := c_scale (real_opp real_one) (c_mult s (c_of_real l))).
  set (W := c_scale (real_opp real_one)
              (c_mult (c_of_real (real_plus (cRe s) (cRe s))) (c_of_real l))).
  apply (real_eq_trans _ (cRe (c_mult (c_exp Z) (c_conj (c_exp Z))))).
  - apply c_norm_sq_via_conj.
  - apply (real_eq_trans _ (cRe (c_mult (c_exp Z) (c_exp (c_conj Z))))).
    + apply cRe_mult_wd; [apply c_eq_refl | apply c_eq_sym; apply c_exp_conj].
    + apply (real_eq_trans _ (cRe (c_exp (c_plus Z (c_conj Z))))).
      * apply cRe_wd. apply c_eq_sym. apply c_exp_plus.
      * apply (real_eq_trans _
            (cRe (c_exp (c_of_real (real_plus (cRe Z) (cRe Z)))))).
        -- apply cRe_wd. apply c_exp_wd. apply c_plus_conj_real.
        -- apply cRe_wd. apply c_exp_wd. apply (c_powq_arg_face s l).
Qed.

(* Helper: the blocked tail is zero once the block starts past the end. *)
Lemma c_tail_zero_le : forall (M N : nat) (s : Cx), NatLe N M ->
  c_eq (c_tail M N s) c_zero.
Proof.
  intros M N s. revert M. induction N as [|m IH]; intros M HNM.
  - cbn [c_tail]. apply c_eq_refl.
  - cbn [c_tail].
    assert (Hltb : Nat.ltb M (S m) = false).
    { exact (proj2 (Nat.ltb_ge M (S m)) (NatLe_drop _ _ HNM)). }
    rewrite Hltb.
    apply (c_eq_trans _ (c_tail M m s)).
    + apply c_plus_zero_r.
    + apply IH. apply NatLe_lift.
      apply Nat.le_trans with (S m);
        [apply Nat.le_succ_diag_r | apply NatLe_drop; exact HNM].
Qed.

(* (c) tail difference identity; the NatLe M N bound is Set-sorted
       (red-line A); without it the statement is false for M > N. *)
Lemma c_zeta_part_tail_eq : forall (M N : nat) (s : Cx), NatLe M N ->
  c_eq (c_plus (c_zeta_part N s) (c_opp (c_zeta_part M s))) (c_tail M N s).
Proof.
  intros M N s HMN. revert M HMN.
  induction N as [|m IH]; intros M HMN.
  - assert (HM0 : M = 0%nat) by (apply Nat.le_0_r; apply NatLe_drop; exact HMN).
    subst M. cbn [c_zeta_part c_tail]. apply c_plus_opp.
  - cbn [c_zeta_part c_tail].
    destruct (Nat.ltb M (S m)) eqn:HLtb.
    + assert (Hlt : (M < S m)%nat) by exact (proj1 (Nat.ltb_lt M (S m)) HLtb).
      assert (HMm : NatLe M m)
        by (apply NatLe_lift; exact (proj1 (Nat.lt_succ_r M m) Hlt)).
      cbn [c_tail].
      apply (c_eq_trans _ (c_plus (c_zeta_part m s)
                (c_plus (c_powq (S m) (NatLe_one_S m) s) (c_opp (c_zeta_part M s))))).
      * apply c_eq_sym. apply c_plus_assoc.
      * apply (c_eq_trans _ (c_plus (c_zeta_part m s)
                  (c_plus (c_opp (c_zeta_part M s)) (c_powq (S m) (NatLe_one_S m) s)))).
        -- apply c_plus_congr; [apply c_eq_refl | apply c_plus_comm].
        -- apply (c_eq_trans _ (c_plus (c_plus (c_zeta_part m s)
                     (c_opp (c_zeta_part M s))) (c_powq (S m) (NatLe_one_S m) s))).
           ++ apply c_plus_assoc.
           ++ apply c_plus_congr; [apply IH; exact HMm | apply c_eq_refl].
    + assert (Hge : (S m <= M)%nat) by exact (proj1 (Nat.ltb_ge M (S m)) HLtb).
      assert (HMSm : S m = M)
        by (apply Nat.le_antisymm; [exact Hge | apply NatLe_drop; exact HMN]).
      rewrite <- HMSm. cbn [c_zeta_part c_tail].
      assert (HT : c_eq (c_plus (c_tail (S m) m s) c_zero) c_zero).
      { apply (c_eq_trans _ (c_tail (S m) m s)).
        - apply c_plus_zero_r.
        - apply c_tail_zero_le. apply NatLe_lift. apply Nat.le_succ_diag_r. }
      apply (c_eq_trans _ c_zero).
      * apply c_plus_opp.
      * apply c_eq_sym. exact HT.
Qed.

End DirichletPartialSum.

(* ==== Section 4. Positive-inverse witness ==== *)

(* sigT-shaped positive inverse: the witness consumes the explicit
   positivity premise only (real_inv_pos, S03:6681); no classical
   selection principle. *)
Definition c_inv_wit (r : Real) (Hr : real_lt real_zero r) : Real :=
  real_inv_pos r Hr.

Lemma c_inv_wit_correct : forall (r : Real) (Hr : real_lt real_zero r),
  real_eq (real_mult r (c_inv_wit r Hr)) real_one.
Proof.
  intros r Hr. apply real_inv_pos_correct.
Qed.
