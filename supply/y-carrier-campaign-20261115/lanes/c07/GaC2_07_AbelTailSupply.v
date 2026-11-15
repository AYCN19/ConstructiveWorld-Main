(** * GaC2_07_AbelTailSupply: the conditional supply face of [abel_tail] (node C2-07).

    Mission.  Supplies the proof body of the statement carrier [abel_tail] of
    [GaC2_07_DirichletTestAbel] (the card (1) Abel window bound in the squared
    house form) under three named premises: [Ha_nonneg] (the coefficient
    sequence is nonnegative; necessary rather than decorative - the
    counterexample replica in the certificate band shows the carried bound
    failing while both carried premises hold), [HB_nonneg] (the prefix modulus
    bound B is nonnegative), and [abel_tri_pair_face] (the two-fold linear
    triangle face of the squared house, the open supply row L-C2.02-C, carried
    here as an explicit premise and consumed, never assumed globally).  Route
    (stem Notes): Abel summation by parts on inclusive prefixes, the triangle
    face lifted to window sums by induction, telescoping collapse to 2*B*a (S M).

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia]; requires [S01_BaseRing]
    (selective [NatLe] import), [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
    [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC2_01_DirichletPartialSum],
    [GaC2_02_AbsConvTailBound_a], [GaC2_06_AltMonoFace], and the stem [GaC2_07_DirichletTestAbel].

    References.  cards_C2.md C2.07; the stem header and Notes block of
    [GaC2_07_DirichletTestAbel]; Titchmarsh Ch.1; Montgomery-Vaughan Ch.1.

    Constructivity.  All constructions are [Set]-carried with Set-sorted [real_lt] /
    [real_le] order premises; no Section wrapper, no assumed constant, no abandoned
    proof; the triangle face is an explicit premise (honest interface) and [Print
    Assumptions] on [abel_tail_supply] reports Closed under the global context;
    every proof ends in [Defined]; [lia] only inside bookkeeping steps on nat indices.

    Build.  [coqc -native-compiler no -q -Q <build root> "" GaC2_07_AbelTailSupply.v]
    (flat build directory; certificate face [GaC2_07_AbelTailSupply_cert]). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_06_AltMonoFace.
Require Import GaC2_07_DirichletTestAbel.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.Arith Lia.

Local Open Scope Q_scope.

(* Section 1. Pointwise closers: real_eq and c_eq goals that reduce to   *)
(* Q ring identities once the Real hypotheses are destructed.            *)
Ltac abel_rring :=
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  apply real_eq_of_zero_diff; intro abelv; simpl; ring.
Ltac abel_cring :=
  repeat match goal with
  | [ x : Cx |- _ ] => destruct x
  | [ x : Real |- _ ] => destruct x
  end;
  unfold c_eq; split; apply real_eq_of_zero_diff; intro abelv; simpl; ring.


(* Section 2. Window carriers.                                           *)

(* The linear-bound window sum sum_{M<n<=N} r n, mirroring the recursion *)
(* shape of [c_wsum].                                                    *)
Fixpoint abel_rsum (M N : nat) (r : nat -> Real) : Real :=
  match N with
  | O => real_zero
  | S m => real_plus (abel_rsum M m r)
                     (if Nat.ltb M (S m) then r (S m) else real_zero)
  end.

(* The inclusive prefix column: sum_{k<=j} b_k.                          *)
Definition inc_prefix (b : nat -> Cx) (j : nat) : Cx := c_abssum (S j) b.

(* The step-difference sequence: a k - a (S k).                          *)
Definition dif_seq (a : nat -> Real) (k : nat) : Real :=
  real_plus (a k) (real_opp (a (S k))).

(* The pointwise closer for real_eq goals whose sides mention function-  *)
(* applied reals: expand through the projection lemmas, then ring.       *)
Ltac abel_pfold :=
  apply real_eq_of_zero_diff; intro abelv;
  try unfold dif_seq;
  repeat first
    [ rewrite real_plus_proj
    | rewrite real_opp_proj
    | rewrite real_mult_proj
    | rewrite real_zero_pt
    | rewrite real_const_proj ];
  simpl; ring.

(* Section 3. Addition rearrangement helpers on the carrier.             *)

(* Left re-association: ((z+w)+u) == (z+(w+u)).                          *)
Lemma cplus_lassoc : forall z w u : Cx,
  c_eq (c_plus (c_plus z w) u) (c_plus z (c_plus w u)).
Proof. intros z w u. apply c_eq_sym. apply c_plus_assoc. Defined.

(* The left rotation: z+(w+u) == w+(z+u).                                *)
Lemma cplus_rotate_l : forall z w u : Cx,
  c_eq (c_plus z (c_plus w u)) (c_plus w (c_plus z u)).
Proof.
  intros z w u. apply (c_eq_trans _ (c_plus (c_plus z w) u)).
  - apply c_plus_assoc.
  - apply (c_eq_trans _ (c_plus (c_plus w z) u)).
    + apply c_plus_congr; [apply c_plus_comm | apply c_eq_refl].
    + apply c_eq_sym. apply c_plus_assoc.
Defined.

(* Section 4. Order algebra supply.                                      *)

(* Left zero of the product collapses pointwise.                         *)
Lemma real_mult_zero_l : forall x : Real,
  real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x. apply real_eq_of_zero_diff. intro m.
  rewrite real_mult_proj, real_zero_pt. simpl. ring.
Defined.

(* A product of nonnegative reals is nonnegative (decided inl/inr form). *)
Lemma r_nonneg_mult : forall x y : Real,
  real_le real_zero x -> real_le real_zero y ->
  real_le real_zero (real_mult x y).
Proof.
  intros x y Hx Hy. unfold real_le in Hx, Hy. unfold real_le.
  destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
  - exact (inl (real_mult_positive x y Hx Hy)).
  - exact (inr (real_eq_sym (real_mult x y) real_zero
                  (real_eq_trans (real_mult x y) (real_mult x real_zero) real_zero
                     (RealSetoid.real_eq_mult_compat x y x real_zero
                        (real_eq_refl x) (real_eq_sym real_zero y Hy))
                     (real_mult_zero x)))).
  - exact (inr (real_eq_sym (real_mult x y) real_zero
                  (real_eq_trans (real_mult x y) (real_mult real_zero y) real_zero
                     (RealSetoid.real_eq_mult_compat x y real_zero y
                        (real_eq_sym real_zero x Hx) (real_eq_refl y))
                     (real_eq_trans (real_mult real_zero y) (real_mult y real_zero)
                        real_zero (real_mult_comm real_zero y)
                        (real_mult_zero y))))).
  - exact (inr (real_eq_sym (real_mult x y) real_zero
                  (real_eq_trans (real_mult x y) (real_mult real_zero y) real_zero
                     (RealSetoid.real_eq_mult_compat x y real_zero y
                        (real_eq_sym real_zero x Hx) (real_eq_refl y))
                     (real_eq_trans (real_mult real_zero y) (real_mult y real_zero)
                        real_zero (real_mult_comm real_zero y)
                        (real_mult_zero y))))).
Defined.

(* Right multiplication by a strictly positive factor is strictly        *)
(* monotone; the witness is built at the projection level.               *)
Lemma real_lt_mult_mono_r : forall z x y : Real,
  real_lt real_zero z -> real_lt x y -> real_lt (real_mult z x) (real_mult z y).
Proof.
  intros z x y Hz Hxy.
  destruct Hz as [epsz [Hepsz [Nz HNz]]].
  destruct Hxy as [eps [Heps [N0 HN0]]].
  assert (Hpe : Qlt 0 (epsz * eps)).
  { assert (H1 : Qlt 0 epsz) by (apply QltT_to_Qlt; exact Hepsz).
    assert (H2 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    assert (H3 : Qlt (0 * eps) (epsz * eps))
      by (apply (Qmult_lt_compat_r _ _ eps H2 H1)).
    rewrite Qmult_0_l in H3. exact H3. }
  exists (epsz * eps)%Q. split.
  - apply Qlt_to_QltT. exact Hpe.
  - exists (Nat.max Nz N0). intros m Hm.
    apply Qlt_to_QltT.
    setoid_replace (projT1 (real_mult z y) m) with (projT1 z m * projT1 y m)
      by apply real_mult_proj.
    setoid_replace (projT1 (real_mult z x) m) with (projT1 z m * projT1 x m)
      by apply real_mult_proj.
    setoid_replace (projT1 z m * projT1 y m - projT1 z m * projT1 x m)%Q
      with (projT1 z m * (projT1 y m - projT1 x m))%Q by ring.
    assert (H0e : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
    assert (H0z : Qlt 0 epsz) by (apply QltT_to_Qlt; exact Hepsz).
    assert (Hzm : Qlt epsz (projT1 z m - projT1 real_zero m)).
    { apply QltT_to_Qlt. apply HNz. apply NatLe_lift.
        apply Nat.le_trans with (Nat.max Nz N0);
        [apply Nat.le_max_l | apply NatLe_drop; exact Hm]. }
    assert (Hym : Qlt eps (projT1 y m - projT1 x m)).
    { apply QltT_to_Qlt. apply HN0. apply NatLe_lift.
        apply Nat.le_trans with (Nat.max Nz N0);
        [apply Nat.le_max_r | apply NatLe_drop; exact Hm]. }
    assert (Hy0 : Qlt 0 (projT1 y m - projT1 x m))
      by (exact (Qlt_trans 0 eps _ H0e Hym)).
    assert (Hi1 : Qlt (eps * epsz) ((projT1 y m - projT1 x m) * epsz))
      by (apply (Qmult_lt_compat_r _ _ epsz H0z Hym)).
    setoid_replace (eps * epsz)%Q with (epsz * eps)%Q in Hi1 by ring.
    setoid_replace ((projT1 y m - projT1 x m) * epsz)%Q
      with (epsz * (projT1 y m - projT1 x m))%Q in Hi1 by ring.
    setoid_replace (projT1 z m - projT1 real_zero m)%Q
      with (projT1 z m)%Q in Hzm by (rewrite real_zero_pt; ring).
    apply (Qlt_trans _ (epsz * (projT1 y m - projT1 x m))%Q).
    + exact Hi1.
    + apply (Qmult_lt_compat_r _ _ _ Hy0 Hzm).
Defined.

(* The pointwise fold-back face of the step difference.                  *)
Lemma r_dif_add_back : forall (a : nat -> Real) (k : nat),
  real_eq (real_plus (a (S k)) (dif_seq a k)) (a k).
Proof.
  intros a k. unfold dif_seq. abel_pfold.
Defined.

(* An antitone step with coinciding endpoints gives a zero difference    *)
(* (the eq branch of the antitone premise).                              *)
Lemma r_eq_zero_minus_of_eq : forall (a : nat -> Real) (k : nat),
  real_eq (a (S k)) (a k) ->
  real_eq real_zero (real_plus (a k) (real_opp (a (S k)))).
Proof.
  intros a k Heq. unfold real_eq. intros eps Heps.
  destruct (Heq eps Heps) as [N HN].
  exists N. intros m Hm. apply Qlt_to_QltT.
  rewrite real_plus_proj, real_opp_proj, real_zero_pt.
  setoid_replace (0 - (projT1 (a k) m - projT1 (a (S k)) m))%Q
    with (projT1 (a (S k)) m - projT1 (a k) m)%Q by ring.
  apply QltT_to_Qlt. exact (HN m Hm).
Defined.

(* The step difference is nonnegative whenever the sequence is antitone; *)
(* the two branches of [real_le] are read off the antitone premise.      *)
Lemma r_dif_nonneg : forall (a : nat -> Real)
  (Ha_anti : forall m n : nat, NatLe m n -> real_le (a n) (a m)) (k : nat),
  real_le real_zero (dif_seq a k).
Proof.
  intros a Ha_anti k. unfold dif_seq.
  destruct (Ha_anti k (S k) (NatLe_lift _ _ (Nat.le_succ_diag_r k))) as [Hlt | Heq].
  - exact (inl (real_lt_opp_plus (a (S k)) (a k) Hlt)).
  - exact (inr (r_eq_zero_minus_of_eq a k Heq)).
Defined.

(* Section 5. Pointwise algebra faces of the scaled terms.               *)

(* Squared modulus of a scaled term: |c z|^2 == c^2 |z|^2.               *)
Lemma c_norm_sq_scale_sq : forall (c : Real) (z : Cx),
  real_eq (c_norm_sq (c_scale c z)) (real_mult (sq c) (c_norm_sq z)).
Proof.
  intros c z. unfold c_norm_sq, c_scale, sq.
  destruct z as [u v]. abel_rring.
Defined.

(* The sign flip inside the scale factor does not move the squared       *)
(* modulus.                                                              *)
Lemma c_norm_sq_scale_opp_flip : forall (c : Real) (z : Cx),
  real_eq (c_norm_sq (c_scale (real_opp c) z)) (c_norm_sq (c_scale c z)).
Proof.
  intros c z. unfold c_norm_sq, c_scale. destruct z as [u v]. abel_rring.
Defined.

(* The squared modulus of the zero carrier vanishes.                     *)
Lemma c_norm_sq_zero_eq : real_eq (c_norm_sq c_zero) real_zero.
Proof. unfold c_norm_sq, c_zero. abel_rring. Defined.

(* The square of the zero real vanishes.                                 *)
Lemma sq_zero_eq : real_eq (sq real_zero) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  unfold sq. rewrite real_mult_proj, real_zero_pt. simpl. ring.
Defined.

(* Square congruence.                                                    *)
Lemma sq_eq_wd : forall x y : Real, real_eq x y -> real_eq (sq x) (sq y).
Proof.
  intros x y H. unfold sq.
  apply RealSetoid.real_eq_mult_compat; assumption.
Defined.

(* Scale congruence in the coefficient slot.                             *)
Lemma c_scale_real_wd : forall (x y : Real) (z : Cx),
  real_eq x y -> c_eq (c_scale x z) (c_scale y z).
Proof.
  intros x y z H. unfold c_scale, c_eq, cRe, cIm. split.
  - apply RealSetoid.real_eq_mult_compat; [exact H | apply real_eq_refl].
  - apply RealSetoid.real_eq_mult_compat; [exact H | apply real_eq_refl].
Defined.

(* Opposite coefficients cancel on a fixed carrier.                      *)
Lemma c_scale_opp_cancel : forall (x : Real) (z : Cx),
  c_eq (c_plus (c_scale x z) (c_scale (real_opp x) z)) c_zero.
Proof. intros x z. unfold c_scale, c_plus, c_eq, cRe, cIm. abel_cring. Defined.

(* Same-carrier scale addition.                                          *)
Lemma c_scale_pair_add : forall (x y : Real) (z : Cx),
  c_eq (c_plus (c_scale x z) (c_scale y z)) (c_scale (real_plus x y) z).
Proof. intros x y z. unfold c_scale, c_plus, c_eq, cRe, cIm. abel_cring. Defined.

(* Five-term associativity-commutativity regrouping for the parts        *)
(* identity step:                                                        *)
(* ((u1+u2)+(u3+u4))+u5  ==  (u1+u5)+(u3+(u4+u2)).                       *)
Lemma abel_cplus_regroup : forall u1 u2 u3 u4 u5 : Cx,
  c_eq (c_plus (c_plus (c_plus u1 u2) (c_plus u3 u4)) u5)
       (c_plus (c_plus u1 u5) (c_plus u3 (c_plus u4 u2))).
Proof.
  intros u1 u2 u3 u4 u5.
  apply (c_eq_trans _ (c_plus (c_plus u1 u2) (c_plus (c_plus u3 u4) u5))).
  - apply cplus_lassoc.
  - apply (c_eq_trans _ (c_plus (c_plus u1 u2) (c_plus u5 (c_plus u3 u4)))).
    + apply c_plus_congr; [apply c_eq_refl | apply c_plus_comm].
    + apply (c_eq_trans _ (c_plus u1 (c_plus u2 (c_plus u5 (c_plus u3 u4))))).
      * apply cplus_lassoc.
      * apply (c_eq_trans _ (c_plus u1 (c_plus u5 (c_plus u2 (c_plus u3 u4))))).
        -- apply c_plus_congr; [apply c_eq_refl | apply cplus_rotate_l].
        -- apply (c_eq_trans _
             (c_plus (c_plus u1 u5) (c_plus u2 (c_plus u3 u4)))).
           ++ apply c_eq_sym. apply cplus_lassoc.
           ++ apply c_plus_congr.
              ** apply c_eq_refl.
              ** apply (c_eq_trans _ (c_plus u3 (c_plus u2 u4))).
                 --- apply cplus_rotate_l.
                 --- apply c_plus_congr; [apply c_eq_refl | apply c_plus_comm].
Defined.

(* Section 6. The window sum faces.                                      *)

(* The empty window sum vanishes.                                        *)
Lemma abel_rsum_zero : forall (M N : nat) (r : nat -> Real),
  NatLe N M -> real_eq (abel_rsum M N r) real_zero.
Proof.
  intros M N r. revert M. induction N as [|m IH]; intros M HNM.
  - cbn [abel_rsum]. apply real_eq_refl.
  - cbn [abel_rsum].
    assert (Hltb : Nat.ltb M (S m) = false).
    { apply (proj2 (Nat.ltb_ge M (S m))). apply NatLe_drop. exact HNM. }
    rewrite Hltb.
    apply (real_eq_trans _ (abel_rsum M m r)).
    + exact (r_plus_zero_r_gen (abel_rsum M m r)).
    + apply IH. apply NatLe_lift. apply Nat.le_trans with (S m);
        [apply Nat.le_succ_diag_r | apply NatLe_drop; exact HNM].
Defined.

(* A window sum of nonnegative linear bounds is nonnegative.             *)
Lemma abel_rsum_nonneg : forall (M N : nat) (r : nat -> Real),
  (forall k : nat, real_le real_zero (r k)) ->
  real_le real_zero (abel_rsum M N r).
Proof.
  intros M N r Hr. induction N as [|m IH].
  - cbn [abel_rsum]. apply real_le_refl.
  - cbn [abel_rsum]. destruct (Nat.ltb M (S m)) eqn:Hltb.
    + exact (r_le_zero_plus (abel_rsum M m r) (r (S m)) IH (Hr (S m))).
    + apply (RealSetoid.real_le_compat real_zero real_zero
               (abel_rsum M m r) (real_plus (abel_rsum M m r) real_zero)).
      * apply real_eq_refl.
      * exact (real_eq_sym (real_plus (abel_rsum M m r) real_zero)
                (abel_rsum M m r) (r_plus_zero_r_gen (abel_rsum M m r))).
      * exact IH.
Defined.

(* The two-fold linear triangle face of the squared house (the in-tree   *)
(* carrier of the registered open supply row; consumed as a premise).    *)
Definition abel_tri_pair_face : Set :=
  forall (x y : Cx) (rx ry : Real),
    real_le real_zero rx -> real_le real_zero ry ->
    real_le (c_norm_sq x) (sq rx) ->
    real_le (c_norm_sq y) (sq ry) ->
    real_le (c_norm_sq (c_plus x y)) (sq (real_plus rx ry)).

(* The triangle face lifted to window sums, by induction on the window.  *)
Lemma abel_tri_wsum : forall (Htri : abel_tri_pair_face) (M N : nat)
  (coef : nat -> Real) (vec : nat -> Cx) (r : nat -> Real),
  (forall k : nat, real_le real_zero (r k)) ->
  (forall k : nat,
     real_le (c_norm_sq (c_scale (coef k) (vec k))) (sq (r k))) ->
  real_le (c_norm_sq (c_wsum M N coef vec)) (sq (abel_rsum M N r)).
Proof.
  intros Htri M N. revert M.
  induction N as [|m IH]; intros M coef vec r Hr Hterm.
  - cbn [c_wsum abel_rsum]. apply r_le_of_eq.
    apply (real_eq_trans (c_norm_sq c_zero) real_zero (sq real_zero)
             c_norm_sq_zero_eq
             (real_eq_sym (sq real_zero) real_zero sq_zero_eq)).
  - cbn [c_wsum abel_rsum]. destruct (Nat.ltb M (S m)) eqn:Hltb.
    + apply (Htri (c_wsum M m coef vec) (c_scale (coef (S m)) (vec (S m)))
                  (abel_rsum M m r) (r (S m))).
      * exact (abel_rsum_nonneg M m r Hr).
      * exact (Hr (S m)).
      * exact (IH M coef vec r Hr Hterm).
      * exact (Hterm (S m)).
    + cbn.
      apply (RealSetoid.real_le_compat
               (c_norm_sq (c_wsum M m coef vec))
               (c_norm_sq (c_plus (c_wsum M m coef vec) c_zero))
               (sq (abel_rsum M m r))
               (sq (real_plus (abel_rsum M m r) real_zero))).
      * exact (real_eq_sym _ _
                 (c_norm_sq_wd _ _ (c_plus_zero_r (c_wsum M m coef vec)))).
      * exact (real_eq_sym _ _
                 (sq_eq_wd _ _ (r_plus_zero_r_gen (abel_rsum M m r)))).
      * exact (IH M coef vec r Hr Hterm).
Defined.

(* Section 7. The telescoping faces.                                     *)

(* The unscaled telescope: sum_{M<j<=K} (a j - a (S j)) equals           *)
(* a (S M) - a (S K).                                                    *)
(* The difference-indexed telescope body: the window sum over            *)
(* M < j <= S (M + d) of the step differences telescopes.                *)
Lemma abel_rsum_dif_tele_diff : forall (a : nat -> Real) (M d : nat),
  real_eq (abel_rsum M (S (M + d)) (fun k => dif_seq a k))
          (real_plus (a (S M)) (real_opp (a (S (S (M + d)))))).
Proof.
  intros a M d. induction d as [|d IH].
  - rewrite (Nat.add_0_r M). cbn [abel_rsum].
    assert (Hltb : Nat.ltb M (S M) = true).
    { apply (proj2 (Nat.ltb_lt M (S M))). lia. }
    rewrite Hltb. unfold dif_seq.
    apply (real_eq_trans _
      (real_plus real_zero (real_plus (a (S M)) (real_opp (a (S (S M))))))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact (abel_rsum_zero M M (fun k => dif_seq a k)
                 (NatLe_lift _ _ (Nat.le_refl M))).
      * apply real_eq_refl.
    + abel_pfold.
  - rewrite (Nat.add_succ_r M d).
    change (abel_rsum M (S (S (M + d))) (fun k => dif_seq a k))
      with (real_plus (abel_rsum M (S (M + d)) (fun k => dif_seq a k))
                      (if Nat.ltb M (S (S (M + d)))
                       then dif_seq a (S (S (M + d))) else real_zero)).
    assert (Hltb : Nat.ltb M (S (S (M + d))) = true).
    { apply (proj2 (Nat.ltb_lt M (S (S (M + d))))). lia. }
    rewrite Hltb. unfold dif_seq.
    apply (real_eq_trans _
      (real_plus (real_plus (a (S M)) (real_opp (a (S (S (M + d))))))
                 (real_plus (a (S (S (M + d))))
                            (real_opp (a (S (S (S (M + d))))))))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact IH.
      * apply real_eq_refl.
    + abel_pfold.
Defined.

Lemma abel_rsum_dif_tele : forall (a : nat -> Real) (M K : nat),
  NatLe M K ->
  real_eq (abel_rsum M K (fun k => dif_seq a k))
          (real_plus (a (S M)) (real_opp (a (S K)))).
Proof.
  intros a M K HMK.
  destruct (Nat.eq_dec K M) as [Hkm | Hkm].
  - subst K. apply (real_eq_trans _ real_zero).
    + exact (abel_rsum_zero M M (fun k => dif_seq a k)
               (NatLe_lift _ _ (Nat.le_refl M))).
    + apply real_eq_sym. abel_pfold.
  - assert (H0 : (M <= K)%nat) by (apply NatLe_drop; exact HMK).
    remember (K - M - 1)%nat as d eqn:Hdd.
    assert (Hd : (K = S (M + d))%nat) by lia.
    rewrite Hd.
    apply (abel_rsum_dif_tele_diff a M d).
Defined.

(* The difference-indexed telescope body: the window sum over            *)
(* M < j <= S (M + d) of the step differences telescopes.                *)




(* The scaled telescope: sum_{M<j<=K} (a j - a (S j)) * B equals         *)
(* B * (a (S M) - a (S K)).                                              *)
(* The difference-indexed scaled telescope body.                         *)
Lemma abel_rsum_scale_tele_diff : forall (a : nat -> Real) (B : Real) (M d : nat),
  real_eq (abel_rsum M (S (M + d)) (fun k => real_mult (dif_seq a k) B))
          (real_mult B (real_plus (a (S M)) (real_opp (a (S (S (M + d))))))).
Proof.
  intros a B M d. induction d as [|d IH].
  - rewrite (Nat.add_0_r M). cbn [abel_rsum].
    assert (Hltb : Nat.ltb M (S M) = true).
    { apply (proj2 (Nat.ltb_lt M (S M))). lia. }
    rewrite Hltb. unfold dif_seq.
    apply (real_eq_trans _
      (real_plus real_zero
         (real_mult (real_plus (a (S M)) (real_opp (a (S (S M))))) B))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact (abel_rsum_zero M M (fun k => real_mult (dif_seq a k) B)
                 (NatLe_lift _ _ (Nat.le_refl M))).
      * apply real_eq_refl.
    + abel_pfold.
  - rewrite (Nat.add_succ_r M d).
    change (abel_rsum M (S (S (M + d))) (fun k => real_mult (dif_seq a k) B))
      with (real_plus (abel_rsum M (S (M + d))
                         (fun k => real_mult (dif_seq a k) B))
                      (if Nat.ltb M (S (S (M + d)))
                       then real_mult (dif_seq a (S (S (M + d)))) B
                       else real_zero)).
    assert (Hltb : Nat.ltb M (S (S (M + d))) = true).
    { apply (proj2 (Nat.ltb_lt M (S (S (M + d))))). lia. }
    rewrite Hltb. unfold dif_seq.
    apply (real_eq_trans _
      (real_plus (real_mult B (real_plus (a (S M)) (real_opp (a (S (S (M + d)))))))
                 (real_mult (real_plus (a (S (S (M + d))))
                              (real_opp (a (S (S (S (M + d))))))) B))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact IH.
      * apply real_eq_refl.
    + abel_pfold.
Defined.

Lemma abel_rsum_scale_tele : forall (a : nat -> Real) (B : Real) (M K : nat),
  NatLe M K ->
  real_eq (abel_rsum M K (fun k => real_mult (dif_seq a k) B))
          (real_mult B (real_plus (a (S M)) (real_opp (a (S K))))).
Proof.
  intros a B M K HMK.
  destruct (Nat.eq_dec K M) as [Hkm | Hkm].
  - subst K. apply (real_eq_trans _ real_zero).
    + exact (abel_rsum_zero M M (fun k => real_mult (dif_seq a k) B)
               (NatLe_lift _ _ (Nat.le_refl M))).
    + apply real_eq_sym. abel_pfold.
  - assert (H0 : (M <= K)%nat) by (apply NatLe_drop; exact HMK).
    remember (K - M - 1)%nat as d eqn:Hdd.
    assert (Hd : (K = S (M + d))%nat) by lia.
    rewrite Hd.
    apply (abel_rsum_scale_tele_diff a B M d).
Defined.



(* Section 8. The scaled per-term bound.                                 *)

(* A scaled carrier term is bounded linearly by coef * B whenever the    *)
(* carrier is bounded by B^2 and B is nonnegative and the coefficient is *)
(* nonnegative.  The square of the coefficient feeds the strict branch;  *)
(* a null coefficient collapses both sides by congruence.                *)
Lemma abel_scaled_term_bound : forall (coef B : Real) (z : Cx),
  real_le real_zero coef -> real_le real_zero B ->
  real_le (c_norm_sq z) (real_mult B B) ->
  real_le (c_norm_sq (c_scale coef z)) (sq (real_mult coef B)).
Proof.
  intros coef B z Hc HB Hz.
  apply (RealSetoid.real_le_compat
           (real_mult (sq coef) (c_norm_sq z))
           (c_norm_sq (c_scale coef z))
           (real_mult (sq coef) (real_mult B B))
           (sq (real_mult coef B))).
  - exact (real_eq_sym (c_norm_sq (c_scale coef z))
            (real_mult (sq coef) (c_norm_sq z)) (c_norm_sq_scale_sq coef z)).
  - apply real_eq_of_zero_diff. intro m.
    unfold sq. rewrite !real_mult_proj. simpl. ring.
  - unfold real_le in Hc, Hz. destruct Hc as [Hpos | Heq0].
    + destruct Hz as [Hlt | Heqz].
      * exact (inl (real_lt_mult_mono_r (sq coef) (c_norm_sq z)
                      (real_mult B B)
                      (real_mult_positive coef coef Hpos Hpos) Hlt)).
      * exact (inr (RealSetoid.real_eq_mult_compat (sq coef) (c_norm_sq z)
                      (sq coef) (real_mult B B)
                      (real_eq_refl (sq coef)) Heqz)).
    + assert (Hsq0 : real_eq (sq coef) real_zero).
      { apply (real_eq_trans (sq coef) (real_mult real_zero coef) real_zero).
        - exact (RealSetoid.real_eq_mult_compat coef coef real_zero coef
                   (real_eq_sym real_zero coef Heq0) (real_eq_refl coef)).
        - exact (real_mult_zero_l coef). }
      destruct Hz as [Hlt | Heqz].
      * exact (inr (real_eq_trans
                      (real_mult (sq coef) (c_norm_sq z))
                      real_zero
                      (real_mult (sq coef) (real_mult B B))
                      (real_eq_trans
                         (real_mult (sq coef) (c_norm_sq z))
                         (real_mult real_zero (c_norm_sq z))
                         real_zero
                         (RealSetoid.real_eq_mult_compat (sq coef) (c_norm_sq z)
                            real_zero (c_norm_sq z) Hsq0
                            (real_eq_refl (c_norm_sq z)))
                         (real_mult_zero_l (c_norm_sq z)))
                      (real_eq_sym
                         (real_mult (sq coef) (real_mult B B))
                         real_zero
                         (real_eq_trans
                            (real_mult (sq coef) (real_mult B B))
                            (real_mult real_zero (real_mult B B))
                            real_zero
                            (RealSetoid.real_eq_mult_compat (sq coef)
                               (real_mult B B) real_zero (real_mult B B)
                               Hsq0 (real_eq_refl (real_mult B B)))
                            (real_mult_zero_l (real_mult B B)))))).
      * exact (inr (real_eq_trans
                    (real_mult (sq coef) (c_norm_sq z))
                    (real_mult real_zero (c_norm_sq z))
                    (real_mult (sq coef) (real_mult B B))
                    (RealSetoid.real_eq_mult_compat (sq coef) (c_norm_sq z)
                       real_zero (c_norm_sq z) Hsq0 (real_eq_refl (c_norm_sq z)))
                    (RealSetoid.real_eq_mult_compat real_zero (c_norm_sq z)
                       (sq coef) (real_mult B B)
                       (real_eq_sym (sq coef) real_zero Hsq0) Heqz))).
Defined.

(* The base-window arithmetic fold: x * w equals the head split plus the *)
(* endpoint term over the empty interior.                                *)
Lemma abel_base_fold : forall (x : Real) (z w : Cx),
  c_eq (c_plus (c_scale x (c_plus z w))
               (c_plus (c_scale (real_opp x) z) c_zero))
       (c_scale x w).
Proof.
  intros x z w. unfold c_scale, c_plus. abel_cring.
Defined.

(* The strict-window unfold: when M < k the window sum at S-indexed k    *)
(* splits into the interior window plus the appended term.               *)
Lemma c_wsum_S : forall (M k : nat) (coef : nat -> Real) (vec : nat -> Cx),
  NatLe (S M) k ->
  c_eq (c_wsum M k coef vec)
       (c_plus (c_wsum M (pred k) coef vec) (c_scale (coef k) (vec k))).
Proof.
  intros M k coef vec Hlt.
  destruct k as [|k'].
  - destruct (Nat.nle_succ_0 M (NatLe_drop _ _ Hlt)).
  - cbn [c_wsum pred].
    assert (Hltb : Nat.ltb M (S k') = true).
    { apply (proj2 (Nat.ltb_lt M (S k'))). assert (H0 := NatLe_drop _ _ Hlt); lia. }
    rewrite Hltb. apply c_eq_refl.
Defined.

(* Section 9. Abel summation by parts on inclusive prefixes.             *)

(* The parts identity: the window sum of a_i b_i equals the head term    *)
(* a N times the inclusive prefix at N, plus the endpoint term, plus     *)
(* the mid window of step differences against the interior prefixes.     *)
Lemma abel_parts_id : forall (a : nat -> Real) (b : nat -> Cx) (M N : nat),
  NatLe (S M) N ->
  c_eq (c_wsum M N a b)
       (c_plus (c_scale (a N) (c_abssum (S N) b))
               (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                       (c_wsum M (pred N) (dif_seq a)
                          (fun k => c_abssum (S k) b)))).
Proof.
  intros a b M N. revert N. induction N as [|k IH]; intros HN.
  - destruct (Nat.nle_succ_0 M (NatLe_drop _ _ HN)).
  - destruct (Nat.eq_dec k M) as [Hkm | Hkm].
    + (* the first window: N = S M, both sides fold to a (S M) * b (S M). *)
      subst k.
      assert (HL : c_eq (c_wsum M (S M) a b) (c_scale (a (S M)) (b (S M)))).
      { change (c_wsum M (S M) a b)
          with (c_plus (c_wsum M M a b)
                    (if Nat.ltb M (S M)
                     then c_scale (a (S M)) (b (S M)) else c_zero)).
        assert (Hltb : Nat.ltb M (S M) = true).
        { apply (proj2 (Nat.ltb_lt M (S M))). lia. }
        rewrite Hltb.
        apply (c_eq_trans _ (c_plus c_zero (c_scale (a (S M)) (b (S M))))).
        - apply c_plus_congr.
          + exact (wsum_zero_le M M a b (NatLe_lift _ _ (Nat.le_refl M))).
          + apply c_eq_refl.
        - apply c_plus_zero. }
      apply (c_eq_trans _ (c_scale (a (S M)) (b (S M)))).
      * exact HL.
      * cbn [pred].
        assert (HZ : c_eq (c_wsum M M (dif_seq a) (fun i => c_abssum (S i) b)
                            ) c_zero).
        { exact (wsum_zero_le M M (dif_seq a) (fun i => c_abssum (S i) b)
                   (NatLe_lift _ _ (Nat.le_refl M))). }
        apply (c_eq_trans _
          (c_plus (c_scale (a (S M))
                     (c_plus (c_abssum (S M) b) (b (S M))))
                  (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                          c_zero))).
        -- exact (c_eq_sym
             (c_plus (c_scale (a (S M))
                        (c_plus (c_abssum (S M) b) (b (S M))))
                     (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                             c_zero))
             (c_scale (a (S M)) (b (S M)))
             (abel_base_fold (a (S M)) (c_abssum (S M) b) (b (S M)))).
        -- apply c_plus_congr.
           ++ apply c_eq_refl.
           ++ apply c_plus_congr.
              ** apply c_eq_refl.
              ** exact (c_eq_sym
                     (c_wsum M M (dif_seq a) (fun i => c_abssum (S i) b))
                     c_zero HZ).
    + (* the step window: S M <= k, both windows advance one index. *)
      assert (HSMk : (S M <= k)%nat) by (assert (H0 := NatLe_drop _ _ HN); lia).
      assert (HLtb1 : Nat.ltb M (S k) = true).
      { apply (proj2 (Nat.ltb_lt M (S k))). lia. }
      assert (HLtb2 : Nat.ltb M k = true).
      { apply (proj2 (Nat.ltb_lt M k)). lia. }
      change (c_wsum M (S k) a b)
        with (c_plus (c_wsum M k a b)
                  (if Nat.ltb M (S k)
                   then c_scale (a (S k)) (b (S k)) else c_zero)).
      rewrite HLtb1.
      assert (HWf : c_eq (c_wsum M k (dif_seq a) (fun i => c_abssum (S i) b))
                    (c_plus (c_wsum M (pred k) (dif_seq a)
                               (fun i => c_abssum (S i) b))
                            (c_scale (dif_seq a k) (c_abssum (S k) b)))
        ) by exact (c_wsum_S M k (dif_seq a) (fun i => c_abssum (S i) b) (NatLe_lift _ _ HSMk)).
      assert (HXsplit : c_eq (c_scale (a k) (c_abssum (S k) b))
                 (c_plus (c_scale (a (S k)) (c_abssum (S k) b))
                         (c_scale (dif_seq a k) (c_abssum (S k) b)))).
      { apply (c_eq_trans _
          (c_scale (real_plus (a (S k)) (dif_seq a k)) (c_abssum (S k) b))).
        - apply c_scale_real_wd. apply real_eq_sym.
          exact (r_dif_add_back a k).
        - apply c_eq_sym. apply c_scale_pair_add. }
      apply (c_eq_trans _
        (c_plus (c_plus (c_plus (c_scale (a (S k)) (c_abssum (S k) b))
                           (c_scale (dif_seq a k) (c_abssum (S k) b)))
                   (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                           (c_wsum M (pred k) (dif_seq a)
                              (fun i => c_abssum (S i) b))))
                (c_scale (a (S k)) (b (S k))))).
      ** apply c_plus_congr.
         -- apply (c_eq_trans _
              (c_plus (c_scale (a k) (c_abssum (S k) b))
                      (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                              (c_wsum M (pred k) (dif_seq a)
                                 (fun i => c_abssum (S i) b))))).
            ++ exact (IH (NatLe_lift _ _ HSMk)).
            ++ apply c_plus_congr; [exact HXsplit | apply c_eq_refl].
         -- apply c_eq_refl.
      ** apply (c_eq_trans _
           (c_plus (c_scale (a (S k)) (c_plus (c_abssum (S k) b) (b (S k))))
                   (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                           (c_wsum M k (dif_seq a)
                              (fun i => c_abssum (S i) b))))).
         --- apply (c_eq_trans _
              (c_plus (c_plus (c_scale (a (S k)) (c_abssum (S k) b))
                         (c_scale (a (S k)) (b (S k))))
                      (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                              (c_plus (c_wsum M (pred k) (dif_seq a)
                                  (fun i => c_abssum (S i) b))
                                 (c_scale (dif_seq a k) (c_abssum (S k) b)))))).
             +++ exact (abel_cplus_regroup (c_scale (a (S k)) (c_abssum (S k) b))
                    (c_scale (dif_seq a k) (c_abssum (S k) b))
                    (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                    (c_wsum M (pred k) (dif_seq a) (fun i => c_abssum (S i) b))
                    (c_scale (a (S k)) (b (S k)))).
             +++ apply c_plus_congr.
                 **** apply c_scale_plus || (apply c_eq_sym; apply c_scale_plus).
                 **** apply c_plus_congr.
                     ----- apply c_eq_refl.
                     ----- apply c_eq_sym; exact HWf.
                 --- apply c_eq_refl.
Defined.

(* Section 10. The conditional supply theorem.                           *)

(* The exact carried statement of [abel_tail], closed under the two      *)
(* nonnegativity premises and the two-fold linear triangle face.         *)
Theorem abel_tail_supply :
  forall (a : nat -> Real) (b : nat -> Cx) (B : Real)
         (Ha_anti : forall m n : nat, NatLe m n -> real_le (a n) (a m))
         (Hb_bounded : forall N : nat,
            real_le (c_norm_sq (c_abssum N b)) (real_mult B B))
         (Ha_nonneg : forall n : nat, real_le real_zero (a n))
         (HB_nonneg : real_le real_zero B)
         (Htri : abel_tri_pair_face),
    abel_tail a b B Ha_anti Hb_bounded.
Proof.
  intros a b B Ha_anti Hb_bounded Ha_nonneg HB_nonneg Htri.
  unfold abel_tail. intros M N HMN.
  destruct N as [|n].
  - destruct (Nat.nle_succ_0 M (NatLe_drop _ _ HMN)).
  - assert (HleMn : (M <= n)%nat) by (assert (H0 := NatLe_drop _ _ HMN); lia).
    assert (HID : c_eq (c_wsum M (S n) a b)
      (c_plus (c_scale (a (S n)) (c_abssum (S (S n)) b))
              (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                      (c_wsum M (pred (S n)) (dif_seq a)
                         (fun k => c_abssum (S k) b)))))
      by exact (abel_parts_id a b M (S n) HMN).
    assert (HT1 : real_le (c_norm_sq (c_scale (a (S n)) (c_abssum (S (S n)) b)))
                          (sq (real_mult (a (S n)) B))).
    { exact (abel_scaled_term_bound (a (S n)) B (c_abssum (S (S n)) b)
               (Ha_nonneg (S n)) HB_nonneg (Hb_bounded (S (S n)))). }
    assert (HT0 : real_le
               (c_norm_sq (c_scale (real_opp (a (S M))) (c_abssum (S M) b)))
               (sq (real_mult (a (S M)) B))).
    { apply (RealSetoid.real_le_compat
               (c_norm_sq (c_scale (a (S M)) (c_abssum (S M) b)))
               (c_norm_sq (c_scale (real_opp (a (S M))) (c_abssum (S M) b)))
               (sq (real_mult (a (S M)) B))
               (sq (real_mult (a (S M)) B))).
      - exact (real_eq_sym
                 (c_norm_sq (c_scale (real_opp (a (S M))) (c_abssum (S M) b)))
                 (c_norm_sq (c_scale (a (S M)) (c_abssum (S M) b)))
                 (c_norm_sq_scale_opp_flip (a (S M)) (c_abssum (S M) b))).
      - apply real_eq_refl.
      - exact (abel_scaled_term_bound (a (S M)) B (c_abssum (S M) b)
                 (Ha_nonneg (S M)) HB_nonneg (Hb_bounded (S M))). }
    assert (HMID : real_le
             (c_norm_sq (c_wsum M (pred (S n)) (dif_seq a)
                          (fun k => c_abssum (S k) b)))
             (sq (abel_rsum M (pred (S n))
                    (fun k => real_mult (dif_seq a k) B)))).
    { exact (abel_tri_wsum Htri M (pred (S n)) (dif_seq a)
               (fun k => c_abssum (S k) b)
               (fun k => real_mult (dif_seq a k) B)
               (fun k => r_nonneg_mult (dif_seq a k) B
                  (r_dif_nonneg a Ha_anti k) HB_nonneg)
               (fun k => abel_scaled_term_bound (dif_seq a k) B
                  (c_abssum (S k) b) (r_dif_nonneg a Ha_anti k) HB_nonneg
                  (Hb_bounded (S k)))). }
    assert (HOUT : real_le
             (c_norm_sq (c_plus (c_scale (a (S n)) (c_abssum (S (S n)) b))
                        (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                                (c_wsum M (pred (S n)) (dif_seq a)
                                   (fun k => c_abssum (S k) b)))))
             (sq (real_plus (real_mult (a (S n)) B)
                    (real_plus (real_mult (a (S M)) B)
                       (abel_rsum M (pred (S n))
                          (fun k => real_mult (dif_seq a k) B)))))).
    { apply (Htri (c_scale (a (S n)) (c_abssum (S (S n)) b))
                  (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                          (c_wsum M (pred (S n)) (dif_seq a)
                             (fun k => c_abssum (S k) b)))
                  (real_mult (a (S n)) B)
                  (real_plus (real_mult (a (S M)) B)
                     (abel_rsum M (pred (S n))
                        (fun k => real_mult (dif_seq a k) B)))).
      - exact (r_nonneg_mult (a (S n)) B (Ha_nonneg (S n)) HB_nonneg).
      - exact (r_le_zero_plus (real_mult (a (S M)) B)
                 (abel_rsum M (pred (S n)) (fun k => real_mult (dif_seq a k) B))
                 (r_nonneg_mult (a (S M)) B (Ha_nonneg (S M)) HB_nonneg)
                 (abel_rsum_nonneg M (pred (S n))
                    (fun k => real_mult (dif_seq a k) B)
                    (fun k => r_nonneg_mult (dif_seq a k) B
                       (r_dif_nonneg a Ha_anti k) HB_nonneg))).
      - exact HT1.
      - exact (Htri (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                    (c_wsum M (pred (S n)) (dif_seq a)
                       (fun k => c_abssum (S k) b))
                    (real_mult (a (S M)) B)
                    (abel_rsum M (pred (S n))
                       (fun k => real_mult (dif_seq a k) B))
                    (r_nonneg_mult (a (S M)) B (Ha_nonneg (S M)) HB_nonneg)
                    (abel_rsum_nonneg M (pred (S n))
                       (fun k => real_mult (dif_seq a k) B)
                       (fun k => r_nonneg_mult (dif_seq a k) B
                          (r_dif_nonneg a Ha_anti k) HB_nonneg))
                    HT0 HMID). }
    assert (HTEL : real_eq (abel_rsum M (pred (S n))
                              (fun k => real_mult (dif_seq a k) B))
                           (real_mult B (real_plus (a (S M))
                                       (real_opp (a (S n))))))
      by exact (abel_rsum_scale_tele a B M (pred (S n)) (NatLe_lift M n HleMn)).
    assert (HFIN : real_eq (real_plus (real_mult (a (S n)) B)
                              (real_plus (real_mult (a (S M)) B)
                                 (abel_rsum M (pred (S n))
                                    (fun k => real_mult (dif_seq a k) B))))
                           (real_mult (real_const (2#1))
                              (real_mult B (a (S M))))).
    { apply (real_eq_trans _
        (real_plus (real_mult (a (S n)) B)
           (real_plus (real_mult (a (S M)) B)
              (real_mult B (real_plus (a (S M)) (real_opp (a (S n)))))))).
      - apply RealSetoid.real_eq_plus_compat.
        + apply real_eq_refl.
        + apply RealSetoid.real_eq_plus_compat;
            [apply real_eq_refl | exact HTEL].
      - abel_pfold. }
    apply (RealSetoid.real_le_compat
             (c_norm_sq
                (c_plus (c_scale (a (S n)) (c_abssum (S (S n)) b))
                        (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                                (c_wsum M (pred (S n)) (dif_seq a)
                                   (fun k => c_abssum (S k) b)))))
             (c_norm_sq (c_wsum M (S n) a b))
             (sq (real_plus (real_mult (a (S n)) B)
                    (real_plus (real_mult (a (S M)) B)
                       (abel_rsum M (pred (S n))
                          (fun k => real_mult (dif_seq a k) B)))))
             (sq (real_mult (real_const (2#1)) (real_mult B (a (S M)))))).
    + exact (real_eq_sym
               (c_norm_sq (c_wsum M (S n) a b))
               (c_norm_sq (c_plus (c_scale (a (S n)) (c_abssum (S (S n)) b))
                        (c_plus (c_scale (real_opp (a (S M))) (c_abssum (S M) b))
                                (c_wsum M (pred (S n)) (dif_seq a)
                                   (fun k => c_abssum (S k) b)))))
               (c_norm_sq_wd _ _ HID)).
    + exact (sq_eq_wd _ _ HFIN).
    + exact HOUT.
Defined.

(* Section 11. The assumption audit line.                                *)
Print Assumptions abel_tail_supply.
