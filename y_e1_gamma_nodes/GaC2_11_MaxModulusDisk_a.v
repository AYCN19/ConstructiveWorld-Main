(* ConstructiveWorld-Main - the real-order machine faces of the
   maximum-modulus disk node. *)

(** * GaC2_11_MaxModulusDisk_a: strict and weak order faces,
      reciprocal kit, and the square-root bridge.

    Mission.  Node C2-11 (segment C2, slot W2), machine piece.  The
      strict and weak addition faces of the real line
      ([mm_rplus_zero_r], [mm_lt_plus_r], [mm_lt_sub_r],
      [mm_le_plus_r], [mm_lt_minus_r], [mm_le_plus_compat]), the
      reciprocal kit over positive reals ([mm_inv_mul_one],
      [mm_inv_pos_le], [mm_mult_one_l], [mm_le_eq_l], [mm_le_eq_r],
      [mm_inv_anti], [mm_mult_cancel_eq], [mm_inv_anti_lt]), the
      strict square monotonicity ([mm_sq_strict_mono]), and the
      square-root monotonicity bridge ([mm_sqrt_lt_mono]) consumed
      by the maximum-modulus statements of this node.  All order
      facts propagate from strict-positivity premises through
      monotone faces only; no sign decision on abstract terms is
      performed.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import), [S02_CauchyComplete]
      (order kit, [real_eq_of_zero_diff] ring route, ring laws),
      [S03_QExp] ([real_inv_pos] and its faces), [S07_RealSetoidExpLog]
      ([real_mult_positive], [real_lt_mult_compat],
      [real_lt_plus_compat_lt_le], [RealSetoid.real_eq_le],
      [real_lt_not_eq], [real_weak_trich]), [CxRealPairCore] +
      [CxRealPairExpLog] (pair carrier), [GaC1_Iface_Cx] (complex
      slice), [GaC1_Iface_Real] (C1-01 log monotonicity, C1-04
      rational bridge, C1-05 square root faces) of this development.

    References.  drafts_C2.md C2.11 statement sketch (the squared
      modulus carrier and the explicit first-order increment
      algebra); Ahlfors Ch.2 the first-order growth direction
      argument mirrored at the squared-carrier level.

    Constructivity.  Every named construction is carried by [Set];
      the order predicates are the Set-sorted [real_lt] /
      [real_le]; zero assumed constants; every proof closes under
      the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_11_MaxModulusDisk_a.v] from the flat
      build directory, thermal guard wrapper. *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(* Section 1. Strict and weak addition faces on the real line.           *)
(* ===================================================================== *)

(* x + 0 == x. *)
Lemma mm_rplus_zero_r : forall x : Real, real_eq (real_plus x real_zero) x.
Proof.
  intros [u Hu]. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_opp real_zero real_one]. ring.
Qed.

(* 0 < t gives x < x + t. *)
Lemma mm_lt_plus_r : forall (x t : Real),
  real_lt real_zero t -> real_lt x (real_plus x t).
Proof.
  intros x t Ht.
  pose proof (real_lt_plus_compat_lt_le real_zero t x x Ht (real_le_refl x)) as H.
  apply (real_eq_lt_lt x (real_plus real_zero x) (real_plus x t)).
  - apply (real_eq_trans x (real_plus real_zero x) (real_plus real_zero x)).
    + apply real_eq_sym. exact (g1_plus_zero_l x).
    + apply real_eq_refl.
  - apply (real_lt_eq_lt (real_plus real_zero x) (real_plus t x) (real_plus x t)).
    + exact H.
    + exact (real_plus_comm t x).
Qed.

(* x < y gives y - x > 0, through the pointwise Q comparison shift. *)
Lemma mm_lt_sub_r : forall (x y : Real),
  real_lt x y -> real_lt real_zero (real_plus y (real_opp x)).
Proof.
  intros x y H. destruct H as [eps [Heps [N HN]]].
  destruct y as [u Hu]. destruct x as [v Hv].
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn. specialize (HN n Hn).
    assert (Hid : projT1 (real_plus (existT (fun s : Qseq => cauchy s) u Hu)
                                    (real_opp (existT (fun s : Qseq => cauchy s) v Hv))) n
                    - projT1 real_zero n
                  == projT1 (existT (fun s : Qseq => cauchy s) u Hu) n
                     - projT1 (existT (fun s : Qseq => cauchy s) v Hv) n).
    { cbn [projT1 real_zero real_plus real_opp]. ring. }
    assert (Hcmp : (eps ?= projT1 (real_plus (existT (fun s : Qseq => cauchy s) u Hu)
                                            (real_opp (existT (fun s : Qseq => cauchy s) v Hv))) n
                          - projT1 real_zero n)
                   = (eps ?= projT1 (existT (fun s : Qseq => cauchy s) u Hu) n
                        - projT1 (existT (fun s : Qseq => cauchy s) v Hv) n)).
    { apply Qcompare_comp.
      - apply Qeq_refl.
      - exact Hid. }
    unfold QltT, Qlt_bool. rewrite Hcmp. exact HN.
Qed.

(* 0 <= t gives x <= x + t. *)
Lemma mm_le_plus_r : forall (x t : Real),
  real_le real_zero t -> real_le x (real_plus x t).
Proof.
  intros x t Ht. destruct Ht as [Hlt | Heq].
  - left. exact (mm_lt_plus_r x t Hlt).
  - right. apply (real_eq_trans x (real_plus x real_zero) (real_plus x t)).
    + apply (real_eq_trans x (real_plus real_zero x) (real_plus x real_zero)).
      * apply real_eq_sym. exact (g1_plus_zero_l x).
      * exact (real_plus_comm real_zero x).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * exact Heq.
Qed.

(* x + y < z gives x < z - y. *)
Lemma mm_lt_minus_r : forall (x y z : Real),
  real_lt (real_plus x y) z -> real_lt x (real_plus z (real_opp y)).
Proof.
  intros x y z H.
  pose proof (real_lt_plus_compat_lt_le (real_plus x y) z (real_opp y) (real_opp y) H
                (real_le_refl (real_opp y))) as H2.
  apply (real_eq_lt_lt x (real_plus (real_plus x y) (real_opp y))
                        (real_plus z (real_opp y))).
  - apply real_eq_of_zero_diff. intro n.
    destruct x as [u Hu]. destruct y as [v Hv].
    cbn [projT1 real_plus real_opp real_zero]. ring.
  - exact H2.
Qed.

(* a <= b, c <= d give a + c <= b + d. *)
Lemma mm_le_plus_compat : forall (a b c d : Real),
  real_le a b -> real_le c d -> real_le (real_plus a c) (real_plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct Hab as [Hlt1 | Heq1]; destruct Hcd as [Hlt2 | Heq2].
  - left. exact (real_lt_plus_compat a b c d Hlt1 Hlt2).
  - left. exact (real_lt_plus_compat_lt_le a b c d Hlt1 (RealSetoid.real_eq_le c d Heq2)).
  - left. exact (real_lt_plus_compat_le_lt a b c d (RealSetoid.real_eq_le a b Heq1) Hlt2).
  - right. apply RealSetoid.real_eq_plus_compat; assumption.
Qed.

(* ===================================================================== *)
(* Section 2. Reciprocal kit (positive reals).                           *)
(* ===================================================================== *)

Lemma mm_inv_mul_one : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult (real_inv_pos x Hx) x) real_one.
Proof.
  intros x Hx.
  apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx)) real_one).
  - apply real_mult_comm.
  - exact (real_inv_pos_correct x Hx).
Qed.

Lemma mm_inv_pos_le : forall (x : Real) (Hx : real_lt real_zero x),
  real_le real_zero (real_inv_pos x Hx).
Proof.
  intros x Hx. exact (real_lt_le_iff real_zero _ (inl (real_inv_pos_pos x Hx))).
Qed.

(* 1 * z == z. *)
Lemma mm_mult_one_l : forall z : Real, real_eq (real_mult real_one z) z.
Proof.
  intro z. apply (real_eq_trans (real_mult real_one z) (real_mult z real_one)).
  - apply real_mult_comm.
  - exact (real_mult_one z).
Qed.

(* real_le transport along real_eq on the left. *)
Lemma mm_le_eq_l : forall (a a' b : Real),
  real_eq a' a -> real_le a b -> real_le a' b.
Proof.
  intros a a' b Haa Hle. destruct Hle as [Hlt | Heq].
  - left. exact (real_eq_lt_lt a' a b Haa Hlt).
  - right. apply (real_eq_trans a' a b). exact Haa. exact Heq.
Qed.

(* real_le transport along real_eq on the right. *)
Lemma mm_le_eq_r : forall (a b b' : Real),
  real_le a b -> real_eq b b' -> real_le a b'.
Proof.
  intros a b b' Hle Hbb. destruct Hle as [Hlt | Heq].
  - left. exact (real_lt_eq_lt a b b' Hlt Hbb).
  - right. apply (real_eq_trans a b b'). exact Heq. exact Hbb.
Qed.

(* x <= y (both positive) gives inv y <= inv x. *)
Lemma mm_inv_anti : forall (x y : Real) (Hx : real_lt real_zero x)
                     (Hy : real_lt real_zero y),
  real_le x y -> real_le (real_inv_pos y Hy) (real_inv_pos x Hx).
Proof.
  intros x y Hx Hy Hab.
  pose proof (mm_inv_pos_le x Hx) as Hix0.
  pose proof (mm_inv_pos_le y Hy) as Hiy0.
  pose proof (real_le_mult_compat_weak x y (real_inv_pos x Hx) Hix0 Hab) as H1.
  pose proof (real_le_trans real_one (real_mult x (real_inv_pos x Hx))
                (real_mult y (real_inv_pos x Hx))
                (RealSetoid.real_eq_le real_one (real_mult x (real_inv_pos x Hx))
                   (real_eq_sym _ _ (real_inv_pos_correct x Hx))) H1) as H2.
  pose proof (real_le_mult_compat_weak real_one
                (real_mult y (real_inv_pos x Hx))
                (real_inv_pos y Hy) Hiy0 H2) as H3.
  apply (real_le_trans (real_inv_pos y Hy)
           (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))
           (real_inv_pos x Hx)).
  - assert (Hsh : real_eq
               (real_mult (real_mult y (real_inv_pos x Hx)) (real_inv_pos y Hy))
               (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))).
    + apply real_mult_comm.
    + apply (mm_le_eq_r (real_inv_pos y Hy)
             (real_mult (real_mult y (real_inv_pos x Hx)) (real_inv_pos y Hy))
             (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))
             (mm_le_eq_l (real_mult real_one (real_inv_pos y Hy))
                (real_inv_pos y Hy)
                (real_mult (real_mult y (real_inv_pos x Hx)) (real_inv_pos y Hy))
                (real_eq_sym _ _ (mm_mult_one_l (real_inv_pos y Hy))) H3)
             Hsh).
  - apply (RealSetoid.real_eq_le (real_mult (real_inv_pos y Hy)
                                  (real_mult y (real_inv_pos x Hx)))
             (real_inv_pos x Hx)).
    apply (real_eq_trans
             (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))
             (real_mult real_one (real_inv_pos x Hx))).
    + apply (real_eq_trans
               (real_mult (real_inv_pos y Hy) (real_mult y (real_inv_pos x Hx)))
               (real_mult (real_mult (real_inv_pos y Hy) y) (real_inv_pos x Hx))).
      * apply real_mult_assoc.
      * apply RealSetoid.real_eq_mult_compat.
        -- exact (mm_inv_mul_one y Hy).
        -- apply real_eq_refl.
    + apply (real_eq_trans (real_mult real_one (real_inv_pos x Hx))
               (real_inv_pos x Hx)).
      * exact (mm_mult_one_l (real_inv_pos x Hx)).
      * apply real_eq_refl.
Qed.


(* x < y (both positive) gives inv y < inv x. *)
Lemma mm_mult_cancel_eq : forall (a b c : Real) (Hc : real_lt real_zero c),
  real_eq (real_mult a c) (real_mult b c) -> real_eq a b.
Proof.
  intros a b c Hc Habc. apply real_weak_trich.
  - intro Hlab.
    pose proof (real_lt_mult_compat a b c Hc Hlab) as Hlt.
    assert (Habc' : real_eq (real_mult c a) (real_mult c b)).
    { apply (real_eq_trans (real_mult c a) (real_mult a c)).
      - apply real_mult_comm.
      - apply (real_eq_trans (real_mult a c) (real_mult b c)).
        + exact Habc.
        + apply real_mult_comm. }
    apply (real_lt_not_eq (real_mult c a) (real_mult c b) Hlt Habc').
  - intro Hlba.
    pose proof (real_lt_mult_compat b a c Hc Hlba) as Hlt.
    assert (Hbac' : real_eq (real_mult c b) (real_mult c a)).
    { apply (real_eq_trans (real_mult c b) (real_mult b c)).
      - apply real_mult_comm.
      - apply (real_eq_trans (real_mult b c) (real_mult a c)).
        + apply (real_eq_sym _ _ Habc).
        + apply real_mult_comm. }
    apply (real_lt_not_eq (real_mult c b) (real_mult c a) Hlt Hbac').
Qed.

Lemma mm_inv_anti_lt : forall (x y : Real) (Hx : real_lt real_zero x)
                       (Hy : real_lt real_zero y),
  real_lt x y -> real_lt (real_inv_pos y Hy) (real_inv_pos x Hx).
Proof.
  intros x y Hx Hy Hlt.
  destruct (mm_inv_anti x y Hx Hy (real_lt_le_iff x y (inl Hlt))) as [Hle | Heq].
  - exact Hle.
  - elim (real_lt_not_eq x y Hlt
           (real_eq_sym _ _ (mm_mult_cancel_eq y x (real_inv_pos y Hy)
              (real_inv_pos_pos y Hy)
              (real_eq_trans (real_mult y (real_inv_pos y Hy)) real_one
                 (real_mult x (real_inv_pos y Hy))
                 (real_inv_pos_correct y Hy)
                 (real_eq_trans real_one (real_mult x (real_inv_pos x Hx))
                    (real_mult x (real_inv_pos y Hy))
                    (real_eq_sym _ _ (real_inv_pos_correct x Hx))
                    (RealSetoid.real_eq_mult_compat x (real_inv_pos x Hx) x
                       (real_inv_pos y Hy) (real_eq_refl x) (real_eq_sym _ _ Heq))))))).
Qed.

(* 0 < c, a * c == b * c give a == b. *)

(* ===================================================================== *)
(* Section 3. Square monotonicity and the square-root bridge.            *)
(* ===================================================================== *)

(* 0 <= a, a < b give a*a < b*b, through (b-a)(b+a) > 0. *)
Lemma mm_sq_strict_mono : forall (a b : Real),
  real_le real_zero a -> real_lt a b -> real_lt (real_mult a a) (real_mult b b).
Proof.
  intros a b Ha0 Hlt.
  pose proof (mm_lt_sub_r a b Hlt) as Hba.
  assert (Hbpos : real_lt real_zero b).
  { destruct Ha0 as [Halt | Haeq].
    - exact (real_lt_le_trans real_zero a b Halt (real_lt_le_iff a b (inl Hlt))).
    - apply (real_eq_lt_lt real_zero (real_plus real_zero a) b).
      + apply (real_eq_trans real_zero a (real_plus real_zero a)).
        * exact Haeq.
        * apply real_eq_sym. exact (g1_plus_zero_l a).
      + apply (real_eq_lt_lt (real_plus real_zero a) a b).
        * exact (g1_plus_zero_l a).
        * exact Hlt. }
  assert (Hbap : real_lt real_zero (real_plus b a)).
  { pose proof (real_lt_plus_compat_lt_le real_zero b real_zero a Hbpos Ha0) as H.
    apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus b a)).
    - apply real_eq_of_zero_diff. intro n.
      cbn [projT1 real_plus real_zero]. ring.
    - exact H. }
  assert (HP : real_lt real_zero (real_mult (real_plus b (real_opp a))
                                            (real_plus b a))).
  { exact (real_mult_positive _ _ Hba Hbap). }
  assert (Heq1 : real_eq (real_mult b b)
                   (real_plus (real_mult a a)
                      (real_mult (real_plus b (real_opp a)) (real_plus b a)))).
  { apply real_eq_of_zero_diff. intro n.
    destruct a as [u Hu]. destruct b as [v Hv].
    cbn [projT1 real_plus real_mult real_opp real_zero]. ring. }
  apply (real_lt_eq_lt (real_mult a a)
           (real_plus (real_mult a a)
              (real_mult (real_plus b (real_opp a)) (real_plus b a)))
           (real_mult b b)).
  - exact (mm_lt_plus_r _ _ HP).
  - apply real_eq_sym. exact Heq1.
Qed.

(* x < y (both positive) gives sqrt x < sqrt y, through the log chain. *)
Lemma mm_sqrt_lt_mono : forall (x y : Real) (Hx : real_lt real_zero x)
                        (Hy : real_lt real_zero y),
  real_lt x y -> real_lt (sqrtR x Hx) (sqrtR y Hy).
Proof.
  intros x y Hx Hy Hlt.
  assert (Hlog : real_lt (real_log x Hx) (real_log y Hy))
    by (exact (gaC1_01_log_lt_mono x y Hx Hy Hlt)).
  assert (HhalfT : QltT 0 (1#2)%Q) by reflexivity.
  assert (Hhalf : real_lt real_zero (real_const (1#2)%Q))
    by (exact (gaC1_04_qlt_const_lt 0 (1#2)%Q HhalfT)).
  apply (cauchy_real_exp_mono _ _ (real_lt_mult_compat _ _ _ Hhalf Hlog)).
Qed.

(* The three-term positivity: 0 < x + (y + z) from three positives. *)
Lemma mm_three_pos : forall (x y z : Real)
    (Hx : real_lt real_zero x) (Hy : real_lt real_zero y)
    (Hz : real_lt real_zero z),
  real_lt real_zero (real_plus x (real_plus y z)).
Proof.
  intros x y z Hx Hy Hz.
  apply (real_lt_trans real_zero x (real_plus x (real_plus y z)) Hx).
  exact (mm_lt_plus_r x (real_plus y z)
           (real_lt_trans real_zero y (real_plus y z) Hy (mm_lt_plus_r y z Hz))).
Qed.
