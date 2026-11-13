(** * GaC2_09_DenomZeroSet - consolidating stem of the denominator
      zero set over the d09 machine kit.
    Mission.  All four roster statements of the C2-09 card
      (drafts_C2.md:718-739) are cast: [denom_zero_real_dir] (a), a
      vanishing denominator forces Re s = 1 (the real direction, no
      periodic dependence); [zero_set_membership] (d), the zero points
      [s_at k] lie on the line Re s = 1; [denom_zero_imag_char_holds]
      (b), the constructive two-pi-lattice witness in sigT form
      (discharged through [_g]); [denom_first_order_holds] (c), the
      first-order Taylor remainder face with the explicit constant
      14 (ln 2)^2 on Bishop [real_le_b] (discharged through
      [_h]/[_i]/[_j]; full disclosure in Notes).
    Dependencies.  Stdlib [QArith.QArith], [ZArith], [Lia]; modules
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [GaC1_Iface_Cx] (real_le_b definition,
      c_exp pair form, [gaC1_16_norm_sq_exp], gaC1_17 period faces),
      [GaC1_Iface_Real]; family pieces [GaC2_09_DenomZeroSet_a..j]
      (the d09 kit, the witness kit, and the first-order kit).
    References.  drafts_C2.md C2.09 card and roster :718-739; the v16
      receipt section VII.3 casting spec; Titchmarsh Ch.1 the eta
      quotient denominator 1 - 2^(1-s) (statement architecture only).
    Constructivity.  All statements Set-sorted; all four roster
      statements discharge with zero Sections, zero assumed constants,
      zero admitted goals; every proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet.v]; acceptance via
      50_toolkit/accept_node.py (six-chain gate), thermal-guard wrapped. *)
Require S01_BaseRing.
(** Notes.  Roster disclosure: (b) [denom_zero_imag_char_holds] is
    discharged through the lattice witness [e09_lattice_witness] of
    [_g]; (c) [denom_first_order_holds] is discharged through the
    first-order face [f09_first_order] of [_j] (the uniform exp-Taylor
    remainder kit [_h] and the pointwise engine [_i]); the constant is
    the explicit 14 (ln 2)^2 on Bishop [real_le_b] (the v16 disclosure
    bishop_ordinal_deviation); the draft :735 sign typo is corrected
    to + ln 2 (s - 1).  Section variables concretized per the
    obligations L11/L12: [s_at k] := 1 - (2 pi k)/ln 2, [c_m1] := -1,
    ln 2 := [d09_ln2]. *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
Require Import GaC2_09_DenomZeroSet_e.
Require Import GaC2_09_DenomZeroSet_f.
Require Import GaC2_09_DenomZeroSet_g.
Require Import GaC2_09_DenomZeroSet_h.
Require Import GaC2_09_DenomZeroSet_i.
Require Import GaC2_09_DenomZeroSet_j.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(* Section 1. The concretized section variables.                          *)
(* ===================================================================== *)
Definition c_m1 : Cx := c_opp c_one.
Definition d09_inv_ln2 : Real := real_inv_pos d09_ln2 d09_ln2_pos.
Definition d09_w (s : Cx) : Cx := c_scale d09_ln2 (c_plus c_one (c_opp s)).
Definition s_at (k : Z) : Cx :=
  c_plus c_one (c_opp (c_scale d09_inv_ln2 (d09_i_two_pi k))).

Lemma d09_mult_zero_r : forall x : Real,
  real_eq (real_mult x real_zero) real_zero.
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  rewrite (real_mult_proj x real_zero n). rewrite real_zero_pt.
  cbn [projT1 real_zero]. ring.
Qed.

Lemma d09_mult_zero_l : forall x : Real,
  real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  rewrite (real_mult_proj real_zero x n). rewrite real_zero_pt.
  cbn [projT1 real_zero]. ring.
Qed.

(* ===================================================================== *)
(* Section 2. The real-line cancellation faces.                           *)
(* ===================================================================== *)
Lemma d09_one_plus_opp_eq_zero : forall x : Real,
  real_eq (real_plus real_one (real_opp x)) real_zero -> real_eq x real_one.
Proof.
  intros x H.
  apply (real_eq_trans x (real_plus (real_plus real_one (real_opp x)) x) real_one).
  - apply (real_eq_trans x (real_plus x real_zero)).
    + apply (real_eq_sym (real_plus x real_zero) x). apply real_plus_zero.
    + apply (real_eq_trans (real_plus x real_zero) (real_plus real_zero x)).
      * apply real_plus_comm.
      * apply RealSetoid.real_eq_plus_compat.
        -- exact (real_eq_sym (real_plus real_one (real_opp x)) real_zero H).
        -- apply real_eq_refl.
  - apply (real_eq_trans (real_plus (real_plus real_one (real_opp x)) x)
             (real_plus real_one (real_plus (real_opp x) x))).
    + apply (real_eq_sym _ _ (real_plus_assoc real_one (real_opp x) x)).
    + apply (real_eq_trans (real_plus real_one (real_plus (real_opp x) x))
               (real_plus real_one real_zero)).
      * apply RealSetoid.real_eq_plus_compat.
        -- apply real_eq_refl.
        -- apply (real_eq_trans (real_plus (real_opp x) x)
                    (real_plus x (real_opp x))).
           ++ apply real_plus_comm.
           ++ apply real_plus_opp.
      * apply (real_eq_trans (real_plus real_one real_zero) real_one).
        -- apply real_plus_zero.
        -- apply real_eq_refl.
Qed.

Lemma d09_plus_self_eq_zero : forall u : Real,
  real_eq (real_plus u u) real_zero -> real_eq u real_zero.
Proof.
  intros u H. apply real_weak_trich.
  - intro Hneg.
    exact (real_lt_not_eq (real_plus u u) real_zero
             (real_lt_plus_compat u real_zero u real_zero Hneg Hneg) H).
  - intro Hpos.
    exact (real_lt_not_eq (real_plus real_zero real_zero) (real_plus u u)
             (real_lt_plus_compat real_zero u real_zero u Hpos Hpos)
             (real_eq_sym (real_plus u u) real_zero H)).
Qed.

(* ===================================================================== *)
(* Section 3. The exponential injectivity face.                           *)
(* ===================================================================== *)
Lemma d09_exp_eq_one_zero : forall x : Real,
  real_eq (cauchy_real_exp x) real_one -> real_eq x real_zero.
Proof.
  intros x Hx. apply real_weak_trich.
  - intro Hneg.
    exact (real_lt_not_eq real_one real_one
             (real_eq_lt_lt real_one (cauchy_real_exp x) real_one
                (real_eq_sym (cauchy_real_exp x) real_one Hx)
                (real_lt_eq_lt (cauchy_real_exp x) (cauchy_real_exp real_zero)
                   real_one
                   (cauchy_real_exp_mono x real_zero Hneg)
                   cauchy_real_exp_zero))
             (real_eq_refl real_one)).
  - intro Hpos.
    exact (real_lt_not_eq real_one real_one
             (real_eq_lt_lt real_one (cauchy_real_exp real_zero) real_one
                (real_eq_sym (cauchy_real_exp real_zero) real_one
                   cauchy_real_exp_zero)
                (real_lt_eq_lt (cauchy_real_exp real_zero) (cauchy_real_exp x)
                   real_one
                   (cauchy_real_exp_mono real_zero x Hpos)
                   Hx))
             (real_eq_refl real_one)).
Qed.

(* ===================================================================== *)
(* Section 4. The roster statements.                                      *)
(* ===================================================================== *)
Lemma d09_norm_sq_wd : forall z w : Cx,
  c_eq z w -> real_eq (c_norm_sq z) (c_norm_sq w).
Proof.
  intros z w Hz. destruct Hz as [Hr Hi].
  unfold c_norm_sq.
  apply (RealSetoid.real_eq_plus_compat
             (real_mult (cRe z) (cRe z)) (real_mult (cIm z) (cIm z))
             (real_mult (cRe w) (cRe w)) (real_mult (cIm w) (cIm w))).
  * apply (RealSetoid.real_eq_mult_compat (cRe z) (cRe z) (cRe w) (cRe w)
             Hr Hr).
  * apply (RealSetoid.real_eq_mult_compat (cIm z) (cIm z) (cIm w) (cIm w)
             Hi Hi).
Qed.

Lemma d09_norm_sq_one : real_eq (c_norm_sq c_one) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n.
  unfold c_norm_sq, c_one, cRe.
  cbv beta iota zeta delta
    [c_norm_sq c_one cRe cIm real_mult real_plus real_one real_zero projT1 fst snd].
  ring.
Qed.

Lemma d09_scale_cRe : forall (a : Real) (z : Cx),
  real_eq (cRe (c_scale a z)) (real_mult a (cRe z)).
Proof.
  intros a z. apply real_eq_of_zero_diff. intro n.
  unfold c_scale, cRe.
  cbv beta iota zeta delta
    [c_scale cRe cIm real_mult real_plus projT1 fst snd].
  ring.
Qed.

Lemma denom_zero_real_dir : forall (s : Cx),
  real_eq (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s)))) real_zero ->
  real_eq (cRe s) real_one.
Proof.
  intros s Hn.
  assert (Hd0 : c_eq (d09_denom s) c_zero)
    by (apply c_norm_sq_zero_elim; exact Hn).
  assert (Htp1 : c_eq (two_pow_1ms s) c_one)
    by (apply (d09_c_plus_one_opp_eq_zero (two_pow_1ms s)); exact Hd0).
  assert (Hnorm : real_eq (c_norm_sq (two_pow_1ms s)) real_one).
  { apply (real_eq_trans (c_norm_sq (two_pow_1ms s)) (c_norm_sq c_one)).
    - apply d09_norm_sq_wd. exact Htp1.
    - exact d09_norm_sq_one. }
  assert (Hexpn : real_eq (cauchy_real_exp (real_plus (cRe (d09_w s)) (cRe (d09_w s))))
                    real_one).
  { apply (real_eq_trans (cauchy_real_exp (real_plus (cRe (d09_w s)) (cRe (d09_w s))))
             (c_norm_sq (c_exp (d09_w s)))).
    - apply (real_eq_sym _ _). exact (gaC1_16_norm_sq_exp (d09_w s)).
    - exact Hnorm. }
  assert (Hw0 : real_eq (cRe (d09_w s)) real_zero)
    by (apply d09_plus_self_eq_zero; apply d09_exp_eq_one_zero; exact Hexpn).
  assert (Hrew : real_eq (cRe (d09_w s))
                   (real_mult d09_ln2
                      (real_plus real_one (real_opp (cRe s))))).
  { apply d09_scale_cRe. }
  assert (Hu0 : real_eq (real_mult d09_ln2
                           (real_plus real_one (real_opp (cRe s))))
                   real_zero)
    by (apply (real_eq_trans (real_mult d09_ln2
                                (real_plus real_one (real_opp (cRe s))))
                 (cRe (d09_w s))); [ apply (real_eq_sym _ _ Hrew) | exact Hw0 ]).
  assert (Hu1 : real_eq (real_plus real_one (real_opp (cRe s))) real_zero).
  { apply (real_eq_trans (real_plus real_one (real_opp (cRe s)))
             (real_mult (real_plus real_one (real_opp (cRe s)))
                        (real_mult d09_ln2 (real_inv_pos d09_ln2 d09_ln2_pos)))).
    - apply (real_eq_trans (real_plus real_one (real_opp (cRe s)))
               (real_mult (real_plus real_one (real_opp (cRe s))) real_one)).
      + apply (real_eq_sym (real_mult (real_plus real_one (real_opp (cRe s)))
                              real_one)
                 (real_plus real_one (real_opp (cRe s)))).
        apply real_mult_one.
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact (real_eq_sym (real_mult d09_ln2
                                (real_inv_pos d09_ln2 d09_ln2_pos)) real_one
                   (real_inv_pos_correct d09_ln2 d09_ln2_pos)).
    - apply (real_eq_trans
               (real_mult (real_plus real_one (real_opp (cRe s)))
                  (real_mult d09_ln2 (real_inv_pos d09_ln2 d09_ln2_pos)))
               (real_mult (real_mult (real_plus real_one (real_opp (cRe s))) d09_ln2)
                          (real_inv_pos d09_ln2 d09_ln2_pos))).
      + exact (real_mult_assoc (real_plus real_one (real_opp (cRe s)))
                 d09_ln2 (real_inv_pos d09_ln2 d09_ln2_pos)).
      + exact (real_eq_trans
                 (real_mult (real_mult (real_plus real_one (real_opp (cRe s))) d09_ln2)
                            (real_inv_pos d09_ln2 d09_ln2_pos))
                 (real_mult (real_mult d09_ln2 (real_plus real_one (real_opp (cRe s))))
                            (real_inv_pos d09_ln2 d09_ln2_pos))
                 real_zero
                 (RealSetoid.real_eq_mult_compat
                    (real_mult (real_plus real_one (real_opp (cRe s))) d09_ln2)
                    (real_inv_pos d09_ln2 d09_ln2_pos)
                    (real_mult d09_ln2 (real_plus real_one (real_opp (cRe s))))
                    (real_inv_pos d09_ln2 d09_ln2_pos)
                    (real_mult_comm (real_plus real_one (real_opp (cRe s))) d09_ln2)
                    (real_eq_refl (real_inv_pos d09_ln2 d09_ln2_pos)))
                 (real_eq_trans
                    (real_mult (real_mult d09_ln2 (real_plus real_one (real_opp (cRe s))))
                               (real_inv_pos d09_ln2 d09_ln2_pos))
                    (real_mult real_zero (real_inv_pos d09_ln2 d09_ln2_pos))
                    real_zero
                    (RealSetoid.real_eq_mult_compat
                       (real_mult d09_ln2 (real_plus real_one (real_opp (cRe s))))
                       (real_inv_pos d09_ln2 d09_ln2_pos)
                       real_zero
                       (real_inv_pos d09_ln2 d09_ln2_pos)
                       Hu0
                       (real_eq_refl (real_inv_pos d09_ln2 d09_ln2_pos)))
                    (d09_mult_zero_l (real_inv_pos d09_ln2 d09_ln2_pos)))).
  }
  apply d09_one_plus_opp_eq_zero. exact Hu1.
Qed.

Lemma d09_ln2_lt_one : real_lt d09_ln2 real_one.
Proof. exact (f09_ln2_lt_one). Qed.

Lemma zero_set_membership : forall (k : Z),
  real_eq (cRe (s_at k)) real_one.
Proof.
  intro k. apply real_eq_of_zero_diff. intro n.
  unfold s_at, c_scale, d09_i_two_pi, c_plus, c_opp, c_one, cRe.
  cbn [fst snd].
  rewrite (real_plus_proj real_one
             (real_opp (real_mult d09_inv_ln2 real_zero)) n).
  rewrite (real_opp_proj (real_mult d09_inv_ln2 real_zero) n).
  rewrite (real_mult_proj d09_inv_ln2 real_zero n).
  rewrite (real_zero_pt n).
  ring.
Qed.

(* The (b) roster statement of the C2-09 card, discharged through the
   lattice-witness face of GaC2_09_DenomZeroSet_g: a vanishing
   denominator at Re s = 1 yields an explicit integer k with
   t * ln 2 = 2 pi k. *)
Theorem denom_zero_imag_char_holds : forall (s : Cx) (t : Real),
  real_eq (cIm s) t -> real_eq (cRe s) real_one ->
  real_eq (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s)))) real_zero ->
  sigT (fun k : Z => real_eq (real_mult t d09_ln2) (d09_two_pi k)).
Proof. exact e09_lattice_witness. Defined.

(* The (c) roster statement of the C2-09 card, discharged through the
   first-order face [f09_first_order] of GaC2_09_DenomZeroSet_j: on the
   disk |s - 1|^2 <= 3/4 the first-order Taylor remainder of the
   denominator satisfies |R|^2 <= 14 (ln 2)^2 |s - 1|^2 in the Bishop
   order [real_le_b] (the registered bishop_ordinal_deviation form;
   the draft :735 sign typo corrected to + ln 2 (s - 1)). *)
Theorem denom_first_order_holds : forall (s : Cx),
  real_le_b (c_norm_sq (c_plus s (c_opp c_one))) (real_const (3 / 4)) ->
  real_le_b (c_norm_sq (c_plus (c_plus (two_pow_1ms s) (c_opp c_one))
                                (c_scale d09_ln2 (c_plus s (c_opp c_one)))))
            (real_mult (real_mult (real_mult (real_const 14) d09_ln2) d09_ln2)
                       (c_norm_sq (c_plus s (c_opp c_one)))).
Proof. exact f09_first_order. Defined.
