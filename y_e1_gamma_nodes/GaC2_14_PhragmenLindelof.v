(* ConstructiveWorld-Main - the Phragmen-Lindelof indicator face of the
   strip: pointwise subquadratic-growth bound with the explicit
   (eps,T) selector carrier. *)

(** * GaC2_14_PhragmenLindelof: Phragmen-Lindelof pointwise face.

    Mission.  Node C2-14 (segment C2, slot W4), indicator-principle
      piece.  Carriers: the squared unit [sq], the tree-carried
      rational maximum inside [max_sq], the closed-strip membership
      [strip_member], the local power-series expansion slot
      [local_exp_at] / [strip_local_exp] (obligation L19), the
      rational-exponent power [r_pow] and the one-capped growth
      carrier [grow_bound] (obligation L20; the cap
      [real_max (real_abs y) real_one] is forced by the positivity
      premise of the constructive log carrier), the data-level
      selector criterion [pl_selector_ok] (obligation L21; its body
      is f-free so the certificate face can sample it), the
      truncation identity [pl_norm_sq_trunc_eq] (the squared modulus
      of f at z equals the squared modulus of the truncated function
      f z e^{eps z^2} times e^{2 eps (Im z^2 - Re z^2)}), and the
      main pointwise statement [pl_strip_point]: a strip function
      with the line bounds M0 and M1, the one-capped subquadratic
      growth, and local expandability satisfies, at every strip point
      z and every accuracy delta, a witness pair (eps,T) with the
      squared bound max(M0,M1)^2 + delta^2, supplied through the W4
      consumer face [pl_w4_consumer_face].  The consumer face is the
      single explicit GAPASUME carrying premise of this wave: its
      discharge consumes the GaC2_11 rectangle maximum-modulus chain
      over [0,1] x [-T,T] together with the GaC2_12 coefficient
      faces, and shrinks monotonically when the mothers land.

    Dependencies.  Stdlib [QArith], [QArith.Qabs], [QArith.Qminmax].
      Requires [S01_BaseRing]
      (selective [NatLe]), [S02_CauchyComplete] (the real carrier,
      [real_eq_of_zero_diff], the pointwise ring faces), [S03_QExp]
      ([cauchy_real_exp], [cauchy_real_exp_pos],
      [cauchy_real_exp_zero], [real_abs], [Qhalf_pos]),
      [S07_RealSetoidExpLog] ([cauchy_real_exp_plus],
      [cauchy_real_exp_wd], [real_lt_zero_one], [cw_log],
      [real_max], the RealSetoid transfer faces), [CxRealPairCore] +
      [CxRealPairExpLog] (the pair carrier, [cdiff],
      [c_norm_sq_mul], [c_scale]), [GaC1_Iface_Cx] (the C1-16 modulus
      identity [gaC1_16_norm_sq_exp]), [GaC1_Iface_Real] (the C1-06
      exponential monotonicity [g06_exp_le]), and the W-wave mothers
      [GaC2_11_MaxModulusDisk], [GaC2_12_CauchyCoeffEst] (the draft
      Require header of drafts_C2.md C2.14; consumed by the
      consumer-face discharge wave).

    References.  drafts_C2.md C2.14 statement sketch (the
      [pl_strip_point] shape, the [pl_selector_ok] signature, the
      [grow_bound] / [max_sq] / [strip_member] / [strip_local_exp]
      carriers); the C2.14 card proposition (the strip indicator
      principle with the exp(eps z^2) truncation and the explicit
      (eps,T) management); Titchmarsh Ch.5 the Phragmen-Lindelof
      principle.

    Constructivity.  Every named construction is carried by [Set];
      the order predicates are the Set-sorted [real_lt] / [real_le];
      the witness pair is a [sigT]; zero assumed constants; the
      truncation identity and the closure chain close under the
      global context.  Carrying-form registration: the rectangle
      maximum-modulus consumption and the (eps,T) selector closure
      live in [pl_w4_consumer_face] until the mothers land.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_14_PhragmenLindelof.v] from the flat
      build directory under the thermal-guard wrapper; the compile
      gate is deferred until the W-wave mothers land, since the
      Require header follows the draft canon. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs QArith.Qminmax.
Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk.
Require Import GaC2_12_CauchyCoeffEst.

(* ---- Section 1: the order and carrier kit. ---- *)

Definition sq (u : Real) : Real := real_mult u u.

Definition max_sq (M0 M1 : Real) : Real := real_max (sq M0) (sq M1).

Lemma pl_cap_pos : forall y : Real,
  real_lt real_zero (real_max (real_abs y) real_one).
Proof.
  intro y.
  assert (H12 : (1#2)%Q < (1#1)%Q) by (cbv; reflexivity).
  exists (1#2)%Q. split.
  - exact (Qlt_to_QltT 0%Q (1#2)%Q Qhalf_pos).
  - exists O. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_max_proj (real_abs y) real_one n).
    rewrite (real_abs_proj y n).
    cbn [projT1 real_zero].
    assert (Hm0 : forall M : Q, (M - 0)%Q == M)
      by (intro M; unfold Qminus; ring).
    rewrite (Hm0 (Qminmax.Qmax (Qabs (projT1 y n)) (projT1 real_one n))).
    cbn [projT1 real_one].
    apply (Qlt_le_trans (1#2)%Q (1#1)%Q
             (Qminmax.Qmax (Qabs (projT1 y n)) (1#1)%Q)).
    + exact H12.
    + apply Q.le_max_r.
Qed.

Definition r_pow (rho : Q) (x : Real) (Hx : real_lt real_zero x) : Real :=
  cauchy_real_exp (real_mult (real_const rho) (cw_log x Hx)).

Definition grow_bound (A B : Real) (rho : Q) (y : Real) : Real :=
  real_mult (sq A)
    (cauchy_real_exp
       (real_mult (real_const (2#1)%Q)
          (real_mult B
             (r_pow rho (real_max (real_abs y) real_one)
                     (pl_cap_pos y))))).

(* ---- Section 2: the strip and the local expansion slot. ---- *)

Definition strip_member (z : Cx) : Set :=
  S01_BaseRing.And (real_le real_zero (cRe z)) (real_le (cRe z) real_one).

Fixpoint cpow (z : Cx) (n : nat) : Cx :=
  match n with
  | O => c_one
  | S k => c_mult z (cpow z k)
  end.

Fixpoint pl_poly (a : nat -> Cx) (u : Cx) (n : nat) : Cx :=
  match n with
  | O => c_zero
  | S k => c_plus (c_mult (a k) (cpow u k)) (pl_poly a u k)
  end.

Definition local_exp_at (f : Cx -> Cx) (z : Cx) : Set :=
  sigT (fun r : Real =>
    S01_BaseRing.And (real_lt real_zero r)
        (sigT (fun a : nat -> Cx =>
          forall w : Cx, real_lt (c_norm_sq (cdiff w z)) r ->
            forall epsq : Q, QltT 0 epsq ->
              sigT (fun N : nat => forall n : nat, NatLe N n ->
                real_lt (c_norm_sq
                           (cdiff (f w) (pl_poly a (cdiff w z) n)))
                        (real_const epsq))))).

Definition strip_local_exp (f : Cx -> Cx) : Set :=
  forall z : Cx, strip_member z -> local_exp_at f z.

(* ---- Section 3: the truncation kit and the selector criterion. ---- *)

Definition pl_trunc_arg (eps : Real) (z : Cx) : Cx :=
  c_scale eps (c_mult z z).

Definition pl_edge_factor (eps : Real) : Real :=
  cauchy_real_exp (real_plus eps eps).

Definition pl_point_factor (eps : Real) (z : Cx) : Real :=
  cauchy_real_exp
    (real_mult (real_plus eps eps)
               (real_plus (sq (cIm z)) (real_opp (sq (cRe z))))).

Definition pl_selector_ok (f : Cx -> Cx) (M0 M1 A B : Real) (rho : Q)
           (z : Cx) (eps T : Real) : Set :=
  S01_BaseRing.And (real_lt (cIm z) T)
  (S01_BaseRing.And (real_lt (real_opp (cIm z)) T)
  (S01_BaseRing.And (real_lt real_zero eps)
  (S01_BaseRing.And (real_lt real_zero T)
       (real_le (grow_bound A B rho T) (max_sq M0 M1))))).

(* ---- Section 4: the truncation identity. ---- *)

Lemma pl_strip_arg_pair_zero : forall X Y : Real,
  real_eq (real_plus (real_plus X (real_opp Y))
                     (real_plus Y (real_opp X)))
          real_zero.
Proof.
  intros [u Hu] [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_opp real_zero projT1]. ring.
Qed.

Lemma pl_trunc_args_sum_zero : forall (eps : Real) (z : Cx),
  real_eq (real_plus (real_mult (real_plus eps eps)
                                (real_plus (sq (cRe z))
                                           (real_opp (sq (cIm z)))))
                     (real_mult (real_plus eps eps)
                                (real_plus (sq (cIm z))
                                           (real_opp (sq (cRe z))))))
          real_zero.
Proof.
  intros [u Hu] [[a Ha] [b Hb]].
  apply real_eq_of_zero_diff. intro n.
  cbn [sq cRe cIm fst snd real_plus real_mult real_opp real_zero
       projT1]. ring.
Qed.

Lemma pl_norm_sq_trunc_eq : forall (f : Cx -> Cx) (eps : Real) (z : Cx),
  real_eq (c_norm_sq (f z))
          (real_mult (c_norm_sq (c_mult (f z) (c_exp (pl_trunc_arg eps z))))
                     (pl_point_factor eps z)).
Proof.
  intros f eps z.
  unfold pl_trunc_arg, pl_point_factor.
  assert (Hre : real_eq
                  (real_plus (cRe (c_scale eps (c_mult z z)))
                             (cRe (c_scale eps (c_mult z z))))
                  (real_mult (real_plus eps eps)
                             (real_plus (sq (cRe z))
                                        (real_opp (sq (cIm z)))))).
  { apply real_eq_of_zero_diff. intro n.
    destruct eps as [u Hu]. destruct z as [[a Ha] [b Hb]].
    cbn [c_scale c_mult c_plus c_opp cRe cIm sq c_norm_sq
         fst snd real_plus real_mult real_opp projT1]. ring. }
  set (S := real_mult (real_plus eps eps)
                      (real_plus (sq (cRe z)) (real_opp (sq (cIm z))))).
  set (S' := real_mult (real_plus eps eps)
                       (real_plus (sq (cIm z)) (real_opp (sq (cRe z))))).
  assert (Hg : real_eq
                 (c_norm_sq (c_mult (f z)
                                    (c_exp (c_scale eps (c_mult z z)))))
                 (real_mult (c_norm_sq (f z)) (cauchy_real_exp S))).
  { apply (real_eq_trans
             _ (real_mult (c_norm_sq (f z)) (c_norm_sq (c_exp (c_scale eps (c_mult z z)))))).
    - exact (c_norm_sq_mul (f z) (c_exp (c_scale eps (c_mult z z)))).
    - apply (real_eq_trans
               _ (real_mult (c_norm_sq (f z))
                            (cauchy_real_exp (real_plus (cRe (c_scale eps (c_mult z z))) (cRe (c_scale eps (c_mult z z))))))).
      + exact (RealSetoid.real_eq_mult_compat
                 (c_norm_sq (f z))
                 (c_norm_sq (c_exp (c_scale eps (c_mult z z))))
                 (c_norm_sq (f z))
                 (cauchy_real_exp (real_plus (cRe (c_scale eps (c_mult z z))) (cRe (c_scale eps (c_mult z z)))))
                 (real_eq_refl (c_norm_sq (f z)))
                 (gaC1_16_norm_sq_exp (c_scale eps (c_mult z z)))).
      + exact (RealSetoid.real_eq_mult_compat
                 (c_norm_sq (f z))
                 (cauchy_real_exp (real_plus (cRe (c_scale eps (c_mult z z))) (cRe (c_scale eps (c_mult z z)))))
                 (c_norm_sq (f z))
                 (cauchy_real_exp S)
                 (real_eq_refl (c_norm_sq (f z)))
                 (cauchy_real_exp_wd (real_plus (cRe (c_scale eps (c_mult z z))) (cRe (c_scale eps (c_mult z z)))) S Hre)). }
  assert (Hinv : real_eq (real_mult (cauchy_real_exp S)
                                    (cauchy_real_exp S'))
                         real_one).
  { apply (real_eq_trans _ (cauchy_real_exp (real_plus S S'))).
    - exact (real_eq_sym _ _ (cauchy_real_exp_plus S S')).
    - apply (real_eq_trans _ (cauchy_real_exp real_zero)).
      + exact (cauchy_real_exp_wd (real_plus S S') real_zero
                 (pl_trunc_args_sum_zero eps z)).
      + exact (cauchy_real_exp_zero). }
  apply (real_eq_trans
           _ (real_mult (real_mult (c_norm_sq (f z)) (cauchy_real_exp S))
                        (cauchy_real_exp S'))).
  - apply (real_eq_trans
             _ (real_mult (c_norm_sq (f z))
                          (real_mult (cauchy_real_exp S)
                                     (cauchy_real_exp S')))).
    + apply (real_eq_sym _ _).
      apply (real_eq_trans
               _ (real_mult (c_norm_sq (f z)) real_one)).
      * exact (RealSetoid.real_eq_mult_compat
                 (c_norm_sq (f z))
                 (real_mult (cauchy_real_exp S) (cauchy_real_exp S'))
                 (c_norm_sq (f z))
                 real_one
                 (real_eq_refl (c_norm_sq (f z)))
                 Hinv).
      * exact (real_mult_one (c_norm_sq (f z))).
    + exact (real_mult_assoc (c_norm_sq (f z))
               (cauchy_real_exp S) (cauchy_real_exp S')).
  - exact (RealSetoid.real_eq_mult_compat
             (real_mult (c_norm_sq (f z)) (cauchy_real_exp S))
             (cauchy_real_exp S')
             (c_norm_sq (c_mult (f z) (c_exp (c_scale eps (c_mult z z)))))
             (cauchy_real_exp S')
             (real_eq_sym _ _ Hg) (real_eq_refl (cauchy_real_exp S'))).
Qed.

(* ---- Section 5: the W4 consumer face and the main pointwise statement. ---- *)

Definition pl_w4_consumer_face (f : Cx -> Cx) (M0 M1 A B : Real)
           (rho : Q) : Set :=
  forall (z : Cx) (delta : Real), strip_member z -> real_lt real_zero delta ->
    sigT (fun eps : Real =>
      sigT (fun T : Real =>
        S01_BaseRing.And (pl_selector_ok f M0 M1 A B rho z eps T)
        (S01_BaseRing.And (real_le (c_norm_sq (c_mult (f z) (c_exp (pl_trunc_arg eps z))))
                      (real_mult (max_sq M0 M1) (pl_edge_factor eps)))
             (real_le (real_mult (c_norm_sq
                                    (c_mult (f z)
                                            (c_exp (pl_trunc_arg eps z))))
                                 (pl_point_factor eps z))
                      (real_plus (max_sq M0 M1) (sq delta)))))).

Lemma pl_strip_point :
  forall (f : Cx -> Cx) (M0 M1 A B : Real) (rho : Q),
  QltT rho (2#1)%Q ->
  strip_local_exp f ->
  (forall y : Real, real_le (c_norm_sq (f (real_zero, y))) (sq M0)) ->
  (forall y : Real, real_le (c_norm_sq (f (real_one, y))) (sq M1)) ->
  (forall x y : Real, strip_member (x, y) ->
     real_le (c_norm_sq (f (x, y))) (grow_bound A B rho y)) ->
  pl_w4_consumer_face f M0 M1 A B rho ->
  forall (z : Cx) (delta : Real),
  strip_member z -> real_lt real_zero delta ->
  { eps : Real & { T : Real &
    S01_BaseRing.And (real_lt real_zero eps)
    (S01_BaseRing.And (real_lt real_zero T)
    (S01_BaseRing.And (pl_selector_ok f M0 M1 A B rho z eps T)
         (real_le (c_norm_sq (f z))
                  (real_plus (max_sq M0 M1) (sq delta))))) } }.
Proof.
  intros f M0 M1 A B rho Hrho Hloc Hb0 Hb1 Hgrow Hw4 z delta Hsz Hdelta.
  destruct (Hw4 z delta Hsz Hdelta) as [eps [T [Hsel [Hraw Hclose]]]].
  destruct Hsel as [Hyz1 [Hyz2 [Heps [HT Hdamp]]]].
  exists eps. exists T.
  split. exact Heps.
  split. exact HT.
  split.
  - split. exact Hyz1.
    split. exact Hyz2.
    split. exact Heps.
    split. exact HT.
    exact Hdamp.
  - apply (real_le_trans
             _ (real_mult
                  (c_norm_sq (c_mult (f z) (c_exp (pl_trunc_arg eps z))))
                  (pl_point_factor eps z))).
    + apply (RealSetoid.real_eq_le _ _).
      exact (pl_norm_sq_trunc_eq f eps z).
    + exact Hclose.
Qed.
