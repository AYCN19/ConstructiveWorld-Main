(* ===================================================================== *)
(* GaC3_V03_VinoZeta.v                                                    *)
(* Mission. Node C3-V03 (segment C3) - the Vinogradov-type bounds for    *)
(*   zeta and its derivative at the 1-line, on the tree carriers.  The   *)
(*   main statements are the squared-modulus faces of the draft bound    *)
(*   faces: with tau(t) = 1 + |t| and the log-power carrier v03_rpow     *)
(*   (x^a := Re exp(a * log x), a rational, x > 0), the zeta face reads  *)
(*   |zeta(1+it)|^2 <= CV^2 (ln tau)^(4/3) (ln ln tau)^(2/3) + eps       *)
(*   (eps-form, Bishop interface shape), i.e. the square of the draft    *)
(*   face |zeta(1+it)| <= CV (ln tau)^(2/3) (ln ln tau)^(1/3); the       *)
(*   derivative face squares (ln tau)^(4/3) (ln ln tau)^(1/3) to         *)
(*   (ln tau)^(8/3) (ln ln tau)^(2/3).                                   *)
(*   Honest scope (the conditional reduction face): the two analytic     *)
(*   inputs of each main theorem are explicit named Section premises     *)
(*   (the premise family L-V03-A..D): the truncated 1-line               *)
(*   representation of the continuation carrier and the oscillatory      *)
(*   main-sum input at the balancing truncations.  Their designated      *)
(*   supply routes are the B-process completion route (C3-V02) and the   *)
(*   A-process exponential-sum route (C3-V01); the truncated 1-line      *)
(*   representation face beyond those routes is the registered gamma4    *)
(*   deferral (not in this segment's edge set).  The derivation proper   *)
(*   is the assembly: the Cx modulus dilute face                         *)
(*   |z+w|^2 <= 2|z|^2 + 2|w|^2 + eps (pointwise square algebra), the    *)
(*   c_eq split algebra of the carriers, and the explicit constant       *)
(*   bookkeeping 2*(K/4) + 2*(K/4) = K folding the premise bounds into   *)
(*   the draft constants CV, CV'.  The exponent bookkeeping of the       *)
(*   power face is certified at Q level in the certificate slice.        *)
(* Dependencies. GaC3_Z01_LogDerivSeries (z01_ln, the log weight face),  *)
(*   GaC2_Iface_DS (C2.01 Dirichlet partial sums c_zeta_part/c_powq),    *)
(*   GaC2_02_AbsConvTailBound_a (nat_real_pos, c_norm_sq_wd),            *)
(*   CxRealPairCore/ExpLog, S01/S02/S03/S07 (Real carrier, real_log,     *)
(*   real_abs, real order algebra); V01/V02 are consumed through the     *)
(*   premise supply-route registration above (no compile-time            *)
(*   consumption position this round); Stdlib QArith, Lia (ring on Qeq). *)
(* References. Vinogradov 1958 / Korobov 1958 / Karatsuba-Korobov 1963   *)
(*   (the 1-line bound shape; the explicit constants CV, CV' are         *)
(*   premise-carried pending the value audit); Titchmarsh, The Theory    *)
(*   of the Riemann Zeta-Function, the 1-line estimates chapter; card    *)
(*   drafts_C3.md C3-V03 (statement skeleton; squared-face re-carrier).  *)
(* Constructivity. Set-carried statements (real_le / real_lt are Set-    *)
(*   sorted, QleT-family Id-carriers for the certificate slice); no      *)
(*   global assumption commands, no proof-abandonment commands, no       *)
(*   classical principles; the eps-form is the constructive Bishop       *)
(*   interface of the non-decidable order face.                          *)
(* Build. coqc -native-compiler no -q -Q . "" -Q <boot_src> "" (sandbox  *)
(*   pair, from the work directory), single compile lane under the       *)
(*   thermal guard wrapper.                                              *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z01_LogDerivSeries.

Local Open Scope Q_scope.

(* ==== Part 0. The Q square kit (pointwise nonnegativity). ==== *)

(* x*x >= 0 over Q: the sign split through the decidable Qle_bool. *)
Lemma v03_qsq_nonneg : forall x : Q, Qle 0 (x * x).
Proof.
  intro x. destruct (Qle_bool x 0) eqn:E.
  - apply Qle_bool_iff in E.
    assert (H0 : Qle (- 0) (- x)) by (apply Qopp_le_compat; exact E).
    replace (- 0)%Q with 0%Q in H0 by reflexivity.
    apply (Qle_trans 0 ((- x) * (- x)) (x * x)).
    + apply (Qle_trans 0 (0 * (- x)) ((- x) * (- x))).
      * apply qeq_le. ring.
      * apply (Qmult_le_compat_r 0 (- x) (- x) H0 H0).
    + apply qeq_le. ring.
  - assert (Hnle : ~ (x <= 0)) by (intro Hc;
      assert (Hb : Qle_bool x 0 = true) by (apply Qle_bool_iff; exact Hc);
      rewrite Hb in E; discriminate E).
    assert (Hlt : 0 < x) by (apply (Qnot_le_lt x 0); exact Hnle).
    assert (Hle : Qle 0 x) by (apply Qlt_le_weak; exact Hlt).
    apply (Qle_trans 0 (0 * x) (x * x)).
    + apply qeq_le. ring.
    + apply (Qmult_le_compat_r 0 x x Hle Hle).
Qed.

(* The pointwise square-difference face: (a-c)^2 + (b-d)^2 >= 0. *)
Lemma v03_qsqsum_nonneg : forall a b c d : Q,
  Qle 0 ((a - c) * (a - c) + (b - d) * (b - d)).
Proof.
  intros a b c d.
  apply (Qle_trans _ (0 + 0) _).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat _ _ _ _).
    + apply v03_qsq_nonneg.
    + apply v03_qsq_nonneg.
Qed.

(* ==== Part 1. The Cx modulus faces. ==== *)

(* The dilute face (eps-form): |z+w|^2 <= 2|z|^2 + 2|w|^2 + eps.  The     *)
(* proof is the pointwise square algebra (a-c)^2 + (b-d)^2 >= 0 with the  *)
(* eps/2 witness bookkeeping (the real_abs_nonneg_le_eps construction     *)
(* shape of S07).                                                         *)
Lemma v03_norm_sq_dilute : forall (z w : Cx) (eps : Real),
  real_lt real_zero eps ->
  real_le (c_norm_sq (c_plus z w))
    (real_plus (real_plus (real_mult (c_norm_sq z) (real_const 2))
                           (real_mult (c_norm_sq w) (real_const 2)))
               eps).
Proof.
  intros z w eps Heps.
  apply (RealSetoid.real_lt_le_iff_req (c_norm_sq (c_plus z w))
           (real_plus (real_plus (real_mult (c_norm_sq z) (real_const 2))
                                 (real_mult (c_norm_sq w) (real_const 2)))
                      eps)). left.
  unfold real_lt.
  destruct Heps as [eps0 [Heps0 [N0 HN0]]].
  exists (eps0 / 2)%Q. split.
  - apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps0 2).
    + reflexivity.
    + apply QltT_to_Qlt. exact Heps0.
  - exists N0. intros n Hn. apply Qlt_to_QltT.
    assert (Hd : projT1 (real_plus (real_plus (real_mult (c_norm_sq z) (real_const 2))
                                               (real_mult (c_norm_sq w) (real_const 2))) eps) n
                  - projT1 (c_norm_sq (c_plus z w)) n
                  == ((projT1 (cRe z) n - projT1 (cRe w) n) * (projT1 (cRe z) n - projT1 (cRe w) n)
                      + (projT1 (cIm z) n - projT1 (cIm w) n) * (projT1 (cIm z) n - projT1 (cIm w) n))
                     + projT1 eps n).
    { rewrite real_plus_proj, real_plus_proj, real_mult_proj,
              real_mult_proj, real_const_proj.
      rewrite (c_norm_sq_pt (c_plus z w) n), (cRe_plus_pt z w n), (cIm_plus_pt z w n),
              (c_norm_sq_pt z n), (c_norm_sq_pt w n).
      unfold Qminus. ring. }
    rewrite Hd.
    apply (Qlt_trans _ eps0 _).
    + apply q_half_lt_self. apply QltT_to_Qlt. exact Heps0.
    + apply (Qlt_le_trans _ (projT1 eps n) _).
      * assert (Hlt0 : Qlt eps0 (projT1 eps n - projT1 real_zero n))
          by (apply QltT_to_Qlt; exact (HN0 n Hn)).
        assert (Hz : projT1 real_zero n == 0) by (apply real_zero_pt).
        rewrite Hz in Hlt0.
        apply (proj2 (Qlt_minus_iff eps0 (projT1 eps n))).
        assert (Hshape : (projT1 eps n - 0) - eps0 == projT1 eps n - eps0)
          by (unfold Qminus; ring).
        rewrite <- Hshape.
        apply (proj1 (Qlt_minus_iff eps0 (projT1 eps n - 0))). exact Hlt0.
      * apply (Qle_trans _ (0 + projT1 eps n) _).
        -- apply qeq_le. ring.
        -- apply (Qplus_le_compat _ _ _ _).
           ++ exact (v03_qsqsum_nonneg (projT1 (cRe z) n) (projT1 (cIm z) n)
                       (projT1 (cRe w) n) (projT1 (cIm w) n)).
           ++ apply Qle_refl.
Qed.

(* The carrier split: s + (z + (-s)) == z (the c_eq algebra assembling    *)
(* the continuation carrier from its truncated part and the remainder).   *)
Lemma v03_plus_opp_split : forall s z : Cx,
  c_eq (c_plus s (c_plus z (c_opp s))) z.
Proof.
  intros s z.
  apply (c_eq_trans _ (c_plus (c_plus s z) (c_opp s))).
  - apply (c_plus_assoc s z (c_opp s)).
  - apply (c_eq_trans _ (c_plus (c_plus z s) (c_opp s))).
    + apply (c_plus_congr _ _ _ _).
      * apply (c_plus_comm s z).
      * apply c_eq_refl.
    + apply (c_eq_trans _ (c_plus z (c_plus s (c_opp s)))).
      * apply c_eq_sym. apply (c_plus_assoc z s (c_opp s)).
      * apply (c_eq_trans _ (c_plus z c_zero)).
        -- apply (c_plus_congr _ _ _ _).
           ++ apply c_eq_refl.
           ++ apply (c_plus_opp s).
        -- apply (c_eq_trans _ (c_plus c_zero z)).
           ++ apply (c_plus_comm z c_zero).
           ++ apply (c_plus_zero z).
Qed.

(* The constant bridge: 0 <= real_const 2 (the fold multiplier). *)
Lemma v03_H2le : real_le real_zero (real_const 2).
Proof.
  apply (RealSetoid.real_lt_le_iff_req real_zero (real_const 2)). left.
  unfold real_lt. exists (1 # 1)%Q. split.
  - apply Qlt_to_QltT. reflexivity.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    rewrite real_const_proj, (real_zero_pt n).
    reflexivity.
Qed.

(* The fold bookkeeping: 2*(K/4)*Y + 2*(K/4)*Y == K*Y (pointwise Q ring). *)
Lemma v03_Wfold : forall (K : Q) (Y : Real),
  real_eq (real_plus (real_mult (real_mult (real_const (K * (1 # 4))) Y) (real_const 2))
                     (real_mult (real_mult (real_const (K * (1 # 4))) Y) (real_const 2)))
          (real_mult (real_const K) Y).
Proof.
  intros K Y. apply real_eq_of_zero_diff. intro n.
  rewrite real_plus_proj, real_mult_proj, real_mult_proj, real_mult_proj.
  rewrite (real_const_proj (K * (1 # 4)) n), (real_const_proj K n),
          (real_const_proj 2 n).
  unfold Qminus. ring.
Qed.

(* ==== Part 2. The section: carriers, premises, and the main faces. ==== *)

Section V03_Vino.

(* The ordinate and its tau-face. *)
Variable t : Real.

Definition v03_tau : Real := real_plus real_one (real_abs t).

Lemma v03_H16pos : real_lt real_zero (real_const 16).
Proof.
  unfold real_lt. exists (1 # 1)%Q. split.
  - apply Qlt_to_QltT. reflexivity.
  - exists 0%nat. intros n Hn. apply Qlt_to_QltT.
    rewrite real_const_proj, (real_zero_pt n).
    reflexivity.
Qed.

(* GAPASUME slot L-V03-E: the large-ordinate regime premise tau(t) > 16. *)
(* The constructive large-t face: it implies t <> 0 (through the tau     *)
(* face) and keeps the double log in the positive domain where the tree  *)
(* real_log is defined; 16 is the tree-native tau_0 choice whose log     *)
(* regime is pinned by slot L-V03-F below.                               *)
Hypothesis Htz : real_lt (real_const 16) v03_tau.

Definition v03_Htaupos : real_lt real_zero v03_tau :=
  real_lt_trans real_zero (real_const 16) v03_tau v03_H16pos Htz.

Definition v03_ltau : Real := real_log v03_tau v03_Htaupos.

(* GAPASUME slot L-V03-F: the numeric log face ln 16 > 1 (the Z01        *)
(* L-Z01-B shape; its rational shadow 9 < 16 is certified in the         *)
(* certificate slice, the transcendental residue stays slot-carried).    *)
Hypothesis Hln16gt1 : real_lt real_one (real_log (real_const 16) v03_H16pos).

Lemma v03_Hltau1pos : real_lt real_one v03_ltau.
Proof.
  apply (real_lt_trans real_one (real_log (real_const 16) v03_H16pos) v03_ltau).
  - exact Hln16gt1.
  - exact (real_log_lt_mono (real_const 16) v03_tau v03_H16pos v03_Htaupos Htz).
Qed.

Definition v03_Hltau0pos : real_lt real_zero v03_ltau :=
  real_lt_trans real_zero real_one v03_ltau real_lt_zero_one v03_Hltau1pos.

Definition v03_lltau : Real := real_log v03_ltau v03_Hltau0pos.

(* ln ln tau > 0, derived: ln tau > ln 16 > 1 = ln 1 pushes the second   *)
(* log into the positive domain. *)
Lemma v03_Hllpos : real_lt real_zero v03_lltau.
Proof.
  apply (RealSetoid.real_lt_compat (real_log real_one real_lt_zero_one)
           real_zero v03_lltau v03_lltau).
  - exact (real_log_one real_lt_zero_one).
  - apply real_eq_refl.
  - exact (real_log_lt_mono real_one v03_ltau real_lt_zero_one
             v03_Hltau0pos v03_Hltau1pos).
Qed.

(* The rational-exponent power face: x^a := Re(exp(a * log x)) for x > 0 *)
(* and a rational (total on its domain; the tree exp-log carrier).       *)
Definition v03_rpow (x : Real) (Hx : real_lt real_zero x) (a : Q) : Real :=
  cRe (c_exp (c_mult (c_of_real (real_const a)) (c_log x real_zero Hx))).

(* The squared Vinogradov bound faces: the squares of the draft faces    *)
(* (ln tau)^(2/3) (ln ln tau)^(1/3) and (ln tau)^(4/3) (ln ln tau)^(1/3). *)
Definition v03_L2 : Real :=
  real_mult (v03_rpow v03_ltau v03_Hltau0pos (4 # 3))
            (v03_rpow v03_lltau v03_Hllpos (2 # 3)).

Definition v03_L2d : Real :=
  real_mult (v03_rpow v03_ltau v03_Hltau0pos (8 # 3))
            (v03_rpow v03_lltau v03_Hllpos (2 # 3)).

(* The 1-line exponent carrier s = 1 + i t. *)
Definition v03_s1 : Cx := (real_one, t).

(* The 1-line continuation carriers: zeta(1+it) and zeta'(1+it) as        *)
(* section-level data (supplied by the continuation machinery; the       *)
(* slot premises below pin them to the truncated carriers).              *)
Variable zeta1 zeta1d : Cx.

(* The truncated Dirichlet carrier at the 1-line (the C2.01 consumption). *)
Definition v03_zpart (N : nat) : Cx := c_zeta_part nat_real_pos N v03_s1.

(* The log weight on the naturals (the Z01 consumption face). *)
Definition v03_lnreal (n : nat) (Hn : NatLe 1 n) : Real :=
  z01_ln nat_real_pos n Hn.

(* The truncated derivative carrier: -sum_{n<=N} ln(n) n^{-s} (the       *)
(* classical truncated face of zeta' at the 1-line).                     *)
Fixpoint v03_lpart (N : nat) : Cx :=
  match N with
  | O => c_zero
  | Datatypes.S m => c_plus (v03_lpart m)
             (c_scale (v03_lnreal (Datatypes.S m) (NatLe_one_S m))
                      (c_powq nat_real_pos (Datatypes.S m) (NatLe_one_S m) v03_s1))
  end.

Definition v03_dzpart (N : nat) : Cx := c_opp (v03_lpart N).

(* The remainder faces against the continuation carriers. *)
Definition v03_rtail (N : nat) : Cx := c_plus zeta1 (c_opp (v03_zpart N)).
Definition v03_drtail (N : nat) : Cx := c_plus zeta1d (c_opp (v03_dzpart N)).

(* The explicit bound constants (the draft CV / CV' slots; values        *)
(* pending the R4 audit). *)
Variables CV CV' : Q.

(* The balancing truncations (supplied with the slots below). *)
Variables Nbal NbalD : nat.

Definition v03_W1 : Real :=
  real_mult (real_const (CV * CV * (1 # 4))) v03_L2.
Definition v03_W1d : Real :=
  real_mult (real_const (CV' * CV' * (1 # 4))) v03_L2d.

(* GAPASUME slot L-V03-A: the truncated 1-line representation input for  *)
(* zeta - the remainder |zeta(1+it) - sum_{n<=N} n^{-1-it}| bounded by   *)
(* (CV^2/4) * L2 at the balancing truncation Nbal.  Supply route: the    *)
(* B-process completion face (C3-V02) on the continuation truncation;    *)
(* the truncated 1-line representation face beyond that route is the     *)
(* registered gamma4 deferral (not in this segment's edge set).          *)
Hypothesis H1line_trunc : real_le (c_norm_sq (v03_rtail Nbal)) v03_W1.

(* GAPASUME slot L-V03-B: the oscillatory main-sum input for zeta -      *)
(* |sum_{n<=N} n^{-1-it}|^2 bounded by (CV^2/4) * L2 at Nbal.  Supply    *)
(* route: the A-process exponential-sum face (C3-V01 toolkit) on the     *)
(* dyadic block decomposition.                                           *)
Hypothesis H1line_main : real_le (c_norm_sq (v03_zpart Nbal)) v03_W1.

(* GAPASUME slot L-V03-C: the truncated 1-line representation input for  *)
(* zeta' (same shape at CV' and the derivative balancing truncation      *)
(* NbalD).                                                               *)
Hypothesis Hderiv_trunc : real_le (c_norm_sq (v03_drtail NbalD)) v03_W1d.

(* GAPASUME slot L-V03-D: the oscillatory main-sum input for zeta'.      *)
Hypothesis Hderiv_main : real_le (c_norm_sq (v03_dzpart NbalD)) v03_W1d.

(* ---- Main theorem 1 (the zeta face). ---- *)
(* |zeta(1+it)|^2 <= CV^2 * (ln tau)^(4/3) (ln ln tau)^(2/3) + eps: the  *)
(* squared-modulus face of the draft bound                               *)
(* |zeta(1+it)| <= CV * (ln tau)^(2/3) (ln ln tau)^(1/3).                *)
Theorem v03_zeta_1line_vino : forall eps : Real, real_lt real_zero eps ->
  real_le (c_norm_sq zeta1)
    (real_plus (real_mult (real_const (CV * CV)) v03_L2) eps).
Proof.
  intros eps Heps.
  apply (real_le_trans _
           (real_plus (real_plus (real_mult (c_norm_sq (v03_zpart Nbal)) (real_const 2))
                                 (real_mult (c_norm_sq (v03_rtail Nbal)) (real_const 2)))
                      eps) _).
  - apply (real_le_trans _ (c_norm_sq (c_plus (v03_zpart Nbal) (v03_rtail Nbal))) _).
    + apply (RealSetoid.real_eq_le _ _). apply c_norm_sq_wd.
      apply c_eq_sym. exact (v03_plus_opp_split (v03_zpart Nbal) zeta1).
    + exact (v03_norm_sq_dilute (v03_zpart Nbal) (v03_rtail Nbal) eps Heps).
  - apply (real_le_plus_compat _ _ _ _).
    + apply (real_le_trans _
               (real_plus (real_mult v03_W1 (real_const 2))
                          (real_mult v03_W1 (real_const 2))) _).
      * apply (real_le_plus_compat _ _ _ _).
        -- exact (real_le_mult_compat_weak (c_norm_sq (v03_zpart Nbal)) v03_W1
                    (real_const 2) v03_H2le H1line_main).
        -- exact (real_le_mult_compat_weak (c_norm_sq (v03_rtail Nbal)) v03_W1
                    (real_const 2) v03_H2le H1line_trunc).
      * apply (RealSetoid.real_eq_le _ _). exact (v03_Wfold (CV * CV) v03_L2).
    + apply real_le_refl.
Qed.

(* ---- Main theorem 2 (the derivative face). ---- *)
(* |zeta'(1+it)|^2 <= CV'^2 * (ln tau)^(8/3) (ln ln tau)^(2/3) + eps:    *)
(* the squared-modulus face of the draft bound                           *)
(* |zeta'(1+it)| <= CV' * (ln tau)^(4/3) (ln ln tau)^(1/3).              *)
Theorem v03_zeta_deriv_1line_vino : forall eps : Real, real_lt real_zero eps ->
  real_le (c_norm_sq zeta1d)
    (real_plus (real_mult (real_const (CV' * CV')) v03_L2d) eps).
Proof.
  intros eps Heps.
  apply (real_le_trans _
           (real_plus (real_plus (real_mult (c_norm_sq (v03_dzpart NbalD)) (real_const 2))
                                 (real_mult (c_norm_sq (v03_drtail NbalD)) (real_const 2)))
                      eps) _).
  - apply (real_le_trans _ (c_norm_sq (c_plus (v03_dzpart NbalD) (v03_drtail NbalD))) _).
    + apply (RealSetoid.real_eq_le _ _). apply c_norm_sq_wd.
      apply c_eq_sym. exact (v03_plus_opp_split (v03_dzpart NbalD) zeta1d).
    + exact (v03_norm_sq_dilute (v03_dzpart NbalD) (v03_drtail NbalD) eps Heps).
  - apply (real_le_plus_compat _ _ _ _).
    + apply (real_le_trans _
               (real_plus (real_mult v03_W1d (real_const 2))
                          (real_mult v03_W1d (real_const 2))) _).
      * apply (real_le_plus_compat _ _ _ _).
        -- exact (real_le_mult_compat_weak (c_norm_sq (v03_dzpart NbalD)) v03_W1d
                    (real_const 2) v03_H2le Hderiv_main).
        -- exact (real_le_mult_compat_weak (c_norm_sq (v03_drtail NbalD)) v03_W1d
                    (real_const 2) v03_H2le Hderiv_trunc).
      * apply (RealSetoid.real_eq_le _ _). exact (v03_Wfold (CV' * CV') v03_L2d).
    + apply real_le_refl.
Qed.

End V03_Vino.
