(* ===================================================================== *)
(* GaC3_Z04_ZetaMainPart.v                                                *)
(* Mission. Node C3-Z04 (segment C3): the main-part expansion of zeta on  *)
(*   the strip, on the tree carriers: zeta(s) = 1/(s-1) + O_B(1) with     *)
(*   explicit constants.  The main part is the pole carrier [z04_mp] (the *)
(*   rational complex inverse kernel (a-1, b) of P05 embedded at Cx);     *)
(*   the derivative main part is [z04_mp2] (1/(s-1)^2, the square of the *)
(*   pole carrier; pair reading ((x^2-y^2), -2xy) / (x^2+y^2)^2).  The   *)
(*   three card faces are cast as squared-modulus slot theorems (Bishop  *)
(*   eps form) with their slots in the _b slice.  The self-cast core is  *)
(*   the pole carrier algebra: the kernel identity, the exact norm face  *)
(*   |mp|^2 = 1/d, the strip cap |mp|^2 <= 4, the square identity of     *)
(*   mp2, and the shared split engine z + y == (x + y) + (z - x) with    *)
(*   the V03 dilute face and the constant-fold bookkeeping.  Each        *)
(*   difference carrier subtracts exactly 1/(s-1) (or adds 1/(s-1)^2):  *)
(*   the card main-part-difference shape on the C2 truncated zeta, the   *)
(*   Z01 von Mangoldt and the log-weight partial sums.                   *)
(* Dependencies. [S01_BaseRing] (NatLe, the Set-sorted Id carrier),       *)
(*   [S02_CauchyComplete] (Real order, QleT'/QltT bridges),               *)
(*   [S07_RealSetoidExpLog] (real_const order faces, RealSetoid),         *)
(*   [CxRealPairCore] + [CxRealPairExpLog] (base pair),                   *)
(*   [GaC2_Iface_DS] (C2.01 [c_zeta_part], C2.03 [zeta_part_add_R_N_stem] *)
(*   re-exported through the C2.04 slice: the cross-segment consumption), *)
(*   [GaC2_02_AbsConvTailBound_a] ([nat_real_pos], [c_norm_sq_wd]),       *)
(*   [GaC3_Z01_LogDerivSeries] ([z01_ln], [z01_manpart]: the              *)
(*   log-derivative carrier), [GaC3_P05_CauchyFormula] ([GaC3_P05_cinv]   *)
(*   kernel and its Cx identity face), [GaC3_V03_VinoZeta]                *)
(*   ([v03_norm_sq_dilute], [v03_plus_opp_split], [v03_qsq_nonneg],       *)
(*   [v03_H2le]: the modulus engine of the first W3 casting); Stdlib      *)
(*   [QArith].  The Z03 casting is the GREEN precondition of this node    *)
(*   (the racing engine over the same partial-sum carriers); it enters    *)
(*   through the supply-route registration (no compile-time consumption   *)
(*   position this round).                                                *)
(* References. drafts_C3.md C3-Z04 card (statement skeleton and slot      *)
(*   discipline); ZZ theory (AFP PNT_with_Remainder) zeta_bound family    *)
(*   :197-268 (the explicit strip-constant discipline 12 + 2|Im s| with   *)
(*   the 1/11 window); Titchmarsh, The Theory of the Riemann              *)
(*   Zeta-Function, the main-part expansion at s = 1; tree precedent      *)
(*   [GaC3_V03_VinoZeta] (squared-face re-carrier, slot family shape).    *)
(* Constructivity. Set-carried statements (real_le / real_lt / QleT' /    *)
(*   QltT are Set-sorted); no global assumption commands, no proof        *)
(*   abandonment, no classical principles; the eps form is the Bishop     *)
(*   interface of the non-decidable order face; no computation tokens in  *)
(*   this stem (the literal bands live in the certificate slice).         *)
(* Build. coqc -native-compiler no -q -Q . "" -Q ../boot_src "" from the  *)
(*   work directory, single compile lane under the thermal guard wrapper. *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Require Import GaC2_03_a.
Require Import HansonLcm.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_P05_CauchyFormula.
Require Import GaC3_V03_VinoZeta.

Local Open Scope Q_scope.

(* ==== Part 0. The rational bookkeeping kit. ==== *)

(* Square monotonicity: a nonnegative multiplier preserves the order. *)
Lemma z04_qsq_mono : forall x y : Q, Qle 0 x -> Qle x y -> Qle (x * x) (y * y).
Proof.
  intros x y Hx0 Hxy.
  apply (Qle_trans (x * x) (x * y) (y * y)).
  - apply (Qle_trans (x * x) (y * x) (x * y)).
    + apply (Qmult_le_compat_r x y x Hxy Hx0).
    + apply qeq_le. ring.
  - apply (Qmult_le_compat_r x y y Hxy (Qle_trans 0 x y Hx0 Hxy)).
Qed.

(* The constant transport: the rational order shadow reads at real_const. *)
Lemma z04_const_le : forall x y : Q, QleT' x y -> real_le (real_const x) (real_const y).
Proof.
  intros x y H.
  apply QleT'_to_Qle in H.
  destruct (Q_dec x y) as [[Hlt | Hgt] | Heq].
  - left. exact (real_const_lt x y Hlt).
  - destruct (Qlt_not_le y x Hgt H).
  - right. apply real_eq_of_zero_diff. intro n.
    rewrite (real_const_proj x n), (real_const_proj y n).
    rewrite Heq. ring.
Qed.

(* The reciprocal read: with d positive and 1 <= k*d, one has 1/d <= k. *)
Lemma z04_inv_le : forall d k : Q, QltT 0 d -> QleT' 1 (k * d) -> QleT' (/ d) k.
Proof.
  intros d k Hd Hk.
  apply QltT_to_Qlt in Hd.
  apply QleT'_to_Qle in Hk.
    assert (Hdne : ~ (d == 0)).
  { intro Hh. exact (Qlt_not_eq 0 d Hd (Qeq_sym d 0 Hh)). }
  assert (Hinv1 : d * / d == 1) by exact (Qmult_inv_r d Hdne).
  assert (Hpos : 0 <= / d).
  { apply Qlt_le_weak. exact (Qinv_lt_0_compat d Hd). }
  apply Qle_to_QleT'.
  apply (Qle_trans (/ d) (k * d * / d) k).
  - apply (Qle_trans (/ d) (1 * / d) (k * d * / d)).
    + apply qeq_le. ring.
    + apply (Qmult_le_compat_r 1 (k * d) (/ d) Hk Hpos).
  - apply (Qle_trans (k * d * / d) (k * (d * / d)) k).
    + apply qeq_le. ring.
    + rewrite Hinv1. apply qeq_le. ring.
Qed.

(* The constant fold: two quarter-squares double to the square, with the *)
(* eps summand carried along (the pointwise ring face). *)
Lemma z04_fold_eps : forall (K : Q) (eps : Real),
  real_eq (real_plus (real_plus (real_mult (real_const (K * (1 # 4))) (real_const 2))
                                (real_mult (real_const (K * (1 # 4))) (real_const 2)))
                     eps)
          (real_plus (real_const K) eps).
Proof.
  intros K eps. apply real_eq_of_zero_diff. intro n.
  rewrite real_plus_proj, real_plus_proj, real_plus_proj, real_mult_proj.
  rewrite (real_const_proj (K * (1 # 4)) n), (real_const_proj K n),
          (real_const_proj 2 n).
  unfold Qminus. ring.
Qed.

(* The Q pair congruence: equal coordinates give equal embedded points. *)
Lemma z04_ofQ_congr : forall u u' v v' : Q,
  Qeq u u' -> Qeq v v' -> c_eq (c_of_Q u v) (c_of_Q u' v').
Proof.
  intros u u' v v' Hu Hv. unfold c_eq. split;
    apply real_eq_of_zero_diff; intro n.
  - rewrite (cRe_of_Q_pt u v n), (cRe_of_Q_pt u' v' n).
    rewrite Hu. ring.
  - rewrite (cIm_of_Q_pt u v n), (cIm_of_Q_pt u' v' n).
    rewrite Hv. ring.
Qed.

(* ==== Part 1. The pole carrier algebra (the self-cast cdiv face). ==== *)

(* The pole distance d = (a-1)^2 + b^2 of the rational point (a, b). *)
Definition z04_dd (a b : Q) : Q := (a - 1) * (a - 1) + b * b.

(* The main part 1/(s-1) at (a, b): the P05 inverse kernel of (a-1, b),  *)
(* embedded at Cx.                                                        *)
Definition z04_mp (a b : Q) : Cx :=
  c_of_Q (fst (GaC3_P05_cinv (a - 1) b)) (snd (GaC3_P05_cinv (a - 1) b)).

(* The derivative main part 1/(s-1)^2: the square of the pole carrier    *)
(* (the cdiv algebra reading (x, y)/(x^2+y^2) squared, with x = a-1,     *)
(* y = b: the pair ((x^2-y^2), -2xy) / (x^2+y^2)^2). *)
Definition z04_mp2 (a b : Q) : Cx := c_mult (z04_mp a b) (z04_mp a b).

(* The kernel identity: (s - 1) times its main part is 1 (the P05 kernel *)
(* consumption face at the pole-shifted point).                          *)
Lemma z04_mp_kernel : forall a b : Q,
  QltT 0 (z04_dd a b) ->
  c_eq (c_mult (c_of_Q (a - 1) b) (z04_mp a b)) (c_of_Q 1 0).
Proof.
  intros a b Hd. exact (GaC3_P05_cinv_cx (a - 1) b Hd).
Qed.

(* The square swap: (a*b)*(c*d) == (a*c)*(b*d) (Cx ring re-association). *)
Lemma z04_mult_square_swap : forall w x y z : Cx,
  c_eq (c_mult (c_mult w x) (c_mult y z)) (c_mult (c_mult w y) (c_mult x z)).
Proof.
  intros w x y z.
  apply (c_eq_trans (c_mult (c_mult w x) (c_mult y z))
                    (c_mult w (c_mult x (c_mult y z))) _).
  - apply c_eq_sym. apply c_mult_assoc.
  - apply (c_eq_trans (c_mult w (c_mult x (c_mult y z)))
                      (c_mult w (c_mult (c_mult x y) z)) _).
    + apply c_mult_congr; [ apply c_eq_refl | apply c_mult_assoc ].
    + apply (c_eq_trans (c_mult w (c_mult (c_mult x y) z))
                         (c_mult w (c_mult (c_mult y x) z)) _).
      * apply c_mult_congr; [ apply c_eq_refl | ].
        apply c_mult_congr; [ apply c_mult_comm | apply c_eq_refl ].
      * apply (c_eq_trans (c_mult w (c_mult (c_mult y x) z))
                           (c_mult w (c_mult y (c_mult x z))) _).
        -- apply c_mult_congr; [ apply c_eq_refl | ].
           apply c_eq_sym. apply c_mult_assoc.
        -- apply c_mult_assoc.
Qed.

(* The derivative kernel identity: (s - 1)^2 times its main part is 1    *)
(* (the kernel square face, through the square swap). *)
Lemma z04_mp2_sq : forall a b : Q,
  QltT 0 (z04_dd a b) ->
  c_eq (c_mult (c_mult (c_of_Q (a - 1) b) (c_of_Q (a - 1) b)) (z04_mp2 a b))
       (c_one).
Proof.
  intros a b Hd.
  apply (c_eq_trans
           (c_mult (c_mult (c_of_Q (a - 1) b) (c_of_Q (a - 1) b)) (z04_mp2 a b))
           (c_mult (c_mult (c_of_Q (a - 1) b) (z04_mp a b))
                   (c_mult (c_of_Q (a - 1) b) (z04_mp a b))) (c_one)).
  - exact (z04_mult_square_swap (c_of_Q (a - 1) b) (c_of_Q (a - 1) b)
                                (z04_mp a b) (z04_mp a b)).
  - apply (c_eq_trans
             (c_mult (c_mult (c_of_Q (a - 1) b) (z04_mp a b))
                     (c_mult (c_of_Q (a - 1) b) (z04_mp a b)))
             (c_mult c_one c_one) (c_one)).
    + apply c_mult_congr;
        [ apply z04_mp_kernel; exact Hd | apply z04_mp_kernel; exact Hd ].
    + apply c_mult_one.
Qed.

(* The pole shift: the point minus the unit reads at the coordinates. *)
Lemma z04_pole_shift : forall a b : Q,
  c_eq (c_plus (c_of_Q a b) (c_opp c_one)) (c_of_Q (a - 1) b).
Proof.
  intros a b. unfold c_eq. split; apply real_eq_of_zero_diff; intro n.
  - rewrite (cRe_plus_pt (c_of_Q a b) (c_opp c_one) n).
    rewrite (cRe_of_Q_pt a b n), (cRe_of_Q_pt (a - 1) b n).
    rewrite (cRe_opp_pt c_one n), (cRe_one_pt n).
    unfold Qminus. ring.
  - rewrite (cIm_plus_pt (c_of_Q a b) (c_opp c_one) n).
    rewrite (cIm_of_Q_pt a b n), (cIm_of_Q_pt (a - 1) b n).
    rewrite (cIm_opp_pt c_one n), (cIm_one_pt n).
    unfold Qminus. ring.
Qed.

(* The exact norm face |1/(s-1)|^2 = 1/d (kernel coordinate collapse).   *)
Lemma z04_mp_norm_sq : forall a b : Q,
  QltT 0 (z04_dd a b) ->
  real_eq (c_norm_sq (z04_mp a b)) (real_const (/ z04_dd a b)).
Proof.
  intros a b Hd.
  assert (Hdlt : (0 < ((a - 1) * (a - 1) + b * b))%Q)
    by (apply QltT_to_Qlt; exact Hd).
  assert (Hdne : ~ (((a - 1) * (a - 1) + b * b) == 0)).
  { intro Hh. exact (Qlt_not_eq _ _ Hdlt (Qeq_sym _ _ Hh)). }
  assert (Hinv1 : ((a - 1) * (a - 1) + b * b) *
                  / ((a - 1) * (a - 1) + b * b) == 1)
    by exact (Qmult_inv_r _ Hdne).
  assert (Hu : fst (GaC3_P05_cinv (a - 1) b) ==
                 ((a - 1) * / ((a - 1) * (a - 1) + b * b))%Q)
    by reflexivity.
  assert (Hv : snd (GaC3_P05_cinv (a - 1) b) ==
                 ((- (b * / ((a - 1) * (a - 1) + b * b))))%Q)
    by reflexivity.
  apply real_eq_of_zero_diff. intro n.
  cbn [z04_mp].
  rewrite (c_norm_sq_pt (c_of_Q (fst (GaC3_P05_cinv (a - 1) b))
                                (snd (GaC3_P05_cinv (a - 1) b))) n).
  rewrite (cRe_of_Q_pt (fst (GaC3_P05_cinv (a - 1) b))
                       (snd (GaC3_P05_cinv (a - 1) b)) n).
  rewrite (cIm_of_Q_pt (fst (GaC3_P05_cinv (a - 1) b))
                       (snd (GaC3_P05_cinv (a - 1) b)) n).
  rewrite Hu, Hv.
  unfold z04_dd.
  rewrite (real_const_proj (/ ((a - 1) * (a - 1) + b * b)) n).
  assert (Hreg : Qeq
           (((a - 1) * / ((a - 1) * (a - 1) + b * b)) *
            ((a - 1) * / ((a - 1) * (a - 1) + b * b)) +
            ((- (b * / ((a - 1) * (a - 1) + b * b))) *
             (- (b * / ((a - 1) * (a - 1) + b * b)))))
           (((a - 1) * (a - 1) + b * b) *
            (/ ((a - 1) * (a - 1) + b * b) * / ((a - 1) * (a - 1) + b * b))))
    by ring.
  rewrite Hreg.
  rewrite (Qmult_assoc ((a - 1) * (a - 1) + b * b)
                       (/ ((a - 1) * (a - 1) + b * b))
                       (/ ((a - 1) * (a - 1) + b * b))).
  rewrite Hinv1.
  unfold Qminus. ring.
Qed.

(* The shared split engine: z + y == (x + y) + (z - x) (the three-carrier *)
(* assembly face behind all three slot theorems).                         *)
Lemma z04_split_gen : forall x y z : Cx,
  c_eq (c_plus z y) (c_plus (c_plus x y) (c_plus z (c_opp x))).
Proof.
  intros x y z.
  apply (c_eq_trans (c_plus z y) (c_plus z (c_plus (c_opp x) (c_plus x y)))
                    (c_plus (c_plus x y) (c_plus z (c_opp x)))).
  - apply c_plus_congr; [ apply c_eq_refl | ].
    apply (c_eq_trans y (c_plus c_zero y) (c_plus (c_opp x) (c_plus x y))).
    + apply c_eq_sym. apply c_plus_zero.
    + apply (c_eq_trans (c_plus c_zero y) (c_plus (c_plus (c_opp x) x) y)
                         (c_plus (c_opp x) (c_plus x y))).
      * apply c_plus_congr; [ | apply c_eq_refl ].
        apply c_eq_sym.
        apply (c_eq_trans (c_plus (c_opp x) x) (c_plus x (c_opp x)) c_zero).
        -- apply c_plus_comm.
        -- apply c_plus_opp.
      * apply c_eq_sym. apply c_plus_assoc.
  - apply (c_eq_trans (c_plus z (c_plus (c_opp x) (c_plus x y)))
                       (c_plus z (c_plus (c_plus x y) (c_opp x))) _).
    + apply c_plus_congr; [ apply c_eq_refl | apply c_plus_comm ].
    + apply (c_eq_trans (c_plus z (c_plus (c_plus x y) (c_opp x)))
                         (c_plus (c_plus z (c_plus x y)) (c_opp x)) _).
      * apply c_plus_assoc.
      * apply (c_eq_trans (c_plus (c_plus z (c_plus x y)) (c_opp x))
                           (c_plus (c_plus (c_plus x y) z) (c_opp x)) _).
        -- apply c_plus_congr; [ apply c_plus_comm | apply c_eq_refl ].
        -- apply c_eq_sym. apply c_plus_assoc.
Qed.

(* The norm commutation: |z - w|^2 = |w - z|^2 (the pointwise square     *)
(* algebra bridging the slot direction to the dilute argument direction). *)
Lemma z04_norm_sq_comm : forall z w : Cx,
  real_eq (c_norm_sq (c_plus z (c_opp w))) (c_norm_sq (c_plus w (c_opp z))).
Proof.
  intros z w. apply real_eq_of_zero_diff. intro n.
  rewrite (c_norm_sq_pt (c_plus z (c_opp w)) n),
          (c_norm_sq_pt (c_plus w (c_opp z)) n).
  rewrite (cRe_plus_pt z (c_opp w) n), (cIm_plus_pt z (c_opp w) n).
  rewrite (cRe_plus_pt w (c_opp z) n), (cIm_plus_pt w (c_opp z) n).
  rewrite (cRe_opp_pt w n), (cIm_opp_pt w n).
  rewrite (cRe_opp_pt z n), (cIm_opp_pt z n).
  unfold Qminus. ring.
Qed.

(* The divisor-sum split of the truncated zeta face (the C2.04 identity  *)
(* re-export: the partial sum reads as the divisor sum minus the smooth  *)
(* remainder, the supply shape for the tail slots).                      *)
Theorem z04_dsum_split : forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
                                (N : nat) (s : Cx) (HN : (1 <= N)%nat),
  c_eq (c_zeta_part Hnpos N s)
       (c_plus (dsumCx (dpow Hnpos s) (hl_lcm_upto N)) (c_opp (R_N Hnpos N s))).
Proof.
  intros Hnpos N s HN.
  apply (c_eq_trans (c_zeta_part Hnpos N s)
                    (c_plus (c_zeta_part Hnpos N s)
                            (c_plus (R_N Hnpos N s) (c_opp (R_N Hnpos N s)))) _).
  - apply c_eq_sym.
    apply (c_eq_trans (c_plus (c_zeta_part Hnpos N s)
                              (c_plus (R_N Hnpos N s) (c_opp (R_N Hnpos N s))))
                      (c_plus (c_zeta_part Hnpos N s) c_zero)
                      (c_zeta_part Hnpos N s)).
    + apply c_plus_congr; [ apply c_eq_refl | apply c_plus_opp ].
    + apply c_plus_zero_r.
  - apply (c_eq_trans (c_plus (c_zeta_part Hnpos N s)
                              (c_plus (R_N Hnpos N s) (c_opp (R_N Hnpos N s))))
                      (c_plus (c_plus (c_zeta_part Hnpos N s) (R_N Hnpos N s))
                              (c_opp (R_N Hnpos N s))) _).
    + apply c_plus_assoc.
    + apply c_plus_congr.
      * apply c_eq_sym. exact (zeta_part_add_R_N_stem Hnpos N s HN).
      * apply c_eq_refl.
Qed.

(* The strip cap: on the right sub-strip a >= 3/2 (off the pole in the   *)
(* real direction) the main part squares to at most 4, explicitly:       *)
(* d >= (a-1)^2 >= 1/4 and |mp|^2 = 1/d <= 4.                            *)
Theorem z04_mp_norm_cap : forall a b : Q,
  QleT' (3 # 2) a -> QltT 0 (z04_dd a b) -> real_le (c_norm_sq (z04_mp a b)) (real_const 4).
Proof.
  intros a b Ha Hd.
  apply (real_le_trans (c_norm_sq (z04_mp a b)) (real_const (/ z04_dd a b)) (real_const 4)).
  - apply (RealSetoid.real_eq_le _ _). exact (z04_mp_norm_sq a b Hd).
  - apply z04_const_le.
    apply z04_inv_le.
    + exact Hd.
    + apply Qle_to_QleT'.
      assert (Hge : (3 # 2 <= a)%Q) by (apply QleT'_to_Qle; exact Ha).
      assert (Hax : ((1 # 2) <= a - 1)%Q).
      { unfold Qminus.
        apply (Qplus_le_compat (3 # 2) a (- 1) (- 1) Hge). apply Qle_refl. }
      assert (Hsq : ((1 # 4) <= (a - 1) * (a - 1))%Q).
      { change (Qle ((1 # 2) * (1 # 2)) ((a - 1) * (a - 1))).
        apply (z04_qsq_mono (1 # 2) (a - 1)).
        - assert (Hq12 : Qlt 0 (1 # 2)) by reflexivity.
          apply Qlt_le_weak. exact Hq12.
        - exact Hax. }
      assert (Hdd : ((1 # 4) <= z04_dd a b)%Q).
      { apply (Qle_trans (1 # 4) ((a - 1) * (a - 1)) (z04_dd a b)).
        - exact Hsq.
        - apply (Qle_trans ((a - 1) * (a - 1)) ((a - 1) * (a - 1) + 0) (z04_dd a b)).
          + apply qeq_le. ring.
          + unfold z04_dd. unfold Qminus.
            apply (Qplus_le_compat ((a - 1) * (a - 1)) ((a - 1) * (a - 1)) 0 (b * b)).
            * apply Qle_refl.
            * apply v03_qsq_nonneg. }
      assert (Hq4 : (1 == 4 * (1 # 4))%Q) by reflexivity.
      apply (Qle_trans 1 (4 * (1 # 4)) (4 * z04_dd a b)).
      * apply qeq_le. exact (Qeq_sym _ _ Hq4).
      * apply (Qle_trans (4 * (1 # 4)) ((1 # 4) * 4) (4 * z04_dd a b)).
        -- apply qeq_le. ring.
        -- apply (Qle_trans ((1 # 4) * 4) (z04_dd a b * 4) (4 * z04_dd a b)).
           ++ apply (Qmult_le_compat_r (1 # 4) (z04_dd a b) 4 Hdd).
              { assert (Hq04 : Qlt 0 4) by reflexivity. apply Qlt_le_weak. exact Hq04. }
           ++ apply qeq_le. ring.
Qed.

(* ==== Supply-face audit tail ==== *)

(* Named-item census of this stem: 3 Definitions (z04_dd, z04_mp, z04_mp2) *)
(* + 12 top-level Lemmas (z04_qsq_mono, z04_const_le, z04_inv_le,         *)
(* z04_fold_eps, z04_ofQ_congr, z04_mult_square_swap, z04_mp2_sq,         *)
(* z04_mp_kernel, z04_pole_shift, z04_mp_norm_sq, z04_norm_sq_comm,       *)
(* z04_split_gen) + 2 Theorems (z04_dsum_split, z04_mp_norm_cap).  Zero   *)
(* assumption commands, zero proof abandonment, zero classical principles, *)
(* zero computation tokens; the strip section lives in the _b slice.      *)
