(* ConstructiveWorld-Main - kernel margin and ML estimate faces of the C3 Cauchy-formula node. *)

(** * GaC3_P05_CauchyFormula_b: estimate faces of the Cauchy-formula node.

    Mission.  Node C3-P05 (segment C3), leaf slice: the estimate faces of
    the Cauchy-formula node, continuing the stem [GaC3_P05_CauchyFormula].
    (1) The kernel margin bound: the Cauchy kernel sampled on the P04
    rectangle boundary is componentwise bounded by the reciprocal of the
    interior margin d - the step-carrier analogue of the 1/|s-1|^2 face of
    ZZ deriv_zeta_bound (the bound of the singular kernel through the
    distance to the excluded point) [GaC3_P05_kernel_rect_bounds]. (2) The
    kernel ML face: the closed-loop sum of f-data against the kernel data
    is bounded by (2*M/d) * L1(boundary) for componentwise M-bounded
    f-data - the step-carrier analogue of the B/r consumption shape,
    consuming the P03 ML engine over the P04 four-edge boundary.  (3) The
    closed-form L1 length of the rectangle boundary for the
    explicit-constant consumption downstream.  The native derivative-bound
    statements (the k-th derivative bound k!*M/r^k and the holomorphic
    premise of the draft skeleton) remain deferred: the base carrier has
    no complex-differentiability machinery (the gap registered at P04),
    and the circle face consumes the uninstalled C1.4 residue (2pi
    periodicity).

    Dependencies.  [GaC3_P05_CauchyFormula] (stem: pair algebra, [veq],
    [cinv]), [GaC3_P03_MLEstimate] (ML engine, [val_bounded]),
    [GaC3_P04_CauchyRect] (rectangle boundary), [GaC3_P02_LineIntegralAlg]
    (path sums), [GaC3_P01_LineIntegralDef], [CxRealPairCore] (base
    module), [S01_BaseRing], [S02_CauchyComplete]; Stdlib [QArith],
    [List].

    References.  AFP PNT_with_Remainder Zeta_Zerofree [deriv_zeta_bound]
    :355-358 (the 1/|s-1|^2 term - the margin d here plays the role of the
    excluded-point distance) and PNT_Complex_Analysis_Lemmas
    [Borel_Caratheodory1/2/3] :375/:484/:497 (statement-shape anchors for
    the analytic-layer continuation); cards_C3 C3-P05.

    Constructivity.  Set-carried statements; the margin and bound premises
    are [QleT'] bearers (the S02 :99 canon); zero assumed constants, zero
    abandoned proofs, zero classical choice; all numerics stay in Q
    (decidable, exact); order reasoning by explicit QArith lemma chains
    (no solver on any goal).

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_P05_CauchyFormula_b.v] compiles cleanly (exit 0) from the work
    directory (sandbox pair), single compile lane under the cpu_guard v3
    wrapper. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import GaC3_P01_LineIntegralDef.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P03_MLEstimate.
Require Import GaC3_P04_CauchyRect.
Require Import GaC3_P05_CauchyFormula.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. Q-order micro-helpers.                                      *)
(* ===================================================================== *)

(* Native Qle transport: replace the left side through Qeq. *)
Lemma GaC3_P05_qle_wd : forall x y z : Q, x == y -> x <= z -> y <= z.
Proof.
  intros x y z Hxy Hxz. rewrite <- Hxy. exact Hxz.
Qed.

(* Native Qle transport: replace the right side through Qeq. *)
Lemma GaC3_P05_qle_wd_r : forall x y z : Q, y == z -> x <= y -> x <= z.
Proof.
  intros x y z Hyz Hxy. rewrite <- Hyz. exact Hxy.
Qed.

(* Subtracting the same amount from both sides preserves Qle. *)
Lemma GaC3_P05_qle_shift : forall x y e : Q, (x <= y)%Q -> (x - e <= y - e)%Q.
Proof.
  intros x y e H. exact (Qplus_le_compat _ _ _ _ H (Qle_refl (- e))).
Qed.

(* From x0 + d <= y: the distance d is available at y - x0. *)
Lemma GaC3_P05_shift_ge : forall x0 y d : Q,
  (x0 + d <= y)%Q -> (d <= y - x0)%Q.
Proof.
  intros x0 y d H.
  apply (GaC3_P05_qle_wd (x0 + d - x0) d (y - x0)).
  - ring.
  - exact (GaC3_P05_qle_shift _ _ x0 H).
Qed.

(* From x0 + d <= y: the point x0 sits at distance at least d below y. *)
Lemma GaC3_P05_shift_le_neg : forall x0 y d : Q,
  (x0 + d <= y)%Q -> (x0 - y <= - d)%Q.
Proof.
  intros x0 y d H.
  apply (GaC3_P05_qle_wd ((x0 + d) - y - d) (x0 - y) (- d)).
  - ring.
  - apply (GaC3_P05_qle_wd_r _ ((y - y) - d)).
    + ring.
    + exact (GaC3_P05_qle_shift _ _ d (GaC3_P05_qle_shift _ _ y H)).
Qed.

(* The absolute value of a nonpositive number is its negation. *)
Lemma GaC3_P05_abs_val_neg : forall x : Q, (x <= 0)%Q -> Qabs x == - x.
Proof.
  intros x Hx. apply (Qabs_case x (fun t => t == - x)).
  - intro Hpos.
    assert (E : (x == 0)%Q) by (apply Qle_antisym; [ exact Hx | exact Hpos ]).
    rewrite E. ring.
  - intro Hneg0. reflexivity.
Qed.

(* The square of the absolute value is the square. *)
Lemma GaC3_P05_abs_sq : forall x : Q, Qabs x * Qabs x == x * x.
Proof.
  intro x. apply (Qabs_case x (fun t => t * t == x * x)).
  - intro Hpos0. reflexivity.
  - intro Hneg0. ring.
Qed.

(* Squares are nonnegative. *)
Lemma GaC3_P05_sq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x. rewrite <- (GaC3_P05_abs_sq x).
  apply Qmult_le_0_compat; apply Qabs_nonneg.
Qed.

(* The reciprocal of a positive rational is nonnegative. *)
Lemma GaC3_P05_qinv_nonneg : forall d : Q, QltT 0 d -> 0 <= / d.
Proof.
  intros d Hd. destruct (Qlt_le_dec 0 (/ d)) as [Hpos | Hnon].
  - apply Qlt_le_weak. exact Hpos.
  - exfalso.
    assert (Hne0 : ~ (d == 0)).
    { intro Hzz. apply (Qlt_not_eq 0 d).
      - apply QltT_to_Qlt. exact Hd.
      - apply Qeq_sym. exact Hzz. }
    assert (Hle : ((/ d) * d <= 0 * d)%Q).
    { apply Qmult_le_compat_r.
      - exact Hnon.
      - apply (Qlt_le_weak 0 d). apply QltT_to_Qlt. exact Hd. }
    rewrite (Qmult_comm (/ d) d) in Hle.
    rewrite (Qmult_inv_r d Hne0) in Hle.
    assert (Hbad : (1 <= 0)%Q)
      by (apply (GaC3_P05_qle_wd_r _ (0 * d)); [ ring | exact Hle ]).
    apply (Qlt_irrefl 0). apply (Qlt_le_trans 0 1 0).
    + apply QltT_to_Qlt. exact qltT_0_1.
    + exact Hbad.
Qed.

(* The division-order step: from x*d <= D with d, D > 0 conclude          *)
(* x/D <= 1/d - the estimate engine behind the kernel bound. *)
Lemma GaC3_P05_qdiv_le : forall x D d : Q,
  QltT 0 d -> QltT 0 D -> (x * d <= D)%Q -> (x * / D <= / d)%Q.
Proof.
  intros x D d Hd HD H.
  assert (Hdd : 0 <= / d) by (apply GaC3_P05_qinv_nonneg; exact Hd).
  assert (HDD : 0 <= / D) by (apply GaC3_P05_qinv_nonneg; exact HD).
  assert (Hne0d : ~ (d == 0)).
  { intro Hzz. apply (Qlt_not_eq 0 d).
    - apply QltT_to_Qlt. exact Hd.
    - apply Qeq_sym. exact Hzz. }
  assert (Hne0D : ~ (D == 0)).
  { intro Hzz. apply (Qlt_not_eq 0 D).
    - apply QltT_to_Qlt. exact HD.
    - apply Qeq_sym. exact Hzz. }
  assert (E2 : (x * d * / d == x)%Q).
  { rewrite <- (Qmult_assoc x d (/ d)), (Qmult_inv_r d Hne0d), Qmult_1_r.
    apply Qeq_refl. }
  assert (S1 : (x * d * / d <= D * / d)%Q)
    by (apply Qmult_le_compat_r; [ exact H | exact Hdd ]).
  assert (Hxd : (x <= D * / d)%Q).
  { rewrite (Qeq_sym _ _ E2). exact S1. }
  assert (S2 : (x * / D <= D * / d * / D)%Q)
    by (apply Qmult_le_compat_r; [ exact Hxd | exact HDD ]).
  assert (E3 : (D * / d * / D == / d)%Q).
  { rewrite <- (Qmult_assoc D (/ d) (/ D)), (Qmult_comm (/ d) (/ D)),
            (Qmult_assoc D (/ D) (/ d)), (Qmult_inv_r D Hne0D), Qmult_1_l.
    apply Qeq_refl. }
  rewrite <- E3. exact S2.
Qed.

(* ===================================================================== *)
(* Section 2. The kernel bound through one coordinate margin.             *)
(* ===================================================================== *)

(* Core bound, margin on the second coordinate: with d <= |b| both        *)
(* components of the kernel inverse are bounded by 1/d.  First component: *)
(* |a|*d <= a^2 or |a|*d < d^2 <= b^2 (two cases); second component:      *)
(* |b|*d <= b^2; both then divided through by the positive norm squared.  *)
Lemma GaC3_P05_cinv_abs_core : forall a b d : Q,
  QltT 0 d -> QleT' d (Qabs b) ->
  Qabs (fst (GaC3_P05_cinv a b)) <= / d /\ Qabs (snd (GaC3_P05_cinv a b)) <= / d.
Proof.
  intros a b d Hd Hb.
  assert (Hd0 : (0 <= d)%Q)
    by (apply (Qlt_le_weak 0 d); apply QltT_to_Qlt; exact Hd).
  assert (Hdb : d <= Qabs b) by (apply QleT'_to_Qle; exact Hb).
  assert (Hsq : (d * d <= b * b)%Q).
  { apply (Qle_trans _ (Qabs b * Qabs b)).
    - apply (Qle_trans _ (Qabs b * d)).
      + apply (Qmult_le_compat_r d (Qabs b) d Hdb Hd0).
      + rewrite (Qmult_comm (Qabs b) d).
        apply (Qmult_le_compat_r d (Qabs b) (Qabs b) Hdb
                 (Qabs_nonneg b)).
    - apply qeq_le. apply GaC3_P05_abs_sq. }
  assert (HbD : (b * b <= a * a + b * b)%Q).
  { apply (Qle_trans _ (b * b + 0)).
    - apply qeq_le. ring.
    - rewrite (Qplus_comm (a * a) (b * b)).
      apply Qplus_le_compat; [ apply Qle_refl | apply GaC3_P05_sq_nonneg ]. }
  assert (HDpos : QltT 0 (a * a + b * b)).
  { apply Qlt_to_QltT. apply (Qlt_le_trans 0 (d * d) (a * a + b * b)).
    - apply QltT_to_Qlt. exact (qmult_ltT_0_compat d d Hd Hd).
    - apply (Qle_trans _ (b * b)); [ exact Hsq | exact HbD ]. }
  assert (Habs1 : Qabs (a * / (a * a + b * b)) == Qabs a * / (a * a + b * b)).
  { rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ (a * a + b * b)) (GaC3_P05_qinv_nonneg _ HDpos)).
    apply Qeq_refl. }
  assert (H1 : Qabs a * d <= a * a + b * b).
  { destruct (Qlt_le_dec (Qabs a) d) as [Hlt | Hge].
    - apply (Qlt_le_weak _ _). apply (Qlt_le_trans _ (d * d)).
      + apply (Qmult_lt_compat_r (Qabs a) d d).
        * apply QltT_to_Qlt. exact Hd.
        * exact Hlt.
      + apply (Qle_trans _ (b * b)); [ exact Hsq | exact HbD ].
    - rewrite <- (GaC3_P05_abs_sq a).
      rewrite (Qmult_comm (Qabs a) d).
      apply (Qle_trans _ (Qabs a * Qabs a)).
      + apply (Qmult_le_compat_r d (Qabs a) (Qabs a) Hge (Qabs_nonneg a)).
      + apply (Qle_trans _ (Qabs a * Qabs a + 0)).
        * apply qeq_le. ring.
        * apply Qplus_le_compat; [ apply Qle_refl | apply GaC3_P05_sq_nonneg ]. }
  assert (Hcomp1 : Qabs (fst (GaC3_P05_cinv a b)) <= / d).
  { cbn [GaC3_P05_cinv fst snd]. rewrite Habs1.
    exact (GaC3_P05_qdiv_le (Qabs a) _ _ Hd HDpos H1). }
  assert (Habs2 : Qabs (- (b * / (a * a + b * b)))
                  == Qabs b * / (a * a + b * b)).
  { rewrite Qabs_opp. rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ (a * a + b * b)) (GaC3_P05_qinv_nonneg _ HDpos)).
    apply Qeq_refl. }
  assert (H2 : Qabs b * d <= a * a + b * b).
  { apply (Qle_trans _ (b * b)).
    - rewrite <- (GaC3_P05_abs_sq b).
      rewrite (Qmult_comm (Qabs b) d).
      apply (Qmult_le_compat_r d (Qabs b) (Qabs b) Hdb
               (Qabs_nonneg b)).
    - exact HbD. }
  assert (Hcomp2 : Qabs (snd (GaC3_P05_cinv a b)) <= / d).
  { cbn [GaC3_P05_cinv fst snd]. rewrite Habs2.
    exact (GaC3_P05_qdiv_le (Qabs b) _ _ Hd HDpos H2). }
  split; assumption.
Qed.

(* Core bound, margin on the first coordinate: the swapped instantiation  *)
(* of the second-coordinate core, with the componentwise sum reordered.   *)
Lemma GaC3_P05_cinv_abs_core_x : forall a b d : Q,
  QltT 0 d -> QleT' d (Qabs a) ->
  Qabs (fst (GaC3_P05_cinv a b)) <= / d /\ Qabs (snd (GaC3_P05_cinv a b)) <= / d.
Proof.
  intros a b d Hd Ha.
  destruct (GaC3_P05_cinv_abs_core b a d Hd Ha) as [H1 H2].
  cbn [GaC3_P05_cinv fst snd] in H1. cbn [GaC3_P05_cinv fst snd] in H2.
  cbn [GaC3_P05_cinv fst snd].
  assert (Ecomm : (b * b + a * a == a * a + b * b)%Q) by ring.
  split.
  - rewrite Qabs_opp in H2. rewrite Ecomm in H2. exact H2.
  - rewrite Qabs_opp. rewrite Ecomm in H1. exact H1.
Qed.

(* ===================================================================== *)
(* Section 3. The interior margin and the kernel data on the rectangle.   *)
(* ===================================================================== *)

(* The interior-margin bearer: the point z0 sits at Q-distance at least d *)
(* from all four sides of the rectangle [c, b] x [-T, T] (d > 0 carried   *)
(* separately as QltT 0 d). *)
Definition GaC3_P05_margin (c b T d : Q) (z0 : Q * Q) : Set :=
  And (QleT' (c + d) (fst z0))
      (And (QleT' (fst z0 + d) b)
           (And (QleT' (- T + d) (snd z0)) (QleT' (snd z0 + d) T))).

(* Bridge (elim): the margin bearer into the native Qle conjunction. *)
Lemma GaC3_P05_margin_elim : forall (c b T d : Q) (z0 : Q * Q),
  GaC3_P05_margin c b T d z0 ->
  (c + d <= fst z0)%Q /\ (fst z0 + d <= b)%Q
  /\ (- T + d <= snd z0)%Q /\ (snd z0 + d <= T)%Q.
Proof.
  intros c b T d z0 H. destruct H as [H1 [H2 [H3 H4]]].
  split; [ | split; [ | split ] ].
  - exact (QleT'_to_Qle _ _ H1).
  - exact (QleT'_to_Qle _ _ H2).
  - exact (QleT'_to_Qle _ _ H3).
  - exact (QleT'_to_Qle _ _ H4).
Qed.

(* A lower margin puts the absolute value above d from above. *)
Lemma GaC3_P05_abs_ge_pos : forall x d : Q,
  QltT 0 d -> (d <= x)%Q -> QleT' d (Qabs x).
Proof.
  intros x d Hd Hdx.
  assert (Hx0 : (0 <= x)%Q).
  { apply (Qle_trans _ d).
    - apply (Qlt_le_weak 0 d). apply QltT_to_Qlt. exact Hd.
    - exact Hdx. }
  apply Qle_to_QleT'. rewrite (Qabs_pos x Hx0). exact Hdx.
Qed.

(* An upper margin below -d puts the absolute value above d from below. *)
Lemma GaC3_P05_abs_ge_neg : forall x d : Q,
  QltT 0 d -> (x <= - d)%Q -> QleT' d (Qabs x).
Proof.
  intros x d Hd Hx.
  assert (Hd0 : (0 <= d)%Q)
    by (apply (Qlt_le_weak 0 d); apply QltT_to_Qlt; exact Hd).
  assert (Hx0 : (x <= 0)%Q).
  { apply (Qle_trans x (- d) 0); [ exact Hx | ].
    apply (GaC3_P05_qle_wd_r (- d) (- 0) 0).
    - ring.
    - apply Qopp_le_compat. exact Hd0. }
  apply Qle_to_QleT'. rewrite (GaC3_P05_abs_val_neg x Hx0).
  apply (Qle_trans d (- - d) (- x)).
  - apply qeq_le. ring.
  - apply Qopp_le_compat. exact Hx.
Qed.

(* The Cauchy kernel value at a sample point w relative to z0. *)
Definition GaC3_P05_kernel_val (z0 w : Q * Q) : Q * Q :=
  GaC3_P05_cinv (fst (GaC3_P05_vsub w z0)) (snd (GaC3_P05_vsub w z0)).

(* The kernel data on a path: the inverse sampled at each segment's start  *)
(* vertex - the discrete quadrature of the Cauchy kernel on the path. *)
Definition GaC3_P05_kernel_data (z0 : Q * Q) (ps : GaC3_P02_cpath)
  : list (Q * Q) :=
  map (fun s => GaC3_P05_kernel_val z0 (fst s)) ps.

(* The membership case analysis over the kernel data (Prop-to-Prop). *)
Lemma GaC3_P05_in_kernel_data_cases : forall (z0 : Q * Q)
  (ps : GaC3_P02_cpath) (w : Q * Q),
  In w (GaC3_P05_kernel_data z0 ps) ->
  exists s, In s ps /\
    fst w == fst (GaC3_P05_kernel_val z0 (fst s)) /\
    snd w == snd (GaC3_P05_kernel_val z0 (fst s)).
Proof.
  intros z0 ps w Hw. unfold GaC3_P05_kernel_data in Hw.
  apply in_map_iff in Hw. destruct Hw as [s [Es Hs]].
  exists s. split; [ exact Hs | ]. rewrite <- Es.
  split; apply Qeq_refl.
Qed.

(* The kernel margin bound on the P04 rectangle: every boundary start     *)
(* vertex carries a coordinate at Q-distance >= d from the interior point *)
(* z0, so every kernel value is componentwise bounded by 1/d - the        *)
(* step-carrier analogue of the 1/|s-1|^2 face of ZZ deriv_zeta_bound. *)
Theorem GaC3_P05_kernel_rect_bounds : forall (c b T d : Q) (z0 : Q * Q),
  QltT 0 d -> GaC3_P05_margin c b T d z0 ->
  forall s : GaC3_P02_pseg,
  In s (GaC3_P04_rect_boundary c b T) ->
  Qabs (fst (GaC3_P05_kernel_val z0 (fst s))) <= / d /\
  Qabs (snd (GaC3_P05_kernel_val z0 (fst s))) <= / d.
Proof.
  intros c b T d z0 Hd Hm s Hs.
  destruct (GaC3_P05_margin_elim c b T d z0 Hm) as [Hm1 [Hm2 [Hm3 Hm4]]].
  destruct Hs as [E | Hs].
  - (* left edge, start (c, -T): the x-coordinate sits d below fst z0 *)
    subst s.
    cbn [GaC3_P05_kernel_val GaC3_P05_vsub fst snd].
    apply GaC3_P05_cinv_abs_core_x; [ exact Hd | ].
    apply GaC3_P05_abs_ge_neg; [ exact Hd | ].
    exact (GaC3_P05_shift_le_neg c (fst z0) d Hm1).
  - destruct Hs as [E | Hs].
    + (* bottom-right run, start (b, -T): x-coordinate d above fst z0 *)
      subst s.
      cbn [GaC3_P05_kernel_val GaC3_P05_vsub fst snd].
      apply GaC3_P05_cinv_abs_core_x; [ exact Hd | ].
      apply GaC3_P05_abs_ge_pos; [ exact Hd | ].
      exact (GaC3_P05_shift_ge (fst z0) b d Hm2).
    + destruct Hs as [E | Hs].
      * (* top edge, start (b, T): y-coordinate d above snd z0 *)
        subst s.
        cbn [GaC3_P05_kernel_val GaC3_P05_vsub fst snd].
        apply GaC3_P05_cinv_abs_core; [ exact Hd | ].
        apply GaC3_P05_abs_ge_pos; [ exact Hd | ].
        exact (GaC3_P05_shift_ge (snd z0) T d Hm4).
      * destruct Hs as [E | Hs].
        -- (* left return, start (c, T): y-coordinate d above snd z0 *)
           subst s.
           cbn [GaC3_P05_kernel_val GaC3_P05_vsub fst snd].
           apply GaC3_P05_cinv_abs_core; [ exact Hd | ].
           apply GaC3_P05_abs_ge_pos; [ exact Hd | ].
           exact (GaC3_P05_shift_ge (snd z0) T d Hm4).
        -- inversion Hs.
Qed.

