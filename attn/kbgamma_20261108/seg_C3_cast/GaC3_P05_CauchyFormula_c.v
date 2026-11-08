(* ConstructiveWorld-Main - kernel ML estimate face of the C3 Cauchy-formula node. *)

(** * GaC3_P05_CauchyFormula_c: the kernel ML face of the Cauchy-formula node.

    Mission.  Node C3-P05 (segment C3), leaf slice: the kernel ML face of
    the Cauchy-formula node, continuing the stem [GaC3_P05_CauchyFormula]
    and the margin leaf [GaC3_P05_CauchyFormula_b].  The closed-loop sum
    of componentwise M-bounded f-data against the Cauchy kernel data on
    the P04 rectangle boundary is bounded by (2*M/d) * L1(boundary) in
    both components [GaC3_P05_cauchy_kernel_ml] - the step-carrier
    analogue of the B/r consumption shape of ZZ deriv_zeta_bound :355-358,
    with the honest discrete constants (the factor 2 from the
    componentwise product estimate, L1 for the perimeter, and the interior
    margin d for the excluded point).  The membership supply for the P03
    ML engine is built by a computational lookup over the product zip: the
    In premises are only constructed and applied, never eliminated into
    Set.  The native derivative-bound statements remain deferred: the base
    carrier has no complex-differentiability machinery (the gap registered
    at P04), and the circle face consumes the uninstalled C1.4 residue
    (2pi periodicity).

    Dependencies.  [GaC3_P05_CauchyFormula_b] (margin face, kernel bound,
    [qinv]), [GaC3_P05_CauchyFormula] (stem: pair algebra, [qmul]),
    [GaC3_P03_MLEstimate] (ML engine), [GaC3_P04_CauchyRect] (rectangle
    boundary), [GaC3_P02_LineIntegralAlg] (path sums),
    [GaC3_P01_LineIntegralDef], [CxRealPairCore] (base module),
    [S01_BaseRing], [S02_CauchyComplete]; Stdlib [QArith], [List].

    References.  AFP PNT_with_Remainder Zeta_Zerofree [deriv_zeta_bound]
    :355-358 (the B/r term; the discrete constants 2*M/d and L1 are the
    honest step-carrier faces of B/r) and PNT_Complex_Analysis_Lemmas
    [Borel_Caratheodory1/2/3] :375/:484/:497 (statement-shape anchors for
    the analytic-layer continuation); cards_C3 C3-P05.

    Constructivity.  Set-carried statements; the bound premises are
    [QleT'] bearers (the S02 :99 canon) and the membership supply is a
    computational lookup with boolean pair equality; zero assumed
    constants, zero abandoned proofs, zero classical choice; all numerics
    stay in Q (decidable, exact); order reasoning by explicit QArith lemma
    chains (no solver on any goal).

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_P05_CauchyFormula_c.v] compiles cleanly (exit 0) from the work
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
Require Import GaC3_P05_CauchyFormula_b.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. The P03 bearer from absolute-value bounds; the product      *)
(* estimate.                                                              *)
(* ===================================================================== *)

(* The P03 val_bounded bearer from absolute-value bounds (the bridge). *)
Lemma GaC3_P05_val_bounded_abs : forall (v : Q * Q) (B : Q),
  Qabs (fst v) <= B -> Qabs (snd v) <= B -> GaC3_P03_val_bounded v B.
Proof.
  intros [vr vi] B Hr Hi. split; [ | split; [ | split ] ].
  - apply Qle_to_QleT'. exact (proj1 (proj1 (Qabs_Qle_condition vr B) Hr)).
  - apply Qle_to_QleT'. exact (proj2 (proj1 (Qabs_Qle_condition vr B) Hr)).
  - apply Qle_to_QleT'. exact (proj1 (proj1 (Qabs_Qle_condition vi B) Hi)).
  - apply Qle_to_QleT'. exact (proj2 (proj1 (Qabs_Qle_condition vi B) Hi)).
Qed.

(* The componentwise product of M-bounded and K-bounded data is           *)
(* (2*M*K)-bounded - the triangle-inequality estimate on both components, *)
(* in the absolute-value face. *)
Lemma GaC3_P05_qmul_abs_bounded : forall (f k : Q * Q) (M K : Q),
  QleT' 0 M -> QleT' 0 K ->
  GaC3_P03_val_bounded f M -> GaC3_P03_val_bounded k K ->
  Qabs (fst (GaC3_P05_qmul f k)) <= 2 * M * K /\
  Qabs (snd (GaC3_P05_qmul f k)) <= 2 * M * K.
Proof.
  intros f k M K HM HK Hf Hk.
  pose proof (GaC3_P03_val_bounded_Qle f M Hf) as Hfq.
  pose proof (GaC3_P03_val_bounded_Qle k K Hk) as Hkq.
  destruct Hfq as [Hf1 [Hf2 [Hf3 Hf4]]].
  destruct Hkq as [Hk1 [Hk2 [Hk3 Hk4]]].
  assert (HMr : Qabs (fst f) <= M).
  { apply (proj2 (Qabs_Qle_condition (fst f) M)).
    split; [ exact Hf1 | exact Hf2 ]. }
  assert (HMi : Qabs (snd f) <= M).
  { apply (proj2 (Qabs_Qle_condition (snd f) M)).
    split; [ exact Hf3 | exact Hf4 ]. }
  assert (HKr : Qabs (fst k) <= K).
  { apply (proj2 (Qabs_Qle_condition (fst k) K)).
    split; [ exact Hk1 | exact Hk2 ]. }
  assert (HKi : Qabs (snd k) <= K).
  { apply (proj2 (Qabs_Qle_condition (snd k) K)).
    split; [ exact Hk3 | exact Hk4 ]. }
  assert (HpM : 0 <= M) by (apply QleT'_to_Qle; exact HM).
  assert (HpK : 0 <= K) by (apply QleT'_to_Qle; exact HK).
  split.
  - cbn [GaC3_P05_qmul fst snd]. unfold Qminus.
    apply (Qle_trans _ (Qabs (fst f * fst k) + Qabs (- (snd f * snd k)))).
    + apply Qabs_triangle.
    + rewrite (Qabs_Qmult (fst f) (fst k)), Qabs_opp,
              (Qabs_Qmult (snd f) (snd k)).
      apply (Qle_trans _ (M * K + M * K)).
      * apply Qplus_le_compat.
        -- apply (Qle_trans _ (Qabs (fst f) * K)).
           ++ rewrite (Qmult_comm (Qabs (fst f)) (Qabs (fst k))),
                      (Qmult_comm (Qabs (fst f)) K).
              apply (Qmult_le_compat_r (Qabs (fst k)) K (Qabs (fst f)) HKr
                       (Qabs_nonneg (fst f))).
           ++ apply (Qmult_le_compat_r (Qabs (fst f)) M K HMr HpK).
        -- apply (Qle_trans _ (Qabs (snd f) * K)).
           ++ rewrite (Qmult_comm (Qabs (snd f)) (Qabs (snd k))),
                      (Qmult_comm (Qabs (snd f)) K).
              apply (Qmult_le_compat_r (Qabs (snd k)) K (Qabs (snd f)) HKi
                       (Qabs_nonneg (snd f))).
           ++ apply (Qmult_le_compat_r (Qabs (snd f)) M K HMi HpK).
      * apply qeq_le. ring.
  - cbn [GaC3_P05_qmul fst snd]. unfold Qminus.
    apply (Qle_trans _ (Qabs (fst f * snd k) + Qabs (snd f * fst k))).
    + apply Qabs_triangle.
    + rewrite (Qabs_Qmult (snd f) (fst k)), (Qabs_Qmult (fst f) (snd k)).
      apply (Qle_trans _ (M * K + M * K)).
      * apply Qplus_le_compat.
        -- apply (Qle_trans _ (Qabs (fst f) * K)).
           ++ rewrite (Qmult_comm (Qabs (fst f)) (Qabs (snd k))),
                      (Qmult_comm (Qabs (fst f)) K).
              apply (Qmult_le_compat_r (Qabs (snd k)) K (Qabs (fst f)) HKi
                       (Qabs_nonneg (fst f))).
           ++ apply (Qmult_le_compat_r (Qabs (fst f)) M K HMr HpK).
        -- apply (Qle_trans _ (Qabs (snd f) * K)).
           ++ rewrite (Qmult_comm (Qabs (snd f)) (Qabs (fst k))),
                      (Qmult_comm (Qabs (snd f)) K).
              apply (Qmult_le_compat_r (Qabs (fst k)) K (Qabs (snd f)) HKr
                       (Qabs_nonneg (snd f))).
           ++ apply (Qmult_le_compat_r (Qabs (snd f)) M K HMi HpK).
      * apply qeq_le. ring.
Qed.

(* ===================================================================== *)
(* Section 2. The product zip and the computational lookup.               *)
(* ===================================================================== *)

(* The positionwise product zip of the f-data with the kernel data - the  *)
(* discrete integrand of the Cauchy formula face. *)
Fixpoint GaC3_P05_vzip (fs ks : list (Q * Q)) : list (Q * Q) :=
  match fs, ks with
  | f :: fs', k :: ks' => GaC3_P05_qmul f k :: GaC3_P05_vzip fs' ks'
  | _, _ => nil
  end.

(* Boolean equality on Q pairs (both components). *)
Definition GaC3_P05_pair_eqb (u v : Q * Q) : bool :=
  andb (Qeq_bool (fst u) (fst v)) (Qeq_bool (snd u) (snd v)).

Lemma GaC3_P05_pair_eqb_refl_true : forall u : Q * Q,
  GaC3_P05_pair_eqb u u = true.
Proof.
  intro u. unfold GaC3_P05_pair_eqb.
  assert (Hq : forall x : Q, Qeq_bool x x = true).
  { intro x. unfold Qeq_bool. apply Z.eqb_refl. }
  rewrite (Hq (fst u)), (Hq (snd u)). reflexivity.
Qed.

(* The boolean check reflects into the Set-carried pair equality. *)
Lemma GaC3_P05_pair_eqb_true : forall u v : Q * Q,
  GaC3_P05_pair_eqb u v = true -> GaC3_P05_veq u v.
Proof.
  intros [a b] [c d] H. unfold GaC3_P05_pair_eqb in H.
  cbn [fst snd] in H.
  destruct (Qeq_bool a c) eqn:E1; destruct (Qeq_bool b d) eqn:E2;
    try discriminate H.
  apply GaC3_P05_veq_intro; apply Qeq_bool_eq; assumption.
Qed.

(* The computational lookup over the product zip against a segment-sampled *)
(* second list: the position of v in the zip is decided by data, so the    *)
(* In premises of the ML engine are supplied without ever eliminating a    *)
(* Prop proof into Set. *)
Fixpoint GaC3_P05_fk_lookup (fvs : list (Q * Q))
  (g : GaC3_P02_pseg -> Q * Q) (ps : GaC3_P02_cpath) (v : Q * Q)
  : option ((Q * Q) * (Q * Q)) :=
  match fvs with
  | nil => None
  | f :: fs' =>
      match ps with
      | nil => None
      | s :: ps' =>
          if GaC3_P05_pair_eqb v (GaC3_P05_qmul f (g s))
          then Some (f, g s) else GaC3_P05_fk_lookup fs' g ps' v
      end
  end.

(* Lookup spec, equality face: a hit identifies v with the product at the *)
(* found position (Set bearer). *)
Lemma GaC3_P05_fk_lookup_spec : forall (fvs : list (Q * Q))
  (g : GaC3_P02_pseg -> Q * Q) (ps : GaC3_P02_cpath) (v f' w' : Q * Q),
  GaC3_P05_fk_lookup fvs g ps v = Some (f', w') ->
  GaC3_P05_veq v (GaC3_P05_qmul f' w').
Proof.
  intros fvs g. induction fvs as [| f fs' IH]; intros ps v f' w' E.
  - discriminate E.
  - destruct ps as [| s ps'].
    + discriminate E.
    + cbn [GaC3_P05_fk_lookup] in E.
      destruct (GaC3_P05_pair_eqb v (GaC3_P05_qmul f (g s))) eqn:Eb.
      * inversion E; subst. exact (GaC3_P05_pair_eqb_true _ _ Eb).
      * exact (IH ps' v f' w' E).
Qed.

(* Lookup spec, first-coordinate face: the found f datum is a member. *)
Lemma GaC3_P05_fk_lookup_fst : forall (fvs : list (Q * Q))
  (g : GaC3_P02_pseg -> Q * Q) (ps : GaC3_P02_cpath) (v f' w' : Q * Q),
  GaC3_P05_fk_lookup fvs g ps v = Some (f', w') -> In f' fvs.
Proof.
  intros fvs g. induction fvs as [| f fs' IH]; intros ps v f' w' E.
  - discriminate E.
  - destruct ps as [| s ps'].
    + discriminate E.
    + cbn [GaC3_P05_fk_lookup] in E.
      destruct (GaC3_P05_pair_eqb v (GaC3_P05_qmul f (g s))) eqn:Eb.
      * inversion E; subst. apply in_eq.
      * apply in_cons. exact (IH ps' v f' w' E).
Qed.

(* Lookup spec, miss face: a None result excludes membership (Prop). *)
Lemma GaC3_P05_fk_lookup_none : forall (fvs : list (Q * Q))
  (g : GaC3_P02_pseg -> Q * Q) (ps : GaC3_P02_cpath) (v : Q * Q),
  GaC3_P05_fk_lookup fvs g ps v = None ->
  ~ In v (GaC3_P05_vzip fvs (map g ps)).
Proof.
  intros fvs g. induction fvs as [| f fs' IH]; intros ps v E Hin.
  - cbn [GaC3_P05_vzip map In] in Hin. destruct Hin.
  - destruct ps as [| s ps'].
    + cbn [GaC3_P05_vzip map In] in Hin. destruct Hin.
    + cbn [GaC3_P05_fk_lookup] in E.
      cbn [GaC3_P05_vzip map In] in Hin.
      destruct Hin as [He | Hc2].
      * subst v.
        assert (Hb := GaC3_P05_pair_eqb_refl_true (GaC3_P05_qmul f (g s))).
        rewrite Hb in E. discriminate E.
      * destruct (GaC3_P05_pair_eqb v (GaC3_P05_qmul f (g s))) eqn:Eb.
        -- discriminate E.
        -- exact (IH ps' v E Hc2).
Qed.

(* Lookup spec, second-coordinate face: the found kernel datum carries    *)
(* the per-segment bound of the sampled list (In only constructed and     *)
(* applied). *)
Lemma GaC3_P05_fk_lookup_bounded : forall (ps : GaC3_P02_cpath)
  (g : GaC3_P02_pseg -> Q * Q) (fvs : list (Q * Q)) (K : Q) (v f' w' : Q * Q),
  (forall s, In s ps -> GaC3_P03_val_bounded (g s) K) ->
  GaC3_P05_fk_lookup fvs g ps v = Some (f', w') ->
  GaC3_P03_val_bounded w' K.
Proof.
  intros ps g fvs. revert ps. induction fvs as [| f fs' IH];
    intros ps K v f' w' Hseg E.
  - discriminate E.
  - destruct ps as [| s ps'].
    + discriminate E.
    + cbn [GaC3_P05_fk_lookup] in E.
      destruct (GaC3_P05_pair_eqb v (GaC3_P05_qmul f (g s))) eqn:Eb.
      * inversion E; subst. exact (Hseg s (in_eq s ps')).
      * exact (IH ps' K v f' w'
                 (fun s' Hs' => Hseg s' (in_cons s s' ps' Hs')) E).
Qed.

(* ===================================================================== *)
(* Section 3. The kernel ML face on the P04 rectangle.                    *)
(* ===================================================================== *)

(* The In-premise supplier for the ML engine over the product zip: the    *)
(* f-data premise is passed through by application; the kernel-data bound *)
(* comes from the margin face of the _b leaf through the per-segment      *)
(* premise of the lookup; the miss branch is killed by False elimination. *)
Lemma GaC3_P05_fk_bounded : forall (fvs : list (Q * Q)) (c b T d : Q)
  (z0 : Q * Q) (M : Q),
  QltT 0 d -> GaC3_P05_margin c b T d z0 -> QleT' 0 M ->
  (forall v, In v fvs -> GaC3_P03_val_bounded v M) ->
  forall v, In v (GaC3_P05_vzip fvs
                   (GaC3_P05_kernel_data z0 (GaC3_P04_rect_boundary c b T)))
    -> GaC3_P03_val_bounded v (2 * M * / d).
Proof.
  intros fvs c b T d z0 M Hd Hm HM Hf v Hv.
  unfold GaC3_P05_kernel_data in Hv.
  destruct (GaC3_P05_fk_lookup fvs
              (fun s => GaC3_P05_kernel_val z0 (fst s))
              (GaC3_P04_rect_boundary c b T) v) as [[f' w'] |] eqn:E.
  - assert (Hseg : forall s, In s (GaC3_P04_rect_boundary c b T) ->
              GaC3_P03_val_bounded (GaC3_P05_kernel_val z0 (fst s)) (/ d)).
    { intros s Hs.
      destruct (GaC3_P05_kernel_rect_bounds c b T d z0 Hd Hm s Hs) as [K1 K2].
      apply GaC3_P05_val_bounded_abs; [ exact K1 | exact K2 ]. }
    destruct (GaC3_P05_veq_elim _ _
                (GaC3_P05_fk_lookup_spec fvs
                   (fun s => GaC3_P05_kernel_val z0 (fst s))
                   (GaC3_P04_rect_boundary c b T) v f' w' E)) as [Hs1 Hs2].
    apply GaC3_P05_val_bounded_abs.
    + rewrite Hs1.
      exact (proj1 (GaC3_P05_qmul_abs_bounded f' w' M (/ d) HM
                      (Qle_to_QleT' 0 (/ d) (GaC3_P05_qinv_nonneg d Hd))
                      (Hf f' (GaC3_P05_fk_lookup_fst fvs
                                (fun s => GaC3_P05_kernel_val z0 (fst s))
                                (GaC3_P04_rect_boundary c b T) v f' w' E))
                      (GaC3_P05_fk_lookup_bounded
                         (GaC3_P04_rect_boundary c b T)
                         (fun s => GaC3_P05_kernel_val z0 (fst s)) fvs (/ d)
                         v f' w' Hseg E))).
    + rewrite Hs2.
      exact (proj2 (GaC3_P05_qmul_abs_bounded f' w' M (/ d) HM
                      (Qle_to_QleT' 0 (/ d) (GaC3_P05_qinv_nonneg d Hd))
                      (Hf f' (GaC3_P05_fk_lookup_fst fvs
                                (fun s => GaC3_P05_kernel_val z0 (fst s))
                                (GaC3_P04_rect_boundary c b T) v f' w' E))
                      (GaC3_P05_fk_lookup_bounded
                         (GaC3_P04_rect_boundary c b T)
                         (fun s => GaC3_P05_kernel_val z0 (fst s)) fvs (/ d)
                         v f' w' Hseg E))).
  - exact (False_rect _
             (GaC3_P05_fk_lookup_none fvs
                (fun s => GaC3_P05_kernel_val z0 (fst s))
                (GaC3_P04_rect_boundary c b T) v E Hv)).
Qed.

(* The L1 length of the P04 rectangle boundary in closed form (the        *)
(* explicit-constant consumption face downstream). *)
Lemma GaC3_P05_len1_rect : forall c b T : Q,
  (0 <= b - c)%Q -> (0 <= T)%Q ->
  GaC3_P03_path_len1 (GaC3_P04_rect_boundary c b T) == 2 * (b - c) + 4 * T.
Proof.
  intros c b T Hbc HT.
  assert (Hcb0 : (c - b <= 0)%Q).
  { apply (GaC3_P05_qle_wd (- (b - c)) (c - b) 0); [ ring | ].
    apply (GaC3_P05_qle_wd_r (- (b - c)) (- 0) 0);
      [ ring | apply Qopp_le_compat; exact Hbc ]. }
  assert (H2T : (0 <= 2 * T)%Q).
  { apply Qmult_le_0_compat.
    - apply (Qlt_le_weak 0 2). apply QltT_to_Qlt. exact qltT_0_2.
    - exact HT. }
  assert (E0 : forall x : Q, Qabs (x - x) == 0).
  { intro x. apply (GaC3_P05_qeq_trans2 _ (Qabs 0)).
    - apply Qabs_wd. ring.
    - apply (Qabs_pos 0 (Qle_refl 0)). }
  assert (E1 : Qabs (b - c) == b - c) by (apply Qabs_pos; exact Hbc).
  assert (E2 : Qabs (c - b) == b - c)
    by (rewrite (GaC3_P05_abs_val_neg (c - b) Hcb0); ring).
  assert (E3 : Qabs (T - - T) == 2 * T).
  { apply (GaC3_P05_qeq_trans2 _ (Qabs (2 * T))).
    - apply Qabs_wd. ring.
    - apply (Qabs_pos (2 * T) H2T). }
  assert (E4 : Qabs (- T - T) == 2 * T).
  { apply (GaC3_P05_qeq_trans2 _ (Qabs (- (2 * T)))).
    - apply Qabs_wd. ring.
    - rewrite Qabs_opp. apply (Qabs_pos (2 * T) H2T). }
  cbn [GaC3_P03_path_len1 GaC3_P04_rect_boundary GaC3_P02_seg_dz fst snd].
  rewrite E1, (E0 (- T)), (E0 b), E3, E2, (E0 T), (E0 c), E4.
  ring.
Qed.

(* The kernel ML face: the closed-loop sum of M-bounded f-data against    *)
(* the kernel data on the P04 rectangle is bounded by (2*M/d) * L1 in     *)
(* both components - the step-carrier analogue of the B/r consumption     *)
(* shape of ZZ deriv_zeta_bound. *)
Theorem GaC3_P05_cauchy_kernel_ml : forall (c b T d : Q) (z0 : Q * Q)
  (fvs : list (Q * Q)) (M : Q),
  QltT 0 d -> GaC3_P05_margin c b T d z0 -> QleT' 0 M ->
  (forall v, In v fvs -> GaC3_P03_val_bounded v M) ->
  Qabs (GaC3_P02_path_sumR (GaC3_P04_rect_boundary c b T)
          (GaC3_P05_vzip fvs
             (GaC3_P05_kernel_data z0 (GaC3_P04_rect_boundary c b T))))
        <= (2 * M * / d) * GaC3_P03_path_len1 (GaC3_P04_rect_boundary c b T)
  /\ Qabs (GaC3_P02_path_sumI (GaC3_P04_rect_boundary c b T)
          (GaC3_P05_vzip fvs
             (GaC3_P05_kernel_data z0 (GaC3_P04_rect_boundary c b T))))
        <= (2 * M * / d) * GaC3_P03_path_len1 (GaC3_P04_rect_boundary c b T).
Proof.
  intros c b T d z0 fvs M Hd Hm HM Hf. split.
  - apply (GaC3_P03_path_sumR_ml _ _ (2 * M * / d)).
    + apply Qmult_le_0_compat.
      * apply Qmult_le_0_compat.
        -- apply (Qlt_le_weak 0 2). apply QltT_to_Qlt. exact qltT_0_2.
        -- apply QleT'_to_Qle. exact HM.
      * apply GaC3_P05_qinv_nonneg. exact Hd.
    + exact (GaC3_P05_fk_bounded fvs c b T d z0 M Hd Hm HM Hf).
  - apply (GaC3_P03_path_sumI_ml _ _ (2 * M * / d)).
    + apply Qmult_le_0_compat.
      * apply Qmult_le_0_compat.
        -- apply (Qlt_le_weak 0 2). apply QltT_to_Qlt. exact qltT_0_2.
        -- apply QleT'_to_Qle. exact HM.
      * apply GaC3_P05_qinv_nonneg. exact Hd.
    + exact (GaC3_P05_fk_bounded fvs c b T d z0 M Hd Hm HM Hf).
Qed.
