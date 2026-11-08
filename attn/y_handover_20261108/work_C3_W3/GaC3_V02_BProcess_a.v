(* ConstructiveWorld-Main - Q-step B-process carrier kit for the C3 completion face. *)

(** * GaC3_V02_BProcess_a: Q-step B-process toolkit leaf A.

    Mission.  Node C3-V02 (segment C3), toolkit leaf A: the Q-step
    B-process carrier kit consumed by [GaC3_V02_BProcess] (the
    completion face): the cell carrier [GaC3_V02_cdat] (weight,
    amplitude, phasor datum), the Q-scalar action [GaC3_V02_gscale],
    the three sum operators (amplitude-weighted grid sum,
    cell-weighted dual frequency-zero integral, mesh mismatch), the
    selector kit (every component face abstracted through a selector
    respecting the phasor walk, the scalar action and the zero
    phasor), the completion identity at the pure qsum level, the
    truncated Poisson kernel on its integer-frequency face, the
    mesh-deviation carrier, and the per-cell scalar bound engine.

    Dependencies.  [GaC3_V01_VdCSecond_a], [GaC3_V01_VdCSecond_b]
    (finite-sum kit, phasor carrier), [GaC3_P03_MLEstimate]
    ([val_bounded] carrier, order micro-helpers), [S01_BaseRing]
    (Set-sorted And), [S02_CauchyComplete] ([QleT']); Stdlib
    [QArith], [List].

    References.  The B-process completion of Srinivasan - van der
    Corput (Graham - Kolesnik, van der Corput's method of exponential
    sums, B-process chapter; Iwaniec - Kowalski Ch. 8); cards_C3
    C3-V02; drafts_C3 V02 statement skeleton (kit leaf, per the
    C3-V01 two-leaf cast pattern).

    Constructivity.  Set-carried data-validation predicates ([QleT']
    reflections through the S01 And product; P03 val_bounded); zero
    assumed constants, zero abandoned proofs, zero classical choice;
    all numerics stay in Q (decidable, exact); order reasoning by
    explicit QArith lemma chains.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
      GaC3_V02_BProcess_a.v] compiles cleanly (exit 0) from the work
      directory (sandbox pair), single compile lane under the
      cpu_guard v3 wrapper (runner.py chain lane). *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import GaC3_V01_VdCSecond_a.
Require Import GaC3_V01_VdCSecond_b.
Require Import GaC3_P03_MLEstimate.

Local Open Scope Q_scope.
Import ListNotations.

(* Section 1. Carrier, accessors, scalar action. *)

(* One cell of the B-process step data: cell weight w, amplitude g, and   *)
(* the phasor datum z (Q-pair carrier of C3-V01).                         *)
Definition GaC3_V02_cdat : Set := (Q * (Q * GaC3_V01_phasor))%type.

Definition GaC3_V02_wt (c : GaC3_V02_cdat) : Q := fst c.
Definition GaC3_V02_amp (c : GaC3_V02_cdat) : Q := fst (snd c).
Definition GaC3_V02_pz (c : GaC3_V02_cdat) : GaC3_V01_phasor := snd (snd c).

(* Q-scalar action on the phasor carrier (the amplitude modulation). *)
Definition GaC3_V02_gscale (g : Q) (z : GaC3_V01_phasor) : GaC3_V01_phasor :=
  (g * fst z, g * snd z).

Lemma GaC3_V02_gscale_fst : forall (g : Q) (z : GaC3_V01_phasor),
  fst (GaC3_V02_gscale g z) == g * fst z.
Proof. intros g z. reflexivity. Qed.

Lemma GaC3_V02_gscale_snd : forall (g : Q) (z : GaC3_V01_phasor),
  snd (GaC3_V02_gscale g z) == g * snd z.
Proof. intros g z. reflexivity. Qed.

(* Component faces of the phasor walk and the zero phasor. *)
Lemma GaC3_V02_pplus_fst : forall z w : GaC3_V01_phasor,
  fst (GaC3_V01_pplus z w) == fst z + fst w.
Proof. intros z w. reflexivity. Qed.

Lemma GaC3_V02_pplus_snd : forall z w : GaC3_V01_phasor,
  snd (GaC3_V01_pplus z w) == snd z + snd w.
Proof. intros z w. reflexivity. Qed.

Lemma GaC3_V02_pzero_fst : fst GaC3_V01_pzero == 0.
Proof. reflexivity. Qed.

Lemma GaC3_V02_pzero_snd : snd GaC3_V01_pzero == 0.
Proof. reflexivity. Qed.

(* Section 2. The three sum operators. *)

(* Weighted exponential sum face: amplitude-weighted phasor sum. *)
Definition GaC3_V02_wsum (cds : list GaC3_V02_cdat) : GaC3_V01_phasor :=
  GaC3_V01_wphas (map (fun c => GaC3_V02_gscale (GaC3_V02_amp c) (GaC3_V02_pz c)) cds).

(* Dual frequency-zero face: cell-weighted step integral of the same data. *)
Definition GaC3_V02_base_dual (cds : list GaC3_V02_cdat) : GaC3_V01_phasor :=
  GaC3_V01_wphas
    (map (fun c => GaC3_V02_gscale (GaC3_V02_wt c)
                                   (GaC3_V02_gscale (GaC3_V02_amp c) (GaC3_V02_pz c)))
         cds).

(* Per-cell mesh-mismatch sum: the explicit remainder witness. *)
Definition GaC3_V02_mismatch (cds : list GaC3_V02_cdat) : GaC3_V01_phasor :=
  GaC3_V01_wphas
    (map (fun c => GaC3_V02_gscale (1 - GaC3_V02_wt c)
                                   (GaC3_V02_gscale (GaC3_V02_amp c) (GaC3_V02_pz c)))
         cds).

(* Section 3. The selector kit. *)

(* Every component face (fst/snd) is abstracted through a selector        *)
(* respecting the phasor walk, the scalar action and the zero phasor;     *)
(* all statements stay at the Qeq level (no equation-sort mixing).        *)
Lemma GaC3_V02_wphas_sel : forall (sel : GaC3_V01_phasor -> Q),
  (forall z w : GaC3_V01_phasor, sel (GaC3_V01_pplus z w) == sel z + sel w) ->
  (forall (g : Q) (z : GaC3_V01_phasor), sel (GaC3_V02_gscale g z) == g * sel z) ->
  (sel GaC3_V01_pzero == 0)%Q ->
  forall l : list GaC3_V01_phasor,
  sel (GaC3_V01_wphas l) == GaC3_V01_qsum (map sel l).
Proof.
  intros sel Hp Hg H0 l. induction l as [| z l IH].
  - cbn [GaC3_V01_wphas map GaC3_V01_qsum]. rewrite H0. reflexivity.
  - cbn [GaC3_V01_wphas map GaC3_V01_qsum]. rewrite Hp, IH. reflexivity.
Qed.

Lemma GaC3_V02_wsum_sel : forall (sel : GaC3_V01_phasor -> Q),
  (forall z w : GaC3_V01_phasor, sel (GaC3_V01_pplus z w) == sel z + sel w) ->
  (forall (g : Q) (z : GaC3_V01_phasor), sel (GaC3_V02_gscale g z) == g * sel z) ->
  (sel GaC3_V01_pzero == 0)%Q ->
  forall cds : list GaC3_V02_cdat,
  sel (GaC3_V02_wsum cds)
  == GaC3_V01_qsum (map (fun c => GaC3_V02_amp c * sel (GaC3_V02_pz c)) cds).
Proof.
  intros sel Hp Hg H0 cds. unfold GaC3_V02_wsum in *.
  induction cds as [| c cds IH].
  - cbn [map GaC3_V01_wphas GaC3_V01_qsum]. rewrite H0. reflexivity.
  - cbn [map GaC3_V01_wphas GaC3_V01_qsum]. cbv beta.
    rewrite Hp, Hg, IH. reflexivity.
Qed.

Lemma GaC3_V02_base_dual_sel : forall (sel : GaC3_V01_phasor -> Q),
  (forall z w : GaC3_V01_phasor, sel (GaC3_V01_pplus z w) == sel z + sel w) ->
  (forall (g : Q) (z : GaC3_V01_phasor), sel (GaC3_V02_gscale g z) == g * sel z) ->
  (sel GaC3_V01_pzero == 0)%Q ->
  forall cds : list GaC3_V02_cdat,
  sel (GaC3_V02_base_dual cds)
  == GaC3_V01_qsum
       (map (fun c => GaC3_V02_wt c * (GaC3_V02_amp c * sel (GaC3_V02_pz c))) cds).
Proof.
  intros sel Hp Hg H0 cds. unfold GaC3_V02_base_dual in *.
  induction cds as [| c cds IH].
  - cbn [map GaC3_V01_wphas GaC3_V01_qsum]. rewrite H0. reflexivity.
  - cbn [map GaC3_V01_wphas GaC3_V01_qsum]. cbv beta.
    rewrite Hp, Hg, Hg, IH. reflexivity.
Qed.

Lemma GaC3_V02_mismatch_sel : forall (sel : GaC3_V01_phasor -> Q),
  (forall z w : GaC3_V01_phasor, sel (GaC3_V01_pplus z w) == sel z + sel w) ->
  (forall (g : Q) (z : GaC3_V01_phasor), sel (GaC3_V02_gscale g z) == g * sel z) ->
  (sel GaC3_V01_pzero == 0)%Q ->
  forall cds : list GaC3_V02_cdat,
  sel (GaC3_V02_mismatch cds)
  == GaC3_V01_qsum
       (map (fun c => (1 - GaC3_V02_wt c) * (GaC3_V02_amp c * sel (GaC3_V02_pz c)))
            cds).
Proof.
  intros sel Hp Hg H0 cds. unfold GaC3_V02_mismatch in *.
  induction cds as [| c cds IH].
  - cbn [map GaC3_V01_wphas GaC3_V01_qsum]. rewrite H0. reflexivity.
  - cbn [map GaC3_V01_wphas GaC3_V01_qsum]. cbv beta.
    rewrite Hp, Hg, Hg, IH. reflexivity.
Qed.

(* Completion identity at the pure qsum level, selector-generic: the      *)
(* unweighted amplitude term splits into the weighted dual term plus the  *)
(* mesh-mismatch term.                                                    *)
Lemma GaC3_V02_wsum_split_sel : forall (sel : GaC3_V01_phasor -> Q)
  (cds : list GaC3_V02_cdat),
  GaC3_V01_qsum (map (fun c => GaC3_V02_amp c * sel (GaC3_V02_pz c)) cds)
  == GaC3_V01_qsum (map (fun c => GaC3_V02_wt c * (GaC3_V02_amp c * sel (GaC3_V02_pz c))) cds)
     + GaC3_V01_qsum
         (map (fun c => (1 - GaC3_V02_wt c) * (GaC3_V02_amp c * sel (GaC3_V02_pz c))) cds).
Proof.
  intros sel cds. induction cds as [| c cds IH].
  - reflexivity.
  - cbn [map GaC3_V01_qsum]. rewrite IH. ring.
Qed.

(* Section 4. The truncated kernel (integer-frequency face). *)

(* The truncated Poisson kernel sin(pi y)/(pi y) at the integer dual      *)
(* frequencies: the constructive y=0 extension gives the value 1 at       *)
(* m = 0, and sin(pi m) = 0 gives the value 0 at every m <> 0 (exact Q,   *)
(* no transcendental evaluation).                                         *)
Definition GaC3_V02_trunc_kernel (m : nat) : Q :=
  match m with
  | 0%nat => 1
  | Datatypes.S _ => 0
  end.

Lemma GaC3_V02_trunc_kernel_zero : GaC3_V02_trunc_kernel 0 == 1.
Proof. reflexivity. Qed.

Lemma GaC3_V02_trunc_kernel_succ : forall m : nat,
  GaC3_V02_trunc_kernel (Datatypes.S m) == 0.
Proof. intro m. reflexivity. Qed.

(* Section 5. Mesh-deviation carrier and the scalar bound engine. *)

(* Mesh-deviation carrier: |1 - w| <= delta, as a two-sided QleT' product *)
(* (Set-borne, S02 QleT' pattern; the check is a computation).            *)
Definition GaC3_V02_wdev (w delta : Q) : Set :=
  And (QleT' (1 - w) delta) (QleT' (- (1 - w)) delta).

(* Bridge (elim): Set bearer -> Qabs face. *)
Lemma GaC3_V02_wdev_abs : forall w delta : Q,
  GaC3_V02_wdev w delta -> Qabs (1 - w) <= delta.
Proof.
  intros w delta H. destruct H as [H1 H2].
  apply (proj2 (Qabs_Qle_condition (1 - w) delta)). split.
  - pose proof (Qopp_le_compat _ _ (QleT'_to_Qle _ _ H2)) as H2'.
    rewrite Qopp_involutive in H2'. exact H2'.
  - exact (QleT'_to_Qle _ _ H1).
Qed.

(* Bridge (intro): two-sided Qle -> Set bearer. *)
Lemma GaC3_V02_wdev_intro : forall w delta : Q,
  (1 - w <= delta)%Q -> (- (1 - w) <= delta)%Q -> GaC3_V02_wdev w delta.
Proof.
  intros w delta H1 H2. split.
  - apply Qle_to_QleT'. exact H1.
  - apply Qle_to_QleT'. exact H2.
Qed.

(* Per-cell scalar bound: |(1-w)*(g*x)| <= delta * B under the mesh,      *)
(* amplitude and unit faces (pure Q level; the component instantiations   *)
(* select x through the val_bounded faces of the phasor datum).           *)
Lemma GaC3_V02_term_abs_le : forall (w g x delta B : Q),
  QleT' 0 delta -> QleT' 0 B -> GaC3_V02_wdev w delta ->
  GaC3_P03_val_bounded (g, 0) B -> QleT' (- 1) x -> QleT' x 1 ->
  Qabs ((1 - w) * (g * x)) <= (delta * B)%Q.
Proof.
  intros w g x delta B Hd Hb Hwd Hv Hx1 Hx2.
  pose proof (QleT'_to_Qle 0 delta Hd) as Hd0.
  pose proof (QleT'_to_Qle 0 B Hb) as Hb0.
  destruct Hv as [Hg1 [Hg2 [Hg3 Hg4]]].
  assert (Hg : Qabs g <= B).
  { apply (proj2 (Qabs_Qle_condition g B)). split.
    - exact (QleT'_to_Qle _ _ Hg1).
    - exact (QleT'_to_Qle _ _ Hg2). }
  assert (Hx : Qabs x <= 1).
  { apply (proj2 (Qabs_Qle_condition x 1)). split.
    - exact (QleT'_to_Qle _ _ Hx1).
    - exact (QleT'_to_Qle _ _ Hx2). }
  assert (Hwd' : Qabs (1 - w) <= delta) by (apply GaC3_V02_wdev_abs; exact Hwd).
  rewrite Qabs_Qmult, Qabs_Qmult.
  rewrite (Qmult_assoc (Qabs (1 - w)) (Qabs g) (Qabs x)).
  apply (Qle_trans _ ((delta * B) * Qabs x)).
  - apply (Qmult_le_compat_r).
    + apply (Qle_trans _ (delta * Qabs g)).
      * apply (Qmult_le_compat_r); [ exact Hwd' | apply Qabs_nonneg ].
      * exact (GaC3_P03_qmult_le_l delta (Qabs g) B Hd0 Hg).
    + apply Qabs_nonneg.
  - apply (Qle_trans _ ((delta * B) * 1)).
    + exact (GaC3_P03_qmult_le_l (delta * B) (Qabs x) 1
               (Qmult_le_0_compat delta B Hd0 Hb0) Hx).
    + rewrite Qmult_1_r. apply Qle_refl.
Qed.

(* Iterated triangle inequality for the Q list sum. *)
Lemma GaC3_V02_abs_qsum_le : forall l : list Q,
  Qabs (GaC3_V01_qsum l) <= GaC3_V01_qsum (map Qabs l)%Q.
Proof.
  induction l as [| a l IH].
  - cbn [map GaC3_V01_qsum]. apply Qle_refl.
  - cbn [map GaC3_V01_qsum].
    eapply Qle_trans; [ apply Qabs_triangle | ].
    apply Qplus_le_compat; [ apply Qle_refl | exact IH ].
Qed.

(* Pointwise-bound transport for list sums over the cell carrier. *)
Lemma GaC3_V02_qsum_map_le : forall (f g : GaC3_V02_cdat -> Q) (l : list GaC3_V02_cdat),
  (forall c, In c l -> f c <= g c)%Q ->
  GaC3_V01_qsum (map f l) <= GaC3_V01_qsum (map g l).
Proof.
  intros f g l. induction l as [| c l IH]; intro Hpt.
  - apply Qle_refl.
  - cbn [map GaC3_V01_qsum]. apply Qplus_le_compat.
    + apply Hpt. apply in_eq.
    + apply IH. intros x Hx. apply Hpt. exact (in_cons c x l Hx).
Qed.
