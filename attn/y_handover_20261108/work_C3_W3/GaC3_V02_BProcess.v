(* ConstructiveWorld-Main - B-process completion face on the Q-step phasor carrier. *)

(** * GaC3_V02_BProcess: the B-process completion face.

    Mission.  Node C3-V02 (segment C3): the B-process completion face
    (Srinivasan - van der Corput form with the truncated Poisson kernel),
    rebuilt on the Q-step phasor carrier per the P01/P03 Q-step doctrine
    (toolkit leaf A is [GaC3_V02_BProcess_a]).  The cast carries: the P01
    step-integral bridge of the dual frequency-zero face, the
    kernel-weighted dual frequency sum, the kernel collapse lemma (the
    Poisson sampling identity: the dual sum equals its frequency-zero term
    for every truncation length and every dual datum family), the
    completion identity (grid sum = dual sum + remainder, componentwise),
    and the explicit remainder bound |E| <= L*delta*B (mesh deviation
    delta, amplitude bound B, unit-phasor face, L cells)
    [GaC3_V02_b_process_completion], [GaC3_V02_b_process_completion_expl].

    Dependencies.  [GaC3_V02_BProcess_a] (toolkit leaf A),
    [GaC3_P01_LineIntegralDef] (step-integral weight machinery),
    [GaC3_P03_MLEstimate] ([val_bounded] carrier), [GaC3_V01_VdCSecond_a],
    [GaC3_V01_VdCSecond_b], [S01_BaseRing], [S02_CauchyComplete]; Stdlib
    [QArith], [List].

    References.  The B-process completion of Srinivasan - van der Corput
    (Graham - Kolesnik, van der Corput's method of exponential sums,
    B-process chapter; Iwaniec - Kowalski Ch. 8): the weighted exponential
    sum equals the dual sum of frequency integrals weighted by the
    truncated kernel sin(pi y)/(pi y) plus an explicit remainder; cards_C3
    C3-V02; drafts_C3 V02 statement skeleton.

    Constructivity.  Set-carried data-validation predicates ([QleT']
    reflections through the S01 And product; P03 val_bounded); zero
    assumed constants, zero abandoned proofs, zero classical choice; all
    numerics stay in Q (decidable, exact); order reasoning by explicit
    QArith lemma chains.  Honest scope, out of the exact-Q carrier: the
    real-line kernel face sin(pi y)/(pi y) at non-integer y, the
    phase-derivative bound |f'| <= 1/2, the higher-frequency dual
    integrals; the dual datum family is a Section variable, annihilated by
    the kernel weights.  Mapping: cmod E <= Rrem as the componentwise Qabs
    view (P03 val_bounded, lemmas [mismatch_bound] / [val_bounded_mono]);
    cadd as the Q-pair plus; smooth_decay g as the amplitude-bound family;
    the m=0 dual integral as the cell-weighted step integral of the same
    data.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_V02_BProcess.v] compiles cleanly (exit 0) from the work directory
    (sandbox pair), single compile lane under the cpu_guard v3 wrapper
    (runner.py chain lane). *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import GaC3_V01_VdCSecond_a.
Require Import GaC3_V01_VdCSecond_b.
Require Import GaC3_P01_LineIntegralDef.
Require Import GaC3_P03_MLEstimate.
Require Import GaC3_V02_BProcess_a.

Local Open Scope Q_scope.
Import ListNotations.

(* Section 1. The P01 step-integral bridge of the dual m=0 face. *)

(* The P01 cell backing one B-process cell: width wt c on the unit base,  *)
(* carrying the amplitude-modulated phasor value (u - l reduces to wt c). *)
Definition GaC3_V02_pcell (c : GaC3_V02_cdat) : GaC3_P01_cell :=
  ((0, GaC3_V02_wt c),
   (GaC3_V02_amp c * fst (GaC3_V02_pz c), GaC3_V02_amp c * snd (GaC3_V02_pz c))).

Lemma GaC3_V02_pcell_cw_R : forall c : GaC3_V02_cdat,
  fst (GaC3_P01_cw (GaC3_V02_pcell c))
  == GaC3_V02_wt c * (GaC3_V02_amp c * fst (GaC3_V02_pz c)).
Proof.
  intro c. cbn [GaC3_V02_pcell GaC3_P01_cw fst]. ring.
Qed.

Lemma GaC3_V02_pcell_cw_I : forall c : GaC3_V02_cdat,
  snd (GaC3_P01_cw (GaC3_V02_pcell c))
  == GaC3_V02_wt c * (GaC3_V02_amp c * snd (GaC3_V02_pz c)).
Proof.
  intro c. cbn [GaC3_V02_pcell GaC3_P01_cw snd]. ring.
Qed.

(* The dual frequency-zero face IS the P01 weighted step sum of the       *)
(* modulated data (both components) - the step-integral consumption. *)
Lemma GaC3_V02_base_dual_pstep_R : forall cds : list GaC3_V02_cdat,
  fst (GaC3_V02_base_dual cds) == GaC3_P01_qstep_sumR (map GaC3_V02_pcell cds).
Proof.
  intro cds.
  rewrite (GaC3_V02_base_dual_sel fst GaC3_V02_pplus_fst GaC3_V02_gscale_fst
             GaC3_V02_pzero_fst cds).
  induction cds as [| c cds IH].
  - reflexivity.
  - cbn [map GaC3_V01_qsum]. cbv beta. rewrite IH.
    rewrite GaC3_P01_qstep_sumR_cons, (GaC3_V02_pcell_cw_R c). ring.
Qed.

Lemma GaC3_V02_base_dual_pstep_I : forall cds : list GaC3_V02_cdat,
  snd (GaC3_V02_base_dual cds) == GaC3_P01_qstep_sumI (map GaC3_V02_pcell cds).
Proof.
  intro cds.
  rewrite (GaC3_V02_base_dual_sel snd GaC3_V02_pplus_snd GaC3_V02_gscale_snd
             GaC3_V02_pzero_snd cds).
  induction cds as [| c cds IH].
  - reflexivity.
  - cbn [map GaC3_V01_qsum]. cbv beta. rewrite IH.
    rewrite GaC3_P01_qstep_sumI_cons, (GaC3_V02_pcell_cw_I c). ring.
Qed.

(* Section 2. The ML remainder bound. *)

(* Selector-generic remainder bound: |sel(mismatch)| <= L*delta*B. *)
Lemma GaC3_V02_mismatch_abs_sel : forall (sel : GaC3_V01_phasor -> Q),
  (forall z w : GaC3_V01_phasor, sel (GaC3_V01_pplus z w) == sel z + sel w) ->
  (forall (g : Q) (z : GaC3_V01_phasor), sel (GaC3_V02_gscale g z) == g * sel z) ->
  (sel GaC3_V01_pzero == 0)%Q ->
  forall (cds : list GaC3_V02_cdat) (delta B : Q),
  QleT' 0 delta -> QleT' 0 B ->
  (forall c, In c cds -> GaC3_V02_wdev (GaC3_V02_wt c) delta) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_amp c, 0) B) ->
  (forall c, In c cds -> QleT' (- 1) (sel (GaC3_V02_pz c))) ->
  (forall c, In c cds -> QleT' (sel (GaC3_V02_pz c)) 1) ->
  Qabs (sel (GaC3_V02_mismatch cds)) <= (GaC3_V01_qn (length cds) * delta * B)%Q.
Proof.
  intros sel Hp Hg H0 cds delta B Hd Hb Hmesh Hamp Hlo Hhi.
  pose proof (QleT'_to_Qle 0 delta Hd) as Hd0.
  pose proof (QleT'_to_Qle 0 B Hb) as Hb0.
  rewrite (GaC3_V02_mismatch_sel sel Hp Hg H0 cds).
  eapply Qle_trans; [ apply GaC3_V02_abs_qsum_le | ].
  rewrite map_map.
  apply (Qle_trans _
           (GaC3_V01_qsum (map (fun _ : GaC3_V02_cdat => delta * B) cds))).
  - apply GaC3_V02_qsum_map_le. intros c Hc.
    apply (GaC3_V02_term_abs_le (GaC3_V02_wt c) (GaC3_V02_amp c)
             (sel (GaC3_V02_pz c)) delta B Hd Hb).
    + apply Hmesh. exact Hc.
    + apply Hamp. exact Hc.
    + apply Hlo. exact Hc.
    + apply Hhi. exact Hc.
  - rewrite (GaC3_V01_qsum_const_mul GaC3_V02_cdat (delta * B) cds).
    rewrite (Qmult_assoc (GaC3_V01_qn (length cds)) delta B).
    apply Qle_refl.
Qed.

(* The explicit remainder bound: the mismatch sum is componentwise        *)
(* bounded by L*delta*B (L cells, mesh delta, amplitude B, unit phasors). *)
Lemma GaC3_V02_mismatch_bound : forall (cds : list GaC3_V02_cdat) (delta B : Q),
  QleT' 0 delta -> QleT' 0 B ->
  (forall c, In c cds -> GaC3_V02_wdev (GaC3_V02_wt c) delta) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_amp c, 0) B) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_pz c) 1) ->
  GaC3_P03_val_bounded (GaC3_V02_mismatch cds)
    (GaC3_V01_qn (length cds) * delta * B).
Proof.
  intros cds delta B Hd Hb Hmesh Hamp Hunit.
  assert (HR : Qabs (fst (GaC3_V02_mismatch cds))
               <= (GaC3_V01_qn (length cds) * delta * B)%Q).
  { apply (GaC3_V02_mismatch_abs_sel fst GaC3_V02_pplus_fst GaC3_V02_gscale_fst
             GaC3_V02_pzero_fst cds delta B Hd Hb Hmesh Hamp).
    - intros c Hc. destruct (Hunit c Hc) as [Hu1 [Hu2 [Hu3 Hu4]]]. exact Hu1.
    - intros c Hc. destruct (Hunit c Hc) as [Hu1 [Hu2 [Hu3 Hu4]]]. exact Hu2. }
  assert (HI : Qabs (snd (GaC3_V02_mismatch cds))
               <= (GaC3_V01_qn (length cds) * delta * B)%Q).
  { apply (GaC3_V02_mismatch_abs_sel snd GaC3_V02_pplus_snd GaC3_V02_gscale_snd
             GaC3_V02_pzero_snd cds delta B Hd Hb Hmesh Hamp).
    - intros c Hc. destruct (Hunit c Hc) as [Hu1 [Hu2 [Hu3 Hu4]]]. exact Hu3.
    - intros c Hc. destruct (Hunit c Hc) as [Hu1 [Hu2 [Hu3 Hu4]]]. exact Hu4. }
  destruct (proj1 (Qabs_Qle_condition (fst (GaC3_V02_mismatch cds))
                     (GaC3_V01_qn (length cds) * delta * B)) HR) as [Hr1 Hr2].
  destruct (proj1 (Qabs_Qle_condition (snd (GaC3_V02_mismatch cds))
                     (GaC3_V01_qn (length cds) * delta * B)) HI) as [Hi1 Hi2].
  apply GaC3_P03_val_bounded_of_Qle.
  split; [ exact Hr1 | split; [ exact Hr2 | split; [ exact Hi1 | exact Hi2 ] ] ].
Qed.

(* Remainder-bound transport along the Rrem slot. *)
Lemma GaC3_V02_val_bounded_mono : forall (v : GaC3_V01_phasor) (C Rrem : Q),
  GaC3_P03_val_bounded v C -> QleT' C Rrem -> GaC3_P03_val_bounded v Rrem.
Proof.
  intros v C Rrem HC HR.
  pose proof (QleT'_to_Qle C Rrem HR) as HCle.
  apply GaC3_P03_val_bounded_of_Qle.
  destruct (GaC3_P03_val_bounded_Qle v C HC) as [H1 [H2 [H3 H4]]].
  split; [ | split; [ | split ] ].
  - exact (Qle_trans _ _ _ (Qopp_le_compat _ _ HCle) H1).
  - exact (Qle_trans _ _ _ H2 HCle).
  - exact (Qle_trans _ _ _ (Qopp_le_compat _ _ HCle) H3).
  - exact (Qle_trans _ _ _ H4 HCle).
Qed.

(* Section 3. The kernel-weighted dual sum and the completion theorems. *)

Section V02_B.

(* The explicit remainder constant of the draft skeleton: a Section-      *)
(* variable slot (discharge position for the consuming instance; zero     *)
(* global assumptions).                                                   *)
Variable Rrem : Q.

(* The dual-integral datum family at the nonzero truncated frequencies    *)
(* (the transcendental face of the draft; annihilated by the kernel       *)
(* weights at integer frequencies, see the collapse lemma below).         *)
Variable dualv : nat -> GaC3_V01_phasor.

(* The dual-integral datum at frequency m: the frequency-zero face is the *)
(* concrete cell-weighted step integral; higher frequencies carry the     *)
(* dual datum family.                                                     *)
Definition GaC3_V02_dual_term (cds : list GaC3_V02_cdat) (m : nat) : GaC3_V01_phasor :=
  match m with
  | 0%nat => GaC3_V02_base_dual cds
  | Datatypes.S m' => dualv m'
  end.

(* The kernel-weighted dual sum over the truncated frequency set          *)
(* {0, ..., M} (the dual_sum face of the draft skeleton).                 *)
Definition GaC3_V02_dual_sum (cds : list GaC3_V02_cdat) (M : nat) : GaC3_V01_phasor :=
  GaC3_V01_wphas
    (map (fun m => GaC3_V02_gscale (GaC3_V02_trunc_kernel m)
                                   (GaC3_V02_dual_term cds m))
         (seq 0 (Datatypes.S M))).

(* Kernel collapse (Poisson sampling identity), selector-generic: the     *)
(* dual sum equals its frequency-zero term for every truncation length M  *)
(* and every dual datum family.                                           *)
Lemma GaC3_V02_dual_sum_base_sel : forall (sel : GaC3_V01_phasor -> Q),
  (forall z w : GaC3_V01_phasor, sel (GaC3_V01_pplus z w) == sel z + sel w) ->
  (forall (g : Q) (z : GaC3_V01_phasor), sel (GaC3_V02_gscale g z) == g * sel z) ->
  (sel GaC3_V01_pzero == 0)%Q ->
  forall (cds : list GaC3_V02_cdat) (M : nat),
  sel (GaC3_V02_dual_sum cds M) == sel (GaC3_V02_base_dual cds).
Proof.
  intros sel Hp Hg H0 cds M. unfold GaC3_V02_dual_sum.
  rewrite (GaC3_V02_wphas_sel sel Hp Hg H0), map_map.
  cbn [seq map GaC3_V01_qsum].
  rewrite (GaC3_V01_map_seq_S Q
             (fun i => sel (GaC3_V02_gscale (GaC3_V02_trunc_kernel i)
                                            (GaC3_V02_dual_term cds i))) M).
  cbv beta.
  assert (Etail : GaC3_V01_qsum
              (map (fun i => sel (GaC3_V02_gscale
                                   (GaC3_V02_trunc_kernel (Datatypes.S i))
                                   (GaC3_V02_dual_term cds (Datatypes.S i))))
                   (seq 0 M)) == 0).
  { rewrite (GaC3_V01_qsum_ext
               (fun i => sel (GaC3_V02_gscale
                                  (GaC3_V02_trunc_kernel (Datatypes.S i))
                                  (GaC3_V02_dual_term cds (Datatypes.S i))))
               (fun _ : nat => 0) M 0%nat).
    - rewrite GaC3_V01_qsum_map_0. reflexivity.
    - intros i _. rewrite Hg.
      cbn [GaC3_V02_trunc_kernel GaC3_V02_dual_term]. ring. }
  rewrite Etail.
  cbn [GaC3_V02_trunc_kernel GaC3_V02_dual_term]. rewrite Hg. ring.
Qed.

(* The B-process completion theorem (draft skeleton face, rebuilt on the  *)
(* Q-step carrier): the weighted exponential sum equals the kernel-       *)
(* weighted dual sum plus an explicit remainder E, componentwise bounded  *)
(* by Rrem.                                                               *)
Theorem GaC3_V02_b_process_completion : forall (cds : list GaC3_V02_cdat)
  (delta B : Q),
  QleT' 0 delta -> QleT' 0 B ->
  (forall c, In c cds -> GaC3_V02_wdev (GaC3_V02_wt c) delta) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_amp c, 0) B) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_pz c) 1) ->
  QleT' (GaC3_V01_qn (length cds) * delta * B) Rrem ->
  exists E : GaC3_V01_phasor,
    Qabs (fst E) <= Rrem /\ Qabs (snd E) <= Rrem /\
    fst (GaC3_V02_wsum cds)
      == fst (GaC3_V01_pplus (GaC3_V02_dual_sum cds (length cds)) E) /\
    snd (GaC3_V02_wsum cds)
      == snd (GaC3_V01_pplus (GaC3_V02_dual_sum cds (length cds)) E).
Proof.
  intros cds delta B Hd Hb Hmesh Hamp Hunit Hcover.
  exists (GaC3_V02_mismatch cds).
  assert (HB : GaC3_P03_val_bounded (GaC3_V02_mismatch cds) Rrem).
  { apply (GaC3_V02_val_bounded_mono (GaC3_V02_mismatch cds)
             (GaC3_V01_qn (length cds) * delta * B) Rrem).
    - apply GaC3_V02_mismatch_bound; assumption.
    - exact Hcover. }
  destruct (GaC3_P03_val_bounded_Qle _ _ HB) as [H1 [H2 [H3 H4]]].
  split; [ | split; [ | split ] ].
  - apply (proj2 (Qabs_Qle_condition (fst (GaC3_V02_mismatch cds)) Rrem)).
    split; [ exact H1 | exact H2 ].
  - apply (proj2 (Qabs_Qle_condition (snd (GaC3_V02_mismatch cds)) Rrem)).
    split; [ exact H3 | exact H4 ].
  - cbn [GaC3_V01_pplus fst].
    rewrite (GaC3_V02_dual_sum_base_sel fst GaC3_V02_pplus_fst GaC3_V02_gscale_fst
               GaC3_V02_pzero_fst cds (length cds)).
    rewrite (GaC3_V02_wsum_sel fst GaC3_V02_pplus_fst GaC3_V02_gscale_fst
               GaC3_V02_pzero_fst cds),
            (GaC3_V02_base_dual_sel fst GaC3_V02_pplus_fst GaC3_V02_gscale_fst
               GaC3_V02_pzero_fst cds),
            (GaC3_V02_mismatch_sel fst GaC3_V02_pplus_fst GaC3_V02_gscale_fst
               GaC3_V02_pzero_fst cds).
    apply (GaC3_V02_wsum_split_sel fst).
  - cbn [GaC3_V01_pplus snd].
    rewrite (GaC3_V02_dual_sum_base_sel snd GaC3_V02_pplus_snd GaC3_V02_gscale_snd
               GaC3_V02_pzero_snd cds (length cds)).
    rewrite (GaC3_V02_wsum_sel snd GaC3_V02_pplus_snd GaC3_V02_gscale_snd
               GaC3_V02_pzero_snd cds),
            (GaC3_V02_base_dual_sel snd GaC3_V02_pplus_snd GaC3_V02_gscale_snd
               GaC3_V02_pzero_snd cds),
            (GaC3_V02_mismatch_sel snd GaC3_V02_pplus_snd GaC3_V02_gscale_snd
               GaC3_V02_pzero_snd cds).
    apply (GaC3_V02_wsum_split_sel snd).
Qed.

End V02_B.

(* The Rrem slot discharged constructively: the remainder constant is the *)
(* derived explicit value L*delta*B, and the dual datum family is         *)
(* instantiated at the zero family (immaterial by the kernel collapse).   *)
Theorem GaC3_V02_b_process_completion_expl : forall (cds : list GaC3_V02_cdat)
  (delta B : Q),
  QleT' 0 delta -> QleT' 0 B ->
  (forall c, In c cds -> GaC3_V02_wdev (GaC3_V02_wt c) delta) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_amp c, 0) B) ->
  (forall c, In c cds -> GaC3_P03_val_bounded (GaC3_V02_pz c) 1) ->
  exists E : GaC3_V01_phasor,
    Qabs (fst E) <= (GaC3_V01_qn (length cds) * delta * B)%Q /\
    Qabs (snd E) <= (GaC3_V01_qn (length cds) * delta * B)%Q /\
    fst (GaC3_V02_wsum cds)
      == fst (GaC3_V01_pplus
               (GaC3_V02_dual_sum (fun _ : nat => GaC3_V01_pzero) cds (length cds)) E) /\
    snd (GaC3_V02_wsum cds)
      == snd (GaC3_V01_pplus
               (GaC3_V02_dual_sum (fun _ : nat => GaC3_V01_pzero) cds (length cds)) E).
Proof.
  intros cds delta B Hd Hb Hmesh Hamp Hunit.
  exact (GaC3_V02_b_process_completion (GaC3_V01_qn (length cds) * delta * B)
           (fun _ : nat => GaC3_V01_pzero) cds delta B Hd Hb Hmesh Hamp Hunit
           (Qle_to_QleT' _ _ (Qle_refl (GaC3_V01_qn (length cds) * delta * B)))).
Qed.
