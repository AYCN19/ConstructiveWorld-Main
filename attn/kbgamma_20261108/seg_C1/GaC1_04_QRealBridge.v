(* ConstructiveWorld-Main - the Q to Real certificate lifting bridge with
   explicit margin witnesses and the craft-discipline helpers. *)

(** * GaC1_04_QRealBridge: the Q-to-Real order bridge.

    Mission.  The Q -> Real certificate lifting bridge with explicit
      margin witnesses [gaC1_04_qlt_const_lt], the sinking direction
      back to a rational witness [gaC1_04_const_lt_qlt_down], and the
      segment-consumable craft-discipline helpers
      [gaC1_04_const_margin]/[gaC1_04_qltT_pointwise_transfer]
      (transparent certificate Definition and the named [QltT]
      pointwise-transfer step, replacing raw apply on unexpanded
      transparent Definitions).

    Dependencies.  Stdlib [Arith.PeanoNat], [QArith.QArith],
      [QArith.Qring], [Setoid], [Morphisms] ([Qcompare_comp],
      [Qmult_lt_compat_r], [Qplus_lt_l/r], [Qplus_opp_r],
      [Qmult_0_l], [Qmult_1_l], [Qmult_comm]).  Requires
      [S01_BaseRing] and [S02_CauchyComplete] ([Real],
      [real_const], [real_lt], [QltT]) of this development.

    References.  This development, [CxRealPairCore] (the family
      precedent [c_norm_sq_Q_pos_bridge] at CxRealPairCore.v:301,
      dual-margin form; the consumption uses the [Qcompare_comp]
      transfer).  Discipline anchors: E840 exact-bridge lemma
      discipline, E841 transparent certificate Definition, E845
      witness sensitivity.  Sample-band craft
      piu_zz_ln_rate_bound.v:246-277.

    Constructivity.  Every named construction is carried by [Set]; all
      predicates are Set-sorted ([real_lt], [QltT], [Id]); zero
      classical choice; margin witnesses are explicit sigT
      inputs/outputs; the development is closed under the global
      context; [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_04_QRealBridge.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.

(* ===================================================================== *)
(* Section 1. Pit-discipline helpers (D3: craft artifacts, zero new       *)
(* mathematics).                                                          *)
(* ===================================================================== *)

Section PitHelpers.

(* D3a. The margin witness as a transparent certificate Definition        *)
(*      (E841 discipline: the certificate lives in a named transparent    *)
(*      artifact, never inlined into proof bodies).                       *)
Definition gaC1_04_const_margin (q1 q2 : Q) : Q :=
  (q2 - q1) * (1#2)%Q.

(* D3b. The named QltT pointwise-transfer step (E840 discipline: instead  *)
(*      of a raw apply that refuses to unfold transparent Definitions,   *)
(*      the Qcompare_comp dance is exported as an explicit bridge lemma). *)
Lemma gaC1_04_qltT_pointwise_transfer :
  forall (u v w : Q), u == v -> QltT w u -> QltT w v.
Proof.
  intros u v w Huv H.
  unfold QltT in *.
  assert (Hcmp : (w ?= u)%Q = (w ?= v)%Q)
    by (apply Qcompare_comp; [apply Qeq_refl | exact Huv]).
  unfold Qlt_bool in *.
  rewrite Hcmp in H.
  exact H.
Qed.

End PitHelpers.

(* ===================================================================== *)
(* Section 2. The lifting bridge (D1) and the sinking bridge (D2).        *)
(* ===================================================================== *)

Section QRealBridge.

(* D1. QltT q1 q2 -> real_lt (real_const q1) (real_const q2): the margin  *)
(*     witness is the transparent certificate D3a at half the gap.        *)
Lemma gaC1_04_qlt_const_lt :
  forall q1 q2 : Q, QltT q1 q2 -> real_lt (real_const q1) (real_const q2).
Proof.
  intros q1 q2 H.
  assert (Hq : Qlt q1 q2) by (apply QltT_to_Qlt; exact H).
  assert (Hd : Qlt 0 (q2 - q1)).
  { unfold Qminus.
    rewrite <- (Qplus_opp_r q1).
    apply Qplus_lt_l.
    exact Hq. }
  assert (Hhalf : Qlt (1#2)%Q 1) by reflexivity.
  assert (Hhalf0 : Qlt 0 (1#2)%Q) by reflexivity.
  unfold real_lt.
  exists (gaC1_04_const_margin q1 q2).
  split.
  - (* 0 < margin *)
    apply Qlt_to_QltT.
    unfold gaC1_04_const_margin.
    pose proof (Qmult_lt_compat_r 0 (q2 - q1) (1#2)%Q Hhalf0 Hd) as Hlt0.
    rewrite (Qmult_0_l (1#2)%Q) in Hlt0.
    exact Hlt0.
  - exists 0%nat. intros n Hn.
    cbn [real_const projT1].
    apply Qlt_to_QltT.
    unfold gaC1_04_const_margin.
    pose proof (Qmult_lt_compat_r (1#2)%Q 1 (q2 - q1) Hd Hhalf) as Hlt.
    rewrite (Qmult_1_l (q2 - q1)) in Hlt.
    rewrite (Qmult_comm (1#2)%Q (q2 - q1)) in Hlt.
    exact Hlt.
Qed.

(* D2. Sinking: a strict order between constants yields an explicit       *)
(*     rational margin witness (sample-band certificate form).            *)
Lemma gaC1_04_const_lt_qlt_down :
  forall q1 q2 : Q,
    real_lt (real_const q1) (real_const q2) ->
    sigT (fun d : Q => And (QltT 0 d) (Qlt (q1 + d) q2)).
Proof.
  intros q1 q2 H. unfold real_lt in H.
  destruct H as [eps [H0 [N HN]]].
  assert (HNN : NatLe N N) by (apply NatLe_lift; apply Nat.le_refl).
  specialize (HN N HNN).
  cbn [real_const projT1] in HN.
  apply QltT_to_Qlt in HN.
  exists eps. split.
  - exact H0.
  - unfold Qminus in HN.
    assert (Hring : q1 + (q2 + (- q1))%Q == q2) by ring.
    rewrite <- Hring.
    apply (proj2 (Qplus_lt_r eps (q2 + (- q1))%Q q1)).
    exact HN.
Qed.

End QRealBridge.
