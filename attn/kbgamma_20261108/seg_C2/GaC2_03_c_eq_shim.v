(* ConstructiveWorld-Main - the Set-layer equality-relation shim for the Cx
   carrier in the QeqT/QltT family design language. *)
(** * GaC2_03_c_eq_shim: the Cx equality shim.
    Mission.  The Set-layer equality-relation shim for the [Cx]
      carrier, in the [QeqT]/[QltT] family design language: the
      relation face is [c_eq] itself (Set-sorted, Re/Im
      pair-carried), supplied with reflexivity, symmetry and
      transitivity faces, a substitutivity face for every consumed Cx
      function (plus, mult, opp, Re, Im, norm-squared, scale), a
      reorder battery of parametrized algebra faces (association,
      commutation, units, zeros, opposite, distribution,
      middle-swaps), and a bounded automation tactic [cx_eq] closing
      Cx algebra goals by congruence recursion with reorder and
      transitivity search.  The shim exists because the Cx equality
      is Set-sorted while the stdlib setoid machinery
      (Equivalence/Proper) is Prop-sorted and cannot carry it
      (verified: "Cannot enforce Set <= Prop"); this mirrors the
      tree's S07 RealSetoid Class pattern at Set level.
    Dependencies.  Stdlib [Arith.Arith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import),
      [S02_CauchyComplete], [CxRealPairCore], and
      [CxRealPairExpLog] of this development.
    References.  [QeqT]/[QltT] family design language (S01/S02
      Set-sorted relation carriers); design language alignment only,
      zero transplant.
    Constructivity.  Every named construction is carried by [Set]; the
      shim adds no statements of its own beyond the supply faces
      below, all Set-carried; no new Prop statements; every proof
      closes under the global context; [coqchk] reports zero assumed
      constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_c_eq_shim.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98
      -AllowG3 -GearForce 0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ==== Section 1. The relation face ==== *)

(* The relation itself is c_eq (re-exported under the slice's name). *)
Definition cxrel (x y : Cx) : Set := c_eq x y.

Lemma cxrel_refl : forall x : Cx, cxrel x x.
Proof. intros x. apply c_eq_refl. Qed.

Lemma cxrel_sym : forall x y : Cx, cxrel x y -> cxrel y x.
Proof. intros x y Hxy. apply (c_eq_sym x y Hxy). Qed.

Lemma cxrel_trans : forall x y z : Cx, cxrel x y -> cxrel y z -> cxrel x z.
Proof. intros x y z Hxy Hyz. apply (c_eq_trans x y z Hxy Hyz). Qed.

(* ==== Section 2. Substitutivity supply faces ==== *)

Lemma cxrel_plus : forall a1 a2 b1 b2 : Cx,
  cxrel a1 a2 -> cxrel b1 b2 -> cxrel (c_plus a1 b1) (c_plus a2 b2).
Proof. intros a1 a2 b1 b2 Ha Hb. apply (c_plus_congr a1 a2 b1 b2 Ha Hb). Qed.

Lemma cxrel_mult : forall a1 a2 b1 b2 : Cx,
  cxrel a1 a2 -> cxrel b1 b2 -> cxrel (c_mult a1 b1) (c_mult a2 b2).
Proof. intros a1 a2 b1 b2 Ha Hb. apply (c_mult_congr a1 a2 b1 b2 Ha Hb). Qed.

Lemma cxrel_opp : forall a b : Cx, cxrel a b -> cxrel (c_opp a) (c_opp b).
Proof. intros a b Hab. apply (c_opp_congr a b Hab). Qed.

Lemma cxrel_Re : forall a b : Cx,
  cxrel a b -> real_eq (cRe a) (cRe b).
Proof. intros a b Hab. unfold c_eq in Hab. destruct Hab as [Hr Hi]. exact Hr. Qed.

Lemma cxrel_Im : forall a b : Cx,
  cxrel a b -> real_eq (cIm a) (cIm b).
Proof. intros a b Hab. unfold c_eq in Hab. destruct Hab as [Hr Hi]. exact Hi. Qed.

Lemma cxrel_norm_sq : forall a b : Cx,
  cxrel a b -> real_eq (c_norm_sq a) (c_norm_sq b).
Proof.
  intros a b Hab.
  pose proof (cxrel_Re a b Hab) as Hr.
  pose proof (cxrel_Im a b Hab) as Hi.
  unfold c_norm_sq.
  apply RealSetoid.real_eq_plus_compat; apply RealSetoid.real_eq_mult_compat; assumption.
Qed.

Lemma cxrel_scale : forall u v : Real, real_eq u v ->
  forall a b : Cx, cxrel a b -> cxrel (c_scale u a) (c_scale v b).
Proof.
  intros u v Huv a b Hab.
  pose proof (cxrel_Re a b Hab) as Hr.
  pose proof (cxrel_Im a b Hab) as Hi.
  unfold c_scale, c_eq.
  split.
  - unfold cRe.
    apply RealSetoid.real_eq_mult_compat; [ exact Huv | exact Hr ].
  - unfold cIm.
    apply RealSetoid.real_eq_mult_compat; [ exact Huv | exact Hi ].
Qed.

(* ==== Section 3. The reorder battery (explicit supply faces) ==== *)

Lemma cx_plus_assoc_l : forall x y z : Cx,
  cxrel (c_plus x (c_plus y z)) (c_plus (c_plus x y) z).
Proof. intros x y z. apply c_plus_assoc. Qed.

Lemma cx_plus_assoc_r : forall x y z : Cx,
  cxrel (c_plus (c_plus x y) z) (c_plus x (c_plus y z)).
Proof. intros x y z. apply c_eq_sym. apply c_plus_assoc. Qed.

Lemma cx_plus_comm : forall x y : Cx,
  cxrel (c_plus x y) (c_plus y x).
Proof. intros x y. apply c_plus_comm. Qed.

Lemma cx_plus_zero_l : forall x : Cx, cxrel (c_plus c_zero x) x.
Proof. intros x. apply c_plus_zero. Qed.

Lemma cx_plus_zero_r : forall x : Cx, cxrel (c_plus x c_zero) x.
Proof.
  intros x. apply (c_eq_trans _ (c_plus c_zero x)).
  - apply (c_plus_comm x c_zero).
  - apply c_plus_zero.
Qed.

Lemma cx_plus_opp_r : forall x : Cx, cxrel (c_plus x (c_opp x)) c_zero.
Proof. intros x. apply c_plus_opp. Qed.

Lemma cx_mult_assoc_l : forall x y z : Cx,
  cxrel (c_mult x (c_mult y z)) (c_mult (c_mult x y) z).
Proof. intros x y z. apply c_mult_assoc. Qed.

Lemma cx_mult_assoc_r : forall x y z : Cx,
  cxrel (c_mult (c_mult x y) z) (c_mult x (c_mult y z)).
Proof. intros x y z. apply c_eq_sym. apply c_mult_assoc. Qed.

Lemma cx_mult_comm : forall x y : Cx,
  cxrel (c_mult x y) (c_mult y x).
Proof. intros x y. apply c_mult_comm. Qed.

Lemma cx_mult_one_l : forall x : Cx, cxrel (c_mult c_one x) x.
Proof. intros x. apply c_mult_one. Qed.

Lemma cx_mult_one_r : forall x : Cx, cxrel (c_mult x c_one) x.
Proof.
  intros x. apply (c_eq_trans _ (c_mult c_one x)).
  - apply (c_mult_comm x c_one).
  - apply c_mult_one.
Qed.

Lemma cx_mult_zero_l : forall x : Cx, cxrel (c_mult c_zero x) c_zero.
Proof. intros x. apply c_mult_zero. Qed.

Lemma cx_mult_zero_r : forall x : Cx, cxrel (c_mult x c_zero) c_zero.
Proof.
  intros x. apply (c_eq_trans _ (c_mult c_zero x)).
  - apply (c_mult_comm x c_zero).
  - apply c_mult_zero.
Qed.

Lemma cx_distrib_l : forall x y z : Cx,
  cxrel (c_mult x (c_plus y z)) (c_plus (c_mult x y) (c_mult x z)).
Proof. intros x y z. apply c_distrib. Qed.

Lemma cx_distrib_r : forall x y z : Cx,
  cxrel (c_mult (c_plus y z) x) (c_plus (c_mult y x) (c_mult z x)).
Proof.
  intros x y z.
  apply (c_eq_trans _ (c_mult x (c_plus y z))).
  - apply c_mult_comm.
  - apply (c_eq_trans _ (c_plus (c_mult x y) (c_mult x z))).
    + apply c_distrib.
    + apply c_plus_congr; apply c_mult_comm.
Qed.

Lemma cx_swap_inner : forall x y z : Cx,
  cxrel (c_plus x (c_plus y z)) (c_plus y (c_plus x z)).
Proof.
  intros x y z.
  apply (c_eq_trans _ (c_plus (c_plus x y) z)).
  - apply c_plus_assoc.
  - apply (c_eq_trans _ (c_plus (c_plus y x) z)).
    + apply c_plus_congr; [ apply c_plus_comm | apply c_eq_refl ].
    + apply c_eq_sym. apply (c_plus_assoc y x z).
Qed.

Lemma cx_swap_outer : forall x y z : Cx,
  cxrel (c_plus (c_plus x y) z) (c_plus y (c_plus x z)).
Proof.
  intros x y z.
  apply (c_eq_trans _ (c_plus x (c_plus y z))).
  - apply c_eq_sym. apply c_plus_assoc.
  - apply (cx_swap_inner x y z).
Qed.

(* ==== Section 4. The bounded automation tactic ==== *)

(* cx_eq_rec n closes Cx algebra goals by congruence recursion with
   reorder and transitivity search, bounded by depth n. *)
Ltac cx_eq_rec n :=
  match n with
  | O => first [ apply c_eq_refl | assumption ]
  | S ?n' =>
      first
        [ apply c_eq_refl
        | assumption
        | apply c_plus_congr; [ cx_eq_rec n' | cx_eq_rec n' ]
        | apply c_mult_congr; [ cx_eq_rec n' | cx_eq_rec n' ]
        | apply c_opp_congr; cx_eq_rec n'
        | eapply c_eq_trans; [ cx_eq_rec n' | cx_eq_rec n' ]
        | apply c_plus_assoc; cx_eq_rec n'
        | apply c_eq_sym; (apply c_plus_assoc; cx_eq_rec n')
        | apply c_plus_comm; cx_eq_rec n'
        | apply c_eq_sym; (apply c_plus_comm; cx_eq_rec n')
        | apply (cx_swap_inner); cx_eq_rec n'
        | apply (cx_swap_outer); cx_eq_rec n'
        | apply c_mult_assoc; cx_eq_rec n'
        | apply c_eq_sym; (apply c_mult_assoc; cx_eq_rec n')
        | apply c_mult_comm; cx_eq_rec n'
        | apply c_eq_sym; (apply c_mult_comm; cx_eq_rec n')
        | apply c_distrib; cx_eq_rec n'
        | apply c_eq_sym; (apply c_distrib; cx_eq_rec n') ]
  end.

(* The entry tactic: depth 4 suffices for the segment's algebra steps. *)
Ltac cx_eq := cx_eq_rec 4.

(* ==== Section 5. Supply-face audit tail ==== *)

(* Named-item census of this slice:
   1 Definition (cxrel) + 27 Lemma supply faces + 2 Ltac automations;
   zero statements beyond them, zero vm_compute, zero assumed constants. *)
