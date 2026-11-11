(* ConstructiveWorld-Main - leaf b of the three-cosine racing engine: the Real assistants and the relax-order kit. *)

(** * GaC3_Z03_NonzeroLine_b: leaf b of node C3-Z03.
    Mission.  Leaf b of the three-cosine racing engine (node C3-Z03): the
    fixed term carriers [z03npos] (the canonical positivity witness of the
    embedded naturals, the C2.02 leaf face, fixed once as the premise
    argument of the Z01 carriers), [z03_lnreal], and [z03_eterm] /
    [z03_coterm] (exp(-sg * ln n) and cos(-t * ln n)); plus the Real-level
    assistant kit [z03_le_mult_l], [z03_cos_peq], [z03_exp_peq], and the
    relax-order kit on [real_ge_relax] (the asymptotic nonnegativity order,
    the Z02 precedent on the equality-versus-positivity obstruction):
    [z03_eq_ge0relax], [z03_relax0_plus], [z03_wy_relax], [z03_lt_add_r],
    [z03_lt_eq_r], [z03_eq_relax_sym], [z03_relax_lt_false].
    Dependencies.  Leaf a [GaC3_Z03_NonzeroLine_a] ([qeq_lt_r],
    [qeq_minus_r0], [qself_le_abs], [qabs_lb],
    [z03_sc_cos_partial_congr]), [S01_BaseRing] ([NatLe], selective
    import), [S02_CauchyComplete] ([QltT] family), [S07_RealSetoidExpLog]
    ([real_ge_relax] family), [S10_KVQuantTrig], [S03_QExp],
    [CxRealPairCore], [GaC2_Iface_DS], [GaC3_Z02_ThreeCosine]; Stdlib
    [QArith] (with [Qring]), [Setoid], [Morphisms], [Arith], [Lia].
    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]
    :136-163; drafts_C3.md C3-Z03 (the racing skeleton, the explicit-radius
    obligation); cards_C3 C3-Z03.
    Constructivity.  Set-carried statements; zero assumed constants, zero
    abandoned proofs, zero classical choice; Print Assumptions reads Closed
    under the global context.
    Build.  coqc -native-compiler no -q -Q . "" -Q <boot_src> "" GaC3_Z03_NonzeroLine_b.v (work directory, dependency-closure build). *)

Require S01_BaseRing.
(* Selective import (the S01 state-space field S shadows the nat          *)
(* constructor under a full import; only the Set-sorted nat bound face is *)
(* consumed). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z03_NonzeroLine_a.
Require Import GaC3_Z02_ThreeCosine.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* The canonical positivity witness of the embedded naturals (the C2.02  *)
(* leaf face), fixed once as the premise argument of the Z01 carriers.   *)
Definition z03npos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n) :=
  nat_real_pos.

(* The natural logarithm on the embedded naturals. *)
Definition z03_lnreal (n : nat) (Hn : NatLe 1 n) : Real :=
  real_log (nat_real n) (z03npos n Hn).

(* Left multiplication by a positive real preserves real_le. *)
Lemma z03_le_mult_l : forall a b c : Real,
  real_lt real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  exact (RealSetoid.real_le_compat (real_mult a c) (real_mult c a)
           (real_mult b c) (real_mult c b)
           (real_mult_comm a c) (real_mult_comm b c)
           (real_le_mult_compat a b c Hc Hab)).
Qed.

(* Pointwise-equal arguments give equal cosines (the construction      *)
(* samples the argument approximation directly, real_cos_proj). *)
Lemma z03_cos_peq : forall a b : Real,
  (forall k : nat, projT1 a k == projT1 b k) ->
  real_eq (cauchy_real_cos a) (cauchy_real_cos b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro k.
  rewrite (real_cos_proj a k), (real_cos_proj b k).
  assert (Hcc : Qeq (cos_partial k (projT1 a k)) (cos_partial k (projT1 b k)))
    by (apply (z03_sc_cos_partial_congr k); exact (H k)).
  rewrite Hcc. ring.
Qed.

(* Pointwise-equal arguments give equal exponentials. *)
Lemma z03_exp_peq : forall a b : Real,
  (forall k : nat, projT1 a k == projT1 b k) ->
  real_eq (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b H. apply cauchy_real_exp_wd.
  apply real_eq_of_zero_diff. intro k. rewrite (H k). ring.
Qed.

(* The canonical exponential and cosine factors on the embedded         *)
(* naturals: exp(-sg * ln n) and cos(-t * ln n). *)
Definition z03_eterm (n : nat) (Hn : NatLe 1 n) (sg : Real) : Real :=
  cauchy_real_exp (real_mult (real_opp sg) (z03_lnreal n Hn)).

Definition z03_coterm (n : nat) (Hn : NatLe 1 n) (t : Real) : Real :=
  cauchy_real_cos (real_mult (real_opp t) (z03_lnreal n Hn)).

(* ===================================================================== *)
(* Part 0b. The relax-order kit (the asymptotic nonnegativity faces).    *)
(* ===================================================================== *)

(* A real equal to zero is asymptotically nonnegative. *)
Lemma z03_eq_ge0relax : forall X : Real,
  real_eq X real_zero -> real_ge_relax X real_zero.
Proof.
  intros X Heq eps Heps. destruct (Heq eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n (NatLe_lift N n Hn)).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (projT1 real_zero n - projT1 X n)
           (Qabs (projT1 X n - projT1 real_zero n)) eps).
  - assert (Hpm : Qeq (projT1 real_zero n - projT1 X n)
                    (- (projT1 X n - projT1 real_zero n))) by ring.
    exact (qeq_le_l (projT1 real_zero n - projT1 X n)
             (- (projT1 X n - projT1 real_zero n))
             (Qabs (projT1 X n - projT1 real_zero n)) Hpm
             (qopp_le_abs (projT1 X n - projT1 real_zero n))).
  - exact (QltT_to_Qlt _ _ HN).
Qed.

(* The asymptotic nonnegativity face is closed under addition. *)
Lemma z03_relax0_plus : forall X Y : Real,
  real_ge_relax X real_zero -> real_ge_relax Y real_zero ->
  real_ge_relax (real_plus X Y) real_zero.
Proof.
  intros X Y HX HY eps Heps.
  assert (Hh : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  destruct (HX (eps / 2)%Q Hh) as [N1 HN1].
  destruct (HY (eps / 2)%Q Hh) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  assert (H1 : QltT (projT1 real_zero n - projT1 X n) (eps / 2))
    by (apply HN1; lia).
  assert (H2 : QltT (projT1 real_zero n - projT1 Y n) (eps / 2))
    by (apply HN2; lia).
  apply Qlt_to_QltT.
  assert (Hexp : (projT1 real_zero n - projT1 (real_plus X Y) n)%Q
                 == ((projT1 real_zero n - projT1 X n)
                     + (projT1 real_zero n - projT1 Y n))%Q).
  { rewrite (real_plus_proj X Y n).
    rewrite (real_zero_pt n). ring. }
  apply (Qlt_le_trans (projT1 real_zero n - projT1 (real_plus X Y) n)
           (eps / 2 + eps / 2)%Q eps).
  - apply (qeq_lt_l _ (projT1 real_zero n - projT1 X n
                       + (projT1 real_zero n - projT1 Y n))
           (eps / 2 + eps / 2)%Q Hexp).
    apply Qplus_lt_compat; apply QltT_to_Qlt; assumption.
  - assert (Hf : Qeq (eps / 2 + eps / 2)%Q eps) by field.
    exact (qeq_le_l _ eps eps Hf (Qle_refl eps)).
Qed.

(* A nonnegative real weight times a pointwise-nonnegative real is      *)
(* asymptotically nonnegative: the strict case carries the pointwise    *)
(* sign, the zero case transfers through the equality. *)
Lemma z03_wy_relax : forall W Y : Real,
  real_le real_zero W -> (forall k : nat, Qle 0 (projT1 Y k)) ->
  real_ge_relax (real_mult W Y) real_zero.
Proof.
  intros W Y HW HY. unfold real_le in HW. destruct HW as [Hlt | Heq].
  - destruct Hlt as [e0 [He0 [N HN]]].
    apply (real_ge_relax_of_pointwise (real_mult W Y) real_zero N).
    intros n Hn. specialize (HN n (NatLe_lift N n Hn)).
    rewrite real_mult_proj.
    assert (Hw2 : Qlt 0 (projT1 W n)).
    { apply QltT_to_Qlt in He0. apply QltT_to_Qlt in HN.
      assert (Hm2 : Qlt e0 (projT1 W n)).
      { apply (qeq_lt_r e0 (projT1 W n - projT1 real_zero n) (projT1 W n)).
        - exact (qeq_minus_r0 (projT1 W n) (projT1 real_zero n)
                   (real_zero_pt n)).
        - exact HN. }
      exact (Qlt_trans 0 e0 (projT1 W n) He0 Hm2). }
    apply Qmult_le_0_compat.
    + apply Qlt_le_weak. exact Hw2.
    + apply HY.
  - apply z03_eq_ge0relax.
    apply (real_eq_trans (real_mult W Y) (real_mult real_zero Y) real_zero).
    + apply RealSetoid.real_eq_mult_compat;
        [exact (real_eq_sym real_zero W Heq) | apply real_eq_refl].
    + exact (real_eq_trans (real_mult real_zero Y) (real_mult Y real_zero)
               real_zero (real_mult_comm real_zero Y) (real_mult_zero Y)).
Qed.

(* The strict order shifts along a common summand. *)
Lemma z03_lt_add_r : forall a b c : Real,
  real_lt a b -> real_lt (real_plus a c) (real_plus b c).
Proof.
  intros a b c Hlt. destruct Hlt as [e0 [He0 [N HN]]].
  exists e0. split; [exact He0 |].
  exists N. intros n Hn.
  assert (Hr : (projT1 (real_plus b c) n - projT1 (real_plus a c) n)%Q
               == (projT1 b n - projT1 a n)%Q).
  { rewrite (real_plus_proj b c n), (real_plus_proj a c n). ring. }
  apply Qlt_to_QltT.
  apply (qeq_lt_r e0 _ _ (Qeq_sym _ _ Hr)).
  apply QltT_to_Qlt. apply (HN n Hn).
Qed.

(* The strict order transfers along an equality on the larger side. *)
Lemma z03_lt_eq_r : forall x y z : Real,
  real_lt x y -> real_eq y z -> real_lt x z.
Proof.
  intros x y z Hlt Heq. destruct Hlt as [e0 [He0 [N HN]]].
  assert (Hh : QltT 0 (e0 / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 e0 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply QltT_to_Qlt. exact He0. }
  destruct (Heq (e0 / 2)%Q Hh) as [N1 HN1].
  exists (e0 / 2)%Q. split; [exact Hh |].
  exists (Nat.max N N1). intros n Hn.
  assert (Hlt' : QltT e0 (projT1 y n - projT1 x n))
    by (apply HN; apply NatLe_lift;
        apply Nat.le_trans with (Nat.max N N1);
        [ apply Nat.le_max_l | apply NatLe_drop; exact Hn ]).
  assert (Heq' : QltT (Qabs (projT1 y n - projT1 z n)) (e0 / 2))
    by (apply HN1; apply NatLe_lift;
        apply Nat.le_trans with (Nat.max N N1);
        [ apply Nat.le_max_r | apply NatLe_drop; exact Hn ]).
  apply Qlt_to_QltT.
  assert (Hz2 : Qlt (projT1 y n - projT1 z n) (e0 / 2)).
  { apply (Qle_lt_trans (projT1 y n - projT1 z n)
             (Qabs (projT1 y n - projT1 z n)) (e0 / 2)).
    - exact (qself_le_abs (projT1 y n - projT1 z n)).
    - apply QltT_to_Qlt. exact Heq'. }
  assert (Hzylow : Qlt (- (e0 / 2)) (projT1 z n - projT1 y n)).
  { apply (qabs_lb (projT1 z n - projT1 y n) (e0 / 2)).
    - apply QltT_to_Qlt. exact Hh.
    - apply (qeq_lt_l (Qabs (projT1 z n - projT1 y n))
               (Qabs (projT1 y n - projT1 z n)) (e0 / 2)).
      + apply (Qeq_trans (Qabs (projT1 z n - projT1 y n))
                 (Qabs (- (projT1 y n - projT1 z n)))
                 (Qabs (projT1 y n - projT1 z n))).
        * apply Qabs_wd. ring.
        * apply Qabs_opp.
      + apply QltT_to_Qlt. exact Heq'. }
  assert (Hsum : Qlt (e0 + (- (e0 / 2)))
                   ((projT1 y n - projT1 x n)
                    + (projT1 z n - projT1 y n))).
  { apply Qplus_lt_compat.
    - apply QltT_to_Qlt. exact Hlt'.
    - exact Hzylow. }
  assert (Hmid : Qlt (e0 / 2)
                   ((projT1 y n - projT1 x n)
                    + (projT1 z n - projT1 y n))).
  { assert (Hprem : Qeq (e0 + (- (e0 / 2))) (e0 / 2)) by field.
    apply (qeq_lt_l (e0 / 2) _ _ (Qeq_sym _ _ Hprem) Hsum). }
  assert (Hkey : Qeq ((projT1 y n - projT1 x n) + (projT1 z n - projT1 y n))
                   (projT1 z n - projT1 x n)) by ring.
  exact (qeq_lt_r (e0 / 2) _ _ Hkey Hmid).
Qed.

(* The equality-transfer mirror of the Z02 relax transfer. *)
Lemma z03_eq_relax_sym : forall a b : Real,
  real_eq a b -> real_ge_relax a real_zero -> real_ge_relax b real_zero.
Proof.
  intros a b Hab Ha.
  exact (GaC3_Z02_eq_relax_transfer b a (real_eq_sym a b Hab) Ha).
Qed.

(* The asymptotic nonnegativity face is jointly incompatible with a     *)
(* strictly negative position carrying a positive margin. *)
Lemma z03_relax_lt_false : forall X : Real,
  real_ge_relax X real_zero -> real_lt X real_zero -> False.
Proof.
  intros X Hr Hl. destruct Hl as [e0 [He0 [N2 HN2]]].
  destruct (Hr e0 He0) as [N1 HN1].
  specialize (HN1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)).
  specialize (HN2 (Nat.max N1 N2)
    (NatLe_lift N2 (Nat.max N1 N2) (Nat.le_max_r N1 N2))).
  apply QltT_to_Qlt in HN1. apply QltT_to_Qlt in HN2.
  exact (Qlt_irrefl _ (Qlt_trans _ _ _ HN2 HN1)).
Qed.
