(* ConstructiveWorld-Main - the carrier stem of the Real
   instantiation of the Banach-algebra pre-class. *)

(** * UpReqBanachInstReal_a: carrier face and bridges (stem one of four).

    Mission.  Conserved statement-for-statement from the boxed piece
    UpReqBanachInstReal: the head evaluator, the constant-real
    constructor, the germ equivalence, the norm, the first-term
    operations and head-reduction lemmas, the Q-layer work pieces,
    the Id bridge, the Z-core division lemma, the Qabs-norm
    invariance, the two wall discharges, the [bnorm_opp] field
    discharge, and the frozen primitive-pinning wall.  Consumed by
    the sibling stems _b/_c/_d.

    Dependencies.  Stdlib [QArith], [Qabs], [ZArith], [Lia];
    [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
    [UpReqBanachExp_dep], [UpReqBanachInstB_dep],
    [UpReqBanachInst_dep] (gate-face dep copies of the boxed upstream).

    References.  The Banach-algebra instantiation line of the
    constructive development; the boxed original piece.

    Constructivity.  All carriers [Set]; conclusions in
    [Id]/[QeqT]/[QleT'] forms; zero assumed constants; every proof
    closes by Qed.

    Build.  [coqc -q -native-compiler no] under the acceptance
    build faces, [cpu_guard v3] wrapped. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp_dep.
Require Import UpReqBanachInstB_dep.
Require Import UpReqBanachInst_dep.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0: carrier-face tools (head evaluation / canonical constant real / germ equivalence / norm)      *)
(* ============================================================ *)

(* First-term evaluation: Real -> Q (definitional level) *)
Definition bxra_head (x : Real) : Q := projT1 x 0%nat.

(* Constant-real constructor (S02 real_const is transparent: the head reduces definitionally) *)
Definition bxra_cR (q : Q) : Real := real_const q.

Lemma bxra_head_cR : forall q : Q, Id (bxra_head (bxra_cR q)) q.
Proof.
  intro q. unfold bxra_head, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

(* Germ equivalence: the canonical germ *)
Definition bxra_bae_germ (a b : Real) : Set :=
  Id (bxib_qnorm (bxra_head a)) (bxib_qnorm (bxra_head b)).

(* Norm: Qabs after qnorm after head (the bxib_qnorm prescription shape) *)
Definition bxra_bnorm_f (x : Real) : Q := Qabs (bxib_qnorm (bxra_head x)).

(* Operation face: first-term rational operation then canonicalization, packaged as a constant real *)
Definition bxra_bplus_f (x y : Real) : Real :=
  bxra_cR (bxib_qnorm (bxra_head x + bxra_head y)%Q).
Definition bxra_bmult_f (x y : Real) : Real :=
  bxra_cR (bxib_qnorm (bxra_head x * bxra_head y)%Q).
Definition bxra_bopp_f (x : Real) : Real :=
  bxra_cR (bxib_qnorm (- bxra_head x)%Q).
Definition bxra_bzero_f : Real := bxra_cR 0%Q.
Definition bxra_bone_f : Real := bxra_cR 1%Q.
Definition bxra_bcoef_f (q : Q) : Real := bxra_cR (bxib_qnorm q).

(* head-face reduction (operation output positions consumed definitionally) *)
Lemma bxra_head_bplus : forall x y : Real,
  Id (bxra_head (bxra_bplus_f x y)) (bxib_qnorm (bxra_head x + bxra_head y)%Q).
Proof.
  intros x y. unfold bxra_head, bxra_bplus_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

Lemma bxra_head_bmult : forall x y : Real,
  Id (bxra_head (bxra_bmult_f x y)) (bxib_qnorm (bxra_head x * bxra_head y)%Q).
Proof.
  intros x y. unfold bxra_head, bxra_bmult_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

Lemma bxra_head_bopp : forall x : Real,
  Id (bxra_head (bxra_bopp_f x)) (bxib_qnorm (- bxra_head x)%Q).
Proof.
  intro x. unfold bxra_head, bxra_bopp_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

(* ============================================================ *)
(* S1: Q-layer work pieces (QeqT congruence / Qabs helpers / nonnegativity / transitivity bridge)      *)
(* ============================================================ *)

(* QeqT multiplication congruence (cong machine patch) *)
Lemma bxra_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (a * c)%Q (b * d)%Q.
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq a b Hab), (qeqT_imp_qeq c d Hcd).
  apply Qeq_refl.
Qed.

(* |xy| = |x||y| (the stdlib lacks the Qabs_mult name, self-built) *)
Lemma bxra_qabs_mult : forall x y : Q, Qabs (x * y)%Q == Qabs x * Qabs y%Q.
Proof.
  intros [n d] [m e].
  unfold Qabs, Qmult, Qeq; simpl.
  rewrite Z.abs_mul. ring.
Qed.

(* Qabs nonnegativity (a QleT' leaf) *)
Lemma bxra_qleT_zero_abs_qn : forall x : Q, QleT' 0 (Qabs (bxib_qnorm x)).
Proof.
  intros [n d]. destruct n as [|p|p];
    apply Qle_to_QleT'; unfold Qle, Qabs, bxib_qnorm; cbn; lia.
Qed.

Lemma bxra_qltT_wd : forall a b c : Q, QeqT a b -> QltT a c -> QltT b c.
Proof.
  intros a b c Hab H.
  apply (qleT'_ltT_ltT b a c).
  - apply Qle_to_QleT'. apply qeq_imp_qle.
    apply qeqT_imp_qeq. apply bxib_qeqT_sym. exact Hab.
  - exact H.
Qed.

(* ============================================================ *)
(* ============================================================ *)

(* Qabs-norm invariance (Id form). Attack route as proven: pure iota falls short (the Z.gcd unfolding of the ggcd *)
(* machine stalls on the symbolic participation), the Z-layer lemma chain closes it: Z.gcd_opp_l + bxib_div_exact *)
(* + Z.abs_opp; the eq bridge returns to Id.                                        *)
Lemma bxra_id_of_eq : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y H.
  exact (match H in (_ = t) return Id x t with
         | eq_refl => id_refl
         end).
Qed.

(* Z core: under exact divisibility the absolute value of the negated quotient is invariant (an algebraic route for div_opp, zero mod conditions) *)
Lemma bxra_zabs_div_opp : forall p g : Z,
  g <> 0%Z -> Z.divide g p -> Z.divide g (Z.opp p) ->
  Z.abs (Z.div (Z.opp p) g) = Z.abs (Z.div p g)%Z.
Proof.
  intros p g Hg0 Hp Hn.
  assert (Hdp : (p = Z.mul g (Z.div p g))%Z)
    by (eapply bxib_div_exact; assumption).
  assert (Hdn : (Z.opp p = Z.mul g (Z.div (Z.opp p) g))%Z)
    by (eapply bxib_div_exact; assumption).
  assert (Hq : (Z.div (Z.opp p) g = Z.opp (Z.div p g))%Z).
  { apply (Z.mul_reg_l (Z.div (Z.opp p) g) (Z.opp (Z.div p g)) g Hg0).
    rewrite <- Hdn. replace p with (Z.mul g (Z.div p g)) at 1
      by (symmetry; exact Hdp).
    ring. }
  rewrite Hq, Z.abs_opp. reflexivity.
Qed.

Lemma bxra_qabs_opp_norm : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof.
  intro u. apply bxra_id_of_eq.
  destruct u as [n d]. destruct n as [|p|p].
  - reflexivity.
  - change (Qopp (Qmake (Zpos p) d)) with (Qmake (Zneg p) d).
    rewrite bxib_qnorm_neg_shape, bxib_qnorm_pos_shape.
    unfold Qabs. cbn [Qnum Qden].
    change (Zneg p) with (- (Zpos p))%Z.
    rewrite (Z.gcd_opp_l (Zpos p) (Z.pos d)).
    f_equal.
    assert (Hg0 : Z.gcd (Zpos p) (Z.pos d) <> 0%Z).
    { intro H0.
      destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
      rewrite H0, Z.mul_0_r in Hk. discriminate Hk. }
    apply bxra_zabs_div_opp;
      [ exact Hg0 | exact (Z.gcd_divide_l (Zpos p) (Z.pos d)) | ].
    destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
    exists (-k)%Z. rewrite Hk at 1. ring.
  - change (Qopp (Qmake (Zneg p) d)) with (Qmake (Zpos p) d).
    rewrite bxib_qnorm_pos_shape, bxib_qnorm_neg_shape.
    unfold Qabs. cbn [Qnum Qden].
    change (Zneg p) with (- (Zpos p))%Z.
    rewrite (Z.gcd_opp_l (Zpos p) (Z.pos d)).
    f_equal.
    assert (Hg0 : Z.gcd (Zpos p) (Z.pos d) <> 0%Z).
    { intro H0.
      destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
      rewrite H0, Z.mul_0_r in Hk. discriminate Hk. }
    symmetry. apply bxra_zabs_div_opp;
      [ exact Hg0 | exact (Z.gcd_divide_l (Zpos p) (Z.pos d)) | ].
    destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
    exists (-k)%Z. rewrite Hk at 1. ring.
Qed.

(* Wall-one discharge (class QeqT form): norm well-definedness of the germ equivalence (via an Id relay) *)
Lemma bxra_norm_wd : forall a b : Real,
  bxra_bae_germ a b -> Id (bxra_bnorm_f a) (bxra_bnorm_f b).
Proof.
  intros a b Hab. unfold bxra_bnorm_f.
  apply (id_cong Qabs). exact Hab.
Qed.

Lemma bxra_norm_wd_qeqt : forall a b : Real,
  bxra_bae_germ a b -> QeqT (bxra_bnorm_f a) (bxra_bnorm_f b).
Proof. intros a b Hab. apply bxib_qeqT_of_id. apply bxra_norm_wd. exact Hab. Qed.

(* Wall-two discharge (class QeqT form): pinning the scalar face to the primitive Qabs q *)
Lemma bxra_norm_coef_qeqt : forall q : Q,
  QeqT (bxra_bnorm_f (bxra_bcoef_f q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  unfold bxra_bnorm_f, bxra_bcoef_f.
  rewrite (bxra_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  apply (Qeq_trans _ (Qabs (bxib_qnorm q))).
  - apply Qabs_wd. apply Qeq_refl.
  - apply (Qeq_trans _ (Qabs q)).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply Qeq_refl.
Qed.

(* bnorm_opp field discharge (class Id form) = the use site of new item (1) *)
Lemma bxra_f_norm_opp : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof.
  intro a.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (- bxra_head a)%Q)))
             (Qabs (bxib_qnorm (bxra_head a)))).
  rewrite (bxib_qnorm_fix_id (- bxra_head a)%Q).
  apply bxra_qabs_opp_norm.
Qed.

(* Primitive pinning wall, frozen (honest note: the Id-form primitive Qabs pinning is unsatisfiable) *)
Lemma bxra_raw_pin_wall :
  Id (bxra_bnorm_f (bxra_bcoef_f (2#4)%Q)) (Qabs (2#4)%Q) ->
  Id (1#2)%Q (2#4)%Q.
Proof.
  intro H.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (2#4)%Q))) (Qabs (2#4)%Q)) in H.
  rewrite bxib_qnorm_fix_id in H.
  exact H.
Qed.
