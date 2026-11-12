(* ConstructiveWorld-Main - the algebra-field stem of the Real
   instantiation of the Banach-algebra pre-class. *)

(** * UpReqBanachInstReal_b: field discharge, group and distributivity
      faces (stem two of four).

    Mission.  Conserved statement-for-statement from the boxed piece
    UpReqBanachInstReal: the three equivalence laws, the additive
    group (assoc/comm/zero/opp), the multiplicative group
    (assoc/one_l/one_r), the two distributivity faces, the
    multiplicative zero face, and the well-definedness trio
    (plus/mult/opp).  Consumed by the sibling stems _c/_d.

    Dependencies.  Stdlib [QArith], [Qabs], [ZArith], [Lia];
    [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
    [UpReqBanachExp_dep], [UpReqBanachInstB_dep],
    [UpReqBanachInst_dep], sibling stem [UpReqBanachInstReal_a].

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
Require Import UpReqBanachInstReal_a.

(* ============================================================ *)
(* S3: field-discharge pieces (the 39 fields of the class, bit by bit)                        *)
(* ============================================================ *)

(* ---- the three equivalence laws ---- *)

Lemma bxra_f_refl : forall a : Real, bxra_bae_germ a a.
Proof. intro a. apply id_refl. Qed.

Lemma bxra_f_sym : forall a b : Real, bxra_bae_germ a b -> bxra_bae_germ b a.
Proof. intros a b H. apply id_sym. exact H. Qed.

Lemma bxra_f_trans : forall a b c : Real,
  bxra_bae_germ a b -> bxra_bae_germ b c -> bxra_bae_germ a c.
Proof. intros a b c H1 H2. apply (id_trans H1 H2). Qed.

(* ---- additive group (floor pieces) ---- *)

Lemma bxra_f_plus_assoc : forall a b c : Real,
  bxra_bae_germ (bxra_bplus_f a (bxra_bplus_f b c))
                (bxra_bplus_f (bxra_bplus_f a b) c).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a (bxra_bplus_f b c)).
  rewrite (bxra_head_bplus b c).
  rewrite (bxra_head_bplus (bxra_bplus_f a b) c).
  rewrite (bxra_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxib_qnorm (bxra_head b + bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a + bxra_head b)%Q + bxra_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a + (bxra_head b + bxra_head c))%Q).
  - apply bxib_qeqT_cong_plus; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a + bxra_head b + bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qplus_assoc.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxra_f_plus_comm : forall a b : Real,
  bxra_bae_germ (bxra_bplus_f a b) (bxra_bplus_f b a).
Proof.
  intros a b. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a b), (bxra_head_bplus b a).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head b + bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qplus_comm.
Qed.

Lemma bxra_f_plus_zero : forall a : Real,
  bxra_bae_germ (bxra_bplus_f a bxra_bzero_f) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a bxra_bzero_f).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a + 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (bxra_head a)).
  - apply Qplus_0_r.
  - apply Qeq_refl.
Qed.

Lemma bxra_f_plus_opp : forall a : Real,
  bxra_bae_germ (bxra_bplus_f a (bxra_bopp_f a)) bxra_bzero_f.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a (bxra_bopp_f a)).
  rewrite (bxra_head_bopp a).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxib_qnorm (- bxra_head a)%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a + (- bxra_head a))%Q).
  - apply bxib_qeqT_cong_plus;
      [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- multiplicative group ---- *)

Lemma bxra_f_mult_assoc : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f a (bxra_bmult_f b c))
                (bxra_bmult_f (bxra_bmult_f a b) c).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bmult_f b c)).
  rewrite (bxra_head_bmult b c).
  rewrite (bxra_head_bmult (bxra_bmult_f a b) c).
  rewrite (bxra_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm (bxra_head b * bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head b)%Q * bxra_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a * (bxra_head b * bxra_head c))%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head b * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply bxra_qeqT_cong_mult;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxra_f_mult_one_l : forall a : Real,
  bxra_bae_germ (bxra_bmult_f bxra_bone_f a) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult bxra_bone_f a).
  unfold bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (1%Q * bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxra_f_mult_one_r : forall a : Real,
  bxra_bae_germ (bxra_bmult_f a bxra_bone_f) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a bxra_bone_f).
  unfold bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a * 1%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

(* ---- distributivity ---- *)

Lemma bxra_f_distrib_l : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f a (bxra_bplus_f b c))
                (bxra_bplus_f (bxra_bmult_f a b) (bxra_bmult_f a c)).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bplus_f b c)).
  rewrite (bxra_head_bplus b c).
  rewrite (bxra_head_bplus (bxra_bmult_f a b) (bxra_bmult_f a c)).
  rewrite (bxra_head_bmult a b), (bxra_head_bmult a c).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm (bxra_head b + bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head b)%Q
                              + bxib_qnorm (bxra_head a * bxra_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a * (bxra_head b + bxra_head c))%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head b + bxra_head a * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxra_f_distrib_r : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f (bxra_bplus_f a b) c)
                (bxra_bplus_f (bxra_bmult_f a c) (bxra_bmult_f b c)).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult (bxra_bplus_f a b) c).
  rewrite (bxra_head_bplus a b).
  rewrite (bxra_head_bplus (bxra_bmult_f a c) (bxra_bmult_f b c)).
  rewrite (bxra_head_bmult a c), (bxra_head_bmult b c).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a + bxra_head b)%Q * bxra_head c)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head c)%Q
                              + bxib_qnorm (bxra_head b * bxra_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ ((bxra_head a + bxra_head b) * bxra_head c)%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qnorm_fix | apply bxib_qeqT_refl].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head c + bxra_head b * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxra_f_mult_zero : forall a : Real,
  bxra_bae_germ (bxra_bmult_f a bxra_bzero_f) bxra_bzero_f.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a bxra_bzero_f).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a * 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ---- the well-definedness trio ---- *)

Lemma bxra_f_plus_wd : forall a b c d : Real,
  bxra_bae_germ a c -> bxra_bae_germ b d ->
  bxra_bae_germ (bxra_bplus_f a b) (bxra_bplus_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a b), (bxra_head_bplus c d).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head c + bxra_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_mult_wd : forall a b c d : Real,
  bxra_bae_germ a c -> bxra_bae_germ b d ->
  bxra_bae_germ (bxra_bmult_f a b) (bxra_bmult_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a b), (bxra_head_bmult c d).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head c * bxra_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxra_qeqT_cong_mult.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_opp_wd : forall a b : Real,
  bxra_bae_germ a b -> bxra_bae_germ (bxra_bopp_f a) (bxra_bopp_f b).
Proof.
  intros a b Hab. unfold bxra_bae_germ.
  rewrite (bxra_head_bopp a), (bxra_head_bopp b).
  rewrite (bxib_qnorm_fix_id (- bxra_head a)%Q).
  rewrite (bxib_qnorm_fix_id (- bxra_head b)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_of_id. exact Hab.
    + apply bxib_qnorm_fix.
Qed.
