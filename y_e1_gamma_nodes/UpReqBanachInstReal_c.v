(* ConstructiveWorld-Main - the assembly stem of the Real
   instantiation of the Banach-algebra pre-class. *)

(** * UpReqBanachInstReal_c: scalar embedding, norm faces, and the
      concrete instance (stem three of four).

    Mission.  Conserved statement-for-statement from the boxed piece
    UpReqBanachInstReal: the scalar embedding faces (coef zero/one/
    mult/comm/plus/wd), the two W6a fields, the norm faces
    (zero/one/pos/plus/mult), the full-field class assembly
    [bxra_real_pre] (the first concrete [bxin_BanachAlgPre]
    instance in the development), and the three assembly smoke
    lemmas.  Consumed by the sibling stem _d.

    Dependencies.  Stdlib [QArith], [Qabs], [ZArith], [Lia];
    [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
    [UpReqBanachExp_dep], [UpReqBanachInstB_dep],
    [UpReqBanachInst_dep], sibling stems
    [UpReqBanachInstReal_a]/[UpReqBanachInstReal_b].

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
Require Import UpReqBanachInstReal_b.

(* ---- scalar embedding face ---- *)

Lemma bxra_f_coef_zero : bxra_bae_germ (bxra_bcoef_f 0%Q) bxra_bzero_f.
Proof.
  unfold bxra_bae_germ, bxra_bcoef_f, bxra_bzero_f.
  rewrite (bxra_head_cR (bxib_qnorm 0%Q)).
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id 0%Q).
  apply id_refl.
Qed.

Lemma bxra_f_coef_one : bxra_bae_germ (bxra_bcoef_f 1%Q) bxra_bone_f.
Proof.
  unfold bxra_bae_germ, bxra_bcoef_f, bxra_bone_f.
  rewrite (bxra_head_cR (bxib_qnorm 1%Q)).
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id 1%Q).
  apply id_refl.
Qed.

Lemma bxra_f_coef_mult : forall q r : Q,
  bxra_bae_germ (bxra_bcoef_f (q * r)%Q)
                (bxra_bmult_f (bxra_bcoef_f q) (bxra_bcoef_f r)).
Proof.
  intros q r. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult (bxra_bcoef_f q) (bxra_bcoef_f r)).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (q * r)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxib_qnorm r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym.
  apply bxra_qeqT_cong_mult; apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_coef_comm : forall (q : Q) (a : Real),
  bxra_bae_germ (bxra_bmult_f a (bxra_bcoef_f q))
                (bxra_bmult_f (bxra_bcoef_f q) a).
Proof.
  intros q a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bcoef_f q)).
  rewrite (bxra_head_bmult (bxra_bcoef_f q) a).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm q)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ---- the two W6a fields ---- *)

Lemma bxra_f_coef_plus : forall q r : Q,
  bxra_bae_germ (bxra_bplus_f (bxra_bcoef_f q) (bxra_bcoef_f r))
                (bxra_bcoef_f (q + r)%Q).
Proof.
  intros q r. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus (bxra_bcoef_f q) (bxra_bcoef_f r)).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_coef_wd : forall q r : Q,
  q == r -> bxra_bae_germ (bxra_bcoef_f q) (bxra_bcoef_f r).
Proof.
  intros q r Hqr. unfold bxra_bae_germ, bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ---- norm face ---- *)

Lemma bxra_f_norm_zero : Id (bxra_bnorm_f bxra_bzero_f) 0%Q.
Proof.
  unfold bxra_bnorm_f, bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  apply id_refl.
Qed.

Lemma bxra_f_norm_one : Id (bxra_bnorm_f bxra_bone_f) 1%Q.
Proof.
  unfold bxra_bnorm_f, bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  apply id_refl.
Qed.

Lemma bxra_f_norm_pos : forall a : Real, QleT' 0 (bxra_bnorm_f a).
Proof.
  intro a. unfold bxra_bnorm_f. apply bxra_qleT_zero_abs_qn.
Qed.

Lemma bxra_f_norm_plus : forall a b : Real,
  QleT' (bxra_bnorm_f (bxra_bplus_f a b))
        (bxra_bnorm_f a + bxra_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxra_bnorm_f.
  rewrite (bxra_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxra_head a + bxra_head b)%Q)).
  - apply qeq_imp_qle.
    apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - apply (Qle_trans _ (Qabs (bxra_head a) + Qabs (bxra_head b))%Q).
    + apply Qabs_triangle.
    + apply qeq_imp_qle.
      apply (@Qplus_comp (Qabs (bxra_head a)) (Qabs (bxib_qnorm (bxra_head a)))
           (Qeq_sym (Qabs (bxib_qnorm (bxra_head a))) (Qabs (bxra_head a))
                (Qabs_wd (bxib_qnorm (bxra_head a)) (bxra_head a)
                     (qeqT_imp_qeq (bxib_qnorm (bxra_head a)) (bxra_head a)
                          (bxib_qnorm_fix (bxra_head a)))))
           (Qabs (bxra_head b)) (Qabs (bxib_qnorm (bxra_head b)))
           (Qeq_sym (Qabs (bxib_qnorm (bxra_head b))) (Qabs (bxra_head b))
                (Qabs_wd (bxib_qnorm (bxra_head b)) (bxra_head b)
                     (qeqT_imp_qeq (bxib_qnorm (bxra_head b)) (bxra_head b)
                          (bxib_qnorm_fix (bxra_head b)))))).
Qed.

Lemma bxra_f_norm_mult : forall a b : Real,
  QleT' (bxra_bnorm_f (bxra_bmult_f a b))
        (bxra_bnorm_f a * bxra_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxra_bnorm_f.
  rewrite (bxra_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxra_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxra_head a) * Qabs (bxra_head b))%Q).
  - apply qeq_imp_qle.
    apply (Qeq_trans (Qabs (bxib_qnorm (bxra_head a * bxra_head b)%Q))
                     (Qabs (bxra_head a * bxra_head b)%Q)
                     (Qabs (bxra_head a) * Qabs (bxra_head b))%Q).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply bxra_qabs_mult.
  - apply qeq_imp_qle.
    apply (@Qmult_comp (Qabs (bxra_head a)) (Qabs (bxib_qnorm (bxra_head a)))
         (Qeq_sym (Qabs (bxib_qnorm (bxra_head a))) (Qabs (bxra_head a))
              (Qabs_wd (bxib_qnorm (bxra_head a)) (bxra_head a)
                   (qeqT_imp_qeq (bxib_qnorm (bxra_head a)) (bxra_head a)
                        (bxib_qnorm_fix (bxra_head a)))))
         (Qabs (bxra_head b)) (Qabs (bxib_qnorm (bxra_head b)))
         (Qeq_sym (Qabs (bxib_qnorm (bxra_head b))) (Qabs (bxra_head b))
              (Qabs_wd (bxib_qnorm (bxra_head b)) (bxra_head b)
                   (qeqT_imp_qeq (bxib_qnorm (bxra_head b)) (bxra_head b)
                        (bxib_qnorm_fix (bxra_head b)))))).
Qed.

(* ============================================================ *)
(* S4: full-field class assembly - the first concrete bxin_BanachAlgPre instance in the development          *)
(* ============================================================ *)

Instance bxra_real_pre : bxin_BanachAlgPre := {|
  bxin_BA := Real;
  bxin_bae := bxra_bae_germ;
  bxin_bae_refl := bxra_f_refl;
  bxin_bae_sym := bxra_f_sym;
  bxin_bae_trans := bxra_f_trans;
  bxin_bzero := bxra_bzero_f;
  bxin_bone := bxra_bone_f;
  bxin_bplus := bxra_bplus_f;
  bxin_bmult := bxra_bmult_f;
  bxin_bopp := bxra_bopp_f;
  bxin_bcoef := bxra_bcoef_f;
  bxin_bnorm := bxra_bnorm_f;
  bxin_bplus_assoc := bxra_f_plus_assoc;
  bxin_bplus_comm := bxra_f_plus_comm;
  bxin_bplus_zero := bxra_f_plus_zero;
  bxin_bplus_opp := bxra_f_plus_opp;
  bxin_bmult_assoc := bxra_f_mult_assoc;
  bxin_bmult_one_l := bxra_f_mult_one_l;
  bxin_bmult_one_r := bxra_f_mult_one_r;
  bxin_bdistrib_l := bxra_f_distrib_l;
  bxin_bdistrib_r := bxra_f_distrib_r;
  bxin_bmult_zero := bxra_f_mult_zero;
  bxin_bplus_wd := bxra_f_plus_wd;
  bxin_bmult_wd := bxra_f_mult_wd;
  bxin_bopp_wd := bxra_f_opp_wd;
  bxin_bnorm_wd := bxra_norm_wd_qeqt;
  bxin_bcoef_zero := bxra_f_coef_zero;
  bxin_bcoef_one := bxra_f_coef_one;
  bxin_bcoef_mult := bxra_f_coef_mult;
  bxin_bcoef_comm := bxra_f_coef_comm;
  bxin_bcoef_plus := bxra_f_coef_plus;
  bxin_bcoef_wd := bxra_f_coef_wd;
  bxin_bnorm_zero := bxra_f_norm_zero;
  bxin_bnorm_one := bxra_f_norm_one;
  bxin_bnorm_opp := bxra_f_norm_opp;
  bxin_bnorm_pos := bxra_f_norm_pos;
  bxin_bnorm_plus := bxra_f_norm_plus;
  bxin_bnorm_mult := bxra_f_norm_mult;
  bxin_bnorm_coef := bxra_norm_coef_qeqt;
|}.

(* Assembly smoke test: the class-projection face (a pointwise confirmation of instance nonemptiness 0 to 100) *)
Lemma bxra_inst_smoke_bone :
  @bxin_bae bxra_real_pre
    (@bxin_bcoef bxra_real_pre 1%Q)
    (@bxin_bone bxra_real_pre).
Proof.
  change (@bxin_bae bxra_real_pre
           (@bxin_bcoef bxra_real_pre 1%Q)
           (@bxin_bone bxra_real_pre))
    with (bxra_bae_germ (bxra_bcoef_f 1%Q) bxra_bone_f).
  apply bxra_f_coef_one.
Qed.

Lemma bxra_inst_smoke_norm_coef : forall q : Q,
  QeqT (@bxin_bnorm bxra_real_pre (@bxin_bcoef bxra_real_pre q)) (Qabs q).
Proof.
  intro q.
  change (@bxin_bnorm bxra_real_pre (@bxin_bcoef bxra_real_pre q))
    with (bxra_bnorm_f (bxra_bcoef_f q)).
  apply bxra_norm_coef_qeqt.
Qed.

Lemma bxra_inst_smoke_norm_wd : forall a b : Real,
  @bxin_bae bxra_real_pre a b ->
  QeqT (@bxin_bnorm bxra_real_pre a) (@bxin_bnorm bxra_real_pre b).
Proof.
  intros a b H.
  change (@bxin_bnorm bxra_real_pre a) with (bxra_bnorm_f a).
  change (@bxin_bnorm bxra_real_pre b) with (bxra_bnorm_f b).
  change (@bxin_bae bxra_real_pre a b) with (bxra_bae_germ a b).
  apply bxra_norm_wd_qeqt. exact H.
Qed.

