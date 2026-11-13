(* ConstructiveWorld-Main - the pointwise estimate engine of the first-order face *)
(** * GaC2_09_DenomZeroSet_i - the pointwise estimate engine of the denominator
      zero set first-order face
    Mission.  Node C2-09 (segment C2, slot W1), estimate-engine piece of the
      denominator zero set family.  Casts [e09_pointwise_bnd]: on the
      rational window where the exponential and trigonometric partial-sum
      arguments stay in the unit disk and the window square L*L*X is at
      most 7/9, the squared first-order remainder of the denominator is
      bounded by 14 * L * L * X uniformly in the partial-sum index, the
      engine consumed by GaC2_09_DenomZeroSet_j.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [ZArith], [Setoid], [Morphisms], [Arith.Arith], [Lia];
      [S01_BaseRing] (selective [NatLe]/[And] import), [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [S10_KVQuantTrig],
      [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx],
      [GaC1_Iface_Real], and the family pieces [GaC2_09_DenomZeroSet_c],
      [e], [h] (named faces in Notes).
    References.  drafts_C2.md C2-09 card (:718-739) with the registered
      L11/L12 concretizations and the bishop_ordinal_deviation and
      draft_sign_typo disclosures of the acceptance checkpoint.
    Constructivity.  Every named construction is carried by [Set]; zero
      Sections, zero assumed constants, zero admitted goals; every proof
      closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_i.v]; flat build
      directory, acceptance via 50_toolkit/accept_node.py. *)
Require S01_BaseRing.
(** Notes.  Named consumed faces behind the Dependencies field:
    [c]: [d09_q_trig_dev], [d09_q_mult_le_r]; [e]: [e09q_sq_abs];
    [h]: [e09_exp_abs_bnd], [e09_q_exp_rem]; [S03_QExp]:
    [q_square_nonneg]; [S02_CauchyComplete]: [Qle_0_1]; [GaC1_Iface_Cx]
    supplies [real_le_b] and the pair carrier faces; stdlib [QArith]:
    [Qabs_triangle], [Qabs_Qmult], [Qabs_nonneg], [Qle_Qabs],
    [Qopp_le_compat], [Qmult_le_compat_r], [Qmult_le_0_compat],
    [Qlt_le_weak], [Qlt_le_trans], [Qle_minus_iff], [Qlt_minus_iff],
    [Qplus_le_compat], [Qle_refl]. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_e.
Require Import GaC2_09_DenomZeroSet_h.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Local Open Scope Q_scope.

Lemma e09_two_sum : forall x : Q, 2 * x == x + x.
Proof. intro x. field. Qed.

Lemma e09_four_prod : forall x y : Q, (2 * x) * (2 * y) == (2 * (x * y)) * 2.
Proof. intros x y. field. Qed.

Lemma e09_pointwise_bnd : forall (n : nat) (L sg tt : Q),
  Qle (Qabs (L * (1 - sg))) 1 ->
  Qle (Qabs (- (L * tt))) 1 ->
  Qle (L * L * ((sg - 1) * (sg - 1) + tt * tt)) (7 / 9) ->
  (1 <= n)%nat ->
  Qle ((exp_partial n (L * (1 - sg)) * cos_partial n (- (L * tt)) - 1
          + L * (sg - 1))
         * (exp_partial n (L * (1 - sg)) * cos_partial n (- (L * tt)) - 1
            + L * (sg - 1))
        + (exp_partial n (L * (1 - sg)) * sin_partial n (- (L * tt)) + L * tt)
          * (exp_partial n (L * (1 - sg)) * sin_partial n (- (L * tt)) + L * tt))
       (14 * L * L * ((sg - 1) * (sg - 1) + tt * tt)).
Proof.
  intros n L sg tt HA1 HB1 HW9 Hn.
  remember (L * (1 - sg)) as A eqn:HAd.
  remember (- (L * tt)) as B eqn:HBd.
  remember ((sg - 1) * (sg - 1) + tt * tt) as X eqn:HXd.
  remember (exp_partial n A) as XP eqn:HXPd.
  remember (cos_partial n B) as CP eqn:HCPd.
  remember (sin_partial n B) as SP eqn:HSPd.
  assert (Htsq : Qle 0 (A * A + B * B)).
  { apply (Qle_trans _ (0 + 0)).
    - apply qeq_le. ring.
    - apply Qplus_le_compat; apply q_square_nonneg. }
  assert (HWX : A * A + B * B == L * L * X).
  { rewrite HAd, HBd, HXd. field. }
  rewrite <- HWX in HW9.
  assert (HWnn : Qle 0 (A * A + B * B)) by exact Htsq.
  assert (HAbsXP : Qle (Qabs XP) 3).
  { rewrite HXPd. exact (e09_exp_abs_bnd n A HA1). }
  assert (HRemXP : Qle (Qabs (XP - 1 - A)) (A * A)).
  { rewrite HXPd. exact (e09_q_exp_rem n A HA1 Hn). }
  destruct (d09_q_trig_dev n B HB1) as [HCos HSin].
  rewrite <- HCPd in HCos. rewrite <- HSPd in HSin.
  assert (HAle : Qle (A * A) (Qabs A)).
  { apply (Qle_trans _ (Qabs A * Qabs A)).
    - apply (Qle_trans _ (Qabs (A * A))).
      + apply Qle_Qabs.
      + rewrite Qabs_Qmult. apply Qle_refl.
    - apply (Qle_trans _ (1 * Qabs A)).
      + apply (Qmult_le_compat_r (Qabs A) 1 (Qabs A)).
        -- exact HA1.
        -- apply Qabs_nonneg.
      + rewrite Qmult_1_l. apply Qle_refl. }
  assert (HBle : Qle (B * B) (Qabs B)).
  { apply (Qle_trans _ (Qabs B * Qabs B)).
    - apply (Qle_trans _ (Qabs (B * B))).
      + apply Qle_Qabs.
      + rewrite Qabs_Qmult. apply Qle_refl.
    - apply (Qle_trans _ (1 * Qabs B)).
      + apply (Qmult_le_compat_r (Qabs B) 1 (Qabs B)).
        -- exact HB1.
        -- apply Qabs_nonneg.
      + rewrite Qmult_1_l. apply Qle_refl. }
  assert (HXP1 : Qle (Qabs (XP - 1)) (2 * Qabs A)).
  { assert (Hre : XP - 1 == (XP - 1 - A) + A) by field.
    rewrite Hre. apply (Qle_trans _ (Qabs (XP - 1 - A) + Qabs A)).
    - apply Qabs_triangle.
    - apply (Qle_trans _ (A * A + Qabs A)).
      + apply (Qplus_le_compat (Qabs (XP - 1 - A)) (A * A) (Qabs A) (Qabs A)
                 HRemXP (Qle_refl _)).
      + apply (Qle_trans _ (Qabs A + Qabs A)).
        * apply (Qplus_le_compat (A * A) (Qabs A) (Qabs A) (Qabs A)
                   HAle (Qle_refl _)).
        * apply qeq_le. rewrite (e09_two_sum (Qabs A)). reflexivity. }
  assert (HSPb : Qle (Qabs SP) (2 * Qabs B)).
  { assert (Hre : SP == B + (SP - B)) by field.
    rewrite Hre. apply (Qle_trans _ (Qabs B + Qabs (SP - B))).
    - apply Qabs_triangle.
    - apply (Qle_trans _ (Qabs B + B * B)).
      + apply (Qplus_le_compat (Qabs B) (Qabs B) (Qabs (SP - B)) (B * B)
                 (Qle_refl _) HSin).
      + apply (Qle_trans _ (Qabs B + Qabs B)).
        * apply (Qplus_le_compat (Qabs B) (Qabs B) (B * B) (Qabs B)
                   (Qle_refl _) HBle).
        * apply qeq_le. rewrite (e09_two_sum (Qabs B)). reflexivity. }
  assert (HmAB : Qle (2 * (Qabs A * Qabs B)) (A * A + B * B)).
  { assert (HsqA : Qabs A * Qabs A == A * A) by apply e09q_sq_abs.
    assert (HsqB : Qabs B * Qabs B == B * B) by apply e09q_sq_abs.
    assert (Hs : Qle 0 ((Qabs A - Qabs B) * (Qabs A - Qabs B)))
      by apply q_square_nonneg.
    assert (Hexp : forall x y : Q,
             (x - y) * (x - y) == x * x + y * y - 2 * (x * y))
      by (intros x y; field).
    pose proof (Hexp (Qabs A) (Qabs B)) as HexpAB.
    rewrite HexpAB in Hs. rewrite HsqA, HsqB in Hs.
    remember (Qabs A * Qabs B) as P eqn:EP.
    exact (proj2 (Qle_minus_iff (2 * P) (A * A + B * B)) Hs). }
  assert (HA3 : Qle (A * A) (3 * (A * A))).
  { apply (Qle_trans _ (1 * (A * A))).
    - rewrite Qmult_1_l. apply Qle_refl.
    - apply (Qmult_le_compat_r 1 3 (A * A)).
      + unfold Qle. simpl. lia.
      + apply q_square_nonneg. }
  assert (HBW : Qle (B * B) (A * A + B * B)).
  { apply (Qle_trans _ (0 + B * B)).
    - apply qeq_le. ring.
    - apply Qplus_le_compat; [apply q_square_nonneg | apply Qle_refl]. }
  assert (HmA : L * (sg - 1) == - A) by (rewrite HAd; field).
  assert (HmB : L * tt == - B) by (rewrite HBd; field).
  assert (HReBd : (XP * CP - 1 + L * (sg - 1))%Q
                  == ((XP - 1 - A) + XP * (CP - 1))%Q) by (rewrite HmA; field).
  assert (HImBd : (XP * SP + L * tt)%Q == ((SP - B) + (XP - 1) * SP)%Q)
    by (rewrite HmB; field).
  assert (HXPcp : Qle (Qabs XP * Qabs (CP - 1)) (3 * (B * B))).
  { apply (Qle_trans _ (3 * Qabs (CP - 1))).
    - apply (Qmult_le_compat_r (Qabs XP) 3 (Qabs (CP - 1))).
      + exact HAbsXP.
      + apply Qabs_nonneg.
    - rewrite (Qmult_comm 3 (Qabs (CP - 1))), (Qmult_comm 3 (B * B)).
      apply (Qmult_le_compat_r (Qabs (CP - 1)) (B * B) 3).
      + exact HCos.
      + apply (Qlt_le_weak 0 3). unfold Qlt. simpl. lia. }
  assert (HXPsp : Qle (Qabs (XP - 1) * Qabs SP)
                       ((2 * Qabs A) * (2 * Qabs B))).
  { apply (Qle_trans _ ((2 * Qabs A) * Qabs SP)).
    - apply (Qmult_le_compat_r (Qabs (XP - 1)) (2 * Qabs A) (Qabs SP)).
      + exact HXP1.
      + apply Qabs_nonneg.
    - rewrite (Qmult_comm (2 * Qabs A) (Qabs SP)),
        (Qmult_comm (2 * Qabs A) (2 * Qabs B)).
      apply (Qmult_le_compat_r (Qabs SP) (2 * Qabs B) (2 * Qabs A)).
      + exact HSPb.
      + apply (Qmult_le_0_compat 2 (Qabs A)).
        * unfold Qle. simpl. lia.
        * apply Qabs_nonneg. }
  assert (H4AB : Qle ((2 * Qabs A) * (2 * Qabs B)) (2 * (A * A + B * B))).
  { rewrite (e09_four_prod (Qabs A) (Qabs B)),
      (Qmult_comm 2 (A * A + B * B)).
    apply (Qmult_le_compat_r (2 * (Qabs A * Qabs B)) (A * A + B * B) 2).
    - exact HmAB.
    - apply (Qlt_le_weak 0 2). unfold Qlt. simpl. lia. }
  assert (HW3re : Qle (Qabs (XP * CP - 1 + L * (sg - 1)))
                       (3 * (A * A + B * B))).
  { rewrite HReBd.
    apply (Qle_trans _ (Qabs (XP - 1 - A) + Qabs (XP * (CP - 1)))).
    - apply Qabs_triangle.
    - rewrite Qabs_Qmult.
      apply (Qle_trans _ (A * A + 3 * (B * B))).
      + apply (Qplus_le_compat (Qabs (XP - 1 - A)) (A * A)
                 (Qabs XP * Qabs (CP - 1)) (3 * (B * B)) HRemXP HXPcp).
      + apply (Qle_trans _ (3 * (A * A) + 3 * (B * B))).
        * apply (Qplus_le_compat (A * A) (3 * (A * A)) (3 * (B * B))
                   (3 * (B * B)) HA3 (Qle_refl _)).
        * apply qeq_le. field. }
  assert (HW3im : Qle (Qabs (XP * SP + L * tt)) (3 * (A * A + B * B))).
  { rewrite HImBd.
    apply (Qle_trans _ (Qabs (SP - B) + Qabs ((XP - 1) * SP))).
    - apply Qabs_triangle.
    - rewrite Qabs_Qmult.
      apply (Qle_trans _ (B * B + (2 * Qabs A) * (2 * Qabs B))).
      + apply (Qplus_le_compat (Qabs (SP - B)) (B * B)
                 (Qabs (XP - 1) * Qabs SP) ((2 * Qabs A) * (2 * Qabs B))
                 HSin HXPsp).
      + apply (Qle_trans _ ((A * A + B * B) + 2 * (A * A + B * B))).
        * apply (Qplus_le_compat (B * B) (A * A + B * B)
                   ((2 * Qabs A) * (2 * Qabs B)) (2 * (A * A + B * B))
                   HBW H4AB).
        * apply qeq_le. field. }
  assert (HsqR : Qle ((XP * CP - 1 + L * (sg - 1))
                        * (XP * CP - 1 + L * (sg - 1))
                       + (XP * SP + L * tt) * (XP * SP + L * tt))
                     (18 * ((A * A + B * B) * (A * A + B * B)))).
  { apply (Qle_trans _ ((3 * (A * A + B * B)) * (3 * (A * A + B * B))
                        + (3 * (A * A + B * B)) * (3 * (A * A + B * B)))).
    - apply Qplus_le_compat.
      + apply (Qle_trans _ (Qabs (XP * CP - 1 + L * (sg - 1))
                               * Qabs (XP * CP - 1 + L * (sg - 1)))).
        * apply (Qle_trans _ (Qabs ((XP * CP - 1 + L * (sg - 1))
                                      * (XP * CP - 1 + L * (sg - 1))))).
          -- apply Qle_Qabs.
          -- rewrite Qabs_Qmult. apply Qle_refl.
        * apply (Qle_trans _ ((3 * (A * A + B * B))
                                 * Qabs (XP * CP - 1 + L * (sg - 1)))).
          -- apply (Qmult_le_compat_r
                      (Qabs (XP * CP - 1 + L * (sg - 1)))
                      (3 * (A * A + B * B))
                      (Qabs (XP * CP - 1 + L * (sg - 1)))).
             ++ exact HW3re.
             ++ apply Qabs_nonneg.
          -- rewrite (Qmult_comm (3 * (A * A + B * B))
                     (Qabs (XP * CP - 1 + L * (sg - 1)))).
             apply (Qmult_le_compat_r
                      (Qabs (XP * CP - 1 + L * (sg - 1)))
                      (3 * (A * A + B * B))
                      (3 * (A * A + B * B))).
             ++ exact HW3re.
             ++ apply (Qmult_le_0_compat 3 (A * A + B * B)).
                ** unfold Qle. simpl. lia.
                ** exact Htsq.
      + apply (Qle_trans _ (Qabs (XP * SP + L * tt)
                              * Qabs (XP * SP + L * tt))).
        * apply (Qle_trans _ (Qabs ((XP * SP + L * tt)
                                      * (XP * SP + L * tt)))).
          -- apply Qle_Qabs.
          -- rewrite Qabs_Qmult. apply Qle_refl.
        * apply (Qle_trans _ ((3 * (A * A + B * B))
                                 * Qabs (XP * SP + L * tt))).
          -- apply (Qmult_le_compat_r
                      (Qabs (XP * SP + L * tt))
                      (3 * (A * A + B * B))
                      (Qabs (XP * SP + L * tt))).
             ++ exact HW3im.
             ++ apply Qabs_nonneg.
          -- rewrite (Qmult_comm (3 * (A * A + B * B))
                     (Qabs (XP * SP + L * tt))).
             apply (Qmult_le_compat_r
                      (Qabs (XP * SP + L * tt))
                      (3 * (A * A + B * B))
                      (3 * (A * A + B * B))).
             ++ exact HW3im.
             ++ apply (Qmult_le_0_compat 3 (A * A + B * B)).
                ** unfold Qle. simpl. lia.
                ** exact Htsq.
    - apply qeq_le. ring. }
  assert (H9 : Qle (9 * (A * A + B * B)) 7).
  { apply (Qle_trans _ (9 * (7 / 9)) 7).
    - rewrite (Qmult_comm 9 (A * A + B * B)), (Qmult_comm 9 (7 / 9)).
      apply (Qmult_le_compat_r (A * A + B * B) (7 / 9) 9).
      + exact HW9.
      + unfold Qle. simpl. lia.
    - apply qeq_le. field. }
  assert (Hfin : Qle (18 * ((A * A + B * B) * (A * A + B * B)))
                     (14 * L * L * X)).
  { apply (Qle_trans _ ((9 * (A * A + B * B)) * (2 * (A * A + B * B)))
             (14 * L * L * X)).
    - apply qeq_le. field.
    - apply (Qle_trans _ (7 * (2 * (A * A + B * B)))).
      + apply (Qmult_le_compat_r (9 * (A * A + B * B)) 7
                 (2 * (A * A + B * B))).
        -- exact H9.
        -- apply (Qmult_le_0_compat 2 (A * A + B * B)).
           ++ unfold Qle. simpl. lia.
           ++ exact HWnn.
      + rewrite HWX. apply qeq_le. field. }
  apply (Qle_trans _ (18 * ((A * A + B * B) * (A * A + B * B)))).
  - exact HsqR.
  - exact Hfin.
Qed.
