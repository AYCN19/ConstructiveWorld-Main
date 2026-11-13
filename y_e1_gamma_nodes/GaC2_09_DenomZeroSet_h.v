(* ConstructiveWorld-Main - the uniform exponential partial-sum remainder kit *)
(** * GaC2_09_DenomZeroSet_h - the uniform exponential partial-sum remainder and
      the pointwise carrier faces of the denominator zero set
    Mission.  Node C2-09 (segment C2, slot W1), first-order support piece of
      the denominator zero set family.  Casts the uniform exponential
      partial-sum remainder [e09_q_exp_rem] (|exp_partial n x - 1 - x| <=
      x*x for |x| <= 1 and n >= 1, uniform in n, the registered open slot
      of the C2-09 card), the uniform partial-sum magnitude bound
      [e09_exp_abs_bnd] (|exp_partial n x| <= 3 for |x| <= 1), and the
      pointwise carrier faces of the first-order remainder complex
      ([e09_sub_norm_pt], [e09_rem_re_pt], [e09_rem_im_pt]) consumed by
      GaC2_09_DenomZeroSet_i.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [ZArith], [Setoid], [Morphisms], [Arith.Arith], [Lia];
      [S01_BaseRing] (selective [NatLe]/[And] import), [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [S10_KVQuantTrig],
      [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx],
      [GaC1_Iface_Real], and the family pieces [GaC2_09_DenomZeroSet_b],
      [c], [d], [e] (named faces in Notes).
    References.  drafts_C2.md C2-09 card (:718-739) with the registered
      L11/L12 concretizations and the draft_sign_typo disclosure.
    Constructivity.  Every named construction is carried by [Set]; zero
      Sections, zero assumed constants, zero admitted goals; every proof
      closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_h.v]; flat build
      directory, acceptance via 50_toolkit/accept_node.py. *)
Require S01_BaseRing.
(** Notes.  Named consumed faces behind the Dependencies field:
    [c]: [d09_q_fact_inv_le2], [d09_q_abs_pow_le_one],
    [d09_q_abs_pow_le_sq], [d09_q_abs_sq_le_sq], [d09_q_mult_le_r];
    [d]: [d09_exp_proj]; [e] is reserved for the Downstream alias note;
    [S03_QExp]: [q_pow_abs], [q_pow_nonneg], [q_fact_pos],
    [q_square_nonneg]; [S10_KVQuantTrig]: [real_cos_proj],
    [real_sin_proj]; [CxRealPairCore]: [c_norm_sq_pt], [cRe_plus_pt],
    [cIm_plus_pt], [cRe_opp_pt], [cIm_opp_pt], [real_zero_pt],
    [real_one_pt]; [S02_CauchyComplete]: [real_mult_proj],
    [real_plus_proj], [real_opp_proj], [real_const_proj];
    [GaC1_Iface_Cx] supplies [real_le_b] and the pair carrier faces.
    Family pieces consumed: [GaC2_09_DenomZeroSet_b] supplies [d09_ln2]
    and [two_pow_1ms] (through the re-export chain of [c]/[d]);
    [GaC2_09_DenomZeroSet_e] is required for the [e09q] prefix registry. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
Require Import GaC2_09_DenomZeroSet_e.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The uniform exponential partial-sum remainder.              *)
(* ===================================================================== *)

Lemma e09_exp_abs_bnd : forall (n : nat) (x : Q),
  Qle (Qabs x) 1 -> Qle (Qabs (exp_partial n x)) 3.
Proof.
  intros n x Hx.
  assert (Hnn : Qle 0 (Qabs x)) by apply Qabs_nonneg.
  assert (Hpow1 : forall k : nat, Qle (q_pow (Qabs x) k) 1).
  { intro k.
    rewrite <- (Qabs_pos (q_pow (Qabs x) k)
                  (q_pow_nonneg (Qabs x) k (Qabs_nonneg x))).
    apply (d09_q_abs_pow_le_one (Qabs x) k).
    rewrite (Qabs_pos (Qabs x) (Qabs_nonneg x)). exact Hx. }
  assert (Hterm : forall m : nat,
    Qle (Qabs (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)))
        (Qabs x * q_pow (1 / 2) m)).
  { intro m.
    assert (Hd : (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m))%Q
                 == q_pow x (Datatypes.S m) * Qinv (q_fact (Datatypes.S m)))
      by reflexivity.
    rewrite Hd, Qabs_Qmult, Qabs_Qinv, q_pow_abs.
    rewrite (Qabs_pos (q_fact (Datatypes.S m))
               (Qlt_le_weak 0 _ (q_fact_pos (Datatypes.S m)))).
    apply (Qle_trans _ (Qabs x * Qinv (q_fact (Datatypes.S m)))).
    - apply (Qmult_le_compat_r (q_pow (Qabs x) (Datatypes.S m)) (Qabs x)
               (Qinv (q_fact (Datatypes.S m)))).
      + rewrite q_pow_succ, (Qmult_comm (Qabs x) (q_pow (Qabs x) m)).
        apply (Qle_trans _ (1 * Qabs x)).
        * apply (Qmult_le_compat_r (q_pow (Qabs x) m) 1 (Qabs x)).
          -- exact (Hpow1 m).
          -- exact (Qabs_nonneg x).
        * rewrite Qmult_1_l. apply Qle_refl.
      + exact (Qlt_le_weak 0 _
             (Qinv_lt_0_compat (q_fact (Datatypes.S m))
                (q_fact_pos (Datatypes.S m)))).
    - rewrite (Qmult_comm (Qabs x) (Qinv (q_fact (Datatypes.S m)))),
        (Qmult_comm (Qabs x) (q_pow (1 / 2) m)).
      destruct m as [| j].
      + assert (Hq1 : (Qinv (q_fact (Datatypes.S 0)))%Q == 1)
          by (cbn [q_fact]; field).
        rewrite Hq1, Qmult_1_l.
        cbn [q_pow].
        rewrite Qmult_1_l.
        apply Qle_refl.
      + exact (d09_q_mult_le_r (Qinv (q_fact (Datatypes.S (Datatypes.S j))))
                 (q_pow (1 / 2) (Datatypes.S j)) (Qabs x)
                 (d09_q_fact_inv_le2 j) Hnn). }
  assert (Hind : forall m : nat,
    Qle (Qabs (exp_partial m x - 1)) ((2 * Qabs x) * (1 - q_pow (1 / 2) m))).
  { intro m. induction m as [| m IHm].
    - assert (Hz : exp_partial 0 x - 1 == 0) by reflexivity.
      rewrite Hz. cbn [Qabs]. unfold Qle. simpl. lia.
    - cbn [exp_partial].
      assert (Hre : exp_partial m x + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m) - 1
                    == (exp_partial m x - 1)
                       + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)) by ring.
      rewrite Hre.
      apply (Qle_trans _ (Qabs (exp_partial m x - 1)
               + Qabs (q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)))).
      + apply Qabs_triangle.
      + apply (Qle_trans _ ((2 * Qabs x) * (1 - q_pow (1 / 2) m)
                            + Qabs x * q_pow (1 / 2) m)).
        * apply Qplus_le_compat.
          -- exact IHm.
          -- exact (Hterm m).
        * assert (Hgeo : forall a : Q,
              (2 * a) * (1 - q_pow (1 / 2) m) + a * q_pow (1 / 2) m
              == (2 * a) * (1 - q_pow (1 / 2) (Datatypes.S m))).
          { intro a. rewrite (q_pow_succ (1 / 2) m). field. }
          rewrite <- (Hgeo (Qabs x)). apply Qle_refl. }
  assert (Hfin : Qle (Qabs (exp_partial n x)) (1 + Qabs (exp_partial n x - 1))).
  { assert (Hre : exp_partial n x == 1 + (exp_partial n x - 1)) by field.
    apply (Qle_trans _ (Qabs (1 + (exp_partial n x - 1)))).
    - rewrite (Qabs_wd (exp_partial n x) (1 + (exp_partial n x - 1)) Hre).
      apply Qle_refl.
    - apply (Qle_trans _ (Qabs 1 + Qabs (exp_partial n x - 1))).
      + apply Qabs_triangle.
      + rewrite (Qabs_pos 1 (Qle_0_1)). apply Qle_refl. }
  apply (Qle_trans _ (1 + (2 * Qabs x) * (1 - q_pow (1 / 2) n)) 3).
  - apply (Qle_trans _ (1 + Qabs (exp_partial n x - 1))).
    + exact Hfin.
    + apply (Qplus_le_compat 1 1 _ _).
      * apply Qle_refl.
      * exact (Hind n).
  - apply (Qle_trans _ (1 + 2 * Qabs x) 3).
    + apply (Qplus_le_compat 1 1 _ _).
      * apply Qle_refl.
      * assert (Hq1 : Qle (1 - q_pow (1 / 2) n) 1).
        { apply (proj2 (Qle_minus_iff (1 - q_pow (1 / 2) n) 1)).
          apply (Qle_trans 0 (q_pow (1 / 2) n) (1 - (1 - q_pow (1 / 2) n))).
          - apply (q_pow_nonneg (1 / 2) n). exact Qhalf_nonneg.
          - apply qeq_le. ring. }
        assert (H2nn : Qle 0 (2 * Qabs x)).
        { apply (Qmult_le_0_compat 2 (Qabs x)).
          - unfold Qle. simpl. lia.
          - exact Hnn. }
        rewrite (Qmult_comm (2 * Qabs x) (1 - q_pow (1 / 2) n)).
        apply (Qle_trans _ (1 * (2 * Qabs x))).
        -- exact (d09_q_mult_le_r (1 - q_pow (1 / 2) n) 1 (2 * Qabs x) Hq1 H2nn).
        -- apply qeq_le. exact (Qmult_1_l (2 * Qabs x)).
    + apply (Qle_trans _ (1 + 2)).
      * apply (Qplus_le_compat 1 1 (2 * Qabs x) 2).
        -- apply Qle_refl.
        -- apply (Qle_trans _ (2 * 1)).
           ++ rewrite (Qmult_comm 2 (Qabs x)), (Qmult_comm 2 1).
              ** apply (Qmult_le_compat_r (Qabs x) 1 2 Hx).
                 --- apply (Qlt_le_weak 0 2). unfold Qlt. simpl. lia.
           ++ apply qeq_le. ring.
      * apply qeq_le. ring.
Qed.

Lemma e09_q_exp_rem : forall (n : nat) (x : Q),
  Qle (Qabs x) 1 -> (1 <= n)%nat ->
  Qle (Qabs (exp_partial n x - 1 - x)) (x * x).
Proof.
  intros n x Hx Hn.
  assert (Htsq : Qle 0 (x * x)) by apply q_square_nonneg.
  assert (Hsq2 : forall k : nat, Qle (Qabs (q_pow x (Datatypes.S (Datatypes.S k)))) (x * x)).
  { intro k. apply (Qle_trans _ (Qabs x * Qabs x)).
    - apply (d09_q_abs_pow_le_sq x (Datatypes.S (Datatypes.S k)) Hx); lia.
    - exact (d09_q_abs_sq_le_sq x Htsq). }
  assert (Hterm : forall m : nat,
    Qle (Qabs (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m)))
                 / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))
        ((x * x) * q_pow (1 / 2) (Datatypes.S (Datatypes.S m)))).
  { intro m.
    assert (Hd : (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m)))
                    / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))%Q
                 == q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m)))
                    * Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))
      by reflexivity.
    rewrite Hd, Qabs_Qmult, Qabs_Qinv.
    rewrite (Qabs_pos (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))
               (Qlt_le_weak 0 _ (q_fact_pos (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
    apply (Qle_trans _ ((x * x) * Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))).    
    - exact (d09_q_mult_le_r (Qabs (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m)))))
               (x * x) (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))
               (Hsq2 (Datatypes.S m))
               (Qlt_le_weak 0 _ (Qinv_lt_0_compat (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))
                  (q_fact_pos (Datatypes.S (Datatypes.S (Datatypes.S m))))))).
    - rewrite (Qmult_comm (x * x) (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))),
        (Qmult_comm (x * x) (q_pow (1 / 2) (Datatypes.S (Datatypes.S m)))).
      exact (d09_q_mult_le_r (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))
               (q_pow (1 / 2) (Datatypes.S (Datatypes.S m))) (x * x)
               (d09_q_fact_inv_le2 (Datatypes.S m)) Htsq). }
  assert (Hind : forall m : nat,
    Qle (Qabs (exp_partial (Datatypes.S (Datatypes.S m)) x - 1 - x))
        ((x * x) * (1 - q_pow (1 / 2) (Datatypes.S m)))).
  { intro m. induction m as [| m IHm].
    - assert (He2 : exp_partial (Datatypes.S (Datatypes.S 0)) x - 1 - x
                    == x * x * (1 # 2)).
      { cbn [exp_partial q_pow q_fact]. field. }
      assert (Hp2 : Qle 0 (x * x * (1 # 2))).
      { rewrite (Qmult_comm (x * x) (1 # 2)).
        apply (Qmult_le_0_compat (1 # 2) (x * x)).
        - unfold Qle. simpl. lia.
        - exact Htsq. }
      rewrite He2, (Qabs_pos (x * x * (1 # 2)) Hp2).
      cbn [q_pow].
      apply qeq_le. field.
    - assert (Hre : exp_partial (Datatypes.S (Datatypes.S (Datatypes.S m))) x - 1 - x
                    == (exp_partial (Datatypes.S (Datatypes.S m)) x - 1 - x)
                       + q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m)))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))))
        by (cbn [exp_partial]; ring).
      rewrite Hre.
      apply (Qle_trans _ (Qabs (exp_partial (Datatypes.S (Datatypes.S m)) x - 1 - x)
               + Qabs (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S m)))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))))).
      + apply Qabs_triangle.
      + apply (Qle_trans _ ((x * x) * (1 - q_pow (1 / 2) (Datatypes.S m))
                            + (x * x) * q_pow (1 / 2) (Datatypes.S (Datatypes.S m)))).
        * apply Qplus_le_compat.
          -- exact IHm.
          -- exact (Hterm m).
        * rewrite (q_pow_succ (1 / 2) (Datatypes.S m)).
          apply qeq_le. field. }
  destruct n as [| n].
  - lia.
  - destruct n as [| m].
    + assert (He1 : exp_partial (Datatypes.S 0) x - 1 - x == 0)
        by (cbn [exp_partial q_pow q_fact]; field).
      rewrite He1, (Qabs_pos 0 (Qle_refl 0)).
      exact Htsq.
    + apply (Qle_trans _ ((x * x) * (1 - q_pow (1 / 2) (Datatypes.S m)))).
      * exact (Hind m).
      * assert (Hq1 : Qle (1 - q_pow (1 / 2) (Datatypes.S m)) 1).
        { apply (proj2 (Qle_minus_iff (1 - q_pow (1 / 2) (Datatypes.S m)) 1)).
          apply (Qle_trans 0 (q_pow (1 / 2) (Datatypes.S m))
                   (1 - (1 - q_pow (1 / 2) (Datatypes.S m)))).
          - apply (q_pow_nonneg (1 / 2) (Datatypes.S m)). exact Qhalf_nonneg.
          - apply qeq_le. ring. }
        rewrite (Qmult_comm (x * x) (1 - q_pow (1 / 2) (Datatypes.S m))).
        apply (Qle_trans _ (1 * (x * x))).
        -- exact (d09_q_mult_le_r (1 - q_pow (1 / 2) (Datatypes.S m)) 1 (x * x) Hq1 Htsq).
        -- apply qeq_le. ring.
Qed.

(* ===================================================================== *)
(* Section 2. The pointwise carrier faces of the remainder complex.       *)
(* ===================================================================== *)

Lemma e09_sub_norm_pt : forall (s : Cx) (n : nat),
  projT1 (c_norm_sq (c_plus s (c_opp c_one))) n
  == (projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
       + projT1 (cIm s) n * projT1 (cIm s) n.
Proof.
  intros s n.
  rewrite c_norm_sq_pt, (cRe_plus_pt _ _ n), (cIm_plus_pt _ _ n),
    (cRe_opp_pt _ n), (cIm_opp_pt _ n).
  change (projT1 (cRe c_one) n) with (projT1 real_one n).
  change (projT1 (cIm c_one) n) with (projT1 real_zero n).
  rewrite (real_one_pt n), (real_zero_pt n).
  ring.
Qed.

Lemma e09_cos_term_wd : forall (j : nat) (x y : Q),
  x == y -> cos_term j x == cos_term j y.
Proof.
  intros j x y Hxy. unfold cos_term.
  rewrite (q_pow_wd x y (2 * j) Hxy). reflexivity.
Qed.

Lemma e09_cos_partial_wd : forall (n : nat) (x y : Q),
  x == y -> cos_partial n x == cos_partial n y.
Proof.
  intros n x y Hxy. induction n as [| m IH]; cbn [cos_partial].
  - exact (e09_cos_term_wd 0 x y Hxy).
  - rewrite IH, (e09_cos_term_wd (Datatypes.S m) x y Hxy). reflexivity.
Qed.

Lemma e09_sin_term_wd : forall (j : nat) (x y : Q),
  x == y -> sin_term j x == sin_term j y.
Proof.
  intros j x y Hxy. unfold sin_term.
  rewrite (q_pow_wd x y (Datatypes.S (2 * j)) Hxy). reflexivity.
Qed.

Lemma e09_sin_partial_wd : forall (n : nat) (x y : Q),
  x == y -> sin_partial n x == sin_partial n y.
Proof.
  intros n x y Hxy. induction n as [| m IH]; cbn [sin_partial].
  - exact (e09_sin_term_wd 0 x y Hxy).
  - rewrite IH, (e09_sin_term_wd (Datatypes.S m) x y Hxy). reflexivity.
Qed.

Lemma e09_rem_re_pt : forall (s : Cx) (n : nat),
  projT1 (cRe (c_plus (c_plus (two_pow_1ms s) (c_opp c_one))
                      (c_scale d09_ln2 (c_plus s (c_opp c_one))))) n
  == exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
       * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
       - 1 + projT1 d09_ln2 n * (projT1 (cRe s) n - 1).
Proof.
  intros [sr si] n.
  cbv beta iota zeta delta [two_pow_1ms c_exp c_scale c_plus c_opp c_one cRe cIm fst snd].
  rewrite ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n),
    ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n),
    ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n),
    ?(real_opp_proj _ n), ?(real_one_pt n), ?(real_zero_pt n),
    ?(d09_exp_proj _ n), ?(real_cos_proj _ n).
  assert (HA : projT1 (real_mult d09_ln2
                          (real_plus real_one (real_opp sr))) n
               == projT1 d09_ln2 n * (1 - projT1 sr n)).
  { rewrite (real_mult_proj _ _ n), (real_plus_proj _ _ n), (real_opp_proj _ n),
      (real_one_pt n).
    field. }
  assert (HB : projT1 (real_mult d09_ln2
                          (real_plus real_zero (real_opp si))) n
               == - (projT1 d09_ln2 n * projT1 si n)).
  { rewrite (real_mult_proj _ _ n), (real_plus_proj _ _ n), (real_opp_proj _ n),
      (real_zero_pt n).
    field. }
  rewrite ?(exp_partial_wd n _ _ HA), ?(e09_cos_partial_wd n _ _ HB).
  field.
Qed.

Lemma e09_rem_im_pt : forall (s : Cx) (n : nat),
  projT1 (cIm (c_plus (c_plus (two_pow_1ms s) (c_opp c_one))
                      (c_scale d09_ln2 (c_plus s (c_opp c_one))))) n
  == exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
       * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
       + projT1 d09_ln2 n * projT1 (cIm s) n.
Proof.
  intros [sr si] n.
  cbv beta iota zeta delta [two_pow_1ms c_exp c_scale c_plus c_opp c_one cRe cIm fst snd].
  rewrite ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n),
    ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n),
    ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n),
    ?(real_opp_proj _ n), ?(real_one_pt n), ?(real_zero_pt n),
    ?(d09_exp_proj _ n), ?(real_sin_proj _ n).
  assert (HA : projT1 (real_mult d09_ln2
                          (real_plus real_one (real_opp sr))) n
               == projT1 d09_ln2 n * (1 - projT1 sr n)).
  { rewrite (real_mult_proj _ _ n), (real_plus_proj _ _ n), (real_opp_proj _ n),
      (real_one_pt n).
    field. }
  assert (HB : projT1 (real_mult d09_ln2
                          (real_plus real_zero (real_opp si))) n
               == - (projT1 d09_ln2 n * projT1 si n)).
  { rewrite (real_mult_proj _ _ n), (real_plus_proj _ _ n), (real_opp_proj _ n),
      (real_zero_pt n).
    field. }
  rewrite ?(exp_partial_wd n _ _ HA), ?(e09_sin_partial_wd n _ _ HB).
  field.
Qed.
