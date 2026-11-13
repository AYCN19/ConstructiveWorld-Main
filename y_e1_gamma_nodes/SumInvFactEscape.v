(* ============================================================ *)
(* SumInvFactEscape.v —— 使命：闭合 UpReqBanachNormOpp 的 Σ1/k! 逃逸目标   *)
(*   的显式假设缺口——Σ1/k! 逃逸主件：对任意 q : Q，存在 n 使               *)
(*   1 < |n!·(q − s_n)|。                                                  *)
(* 主件：sif_escape : forall q : Q,                                        *)
(*       sigT (fun n : nat =>                                              *)
(*         Qlt 1%Q (Qabs (q_fact n * (q - exp_series n 1)%Q)))；           *)
(*       目标形即 UpReqBanachNormOpp 原文语句面；                          *)
(*       伴件 sif_escape_closed : sif_sum_inv_fact_escape。                *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、                      *)
(*       UpReqBanachNormOpp；Stdlib QArith.QArith、QArith.Qabs、           *)
(*       ZArith.ZArith、Arith.Arith、Bool.Bool、Arith.Factorial、          *)
(*       Lia、Setoid、Morphisms、Extraction。                              *)
(* 备注：证法全构造性（零经典逻辑、零禁用假设形态）。 设 b := Z.pos (Qden q) > 0，Zc_n := n!·s_n 的整数化 （sif_Zc，归纳桥配引擎件 bno_q_pow_one / bno_mul_div_self / q_fact_pos），分子 d_n := Qnum q·n! − Zc_n·b，主乘积桥给 Qabs (n!·(q − s_n)) == (Z.abs d_n # b)（sif_abs_frac）。 窗口引理（sif_window）：若对一切 k ≤ 2b+1 均有 d_k ≠ 0 且         *)
(*       −b ≤ d_k ≤ b，则负支一步逃逸（d_{k+1} = (k+1)d_k − b < −b）       *)
(*       与回溯窗 N·d_{N−1} = d_N + b ≤ 2b、d_{N−1} ≥ 1 联立得             *)
(*       2b+1 ≤ 2b，矛盾。                                                *)
(*       零点引理（sif_zero_escape）：d_k = 0 ⟹ |d_{k+2}| = (k+3)·b       *)
(*       > b。                                                            *)
(*       witness 由 Type 层有界枚举 sif_enum（Qlt_bool 逐点判定，上界      *)
(*       2b+3 覆盖零点两步逃逸）给出：枚举失败支（Empty_set）逐点          *)
(*       Qcompare 三分（Lt 支定义性矛盾 / Eq 支 |d|=b 界内 / Gt 支         *)
(*       |d|<b 界内，零点情形经零点引理在 k+2 ≤ 2b+3 处消解），补足        *)
(*       窗口引理前提。                                                   *)
(* 构造性注记：全件语句面 Type 层 sigT，witness 全由 Set 层枚举产出，      *)
(*       无 Prop 泄露位；提取面预期干净，语句面无承认式构造。              *)
(*       命名：sif_ 前缀避免命名冲突；不依赖                               *)
(*       SqrtfCauchyDischarge / KLWallClosed / ExpNegPos 系模块。          *)
(* 编译配方：coqc 9.1 直调（vo 树内 -Q . "" 平面命名空间），信任缓存前置。 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lia Setoid Morphisms.

(* ============================================================ *)
(* S0：Q 层通用小件（同调/字面归一，零除法语义展开）                  *)
(* ============================================================ *)

Lemma sif_posZ : forall p : positive, (0%Z < Z.pos p)%Z.
Proof. intro p. exact (Pos2Z.is_pos p). Qed.

Lemma sif_Zpos_mul : forall (bp df : positive),
  (Z.pos (Pos.mul bp df) = Z.pos bp * Z.pos df)%Z.
Proof. intros bp df. exact (@eq_refl _ (Z.pos bp * Z.pos df)%Z). Qed.

Lemma sif_Qmake_eta : forall q : Q, (Qmake (Qnum q) (Qden q))%Q == q.
Proof. intro q. destruct q as [a b]. reflexivity. Qed.

Lemma sif_minus_make : forall q r : Q,
  (q - r)%Q ==
  ((Qnum q * Zpos (Qden r) - Qnum r * Zpos (Qden q))
   # (Qden q * Qden r))%Q.
Proof.
  intros q r. destruct q as [a b]. destruct r as [c d].
  unfold Qminus, Qeq. cbn [Qnum Qden Qplus Qopp Qmult].
  ring.
Qed.

Lemma sif_minus_comp_r : forall x y z : Q, x == y -> (x - z)%Q == (y - z)%Q.
Proof.
  intros x y z H. destruct x as [a b]. destruct y as [c d]. destruct z as [e f].
  unfold Qeq in H. unfold Qminus, Qeq.
  cbn [Qnum Qden Qplus Qopp Qmult] in *.
  rewrite (sif_Zpos_mul b f), (sif_Zpos_mul d f).
  (* 兼容性：目标含 Z 原子乘积（Q 分母正性消去），线性 lia 无见证——升 nia *)
  nia.
Qed.

Lemma sif_mult_comp_l : forall x y z : Q, x == y -> x * z == y * z.
Proof.
  intros x y z H. destruct x as [a b]. destruct y as [c d]. destruct z as [e f].
  unfold Qeq in H. unfold Qeq.
  cbn [Qnum Qden Qmult] in *.
  rewrite (sif_Zpos_mul b f), (sif_Zpos_mul d f).
  (* 兼容性：目标为三度 Z 单项式恒等（H: a·Z.pos d = c·Z.pos b 乘 Zpos f·e 消去）
     ——nia 乘深不足，改 ring 恒等式归零 + 线性 lia 完成（Qden 为 positive，须 Zpos 提升） *)
  assert (Hd : ((a*e)*(Zpos d * Zpos f) = (c*e)*(Zpos b * Zpos f))%Z).
  { assert (Hd1 : ((a*e)*(Zpos d * Zpos f))%Z
                  = ((a * Zpos d) * (e * Zpos f))%Z) by ring.
    assert (Hd2 : ((c*e)*(Zpos b * Zpos f))%Z
                  = ((c * Zpos b) * (e * Zpos f))%Z) by ring.
    rewrite Hd1, Hd2, H. reflexivity. }
  lia.
Qed.

Lemma sif_mult_comp_r : forall x y z : Q, x == y -> z * x == z * y.
Proof.
  intros x y z H. destruct x as [a b]. destruct y as [c d]. destruct z as [e f].
  unfold Qeq in H. unfold Qeq.
  cbn [Qnum Qden Qmult] in *.
  rewrite (sif_Zpos_mul f b), (sif_Zpos_mul f d).
  (* 兼容性：目标为三度 Z 单项式恒等，nia 乘深不足——ring 恒等式归零 +
     线性 lia 完成（与 sif_mult_comp_l 同法） *)
  assert (Hd : ((e*a)*(Zpos f * Zpos d) = (e*c)*(Zpos f * Zpos b))%Z).
  { assert (Hd1 : ((e*a)*(Zpos f * Zpos d))%Z
                  = ((e * Zpos f) * (a * Zpos d))%Z) by ring.
    assert (Hd2 : ((e*c)*(Zpos f * Zpos b))%Z
                  = ((e * Zpos f) * (c * Zpos b))%Z) by ring.
    rewrite Hd1, Hd2, H. reflexivity. }
  lia.
Qed.

Lemma sif_plus_comp : forall a b c d : Q,
  a == c -> b == d -> (a + b)%Q == (c + d)%Q.
Proof.
  intros a b c d H1 H2.
  destruct a as [a1 a2]. destruct b as [b1 b2].
  destruct c as [c1 c2]. destruct d as [d1 d2].
  unfold Qeq in H1, H2. unfold Qeq.
  cbn [Qnum Qden Qplus Qmult] in *.
  rewrite (sif_Zpos_mul a2 b2), (sif_Zpos_mul c2 d2).
  (* 兼容性：目标为双积 Z 恒等（Q 加法展开），线性 lia 无见证——
     ring 重排归位 H1/H2 形后代换完成（与 sif_mult_comp_l 同法） *)
  assert (Hd : ((a1*Zpos b2 + b1*Zpos a2) * (Zpos c2 * Zpos d2)
                = (c1*Zpos d2 + d1*Zpos c2) * (Zpos a2 * Zpos b2))%Z).
  { assert (Hd1 : ((a1*Zpos b2 + b1*Zpos a2) * (Zpos c2 * Zpos d2))%Z
                  = ((a1 * Zpos c2) * (Zpos b2 * Zpos d2)
                     + (b1 * Zpos d2) * (Zpos a2 * Zpos c2))%Z) by ring.
    assert (Hd2 : ((c1*Zpos d2 + d1*Zpos c2) * (Zpos a2 * Zpos b2))%Z
                  = ((c1 * Zpos a2) * (Zpos b2 * Zpos d2)
                     + (d1 * Zpos b2) * (Zpos a2 * Zpos c2))%Z) by ring.
    rewrite Hd1, Hd2, H1, H2. reflexivity. }
  exact Hd.
Qed.

Lemma sif_mult_opp_r : forall x y : Q, (x * (- y))%Q == (- (x * y))%Q.
Proof.
  intros x y. destruct x as [a b]. destruct y as [c d].
  unfold Qopp, Qmult, Qeq. cbn [Qnum Qden Qmult].
  ring.
Qed.

Lemma sif_opp_comp : forall x y : Q, x == y -> (- x)%Q == (- y)%Q.
Proof.
  intros x y H. destruct x as [a b]. destruct y as [c d].
  unfold Qeq in H. unfold Qopp, Qeq.
  cbn [Qnum Qden Qmult Pos.mul] in *.
  nia.
Qed.

Lemma sif_eq_id : forall (b1 b2 : bool), b1 = b2 -> Id b1 b2.
Proof. intros b1 b2 H. rewrite H. apply id_refl. Qed.

Lemma sif_qltt : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H. unfold QltT. unfold Qlt_bool.
  pose proof (proj1 (Qlt_alt x y) H) as Hc.
  rewrite Hc. apply id_refl.
Qed.

Lemma sif_qlt_one_comp_r : forall x y : Q, x == y -> Qlt 1%Q x -> Qlt 1%Q y.
Proof.
  intros x y H Hlt. destruct x as [a b]. destruct y as [c d].
  unfold Qlt, Qeq in *. cbn [Qnum Qden] in *.
  nia.
Qed.

(* ============================================================ *)
(* S1：整数骨架（Zc 整数化 + 分子函数 + 乘积桥）                      *)
(* ============================================================ *)

Fixpoint sif_Zc (n : nat) : Z :=
  match n with
  | O => 1%Z
  | Datatypes.S m => Z.of_nat (Datatypes.S m) * sif_Zc m + 1
  end.

Lemma sif_qfact_Z : forall n : nat,
  q_fact n == ((Z.of_nat (fact n)) # 1)%Q.
Proof.
  induction n as [| m IH].
  - cbn [q_fact fact]. first [reflexivity | lia | ring].
  - cbn [q_fact fact]. rewrite IH.
    rewrite (Nat2Z.inj_mul (Datatypes.S m) (fact m)).
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
    first [lia | ring | nia | reflexivity].
Qed.

(* 乘 F 归一桥（右乘形，分母 1，零除法语义）：
   (n! # 1) * s_n == (Zc_n # 1) *)
Lemma sif_Zc_bridge : forall n : nat,
  ((Z.of_nat (fact n)) # 1)%Q * exp_series n 1%Q
    == ((sif_Zc n) # 1)%Q.
Proof.
  induction n as [| m IH].
  - cbn [exp_series q_pow fact]. cbn [Qmult Pos.mul].
    first [reflexivity | lia | ring].
  - cbn [exp_series q_pow]. rewrite bno_q_pow_one.
    cbn [fact].
    rewrite Qmult_plus_distr_r.
    (* 兼容性：受限 cbn 下第二加数为 (N # 1) * (1 * 1 / q_fact) 形，无 Qopp 可供
       sif_mult_opp_r；交换两积并归一 1 * 1 == 1 后接入 H2/H1 链 *)
    rewrite (Qmult_comm (Z.of_nat (Datatypes.S m * fact m) # 1)
                        (exp_series m 1)).
    rewrite (Qmult_comm (Z.of_nat (Datatypes.S m * fact m) # 1)
                        (1 * 1 / q_fact (Datatypes.S m))).
    cbn [Qmult sif_Zc].
    assert (H2 : (1%Q / q_fact (Datatypes.S m))%Q
                 * ((Z.of_nat (Datatypes.S m * fact m)) # 1)%Q
                 == 1%Q).
    { apply (Qeq_trans _ ((1%Q / q_fact (Datatypes.S m))%Q
                          * q_fact (Datatypes.S m)%Q)%Q).
      - apply sif_mult_comp_r. apply Qeq_sym. apply sif_qfact_Z.
      - rewrite Qmult_comm. apply bno_mul_div_self.
        intro Hc. apply (Qlt_not_eq 0%Q _ (q_fact_pos (Datatypes.S m))).
        apply Qeq_sym. exact Hc. }
    assert (H1 : exp_series m 1%Q
                 * ((Z.of_nat (Datatypes.S m * fact m)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S m) * sif_Zc m) # 1)%Q).
    { apply (Qeq_trans _ (exp_series m 1%Q
                  * (((Z.of_nat (Datatypes.S m)) # 1)
                     * ((Z.of_nat (fact m)) # 1))%Q)%Q).
      - apply sif_mult_comp_r.
        unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
        rewrite (Nat2Z.inj_mul (Datatypes.S m) (fact m)).
        first [lia | ring | nia | reflexivity].
      - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S m)) # 1)
                            * (exp_series m 1%Q
                               * ((Z.of_nat (fact m)) # 1))%Q)%Q).
        + ring.
        + apply (Qeq_trans _ (((Z.of_nat (Datatypes.S m)) # 1)
                              * ((sif_Zc m) # 1))%Q).
          * apply sif_mult_comp_r.
            apply (Qeq_trans _ (((Z.of_nat (fact m)) # 1)
                                * exp_series m 1%Q)%Q).
            -- apply Qmult_comm.
            -- exact IH.
          * unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
            first [lia | ring | nia | reflexivity]. }
    rewrite H2. rewrite H1.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult Pos.mul].
    first [lia | ring | nia | reflexivity].
Qed.

(* 分子函数：d_n := Qnum q·n! − Zc_n·b，b := Z.pos (Qden q) *)
Definition sif_d (q : Q) (n : nat) : Z :=
  Qnum q * Z.of_nat (fact n) - sif_Zc n * Z.pos (Qden q).

Lemma sif_d_succ : forall (q : Q) (n : nat),
  sif_d q (Datatypes.S n) =
  (Z.of_nat (Datatypes.S n) * sif_d q n - Z.pos (Qden q))%Z.
Proof.
  intros q n. unfold sif_d. cbn [sif_Zc fact].
  rewrite (Nat2Z.inj_mul (Datatypes.S n) (fact n)).
  ring.
Qed.

(* 主乘积桥：n!·(q − s_n) == (d_n # b) *)
Lemma sif_frac_prod : forall (q : Q) (n : nat),
  (q_fact n * (q - exp_series n 1)%Q)%Q
    == ((sif_d q n) # (Qden q))%Q.
Proof.
  intros q n.
  apply (Qeq_trans _ (((Z.of_nat (fact n)) # 1)
                      * (q - exp_series n 1)%Q)%Q).
  - apply sif_mult_comp_l. apply sif_qfact_Z.
  - apply (Qeq_trans _ (((Z.of_nat (fact n)) # 1) * q%Q
                        + (- (((Z.of_nat (fact n)) # 1)
                              * exp_series n 1%Q))%Q)%Q).
    + unfold Qminus. rewrite Qmult_plus_distr_r.
      rewrite (sif_mult_opp_r _ _). reflexivity.
    + apply (Qeq_trans _ ((Qmake (Z.of_nat (fact n) * Qnum q) (Qden q)
                           - ((sif_Zc n) # 1))%Q)).
      * apply sif_plus_comp.
        -- apply (Qeq_trans _
                    ((Qmake (Z.of_nat (fact n) * Qnum q) (Qden q))%Q)).
           ++ apply sif_mult_comp_r. symmetry. apply sif_Qmake_eta.
        ++ unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
           first [lia | ring | nia | reflexivity].
        -- apply sif_opp_comp. exact (sif_Zc_bridge n).
      * destruct q as [a b]. unfold sif_d in *. unfold Qminus, Qeq.
        cbn [Qnum Qden Qplus Qopp Qmult Pos.mul] in *.
        rewrite (sif_Zpos_mul b 1).
        first [lia | ring | nia | reflexivity].
Qed.

Lemma sif_abs_frac : forall (q : Q) (n : nat),
  Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)
    == ((Z.abs (sif_d q n)) # (Qden q))%Q.
Proof.
  intros q n. rewrite sif_frac_prod. cbn [Qabs]. reflexivity.
Qed.

Lemma sif_hit_of_dd : forall (q : Q) (n : nat),
  (Z.pos (Qden q) < Z.abs (sif_d q n))%Z ->
  Qlt 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)).
Proof.
  intros q n Hesc.
  apply (sif_qlt_one_comp_r
          ((Z.abs (sif_d q n)) # (Qden q))%Q
          (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))).
  - apply Qeq_sym. apply sif_abs_frac.
  - unfold Qlt. cbn [Qnum Qden Qmult]. lia.
Qed.

(* 零点两步逃逸：d_k = 0 ⟹ |d_{k+2}| = (k+3)·b > b *)
Lemma sif_zero_escape : forall (q : Q) (k : nat),
  sif_d q k = 0%Z ->
  (Z.pos (Qden q) < Z.abs (sif_d q (Datatypes.S (Datatypes.S k))))%Z.
Proof.
  intros q k H0.
  assert (Hbq : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
  assert (H1 : sif_d q (Datatypes.S k) = (- Z.pos (Qden q))%Z)
    by (rewrite sif_d_succ, H0; lia).
  assert (H2 : sif_d q (Datatypes.S (Datatypes.S k))
               = (- (Z.of_nat k + 3) * Z.pos (Qden q))%Z)
    by (rewrite sif_d_succ, H1; nia).
  assert (Hssk : (sif_d q (Datatypes.S (Datatypes.S k)) <= 0)%Z)
    by (rewrite H2; nia).
  rewrite (Z.abs_neq _ Hssk).
  nia.
Qed.

(* ============================================================ *)
(* S2：窗口主引理 + 有界枚举                                          *)
(* ============================================================ *)

Lemma sif_window : forall (q : Q), (0%Z < Z.pos (Qden q))%Z ->
  (forall k : nat, (k <= Z.to_nat (2 * Z.pos (Qden q) + 1))%nat ->
     sif_d q k <> 0%Z /\ (sif_d q k <= Z.pos (Qden q) /\ - Z.pos (Qden q) <= sif_d q k))%Z -> False.
Proof.
  intros q Hb Hall.
  assert (Hsucc : forall n : nat,
    sif_d q (Datatypes.S n) =
    (Z.of_nat (Datatypes.S n) * sif_d q n - Z.pos (Qden q))%Z)
    by (intro n; rewrite (sif_d_succ q n); reflexivity).
  assert (Hpos : forall k : nat, (k < Z.to_nat (2 * Z.pos (Qden q) + 1))%nat ->
                 (0 < sif_d q k)%Z).
  { intros k HkN.
    destruct (Z_le_gt_dec 0 (sif_d q k)) as [Hle | Hgt].
    - destruct (Z.eq_dec (sif_d q k) 0) as [Heq | Hne].
      + exfalso. destruct (Hall k (Nat.lt_le_incl _ _ HkN)) as [Hne2 _].
        congruence.
      + lia.
    - exfalso.
      assert (Hge1 : (1 <= Z.of_nat (Datatypes.S k))%Z) by lia.
      assert (Hprod : (Z.of_nat (Datatypes.S k) * sif_d q k <= -1)%Z) by nia.
      assert (Hdn : (sif_d q (Datatypes.S k) < - Z.pos (Qden q))%Z)
        by (rewrite Hsucc; lia).
      destruct (Hall (Datatypes.S k) ltac:(lia)) as [_ [Hub Hlow]].
      lia. }
  assert (HN1 : (1 <= Z.to_nat (2 * Z.pos (Qden q) + 1))%nat) by lia.
  assert (HzN : (Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 1)) = 2 * Z.pos (Qden q) + 1)%Z) by lia.
  assert (Hwin : (Z.of_nat (Z.to_nat (2 * Z.pos (Qden q) + 1))
                  * sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1))) <= 2 * Z.pos (Qden q))%Z).
  { assert (HSN : (Datatypes.S (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1)))
                   = Z.to_nat (2 * Z.pos (Qden q) + 1))%nat) by lia.
    pose proof (Hsucc (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1)))) as HH.
    rewrite HSN in HH.
    destruct (Hall (Z.to_nat (2 * Z.pos (Qden q) + 1)) (Nat.le_refl _)) as [_ [Hub _]].
    lia. }
  assert (Hpd : (0 < sif_d q (Nat.pred (Z.to_nat (2 * Z.pos (Qden q) + 1))))%Z)
    by (apply Hpos; lia).
  nia.
Qed.

Lemma sif_dec_pt : forall (q : Q) (n : nat),
  (QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)))
  + (QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))
      -> Empty_set).
Proof.
  intros q n. unfold QltT.
  destruct (Qlt_bool 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) eqn:E.
  - left. apply id_refl.
  - right. intros Hc. inversion Hc.
Qed.

Fixpoint sif_enum (q : Q) (k : nat) :
  (sigT (fun n : nat => prod (n <= k)%nat
            (QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q)))))
  + (forall n : nat, (n <= k)%nat ->
       QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))
       -> Empty_set) :=
  match k with
  | O =>
    match sif_dec_pt q O with
    | inl c => inl (existT _ O (pair (Nat.le_refl O) c))
    | inr c =>
        inr (fun (n : nat) (Hn0 : (n <= 0)%nat) (Hcc : QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) =>
          match Nat.eq_dec n O with
          | left E =>
              c (eq_rect n
                   (fun n1 : nat =>
                      QltT 1%Q
                        (Qabs ((q_fact n1 * (q - exp_series n1 1)%Q)%Q)))
                   Hcc O E)
          | right E => False_rect _ ltac:(lia)
          end)
    end
  | Datatypes.S m =>
    match sif_enum q m with
    | inl f =>
        inl (match f with
             | existT _ n0 pf =>
                 match pf with
                 | pair Hn0 Hc0 =>
                     existT _ n0 (pair (le_S _ _ Hn0) Hc0)
                 end
             end)
    | inr g =>
      match sif_dec_pt q (Datatypes.S m) with
      | inl c => inl (existT _ (Datatypes.S m)
                          (pair (Nat.le_refl (Datatypes.S m)) c))
      | inr c =>
        inr (fun (n : nat) (Hn : (n <= Datatypes.S m)%nat) (Hcc : QltT 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))) =>
          match Nat.eq_dec n (Datatypes.S m) with
          | right E => g n ltac:(lia) Hcc
          | left E =>
              c (eq_rect n
                   (fun n1 : nat =>
                      QltT 1%Q
                        (Qabs ((q_fact n1 * (q - exp_series n1 1)%Q)%Q)))
                   Hcc (Datatypes.S m) E)
          end)
      end
    end
  end.

(* ============================================================ *)
(* S3：逃逸主件（目标形即 UpReqBanachNormOpp.v 原文语句面）           *)
(* ============================================================ *)

Definition sif_sum_inv_fact_escape : Type :=
  forall q : Q,
    sigT (fun n : nat => Qlt 1 (Qabs (q_fact n * (q - exp_series n 1))%Q)).

Theorem sif_escape : forall q : Q,
  sigT (fun n : nat =>
    Qlt 1%Q (Qabs ((q_fact n * (q - exp_series n 1)%Q)%Q))).
Proof.
  intro q.
  assert (Hbq : (0 < Z.pos (Qden q))%Z) by apply sif_posZ.
  destruct (sif_enum q (Z.to_nat (2 * Z.pos (Qden q) + 3)))
    as [[n [Hn Hc]] | Hno].
  - exists n. apply QltT_to_Qlt. exact Hc.
  - exfalso. apply (sif_window q Hbq).
    intros k HkN.
    assert (HkN3 : (k <= Z.to_nat (2 * Z.pos (Qden q) + 3))%nat) by lia.
    destruct (Qlt_bool 1%Q (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q)))
      eqn:EQ.
    + exfalso. destruct (Hno k HkN3 (sif_eq_id _ _ EQ)).
    + (* EQ : Qlt_bool 1 (Qabs ...) = false ⟹ 无逃逸 ⟹ |d_k| ≤ b *)
      assert (Hnb : ~ (1%Q < Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))).
      { intro Hlt.
        destruct (Hno k HkN3 (sif_qltt _ _ Hlt)). }
      pose proof (sif_abs_frac q k) as HF.
      assert (Habsb : (Z.abs (sif_d q k) <= Z.pos (Qden q))%Z).
      { destruct (Z_le_gt_dec (Z.abs (sif_d q k)) (Z.pos (Qden q)))
          as [Hle | Hgt].
        - exact Hle.
        - exfalso. apply Hnb.
          apply (sif_qlt_one_comp_r
                   ((Z.abs (sif_d q k)) # (Qden q))%Q
                   (Qabs ((q_fact k * (q - exp_series k 1)%Q)%Q))).
          ++ apply Qeq_sym. exact HF.
          ++ unfold Qlt. cbn [Qnum Qden Qmult]. lia. }
      assert (Hssk3 : (Datatypes.S (Datatypes.S k)
                       <= Z.to_nat (2 * Z.pos (Qden q) + 3))%nat) by lia.
      destruct (Z.eq_dec (sif_d q k) 0) as [Hz | Hnz].
      { destruct (Hno (Datatypes.S (Datatypes.S k)) Hssk3
            (sif_qltt _ _
               ltac:(apply sif_hit_of_dd;
                     apply (sif_zero_escape q k Hz)))). }
      split; [ exact Hnz | split; lia ].
Qed.

Corollary sif_escape_closed : sif_sum_inv_fact_escape.
Proof. exact sif_escape. Qed.

(* ============================================================ *)
(* S4：提取检验 + 假设面自审                                          *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction sif_escape sif_escape_closed sif_enum sif_dec_pt
  sif_window sif_abs_frac sif_frac_prod sif_hit_of_dd sif_d sif_d_succ
  sif_zero_escape sif_Zc sif_Zc_bridge sif_qfact_Z.

Print Assumptions sif_escape.
Print Assumptions sif_escape_closed.
