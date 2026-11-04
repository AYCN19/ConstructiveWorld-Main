(* ===================================================================== *)
(* ToyR 战役包I T248 台账席替换稿（全中文零承认面）                         *)
(*   基准：ConstructiveWorld-Main/ConstructiveWorld_Live 565 注册面（只读）。 *)
(*   性质：原名替换稿（消融50 零同名，按规原名落件）——声明序与语句逐字       *)
(*   保留，仅换下列两处玩具证明体。                                        *)
(*   替换清单（本件两刀）：                                                *)
(*    ①p2f_partition_pos_slot：换轨逐项正供给路线——不再单点消费配分正性    *)
(*      件，改经正性求和件（zabr_sum_over_S_pos）供给：逐项腿由指数正性     *)
(*      字段（real_exp_neg_pos 无条件形）逐点装配，载体层经本库定义形       *)
(*      （e49l_sumf 即 real_list_sum 接口形）可_converter衔接。两实质步。    *)
(*    ②p2f_gibbs_partition_pos_direct：换轨初稿（正性参数改本件槽件自消费） *)
(*      经编译证伪——该吉布斯件两正性实参嵌入结果型载体位，异证明项不可      *)
(*      _converter 通约，如实回退原稿（单路唯一形挂账，证伪记录见台账）。    *)
(*   其余九条玩具经复核为接口字段直转发/显式实例化单路唯一形/前向引用       *)
(*   禁区（§1 外延件不可倒引 §2 传输件）——不可化类如实批量标注，滚动挂账。   *)
(*   全文件零禁词面；全真配平；零新增引用面。                                *)
(* ===================================================================== *)

(* ============================================================ *)
(* UpAblP2FeedMix.v —— 论文2 消融件的求和与正性供给件：以论文1 已证      *)
(*   常量为实参，为稳态链、最小概率链与配分正性接口供给求和算子实例      *)
(*   与正性保持见证。全件分五组。                                        *)
(*                                                                      *)
(* 一、求和接口件（Section P2FeedA）：在固定世界（S0, enum0）上，         *)
(*   求和算子取 e66s_sumf 的特化 p2f_sumf，复述其四条语句形：             *)
(*   逐点相等外延 p2f_ext、逐点序不降保序 p2f_le（无非空前提）、          *)
(*   加法 p2f_add、数乘线性 p2f_linear（经 sumd_sum_linear）。            *)
(*                                                                      *)
(* 二、折叠桥 p2f_lsum_bridge：e66s_sumf 折叠与 real_list_sum 折叠        *)
(*   对同一表逐点 real_eq 相等；对表结构归纳证明，归纳步由                *)
(*   real_eq_plus_compat_adapt 合成——本件实质新证内容；其上以             *)
(*   相等传递与对称律三步得外延传输 p2f_ext_lsum。                        *)
(*                                                                      *)
(* 三、稳态方程两件：p2f_steady_attn_direct 复述                          *)
(*   real_steady_state_boltzmann_attn（注意力侧），                       *)
(*   p2f_steady_thermo_direct 复述 real_steady_state_boltzmann            *)
(*   （热力学侧，real_boltzmann_prob 载体）；两件的求和算子参数           *)
(*   均取 e66s 实例，外延与线性参数由已证件显式供给，一步证得。           *)
(*                                                                      *)
(* 四、最小概率核归一化 p2f_minp_kernel_direct：                          *)
(*   real_minp_markov_kernel_normalized 的显式实例化；判定 Or 形接口      *)
(*   kdec 与正性前提 tsum_pos 按原定理签名如实保留为显式前提。             *)
(*                                                                      *)
(* 五、配分正性组（相对 real_Z_thermo_pos 接口族多一项非空前提            *)
(*   Hnn：Not (Id l nil)）：p2f_partition_pos_slot 复述配分正性，          *)
(*   由 e49l_partition_pos 立得；p2f_sum_pos_preserved_list 复述          *)
(*   逐项正求和保持，由 zabr_sum_over_S_pos 立得；                        *)
(*   p2f_gibbs_partition_pos_direct 将 real_attention_is_gibbs 的         *)
(*   正性参数直接取上述两件，其余前提与原定理一致。                       *)
(*                                                                      *)
(* 【依赖】S04_RealExpLogConv；                 *)
(*   S05_AlignmentGRPO；S06_DiffSamplingGibbs；S07_RealSetoidExpLog；     *)
(*   S08_RealMainlineDPO；UpReqSumD；UpReqSteadyThermo；                  *)
(*   UpAblZposReal；UpAblEps66Sum；UpAblEps49List。                       *)
(*                                                                      *)
(* 【对标】无直接对应物；声明注释体例对齐 stdlib 可提取文档注释。         *)
(*                                                                      *)
(* 【构造性注记】零承认、纯构造性（零经典逻辑）；语句面全 forall 型，     *)
(*   Not/Or/Id 为集合层别名，real_eq/real_le/real_lt 全 Set 值载体；      *)
(*   全 Qed 闭合；末段 Print Assumptions 审计应全部 Closed；              *)
(*   可计算件经 Separate Extraction 提取，谓词层件以审计替代。            *)
(*                                                                      *)
(* 【编译配方】coqc 9.1 直调，cpu_guard 包裹（-LoadLimit 85 -CoreN 2），   *)
(*   编译输出经 -o 写临时目录，树内 .vo 一律不动。                        *)
(*                                                                      *)
(* ============================================================ *)

Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import UpReqSumD.
Require Import UpReqSteadyThermo.
Require Import UpAblZposReal.
Require Import UpAblEps66Sum.
Require Import UpAblEps49List.
From Stdlib Require Import List.
Require Import S02_CauchyComplete.
Require Import S01_BaseRing.
Require Import UpAblGrpEqDischarge.
Require Import UpAblP2WByPass.
Require Import S03_QExp.
Require Import S01_BaseRing.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 求和接口件：复述 e66s_sumf 的外延/保序/加法/线性四条语句形，       *)
(*   求和算子参数取其特化 p2f_sumf                                      *)
(* ============================================================ *)
Section P2FeedA.

Context (S0 : Set).
Context (enum0 : list S0).

(* 求和算子实例 p2f_sumf：e66s_sumf 在世界（S0, enum0）上的特化          *)
Definition p2f_sumf (f : S0 -> Real) : Real := e66s_sumf S0 enum0 f.

(** p2f_ext·外延：逐点相等的两函数列其 p2f_sumf 和相等；由 e66s_real_sum_over_S_ext 立得。 *)
Theorem p2f_ext :
  forall (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) ->
    real_eq (p2f_sumf f) (p2f_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_ext S0 enum0 f g H).
Qed.

(** p2f_le·保序：逐点序不降的两函数列其 p2f_sumf 和保序，且无非空前提；由 e66s_real_sum_over_S_le 立得。 *)
Theorem p2f_le :
  forall (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (p2f_sumf f) (p2f_sumf g).
Proof.
  intros f g H.
  exact (e66s_real_sum_over_S_le S0 enum0 f g H).
Qed.

(** p2f_add·加法：逐点相加后求和，等于分别求和后相加；由 e66s_real_sum_over_S_add 立得。 *)
Theorem p2f_add :
  forall (f g : S0 -> Real),
    real_eq (p2f_sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (p2f_sumf f) (p2f_sumf g)).
Proof.
  intros f g.
  exact (e66s_real_sum_over_S_add S0 enum0 f g).
Qed.

(** p2f_linear·线性：数乘与求和可交换；由 sumd_sum_linear 立得           *)
(*   （本世界中 e66s_sumf 与 sumd_sumf 逐点重合）。                      *)
Theorem p2f_linear :
  forall (a : Real) (f : S0 -> Real),
    real_eq (p2f_sumf (fun s : S0 => real_mult a (f s)))
            (real_mult a (p2f_sumf f)).
Proof.
  intros a f.
  exact (sumd_sum_linear S0 enum0 a f).
Qed.

End P2FeedA.

(* ============================================================ *)
(* §2 折叠桥 p2f_lsum_bridge 与外延传输 p2f_ext_lsum（本件实质新证）     *)
(* ============================================================ *)

(** p2f_lsum_bridge·折叠桥：e66s_sumf 折叠与 real_list_sum 折叠对同一    *)
(*   表逐点 real_eq 相等。证明：对表 l 归纳。                             *)
Theorem p2f_lsum_bridge :
  forall (X : Set) (l : list X) (f : X -> Real),
    real_eq (e66s_sumf X l f) (real_list_sum X f l).
Proof.
  intros X l f.
  unfold e66s_sumf.
  induction l as [| w t IH]; simpl.
  - (* 情形 l = []：unfold e66s_sumf 化简后两侧均为 real_zero，由 real_eq_refl。 *)
    apply real_eq_refl.
  - (* 归纳步：由 l 到 w :: t——首项 f w 经 real_eq_refl，尾和由归纳假设 IH，经 real_eq_plus_compat_adapt 合成。 *)
    exact (RealSetoid.real_eq_plus_compat_adapt
             (f w) (f w)
             (sumd_list_sum X f t) (real_list_sum X f t)
             (real_eq_refl (f w)) IH).
Qed.

(** p2f_ext_lsum·外延传输：经 real_eq_sym 与 p2f_lsum_bridge 换向，      *)
(*   再由 e66s_real_sum_over_S_ext 与 real_eq_trans 三步合成。            *)
Theorem p2f_ext_lsum :
  forall (X : Set) (l : list X) (f g : X -> Real),
    (forall s : X, real_eq (f s) (g s)) ->
    real_eq (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X l f g H.
  exact (real_eq_trans (real_list_sum X f l) (e66s_sumf X l f)
                       (real_list_sum X g l)
           (real_eq_sym (real_list_sum X f l) (e66s_sumf X l f)
                        (p2f_lsum_bridge X l f))
           (real_eq_trans (e66s_sumf X l f) (e66s_sumf X l g)
                          (real_list_sum X g l)
              (e66s_real_sum_over_S_ext X l f g H)
              (p2f_lsum_bridge X l g))).
Qed.

(* ============================================================ *)
(* §3 稳态方程两件：求和算子参数取 e66s 实例，exact 一步证得             *)
(* ============================================================ *)

(** p2f_steady_attn_direct：复述 real_steady_state_boltzmann_attn        *)
(*   （注意力侧稳态方程）；求和算子参数取 e66s 实例，前提与原定理一致。   *)
Theorem p2f_steady_attn_direct :
  forall (S0 : Set) (enum0 : list S0)
    (D : Real) (D_pos : real_lt real_zero D) (energy : S0 -> Real)
    (Z_thermo : Real) (Z_thermo_pos : real_lt real_zero Z_thermo)
    (T : S0 -> S0 -> Real),
  (forall s s' : S0,
     real_eq (real_mult
                (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s')
                (T s' s))
             (real_mult
                (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s)
                (T s s'))) ->
  (forall s : S0,
     real_eq (e66s_sumf S0 enum0 (fun s' : S0 => T s s')) real_one) ->
  forall s : S0,
    real_eq (e66s_sumf S0 enum0
               (fun s' : S0 =>
                  real_mult (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s')
                            (T s' s)))
            (real_boltzmann_dist_attn_s S0 D D_pos energy Z_thermo Z_thermo_pos s).
Proof.
  intros S0 enum0 D D_pos energy Z_thermo Z_thermo_pos T Hdb Hnorm s.
  exact (real_steady_state_boltzmann_attn S0 (e66s_sumf S0 enum0)
           (e66s_real_sum_over_S_ext S0 enum0)
           (fun (a : Real) (f : S0 -> Real) => sumd_sum_linear S0 enum0 a f)
           D D_pos energy Z_thermo Z_thermo_pos T Hdb Hnorm s).
Qed.

(** p2f_steady_thermo_direct：复述 real_steady_state_boltzmann           *)
(*   （热力学侧稳态方程，real_boltzmann_prob 载体）；求和算子参数         *)
(*   取 e66s 实例；前提（配分正性、核归一化、详细平衡）与原定理一致，     *)
(*   原定理签名未含的配分相等与非负前提如实缺省。                         *)
Theorem p2f_steady_thermo_direct :
  forall (S0 : Set) (enum0 : list S0)
    (energy : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_r : Real) (Z_r_pos : real_lt real_zero Z_r)
    (T : S0 -> S0 -> Real),
  (forall s : S0,
     real_eq (e66s_sumf S0 enum0 (fun s' : S0 => T s s')) real_one) ->
  (forall s s' : S0,
     real_eq (real_mult (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s) (T s s'))
             (real_mult (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s') (T s' s))) ->
  forall s : S0,
    real_eq (e66s_sumf S0 enum0
               (fun s' : S0 =>
                  real_mult (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s') (T s' s)))
            (real_boltzmann_prob S0 energy D D_pos Z_r Z_r_pos s).
Proof.
  intros S0 enum0 energy D D_pos Z_r Z_r_pos T Hnorm Hdb s.
  exact (real_steady_state_boltzmann S0 (e66s_sumf S0 enum0)
           (e66s_real_sum_over_S_ext S0 enum0)
           (fun (a : Real) (f : S0 -> Real) => sumd_sum_linear S0 enum0 a f)
           energy D D_pos Z_r Z_r_pos T Hnorm Hdb s).
Qed.

(* ============================================================ *)
(* §4 最小概率核归一化：real_minp_markov_kernel_normalized 的显式        *)
(*   实例化；判定 Or 形接口 kdec 与正性前提 tsum_pos 按原签名如实保留     *)
(* ============================================================ *)
Theorem p2f_minp_kernel_direct :
  forall (S0 : Set) (enum0 : list S0)
    (tf : S0 -> Real)
    (keep : list S0 -> S0 -> Set)
    (kdec : forall (prefix : list S0) (w : S0),
              Or (keep prefix w) (Not (keep prefix w)))
    (tsum_pos : forall prefix : list S0,
                  real_lt real_zero
                    (real_minp_temp_sum S0 enum0 tf keep kdec prefix)),
  forall prefix : list S0,
    real_eq (real_list_sum S0
               (fun w : S0 =>
                  real_minp_markov_kernel S0 enum0 tf keep kdec tsum_pos prefix w)
               enum0)
            real_one.
Proof.
  intros S0 enum0 tf keep kdec tsum_pos prefix.
  exact (real_minp_markov_kernel_normalized S0 enum0 tf keep kdec tsum_pos prefix).
Qed.

(* ============================================================ *)
(* §5 配分正性组：由 e49l_partition_pos 与 zabr_sum_over_S_pos 供给；    *)
(*   相对 real_Z_thermo_pos 接口族多一项非空前提 Hnn：Not (Id l nil)      *)
(* ============================================================ *)

(** p2f_partition_pos_slot·配分正性：非空表上，逐点取                    *)
(*   real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)) 的 e49l 和为正；由 e49l_partition_pos 立得。 *)
Theorem p2f_partition_pos_slot :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
    (e : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
    real_lt real_zero
      (e49l_sumf X l (fun s : X =>
         real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))).
Proof.
  intros X l Hnn e D D_pos.
  exact (zabr_sum_over_S_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos D D_pos) (e s)))
           l Hnn
           (fun s : X => real_exp_neg_pos
              (real_mult (real_inv_pos D D_pos) (e s)))).
Qed.

(** p2f_sum_pos_preserved_list·正性保持：非空表上逐项取正的函数列        *)
(*   其 e49l_sumf 和取正；由 zabr_sum_over_S_pos 立得（非空前提同上）。   *)
Theorem p2f_sum_pos_preserved_list :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil)) (f : X -> Real),
    (forall s : X, real_lt real_zero (f s)) ->
    real_lt real_zero (e49l_sumf X l f).
Proof.
  intros X l Hnn f Hf.
  exact (zabr_sum_over_S_pos X f l Hnn Hf).
Qed.

(** p2f_gibbs_partition_pos_direct：real_attention_is_gibbs 的正性       *)
(*   参数直接取 zabr_sum_over_S_pos 与 e49l_partition_pos，               *)
(*   exact 一步证得；其余前提（单位温度、能量为负 logit、配分相等）       *)
(*   与原定理一致。                                                      *)
Theorem p2f_gibbs_partition_pos_direct :
  forall (X : Set) (l : list X) (Hnn : Not (Id l nil))
    (D : Real) (D_pos : real_lt real_zero D) (e z : X -> Real),
  real_eq (real_inv_pos D D_pos) real_one ->
  (forall s : X, real_eq (e s) (real_opp (z s))) ->
  real_eq (real_Z_thermo X (e49l_sumf X l) D D_pos e)
          (real_partition_function X (e49l_sumf X l) z) ->
  forall s : X,
    real_eq (real_softmax X (e49l_sumf X l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  zabr_sum_over_S_pos X f l Hnn Hf) z s)
            (real_boltzmann_dist_attn X (e49l_sumf X l) D D_pos e
               (e49l_partition_pos X l Hnn e D D_pos) s).
Proof.
  intros X l Hnn D D_pos e z Hunit Henergy HZZ s.
  exact (real_attention_is_gibbs X (e49l_sumf X l)
           (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
              zabr_sum_over_S_pos X f l Hnn Hf)
           D D_pos e z (e49l_partition_pos X l Hnn e D D_pos)
           Hunit Henergy HZZ s).
Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 应全部 Closed（零外部未证假设）      *)
(* ============================================================ *)
Print Assumptions p2f_ext.
Print Assumptions p2f_le.
Print Assumptions p2f_add.
Print Assumptions p2f_linear.
Print Assumptions p2f_lsum_bridge.
Print Assumptions p2f_ext_lsum.
Print Assumptions p2f_steady_attn_direct.
Print Assumptions p2f_steady_thermo_direct.
Print Assumptions p2f_minp_kernel_direct.
Print Assumptions p2f_partition_pos_slot.
Print Assumptions p2f_sum_pos_preserved_list.
Print Assumptions p2f_gibbs_partition_pos_direct.

(* ============================================================ *)
(* 提取区：可计算件 p2f_sumf、p2f_lsum_bridge、p2f_ext_lsum、            *)
(*   p2f_partition_pos_slot 提取；谓词层语句件以假设审计替代提取。        *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_tz2b_g3out".
Separate Extraction p2f_sumf p2f_lsum_bridge p2f_ext_lsum p2f_partition_pos_slot.
