(* 五字段指针｜模块：LW0PiTrigValues.v。
   使命：以几何法定义的圆周率 real_pi_geom（pi := 2 * cos_pi_half，其中
   cos_pi_half 是余弦在区间 (3/2, 5/3) 内的唯一零点，见 S10）给出正弦与
   余弦在 pi 处的值：cos(pi) == -1 与 sin(pi) == 0。此两端点值是 Niven 型
   积分机制（pi 无理性的构造性证明框架）所需的边界输入。本件为值面封装件：
   值面核心已 Closed 于库内 S12_B5RecycleSF 的 b5p 系（b5p_sin_pi_geom_zero /
   b5p_cos_pi_geom_neg_one / b5p_pi_geom_double），本件核对其语句形并以
   Set 层 And 桥与 real_const (-1) 表示桥补齐任务所需语句面。
   依赖：S01_BaseRing、S02_CauchyComplete（构造性实数环核、real_eq、
   real_eq_trans、real_eq_of_zero_diff、real_opp_proj）、
   S10_KVQuantTrig（cauchy_real_sin / cauchy_real_cos、cos_pi_half、
   real_pi_geom）、S12_B5RecycleSF（b5p_sin_pi_geom_zero、
   b5p_cos_pi_geom_neg_one、b5p_pi_trig_signature）。
   对标：I. Niven, A simple proof that pi is irrational, Bulletin of the
   American Mathematical Society 53 (1947), 509——本件供应其积分法所用的
   端点值 cos pi = -1 与 sin pi = 0；值面内核见库内 b5p 系
   （S12_B5RecycleSF，pi 三角签名节）。
   构造性：全部语句为 Set 层（real_eq : Real -> Real -> Set；And := A*B
   为 Set 层积型；语句面零 Prop 命题）；零公理、零承认、零经典逻辑；
   证明由库内 b5p 件的直接引用与一条 Q 层逐点恒等式（ring 闭合）组装，
   支持 Separate Extraction。
   编译配方：coqc -Q "D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo" "" LW0PiTrigValues.v *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Import PropositionConvergenceCore.
From Stdlib Require Import Lqa.
Opaque Qred.

(* ---- 表示桥：real_opp real_one == real_const (-1)（Q 层逐点恒等） ---- *)
Lemma lw0_real_opp_one_const : real_eq (real_opp real_one) (real_const (-1)%Q).
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_opp_proj real_one n).
  assert (Ho : projT1 real_one n == 1) by (cbn [projT1]; reflexivity).
  rewrite Ho.
  cbn [projT1 real_const].
  ring.
Qed.

(* ---- 主语句一：cos(pi) == -1 ----
   b5p_cos_pi_geom_neg_one 给出 cos(pi) == real_opp real_one；
   经 lw0_real_opp_one_const 换为 real_const (-1) 表示。 *)
Lemma pi_geom_cos_pi_neg_one :
  real_eq (cauchy_real_cos real_pi_geom) (real_const (-1)%Q).
Proof.
  apply (real_eq_trans
    (cauchy_real_cos real_pi_geom)
    (real_opp real_one)
    (real_const (-1)%Q)).
  - exact b5p_cos_pi_geom_neg_one.
  - exact lw0_real_opp_one_const.
Qed.

(* ---- 主语句二：sin(pi) == 0 ----
   与 b5p_sin_pi_geom_zero 语句面逐字相同，直接引用。 *)
Lemma pi_geom_sin_pi_zero :
  real_eq (cauchy_real_sin real_pi_geom) real_zero.
Proof.
  exact b5p_sin_pi_geom_zero.
Qed.

(* ---- Set 层积型封装：两端点值的 And 证书 ---- *)
Lemma pi_geom_trig_values :
  And (real_eq (cauchy_real_sin real_pi_geom) real_zero)
      (real_eq (cauchy_real_cos real_pi_geom) (real_const (-1)%Q)).
Proof.
  exact (pi_geom_sin_pi_zero, pi_geom_cos_pi_neg_one).
Qed.
