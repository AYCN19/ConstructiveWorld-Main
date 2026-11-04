(* ==========================================================================)
   UpAblP6_S5SlotWire.v — S5 数据位的单点实例对接件
   使命: Section UasswFeed：协方差正性（uassw_covariance_unit_pos）、涨落-耗散恒等（uassw_fluctuation_unit_id）、熵产率（uassw_entropy_production_unit）、nat→R 嵌入三件与宏损失单调/符号衰减/κ-半量评估五件。
   依赖: S01_BaseRing、fa56_id_carrier、fa56c_ext、PhysPredAblation、p4a_GradSignQDec、S5SlotWire；Stdlib QArith、Lists.List。
   对标: 涨落-耗散定理与熵产率的具体单点实例（统计物理）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56c_ext.
Require Import PhysPredAblation.
Require Import p4a_GradSignQDec.
Require Import S5SlotWire.
From Stdlib Require Import QArith_base Qring Qabs.
From Stdlib Require Import Lists.List.

(* ============ §一 接口字段四组输入实例（字段4/5/6/8/3） ================== *)

Section UasswFeed.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R    := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le   := @le RI.
Let lt   := @lt RI.

(* ---- 输入实例一（字段4/5：协方差位单位点正性使用） -------------------
   输入数据：D := one、H_inv := one（接口单位点），正性证书
   one_pos × one_pos 双供——被供给方 ssw_covariance_pos 在该具体点
   实例化，结论 lt zero (fa56_covariance one one) 为单位点协方差正性
   实例。非平凡性：使用链经 fa56_covariance_pos（mult_positive）在
   实例点闭合，证书合成（单位点双正）为本件构造。 ---- *)
Theorem uassw_covariance_unit_pos : lt zero (fa56_covariance one one).
Proof.
  exact (ssw_covariance_pos one one one_pos one_pos).
Qed.

(* ---- 输入实例二（字段6：恒等位单位点求值；强度如实申报） --------------
   输入数据：D := one、H_inv := one。fa56_covariance 装配在实例点
   定义性展开＝mult one one，恒等以 id_refl 构造子闭合——
   装配体沿实例点真实求值，恒等两肢逐位同型（透明展开级，如实申报）。 ---- *)
Theorem uassw_fluctuation_unit_id : Id (fa56_covariance one one) (mult one one).
Proof.
  exact id_refl.
Qed.

(* ---- 输入实例三（字段8：产率位单位权重实例） -------------------------
   输入数据：Flx := unit、TD := unit、w := 常一权重、theta := 常一势、
   J := tt、X := tt。fa56c 产率装配（权重×势）在实例点求值：
   常一×常一＝mult one one，恒等经被供给方 ssw_entropy_production_rate
   实例化后按 β 规约闭合。 ---- *)
Theorem uassw_entropy_production_unit :
  Id (fa56c_entropy_production_rate unit unit (fun _ => one) (fun _ => one) tt tt)
     (mult one one).
Proof.
  exact (ssw_entropy_production_rate unit unit (fun _ => one) (fun _ => one) tt tt).
Qed.

(* ---- 输入实例四（字段3：of_nat 三前提具体实现实例） ------------------
   输入数据：nat_to_R 具体实现（零元 zero、步进 plus·one 的
   nat 递归构造，泛型于接口），三前提件逐件构造为独立 Qed 件：
   零元恒等（iota 求值）、步进恒等（iota 求值）、非负（归纳＋
   plus_le_lt_pos 在实例点合成），再将 ssw_macro_loss_monotone
   实例化于 m0 := zero、t := 2 双步轨道点使用。 ---- *)
Fixpoint nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S m => plus (nat_to_R m) one
  end.

Theorem uassw_nat_to_R_zero_id : Id (nat_to_R O) zero.
Proof.
  exact id_refl.
Qed.

Theorem uassw_nat_to_R_step :
  forall n : nat, Id (nat_to_R (Datatypes.S n)) (plus (nat_to_R n) one).
Proof.
  intro n.
  exact (@id_refl _ (plus (nat_to_R n) one)).
Qed.

Theorem uassw_nat_to_R_nonneg : forall n : nat, le zero (nat_to_R n).
Proof.
  induction n as [| m IH].
  - apply le_refl.
  - apply lt_le_iff.
    apply inl.
    apply plus_le_lt_pos.
    * exact IH.
    * apply one_pos.
Qed.

Theorem uassw_macro_loss_zero_step2 :
  le (ppa_macro_loss (iterate ppa_macro_dynamics (Datatypes.S (Datatypes.S O)) zero))
     (ppa_macro_loss zero).
Proof.
  exact (ssw_macro_loss_monotone nat_to_R
           uassw_nat_to_R_zero_id uassw_nat_to_R_step uassw_nat_to_R_nonneg
           zero (Datatypes.S (Datatypes.S O))).
Qed.

End UasswFeed.

(* ============ §二 字段9a Q 数值输入实例（半半实例＋闭式求值伴件） ========== *)

Open Scope Q_scope.

(* ---- 输入实例五（字段9a：eta := 1/2、mu := 1/2、x0 := 1/2、n := 0、k := 1） --
   输入数据：ημ ＝ 1/4 ＜ 1（收缩系数 κ ＝ 3/4 落 (0,1)），三前提
   逐件由 Q 层有序比较计算闭合；被供给方 ssw_full_sign_decay_instance_ref
   在该闭式点实例化出数值衰减不等式。 ---- *)
Theorem uassw_full_sign_decay_half :
  Qle (Qabs (gsq_grad (1#2) (gsq_iter (1#2) (1#2) (O + Datatypes.S O) (1#2))))
      (gsq_pow (gsq_kappa (1#2) (1#2)) (Datatypes.S O)
         * Qabs (gsq_grad (1#2) (gsq_iter (1#2) (1#2) O (1#2)))).
Proof.
  apply (ssw_full_sign_decay_instance_ref (1#2) (1#2) (1#2) O (Datatypes.S O)).
  - (* 前提 0 < 1#2：Qlt 展开后为字面 Z 比较，具名引理 Z.lt_0_1 直给 *)
    exact Z.lt_0_1.
  - exact Z.lt_0_1.
  - (* 前提 1#2 * 1#2 < 1：Qlt 展开后为字面 Z 比较 1 < 4，单调链收束 *)
    exact (Z.lt_le_trans 1 2 4 (Z.lt_succ_diag_r 1)
             (Z.le_le_succ_r 2 3 (Z.le_le_succ_r 2 2 (Z.le_refl 2)))).
Qed.

(* ---- 真求值伴件三件：实例点数据经 Defined 体计算至闭式有理数 ---------
   κ(1/2,1/2) ＝ 3/4、g(1/2) ＝ 1/4、轨道一步 x₁ ＝ 3/8——
   gsq_step 三分支判定（stdlib 构造性三分，Defined 透明）沿实例点
   真实求值，结论逐位为字面有理数（Qeq 交叉积比较闭合）。 ---- *)
Theorem uassw_kappa_half_eval : gsq_kappa (1#2) (1#2) == (3#4).
Proof.
  (* 定义性求值：gsq_kappa 定义展开后核内换形至字面 3#4，右端显式取项 *)
  exact (Qeq_refl (3#4)).
Qed.

Theorem uassw_grad_half_eval : gsq_grad (1#2) (1#2) == (1#4).
Proof.
  (* 同上：gsq_grad 定义展开后核内换形至字面 1#4 *)
  exact (Qeq_refl (1#4)).
Qed.

Theorem uassw_iter_half_step_eval : gsq_iter (1#2) (1#2) (Datatypes.S O) (1#2) == (3#8).
Proof.
  cbn [gsq_iter]. unfold gsq_step, gsq_grad.
  destruct (Q_dec ((1#2) * (1#2)) 0) as [[Hneg | Hpos] | Hzero].
  - (* 情形 g < 0：下降支，Qeq 交叉积计算闭合于字面 48 *)
    unfold Qeq. cbv. exact (@eq_refl Z 48%Z).
  - (* 情形 0 < g：下降支同式 *)
    unfold Qeq. cbv. exact (@eq_refl Z 48%Z).
  - (* 情形 g ＝ 0：驻留支与 (1#2)*(1#2) 非零矛盾 *)
    exfalso. unfold Qeq in Hzero. cbv in Hzero. discriminate Hzero.
Qed.

Close Scope Q_scope.

(* ============ 自检段（G4 口径：逐件 Closed 实证） ===================== *)

Print Assumptions uassw_covariance_unit_pos.
Print Assumptions uassw_fluctuation_unit_id.
Print Assumptions uassw_entropy_production_unit.
Print Assumptions uassw_nat_to_R_zero_id.
Print Assumptions uassw_nat_to_R_step.
Print Assumptions uassw_nat_to_R_nonneg.
Print Assumptions uassw_macro_loss_zero_step2.
Print Assumptions uassw_full_sign_decay_half.
Print Assumptions uassw_kappa_half_eval.
Print Assumptions uassw_grad_half_eval.
Print Assumptions uassw_iter_half_step_eval.
