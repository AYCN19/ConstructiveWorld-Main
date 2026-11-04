(* ==========================================================================)
   fka_weak_triangle_ref.v — 二元 Gram 不等式核的实数层实例引述件
   使命: fka_weak_triangle_ref：(ac+bd)² ≤ (a²+b²)(c²+d²) 的实数层实例——语句面逐字照录 ForwardKLAdjudication 定格区，由被引主件 wtc_weak_triangle_load 直接给出；范围如实注记为 Gram 核实例而非 KL 弱三角本体。
   依赖: S01_BaseRing、fa53_compat_abs、WeakTriangleClose；Local Existing Instance RI_base。
   对标: Cauchy–Schwarz 不等式的二元实数实例。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing. Require Import fa53_compat_abs.
Require Import WeakTriangleClose.
(* 裸名 R/plus/mult/le 顶层解析前提补注（S01／WeakTriangleClose 同款定式；
   缺此行时顶层展开报 Could not find an instance for RealInterface，
   补此一行即合，语句面仍逐字）： *)
Local Existing Instance RI_base.
Theorem fka_weak_triangle_ref :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI)
         (a b c d : R),
    le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
       (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof. intros RI DO a b c d. exact (@wtc_weak_triangle_load RI DO a b c d). Qed.

Print Assumptions fka_weak_triangle_ref.
