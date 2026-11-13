(* ============================================================
   模块：LW0PiIrrational.v
   使命：圆周率（π）无理性的构造性证明（Niven 路线）：对每个有理数 q，
         给出圆周率与 q 的显式相离见证。技术路线为 Niven 型积分论证的
         代数化——ℚ[t] 多项式微分代数、圆周率处的三角端点值、正弦在区
         间 (0, pi) 上的正性、端点泛函与反导数构造、端点泛函值的整数
         性、下界见证与无理性装配。
   依赖：S01_BaseRing（NatLe、Set 层积型 And/Or）、S02_CauchyComplete
        （Real、real_eq/real_lt 序环核心、QltT/QleT'、real_const）、
        S03_QExp（q_pow、q_fact）、S07_RealSetoidExpLog
        （real_lt_plus_translate、real_opp_lt_compat）、S08_RealMainlineDPO
        （real_opp_opp）、S09_EntropyReal（real_mult_opp_one_l）、
        S10_KVQuantTrig（cauchy_real_sin、cauchy_real_cos、real_pi_geom、
        real_pi_geom_between、real_metric、real_mult_proj、
        cos_pi_half_proj）、S12_B5RecycleSF（b5p_sin_pi_geom_zero、
        b5p_cos_pi_geom_neg_one）、UpReqPadeTailPos（qtr_mult_eq_compat_l）、
        UpReqAltSumPos（altsum 交错和引擎）、UpReqBanachAdd（bpa_binom
        二项式系数面）、UpReqIrrationalCriterion（lic_metric_proj 度量投
        影）；Stdlib QArith、Setoid、Morphisms、Arith（含 Arith.Factorial
        的 fact）、ZArith、Lia、Lqa。
   对标：I. Niven, A simple proof that pi is irrational, Bull. Amer.
         Math. Soc. 53 (1947), 509；Coq 标准库无对应物。
   构造性：全部语句 Set 层承载；零公理、零承认、零经典逻辑；主语句
         支持 Separate Extraction。
   编译配方：coqc -Q ConstructiveWorld_vo "" LW0PiIrrational.v
   ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S12_B5RecycleSF.
Require Import UpReqPadeTailPos.
Require Import UpReqAltSumPos.
Require Import UpReqIrrationalCriterion.
Require Import UpReqBanachAdd.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Arith.Arith Arith.Factorial ZArith.ZArith Lia Lqa.
From Stdlib Require Import Setoid Morphisms.
Import Datatypes.

(* ================= §1 ℚ 上的多项式微分代数 ================= *)

(* A polynomial is its coefficient list, constant term first. *)
Definition QPoly := list Q.

(* Coefficientwise addition, padding the shorter list with zeros. *)
Fixpoint qpoly_add (p q : QPoly) : QPoly :=
  match p with
  | nil => q
  | cons a p' =>
      match q with
      | nil => p
      | cons b q' => cons (a + b) (qpoly_add p' q')
      end
  end.

(* Scalar multiplication by a rational number. *)
Fixpoint qpoly_scalar (a : Q) (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons b p' => cons (a * b) (qpoly_scalar a p')
  end.

(* Multiplication, using (a + t * P) * Q = a * Q + t * (P * Q). *)
Fixpoint qpoly_mul (p q : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' =>
      qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p' q))
  end.

(* Evaluation at x, by Horner recursion on the coefficient list. *)
Fixpoint qpoly_eval (p : QPoly) (x : Q) : Q :=
  match p with
  | nil => 0
  | cons a p' => a + x * qpoly_eval p' x
  end.

(* Nontriviality test: does any coefficient differ from zero? *)
Fixpoint qpoly_is_nonzero (p : QPoly) : bool :=
  match p with
  | nil => false
  | cons a p' => negb (Qeq_bool a 0) || qpoly_is_nonzero p'
  end.

(* Degree: the index of the highest nonzero coefficient.  The zero          *)
(* polynomial has degree 0 by convention.                                   *)
Fixpoint qpoly_degree (p : QPoly) : nat :=
  match p with
  | nil => 0
  | cons a p' => if qpoly_is_nonzero p' then S (qpoly_degree p') else 0
  end.

(* Formal derivative: the coefficient of t^i becomes i * a_i, so            *)
(* d/dt (a + t * P) = P + t * P'  (the derivative of a constant is the      *)
(* one-element zero list).                                                  *)
Fixpoint qpoly_deriv (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' => qpoly_add p' (cons 0 (qpoly_deriv p'))
  end.

(* Helper for the substitution t |-> c * t: cc is the running power c^i,    *)
(* so the coefficient of t^i becomes a_i * cc. *)
Fixpoint qpoly_comp_aux (c cc : Q) (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' => cons (a * cc) (qpoly_comp_aux c (cc * c) p')
  end.

(* The substitution t |-> c * t, coefficientwise: a_i becomes a_i * c^i. *)
Definition qpoly_comp_scale (c : Q) (p : QPoly) : QPoly :=
  qpoly_comp_aux c 1 p.

(* The n-th formal derivative. *)
Fixpoint qpoly_deriv_iter (n : nat) (p : QPoly) : QPoly :=
  match n with
  | 0 % nat => p
  | S m => qpoly_deriv (qpoly_deriv_iter m p)
  end.

(* ------------------------------------------------------------------ *)
(* Evaluation identities.                                             *)
(* ------------------------------------------------------------------ *)

Lemma qpoly_add_r_nil : forall p : QPoly, qpoly_add p nil = p.
Proof.
  induction p as [|a p IH]; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma qpoly_eval_add : forall p q x,
  qpoly_eval (qpoly_add p q) x == qpoly_eval p x + qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x; simpl.
  - ring.
  - destruct q as [|b q]; simpl.
    + ring.
    + rewrite (IH q x); ring.
Qed.

Lemma qpoly_eval_scalar : forall a p x,
  qpoly_eval (qpoly_scalar a p) x == a * qpoly_eval p x.
Proof.
  intros a p x; induction p as [|b p IH]; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(* The derivative of a nonempty list, evaluated pointwise: this is the    *)
(* identity P' = P + t * P' written for P = a + t * rest.                 *)
Lemma qpoly_eval_deriv_cons : forall a p x,
  qpoly_eval (qpoly_deriv (cons a p)) x ==
  qpoly_eval p x + x * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a p x.
  change (qpoly_deriv (cons a p))
    with (qpoly_add p (cons 0 (qpoly_deriv p))).
  rewrite (qpoly_eval_add p (cons 0 (qpoly_deriv p)) x).
  change (qpoly_eval (cons 0 (qpoly_deriv p)) x)
    with (0 + x * qpoly_eval (qpoly_deriv p) x).
  ring.
Qed.

(* Differentiation is additive, pointwise. *)
Lemma qpoly_eval_deriv_add : forall p q x,
  qpoly_eval (qpoly_deriv (qpoly_add p q)) x ==
  qpoly_eval (qpoly_add (qpoly_deriv p) (qpoly_deriv q)) x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - destruct q as [|b q].
    + change (qpoly_deriv nil) with (@nil Q).
      rewrite (qpoly_add_r_nil (qpoly_deriv (cons a p))).
      rewrite (qpoly_add_r_nil (cons a p)).
      ring.
    + replace (qpoly_add (cons a p) (cons b q))
        with (cons (a + b) (qpoly_add p q)) by reflexivity.
      change (qpoly_deriv (cons (a + b) (qpoly_add p q)))
        with (qpoly_add (qpoly_add p q)
                (cons 0 (qpoly_deriv (qpoly_add p q)))).
      rewrite (qpoly_eval_add (qpoly_add p q)
                 (cons 0 (qpoly_deriv (qpoly_add p q))) x).
      change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_add p q))) x)
        with (0 + x * qpoly_eval (qpoly_deriv (qpoly_add p q)) x).
      rewrite (IH q x).
      rewrite (qpoly_eval_add p q x).
      rewrite (qpoly_eval_add (qpoly_deriv p) (qpoly_deriv q) x).
      rewrite (qpoly_eval_add (qpoly_deriv (cons a p))
                 (qpoly_deriv (cons b q)) x).
      rewrite (qpoly_eval_deriv_cons a p x).
      rewrite (qpoly_eval_deriv_cons b q x).
      ring.
Qed.

(* Differentiation commutes with scalar multiplication, pointwise. *)
Lemma qpoly_eval_deriv_scalar : forall a p x,
  qpoly_eval (qpoly_deriv (qpoly_scalar a p)) x ==
  qpoly_eval (qpoly_scalar a (qpoly_deriv p)) x.
Proof.
  intros a p x; induction p as [|b p IH].
  - simpl; ring.
  - change (qpoly_scalar a (cons b p)) with (cons (a * b) (qpoly_scalar a p)).
    change (qpoly_deriv (cons (a * b) (qpoly_scalar a p)))
      with (qpoly_add (qpoly_scalar a p)
              (cons 0 (qpoly_deriv (qpoly_scalar a p)))).
    rewrite (qpoly_eval_add (qpoly_scalar a p)
               (cons 0 (qpoly_deriv (qpoly_scalar a p))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_scalar a p))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (qpoly_scalar a p)) x).
    rewrite IH.
    rewrite (qpoly_eval_scalar a p x).
    rewrite (qpoly_eval_scalar a (qpoly_deriv p) x).
    rewrite (qpoly_eval_scalar a (qpoly_deriv (cons b p)) x).
    rewrite (qpoly_eval_deriv_cons b p x).
    change (qpoly_eval (cons b p) x) with (b + x * qpoly_eval p x).
    ring.
Qed.

(* Evaluation is multiplicative. *)
Lemma qpoly_eval_mul : forall p q x,
  qpoly_eval (qpoly_mul p q) x == qpoly_eval p x * qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - replace (qpoly_mul (cons a p) q)
      with (qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)))
        by reflexivity.
    rewrite (qpoly_eval_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)) x).
    rewrite (qpoly_eval_scalar a q x).
    change (qpoly_eval (cons 0 (qpoly_mul p q)) x)
      with (0 + x * qpoly_eval (qpoly_mul p q) x).
    rewrite (IH q x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    ring.
Qed.

(* The product rule, stated pointwise:                                     *)
(* (p * q)' evaluated at x equals (p' * q + p * q') evaluated at x.        *)
Lemma qpoly_deriv_mul : forall p q x,
  qpoly_eval (qpoly_deriv (qpoly_mul p q)) x ==
  qpoly_eval
    (qpoly_add (qpoly_mul (qpoly_deriv p) q) (qpoly_mul p (qpoly_deriv q))) x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - replace (qpoly_mul (cons a p) q)
      with (qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)))
        by reflexivity.
    rewrite (qpoly_eval_deriv_add (qpoly_scalar a q)
               (cons 0 (qpoly_mul p q)) x).
    rewrite (qpoly_eval_add (qpoly_deriv (qpoly_scalar a q))
               (qpoly_deriv (cons 0 (qpoly_mul p q))) x).
    rewrite (qpoly_eval_deriv_scalar a q x).
    rewrite (qpoly_eval_scalar a (qpoly_deriv q) x).
    rewrite (qpoly_eval_deriv_cons 0 (qpoly_mul p q) x).
    rewrite (IH q x).
    rewrite (qpoly_eval_mul p q x).
    rewrite (qpoly_eval_add (qpoly_mul (qpoly_deriv p) q)
               (qpoly_mul p (qpoly_deriv q)) x).
    rewrite (qpoly_eval_mul (qpoly_deriv p) q x).
    rewrite (qpoly_eval_mul p (qpoly_deriv q) x).
    rewrite (qpoly_eval_add (qpoly_mul (qpoly_deriv (cons a p)) q)
               (qpoly_mul (cons a p) (qpoly_deriv q)) x).
    rewrite (qpoly_eval_mul (qpoly_deriv (cons a p)) q x).
    rewrite (qpoly_eval_mul (cons a p) (qpoly_deriv q) x).
    rewrite (qpoly_eval_deriv_cons a p x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The substitution t |-> c * t and its chain rule.                   *)
(* ------------------------------------------------------------------ *)

Lemma qpoly_comp_aux_eval : forall p c cc x,
  qpoly_eval (qpoly_comp_aux c cc p) x == cc * qpoly_eval p (c * x).
Proof.
  intros p c; induction p as [|a p IH]; intros cc x.
  - simpl; ring.
  - change (qpoly_comp_aux c cc (cons a p))
      with (cons (a * cc) (qpoly_comp_aux c (cc * c) p)).
    change (qpoly_eval (cons (a * cc) (qpoly_comp_aux c (cc * c) p)) x)
      with (a * cc + x * qpoly_eval (qpoly_comp_aux c (cc * c) p) x).
    change (qpoly_eval (cons a p) (c * x))
      with (a + (c * x) * qpoly_eval p (c * x)).
    rewrite (IH (cc * c) x).
    ring.
Qed.

Lemma qpoly_comp_aux_deriv_eval : forall p c cc x,
  qpoly_eval (qpoly_deriv (qpoly_comp_aux c cc p)) x ==
  cc * c * qpoly_eval (qpoly_deriv p) (c * x).
Proof.
  intros p c; induction p as [|a p IH]; intros cc x.
  - simpl; ring.
  - change (qpoly_comp_aux c cc (cons a p))
      with (cons (a * cc) (qpoly_comp_aux c (cc * c) p)).
    change (qpoly_deriv (cons (a * cc) (qpoly_comp_aux c (cc * c) p)))
      with (qpoly_add (qpoly_comp_aux c (cc * c) p)
              (cons 0 (qpoly_deriv (qpoly_comp_aux c (cc * c) p)))).
    rewrite (qpoly_eval_add (qpoly_comp_aux c (cc * c) p)
               (cons 0 (qpoly_deriv (qpoly_comp_aux c (cc * c) p))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_comp_aux c (cc * c) p))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (qpoly_comp_aux c (cc * c) p)) x).
    rewrite (qpoly_comp_aux_eval p c (cc * c) x).
    rewrite (IH (cc * c) x).
    rewrite (qpoly_eval_deriv_cons a p (c * x)).
    change (qpoly_eval (cons a p) (c * x))
      with (a + (c * x) * qpoly_eval p (c * x)).
    ring.
Qed.

(* The chain rule for the substitution t |-> c * t, stated pointwise:      *)
(* d/dt P(c*t) evaluated at x equals c * P' evaluated at c*x.              *)
Lemma qpoly_deriv_comp_scale : forall p c x,
  qpoly_eval (qpoly_deriv (qpoly_comp_scale c p)) x ==
  c * qpoly_eval (qpoly_deriv p) (c * x).
Proof.
  intros p c x; destruct p as [|a [|b p]].
  - unfold qpoly_comp_scale; simpl; ring.
  - unfold qpoly_comp_scale; simpl; ring.
  - unfold qpoly_comp_scale.
    change (qpoly_comp_aux c 1 (cons a (cons b p)))
      with (cons (a * 1)
                (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))).
    change (qpoly_deriv
              (cons (a * 1)
                 (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))))
      with (qpoly_add
              (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))
              (cons 0 (qpoly_deriv
                         (cons (b * (1 * c))
                            (qpoly_comp_aux c (1 * c * c) p))))).
    rewrite (qpoly_eval_add
               (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p))
               (cons 0 (qpoly_deriv
                          (cons (b * (1 * c))
                             (qpoly_comp_aux c (1 * c * c) p)))) x).
    change (qpoly_eval
              (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p)) x)
      with (b * (1 * c)
              + x * qpoly_eval (qpoly_comp_aux c (1 * c * c) p) x).
    change (qpoly_eval
              (cons 0
                 (qpoly_deriv
                    (cons (b * (1 * c)) (qpoly_comp_aux c (1 * c * c) p)))) x)
      with (0 + x * qpoly_eval
                       (qpoly_deriv
                          (cons (b * (1 * c))
                             (qpoly_comp_aux c (1 * c * c) p))) x).
    rewrite (qpoly_eval_deriv_cons (b * (1 * c))
               (qpoly_comp_aux c (1 * c * c) p) x).
    rewrite (qpoly_comp_aux_eval p c (1 * c * c) x).
    rewrite (qpoly_comp_aux_deriv_eval p c (1 * c * c) x).
    rewrite (qpoly_eval_deriv_cons a (cons b p) (c * x)).
    rewrite (qpoly_eval_deriv_cons b p (c * x)).
    change (qpoly_eval (cons b p) (c * x))
      with (b + (c * x) * qpoly_eval p (c * x)).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Iterated derivatives: recursion identities.                        *)
(* ------------------------------------------------------------------ *)

(* One step of the recursion defining iterated derivatives. *)
Lemma qpoly_deriv_iter_succ : forall n p,
  qpoly_deriv_iter (S n) p = qpoly_deriv (qpoly_deriv_iter n p).
Proof.
  reflexivity.
Qed.

(* Iterated derivatives may be taken in any order:                         *)
(* the (n+1)-st derivative equals the n-th derivative of the derivative.   *)
Lemma qpoly_deriv_iter_commute : forall n p,
  qpoly_deriv_iter (S n) p = qpoly_deriv_iter n (qpoly_deriv p).
Proof.
  induction n as [|n IH]; intros p.
  - reflexivity.
  - change (qpoly_deriv_iter (S (S n)) p)
      with (qpoly_deriv (qpoly_deriv_iter (S n) p)).
    rewrite (IH p).
    reflexivity.
Qed.

(* ---------- 阶乘增长与压制引擎 ---------- *)

(* ---------- 有理数层的保序支撑件 ---------- *)

(* 自然数的有理像（与 q_fact 步进系数同形，便于定义性归约）。 *)
Definition lw0_q_of_nat (n : nat) : Q := (Z.of_nat n # 1)%Q.

(* 自然数的有理像非负。 *)
Lemma lw0_q_of_nat_nonneg : forall n : nat, QleT' 0 (lw0_q_of_nat n).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 自然数的后继有理像不小于 1。 *)
Lemma lw0_q_of_nat_ge_one : forall n : nat, QleT' 1 (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 有理像关于后继的单调性。 *)
Lemma lw0_q_of_nat_le_succ : forall n : nat,
  QleT' (lw0_q_of_nat n) (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 有理像关于加法的单调性：a 的有理像不超过 a+b 的有理像。 *)
Lemma lw0_q_of_nat_le_add : forall a b : nat,
  QleT' (lw0_q_of_nat a) (lw0_q_of_nat (a + b)%nat).
Proof.
  intros a b. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
Qed.

(* 幂关于底的单调性：0 ≤ x ≤ y 蕴含 x^n ≤ y^n。 *)
Lemma lw0_q_pow_mono_base : forall (x y : Q) (n : nat),
  QleT' 0 x -> QleT' x y -> QleT' (q_pow x n) (q_pow y n).
Proof.
  intros x y n H0 Hxy. apply Qle_to_QleT'.
  induction n as [| n IH].
  - apply Qle_refl.
  - cbn [q_pow].
    apply (Qle_trans _ (x * q_pow y n)%Q).
    + rewrite (Qmult_comm x (q_pow x n)), (Qmult_comm x (q_pow y n)).
      apply Qmult_le_compat_r.
      * exact IH.
      * exact (QleT'_to_Qle _ _ H0).
    + apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hxy).
      * apply q_pow_nonneg. exact (QleT'_to_Qle _ _ (qleT'_trans 0 x y H0 Hxy)).
Qed.

(* 幂的后继放大：x ≥ 1 蕴含 x^n ≤ x^(n+1)。 *)
Lemma lw0_q_pow_le_succ_pow : forall (x : Q) (n : nat),
  QleT' 1 x -> QleT' (q_pow x n) (q_pow x (Datatypes.S n)).
Proof.
  intros x n Hx. apply Qle_to_QleT'.
  rewrite q_pow_succ.
  apply (Qle_trans _ (1 * q_pow x n)%Q).
  - rewrite (Qmult_comm 1 (q_pow x n)), Qmult_1_r. apply Qle_refl.
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hx).
    + apply q_pow_nonneg. apply (Qle_trans 0%Q 1%Q x).
      * unfold Qle. cbn [Qnum Qden]. lia.
      * exact (QleT'_to_Qle _ _ Hx).
Qed.

(* ---------- 阶乘的因子表分解与半数底幂下界 ---------- *)

(* 阶乘的步进等式：q_fact (n+1) == (n+1)·q_fact n（系数与 lw0_q_of_nat 定义性一致）。 *)
Lemma lw0_q_fact_step : forall k : nat,
  q_fact (Datatypes.S k) == lw0_q_of_nat (Datatypes.S k) * q_fact k.
Proof. intro k. reflexivity. Qed.

(* 阶乘不小于 1。 *)
Lemma lw0_q_fact_ge_one : forall k : nat, QleT' 1 (q_fact k).
Proof.
  intro k. apply Qle_to_QleT'.
  induction k as [| k IH].
  - apply Qle_refl.
  - rewrite lw0_q_fact_step.
    apply Qmult_le_1_compat.
    + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one k)).
    + exact IH.
Qed.

(* 阶乘的双步等式：q_fact (n+2) == (n+2)·(n+1)·q_fact n。 *)
Lemma lw0_q_fact_step2 : forall k : nat,
  q_fact (Datatypes.S (Datatypes.S k)) ==
  lw0_q_of_nat (Datatypes.S (Datatypes.S k)) * lw0_q_of_nat (Datatypes.S k) * q_fact k.
Proof.
  intro k.
  transitivity (lw0_q_of_nat (Datatypes.S (Datatypes.S k)) *
                (lw0_q_of_nat (Datatypes.S k) * q_fact k))%Q.
  - reflexivity.
  - ring.
Qed.

(* 因子表尾段：(a+1)·(a+2)···(a+k)，真构造的归纳结构。 *)
Fixpoint lw0_fact_range (a k : nat) : Q :=
  match k with
  | 0%nat => 1%Q
  | Datatypes.S j => lw0_q_of_nat (a + Datatypes.S j) * lw0_fact_range a j
  end.

(* 因子表分解：q_fact (a+k) == q_fact a·(a+1)···(a+k)。 *)
Lemma lw0_q_fact_split : forall a k : nat,
  q_fact (a + k)%nat == q_fact a * lw0_fact_range a k.
Proof.
  intros a k. induction k as [| k IH].
  - rewrite Nat.add_0_r, Qmult_1_r. reflexivity.
  - cbn [lw0_fact_range].
    replace (a + Datatypes.S k)%nat with (Datatypes.S (a + k))%nat by lia.
    rewrite lw0_q_fact_step, IH. ring.
Qed.

(* 尾段因子的幂下界：(a+1)^k ≤ (a+1)·(a+2)···(a+k)，逐因子比较。 *)
Lemma lw0_fact_range_ge_pow : forall a k : nat,
  QleT' (q_pow (lw0_q_of_nat (Datatypes.S a)) k) (lw0_fact_range a k).
Proof.
  intros a k. induction k as [| k IH].
  - apply qleT'_refl.
  - apply Qle_to_QleT'.
    cbn [lw0_fact_range q_pow].
    apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S a) * lw0_fact_range a k)%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S a))
                          (q_pow (lw0_q_of_nat (Datatypes.S a)) k)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S a)) (lw0_fact_range a k)).
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ IH).
      * apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
    + apply Qmult_le_compat_r.
      * unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
      * apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S a)) k)
                           (lw0_fact_range a k)).
        -- apply q_pow_nonneg. apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
        -- exact (QleT'_to_Qle _ _ IH).
Qed.

(** 半数底幂的双倍下界：对每个自然数 m，m^m ≤ (2m)!。数学含义：因子表
    1·2···(2m) 的尾段 (m+1)···(2m) 共 m 个因子，逐个不小于 m+1 ≥ m。
    证明策略：因子表分解至尾段，尾段逐因子与 (m+1)^m 比较，再乘回前段。 *)
Lemma lw0_pow_half_le_fact_double : forall m : nat,
  QleT' (q_pow (lw0_q_of_nat m) m) (q_fact (2 * m)%nat).
Proof.
  intro m.
  apply (qleT'_trans (q_pow (lw0_q_of_nat m) m) (q_pow (lw0_q_of_nat (Datatypes.S m)) m)).
  - exact (lw0_q_pow_mono_base (lw0_q_of_nat m) (lw0_q_of_nat (Datatypes.S m)) m
      (lw0_q_of_nat_nonneg m) (lw0_q_of_nat_le_succ m)).
  - apply (qleT'_trans (q_pow (lw0_q_of_nat (Datatypes.S m)) m) (lw0_fact_range m m)).
    + exact (lw0_fact_range_ge_pow m m).
    + replace (2 * m)%nat with (m + m)%nat by lia.
      apply Qle_to_QleT'.
      rewrite lw0_q_fact_split.
      apply (Qle_trans _ (1 * lw0_fact_range m m)%Q).
      * rewrite (Qmult_comm 1 (lw0_fact_range m m)), Qmult_1_r. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one m)).
        -- apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S m)) m)
                             (lw0_fact_range m m)).
           ++ apply q_pow_nonneg. apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
           ++ exact (QleT'_to_Qle _ _ (lw0_fact_range_ge_pow m m)).
Qed.

(** 阶乘的半数底幂下界：对每个自然数 n，(n/2)^(n/2) ≤ n!，其中取半为
    Nat.div2。数学含义：n 的因子表中自 n/2 起的因子逐个不小于 n/2。
    证明策略：以 Nat.div2_odd 的奇偶方程按 Nat.odd 的布尔值分情形，
    偶情形归约到双倍下界，奇情形再乘入最后一个因子。 *)
Theorem lw0_fact_lower_growth : forall n : nat,
  QleT' (q_pow (lw0_q_of_nat (Nat.div2 n)) (Nat.div2 n)) (q_fact n).
Proof.
  intro n.
  pose proof (Nat.div2_odd n) as Hd.
  destruct (Nat.odd n) eqn:Hodd.
  - (* 情形 n 为奇数：n = 2·(n/2)+1。 *)
    cbn [Nat.b2n] in Hd |- *.
    set (m := Nat.div2 n) in *.
    rewrite Hd.
    apply (qleT'_trans (q_pow (lw0_q_of_nat m) m) (q_fact (2 * m))).
    + exact (lw0_pow_half_le_fact_double m).
    + replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
      apply Qle_to_QleT'.
      rewrite lw0_q_fact_step.
      apply (Qle_trans _ (1 * q_fact (2 * m))%Q).
      * rewrite (Qmult_comm 1 (q_fact (2 * m))), Qmult_1_r. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one (2 * m))).
        -- apply (Qlt_le_weak 0). apply q_fact_pos.
  - (* 情形 n 为偶数：n = 2·(n/2)。 *)
    cbn [Nat.b2n] in Hd |- *. rewrite Nat.add_0_r in Hd.
    set (m := Nat.div2 n) in *.
    rewrite Hd.
    exact (lw0_pow_half_le_fact_double m).
Qed.

(* ---------- 圆周率有理上界的幂被阶乘压制 ---------- *)

(* 双步推进引理：若 1 ≤ c ≤ n+1 的有理像且 c^n ≤ n!，则 c^(n+2) ≤ (n+2)!。
   由 c^(n+2) = c·(c·c^n) 与 (n+2)! = (n+2)·(n+1)·n! 逐因子放缩。 *)
Lemma lw0_q_pow_fact_step2 : forall (c : Q) (n : nat),
  QleT' 1 c ->
  QleT' c (lw0_q_of_nat (Datatypes.S n)) ->
  QleT' (q_pow c n) (q_fact n) ->
  QleT' (q_pow c (Datatypes.S (Datatypes.S n)))
        (q_fact (Datatypes.S (Datatypes.S n))).
Proof.
  intros c n H1c Hcn IH. apply Qle_to_QleT'.
  rewrite lw0_q_fact_step2, !q_pow_succ.
  rewrite <- (Qmult_assoc (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                          (lw0_q_of_nat (Datatypes.S n)) (q_fact n))%Q.
  assert (H0c : Qle 0 c).
  { apply (Qle_trans 0%Q 1%Q c).
    - unfold Qle. cbn [Qnum Qden]. lia.
    - exact (QleT'_to_Qle _ _ H1c). }
  assert (H0P : Qle 0 (q_pow c n)) by (apply q_pow_nonneg; exact H0c).
  assert (HcP : Qle (c * q_pow c n)
                    (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
  { apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) * q_pow c n)).
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hcn).
      + exact H0P.
    - rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (q_pow c n)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (q_fact n)).
      apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ IH).
      + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))). }
  assert (H0cP : Qle 0 (c * q_pow c n))
    by (apply Qmult_le_0_compat; assumption).
  assert (H0BF : Qle 0 (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
  { apply Qmult_le_0_compat.
    - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))).
    - apply (Qlt_le_weak 0). apply q_fact_pos. }
  assert (HBA : Qle (lw0_q_of_nat (Datatypes.S n))
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
  { replace (Datatypes.S (Datatypes.S n))%nat with (Datatypes.S n + 1)%nat by lia.
    exact (QleT'_to_Qle _ _ (lw0_q_of_nat_le_add (Datatypes.S n) 1)). }
  apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) * (c * q_pow c n))%Q).
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hcn).
    + exact H0cP.
  - apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S n) *
                        (lw0_q_of_nat (Datatypes.S n) * q_fact n))%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S n)) (c * q_pow c n)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S n))
                          (lw0_q_of_nat (Datatypes.S n) * q_fact n)).
      apply Qmult_le_compat_r.
      * exact HcP.
      * exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg (Datatypes.S n))).
    + apply Qmult_le_compat_r.
      * exact HBA.
      * exact H0BF.
Qed.

(** 圆周率有理上界的幂的阶乘压制（偶数族）：对每个自然数 k，
    (10/3)^(22+2k) ≤ (22+2k)!。数学含义：结合库内估计 π < 10/3
    （S10_KVQuantTrig 的 real_pi_leibniz_lt_ten_thirds），对一切偶数
    n ≥ 22，π 的上界 10/3 的 n 次幂不超过 n!。证明策略：基例以数值
    判定闭合，归纳步由双步推进引理完成。 *)
Theorem lw0_pi_bound_dominated_even : forall k : nat,
  QleT' (q_pow (10 # 3) (22 + 2 * k)%nat) (q_fact (22 + 2 * k)%nat).
Proof.
  intro k.
  induction k as [| k IH].
  - (* 基例 k = 0，即 n = 22：数值判定。 *)
    vm_compute. reflexivity.
  - (* 归纳步：由 k 到 S k，即由 n 到 n+2。 *)
    replace (22 + 2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (22 + 2 * k)))%nat by lia.
    apply (lw0_q_pow_fact_step2 (10 # 3)%Q (22 + 2 * k)%nat).
    + vm_compute. reflexivity.
    + replace (Datatypes.S (22 + 2 * k)) with (23 + 2 * k)%nat by lia.
      apply (qleT'_trans (10 # 3)%Q (lw0_q_of_nat 23)).
      * vm_compute. reflexivity.
      * apply lw0_q_of_nat_le_add.
    + exact IH.
Qed.

(** 圆周率有理上界的幂的阶乘压制（奇数族）：对每个自然数 k，
    (10/3)^(23+2k) ≤ (23+2k)!。与偶数族合取，覆盖一切 n ≥ 22。
    证明策略与偶数族相同：基例数值判定，归纳步双步推进。 *)
Theorem lw0_pi_bound_dominated_odd : forall k : nat,
  QleT' (q_pow (10 # 3) (23 + 2 * k)%nat) (q_fact (23 + 2 * k)%nat).
Proof.
  intro k.
  induction k as [| k IH].
  - (* 基例 k = 0，即 n = 23：数值判定。 *)
    vm_compute. reflexivity.
  - (* 归纳步：由 k 到 S k，即由 n 到 n+2。 *)
    replace (23 + 2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (23 + 2 * k)))%nat by lia.
    apply (lw0_q_pow_fact_step2 (10 # 3)%Q (23 + 2 * k)%nat).
    + vm_compute. reflexivity.
    + replace (Datatypes.S (23 + 2 * k)) with (24 + 2 * k)%nat by lia.
      apply (qleT'_trans (10 # 3)%Q (lw0_q_of_nat 24)).
      * vm_compute. reflexivity.
      * apply lw0_q_of_nat_le_add.
    + exact IH.
Qed.

(* 接口适配壳：契约名 qpoly 对实产 QPoly，语句面书写全件一致。 *)
Notation qpoly := QPoly.

(* ================= §2 圆周率处的三角端点值 ================= *)

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

(* ================= §3 正弦函数在区间 (0, pi) 上的正性 ================= *)

(* ---- real_eq 对 real_plus 的双边合同 ----
   逐点三角不等式：|(A+B)-(A'+B')| <= |A-A'| + |B-B'|，半额松弛 eps/2。 *)

Lemma lw0_sin_plus_eq_compat : forall a a' b b' : Real,
  real_eq a a' -> real_eq b b' ->
  real_eq (real_plus a b) (real_plus a' b').
Proof.
  intros a a' b b' Ha Hb eps Heps.
  assert (Hh : QltT 0 (eps * (1 # 2))%Q).
  { apply Qlt_to_QltT.
    assert (Hlt : (0 < eps)%Q) by (apply QltT_to_Qlt; exact Heps).
    assert (Hc : (0 < (1 # 2))%Q) by (unfold Qlt; reflexivity).
    assert (Hm : (0 * (1 # 2) < eps * (1 # 2))%Q)
      by (apply (proj2 (Qmult_lt_r 0 eps (1 # 2) Hc)); exact Hlt).
    assert (Hcz : ((0 * (1 # 2)) == 0)%Q) by ring.
    setoid_rewrite Hcz in Hm.
    exact Hm. }
  destruct (Ha (eps * (1 # 2))%Q Hh) as [N1 HN1].
  destruct (Hb (eps * (1 # 2))%Q Hh) as [N2 HN2].
  destruct a as [u Hu]. destruct a' as [u' Hu'].
  destruct b as [v Hv]. destruct b' as [v' Hv'].
  exists (Nat.max N1 N2). intros n Hn.
  assert (Hn1 : NatLe N1 n).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_l.
    - apply NatLe_drop. exact Hn. }
  assert (Hn2 : NatLe N2 n).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_r.
    - apply NatLe_drop. exact Hn. }
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  change (QltT (Qabs ((u n + v n) - (u' n + v' n))) eps).
  apply Qlt_to_QltT.
  assert (H1 : Qlt (Qabs (u n - u' n)) (eps * (1 # 2)))
    by (apply QltT_to_Qlt; exact HN1).
  assert (H2 : Qlt (Qabs (v n - v' n)) (eps * (1 # 2)))
    by (apply QltT_to_Qlt; exact HN2).
  assert (Hrw : (((u n + v n) - (u' n + v' n))
               == ((u n - u' n) + (v n - v' n)))%Q) by ring.
  setoid_rewrite Hrw.
  apply (Qle_lt_trans _ (Qabs (u n - u' n) + Qabs (v n - v' n))%Q _).
  - apply Qabs_triangle.
  - assert (Hs : Qlt (Qabs (u n - u' n) + Qabs (v n - v' n))
                     ((eps * (1 # 2)) + (eps * (1 # 2))))
      by (apply Qplus_lt_compat; [exact H1 | exact H2]).
    assert (Hrw2 : (((eps * (1 # 2)) + (eps * (1 # 2))) == eps)%Q) by ring.
    setoid_rewrite Hrw2 in Hs.
    exact Hs.
Qed.

(* ---- 常数差的定义性算术：a + (-b) 逐点等于 a-b ---- *)

Lemma lw0_sin_const_plus_opp_const : forall a b : Q,
  real_eq (real_plus (real_const a) (real_opp (real_const b)))
          (real_const (a - b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  change ((a + (- b) - (a - b)) == 0)%Q.
  ring.
Qed.

(* ---- 10/3 - 4/3 == 2：常数桥（gap 二分右岸用） ---- *)

Lemma lw0_sin_ten_thirds_bridge :
  real_eq (real_plus (real_const (10 / 3)) (real_opp (real_const (4 / 3))))
          (real_const 2).
Proof.
  apply real_eq_of_zero_diff. intro n.
  vm_compute. reflexivity.
Qed.

(* ---- 由 t < pi_geom 构造 0 < pi_geom - t ----
   路径：real_lt_plus_translate 给出 (-t) + t < (-t) + pi_geom，
   左端经 real_plus_opp 等于零，右端经 real_plus_comm 换序。 *)

Lemma lw0_sin_zero_lt_pi_minus : forall X : Real,
  real_lt X real_pi_geom ->
  real_lt real_zero (real_plus real_pi_geom (real_opp X)).
Proof.
  intros X Hp.
  apply (real_eq_lt_lt real_zero
    (real_plus (real_opp X) X)
    (real_plus real_pi_geom (real_opp X))).
  - apply (real_eq_trans real_zero
      (real_plus X (real_opp X)) (real_plus (real_opp X) X)).
    + apply (real_eq_sym _ _ (real_plus_opp X)).
    + apply real_plus_comm.
  - apply (real_lt_eq_lt
      (real_plus (real_opp X) X)
      (real_plus (real_opp X) real_pi_geom)
      (real_plus real_pi_geom (real_opp X))).
    + apply (real_lt_plus_translate (real_opp X) X real_pi_geom Hp).
    + apply real_plus_comm.
Qed.

(* ---- 由 4/3 < t 与 pi_geom < 10/3 构造 pi_geom - t < 2 ---- *)

Lemma lw0_sin_pi_minus_lt_two : forall X : Real,
  real_lt (real_const (4 / 3)) X ->
  real_lt (real_plus real_pi_geom (real_opp X)) (real_const 2).
Proof.
  intros X H43.
  apply (real_lt_eq_lt
    (real_plus real_pi_geom (real_opp X))
    (real_plus (real_const (10 / 3)) (real_opp (real_const (4 / 3))))
    (real_const 2)).
  - apply (real_lt_plus_compat real_pi_geom (real_const (10 / 3))
             (real_opp X) (real_opp (real_const (4 / 3)))).
    + apply real_pi_geom_lt_ten_thirds.
    + apply (real_opp_lt_compat (real_const (4 / 3)) X H43).
  - apply lw0_sin_ten_thirds_bridge.
Qed.

(* ---- gap 二分：任意实数落在 X < 2 或 4/3 < X 之一 ----
   在 1/12 精度封住 cauchy 尾，以 t_N 与 5/3 的 Qcompare 三分；
   5/3 为 4/3 与 2 的中点，两岸各留 1/4 的实数间隙。 *)

Lemma lw0_gap_dichotomy : forall X : Real,
  Or (real_lt X (real_const 2)) (real_lt (real_const (4 / 3)) X).
Proof.
  intros X. destruct X as [u Hu].
  assert (Hpos12 : QltT 0 (1 # 12)%Q) by (apply Qlt_to_QltT; unfold Qlt; reflexivity).
  assert (Hpos6 : QltT 0 (1 # 6)%Q) by (apply Qlt_to_QltT; unfold Qlt; reflexivity).
  assert (Hc43 : ((4 / 3) == (4 # 3))%Q) by (vm_compute; reflexivity).
  destruct (Hu (1 # 12)%Q Hpos12) as [N HN].
  assert (HNN : NatLe N N) by (apply NatLe_lift, Nat.le_refl).
  destruct ((u N ?= (5 # 3))%Q) eqn:Hcmp.
  - (* 情形 u N = 5/3：u m 落在 (5/3 - 1/12, 5/3 + 1/12)，两岸皆通，取右岸 *)
    right. exists (1 # 6)%Q. split.
    + exact Hpos6.
    + exists N. intros m Hm.
      specialize (HN m N Hm HNN).
      change (projT1 (real_const (4 / 3)) m) with ((4 / 3)%Q).
      change (projT1 (existT (fun u0 : Qseq => cauchy u0) u Hu) m) with (u m).
      apply Qlt_to_QltT.
      assert (Habs : Qlt (Qabs (u m - u N)) (1 # 12))
        by (apply QltT_to_Qlt; exact HN).
      assert (Hq12 : Qlt 0 (1 # 12)) by (apply QltT_to_Qlt; exact Hpos12).
      assert (Hlow : Qlt (- (1 # 12)) (u m - u N))
        by (apply (q_abs_gt_neg _ _ Hq12 Habs)).
      assert (Hum : Qlt (u N + (- (1 # 12))) (u m)).
      { assert (H1 : Qlt ((- (1 # 12)) + u N) ((u m - u N) + u N))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact Hlow).
        assert (Hr1 : (((- (1 # 12)) + u N) == (u N + (- (1 # 12))))%Q) by ring.
        setoid_rewrite Hr1 in H1.
        assert (Hr2 : (((u m - u N) + u N) == u m)%Q) by ring.
        setoid_rewrite Hr2 in H1.
        exact H1. }
      assert (Hge : Qle ((5 # 3)) (u N)).
      { destruct (Qlt_le_dec (u N) (5 # 3)) as [Hc' | Hc'].
        - exfalso.
          assert (Hcc : (u N ?= 5 # 3)%Q = Lt)
            by (exact (proj1 (Qlt_alt (u N) (5 # 3)) Hc')).
          rewrite Hcmp in Hcc. discriminate Hcc.
        - exact Hc'. }
      assert (Hlelt : forall a0 b0 c0 d0 : Q,
        Qle a0 b0 -> Qlt (b0 + c0) d0 -> Qlt (a0 + c0) d0).
      { intros a0 b0 c0 d0 Hab Hbc.
        destruct (Qlt_le_dec a0 b0) as [Hl | Hl'].
        - apply (Qlt_trans _ (b0 + c0)).
          + apply (proj2 (Qplus_lt_l _ _ _)). exact Hl.
          + exact Hbc.
        - assert (Heqab : a0 == b0) by (apply Qle_antisym; [exact Hab | exact Hl']).
          assert (Hrc : ((a0 + c0) == (b0 + c0))%Q)
            by (rewrite Heqab; ring).
          setoid_rewrite Hrc.
          exact Hbc. }
      assert (Hge2 : Qlt ((5 # 3) + (- (1 # 12))) (u m))
        by (apply (Hlelt (5 # 3) (u N) (- (1 # 12)) (u m) Hge Hum)).
      assert (Hlit : Qlt ((4 # 3) + (1 # 6)) ((5 # 3) + (- (1 # 12))))
        by (unfold Qlt; reflexivity).
      assert (Hfin : Qlt ((4 # 3) + (1 # 6) + (- (4 # 3)))
                          (u m + (- (4 # 3))))
        by (apply (proj2 (Qplus_lt_l _ _ _));
            apply (Qlt_trans _ ((5 # 3) + (- (1 # 12))));
            [exact Hlit | exact Hge2]).
      assert (Hr3 : (((4 # 3) + (1 # 6) + (- (4 # 3))) == (1 # 6))%Q) by ring.
      setoid_rewrite Hr3 in Hfin.
      assert (Hr4 : ((u m + (- (4 # 3))) == (u m - (4 # 3)))%Q) by ring.
      setoid_rewrite Hr4 in Hfin.
      setoid_rewrite Hc43.
      exact Hfin.
  - (* 情形 u N < 5/3：取左岸 X < 2 *)
    left. exists (1 # 6)%Q. split.
    + exact Hpos6.
    + exists N. intros m Hm.
      specialize (HN m N Hm HNN).
      change (projT1 (real_const 2) m) with 2%Q.
      change (projT1 (existT (fun u0 : Qseq => cauchy u0) u Hu) m) with (u m).
      apply Qlt_to_QltT.
      assert (Habs : Qlt (Qabs (u m - u N)) (1 # 12))
        by (apply QltT_to_Qlt; exact HN).
      (* 上岸：d < 0 时 d < 1/12 直接；d >= 0 时 |d| == d 逐字替换 *)
      assert (Hub : Qlt (u m - u N) (1 # 12)).
      { destruct (Qlt_le_dec (u m - u N) 0) as [Hnegd | Hnond].
        - apply (Qlt_le_trans _ 0 _).
          + exact Hnegd.
          + apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpos12.
        - assert (Habsd : Qabs (u m - u N) == (u m - u N))
            by (apply Qabs_pos; exact Hnond).
          rewrite Habsd in Habs. exact Habs. }
      assert (Hum : Qlt (u m) (u N + (1 # 12))).
      { assert (H1 : Qlt ((u m - u N) + u N) ((1 # 12) + u N))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact Hub).
        assert (Hr1 : (((u m - u N) + u N) == u m)%Q) by ring.
        setoid_rewrite Hr1 in H1.
        assert (Hr2 : (((1 # 12) + u N) == (u N + (1 # 12)))%Q) by ring.
        setoid_rewrite Hr2 in H1.
        exact H1. }
      assert (HltN : Qlt (u N) ((5 # 3))) by (unfold Qlt; exact Hcmp).
      assert (Hlit : Qlt ((5 # 3) + (1 # 12)) (2 - (1 # 6)))
        by (unfold Qlt; reflexivity).
      assert (Hum2 : Qlt (u m) ((5 # 3) + (1 # 12))).
      { assert (H1' : Qlt (u N + (1 # 12)) ((5 # 3) + (1 # 12)))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact HltN).
        apply (Qlt_trans _ (u N + (1 # 12))).
        - exact Hum.
        - exact H1'. }
      assert (Hfin : Qlt (u m + (1 # 6)) (2 - (1 # 6) + (1 # 6)))
        by (apply (proj2 (Qplus_lt_l _ _ _));
            apply (Qlt_trans _ ((5 # 3) + (1 # 12)));
            [exact Hum2 | exact Hlit]).
      assert (Hr3 : ((2 - (1 # 6) + (1 # 6)) == 2)%Q) by ring.
      setoid_rewrite Hr3 in Hfin.
      assert (Hfin2 : Qlt ((1 # 6) + u m) ((2 - u m) + u m)).
      { assert (Hr4 : (((2 - u m) + u m) == 2)%Q) by ring.
        setoid_rewrite Hr4.
        assert (Hr5 : (((1 # 6) + u m) == (u m + (1 # 6)))%Q) by ring.
        setoid_rewrite Hr5.
        exact Hfin. }
      exact (proj1 (Qplus_lt_l _ _ _) Hfin2).
  - (* 情形 u N > 5/3：取右岸 4/3 < X *)
    right. exists (1 # 6)%Q. split.
    + exact Hpos6.
    + exists N. intros m Hm.
      specialize (HN m N Hm HNN).
      change (projT1 (real_const (4 / 3)) m) with ((4 / 3)%Q).
      change (projT1 (existT (fun u0 : Qseq => cauchy u0) u Hu) m) with (u m).
      apply Qlt_to_QltT.
      assert (Habs : Qlt (Qabs (u m - u N)) (1 # 12))
        by (apply QltT_to_Qlt; exact HN).
      assert (Hq12 : Qlt 0 (1 # 12)) by (apply QltT_to_Qlt; exact Hpos12).
      assert (Hlow : Qlt (- (1 # 12)) (u m - u N))
        by (apply (q_abs_gt_neg _ _ Hq12 Habs)).
      assert (Hum : Qlt (u N + (- (1 # 12))) (u m)).
      { assert (H1 : Qlt ((- (1 # 12)) + u N) ((u m - u N) + u N))
          by (apply (proj2 (Qplus_lt_l _ _ _)); exact Hlow).
        assert (Hr1 : (((- (1 # 12)) + u N) == (u N + (- (1 # 12))))%Q) by ring.
        setoid_rewrite Hr1 in H1.
        assert (Hr2 : (((u m - u N) + u N) == u m)%Q) by ring.
        setoid_rewrite Hr2 in H1.
        exact H1. }
      assert (Hge : Qle ((5 # 3)) (u N)).
      { destruct (Qlt_le_dec (u N) (5 # 3)) as [Hc' | Hc'].
        - exfalso.
          assert (Hcc : (u N ?= 5 # 3)%Q = Lt)
            by (exact (proj1 (Qlt_alt _ _) Hc')).
          congruence.
        - exact Hc'. }
      assert (Hlelt : forall a0 b0 c0 d0 : Q,
        Qle a0 b0 -> Qlt (b0 + c0) d0 -> Qlt (a0 + c0) d0).
      { intros a0 b0 c0 d0 Hab Hbc.
        destruct (Qlt_le_dec a0 b0) as [Hl | Hl'].
        - apply (Qlt_trans _ (b0 + c0)).
          + apply (proj2 (Qplus_lt_l _ _ _)). exact Hl.
          + exact Hbc.
        - assert (Heqab : a0 == b0) by (apply Qle_antisym; [exact Hab | exact Hl']).
          assert (Hrc : ((a0 + c0) == (b0 + c0))%Q)
            by (rewrite Heqab; ring).
          setoid_rewrite Hrc.
          exact Hbc. }
      assert (Hge2 : Qlt ((5 # 3) + (- (1 # 12))) (u m))
        by (apply (Hlelt (5 # 3) (u N) (- (1 # 12)) (u m) Hge Hum)).
      assert (Hlit : Qlt ((4 # 3) + (1 # 6)) ((5 # 3) + (- (1 # 12))))
        by (unfold Qlt; reflexivity).
      assert (Hfin : Qlt ((4 # 3) + (1 # 6) + (- (4 # 3)))
                          (u m + (- (4 # 3))))
        by (apply (proj2 (Qplus_lt_l _ _ _));
            apply (Qlt_trans _ ((5 # 3) + (- (1 # 12))));
            [exact Hlit | exact Hge2]).
      assert (Hr3 : (((4 # 3) + (1 # 6) + (- (4 # 3))) == (1 # 6))%Q) by ring.
      setoid_rewrite Hr3 in Hfin.
      assert (Hr4 : ((u m + (- (4 # 3))) == (u m - (4 # 3)))%Q) by ring.
      setoid_rewrite Hr4 in Hfin.
      setoid_rewrite Hc43.
      exact Hfin.
Qed.

(* ---- reflection：sin X == sin(pi_geom - X) ----
   和角公式一次实例化：sin(pi + (-X)) = sin(pi)cos(-X) + cos(pi)sin(-X)，
   端点值 sin(pi) = 0、cos(pi) = -1 代入后余
   0·cos(-X) + (-1)·sin(-X) == 0 + (-1)·(-sin X) == sin X。 *)

Lemma lw0_sin_reflection : forall X : Real,
  real_eq (cauchy_real_sin X)
          (cauchy_real_sin (real_plus real_pi_geom (real_opp X))).
Proof.
  intros X. apply real_eq_sym.
  apply (real_eq_trans
    (cauchy_real_sin (real_plus real_pi_geom (real_opp X)))
    (real_plus (real_mult (cauchy_real_sin real_pi_geom)
                           (cauchy_real_cos (real_opp X)))
               (real_mult (cauchy_real_cos real_pi_geom)
                          (cauchy_real_sin (real_opp X))))
    (cauchy_real_sin X)).
  - apply rs_add_sin.
  - apply (real_eq_trans
      (real_plus (real_mult (cauchy_real_sin real_pi_geom)
                             (cauchy_real_cos (real_opp X)))
                 (real_mult (cauchy_real_cos real_pi_geom)
                            (cauchy_real_sin (real_opp X))))
      (real_plus real_zero (cauchy_real_sin X))
      (cauchy_real_sin X)).
    + apply lw0_sin_plus_eq_compat.
      * (* sin(pi)·cos(-X) == 0·cos(-X) == 0 *)
        apply (real_eq_trans
          (real_mult (cauchy_real_sin real_pi_geom)
                     (cauchy_real_cos (real_opp X)))
          (real_mult real_zero (cauchy_real_cos (real_opp X)))
          real_zero).
        -- apply (qtr_mult_eq_compat_l (cauchy_real_sin real_pi_geom)
                    real_zero (cauchy_real_cos (real_opp X))
                    b5p_sin_pi_geom_zero).
        -- apply (real_eq_trans
             (real_mult real_zero (cauchy_real_cos (real_opp X)))
             (real_mult (cauchy_real_cos (real_opp X)) real_zero)
             real_zero).
           ++ apply real_mult_comm.
           ++ apply real_mult_zero.
      * (* cos(pi)·sin(-X) == (-sin X)·(-1) == sin X *)
        apply (real_eq_trans
          (real_mult (cauchy_real_cos real_pi_geom)
                     (cauchy_real_sin (real_opp X)))
          (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))
          (cauchy_real_sin X)).
        -- apply (real_eq_trans
             (real_mult (cauchy_real_cos real_pi_geom)
                        (cauchy_real_sin (real_opp X)))
             (real_mult (real_opp real_one) (cauchy_real_sin (real_opp X)))
             (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))).
           ++ apply (qtr_mult_eq_compat_l (cauchy_real_cos real_pi_geom)
                       (real_opp real_one) (cauchy_real_sin (real_opp X))
                       b5p_cos_pi_geom_neg_one).
           ++ apply (real_eq_trans
                (real_mult (real_opp real_one) (cauchy_real_sin (real_opp X)))
                (real_mult (cauchy_real_sin (real_opp X)) (real_opp real_one))
                (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))).
              ** apply real_mult_comm.
              ** apply (qtr_mult_eq_compat_l (cauchy_real_sin (real_opp X))
                          (real_opp (cauchy_real_sin X)) (real_opp real_one)
                          (real_sin_opp X)).
        -- (* (−sin X)·(−1) == sin X：负负相消，库内乘法负元引理两级装配 *)
           apply (real_eq_trans
             (real_mult (real_opp (cauchy_real_sin X)) (real_opp real_one))
             (real_opp (real_opp (cauchy_real_sin X)))
             (cauchy_real_sin X)).
           ++ apply real_mult_opp_one_l.
           ++ apply real_opp_opp.
    + apply (real_eq_trans
        (real_plus real_zero (cauchy_real_sin X))
        (real_plus (cauchy_real_sin X) real_zero)
        (cauchy_real_sin X)).
      * apply real_plus_comm.
      * apply real_plus_zero.
Qed.

(* ---- 主语句：sin 在 (0, pi_geom) 内逐点为正 ----
   gap 二分：X < 2 支由库内 (0,2) 段正性直接供给；
   4/3 < X 支：pi_geom - X < 10/3 - 4/3 = 2 且 pi_geom - X > 0，
   reflection 把正性从 sin(pi_geom - X) 传回 sin X。 *)

Lemma lw0_sin_pos_pi : forall X : Real,
  real_lt real_zero X -> real_lt X real_pi_geom ->
  real_lt real_zero (cauchy_real_sin X).
Proof.
  intros X H0 Hp.
  destruct (lw0_gap_dichotomy X) as [H2 | H43].
  - exact (real_sin_pos_lt_two X H0 H2).
  - assert (HY : real_lt real_zero
                   (cauchy_real_sin (real_plus real_pi_geom (real_opp X)))).
    { apply (real_sin_pos_lt_two (real_plus real_pi_geom (real_opp X))).
      - apply lw0_sin_zero_lt_pi_minus. exact Hp.
      - apply lw0_sin_pi_minus_lt_two. exact H43. }
    exact (real_lt_eq_lt real_zero
            (cauchy_real_sin (real_plus real_pi_geom (real_opp X)))
            (cauchy_real_sin X)
            HY (real_eq_sym _ _ (lw0_sin_reflection X))).
Qed.

(* ---------- W 序列的正性、上界与阶乘压制（[1, 2] 下界备料） ---------- *)


(* ---------- 有理数与自然数小件 ---------- *)
(* 同物异名去重（方案①）：lw0_q_of_nat / lw0_q_of_nat_nonneg /
   lw0_q_fact_step / lw0_q_pow_mono_base 四名直接复用 LW0FactGrowth 在库件，
   本件不再自建；本件保留的三条真新语句 lw0_q_of_nat_succ / lw0_q_of_nat_add /
   lw0_q_of_nat_le_mono 见语句对照表记录。 *)

Lemma lw0_q_of_nat_le_mono : forall a b : nat, (a <= b)%nat -> QleT' (lw0_q_of_nat a) (lw0_q_of_nat b).
Proof. intros a b H. apply Qle_to_QleT'. unfold lw0_q_of_nat, Qle. simpl. lia. Qed.

Lemma lw0_q_of_nat_succ : forall k : nat, lw0_q_of_nat (Datatypes.S k) == lw0_q_of_nat k + 1.
Proof.
  intro k. unfold lw0_q_of_nat, Qeq. cbn [Qnum Qden Qplus]. lia.
Qed.

Lemma lw0_q_of_nat_add : forall a b : nat,
  lw0_q_of_nat (a + b)%nat == lw0_q_of_nat a + lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qeq. cbn [Qnum Qden Qplus]. lia.
Qed.

Lemma lw0_q_pow_S : forall (x : Q) (k : nat),
  q_pow x (Datatypes.S k) == x * q_pow x k.
Proof. intros x k. reflexivity. Qed.

Lemma lw0_q_pow_mult : forall (x y : Q) (k : nat),
  q_pow x k * q_pow y k == q_pow (x * y) k.
Proof.
  intros x y k. induction k as [| k IH].
  - reflexivity.
  - rewrite !lw0_q_pow_S.
    transitivity ((x * y) * (q_pow x k * q_pow y k))%Q.
    + ring.
    + rewrite IH. ring.
Qed.

Lemma lw0_q_pow_pos : forall (x : Q) (k : nat), QltT 0 x -> QltT 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - reflexivity.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. exact Hx.
    + apply QltT_to_Qlt. exact IH.
Qed.

Lemma lw0_q_fact_ne0 : forall k : nat, ~ (q_fact k == 0).
Proof.
  intro k. intro Hne. apply (qltT_not_eq_zero (q_fact k)).
  - apply Qlt_to_QltT. apply q_fact_pos.
  - exact Hne.
Qed.

Lemma lw0_ltT_leT_trans : forall x y z : Q,
  QltT x y -> QleT' y z -> QltT x z.
Proof.
  intros x y z H1 H2. apply Qlt_to_QltT.
  apply QltT_to_Qlt in H1. apply QleT'_to_Qle in H2. lra.
Qed.

Lemma lw0_leT'_ltT_trans : forall x y z : Q,
  QleT' x y -> QltT y z -> QltT x z.
Proof.
  intros x y z H1 H2. apply Qlt_to_QltT.
  apply QleT'_to_Qle in H1. apply QltT_to_Qlt in H2. lra.
Qed.

Lemma lw0_Qabs_pos_eq : forall x : Q, QleT' 0 x -> Qabs x == x.
Proof. intros x H. apply Qabs_pos. apply QleT'_to_Qle. exact H. Qed.

Lemma lw0_QltT_le : forall x : Q, QltT 0 x -> QleT' 0 x.
Proof. intros x H. apply Qle_to_QleT'. apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact H. Qed.

Lemma lw0_Qlt_le : forall x : Q, Qlt 0 x -> QleT' 0 x.
Proof. intros x H. apply Qle_to_QleT'. apply (Qlt_le_weak 0). exact H. Qed.

Lemma lw0_qmul_le0T : forall a b : Q, QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof. intros a b Ha Hb. apply Qle_to_QleT'.
  apply Qmult_le_0_compat; apply QleT'_to_Qle; assumption. Qed.

Lemma lw0_qcompat4 : forall w x y z : Q,
  QleT' 0 w -> QleT' w x -> QleT' 0 y -> QleT' y z -> QleT' (w * y) (x * z).
Proof. intros w x y z H1 H2 H3 H4. apply Qle_to_QleT'.
  apply Qmult_le_compat_nonneg; split; apply QleT'_to_Qle; assumption. Qed.

Lemma lw0_qcompat_r : forall x y z : Q,
  QleT' x y -> QleT' 0 z -> QleT' (x * z) (y * z).
Proof. intros x y z H1 H2. apply Qle_to_QleT'.
  apply Qmult_le_compat_r; apply QleT'_to_Qle; assumption. Qed.

Lemma lw0_qcompat_l : forall x y z : Q,
  QleT' x y -> QleT' 0 z -> QleT' 0 x -> QleT' (z * x) (z * y).
Proof. intros x y z H1 H2 H3. apply Qle_to_QleT'.
  apply (Qmult_le_compat_nonneg z z x y).
  - split; apply QleT'_to_Qle; [ exact H2 | apply qleT'_refl ].
  - split; apply QleT'_to_Qle; [ exact H3 | exact H1 ].
Qed.

Lemma lw0_opp_le_swap : forall x y : Q, QleT' x y -> QleT' (Qopp y) (Qopp x).
Proof.
  intros x y H. apply Qle_to_QleT'. apply QleT'_to_Qle in H. lra.
Qed.

Lemma lw0_q_pow_nonnegT : forall (x : Q) (k : nat), QleT' 0 x -> QleT' 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - apply lw0_qmul_le0T.
    + exact Hx.
    + exact IH.
Qed.

Lemma lw0_sub_lt0 : forall x y : Q, QltT y x -> QltT 0 (x - y).
Proof. intros x y H. apply Qlt_to_QltT. apply QltT_to_Qlt in H. lra. Qed.

Lemma lw0_sub_le0T : forall x y : Q, QleT' y x -> QleT' 0 (x - y).
Proof.
  intros x y H. apply Qle_to_QleT'. apply QleT'_to_Qle in H. lra.
Qed.

Lemma lw0_half_pos : forall x : Q, QltT 0 x -> QltT 0 (x / 2).
Proof.
  intros x Hx. apply (qltT_shift_div_lT 0 x (2#1)).
  - exact qltT_0_2.
  - replace (0 * (2#1))%Q with 0%Q by reflexivity. apply Hx.
Qed.

(* —— 补充小件：q_of_nat 正性/非零、乘正因子严格化、q_pow 1、Q 乘非零 —— *)
Lemma lw0_q_of_nat_lt0T_S : forall m : nat, QltT 0 (lw0_q_of_nat (Datatypes.S m)).
Proof.
  intro m. apply (qltT_leT'_ltT 0 1 (lw0_q_of_nat (Datatypes.S m)) (qltT_0_1)).
  apply lw0_q_of_nat_ge_one.
Qed.

Lemma lw0_q_of_nat_lt0T : forall m : nat, (1 <= m)%nat -> QltT 0 (lw0_q_of_nat m).
Proof.
  intros m Hm. destruct m as [| m']; [ lia | apply lw0_q_of_nat_lt0T_S ].
Qed.


Lemma lw0_mul_lt_one : forall z x : Q, Qlt 0 z -> Qlt x 1 -> Qlt (z * x) z.
Proof.
  intros z x Hz Hx1.
  pose proof (Qmult_lt_compat_r x 1 z Hz Hx1) as Hraw.
  rewrite (Qmult_comm x z) in Hraw. rewrite (Qmult_1_l z) in Hraw.
  exact Hraw.
Qed.

Lemma lw0_q_pow_one : forall j : nat, q_pow 1%Q j == 1%Q.
Proof.
  intro j. induction j as [| j IH].
  - reflexivity.
  - rewrite lw0_q_pow_S, IH. reflexivity.
Qed.

Lemma lw0_div_lt : forall x y z : Q,
  QltT 0 z -> QltT x (y * z) -> QltT (x / z) y.
Proof.
  intros x y z Hz Hlt.
  assert (Hz0 : z == 0 -> False) by (apply qltT_not_eq_zero; exact Hz).
  assert (Hpos : Qlt 0 (/ z)) by (apply Qinv_lt_0_compat; apply QltT_to_Qlt; exact Hz).
  apply Qlt_to_QltT. apply QltT_to_Qlt in Hlt.
  unfold Qdiv.
  pose proof (Qmult_lt_compat_r x (y * z) (/ z) Hpos Hlt) as Hfin.
  rewrite <- (Qmult_assoc y z (/ z)), (Qmult_inv_r z Hz0), Qmult_1_r in Hfin.
  exact Hfin.
Qed.

Lemma lw0_inv_le : forall x y : Q,
  QltT 0 x -> QltT 0 y -> QleT' x y -> QleT' (/ y) (/ x).
Proof.
  intros x y Hx Hy Hle.
  assert (Hx0 : x == 0 -> False) by (apply qltT_not_eq_zero; exact Hx).
  assert (Hy0 : y == 0 -> False) by (apply qltT_not_eq_zero; exact Hy).
  assert (Hpos : QleT' 0 ((/ x) * (/ y))).
  { apply lw0_qmul_le0T; apply lw0_Qlt_le; apply Qinv_lt_0_compat, QltT_to_Qlt;
      [ exact Hx | exact Hy ]. }
  apply (qleT'_trans (/ y) (x * ((/ x) * (/ y))) (/ x)).
  - apply qeq_leT'.
    rewrite (Qmult_assoc x (/ x) (/ y)), (Qmult_inv_r x Hx0). ring.
  - apply (qleT'_trans (x * ((/ x) * (/ y))) (y * ((/ x) * (/ y))) (/ x)).
    + apply (lw0_qcompat_r x y ((/ x) * (/ y)) Hle Hpos).
    + apply qeq_leT'.
      rewrite (Qmult_comm y ((/ x) * (/ y))), <- (Qmult_assoc (/ x) (/ y) y).
      rewrite (Qmult_comm (/ y) y), (Qmult_inv_r y Hy0). ring.
Qed.

Lemma lw0_div_le_mono : forall x a b : Q,
  QltT 0 x -> QltT 0 a -> QleT' a b -> QleT' (x / b) (x / a).
Proof.
  intros x a b Hx Ha Hab.
  assert (Hbpos : QltT 0 b) by (apply (qltT_leT'_ltT 0 a b); [ exact Ha | exact Hab ]).
  apply (qleT'_trans (x / b) ((/ b) * x) (x / a)).
  - apply qeq_leT'. unfold Qdiv. ring.
  - apply (qleT'_trans ((/ b) * x) ((/ a) * x) (x / a)).
    + apply lw0_qcompat_r.
      * apply lw0_inv_le; [ exact Ha | exact Hbpos | exact Hab ].
      * apply lw0_QltT_le. exact Hx.
    + apply qeq_leT'. unfold Qdiv. ring.
Qed.

(* ---------- W 序列的 Beta 闭式与正性 ---------- *)

Definition lw0_Wb (b q : Q) (n j : nat) : Q :=
  q_pow b n * q_pow q (2*n + 2*j + 2) * q_fact (n + 2*j + 1) /
  (q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2)).

Lemma lw0_Wb_pos : forall (b q : Q) (n j : nat),
  QltT 0 b -> QltT 0 q -> QltT 0 (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq.
  assert (Hnum : Qlt 0 (q_pow b n * q_pow q (2*n + 2*j + 2) * q_fact (n + 2*j + 1))).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; apply QltT_to_Qlt;
        [ apply lw0_q_pow_pos; exact Hb | apply lw0_q_pow_pos; exact Hq ].
    - apply q_fact_pos. }
  assert (Hden : Qlt 0 (q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))).
  { apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; apply q_fact_pos | apply q_fact_pos ]. }
  unfold lw0_Wb, Qdiv. apply Qlt_to_QltT. apply Qmult_lt_0_compat.
  - exact Hnum.
  - apply Qinv_lt_0_compat. exact Hden.
Qed.

Lemma lw0_Wb_nonneg : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QleT' 0 q -> QleT' 0 (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq. unfold lw0_Wb, Qdiv.
  apply lw0_qmul_le0T.
  - apply lw0_qmul_le0T.
    + apply lw0_qmul_le0T.
      * exact (lw0_q_pow_nonnegT b n Hb).
      * exact (lw0_q_pow_nonnegT q (2*n + 2*j + 2)%nat Hq).
    + exact (lw0_Qlt_le (q_fact (n + 2*j + 1)) (q_fact_pos (n + 2*j + 1))).
  - apply lw0_Qlt_le. apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat;
      [ apply Qmult_lt_0_compat; apply q_fact_pos | apply q_fact_pos ].
Qed.

(* 递减比值的闭式：W_{j+1} == W_j · q²(n+2j+2)(n+2j+3)/((2j+2)(2j+3)(2n+2j+3)(2n+2j+4)) *)
Lemma lw0_Wb_ratio_eq : forall (b q : Q) (n j : nat),
  lw0_Wb b q n (Datatypes.S j) ==
  lw0_Wb b q n j *
  (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
   (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
    lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
Proof.
  intros b q n j.
  assert (E1 : q_fact (n + 2 * Datatypes.S j + 1)%nat ==
               lw0_q_of_nat (n + 2*j + 3) * lw0_q_of_nat (n + 2*j + 2) * q_fact (n + 2*j + 1)).
  { replace (n + 2 * Datatypes.S j + 1)%nat with (Datatypes.S (n + 2*j + 2))%nat by lia.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (n + 2*j + 2))%nat with (n + 2*j + 3)%nat by lia.
    replace (n + 2 * j + 2)%nat with (Datatypes.S (n + 2*j + 1))%nat by lia.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (Datatypes.S (n + 2*j + 1)))%nat with (n + 2*j + 3)%nat by lia.
    replace (Datatypes.S (n + 2*j + 1))%nat with (n + 2*j + 2)%nat by lia.
    ring. }
  assert (E2 : q_fact (2 * Datatypes.S j + 1)%nat ==
               lw0_q_of_nat (2*j + 3) * lw0_q_of_nat (2*j + 2) * q_fact (2*j + 1)).
  { replace (2 * Datatypes.S j + 1)%nat with (Datatypes.S (2 * j + 2))%nat by lia.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (2 * j + 2))%nat with (2 * j + 3)%nat by lia.
    replace (2 * j + 2)%nat with (Datatypes.S (2 * j + 1))%nat by lia.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (Datatypes.S (2 * j + 1)))%nat with (2 * j + 3)%nat by lia.
    replace (Datatypes.S (2 * j + 1))%nat with (2 * j + 2)%nat by lia.
    ring. }
  assert (E3 : q_fact (2 * n + 2 * Datatypes.S j + 2)%nat ==
               lw0_q_of_nat (2*n + 2*j + 4) * lw0_q_of_nat (2*n + 2*j + 3) * q_fact (2*n + 2*j + 2)).
  { replace (2 * n + 2 * Datatypes.S j + 2)%nat with (Datatypes.S (2 * n + 2*j + 3))%nat by lia.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (2 * n + 2*j + 3))%nat with (2 * n + 2*j + 4)%nat by lia.
    replace (2 * n + 2*j + 3)%nat with (Datatypes.S (2 * n + 2*j + 2))%nat by lia.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (Datatypes.S (2 * n + 2*j + 2)))%nat with (2 * n + 2*j + 4)%nat by lia.
    replace (Datatypes.S (2 * n + 2*j + 2))%nat with (2 * n + 2*j + 3)%nat by lia.
    ring. }
  assert (E4 : q_pow q (2 * n + 2 * Datatypes.S j + 2)%nat ==
               q * q * q_pow q (2*n + 2*j + 2)%nat).
  { replace (2 * n + 2 * Datatypes.S j + 2)%nat
      with (Datatypes.S (Datatypes.S (2 * n + 2 * j + 2)))%nat by lia.
    rewrite !lw0_q_pow_S. ring. }
  unfold lw0_Wb, Qdiv.
  rewrite E4, E1, E2, E3.
  assert (HD : (q_fact n * (lw0_q_of_nat (2*j + 3) * lw0_q_of_nat (2*j + 2) * q_fact (2*j + 1)) *
                (lw0_q_of_nat (2*n + 2*j + 4) * lw0_q_of_nat (2*n + 2*j + 3) * q_fact (2*n + 2*j + 2)))%Q ==
               ((q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2)) *
                (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                 lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))%Q) by ring.
  rewrite HD.
  rewrite (Qinv_mult_distr (q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))
             (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
              lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  ring.
Qed.

(* 交叉相乘转移：0<Y, 0<D 且 X·D ≤ Y·P 则 X/Y ≤ P/D *)
Lemma lw0_frac_le : forall X Y P D : Q,
  QltT 0 Y -> QltT 0 D -> QleT' (X * D) (Y * P) -> QleT' (X / Y) (P / D).
Proof.
  intros X Y P D HY HD Hkey.
  assert (HY0 : Y == 0 -> False) by (apply qltT_not_eq_zero; exact HY).
  assert (HD0 : D == 0 -> False) by (apply qltT_not_eq_zero; exact HD).
  assert (Hpos : QleT' 0 ((/ Y) * (/ D))).
  { apply lw0_qmul_le0T; apply lw0_Qlt_le; apply Qinv_lt_0_compat, QltT_to_Qlt;
      [ exact HY | exact HD ]. }
  apply (qleT'_trans (X / Y) ((X * D) * ((/ Y) * (/ D))) (P / D)).
  - apply qeq_leT'. unfold Qdiv.
    rewrite <- (Qmult_assoc X D ((/ Y) * (/ D))), (Qmult_comm D ((/ Y) * (/ D))).
    rewrite <- (Qmult_assoc (/ Y) (/ D) D), (Qmult_comm (/ D) D), (Qmult_inv_r D HD0).
    ring.
  - apply (qleT'_trans ((X * D) * ((/ Y) * (/ D))) ((Y * P) * ((/ Y) * (/ D))) (P / D)).
    + apply (lw0_qcompat_r (X * D) (Y * P) ((/ Y) * (/ D)) Hkey Hpos).
    + apply qeq_leT'.
      unfold Qdiv. rewrite (Qmult_comm Y P).
      rewrite <- (Qmult_assoc P Y ((/ Y) * (/ D))), (Qmult_assoc Y (/ Y) (/ D)).
      rewrite (Qmult_inv_r Y HY0). ring.
Qed.

(* 二次因子对压：2(n+2j+2) ≤ (n+2)(2j+2)，3(n+2j+3) ≤ (n+3)(2j+3) *)
Lemma lw0_lin_beat2 : forall (n j : nat),
  QleT' ((2#1) * lw0_q_of_nat (n + 2*j + 2)) (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)).
Proof.
  intros n j.
  assert (HA : lw0_q_of_nat (n + 2*j + 2) == lw0_q_of_nat (n + 2) + lw0_q_of_nat (2*j)) by
    (replace (n + 2*j + 2)%nat with ((n + 2) + (2*j))%nat by lia;
     apply lw0_q_of_nat_add).
  assert (HC : lw0_q_of_nat (2*j + 2) == lw0_q_of_nat 2 + lw0_q_of_nat (2*j)) by
    (replace (2*j + 2)%nat with (2 + (2*j))%nat by lia; apply lw0_q_of_nat_add).
  assert (H2 : lw0_q_of_nat 2 == (2#1)) by reflexivity.
  apply (qleT'_trans ((2#1) * lw0_q_of_nat (n + 2*j + 2))
                     ((2#1) * lw0_q_of_nat (n + 2) + (2#1) * lw0_q_of_nat (2*j))
                     (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2))).
  - apply (qeq_leT' ((2#1) * lw0_q_of_nat (n + 2*j + 2))
                    ((2#1) * lw0_q_of_nat (n + 2) + (2#1) * lw0_q_of_nat (2*j))).
    rewrite HA. ring.
  - apply (qleT'_trans
           ((2#1) * lw0_q_of_nat (n + 2) + (2#1) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 2) * (2#1) + lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2))).
    + apply qleT'_plus_compat.
      * apply (qeq_leT' ((2#1) * lw0_q_of_nat (n + 2))
                        (lw0_q_of_nat (n + 2) * (2#1))).
        ring.
      * apply lw0_qcompat_r.
        -- apply Qle_to_QleT'. unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
        -- apply lw0_q_of_nat_nonneg.
    + apply (qeq_leT' (lw0_q_of_nat (n + 2) * (2#1) + lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j))
                      (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2))).
      rewrite HC. rewrite H2. ring.
Qed.

Lemma lw0_lin_beat3 : forall (n j : nat),
  QleT' ((3#1) * lw0_q_of_nat (n + 2*j + 3)) (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3)).
Proof.
  intros n j.
  assert (HA : lw0_q_of_nat (n + 2*j + 3) == lw0_q_of_nat (n + 3) + lw0_q_of_nat (2*j)) by
    (replace (n + 2*j + 3)%nat with ((n + 3) + (2*j))%nat by lia;
     apply lw0_q_of_nat_add).
  assert (HC : lw0_q_of_nat (2*j + 3) == lw0_q_of_nat 3 + lw0_q_of_nat (2*j)) by
    (replace (2*j + 3)%nat with (3 + (2*j))%nat by lia; apply lw0_q_of_nat_add).
  assert (H3 : lw0_q_of_nat 3 == (3#1)) by reflexivity.
  apply (qleT'_trans ((3#1) * lw0_q_of_nat (n + 2*j + 3))
                     ((3#1) * lw0_q_of_nat (n + 3) + (3#1) * lw0_q_of_nat (2*j))
                     (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))).
  - apply (qeq_leT' ((3#1) * lw0_q_of_nat (n + 2*j + 3))
                    ((3#1) * lw0_q_of_nat (n + 3) + (3#1) * lw0_q_of_nat (2*j))).
    rewrite HA. ring.
  - apply (qleT'_trans
           ((3#1) * lw0_q_of_nat (n + 3) + (3#1) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 3) * (3#1) + lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))).
    + apply qleT'_plus_compat.
      * apply (qeq_leT' ((3#1) * lw0_q_of_nat (n + 3))
                        (lw0_q_of_nat (n + 3) * (3#1))).
        ring.
      * apply lw0_qcompat_r.
        -- apply Qle_to_QleT'. unfold Qle, lw0_q_of_nat. cbn [Qnum Qden]. lia.
        -- apply lw0_q_of_nat_nonneg.
    + apply (qeq_leT' (lw0_q_of_nat (n + 3) * (3#1) + lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j))
                      (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))).
      rewrite HC. rewrite H3. ring.
Qed.

(* 核不等式：12(n+2j+2)(n+2j+3) ≤ (2j+2)(2j+3)(2n+2j+3)(2n+2j+4) *)
Lemma lw0_twelve_AB_le : forall (n j : nat), (2 <= n)%nat ->
  QleT' ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
        (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)).
Proof.
  intros n j Hn.
  assert (S1 := lw0_lin_beat2 n j).
  assert (S2 := lw0_lin_beat3 n j).
  assert (S3 : QleT' (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4))
                     (lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  { apply lw0_qcompat4.
    - apply lw0_q_of_nat_nonneg.
    - apply lw0_q_of_nat_le_mono. lia.
    - apply lw0_q_of_nat_nonneg.
    - apply lw0_q_of_nat_le_mono. lia. }
  assert (S4 : QleT' ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3))
                     (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4))).
  { assert (HD : lw0_q_of_nat (2*n + 4) == (2#1) * lw0_q_of_nat (n + 2)).
    { replace (2 * n + 4)%nat with ((n + 2) + (n + 2))%nat by lia.
      rewrite lw0_q_of_nat_add. ring. }
    apply (qleT'_trans ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3))
                       (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2 * n + 4))
                       (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4))).
    - apply (qeq_leT' ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3))
                      (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2 * n + 4))).
      rewrite HD. ring.
    - apply lw0_qcompat_r.
      + apply lw0_q_of_nat_le_mono. lia.
      + apply lw0_q_of_nat_nonneg. }
  apply (qleT'_trans
      ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
      (((lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)) *
        (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))) * (2#1))
      (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
       lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  - apply (qleT'_trans
        ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
        (((2#1) * lw0_q_of_nat (n + 2*j + 2)) * ((3#1) * lw0_q_of_nat (n + 2*j + 3)) * (2#1))
        (((lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)) *
          (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))) * (2#1))).
    + apply qeq_leT'. ring.
    + apply lw0_qcompat_r.
      * apply lw0_qcompat4.
        -- apply lw0_qmul_le0T;
             [ apply Qle_to_QleT'; unfold Qle; simpl; lia
             | apply lw0_q_of_nat_nonneg ].
        -- exact S1.
        -- apply lw0_qmul_le0T;
             [ apply Qle_to_QleT'; unfold Qle; simpl; lia
             | apply lw0_q_of_nat_nonneg ].
        -- exact S2.
      * apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - apply (qleT'_trans
        (((lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)) *
          (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))) * (2#1))
        ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
         ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3)))
        (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
    + apply qeq_leT'. ring.
    + apply (qleT'_trans
          ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
           ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3)))
          ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
           (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)))
          (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
           lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
      * apply lw0_qcompat4.
        -- apply lw0_qmul_le0T; apply lw0_q_of_nat_nonneg.
        -- apply qleT'_refl.
        -- apply lw0_qmul_le0T;
             [ apply Qle_to_QleT'; unfold Qle, lw0_q_of_nat; cbn [Qnum Qden Qmult]; lia
             | apply lw0_q_of_nat_nonneg ].
        -- exact S4.
      * apply (qleT'_trans
              ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
               (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)))
              ((lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)) *
               (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)))
              (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
               lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
        -- apply qeq_leT'. ring.
        -- apply (qleT'_trans
                ((lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)) *
                 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)))
                ((lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)) *
                 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)))
                (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                 lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
           ++ apply lw0_qcompat_r.
              ** exact S3.
              ** apply lw0_qmul_le0T; apply lw0_q_of_nat_nonneg.
           ++ apply qeq_leT'. ring.
Qed.

(* 几何率：n≥2, 0<q≤10/3 时 W_{j+1} ≤ W_j·25/27 < W_j（Leibniz 收敛核） *)
Lemma lw0_Wb_ratio_bound : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j * (25#27)).
Proof.
  intros b q n j Hb0 Hq Hq103 Hn.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (Hden : QltT 0 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply qmult_ltT_0_compat.
      + apply qmult_ltT_0_compat; apply lw0_q_of_nat_lt0T; lia.
      + apply lw0_q_of_nat_lt0T. lia.
    - apply QltT_to_Qlt. apply lw0_q_of_nat_lt0T. lia. }
  assert (Hqq : QleT' (q * q) ((100#9))).
  { apply (qleT'_trans (q * q) ((10#3) * (10#3)) ((100#9))).
    - apply lw0_qcompat4; assumption.
    - apply qeq_leT'. reflexivity. }
  assert (Hratio : QleT' (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                          (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                           lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))
                         ((25#1) / (27#1))).
  { apply lw0_frac_le.
    + exact Hden.
    + apply Qlt_to_QltT. unfold Qlt. simpl. lia.
    + apply (qleT'_trans
          ((q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)) * (27#1))
          (((100#9) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)) * (27#1))
          (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
           lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) * (25#1))).
      * apply lw0_qcompat_r.
        -- apply lw0_qcompat_r.
           ++ apply lw0_qcompat_r.
              ** exact Hqq.
              ** apply lw0_q_of_nat_nonneg.
           ++ apply lw0_q_of_nat_nonneg.
        -- apply Qle_to_QleT'. unfold Qle. simpl. lia.
      * apply (qleT'_trans
            (((100#9) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)) * (27#1))
            ((25#1) * ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)))
            (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
             lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) * (25#1))).
        -- apply qeq_leT'. ring.
        -- apply (qleT'_trans
              ((25#1) * ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)))
              ((25#1) * (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))
              (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
               lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) * (25#1))).
           ++ apply lw0_qcompat_l.
              ** exact (lw0_twelve_AB_le n j Hn).
              ** apply Qle_to_QleT'. unfold Qle. simpl. lia.
              ** apply lw0_qmul_le0T.
                 --- apply lw0_qmul_le0T;
                       [ apply Qle_to_QleT'; unfold Qle; simpl; lia
                       | apply lw0_q_of_nat_nonneg ].
                 --- apply lw0_q_of_nat_nonneg.
           ++ apply qeq_leT'. ring. }
  assert (Hratio0 : QleT' 0 (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                           (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                            lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))).
  { unfold Qdiv. apply lw0_qmul_le0T.
    - apply lw0_QltT_le. apply qmult_ltT_0_compat.
      + apply qmult_ltT_0_compat.
        * exact (qmult_ltT_0_compat q q Hq Hq).
        * apply lw0_q_of_nat_lt0T. lia.
      + apply lw0_q_of_nat_lt0T. lia.
    - apply lw0_Qlt_le. apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Hden. }
  apply (qleT'_trans (lw0_Wb b q n (Datatypes.S j))
                     (lw0_Wb b q n j * (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                       (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                        lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))
                     (lw0_Wb b q n j * (25#27))).
  - apply (qeq_leT' (lw0_Wb b q n (Datatypes.S j))
                    (lw0_Wb b q n j * (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                     (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                      lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))).
    exact (lw0_Wb_ratio_eq b q n j).
  - apply (qleT'_trans (lw0_Wb b q n j * (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                        (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))
                       (lw0_Wb b q n j * ((25#1) / (27#1)))
                       (lw0_Wb b q n j * (25#27))).
    + apply lw0_qcompat_l.
      * exact Hratio.
      * exact (lw0_Wb_nonneg b q n j Hb0 Hq0).
      * exact Hratio0.
    + apply qeq_leT'. reflexivity.
Qed.

(* 严格首对：W_1 < W_0（b 须严格正：b=0 时 W 序列全零，非严格前提下命题为假） *)
Lemma lw0_Wb_lt01 : forall (b q : Q) (n : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QltT (lw0_Wb b q n 1) (lw0_Wb b q n 0).
Proof.
  intros b q n Hb0 Hq Hq103 Hn.
  apply Qlt_to_QltT.
  assert (Hb : QleT' (lw0_Wb b q n 1) (lw0_Wb b q n 0 * (25#27)))
    by (apply lw0_Wb_ratio_bound;
        [ apply lw0_QltT_le; exact Hb0 | exact Hq | exact Hq103 | exact Hn ]).
  assert (HW0pos : Qlt 0 (lw0_Wb b q n 0))
    by (apply QltT_to_Qlt; apply lw0_Wb_pos; assumption).
  assert (Hlt : Qlt (lw0_Wb b q n 0 * (25#27)) (lw0_Wb b q n 0))
    by (apply lw0_mul_lt_one; [ exact HW0pos | unfold Qlt; simpl; lia ]).
  apply (Qle_lt_trans (lw0_Wb b q n 1) (lw0_Wb b q n 0 * (25#27)) (lw0_Wb b q n 0)).
  - apply QleT'_to_Qle. exact Hb.
  - exact Hlt.
Qed.

(* 逐项严格递减（对每个 j；b 须严格正，理由同 lw0_Wb_lt01） *)
Lemma lw0_Wb_seq_dec_strict : forall (b q : Q) (n j : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QltT (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j).
Proof.
  intros b q n j Hb0 Hq Hq103 Hn.
  apply Qlt_to_QltT.
  assert (Hqpos : Qlt 0 (lw0_Wb b q n j))
    by (apply QltT_to_Qlt; apply lw0_Wb_pos; assumption).
  assert (Hb : QleT' (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j * (25#27)))
    by (apply lw0_Wb_ratio_bound;
        [ apply lw0_QltT_le; exact Hb0 | exact Hq | exact Hq103 | exact Hn ]).
  assert (Hlt : Qlt (lw0_Wb b q n j * (25#27)) (lw0_Wb b q n j))
    by (apply lw0_mul_lt_one; [ exact Hqpos | unfold Qlt; simpl; lia ]).
  apply (Qle_lt_trans (lw0_Wb b q n (Datatypes.S j))
                      (lw0_Wb b q n j * (25#27)) (lw0_Wb b q n j)).
  - apply QleT'_to_Qle. exact Hb.
  - exact Hlt.
Qed.

(* Bernoulli 线性下界：(1+x)^j ≥ 1 + j·x 的 c 形：1 ≤ c 时 c^j ≥ 1 + j(c−1) *)
Lemma lw0_geom_lin_lb : forall (c : Q) (j : nat),
  QleT' 1 c -> QleT' (1 + lw0_q_of_nat j * (c - 1)) (q_pow c j).
Proof.
  intros c j Hc. induction j as [| j IH].
  - change (q_pow c 0) with 1%Q.
    replace (lw0_q_of_nat 0) with 0%Q by reflexivity.
    apply qeq_leT'. ring.
  - apply (qleT'_trans (1 + lw0_q_of_nat (Datatypes.S j) * (c - 1))
                       (1 + (lw0_q_of_nat j + 1) * (c - 1))
                       (q_pow c (Datatypes.S j))).
    + apply (qeq_leT' (1 + lw0_q_of_nat (Datatypes.S j) * (c - 1))
                      (1 + (lw0_q_of_nat j + 1) * (c - 1))).
      rewrite lw0_q_of_nat_succ. reflexivity.
    + apply (qleT'_trans (1 + (lw0_q_of_nat j + 1) * (c - 1))
                         (c * (1 + lw0_q_of_nat j * (c - 1)))
                         (q_pow c (Datatypes.S j))).
      * apply (qleT'_trans
            (1 + (lw0_q_of_nat j + 1) * (c - 1))
            (1 + (lw0_q_of_nat j + 1) * (c - 1) + lw0_q_of_nat j * (c - 1) * (c - 1))
            (c * (1 + lw0_q_of_nat j * (c - 1)))).
        -- apply (qleT'_trans (1 + (lw0_q_of_nat j + 1) * (c - 1))
                              ((1 + (lw0_q_of_nat j + 1) * (c - 1)) + 0)
                              (1 + (lw0_q_of_nat j + 1) * (c - 1)
                               + lw0_q_of_nat j * (c - 1) * (c - 1))).
           ++ apply (qeq_leT' (1 + (lw0_q_of_nat j + 1) * (c - 1))
                              ((1 + (lw0_q_of_nat j + 1) * (c - 1)) + 0)).
              ring.
           ++ apply (qleT'_plus_compat (1 + (lw0_q_of_nat j + 1) * (c - 1))
                          (1 + (lw0_q_of_nat j + 1) * (c - 1)) 0
                          (lw0_q_of_nat j * (c - 1) * (c - 1))).
              ** apply qleT'_refl.
              ** apply lw0_qmul_le0T.
                 *** apply lw0_qmul_le0T.
                     **** apply lw0_q_of_nat_nonneg.
                     **** apply (lw0_sub_le0T c 1); exact Hc.
                 *** apply (lw0_sub_le0T c 1); exact Hc.
        -- apply qeq_leT'. ring.
      * apply (qleT'_trans (c * (1 + lw0_q_of_nat j * (c - 1)))
                           (c * q_pow c j)
                           (q_pow c (Datatypes.S j))).
        -- apply (qleT'_trans (c * (1 + lw0_q_of_nat j * (c - 1)))
                              ((1 + lw0_q_of_nat j * (c - 1)) * c)
                              (c * q_pow c j)).
           ++ apply qeq_leT'. ring.
           ++ apply (qleT'_trans ((1 + lw0_q_of_nat j * (c - 1)) * c)
                                 (q_pow c j * c)
                                 (c * q_pow c j)).
              ** apply lw0_qcompat_r.
                 *** exact IH.
                 *** apply (qleT'_trans 0 1 c);
                     [ apply Qle_to_QleT'; unfold Qle; simpl; lia | exact Hc ].
              ** apply qeq_leT'. ring.
        -- apply (qeq_leT' (c * q_pow c j) (q_pow c (Datatypes.S j))).
           rewrite <- lw0_q_pow_S. reflexivity.
Qed.

(* 几何包络：W_j ≤ W_0·(25/27)^j *)
Lemma lw0_Wb_geo_le : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n j) (lw0_Wb b q n 0 * q_pow (25#27) j).
Proof.
  intros b q n j Hb0 Hq Hq103 Hn.
  induction j as [| j IH].
  - change (q_pow (25#27) 0) with 1%Q. apply qeq_leT'. ring.
  - apply (qleT'_trans
        (lw0_Wb b q n (Datatypes.S j))
        (lw0_Wb b q n j * (25#27))
        (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j))).
    + apply lw0_Wb_ratio_bound; assumption.
    + assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
      assert (Hc0 : QleT' 0 (25#27)) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
      apply (qleT'_trans
          (lw0_Wb b q n j * (25#27))
          ((lw0_Wb b q n 0 * q_pow (25#27) j) * (25#27))
          (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j))).
      * apply lw0_qcompat_r.
        -- exact IH.
        -- apply Qle_to_QleT'. unfold Qle. simpl. lia.
      * apply (qleT'_trans
              ((lw0_Wb b q n 0 * q_pow (25#27) j) * (25#27))
              (lw0_Wb b q n 0 * (q_pow (25#27) j * (25#27)))
              (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j))).
        -- apply qeq_leT'. ring.
        -- apply (qeq_leT' (lw0_Wb b q n 0 * (q_pow (25#27) j * (25#27)))
                           (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j))).
           rewrite lw0_q_pow_S. ring.
Qed.


(* ---------- 交错和尾界机械（任意起点） ---------- *)

(* 加法分解：acc sg k (a+b) == acc sg k a + acc（a 奇偶定号）W (k+a) b *)
Lemma lw0_acc_add_gen : forall (a : nat) (sg : bool) (W : nat -> Q) (k b : nat),
  altsum_acc sg W k (a + b)%nat ==
  altsum_acc sg W k a +
  altsum_acc (if Nat.even a then sg else negb sg) W (k + a) b.
Proof.
  intros a. induction a as [| a IH]; intros sg W k b.
  - replace (0 + b)%nat with b%nat by lia.
    rewrite (altsum_acc_0_eq sg W k).
    replace (k + 0)%nat with k%nat by lia.
    replace (if Nat.even 0 then sg else negb sg) with sg by reflexivity.
    ring.
  - destruct sg.
    + replace (Datatypes.S a + b)%nat with (Datatypes.S (a + b))%nat by lia.
      rewrite altsum_acc_T.
      rewrite (IH false W (Datatypes.S k) b).
      rewrite (altsum_acc_T W k a).
      replace (k + Datatypes.S a)%nat with (Datatypes.S k + a)%nat by lia.
      rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even a); cbn; ring.
    + replace (Datatypes.S a + b)%nat with (Datatypes.S (a + b))%nat by lia.
      rewrite altsum_acc_F.
      rewrite (IH true W (Datatypes.S k) b).
      rewrite (altsum_acc_F W k a).
      replace (k + Datatypes.S a)%nat with (Datatypes.S k + a)%nat by lia.
      rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even a); cbn; ring.
Qed.

Lemma lw0_altsum_add : forall (W : nat -> Q) (a b : nat),
  altsum W (a + b)%nat == altsum W a + altsum_acc (altsum_sgp a) W a b.
Proof.
  intros W a b. unfold altsum, altsum_sgp.
  pose proof (lw0_acc_add_gen a true W 0 b) as H.
  rewrite H.
  destruct (Nat.even a); cbn; ring.
Qed.

(* 四分量夹板：任意起点下 true 尾 ∈ [0, W k]、false 尾 ∈ [−W k, 0] *)
Lemma lw0_acc_quad : forall (W : nat -> Q),
  (forall k, QleT' 0 (W k)) -> (forall k, QleT' (W (Datatypes.S k)) (W k)) ->
  forall m k : nat,
  And (QleT' 0 (altsum_acc true W k m))
  (And (QleT' (altsum_acc true W k m) (W k))
  (And (QleT' (altsum_acc false W k m) 0)
       (QleT' (Qopp (W k)) (altsum_acc false W k m)))).
Proof.
  intros W H0 Hd m. induction m as [| m IH].
  - intro k. split; [ apply qleT'_refl | split; [ apply H0
      | split; [ apply qleT'_refl | apply altsum_qleT'_neg_le0; apply H0 ] ] ].
  - intro k.
    destruct (IH k) as [I1 [I2 [I3 I4]]].
    destruct (IH (Datatypes.S k)) as [J1 [J2 [J3 J4]]].
    (* 项数 S m *)
      assert (EA : altsum_acc true W k (Datatypes.S m)
                   == W k + altsum_acc false W (Datatypes.S k) m) by apply altsum_acc_T.
      assert (EB : altsum_acc false W k (Datatypes.S m)
                   == Qopp (W k) + altsum_acc true W (Datatypes.S k) m) by apply altsum_acc_F.
      split.
      * apply (qleT'_trans 0 (W k + Qopp (W (Datatypes.S k)))
                           (altsum_acc true W k (Datatypes.S m))).
        -- apply altsum_qleT'_ge_sub. apply Hd.
        -- apply (qleT'_trans (W k + Qopp (W (Datatypes.S k)))
                              (W k + altsum_acc false W (Datatypes.S k) m)
                              (altsum_acc true W k (Datatypes.S m))).
           ++ apply qleT'_plus_compat; [ apply qleT'_refl | exact J4 ].
           ++ apply qeq_leT'. rewrite EA. reflexivity.
      * split.
        -- apply (qleT'_trans (altsum_acc true W k (Datatypes.S m)) (W k + 0) (W k)).
           ++ apply (qleT'_trans (altsum_acc true W k (Datatypes.S m))
                                 (W k + altsum_acc false W (Datatypes.S k) m)
                                 (W k + 0)).
              ** apply qeq_leT'. rewrite EA. reflexivity.
              ** apply qleT'_plus_compat; [ apply qleT'_refl | exact J3 ].
           ++ apply qeq_leT'. ring.
        -- split.
              ** apply (qleT'_trans (altsum_acc false W k (Datatypes.S m))
                                    (Qopp (W k) + altsum_acc true W (Datatypes.S k) m) 0).
                 --- apply qeq_leT'. rewrite EB. reflexivity.
                 --- apply (qleT'_trans (Qopp (W k) + altsum_acc true W (Datatypes.S k) m)
                                        (Qopp (W k) + W k) 0).
                     +++ apply qleT'_plus_compat;
                         [ apply qleT'_refl
                         | apply (qleT'_trans (altsum_acc true W (Datatypes.S k) m)
                                              (W (Datatypes.S k)) (W k));
                           [ exact J2 | apply Hd ] ].
                     +++ apply qeq_leT'. ring.
              ** apply (qleT'_trans (Qopp (W k)) (Qopp (W k) + 0)
                                       (altsum_acc false W k (Datatypes.S m))).
                 --- apply qeq_leT'. ring.
                 --- apply (qleT'_trans (Qopp (W k) + 0)
                           (Qopp (W k) + altsum_acc true W (Datatypes.S k) m)
                           (altsum_acc false W k (Datatypes.S m))).
                     +++ apply qleT'_plus_compat; [ apply qleT'_refl | exact J1 ].
                     +++ apply qeq_leT'. rewrite EB. reflexivity.
Qed.

(* 尾项绝对值界（任意起点）：|acc(sgp m) W m r| ≤ W m *)
Lemma lw0_altseq_rem_le : forall (W : nat -> Q),
  (forall k, QleT' 0 (W k)) -> (forall k, QleT' (W (Datatypes.S k)) (W k)) ->
  forall m r : nat,
  QleT' (Qabs (altsum_acc (altsum_sgp m) W m r)) (W m).
Proof.
  intros W H0 Hd m r.
  destruct (lw0_acc_quad W H0 Hd r m) as [I1 [I2 [I3 I4]]].
  unfold altsum_sgp. destruct (Nat.even m).
  - apply (qleT'_trans (Qabs (altsum_acc true W m r))
                       (altsum_acc true W m r) (W m)).
    ++ apply qeq_leT'. exact (lw0_Qabs_pos_eq (altsum_acc true W m r) I1).
    ++ exact I2.
  - apply (qleT'_trans (Qabs (altsum_acc false W m r))
                       (Qopp (altsum_acc false W m r)) (W m)).
    ++ apply qeq_leT'.
       exact (Qabs_neg (altsum_acc false W m r) (QleT'_to_Qle (altsum_acc false W m r) 0 I3)).
    ++ apply (qleT'_trans (Qopp (altsum_acc false W m r))
                         (Qopp (Qopp (W m))) (W m)).
       ** apply lw0_opp_le_swap. exact I4.
       ** apply qeq_leT'. ring.
Qed.

(* 交错部分和序列的柯西见证（消逝界作显式前提——接口以 S05 交付为准） *)
Lemma lw0_altseq_cauchy : forall (W : nat -> Q),
  (forall k, QleT' 0 (W k)) -> (forall k, QleT' (W (Datatypes.S k)) (W k)) ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall j : nat, (N <= j)%nat -> QltT (W j) eps)) ->
  cauchy (fun m : nat => altsum W m).
Proof.
  intros W H0 Hd Hvan eps Heps.
  destruct (Hvan (eps / 2)%Q) as [N HN].
  { apply lw0_half_pos. exact Heps. }
  exists N. intros m n Hm Hn.
  destruct (le_dec m n) as [Hle | Hgt].
  - replace (altsum W n) with (altsum W (m + (n - m))%nat) by (f_equal; lia).
    assert (Ed : (altsum W m - altsum W (m + (n - m)))%Q ==
                 Qopp (altsum_acc (altsum_sgp m) W m (n - m))).
    { rewrite lw0_altsum_add. ring. }
    apply (lw0_leT'_ltT_trans (Qabs (altsum W m - altsum W (m + (n - m))%nat))
                              (W m) eps).
    + apply (qleT'_trans (Qabs (altsum W m - altsum W (m + (n - m))%nat))
                         (Qabs (Qopp (altsum_acc (altsum_sgp m) W m (n - m)))) (W m)).
      * apply (qeq_leT' (Qabs (altsum W m - altsum W (m + (n - m))%nat))
                        (Qabs (Qopp (altsum_acc (altsum_sgp m) W m (n - m))))
                        (Qabs_wd (altsum W m - altsum W (m + (n - m))%nat)
                                 (Qopp (altsum_acc (altsum_sgp m) W m (n - m))) Ed)).
      * apply (qleT'_trans (Qabs (Qopp (altsum_acc (altsum_sgp m) W m (n - m))))
                           (Qabs (altsum_acc (altsum_sgp m) W m (n - m))) (W m)).
        -- apply (qeq_leT' (Qabs (Qopp (altsum_acc (altsum_sgp m) W m (n - m))))
                           (Qabs (altsum_acc (altsum_sgp m) W m (n - m)))
                           (Qabs_opp (altsum_acc (altsum_sgp m) W m (n - m)))).
        -- apply lw0_altseq_rem_le; assumption.
    + apply (lw0_ltT_leT_trans (W m) (eps / 2)%Q eps).
      * apply HN. exact (NatLe_drop N m Hm).
      * apply Qle_to_QleT'. apply (Qlt_le_weak (eps / 2)).
        apply (lw0_mul_lt_one eps (1#2));
          [ apply QltT_to_Qlt; exact Heps | unfold Qlt; simpl; lia ].
  - assert (Hge : (n <= m)%nat) by lia.
    replace (altsum W m) with (altsum W (n + (m - n))%nat) by (f_equal; lia).
    assert (Ed : (altsum W (n + (m - n)) - altsum W n)%Q ==
                 altsum_acc (altsum_sgp n) W n (m - n)).
    { rewrite lw0_altsum_add. ring. }
    apply (lw0_leT'_ltT_trans (Qabs (altsum W (n + (m - n)) - altsum W n))
                              (W n) eps).
    + apply (qleT'_trans (Qabs (altsum W (n + (m - n)) - altsum W n))
                         (Qabs (altsum_acc (altsum_sgp n) W n (m - n))) (W n)).
      * apply (qeq_leT' (Qabs (altsum W (n + (m - n)) - altsum W n))
                        (Qabs (altsum_acc (altsum_sgp n) W n (m - n)))
                        (Qabs_wd (altsum W (n + (m - n)) - altsum W n)
                                 (altsum_acc (altsum_sgp n) W n (m - n)) Ed)).
      * apply lw0_altseq_rem_le; assumption.
    + apply (lw0_ltT_leT_trans (W n) (eps / 2)%Q eps).
      * apply HN. exact (NatLe_drop N n Hn).
      * apply Qle_to_QleT'. apply (Qlt_le_weak (eps / 2)).
        apply (lw0_mul_lt_one eps (1#2));
          [ apply QltT_to_Qlt; exact Heps | unfold Qlt; simpl; lia ].
Qed.

(* ---------- 端点泛函与正性/上界传递 ---------- *)
(* lw0_L_of_seq 为 S05 模块之占位形——接口以 S05 交付为准。 *)

Definition lw0_L_of_seq (W : nat -> Q) (Hc : cauchy (fun m : nat => altsum W m)) : Real :=
  existT _ (fun m : nat => altsum W m) Hc.

Lemma lw0_proj_L : forall (W : nat -> Q)
                          (Hc : cauchy (fun m : nat => altsum W m)) (n : nat),
  projT1 (lw0_L_of_seq W Hc) n == altsum W n.
Proof. intros W Hc n. unfold lw0_L_of_seq. reflexivity. Qed.

Lemma lw0_proj_zero : forall n : nat, projT1 real_zero n == 0.
Proof. intros n. unfold real_zero. reflexivity. Qed.

Lemma lw0_proj_const : forall (c : Q) (n : nat), projT1 (real_const c) n == c.
Proof. intros c n. unfold real_const. reflexivity. Qed.

(* 正性传递：非负 + 递减 + 严格首对 ⟹ 0 < L *)
Lemma lw0_L_pos : forall (W : nat -> Q) (Hc : cauchy (fun m : nat => altsum W m)),
  (forall k, QleT' 0 (W k)) -> (forall k, QleT' (W (Datatypes.S k)) (W k)) ->
  QltT (W 1%nat) (W 0%nat) ->
  real_lt real_zero (lw0_L_of_seq W Hc).
Proof.
  intros W Hc H0 Hd Hlt.
  assert (Hpos : QltT 0 (W 0%nat - W 1%nat)) by (apply lw0_sub_lt0; exact Hlt).
  unfold real_lt. exists ((W 0%nat - W 1%nat) / 2)%Q. split.
  - apply lw0_half_pos. exact Hpos.
  - exists 1%nat. intros n Hn.
    change (projT1 (lw0_L_of_seq W Hc) n - projT1 real_zero n)%Q
      with (altsum W n - 0)%Q.
    apply (lw0_ltT_leT_trans ((W 0%nat - W 1%nat) / 2)%Q (W 0%nat - W 1%nat) (altsum W n - 0)%Q).
    + apply Qlt_to_QltT.
      apply (lw0_mul_lt_one (W 0%nat - W 1%nat) (1#2));
        [ apply QltT_to_Qlt; exact Hpos | unfold Qlt; simpl; lia ].
    + apply (qleT'_trans (W 0%nat + Qopp (W 1%nat)) (altsum W n) (altsum W n - 0)%Q).
      * apply altsum_ge_pair0;
          [ assumption | assumption | apply NatLe_drop; exact Hn ].
      * apply qeq_leT'. ring.
Qed.

(* 上界传递：非负 + 递减 + 逐项严格递减 ⟹ L < W 0 *)
Lemma lw0_L_upper : forall (W : nat -> Q) (Hc : cauchy (fun m : nat => altsum W m)),
  (forall k, QleT' 0 (W k)) -> (forall k, QleT' (W (Datatypes.S k)) (W k)) ->
  (forall j, QltT (W (Datatypes.S j)) (W j)) ->
  real_lt (lw0_L_of_seq W Hc) (real_const (W 0%nat)).
Proof.
  intros W Hc H0 Hd Hst.
  assert (Hpos : QltT 0 (W 1%nat - W 2%nat)) by (apply lw0_sub_lt0; apply Hst).
  unfold real_lt. exists ((W 1%nat - W 2%nat) / 2)%Q. split.
  - apply lw0_half_pos. exact Hpos.
  - exists 2%nat. intros n Hn.
    destruct n as [|[|m]];
      [ cbn in Hn; inversion Hn
      | cbn in Hn; inversion Hn | ].
    change (projT1 (lw0_L_of_seq W Hc) (Datatypes.S (Datatypes.S m))
            - projT1 (real_const (W 0%nat)) (Datatypes.S (Datatypes.S m)))%Q
      with (altsum W (Datatypes.S (Datatypes.S m)) - W 0%nat)%Q.
    apply (lw0_ltT_leT_trans ((W 1%nat - W 2%nat) / 2)%Q (W 1%nat - W 2%nat)
                             (W 0%nat - altsum W (Datatypes.S (Datatypes.S m)))%Q).
    + apply Qlt_to_QltT.
      apply (lw0_mul_lt_one (W 1%nat - W 2%nat) (1#2));
        [ apply QltT_to_Qlt; exact Hpos | unfold Qlt; simpl; lia ].
    + assert (E : altsum W (Datatypes.S (Datatypes.S m))
                  == (W 0%nat + Qopp (W 1%nat)) + altsum_acc true W 2 m).
      { unfold altsum. rewrite altsum_acc_T, altsum_acc_F. ring. }
      destruct (lw0_acc_quad W H0 Hd m 2) as [Q1 [Q2 [Q3 Q4]]].
      apply (qleT'_trans (W 1%nat - W 2%nat)
                         (W 1%nat + Qopp (altsum_acc true W 2 m))
                         (W 0%nat - altsum W (Datatypes.S (Datatypes.S m)))).
      * apply qleT'_plus_compat.
        -- apply qleT'_refl.
        -- apply lw0_opp_le_swap. exact Q2.
      * apply qeq_leT'. rewrite E. ring.
Qed.

(* ---------- 实例装配：Niven 型 W 序列的 0 < L < W 0 ---------- *)

Lemma lw0_Wb_seq_nonneg : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' 0 (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq.
  apply lw0_Wb_nonneg.
  - exact Hb.
  - apply lw0_QltT_le. exact Hq.
Qed.

Lemma lw0_Wb_seq_decr : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq Hq103 Hn.
  apply (qleT'_trans (lw0_Wb b q n (Datatypes.S j))
                     (lw0_Wb b q n j * (25#27)) (lw0_Wb b q n j)).
  - apply lw0_Wb_ratio_bound; assumption.
  - apply (qleT'_trans (lw0_Wb b q n j * (25#27))
                       (lw0_Wb b q n j * 1) (lw0_Wb b q n j)).
    + apply (lw0_qcompat_l (25#27) 1 (lw0_Wb b q n j)).
      * apply Qle_to_QleT'. unfold Qle. simpl. lia.
      * apply lw0_Wb_seq_nonneg; [ exact Hb | exact Hq ].
      * apply Qle_to_QleT'. unfold Qle. simpl. lia.
    + apply qeq_leT'. ring.
Qed.

(* 0 < L(f_n)：正性传递主件（b 严格正：lt01 前提支所需，见 lw0_Wb_lt01 注） *)
Lemma lw0_L_f_n_pos : forall (b q : Q) (n : nat)
                             (Hc : cauchy (fun m : nat => altsum (lw0_Wb b q n) m)),
  QltT 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  real_lt real_zero (lw0_L_of_seq (lw0_Wb b q n) Hc).
Proof.
  intros b q n Hc Hb Hq Hq103 Hn.
  apply (lw0_L_pos (lw0_Wb b q n) Hc).
  - intros j. apply lw0_Wb_seq_nonneg.
    + apply lw0_QltT_le. exact Hb.
    + exact Hq.
  - intros j. apply lw0_Wb_seq_decr.
    + apply lw0_QltT_le. exact Hb.
    + exact Hq.
    + exact Hq103.
    + exact Hn.
  - apply lw0_Wb_lt01; assumption.
Qed.

(* L(f_n) < W 0：上界传递主件（b 严格正：seq_dec_strict 前提支所需） *)
Lemma lw0_L_f_n_upper : forall (b q : Q) (n : nat)
                               (Hc : cauchy (fun m : nat => altsum (lw0_Wb b q n) m)),
  QltT 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  real_lt (lw0_L_of_seq (lw0_Wb b q n) Hc) (real_const (lw0_Wb b q n 0)).
Proof.
  intros b q n Hc Hb Hq Hq103 Hn.
  apply (lw0_L_upper (lw0_Wb b q n) Hc).
  - intros j. apply lw0_Wb_seq_nonneg.
    + apply lw0_QltT_le. exact Hb.
    + exact Hq.
  - intros j. apply lw0_Wb_seq_decr.
    + apply lw0_QltT_le. exact Hb.
    + exact Hq.
    + exact Hq103.
    + exact Hn.
  - intros j. apply lw0_Wb_seq_dec_strict; assumption.
Qed.

(* ---------- 阶乘压制链（W 0 的显式 ℚ 上界） ---------- *)

Lemma lw0_Wb0_closed : forall (b q : Q) (n : nat),
  lw0_Wb b q n 0 ==
  q_pow b n * q_pow q (2*n + 2) * lw0_q_of_nat (n + 1) / q_fact (2*n + 2).
Proof.
  intros b q n. unfold lw0_Wb.
  replace (n + 2 * 0 + 1)%nat with (Datatypes.S n)%nat by lia.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  replace (2 * n + 2 * 0 + 2)%nat with (2*n + 2)%nat by lia.
  rewrite !lw0_q_fact_step.
  replace (Datatypes.S n)%nat with (n + 1)%nat by lia.
  change (q_fact 0) with 1%Q.
  replace (lw0_q_of_nat 1 * 1)%Q with 1%Q by reflexivity.
  assert (E1 : (q_fact n * 1 * q_fact (2*n + 2))%Q ==
               (q_fact n * q_fact (2*n + 2))%Q) by ring.
  rewrite E1.
  unfold Qdiv.
  assert (HC : q_fact n * / (q_fact n * q_fact (2*n + 2)) == / q_fact (2*n + 2)).
  { rewrite (Qinv_mult_distr (q_fact n) (q_fact (2*n + 2))).
    rewrite (Qmult_assoc (q_fact n) (/ (q_fact n)) (/ (q_fact (2*n + 2)))).
    rewrite (Qmult_inv_r (q_fact n) (lw0_q_fact_ne0 n)).
    ring. }
  rewrite <- HC. ring.
Qed.

Lemma lw0_Wb0_upper : forall (b q : Q) (n : nat),
  QleT' 0 b -> QltT 0 b -> QleT' 0 q -> QleT' q (10/3) ->
  QleT' (lw0_Wb b q n 0)
        (q_pow b n * q_pow (10/3) (2*n + 2) * lw0_q_of_nat (n + 1)
                / q_fact (2*n + 2)).
Proof.
  intros b q n Hb0 Hbp Hq0 Hq103.
  apply (qleT'_trans (lw0_Wb b q n 0)
                     (q_pow b n * q_pow q (2*n + 2) * lw0_q_of_nat (n + 1) / q_fact (2*n + 2))
                     (q_pow b n * q_pow (10/3) (2*n + 2) * lw0_q_of_nat (n + 1)
                            / q_fact (2*n + 2))).
  - apply qeq_leT'. apply lw0_Wb0_closed.
  - unfold Qdiv.
    apply (lw0_qcompat4 (q_pow b n * q_pow q (2*n + 2) * lw0_q_of_nat (n + 1))
                        (q_pow b n * q_pow (10/3) (2*n + 2) * lw0_q_of_nat (n + 1))
                        (/ q_fact (2*n + 2)) (/ q_fact (2*n + 2))).
    + apply lw0_qmul_le0T.
      * apply lw0_qmul_le0T;
          [ apply lw0_q_pow_nonnegT; exact Hb0
          | apply lw0_q_pow_nonnegT; exact Hq0 ].
      * apply lw0_q_of_nat_nonneg.
    + apply (lw0_qcompat4 (q_pow b n * q_pow q (2*n + 2))
                          (q_pow b n * q_pow (10/3) (2*n + 2))
                          (lw0_q_of_nat (n + 1)) (lw0_q_of_nat (n + 1))).
      * apply lw0_qmul_le0T;
          [ apply lw0_q_pow_nonnegT; exact Hb0
          | apply lw0_q_pow_nonnegT; exact Hq0 ].
      * apply (lw0_qcompat4 (q_pow b n) (q_pow b n)
                            (q_pow q (2*n + 2)) (q_pow (10/3) (2*n + 2))).
        -- apply lw0_q_pow_nonnegT; exact Hb0.
        -- apply qleT'_refl.
        -- apply lw0_q_pow_nonnegT; exact Hq0.
        -- apply lw0_q_pow_mono_base; assumption.
      * apply lw0_q_of_nat_nonneg.
      * apply qleT'_refl.
    + apply lw0_Qlt_le. apply Qinv_lt_0_compat. apply q_fact_pos.
    + apply qleT'_refl.
Qed.

Lemma lw0_Wb0_dominated : forall (b q : Q) (n : nat),
  QleT' 0 b -> QltT 0 b -> QleT' 0 q -> QleT' q (10/3) ->
  QleT' (lw0_Wb b q n 0)
        (q_pow b n * q_pow (10/3) (2*n + 2) * lw0_q_of_nat (n + 1)
                / q_pow (lw0_q_of_nat (n + 1)) (n + 1)).
Proof.
  intros b q n Hb0 Hbp Hq0 Hq103.
  apply (qleT'_trans (lw0_Wb b q n 0)
          (q_pow b n * q_pow (10/3) (2*n + 2) * lw0_q_of_nat (n + 1)
           / q_fact (2*n + 2))
          (q_pow b n * q_pow (10/3) (2*n + 2) * lw0_q_of_nat (n + 1)
           / q_pow (lw0_q_of_nat (n + 1)) (n + 1))).
  - apply lw0_Wb0_upper; assumption.
  - apply lw0_div_le_mono.
    + apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      * apply QltT_to_Qlt. apply qmult_ltT_0_compat.
        -- apply lw0_q_pow_pos; exact Hbp.
        -- assert (Hc103 : QltT 0 (10#3)) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
           exact (lw0_q_pow_pos (10#3) (2*n + 2) Hc103).
      * apply QltT_to_Qlt. apply lw0_q_of_nat_lt0T. lia.
    + apply lw0_q_pow_pos. apply lw0_q_of_nat_lt0T. lia.
    + assert (Hgrow := lw0_fact_lower_growth (2*n + 2)%nat).
      replace (2 * n + 2)%nat with (2 * (n + 1))%nat in Hgrow by lia.
      rewrite Nat.div2_double in Hgrow.
      replace (2 * (n + 1))%nat with (2 * n + 2)%nat in Hgrow by lia.
      exact Hgrow.
Qed.

(* ---------- 阶乘双 range 分裂下界 ---------- *)

(* 幂的指数可加性：x^(m+n) == x^m·x^n，供压制链指数分裂取用。 *)
Lemma lw0_q_pow_add : forall (x : Q) (m n : nat),
  q_pow x (m + n)%nat == q_pow x m * q_pow x n.
Proof.
  intros x m n. induction n as [| n IH].
  - rewrite Nat.add_0_r, Qmult_1_r. reflexivity.
  - replace (m + Datatypes.S n)%nat with (Datatypes.S (m + n))%nat by lia.
    rewrite !q_pow_succ, IH. ring.
Qed.

(** 阶乘的双 range 分裂下界：对每个自然数 m，
    (m+1)^m · (m/2)^(m/2) ≤ (2m)!。数学含义：(2m)! 的因子表自 m 处
    分裂为前后两段，尾段 (m+1)···(2m) 共 m 个因子逐个不小于 m+1，
    前段 m! 以半数底幂压制。证明策略：尾段经因子表分解与逐因子幂
    比较，前段直用阶乘半数下界，两段下界按乘法单调合成。 *)
Lemma lw0_qfact_split_lower : forall m : nat,
  QleT' (q_pow (lw0_q_of_nat (Datatypes.S m)) m
         * q_pow (lw0_q_of_nat (Nat.div2 m)) (Nat.div2 m))%Q
        (q_fact (2 * m)%nat).
Proof.
  intro m.
  pose proof (lw0_fact_range_ge_pow m m) as Htail.
  pose proof (lw0_fact_lower_growth m) as Hhead.
  assert (Hrpos : Qle 0 (lw0_fact_range m m)).
  { apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S m)) m)
                     (lw0_fact_range m m)).
    - apply q_pow_nonneg. apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
    - exact (QleT'_to_Qle _ _ Htail). }
  apply (qleT'_trans _
          (lw0_fact_range m m * q_pow (lw0_q_of_nat (Nat.div2 m)) (Nat.div2 m))%Q).
  - apply Qle_to_QleT'. apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Htail).
    + apply q_pow_nonneg. apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
  - apply Qle_to_QleT'.
    replace (2 * m)%nat with (m + m)%nat by lia.
    rewrite lw0_q_fact_split.
    rewrite (Qmult_comm (lw0_fact_range m m)
                        (q_pow (lw0_q_of_nat (Nat.div2 m)) (Nat.div2 m))).
    apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hhead).
    + exact Hrpos.
Qed.

(* 常值函数的单调性：QleT' x y ⟹ real_le (const x) (const y) *)
Lemma lw0_real_const_le : forall x y : Q, QleT' x y -> real_le (real_const x) (real_const y).
Proof.
  intros x y H.
  destruct (Qlt_le_dec x y) as [Hlt | Hge].
  - apply inl. unfold real_lt. exists ((y - x) / 2)%Q. split.
    + apply lw0_half_pos.
      apply Qlt_to_QltT. lra.
    + exists 1%nat. intros n Hn.
      change (projT1 (real_const y) n - projT1 (real_const x) n)%Q with (y - x)%Q.
      apply (lw0_ltT_leT_trans ((y - x) / 2) (y - x) (y - x)).
      * apply Qlt_to_QltT.
        apply (lw0_mul_lt_one (y - x) (1#2));
          [ lra | unfold Qlt; simpl; lia ].
      * apply qleT'_refl.
  - apply inr. unfold real_eq.
    assert (Hxy : x == y) by (apply Qle_antisym; [ apply QleT'_to_Qle; exact H | exact Hge ]).
    intros eps Heps. exists 0%nat. intros m Hm.
    change (projT1 (real_const x) m - projT1 (real_const y) m)%Q with (x - y)%Q.
    apply (altsum_qltT_shift_l 0 eps (Qabs (x - y))).
    + rewrite Hxy. assert (Ez : (y - y)%Q == 0) by ring.
      rewrite Ez. reflexivity.
    + exact Heps.
Qed.

(* ---------- 消逝见证（W_j → 0，显式 ℤ 阈值形） ---------- *)
(* 阈值 N := Z.to_nat (Z.succ (Qceiling (25·W_0/(2·eps))))，配方照 PiEnvelope:576 先例
   （Qle_ceiling / Qle_lt_trans / Z.succ / lia-zify）。Bernoulli c:=27/25 乘-through：
   lw0_geom_lin_lb（本件在盘）给 (27/25)^j ≥ 1+2j/25 ≥ 2j/25，lw0_inv_le 转倒数得
   (25/27)^j ≤ 25/(2j)，幂互逆桥走 lw0_q_pow_mult＋lw0_q_pow_one（本件在盘），
   尾段 lw0_div_lt 直收除法形；全程 QleT'/QltT 承载，Qeq 改写仅于 Qeq 目标合法区。 *)
Lemma lw0_Wb_vanish : forall (b q : Q) (n : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall j : nat, (N <= j)%nat -> QltT (lw0_Wb b q n j) eps).
Proof.
  intros b q n Hb Hq Hq103 Hn eps Heps.
  assert (HW0pos : QltT 0 (lw0_Wb b q n 0)) by (apply lw0_Wb_pos; assumption).
  assert (Hpowinv : forall k : nat, q_pow (25#27) k * q_pow (27#25) k == 1%Q).
  { intro k.
    assert (E1 : (25#27) * (27#25) == 1%Q) by reflexivity.
    rewrite (lw0_q_pow_mult (25#27) (27#25) k), E1. apply lw0_q_pow_one. }
  assert (HTpos : QltT 0 ((25 * lw0_Wb b q n 0) / (2 * eps))).
  { apply Qlt_to_QltT. unfold Qdiv. apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat;
        [ unfold Qlt; simpl; lia | apply QltT_to_Qlt; exact HW0pos ].
    - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat;
        [ unfold Qlt; simpl; lia | apply QltT_to_Qlt; exact Heps ]. }
  assert (Hcq : Qle 0 (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)) # 1)).
  { apply (Qle_trans 0 ((25 * lw0_Wb b q n 0) / (2 * eps))
                      (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)) # 1)).
    - apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact HTpos.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)))%Z).
  { unfold Qle in Hcq. simpl in Hcq. lia. }
  exists (Z.to_nat (Z.succ (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps))))).
  intros j HjN. destruct j as [| j']. lia.
  assert (Hgeo : QleT' (lw0_Wb b q n (Datatypes.S j'))
                       (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j')))
    by (apply lw0_Wb_geo_le;
        [ apply lw0_QltT_le; exact Hb | exact Hq | exact Hq103 | exact Hn ]).
  assert (HCpos : QltT 0 (q_pow (27#25) (Datatypes.S j')))
    by (apply lw0_q_pow_pos; apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (Hc2725 : QleT' 1 (27#25)) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
  (* Bernoulli：2j/25 ≤ (27/25)^j（j = S j' ≥ 1） *)
  assert (Hbern : QleT' (lw0_q_of_nat (Datatypes.S j') * (2#25))
                        (q_pow (27#25) (Datatypes.S j'))).
  { apply (qleT'_trans (lw0_q_of_nat (Datatypes.S j') * (2#25))
                       (1 + lw0_q_of_nat (Datatypes.S j') * (2#25))
                       (q_pow (27#25) (Datatypes.S j'))).
    - apply Qle_to_QleT'. lra.
    - exact (lw0_geom_lin_lb (27#25) (Datatypes.S j') Hc2725). }
  assert (Hxpos : QltT 0 (lw0_q_of_nat (Datatypes.S j') * (2#25)))
    by (apply qmult_ltT_0_compat;
        [ apply lw0_q_of_nat_lt0T; lia
        | apply Qlt_to_QltT; unfold Qlt; simpl; lia ]).
  (* 倒数比较：(25/27)^j == /(27/25)^j ≤ /(2j/25) *)
  assert (HC0 : q_pow (27#25) (Datatypes.S j') == 0 -> False)
    by (apply qltT_not_eq_zero; exact HCpos).
  assert (EP : q_pow (25#27) (Datatypes.S j') == / (q_pow (27#25) (Datatypes.S j'))).
  { apply (Qeq_trans _ (q_pow (25#27) (Datatypes.S j') *
                        (q_pow (27#25) (Datatypes.S j') * / (q_pow (27#25) (Datatypes.S j'))))).
    - rewrite (Qmult_inv_r (q_pow (27#25) (Datatypes.S j')) HC0). ring.
    - rewrite (Qmult_assoc (q_pow (25#27) (Datatypes.S j'))
                           (q_pow (27#25) (Datatypes.S j'))
                           (/ (q_pow (27#25) (Datatypes.S j')))),
              (Hpowinv (Datatypes.S j')). ring. }
  assert (Hinv2 : QleT' (/ (q_pow (27#25) (Datatypes.S j')))
                        (/ (lw0_q_of_nat (Datatypes.S j') * (2#25))))
    by (apply lw0_inv_le; [ exact Hxpos | exact HCpos | exact Hbern ]).
  assert (Hgeow : QleT' (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j'))
                        (lw0_Wb b q n 0 * / (lw0_q_of_nat (Datatypes.S j') * (2#25)))).
  { apply (lw0_qcompat_l (q_pow (25#27) (Datatypes.S j'))
                         (/ (lw0_q_of_nat (Datatypes.S j') * (2#25)))
                         (lw0_Wb b q n 0)).
    - apply (qleT'_trans (q_pow (25#27) (Datatypes.S j'))
                         (/ (q_pow (27#25) (Datatypes.S j')))
                         (/ (lw0_q_of_nat (Datatypes.S j') * (2#25)))).
      + apply qeq_leT'. exact EP.
      + exact Hinv2.
    - apply lw0_QltT_le. exact HW0pos.
    - apply lw0_QltT_le. apply lw0_q_pow_pos. apply Qlt_to_QltT. unfold Qlt. simpl. lia. }
  (* 阈值乘-through：T := 25·W_0/(2·eps)；j ≥ N ⟹ T < j ⟹ 25·W_0 < 2j·eps *)
  assert (Hstep : Qlt ((25 * lw0_Wb b q n 0) / (2 * eps))
                      ((Z.succ (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)))) # 1)).
  { apply (Qle_lt_trans ((25 * lw0_Wb b q n 0) / (2 * eps))
                        (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)) # 1)
                        ((Z.succ (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)))) # 1)).
    - apply Qle_ceiling.
    - unfold Qlt, Qle. simpl. lia. }
  assert (Hzlt : (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps))
                  < Z.of_nat (Datatypes.S j'))%Z) by lia.
  assert (Hle2 : Qle ((Z.succ (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)))) # 1)
                     ((Z.of_nat (Datatypes.S j')) # 1))
    by (unfold Qle; simpl; lia).
  assert (Hlt0 : Qlt ((25 * lw0_Wb b q n 0) / (2 * eps))
                     ((Z.of_nat (Datatypes.S j')) # 1)).
  { apply (Qlt_le_trans ((25 * lw0_Wb b q n 0) / (2 * eps))
                        ((Z.succ (Qceiling ((25 * lw0_Wb b q n 0) / (2 * eps)))) # 1)
                        ((Z.of_nat (Datatypes.S j')) # 1));
      [ exact Hstep | exact Hle2 ]. }
  assert (Heps2 : Qlt 0 (2 * eps)).
  { apply Qmult_lt_0_compat.
    - unfold Qlt; simpl; lia.
    - apply QltT_to_Qlt; exact Heps. }
  assert (HE0 : (2 * eps) == 0 -> False) by (apply qltT_not_eq_zero; apply Qlt_to_QltT; exact Heps2).
  assert (Eprod : ((25 * lw0_Wb b q n 0) * / (2 * eps)) * (2 * eps)
                  == 25 * lw0_Wb b q n 0).
  { rewrite <- (Qmult_assoc (25 * lw0_Wb b q n 0) (/ (2 * eps)) (2 * eps)).
    rewrite (Qmult_comm (/ (2 * eps)) (2 * eps)), (Qmult_inv_r (2 * eps) HE0). ring. }
  assert (Hmul : Qlt (25 * lw0_Wb b q n 0)
                     (((Z.of_nat (Datatypes.S j')) # 1) * (2 * eps))).
  { setoid_replace (25 * lw0_Wb b q n 0)
      with (((25 * lw0_Wb b q n 0) * / (2 * eps)) * (2 * eps))
      by (apply Qeq_sym; exact Eprod).
    apply (Qmult_lt_compat_r ((25 * lw0_Wb b q n 0) * / (2 * eps))
                             ((Z.of_nat (Datatypes.S j')) # 1) (2 * eps) Heps2 Hlt0). }
  assert (Ec : (/ (2#25))%Q == 25 * / 2) by reflexivity.
  assert (EA1 : lw0_q_of_nat (Datatypes.S j') == (Z.of_nat (Datatypes.S j')) # 1)
    by reflexivity.
  assert (Efin : lw0_Wb b q n 0 * / (lw0_q_of_nat (Datatypes.S j') * (2#25))
                 == (25 * lw0_Wb b q n 0) * / (2 * lw0_q_of_nat (Datatypes.S j'))).
  { rewrite (Qinv_mult_distr (lw0_q_of_nat (Datatypes.S j')) (2#25)), Ec,
            (Qinv_mult_distr 2 (lw0_q_of_nat (Datatypes.S j'))). ring. }
  assert (Hbridge : QleT' (((Z.of_nat (Datatypes.S j')) # 1) * (2 * eps))
                          (eps * (2 * lw0_q_of_nat (Datatypes.S j')))).
  { apply qeq_leT'. rewrite <- EA1. ring. }
  assert (Hdiv : QltT ((25 * lw0_Wb b q n 0) / (2 * lw0_q_of_nat (Datatypes.S j'))) eps).
  { apply lw0_div_lt.
    - apply qmult_ltT_0_compat.
      + apply Qlt_to_QltT. unfold Qlt. simpl. lia.
      + apply lw0_q_of_nat_lt0T. lia.
    - apply (lw0_ltT_leT_trans (25 * lw0_Wb b q n 0)
                               (((Z.of_nat (Datatypes.S j')) # 1) * (2 * eps))
                               (eps * (2 * lw0_q_of_nat (Datatypes.S j')))).
      + apply Qlt_to_QltT. exact Hmul.
      + exact Hbridge. }
  apply (lw0_leT'_ltT_trans (lw0_Wb b q n (Datatypes.S j'))
                            ((25 * lw0_Wb b q n 0) / (2 * lw0_q_of_nat (Datatypes.S j')))
                            eps).
  - apply (qleT'_trans (lw0_Wb b q n (Datatypes.S j'))
                       (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j'))
                       ((25 * lw0_Wb b q n 0) / (2 * lw0_q_of_nat (Datatypes.S j')))).
    + exact Hgeo.
    + apply (qleT'_trans (lw0_Wb b q n 0 * q_pow (25#27) (Datatypes.S j'))
                         (lw0_Wb b q n 0 * / (lw0_q_of_nat (Datatypes.S j') * (2#25)))
                         ((25 * lw0_Wb b q n 0) / (2 * lw0_q_of_nat (Datatypes.S j')))).
      * exact Hgeow.
      * apply qeq_leT'. exact Efin.
  - exact Hdiv.
Qed.

(* 闭环柯西见证：实例化 lw0_altseq_cauchy（W := lw0_Wb b q n）——
   消逝见证结论形（sigT＋Nat.le 界）直接喂其第三前提，交错部分和为柯西列。 *)
Corollary lw0_Wb_altseq_cauchy : forall (b q : Q) (n : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  cauchy (fun m : nat => altsum (lw0_Wb b q n) m).
Proof.
  intros b q n Hb Hq Hq103 Hn.
  apply (lw0_altseq_cauchy (lw0_Wb b q n)).
  - intros k. apply lw0_Wb_seq_nonneg; [ apply lw0_QltT_le; exact Hb | exact Hq ].
  - intros k. apply lw0_Wb_seq_decr;
      [ apply lw0_QltT_le; exact Hb | exact Hq | exact Hq103 | exact Hn ].
  - intros eps Heps. apply lw0_Wb_vanish; assumption.
Qed.


(* ================= §4 端点泛函与反导数构造 ================= *)
(* 段体来源：LW0Endpoint.v 现势 2080 行 md5 cb265ac19710f678dcd3b60912686d73
   （S05 全量闭合版），取形时点 2026 09 29。内嵌适配面：QPoly 由 §1 在件
   供形（qpoly 记号在 §1 尾），Require 面、提取面与公理自审面并入件级尾段。
   以 S05 定版为准按三元组重验。 *)

(* 接口适配壳：契约名 qpoly 对实产 QPoly。 *)

(* ------------------------------------------------------------------ *)
(* 接口缺口自带件（_tlw06_ :119 预留：S04 未交付 qpoly_zero/qpoly_opp，  *)
(* 本件自带）。                                                          *)
(* ------------------------------------------------------------------ *)

Definition qpoly_zero : qpoly := nil.

Fixpoint qpoly_opp (p : qpoly) : qpoly :=
  match p with
  | nil => nil
  | cons a p' => cons (- a)%Q (qpoly_opp p')
  end.

(* ------------------------------------------------------------------ *)
(* 除法消因子助手：除数恒为 (z # 1) 形，故无需非零前提。                  *)
(* ------------------------------------------------------------------ *)

(* (z # 1) 的逆在正整数分母下回到 1；前提 (0 < z)%Z 在全部应用处由     *)
(* 除数恒为 Z.of_nat (S k)（k:nat 恒正）卸载。                          *)
Lemma lw0_q_int_inv : forall z : Z, (0 < z)%Z -> (z # 1) * (/ (z # 1)) == 1.
Proof.
  intros z Hz.
  unfold Qeq, Qmult, Qinv.
  destruct z; simpl; try ring; lia.
Qed.

Lemma lw0_q_div_int_mul : forall (z : Z) (a : Q),
  (0 < z)%Z -> (z # 1) * (a / (z # 1)) == a.
Proof.
  intros z a Hz.
  change (a / (z # 1)) with (a * / (z # 1)).
  rewrite (Qmult_assoc (z # 1) a (/ (z # 1))).
  rewrite (Qmult_comm (z # 1) a).
  rewrite <- (Qmult_assoc a (z # 1) (/ (z # 1))).
  rewrite (lw0_q_int_inv z Hz).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 逐项不定积分：递归携带次数指标 k（第 j 层系数除以 j+k+1）。             *)
(* 数学形：lw0_qp_ai p k = sum_j p_j t^j/(j+k+1)；lw0_qp_antideriv p      *)
(* = cons 0 (lw0_qp_ai p 0) = sum_j p_j t^{j+1}/(j+1)。                  *)
(* ------------------------------------------------------------------ *)

Fixpoint lw0_qp_ai (p : qpoly) (k : nat) : qpoly :=
  match p with
  | nil => nil
  | cons a p' => cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p' (S k))
  end.

Definition lw0_qp_antideriv (p : qpoly) : qpoly := cons 0 (lw0_qp_ai p 0).

(* 求值基础：Horner 逐层展开。 *)
Lemma lw0_qp_ai_cons_eval : forall a p k x,
  qpoly_eval (lw0_qp_ai (cons a p) k) x ==
  a / (Z.of_nat (S k) # 1) + x * qpoly_eval (lw0_qp_ai p (S k)) x.
Proof.
  intros a p k x.
  change (lw0_qp_ai (cons a p) k)
    with (cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p (S k))).
  change (qpoly_eval (cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p (S k))) x)
    with (a / (Z.of_nat (S k) # 1)
            + x * qpoly_eval (lw0_qp_ai p (S k)) x).
  reflexivity.
Qed.

(* 常数项零表的求值：0/(k+1) 与 0 相消。 *)
Lemma lw0_qp_ai_zero_head_eval : forall p k x,
  qpoly_eval (lw0_qp_ai (cons 0 p) k) x == x * qpoly_eval (lw0_qp_ai p (S k)) x.
Proof.
  intros p k x.
  rewrite (lw0_qp_ai_cons_eval 0 p k x).
  assert (Hz : 0 / (Z.of_nat (S k) # 1) == 0) by (unfold Qdiv; ring).
  rewrite Hz.
  ring.
Qed.

(* 求值可加性：对被积分表的第一变元归纳，次数指标随层递增。 *)
Lemma lw0_qp_ai_add : forall p q k x,
  qpoly_eval (lw0_qp_ai (qpoly_add p q) k) x ==
  qpoly_eval (lw0_qp_ai p k) x + qpoly_eval (lw0_qp_ai q k) x.
Proof.
  induction p as [|a p IH]; intros q k x.
  - simpl. ring.
  - destruct q as [|b q].
    + change (qpoly_add (cons a p) nil) with (cons a p).
      change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
      ring.
    + change (qpoly_add (cons a p) (cons b q))
        with (cons (a + b) (qpoly_add p q)).
      rewrite (lw0_qp_ai_cons_eval (a + b) (qpoly_add p q) k x).
      rewrite (lw0_qp_ai_cons_eval a p k x).
      rewrite (lw0_qp_ai_cons_eval b q k x).
      rewrite (IH q (S k) x).
      change ((a + b) / (Z.of_nat (S k) # 1))
        with ((a + b) * / (Z.of_nat (S k) # 1)).
      change (a / (Z.of_nat (S k) # 1))
        with (a * / (Z.of_nat (S k) # 1)).
      change (b / (Z.of_nat (S k) # 1))
        with (b * / (Z.of_nat (S k) # 1)).
      ring.
Qed.

(* 求值数乘齐性。 *)
Lemma lw0_qp_ai_scalar : forall c p k x,
  qpoly_eval (lw0_qp_ai (qpoly_scalar c p) k) x ==
  c * qpoly_eval (lw0_qp_ai p k) x.
Proof.
  intros c p.
  induction p as [|a p IH]; intros k x.
  - simpl. ring.
  - change (qpoly_scalar c (cons a p)) with (cons (c * a) (qpoly_scalar c p)).
    rewrite (lw0_qp_ai_cons_eval (c * a) (qpoly_scalar c p) k x).
    rewrite (lw0_qp_ai_cons_eval a p k x).
    rewrite IH.
    change ((c * a) / (Z.of_nat (S k) # 1))
      with ((c * a) * / (Z.of_nat (S k) # 1)).
    change (a / (Z.of_nat (S k) # 1))
      with (a * / (Z.of_nat (S k) # 1)).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 右逆律的归纳核：积分片与其导数的加权恒等式（次数指标族）。              *)
(* 数学内容：(k+1)·t^k·A_k(t) + t^{k+1}·A_k'(t) = t^k·p(t)，其中          *)
(* A_k := lw0_qp_ai p k。cons 层与 k+1 指标处的归纳假设恰好相接。          *)
(* ------------------------------------------------------------------ *)

Lemma lw0_qp_ai_deriv_pair : forall p k x,
  (Z.of_nat (S k) # 1) * q_pow x k * qpoly_eval (lw0_qp_ai p k) x
  + q_pow x (S k) * qpoly_eval (qpoly_deriv (lw0_qp_ai p k)) x
  == q_pow x k * qpoly_eval p x.
Proof.
  induction p as [|a p IH]; intros k x.
  - simpl. ring.
  - assert (Hpos : (0 < Z.of_nat (S k))%Z) by lia.
    assert (Hz : (Z.of_nat (S k) # 1) * (a / (Z.of_nat (S k) # 1)) == a)
      by exact (lw0_q_div_int_mul (Z.of_nat (S k)) a Hpos).
    assert (Hn : Z.of_nat (S (S k)) = (Z.of_nat (S k) + 1)%Z) by lia.
    assert (Hz2 : ((Z.of_nat (S k) # 1)%Q + 1)%Q
                  == (Z.of_nat (S (S k)) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn; lia).
    assert (Hf := IH (S k) x).
    rewrite <- Hz2 in Hf.
    rewrite (q_pow_succ x (S k)) in Hf.
    rewrite (q_pow_succ x k) in Hf.
    rewrite (lw0_qp_ai_cons_eval a p k x).
    change (qpoly_deriv (cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p (S k))))
      with (qpoly_add (lw0_qp_ai p (S k))
              (cons 0 (qpoly_deriv (lw0_qp_ai p (S k))))).
    rewrite (qpoly_eval_add (lw0_qp_ai p (S k))
               (cons 0 (qpoly_deriv (lw0_qp_ai p (S k)))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (lw0_qp_ai p (S k)))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p (S k))) x).
    change (q_pow x (S k)) with (x * q_pow x k).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    assert (Hd : (Z.of_nat (S k) # 1) * q_pow x k
                   * (a / (Z.of_nat (S k) # 1)
                      + x * qpoly_eval (lw0_qp_ai p (S k)) x)
                 == q_pow x k * a
                    + (Z.of_nat (S k) # 1) * q_pow x k * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x).
    { transitivity ((Z.of_nat (S k) # 1) * q_pow x k
                      * (a / (Z.of_nat (S k) # 1))
                    + (Z.of_nat (S k) # 1) * q_pow x k * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x)%Q.
      - ring.
      - rewrite <- (Qmult_assoc (Z.of_nat (S k) # 1) (q_pow x k)
                      (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_comm (q_pow x k) (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_assoc (Z.of_nat (S k) # 1) (a / (Z.of_nat (S k) # 1))
                   (q_pow x k)).
        rewrite Hz.
        ring. }
    rewrite Hd.
    assert (Hg : q_pow x k * a
                 + x * q_pow x k * (((Z.of_nat (S k) # 1)%Q + 1)
                                      * qpoly_eval (lw0_qp_ai p (S k)) x
                                      + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p (S k))) x)
                 == q_pow x k * a + x * q_pow x k * qpoly_eval p x).
    { rewrite <- Hf. ring. }
    transitivity (q_pow x k * a
                    + x * q_pow x k * (((Z.of_nat (S k) # 1)%Q + 1)
                                         * qpoly_eval (lw0_qp_ai p (S k)) x
                                         + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p (S k))) x))%Q.
    { ring. }
    { rewrite Hg. ring. }
Qed.

(* 右逆律：先积分后求导，逐点还原。 *)
Lemma lw0_qp_antideriv_deriv : forall p x,
  qpoly_eval (qpoly_deriv (lw0_qp_antideriv p)) x == qpoly_eval p x.
Proof.
  intros p x.
  unfold lw0_qp_antideriv.
  change (qpoly_deriv (cons 0 (lw0_qp_ai p 0)))
    with (qpoly_add (lw0_qp_ai p 0) (cons 0 (qpoly_deriv (lw0_qp_ai p 0)))).
  rewrite (qpoly_eval_add (lw0_qp_ai p 0)
             (cons 0 (qpoly_deriv (lw0_qp_ai p 0))) x).
  change (qpoly_eval (cons 0 (qpoly_deriv (lw0_qp_ai p 0))) x)
    with (0 + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p 0)) x).
  assert (Hk := lw0_qp_ai_deriv_pair p 0 x).
  assert (Hz1 : (Z.of_nat (S 0) # 1)%Q == 1) by reflexivity.
  assert (H1 : q_pow x 0 == 1) by reflexivity.
  assert (Hs : q_pow x (S 0) == x).
  { change (q_pow x (S 0)) with (x * q_pow x 0).
    change (q_pow x 0) with 1.
    ring. }
  rewrite Hz1 in Hk.
  rewrite H1 in Hk.
  rewrite Hs in Hk.
  transitivity (1 * 1 * qpoly_eval (lw0_qp_ai p 0) x
                + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p 0)) x)%Q.
  { ring. }
  { rewrite Hk. ring. }
Qed.

(* ------------------------------------------------------------------ *)
(* 牛顿-莱布尼茨律的归纳核：求导片的积分恒等式（次数指标族）。             *)
(* 数学内容：t^{k+2}·B_{k+1}(t) + (k+1)·t^{k+1}·A_k(t) = t^{k+1}·p(t)，   *)
(* 其中 A_k := ai p k，B_{k+1} := ai (deriv p) (S k)。                    *)
(* ------------------------------------------------------------------ *)

Lemma lw0_qp_ai_deriv_ft : forall p k x,
  q_pow x (S (S k)) * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S k)) x
  + (Z.of_nat (S k) # 1) * q_pow x (S k) * qpoly_eval (lw0_qp_ai p k) x
  == q_pow x (S k) * qpoly_eval p x.
Proof.
  induction p as [|a p IH]; intros k x.
  - simpl. ring.
  - assert (Hpos : (0 < Z.of_nat (S k))%Z) by lia.
    assert (Hz : (Z.of_nat (S k) # 1) * (a / (Z.of_nat (S k) # 1)) == a)
      by exact (lw0_q_div_int_mul (Z.of_nat (S k)) a Hpos).
    assert (Hn : Z.of_nat (S (S k)) = (Z.of_nat (S k) + 1)%Z) by lia.
    assert (Hz2 : ((Z.of_nat (S k) # 1)%Q + 1)%Q
                  == (Z.of_nat (S (S k)) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn; lia).
    assert (Hf := IH (S k) x).
    rewrite <- Hz2 in Hf.
    rewrite (q_pow_succ x (S (S k))) in Hf.
    rewrite (q_pow_succ x (S k)) in Hf.
    rewrite (q_pow_succ x k) in Hf.
    change (qpoly_deriv (cons a p))
      with (qpoly_add p (cons 0 (qpoly_deriv p))).
    rewrite (lw0_qp_ai_add p (cons 0 (qpoly_deriv p)) (S k) x).
    change (lw0_qp_ai (cons 0 (qpoly_deriv p)) (S k))
      with (cons (0 / (Z.of_nat (S (S k)) # 1))
              (lw0_qp_ai (qpoly_deriv p) (S (S k)))).
    change (qpoly_eval
              (cons (0 / (Z.of_nat (S (S k)) # 1))
                 (lw0_qp_ai (qpoly_deriv p) (S (S k)))) x)
      with (0 / (Z.of_nat (S (S k)) # 1)
              + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S (S k))) x).
    rewrite (lw0_qp_ai_cons_eval a p k x).
    change (q_pow x (S (S k))) with (x * q_pow x (S k)).
    change (q_pow x (S k)) with (x * q_pow x k).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    assert (Hz0 : 0 / (Z.of_nat (S (S k)) # 1) == 0)
      by (unfold Qdiv; ring).
    rewrite Hz0.
    assert (Hd : (Z.of_nat (S k) # 1) * (x * q_pow x k)
                   * (a / (Z.of_nat (S k) # 1)
                      + x * qpoly_eval (lw0_qp_ai p (S k)) x)
                 == (x * q_pow x k) * a
                    + (Z.of_nat (S k) # 1) * (x * q_pow x k) * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x).
    { transitivity ((Z.of_nat (S k) # 1) * (x * q_pow x k)
                      * (a / (Z.of_nat (S k) # 1))
                    + (Z.of_nat (S k) # 1) * (x * q_pow x k) * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x)%Q.
      - ring.
      - rewrite <- (Qmult_assoc (Z.of_nat (S k) # 1) (x * q_pow x k)
                      (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_comm (x * q_pow x k) (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_assoc (Z.of_nat (S k) # 1) (a / (Z.of_nat (S k) # 1))
                   (x * q_pow x k)).
        rewrite Hz.
        ring. }
    rewrite Hd.
    assert (Hg : q_pow x k * x * x
                   * (((Z.of_nat (S k) # 1)%Q + 1) * qpoly_eval (lw0_qp_ai p (S k)) x
                      + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S (S k))) x)
                 == x * (x * q_pow x k) * qpoly_eval p x).
    { rewrite <- Hf. ring. }
    transitivity ((x * q_pow x k) * a
                    + q_pow x k * x * x
                        * (((Z.of_nat (S k) # 1)%Q + 1) * qpoly_eval (lw0_qp_ai p (S k)) x
                           + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S (S k))) x))%Q.
    { ring. }
    { rewrite Hg. ring. }
Qed.

(* 牛顿-莱布尼茨律：先求导后积分，相差常数值（eval 层基本定理）。 *)
Lemma lw0_qp_antideriv_deriv_at : forall p x,
  qpoly_eval (lw0_qp_antideriv (qpoly_deriv p)) x
  == qpoly_eval p x - qpoly_eval p 0.
Proof.
  induction p as [|a p IH]; intros x.
  - simpl. ring.
  - assert (Hf := lw0_qp_ai_deriv_ft p 0 x).
    rewrite (q_pow_succ x (S 0)) in Hf.
    rewrite (q_pow_succ x 0) in Hf.
    change (q_pow x 0) with 1 in Hf.
    assert (Hz1 : (Z.of_nat (S 0) # 1)%Q == 1) by reflexivity.
    rewrite Hz1 in Hf.
    rewrite (Qmult_1_r x) in Hf.
    change (qpoly_deriv (cons a p))
      with (qpoly_add p (cons 0 (qpoly_deriv p))).
    unfold lw0_qp_antideriv.
    change (qpoly_eval
              (cons 0
                 (lw0_qp_ai (qpoly_add p (cons 0 (qpoly_deriv p))) 0)) x)
      with (0 + x * qpoly_eval
              (lw0_qp_ai (qpoly_add p (cons 0 (qpoly_deriv p))) 0) x).
    rewrite (lw0_qp_ai_add p (cons 0 (qpoly_deriv p)) 0 x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_deriv p) 0 x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    change (qpoly_eval (cons a p) 0%Q) with (a + 0 * qpoly_eval p 0%Q).
    assert (Hg : x * (qpoly_eval (lw0_qp_ai p 0) x
                        + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S 0)) x)
                 == x * qpoly_eval p x).
    { rewrite <- Hf. ring. }
    rewrite Hg.
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 超次数零化：求导次数达到表长即逐点为零（表长 ≥ 多项式次数 + 1）。       *)
(* 判据取 (length p <= n)%nat：nat/Z 序前提为已注册语句先例形             *)
(* （bno_qfact_scale_d 型先例）。                                  *)
(* ------------------------------------------------------------------ *)

(* 求和的表长不超过两表长的较大者（内部桥接）。 *)
Lemma lw0_qp_length_add : forall p q,
  (length (qpoly_add p q) <= Nat.max (length p) (length q))%nat.
Proof.
  induction p as [|a p IH]; intros q.
  - simpl. lia.
  - destruct q as [|b q].
    + simpl. lia.
    + change (qpoly_add (cons a p) (cons b q))
        with (cons (a + b) (qpoly_add p q)).
      simpl.
      specialize (IH q).
      lia.
Qed.

(* 求导不增表长（内部桥接）。 *)
Lemma lw0_qp_length_deriv : forall p,
  (length (qpoly_deriv p) <= length p)%nat.
Proof.
  induction p as [|a p IH].
  - simpl. lia.
  - change (qpoly_deriv (cons a p))
      with (qpoly_add p (cons 0 (qpoly_deriv p))).
    assert (H := lw0_qp_length_add p (cons 0 (qpoly_deriv p))).
    simpl in H.
    simpl.
    lia.
Qed.

(* 迭代求导的次数加法拆分（list 层等式）。 *)
Lemma lw0_qp_deriv_iter_plus : forall n m p,
  qpoly_deriv_iter (n + m) p = qpoly_deriv_iter n (qpoly_deriv_iter m p).
Proof.
  induction n as [|n IH]; intros m p.
  - reflexivity.
  - change (qpoly_deriv_iter (S n + m) p)
      with (qpoly_deriv (qpoly_deriv_iter (n + m) p)).
    rewrite (IH m p).
    reflexivity.
Qed.

(* 迭代求导在求值层的可加性：该等式的 S n 步需把 deriv 穿过 add 的 list     *)
(* 分解——正撞 qpoly_deriv_mul 同款表示墙                                   *)
(* （deriv(add p q) 与 add(deriv p)(deriv q) 仅 eval 相等、list 不等），    *)
(* 且本文件内无使用处，故不收录（诊断存同波交付记录）。                      *)

(* 超次数零化（lw0_qp_deriv_iter_zero）：语句 (length p <= n) ->            *)
(* eval (deriv_iter n p) x == 0 存在粗粒度表长障碍——length 含尾零不        *)
(* 收缩（deriv (a::p) = add p (cons 0 (deriv p)) 的表长可达 S (length p)，  *)
(* n-归纳与 p-归纳双双无法卸载归纳前提；正解=先建 eval (deriv_iter m (add)) *)
(* 可加性＋cons-0 核的互归纳论证（40–60 行）或改用 qpoly_degree 规范化）。  *)
(* 本文件内无使用处（lw0_F_plus_deriv2 未落），故暂不收录（诊断存交付记录）；*)
(* length 两件保留为后继施工基础设施。                                       *)

(* ------------------------------------------------------------------ *)
(* 单项式与配对积。                                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint lw0_mono (m : nat) : qpoly :=
  match m with
  | 0%nat => cons 1 nil
  | Datatypes.S m' => cons 0 (lw0_mono m')
  end.

Lemma lw0_mono_eval : forall m x, qpoly_eval (lw0_mono m) x == q_pow x m.
Proof.
  induction m as [|m IH]; intros x.
  - change (qpoly_eval (lw0_mono 0) x) with (1 + x * qpoly_eval nil x)%Q.
    change (qpoly_eval nil x) with 0%Q.
    change (q_pow x 0) with 1.
    ring.
  - change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
    change (qpoly_eval (cons 0 (lw0_mono m)) x)
      with (0 + x * qpoly_eval (lw0_mono m) x).
    rewrite IH.
    rewrite (q_pow_succ x m).
    ring.
Qed.

(* 配对积：积分型双线性泛函 <f,g>_q := 积分片 mul f g 在 q 的取值。 *)
Definition lw0_qp_pair (f g : qpoly) (q : Q) : Q :=
  qpoly_eval (lw0_qp_antideriv (qpoly_mul f g)) q.

(* 双线性生成元其一：mul 对第一变元加法的积分片可加（次数指标族）。 *)
Lemma lw0_qp_ai_mul_add_l : forall f1 f2 g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_add f1 f2) g) k) x ==
  qpoly_eval (lw0_qp_ai (qpoly_mul f1 g) k) x
  + qpoly_eval (lw0_qp_ai (qpoly_mul f2 g) k) x.
Proof.
  induction f1 as [|a f1 IH]; intros f2 g k x.
  - change (qpoly_add nil f2) with f2.
    change (qpoly_mul nil g) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - destruct f2 as [|b f2].
    + change (qpoly_add (cons a f1) nil) with (cons a f1).
      change (qpoly_mul nil g) with (@nil Q).
      change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
      ring.
    + change (qpoly_add (cons a f1) (cons b f2))
        with (cons (a + b) (qpoly_add f1 f2)).
      change (qpoly_mul (cons (a + b) (qpoly_add f1 f2)) g)
        with (qpoly_add (qpoly_scalar (a + b) g)
                (cons 0 (qpoly_mul (qpoly_add f1 f2) g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar (a + b) g)
                 (cons 0 (qpoly_mul (qpoly_add f1 f2) g)) k x).
      rewrite (lw0_qp_ai_scalar (a + b) g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_add f1 f2) g) k x).
      rewrite (IH f2 g (S k) x).
      change (qpoly_mul (cons a f1) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f1 g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g) (cons 0 (qpoly_mul f1 g)) k x).
      rewrite (lw0_qp_ai_scalar a g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f1 g) k x).
      change (qpoly_mul (cons b f2) g)
        with (qpoly_add (qpoly_scalar b g) (cons 0 (qpoly_mul f2 g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar b g) (cons 0 (qpoly_mul f2 g)) k x).
      rewrite (lw0_qp_ai_scalar b g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f2 g) k x).
      ring.
Qed.

(* 双线性生成元其二：mul 对第一变元数乘的积分片齐性。 *)
Lemma lw0_qp_ai_mul_scalar_l : forall c f g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_scalar c f) g) k) x ==
  c * qpoly_eval (lw0_qp_ai (qpoly_mul f g) k) x.
Proof.
  intros c f.
  induction f as [|a f IH]; intros g k x.
  - change (qpoly_scalar c nil) with (@nil Q).
    change (qpoly_mul nil g) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - change (qpoly_scalar c (cons a f)) with (cons (c * a) (qpoly_scalar c f)).
    change (qpoly_mul (cons (c * a) (qpoly_scalar c f)) g)
      with (qpoly_add (qpoly_scalar (c * a) g)
              (cons 0 (qpoly_mul (qpoly_scalar c f) g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar (c * a) g)
               (cons 0 (qpoly_mul (qpoly_scalar c f) g)) k x).
    rewrite (lw0_qp_ai_scalar (c * a) g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_scalar c f) g) k x).
    rewrite IH.
    change (qpoly_mul (cons a f) g)
      with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g)) k x).
    rewrite (lw0_qp_ai_scalar a g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g) k x).
    ring.
Qed.

(* 双线性生成元其三：mul 对第二变元加法的积分片可加（对 f 归纳）。 *)
Lemma lw0_qp_ai_mul_add_r : forall f g1 g2 k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_add g1 g2)) k) x ==
  qpoly_eval (lw0_qp_ai (qpoly_mul f g1) k) x
  + qpoly_eval (lw0_qp_ai (qpoly_mul f g2) k) x.
Proof.
  induction f as [|a f IH]; intros g1 g2 k x.
  - change (qpoly_mul nil (qpoly_add g1 g2)) with (@nil Q).
    change (qpoly_mul nil g1) with (@nil Q).
    change (qpoly_mul nil g2) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - change (qpoly_mul (cons a f) (qpoly_add g1 g2))
      with (qpoly_add (qpoly_scalar a (qpoly_add g1 g2))
              (cons 0 (qpoly_mul f (qpoly_add g1 g2)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_add g1 g2))
               (cons 0 (qpoly_mul f (qpoly_add g1 g2))) k x).
    rewrite (lw0_qp_ai_scalar a (qpoly_add g1 g2) k x).
    rewrite (lw0_qp_ai_add g1 g2 k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f (qpoly_add g1 g2)) k x).
    rewrite (IH g1 g2 (S k) x).
    change (qpoly_mul (cons a f) g1)
      with (qpoly_add (qpoly_scalar a g1) (cons 0 (qpoly_mul f g1))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g1) (cons 0 (qpoly_mul f g1)) k x).
    rewrite (lw0_qp_ai_scalar a g1 k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g1) k x).
    change (qpoly_mul (cons a f) g2)
      with (qpoly_add (qpoly_scalar a g2) (cons 0 (qpoly_mul f g2))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g2) (cons 0 (qpoly_mul f g2)) k x).
    rewrite (lw0_qp_ai_scalar a g2 k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g2) k x).
    ring.
Qed.

(* 双线性生成元其四：mul 对第二变元数乘的积分片齐性。 *)
Lemma lw0_qp_ai_mul_scalar_r : forall c f g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_scalar c g)) k) x ==
  c * qpoly_eval (lw0_qp_ai (qpoly_mul f g) k) x.
Proof.
  intros c f.
  induction f as [|a f IH]; intros g k x.
  - change (qpoly_mul nil (qpoly_scalar c g)) with (@nil Q).
    change (qpoly_mul nil g) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - change (qpoly_mul (cons a f) (qpoly_scalar c g))
      with (qpoly_add (qpoly_scalar a (qpoly_scalar c g))
              (cons 0 (qpoly_mul f (qpoly_scalar c g)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_scalar c g))
               (cons 0 (qpoly_mul f (qpoly_scalar c g))) k x).
    rewrite (lw0_qp_ai_scalar a (qpoly_scalar c g) k x).
    rewrite (lw0_qp_ai_scalar c g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f (qpoly_scalar c g)) k x).
    rewrite IH.
    change (qpoly_mul (cons a f) g)
      with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g)) k x).
    rewrite (lw0_qp_ai_scalar a g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g) k x).
    ring.
Qed.

(* 配对积双线性四件：由生成元在 k = 0 处直读。 *)

Lemma lw0_qp_pair_add_l : forall f1 f2 g q,
  lw0_qp_pair (qpoly_add f1 f2) g q
  == lw0_qp_pair f1 g q + lw0_qp_pair f2 g q.
Proof.
  intros f1 f2 g q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul (qpoly_add f1 f2) g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_add f1 f2) g) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f1 g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f1 g) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f2 g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f2 g) 0) q).
  rewrite (lw0_qp_ai_mul_add_l f1 f2 g 0 q).
  ring.
Qed.

Lemma lw0_qp_pair_add_r : forall f g1 g2 q,
  lw0_qp_pair f (qpoly_add g1 g2) q
  == lw0_qp_pair f g1 q + lw0_qp_pair f g2 q.
Proof.
  intros f g1 g2 q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f (qpoly_add g1 g2)) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_add g1 g2)) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g1) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g1) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g2) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g2) 0) q).
  rewrite (lw0_qp_ai_mul_add_r f g1 g2 0 q).
  ring.
Qed.

Lemma lw0_qp_pair_scalar_l : forall c f g q,
  lw0_qp_pair (qpoly_scalar c f) g q == c * lw0_qp_pair f g q.
Proof.
  intros c f g q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul (qpoly_scalar c f) g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_scalar c f) g) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q).
  rewrite (lw0_qp_ai_mul_scalar_l c f g 0 q).
  ring.
Qed.

Lemma lw0_qp_pair_scalar_r : forall c f g q,
  lw0_qp_pair f (qpoly_scalar c g) q == c * lw0_qp_pair f g q.
Proof.
  intros c f g q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f (qpoly_scalar c g)) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_scalar c g)) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q).
  rewrite (lw0_qp_ai_mul_scalar_r c f g 0 q).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 提取与假设核验。                                                  *)
(* ------------------------------------------------------------------ *)



(* ------------------------------------------------------------------ *)
(* 分部积分层。数学内容：配对积满足 <R',S>_q + <R,S'>_q = (RS)(q)-(RS)(0)  *)
(* （分部积分恒等式的纯多项式代数形）。证法分两段：先建加权基本定理族      *)
(* （单项式权 t^k 的逐点牛顿-莱布尼茨律，对被导表归纳），再对第一变元      *)
(* 归纳得主恒等式；cons 层的表头常数项贡献恰为加权族的实例，逐层卸载。     *)
(* ------------------------------------------------------------------ *)

(* 零的幂：0^(S n) = 0（Q 值乘法零吸收）。 *)
Lemma lw0_q_pow_zero_succ : forall n : nat, q_pow 0 (Datatypes.S n) == 0.
Proof.
  intros n.
  change (q_pow 0 (Datatypes.S n)) with (0 * q_pow 0 n)%Q.
  ring.
Qed.

(* 加权基本定理族：t^k 权下的逐点牛顿-莱布尼茨律（k=0 情形即既有引理      *)
(* lw0_qp_antideriv_deriv_at 的展开形）。沿系数表归纳；cons 层分 k=0 与    *)
(* k=S j 两支，k=S j 支的表头项经消因子引理归入归纳假设（指标 S(S j)）。   *)
Lemma lw0_qp_ai_deriv_ft_pow : forall p k x,
  q_pow x (Datatypes.S k) * qpoly_eval (lw0_qp_ai (qpoly_deriv p) k) x
  + (Z.of_nat k # 1) * q_pow x k * qpoly_eval (lw0_qp_ai p (Nat.sub k 1)) x
  == q_pow x k * qpoly_eval p x - q_pow 0 k * qpoly_eval p 0.
Proof.
  induction p as [|a p IH]; intros k x.
  - change (qpoly_deriv (@nil Q)) with (@nil Q).
    change (lw0_qp_ai (@nil Q) k) with (@nil Q).
    change (lw0_qp_ai (@nil Q) (Nat.sub k 1)) with (@nil Q).
    change (qpoly_eval (@nil Q) x) with 0%Q.
    change (qpoly_eval (@nil Q) 0%Q) with 0%Q.
    ring.
  - destruct k as [|j].
    + assert (Hf := lw0_qp_antideriv_deriv_at (cons a p) x).
      unfold lw0_qp_antideriv in Hf.
      change (qpoly_eval
                (cons 0 (lw0_qp_ai (qpoly_deriv (cons a p)) 0)) x)
        with (0 + x * qpoly_eval (lw0_qp_ai (qpoly_deriv (cons a p)) 0) x)
        in Hf.
      assert (H1 : (Z.of_nat 0 # 1)%Q == 0) by reflexivity.
      rewrite H1.
      assert (H2 : q_pow x (Datatypes.S 0) == x).
      { change (q_pow x (Datatypes.S 0)) with (x * q_pow x 0).
        change (q_pow x 0) with 1.
        ring. }
      rewrite H2.
      change (q_pow x 0) with 1.
      change (q_pow 0 0) with 1.
      rewrite (Qmult_1_l (qpoly_eval (cons a p) x)).
      rewrite (Qmult_1_l (qpoly_eval (cons a p) 0%Q)).
      transitivity (x * qpoly_eval (lw0_qp_ai (qpoly_deriv (cons a p)) 0) x
                    + 0 * qpoly_eval (lw0_qp_ai (cons a p) (Nat.sub 0 1)) x)%Q.
      { ring. }
      { rewrite <- Hf. ring. }
    + assert (Hpos : (0 < Z.of_nat (Datatypes.S j))%Z) by lia.
      assert (Hc : (Z.of_nat (Datatypes.S j) # 1)
                     * (a / (Z.of_nat (Datatypes.S j) # 1)) == a)
        by exact (lw0_q_div_int_mul (Z.of_nat (Datatypes.S j)) a Hpos).
      rewrite (q_pow_succ x (Datatypes.S j)).
      assert (Hsub : Nat.sub (Datatypes.S j) 1 = j) by lia.
      rewrite Hsub.
      change (qpoly_deriv (cons a p))
        with (qpoly_add p (cons 0 (qpoly_deriv p))).
      rewrite (lw0_qp_ai_add p (cons 0 (qpoly_deriv p)) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_deriv p) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_cons_eval a p j x).
      change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
      change (qpoly_eval (cons a p) 0%Q)
        with (a + 0 * qpoly_eval p 0%Q).
      rewrite (lw0_q_pow_zero_succ j).
      assert (Hih := IH (Datatypes.S (Datatypes.S j)) x).
      rewrite (q_pow_succ x (Datatypes.S (Datatypes.S j))) in Hih.
      rewrite (q_pow_succ x (Datatypes.S j)) in Hih.
      assert (Hn2 : Z.of_nat (Datatypes.S (Datatypes.S j))
                    = (Z.of_nat (Datatypes.S j) + 1)%Z) by lia.
      assert (Hz3 : (Z.of_nat (Datatypes.S (Datatypes.S j)) # 1)%Q
                    == ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)%Q)
        by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn2; lia).
      rewrite Hz3 in Hih.
      change (Nat.sub (Datatypes.S (Datatypes.S j)) 1)
        with (Datatypes.S j) in Hih.
      rewrite (lw0_q_pow_zero_succ (Datatypes.S j)) in Hih.
      assert (Hd : (Z.of_nat (Datatypes.S j) # 1) * q_pow x (Datatypes.S j)
                     * (a / (Z.of_nat (Datatypes.S j) # 1)
                        + x * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x)
                   == q_pow x (Datatypes.S j) * a
                      + (Z.of_nat (Datatypes.S j) # 1)
                          * q_pow x (Datatypes.S j) * x
                          * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x).
      { transitivity ((Z.of_nat (Datatypes.S j) # 1)
                        * q_pow x (Datatypes.S j)
                        * (a / (Z.of_nat (Datatypes.S j) # 1))
                      + (Z.of_nat (Datatypes.S j) # 1)
                          * q_pow x (Datatypes.S j) * x
                          * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x)%Q.
        - ring.
        - rewrite <- (Qmult_assoc (Z.of_nat (Datatypes.S j) # 1)
                        (q_pow x (Datatypes.S j))
                        (a / (Z.of_nat (Datatypes.S j) # 1))).
          rewrite (Qmult_comm (q_pow x (Datatypes.S j))
                     (a / (Z.of_nat (Datatypes.S j) # 1))).
          rewrite (Qmult_assoc (Z.of_nat (Datatypes.S j) # 1)
                     (a / (Z.of_nat (Datatypes.S j) # 1))
                     (q_pow x (Datatypes.S j))).
          rewrite Hc.
          ring. }
      rewrite Hd.
      assert (Hg : q_pow x (Datatypes.S j) * a
                   + (x * (x * q_pow x (Datatypes.S j))
                        * qpoly_eval (lw0_qp_ai (qpoly_deriv p)
                                             (Datatypes.S (Datatypes.S j))) x
                      + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                          * (x * q_pow x (Datatypes.S j))
                          * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x)
                   == q_pow x (Datatypes.S j) * a
                      + x * q_pow x (Datatypes.S j) * qpoly_eval p x
                      - 0 * qpoly_eval p 0%Q).
      { rewrite Hih. ring. }
      transitivity (q_pow x (Datatypes.S j) * a
                    + (x * (x * q_pow x (Datatypes.S j))
                         * qpoly_eval (lw0_qp_ai (qpoly_deriv p)
                                              (Datatypes.S (Datatypes.S j))) x
                       + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                           * (x * q_pow x (Datatypes.S j))
                           * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x))%Q.
      { ring. }
      { rewrite Hg. ring. }
Qed.

(* 分部积分主恒等式（加权族）：对第一变元归纳；cons 层的表头常数项贡献     *)
(* a·(t^k 权基本定理族的实例) 随归纳逐层卸载，表尾贡献恰为归纳假设在       *)
(* 指标 S(S j) 处的实例。                                                *)
Lemma lw0_qp_pair_ibp_family : forall R S k x,
  q_pow x (Datatypes.S k)
    * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) k) x
  + q_pow x (Datatypes.S k)
    * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) k) x
  + (Z.of_nat k # 1) * q_pow x k
    * qpoly_eval (lw0_qp_ai (qpoly_mul R S) (Nat.sub k 1)) x
  == q_pow x k * qpoly_eval (qpoly_mul R S) x
     - q_pow 0 k * qpoly_eval (qpoly_mul R S) 0.
Proof.
  induction R as [|a R IH]; intros S k x.
  - change (qpoly_deriv (@nil Q)) with (@nil Q).
    change (qpoly_mul (@nil Q) S) with (@nil Q).
    change (qpoly_mul (@nil Q) (qpoly_deriv S)) with (@nil Q).
    change (lw0_qp_ai (@nil Q) k) with (@nil Q).
    change (lw0_qp_ai (@nil Q) (Nat.sub k 1)) with (@nil Q).
    change (qpoly_eval (@nil Q) x) with 0%Q.
    change (qpoly_eval (@nil Q) 0%Q) with 0%Q.
    ring.
  - destruct k as [|j].
    + assert (H1 : (Z.of_nat 0 # 1)%Q == 0) by reflexivity.
      rewrite H1.
      assert (H2 : q_pow x (Datatypes.S 0) == x).
      { change (q_pow x (Datatypes.S 0)) with (x * q_pow x 0).
        change (q_pow x 0) with 1.
        ring. }
      rewrite H2.
      change (q_pow x 0) with 1.
      change (q_pow 0 0) with 1.
      change (qpoly_deriv (cons a R))
        with (qpoly_add R (cons 0 (qpoly_deriv R))).
      rewrite (lw0_qp_ai_mul_add_l R (cons 0 (qpoly_deriv R)) S 0 x).
      change (qpoly_mul (cons 0 (qpoly_deriv R)) S)
        with (qpoly_add (qpoly_scalar 0 S)
               (cons 0 (qpoly_mul (qpoly_deriv R) S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar 0 S)
                 (cons 0 (qpoly_mul (qpoly_deriv R) S)) 0 x).
      rewrite (lw0_qp_ai_scalar 0 S 0 x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_deriv R) S) 0 x).
      change (qpoly_mul (cons a R) (qpoly_deriv S))
        with (qpoly_add (qpoly_scalar a (qpoly_deriv S))
               (cons 0 (qpoly_mul R (qpoly_deriv S)))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_deriv S))
                 (cons 0 (qpoly_mul R (qpoly_deriv S))) 0 x).
      rewrite (lw0_qp_ai_scalar a (qpoly_deriv S) 0 x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R (qpoly_deriv S)) 0 x).
      change (qpoly_mul (cons a R) S)
        with (qpoly_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S))
                 (Nat.sub 0 1) x).
      rewrite (lw0_qp_ai_scalar a S (Nat.sub 0 1) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R S) (Nat.sub 0 1) x).
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) x).
      rewrite (qpoly_eval_scalar a S x).
      assert (Hc0 : qpoly_eval (cons 0 (qpoly_mul R S)) x
                    == 0 + x * qpoly_eval (qpoly_mul R S) x)
        by reflexivity.
      rewrite ?Hc0.
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) 0%Q).
      rewrite (qpoly_eval_scalar a S 0%Q).
      change (qpoly_eval (cons 0 (qpoly_mul R S)) 0%Q)
        with (0 + 0 * qpoly_eval (qpoly_mul R S) 0%Q).
      assert (Hih := IH S (Datatypes.S 0) x).
      rewrite (q_pow_succ x (Datatypes.S 0)) in Hih.
      rewrite H2 in Hih.
      assert (Hz1 : (Z.of_nat (Datatypes.S 0) # 1)%Q == 1) by reflexivity.
      rewrite Hz1 in Hih.
      assert (Hs01 : Nat.sub (Datatypes.S 0) 1 = 0%nat) by reflexivity.
      rewrite Hs01 in Hih.
      rewrite (lw0_q_pow_zero_succ 0) in Hih.
      assert (Hn0 := lw0_qp_ai_deriv_ft_pow S 0 x).
      rewrite H1 in Hn0.
      rewrite H2 in Hn0.
      change (q_pow x 0) with 1 in Hn0.
      change (q_pow 0 0) with 1 in Hn0.
      assert (Hg : x * x
                     * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                        (Datatypes.S 0)) x
                   + x * x
                     * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                        (Datatypes.S 0)) x
                   + 1 * x * qpoly_eval (lw0_qp_ai (qpoly_mul R S) 0) x
                   + a * (x * qpoly_eval (lw0_qp_ai (qpoly_deriv S) 0) x
                            + 0 * 1
                                * qpoly_eval (lw0_qp_ai S (Nat.sub 0 1)) x)
                   == a * qpoly_eval S x
                      + (x * qpoly_eval (qpoly_mul R S) x
                         - 0 * qpoly_eval (qpoly_mul R S) 0%Q)
                      - a * qpoly_eval S 0%Q).
      { rewrite Hih. rewrite Hn0. ring. }
      transitivity (x * x
                      * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                           (Datatypes.S 0)) x
                    + x * x
                      * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                           (Datatypes.S 0)) x
                    + 1 * x * qpoly_eval (lw0_qp_ai (qpoly_mul R S) 0) x
                    + a * (x * qpoly_eval (lw0_qp_ai (qpoly_deriv S) 0) x
                             + 0 * 1
                                 * qpoly_eval (lw0_qp_ai S (Nat.sub 0 1)) x))%Q.
      { ring. }
      { rewrite Hg. ring. }
    + rewrite (q_pow_succ x (Datatypes.S j)).
      assert (Hsub : Nat.sub (Datatypes.S j) 1 = j) by lia.
      rewrite Hsub.
      change (qpoly_deriv (cons a R))
        with (qpoly_add R (cons 0 (qpoly_deriv R))).
      rewrite (lw0_qp_ai_mul_add_l R (cons 0 (qpoly_deriv R)) S
                 (Datatypes.S j) x).
      change (qpoly_mul (cons 0 (qpoly_deriv R)) S)
        with (qpoly_add (qpoly_scalar 0 S)
               (cons 0 (qpoly_mul (qpoly_deriv R) S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar 0 S)
                 (cons 0 (qpoly_mul (qpoly_deriv R) S)) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_scalar 0 S (Datatypes.S j) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_deriv R) S)
                 (Datatypes.S j) x).
      change (qpoly_mul (cons a R) (qpoly_deriv S))
        with (qpoly_add (qpoly_scalar a (qpoly_deriv S))
               (cons 0 (qpoly_mul R (qpoly_deriv S)))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_deriv S))
                 (cons 0 (qpoly_mul R (qpoly_deriv S))) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_scalar a (qpoly_deriv S) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R (qpoly_deriv S))
                 (Datatypes.S j) x).
      change (qpoly_mul (cons a R) S)
        with (qpoly_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) j x).
      rewrite (lw0_qp_ai_scalar a S j x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R S) j x).
      rewrite (lw0_q_pow_zero_succ j).
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) x).
      rewrite (qpoly_eval_scalar a S x).
      assert (Hc0j : qpoly_eval (cons 0 (qpoly_mul R S)) x
                     == 0 + x * qpoly_eval (qpoly_mul R S) x)
        by reflexivity.
      rewrite ?Hc0j.
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) 0%Q).
      rewrite (qpoly_eval_scalar a S 0%Q).
      change (qpoly_eval (cons 0 (qpoly_mul R S)) 0%Q)
        with (0 + 0 * qpoly_eval (qpoly_mul R S) 0%Q).
      assert (Hih := IH S (Datatypes.S (Datatypes.S j)) x).
      rewrite (q_pow_succ x (Datatypes.S (Datatypes.S j))) in Hih.
      rewrite (q_pow_succ x (Datatypes.S j)) in Hih.
      assert (Hn2 : Z.of_nat (Datatypes.S (Datatypes.S j))
                    = (Z.of_nat (Datatypes.S j) + 1)%Z) by lia.
      assert (Hz3 : (Z.of_nat (Datatypes.S (Datatypes.S j)) # 1)%Q
                    == ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)%Q)
        by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn2; lia).
      rewrite Hz3 in Hih.
      change (Nat.sub (Datatypes.S (Datatypes.S j)) 1)
        with (Datatypes.S j) in Hih.
      rewrite (lw0_q_pow_zero_succ (Datatypes.S j)) in Hih.
      assert (Hn := lw0_qp_ai_deriv_ft_pow S (Datatypes.S j) x).
      rewrite (q_pow_succ x (Datatypes.S j)) in Hn.
      assert (Hsubn : Nat.sub (Datatypes.S j) 1 = j) by lia.
      rewrite Hsubn in Hn.
      rewrite (lw0_q_pow_zero_succ j) in Hn.
      assert (Hg : a * (x * q_pow x (Datatypes.S j)
                          * qpoly_eval (lw0_qp_ai (qpoly_deriv S)
                                             (Datatypes.S j)) x
                        + (Z.of_nat (Datatypes.S j) # 1)
                            * q_pow x (Datatypes.S j)
                            * qpoly_eval (lw0_qp_ai S j) x)
                   + (x * (x * q_pow x (Datatypes.S j))
                        * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                             (Datatypes.S (Datatypes.S j))) x
                      + x * (x * q_pow x (Datatypes.S j))
                          * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                                   (Datatypes.S (Datatypes.S j))) x
                      + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                          * (x * q_pow x (Datatypes.S j))
                          * qpoly_eval (lw0_qp_ai (qpoly_mul R S)
                                                   (Datatypes.S j)) x)
                   == q_pow x (Datatypes.S j) * a * qpoly_eval S x
                      + (x * q_pow x (Datatypes.S j)
                           * qpoly_eval (qpoly_mul R S) x
                         - 0 * qpoly_eval (qpoly_mul R S) 0%Q)).
      { rewrite Hn. rewrite <- Hih. ring. }
      transitivity (a * (x * q_pow x (Datatypes.S j)
                           * qpoly_eval (lw0_qp_ai (qpoly_deriv S)
                                                (Datatypes.S j)) x
                         + (Z.of_nat (Datatypes.S j) # 1)
                             * q_pow x (Datatypes.S j)
                             * qpoly_eval (lw0_qp_ai S j) x)
                    + (x * (x * q_pow x (Datatypes.S j))
                         * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                              (Datatypes.S (Datatypes.S j))) x
                       + x * (x * q_pow x (Datatypes.S j))
                           * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                                (Datatypes.S (Datatypes.S j))) x
                       + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                           * (x * q_pow x (Datatypes.S j))
                           * qpoly_eval (lw0_qp_ai (qpoly_mul R S)
                                                (Datatypes.S j)) x))%Q.
      { ring. }
      { rewrite Hg. ring. }
Qed.

(* 分部积分恒等式（配对积形式）：加权族在 k = 0 处的直读。 *)
Lemma lw0_qp_pair_ibp : forall R S q,
  lw0_qp_pair (qpoly_deriv R) S q + lw0_qp_pair R (qpoly_deriv S) q
  == qpoly_eval (qpoly_mul R S) q - qpoly_eval (qpoly_mul R S) 0.
Proof.
  intros R S q.
  unfold lw0_qp_pair.
  unfold lw0_qp_antideriv.
  change (qpoly_eval
            (cons 0 (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) 0) q).
  change (qpoly_eval
            (cons 0 (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) 0) q).
  assert (Hf := lw0_qp_pair_ibp_family R S 0 q).
  assert (H1 : (Z.of_nat 0 # 1)%Q == 0) by reflexivity.
  rewrite H1 in Hf.
  assert (H2 : q_pow q (Datatypes.S 0) == q).
  { change (q_pow q (Datatypes.S 0)) with (q * q_pow q 0).
    change (q_pow q 0) with 1.
    ring. }
  rewrite H2 in Hf.
  change (q_pow q 0) with 1 in Hf.
  change (q_pow 0 0) with 1 in Hf.
  transitivity (q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) 0) q
                + q * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) 0) q
                + 0 * 1
                    * qpoly_eval (lw0_qp_ai (qpoly_mul R S)
                                     (Nat.sub 0 1)) q)%Q.
  { ring. }
  { rewrite Hf. ring. }
Qed.


(* ------------------------------------------------------------------ *)
(* 部分和的多项式替身层（sigma / gamma）。数学内容：sin_partial N 与      *)
(* cos_partial N 是 t 的多项式（截断泰勒表）；其系数表（低次在首）按      *)
(* 「自高次段向低次段包入」的累积器递归给出。四条泛化引擎给出求值与      *)
(* 逐点导数的精确换形；交付面沿库约定取 eval 层逐点等式（_tlw06_ §3.3    *)
(* 原案的 list 层导数等式在「低次在首＋允许尾零」表示下非可靠不变量，    *)
(* 依删除件判例的正路改取 eval 层，响亮登记）。                          *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* 部分和的多项式替身层（sigma / gamma）。sin 侧五件验收绿交付；cos 侧    *)
(* 四件（引擎二、零点件与两交付面）已复绿去壳：前记三连拒经复核为施工    *)
(* 脚本内作用域与指标缺陷，非 tactic 墙；破译取样存 _t58_probe1.v。      *)
(* ------------------------------------------------------------------ *)

Fixpoint lw0_sin_aux (j : nat) (acc : qpoly) : qpoly :=
  match j with
  | Datatypes.O => cons 0 (cons (q_pow (-1) 0 / q_fact 1)%Q acc)
  | Datatypes.S M =>
      lw0_sin_aux M
        (cons 0
           (cons (q_pow (-1) (Datatypes.S M)
                   / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q
              acc))
  end.

Fixpoint lw0_cos_aux (j : nat) (acc : qpoly) : qpoly :=
  match j with
  | Datatypes.O => cons (q_pow (-1) 0 / q_fact 0)%Q acc
  | Datatypes.S M =>
      lw0_cos_aux M
        (cons 0
           (cons (q_pow (-1) (Datatypes.S M)
                   / q_fact (Datatypes.S (Datatypes.S (2 * M))))%Q
              acc))
  end.

Definition lw0_sin_qp (N : nat) : qpoly := lw0_sin_aux N nil.
Definition lw0_cos_qp (N : nat) : qpoly := lw0_cos_aux N nil.

(* 引擎一（sin 侧求值泛化）：表 = sigma_j 的表 ++ acc，Horner 展开后      *)
(* 尾段以 t^(2j+2) 幂乘入。归纳步的段贡献经幂次换形与除法环展开归位。    *)
Lemma lw0_sin_aux_eval : forall j acc x,
  qpoly_eval (lw0_sin_aux j acc) x
  == sin_partial j x
     + q_pow x (Datatypes.S (Datatypes.S (2 * j))) * qpoly_eval acc x.
Proof.
  induction j as [|M IH]; intros acc x.
  - unfold sin_partial.
    change (lw0_sin_aux 0 acc)
      with (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)).
    change (qpoly_eval (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)) x)
      with (0 + x * (q_pow (-1) 0 / q_fact 1 + x * qpoly_eval acc x)).
    change (sin_term 0 x)
      with (q_pow (-1) 0
              * (q_pow x (Datatypes.S (2 * 0))
                 / q_fact (Datatypes.S (2 * 0)))).
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    change (q_fact (Datatypes.S (2 * 0)))
      with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    change (q_fact 0) with 1%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * 0))))
      with (x * (x * q_pow x 0))%Q.
    change (q_pow x 0) with 1%Q.
    unfold Qdiv. ring.
  - change (sin_partial (Datatypes.S M) x)
      with (sin_partial M x + sin_term (Datatypes.S M) x).
    set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q).
    change (lw0_sin_aux (Datatypes.S M) acc)
      with (lw0_sin_aux M (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (sin_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (Datatypes.S (2 * Datatypes.S M))
                 / q_fact (Datatypes.S (2 * Datatypes.S M)))).
    assert (H2 : Datatypes.S (2 * Datatypes.S M)
                 = Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) by lia.
    rewrite H2.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))).
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M)))).
    unfold c. unfold Qdiv. ring.
Qed.

Lemma lw0_sin_partial_zero : forall N, sin_partial N 0 == 0.
Proof.
  induction N as [|M IH].
  - unfold sin_partial. unfold sin_term.
    change (q_pow (-1) 0) with 1%Q.
    rewrite (lw0_q_pow_zero_succ (2 * 0)).
    unfold Qdiv. ring.
  - unfold sin_partial. rewrite IH. unfold sin_term.
    rewrite (lw0_q_pow_zero_succ (Datatypes.S (2 * Datatypes.S M))).
    unfold Qdiv. ring.
Qed.

Lemma lw0_sin_qp_eval : forall N x,
  qpoly_eval (lw0_sin_qp N) x == sin_partial N x.
Proof.
  intros N x. unfold lw0_sin_qp.
  rewrite (lw0_sin_aux_eval N nil x).
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (Datatypes.S (Datatypes.S (2 * N))) * 0 == 0) by ring.
  rewrite H0. ring.
Qed.

Lemma lw0_sin_qp_zero_eval : forall N, qpoly_eval (lw0_sin_qp N) 0 == 0.
Proof. intros N. rewrite (lw0_sin_qp_eval N 0). exact (lw0_sin_partial_zero N). Qed.

(* 引擎二（cos 侧求值泛化）：表 = gamma_j 的表 ++ acc，Horner 展开后      *)
(* 尾段以 t^(2j+1) 幂乘入。证法为 sin 侧绿形逐字模板加指标映射：          *)
(* cos_term 用自身 2j 指标（区别于 sin 的 2j+1），指标换算式带 %nat       *)
(* 作用域标注（Q_scope 劫持防御），全局改写后两级幂降归位。              *)
Lemma lw0_cos_aux_eval : forall j acc x,
  qpoly_eval (lw0_cos_aux j acc) x
  == cos_partial j x
     + q_pow x (Datatypes.S (2 * j)) * qpoly_eval acc x.
Proof.
  induction j as [|M IH]; intros acc x.
  - unfold cos_partial.
    change (lw0_cos_aux 0 acc) with (cons (q_pow (-1) 0 / q_fact 0) acc).
    change (qpoly_eval (cons (q_pow (-1) 0 / q_fact 0) acc) x)
      with (q_pow (-1) 0 / q_fact 0 + x * qpoly_eval acc x).
    change (cos_term 0 x)
      with (q_pow (-1) 0 * (q_pow x (2 * 0) / q_fact (2 * 0))).
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow x (2 * 0)) with 1%Q.
    change (q_fact (2 * 0)) with 1%Q.
    change (q_fact 0) with 1%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    unfold Qdiv. ring.
  - change (cos_partial (Datatypes.S M) x)
      with (cos_partial M x + cos_term (Datatypes.S M) x).
    set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (2 * M))))%Q).
    change (lw0_cos_aux (Datatypes.S M) acc)
      with (lw0_cos_aux M (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (cos_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (2 * Datatypes.S M)
                 / q_fact (2 * Datatypes.S M))).
    assert (H2 : (2 * Datatypes.S M)%nat
                 = Datatypes.S (Datatypes.S (2 * M))) by lia.
    rewrite H2.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M)))).
    change (q_pow x (Datatypes.S (Datatypes.S (2 * M))))
      with (x * q_pow x (Datatypes.S (2 * M))).
    unfold c. unfold Qdiv. ring.
Qed.

(* gamma 部分和在零点的取值：cos(0)=1（j=0 项 0^0/0!=1，j≥1 项零吸收）。 *)
Lemma lw0_cos_partial_zero : forall N, cos_partial N 0 == 1.
Proof.
  induction N as [|M IH].
  - unfold cos_partial. unfold cos_term.
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow 0 (2 * 0) / q_fact (2 * 0)) with 1%Q.
    unfold Qdiv. ring.
  - unfold cos_partial. rewrite IH. unfold cos_term.
    assert (H2 : (2 * Datatypes.S M)%nat
                 = Datatypes.S (Datatypes.S (2 * M))) by lia.
    rewrite H2.
    rewrite (lw0_q_pow_zero_succ (Datatypes.S (2 * M))).
    unfold Qdiv. ring.
Qed.

(* 交付面一（eval 层）：gamma 表求值 == cos 部分和。 *)
Lemma lw0_cos_qp_eval : forall N x,
  qpoly_eval (lw0_cos_qp N) x == cos_partial N x.
Proof.
  intros N x. unfold lw0_cos_qp.
  rewrite (lw0_cos_aux_eval N nil x).
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (Datatypes.S (2 * N)) * 0 == 0) by ring.
  rewrite H0. ring.
Qed.

(* 交付面二（eval 层）：gamma 表在零点取值为 1（cos(0)=1）。 *)
Lemma lw0_cos_qp_zero_eval : forall N, qpoly_eval (lw0_cos_qp N) 0 == 1.
Proof. intros N. rewrite (lw0_cos_qp_eval N 0). exact (lw0_cos_partial_zero N). Qed.

(* ------------------------------------------------------------------ *)
(* deriv 两件：eval 层三-term 泛化引擎（配方直读自 _tlw58_ 施工记录      *)
(* §六.1）。数学内容：sin_aux j acc 的表 deriv 求值 = γ_j +              *)
(* (2j+2)·t^{2j+1}·acc + t^{2j+2}·acc'；cos_aux (S i) acc 的表 deriv     *)
(* 求值 = −σ_i + (2i+3)·t^{2i+2}·acc + t^{2i+3}·acc'（γ_{S i}′ = −σ_i   *)
(* 移一位）。归纳步的段头系数消因子走 q_fact_succ＋Qinv_mult_distr＋     *)
(* lw0_q_int_inv 手工链（lw0_q_div_int_mul 同款）；段头商在基例处整体    *)
(* change 归一（禁拆散单侧 Qinv 原子）；nat 指标等式一律 %nat 标注。     *)
(* ------------------------------------------------------------------ *)

(* 消因子泛化助手：z 正时 (z#1)·(a/((z#1)·b)) = a/b。证法为                 *)
(* lw0_q_div_int_mul 同款 Qmult_assoc/Qmult_comm 纯语法重连锁（ring 无法  *)
(* 凭空造出 z·/z 相消形，原子净幂次不变）。                                *)
Lemma lw0_q_div_int_mul_gen : forall (z : Z) (a b : Q),
  (0 < z)%Z -> (z # 1) * (a / ((z # 1) * b)) == a / b.
Proof.
  intros z a b Hz.
  change (a / ((z # 1) * b)) with (a * / ((z # 1) * b)).
  change (a / b) with (a * / b).
  rewrite Qinv_mult_distr.
  rewrite (Qmult_assoc (z # 1) a (/ (z # 1) * / b)).
  rewrite (Qmult_comm (z # 1) a).
  rewrite <- (Qmult_assoc a (z # 1) (/ (z # 1) * / b)).
  rewrite (Qmult_assoc (z # 1) (/ (z # 1)) (/ b)).
  rewrite (lw0_q_int_inv z Hz).
  ring.
Qed.

Lemma lw0_sin_aux_deriv_eval : forall j acc x,
  qpoly_eval (qpoly_deriv (lw0_sin_aux j acc)) x
  == cos_partial j x
     + q_pow x (Datatypes.S (2 * j))
         * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
              * qpoly_eval acc x)
     + q_pow x (Datatypes.S (Datatypes.S (2 * j)))
         * qpoly_eval (qpoly_deriv acc) x.
Proof.
  induction j as [|M IH]; intros acc x.
  - unfold cos_partial.
    change (lw0_sin_aux 0 acc)
      with (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)).
    change (qpoly_deriv (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)))
      with (qpoly_add (cons (q_pow (-1) 0 / q_fact 1) acc)
              (cons 0 (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc)))).
    rewrite (qpoly_eval_add (cons (q_pow (-1) 0 / q_fact 1) acc)
               (cons 0 (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc))) x).
    change (qpoly_eval
              (cons 0 (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc))) x)
      with (0 + x * qpoly_eval
              (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc)) x).
    rewrite (qpoly_eval_deriv_cons (q_pow (-1) 0 / q_fact 1) acc x).
    change (qpoly_eval (cons (q_pow (-1) 0 / q_fact 1) acc) x)
      with (q_pow (-1) 0 / q_fact 1 + x * qpoly_eval acc x).
    change (cos_term 0 x) with 1%Q.
    change (q_pow (-1) 0 / q_fact 1) with 1%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * 0))))
      with (x * (x * q_pow x 0))%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    change (Z.of_nat (Datatypes.S (Datatypes.S (2 * 0))) # 1)
      with (1 + 1)%Q.
    unfold Qdiv. ring.
  - change (cos_partial (Datatypes.S M) x)
      with (cos_partial M x + cos_term (Datatypes.S M) x).
    set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q).
    change (lw0_sin_aux (Datatypes.S M) acc)
      with (lw0_sin_aux M (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (qpoly_deriv (cons 0 (cons c acc)))
      with (qpoly_add (cons c acc) (cons 0 (qpoly_deriv (cons c acc)))).
    rewrite (qpoly_eval_add (cons c acc)
               (cons 0 (qpoly_deriv (cons c acc))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (cons c acc))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (cons c acc)) x).
    rewrite (qpoly_eval_deriv_cons c acc x).
    change (qpoly_eval (cons c acc) x)
      with (c + x * qpoly_eval acc x).
    change (cos_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (2 * Datatypes.S M)
                 / q_fact (2 * Datatypes.S M))).
    assert (H2 : Datatypes.S (2 * Datatypes.S M)
                 = Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) by lia.
    rewrite H2.
    assert (H2b : (2 * Datatypes.S M)%nat
                  = Datatypes.S (Datatypes.S (2 * M))) by lia.
    rewrite H2b.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * M))))
      with (x * q_pow x (Datatypes.S (2 * M)))%Q.
    change (q_pow x (Datatypes.S (2 * M)))
      with (x * q_pow x (2 * M))%Q.
    assert (Hpos : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Z) by lia.
    assert (Hn3 : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))
                  = (Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) + 1)%Z) by lia.
    assert (Hz3 : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1)%Q
                  == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn3; lia).
    assert (Hn4 : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                  = (Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) + 2)%Z) by lia.
    assert (Hz4 : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1 + 1)%Q
                  == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn4; lia).
    assert (Hkey : (Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)
                     * (q_pow (-1) (Datatypes.S M)
                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                     + (q_pow (-1) (Datatypes.S M)
                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                   == q_pow (-1) (Datatypes.S M)
                      / q_fact (Datatypes.S (Datatypes.S (2 * M)))).
    { unfold c.
      transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1)
                      * (q_pow (-1) (Datatypes.S M)
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
      { ring. }
      rewrite Hz3.
      rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * M)))).
      rewrite (lw0_q_div_int_mul_gen
                 (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                 (q_pow (-1) (Datatypes.S M))
                 (q_fact (Datatypes.S (Datatypes.S (2 * M)))) Hpos).
      reflexivity. }
    assert (Hza : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)
                     * qpoly_eval acc x
                     + qpoly_eval acc x + qpoly_eval acc x)%Q
                  == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) # 1)
                       * qpoly_eval acc x).
    { transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1 + 1)
                      * qpoly_eval acc x).
      { ring. }
      rewrite Hz4. ring. }
    transitivity (cos_partial M x
                  + (x * (x * q_pow x (2 * M)))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1) * c + c)
                  + (x * (x * (x * q_pow x (2 * M))))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)
                           * qpoly_eval acc x
                         + qpoly_eval acc x + qpoly_eval acc x)
                  + (x * (x * (x * (x * q_pow x (2 * M)))))
                      * qpoly_eval (qpoly_deriv acc) x)%Q.
    { ring. }
    unfold c.
    rewrite Hkey. rewrite Hza.
    unfold Qdiv. ring.
Qed.

Lemma lw0_cos_aux_deriv_eval_S : forall i acc x,
  qpoly_eval (qpoly_deriv (lw0_cos_aux (Datatypes.S i) acc)) x
  == - sin_partial i x
     + q_pow x (2 * Datatypes.S i)
         * ((Z.of_nat (Datatypes.S (2 * Datatypes.S i)) # 1)
              * qpoly_eval acc x)
     + q_pow x (Datatypes.S (2 * Datatypes.S i))
         * qpoly_eval (qpoly_deriv acc) x.
Proof.
  induction i as [|M IH]; intros acc x.
  - unfold sin_partial.
    set (c0 := (q_pow (-1) (Datatypes.S 0)
                / q_fact (Datatypes.S (Datatypes.S (2 * 0))))%Q).
    change (lw0_cos_aux (Datatypes.S 0) acc)
      with (lw0_cos_aux 0 (cons 0 (cons c0 acc))).
    change (lw0_cos_aux 0 (cons 0 (cons c0 acc)))
      with (cons (q_pow (-1) 0 / q_fact 0) (cons 0 (cons c0 acc))).
    change (qpoly_deriv
              (cons (q_pow (-1) 0 / q_fact 0) (cons 0 (cons c0 acc))))
      with (qpoly_add (cons 0 (cons c0 acc))
              (cons 0 (qpoly_deriv (cons 0 (cons c0 acc))))).
    rewrite (qpoly_eval_add (cons 0 (cons c0 acc))
               (cons 0 (qpoly_deriv (cons 0 (cons c0 acc)))) x).
    change (qpoly_eval
              (cons 0 (qpoly_deriv (cons 0 (cons c0 acc)))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (cons 0 (cons c0 acc))) x).
    rewrite (qpoly_eval_deriv_cons 0 (cons c0 acc) x).
    change (qpoly_eval (cons 0 (cons c0 acc)) x)
      with (0 + x * (c0 + x * qpoly_eval acc x)).
    rewrite (qpoly_eval_deriv_cons c0 acc x).
    change (qpoly_eval (cons c0 acc) x)
      with (c0 + x * qpoly_eval acc x).
    change (sin_term 0 x)
      with (q_pow (-1) 0
              * (q_pow x (Datatypes.S (2 * 0))
                 / q_fact (Datatypes.S (2 * 0)))).
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow x (Datatypes.S (2 * Datatypes.S 0)))
      with (x * q_pow x (2 * Datatypes.S 0))%Q.
    change (q_pow x (2 * Datatypes.S 0)) with (x * (x * q_pow x 0))%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    change (Z.of_nat (Datatypes.S (2 * Datatypes.S 0)) # 1)
      with (1 + 1 + 1)%Q.
    assert (Hkey0 : (2 * x) * (q_pow (-1) (Datatypes.S 0)
                               / q_fact (Datatypes.S (Datatypes.S (2 * 0))))
                    == - (1 * ((x * 1)
                               / q_fact (Datatypes.S (2 * 0))))).
    { change (q_fact (Datatypes.S (Datatypes.S (2 * 0))))
        with (((2 # 1) * q_fact (Datatypes.S (2 * 0)))%Q).
      change (q_pow (-1) (Datatypes.S 0)) with (-1)%Q.
      assert (Hpos2 : (0 < 2)%Z) by lia.
      rewrite <- (Qmult_assoc (2 # 1) x
                    ((-1) / ((2 # 1) * q_fact (Datatypes.S (2 * 0))))).
      rewrite (Qmult_comm x
                 ((-1) / ((2 # 1) * q_fact (Datatypes.S (2 * 0))))).
      rewrite (Qmult_assoc (2 # 1)
                 ((-1) / ((2 # 1) * q_fact (Datatypes.S (2 * 0)))) x).
      rewrite (lw0_q_div_int_mul_gen 2 (-1)
                 (q_fact (Datatypes.S (2 * 0))) Hpos2).
      unfold Qdiv. ring. }
    transitivity ((2 * x) * c0
                  + (x * (x * 1)) * ((1 + 1 + 1) * qpoly_eval acc x)
                  + (x * (x * (x * 1)))
                      * qpoly_eval (qpoly_deriv acc) x)%Q.
    { ring. }
    unfold c0.
    rewrite Hkey0.
    unfold Qdiv. ring.
  - change (- sin_partial (Datatypes.S M) x)
      with (- (sin_partial M x + sin_term (Datatypes.S M) x))%Q.
    set (c := (q_pow (-1) (Datatypes.S (Datatypes.S M))
               / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S M))))%Q).
    change (lw0_cos_aux (Datatypes.S (Datatypes.S M)) acc)
      with (lw0_cos_aux (Datatypes.S M) (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (qpoly_deriv (cons 0 (cons c acc)))
      with (qpoly_add (cons c acc) (cons 0 (qpoly_deriv (cons c acc)))).
    rewrite (qpoly_eval_add (cons c acc)
               (cons 0 (qpoly_deriv (cons c acc))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (cons c acc))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (cons c acc)) x).
    rewrite (qpoly_eval_deriv_cons c acc x).
    change (qpoly_eval (cons c acc) x)
      with (c + x * qpoly_eval acc x).
    change (sin_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (Datatypes.S (2 * Datatypes.S M))
                 / q_fact (Datatypes.S (2 * Datatypes.S M)))).
    assert (H2 : Datatypes.S (2 * Datatypes.S M)
                 = Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) by lia.
    rewrite H2.
    assert (H2b : (2 * Datatypes.S M)%nat
                  = Datatypes.S (Datatypes.S (2 * M))) by lia.
    rewrite H2b.
    assert (H4 : Datatypes.S (2 * Datatypes.S (Datatypes.S M))
                 = Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))) by lia.
    rewrite H4.
    assert (H3 : (2 * Datatypes.S (Datatypes.S M))%nat
                 = Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) by lia.
    rewrite H3.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * M))))
      with (x * q_pow x (Datatypes.S (2 * M)))%Q.
    change (q_pow x (Datatypes.S (2 * M)))
      with (x * q_pow x (2 * M))%Q.
    assert (Hpos4 : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))%Z) by lia.
    assert (Hn4c : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                   = (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) + 1)%Z) by lia.
    assert (Hz3c : ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1)%Q
                   == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn4c; lia).
    assert (Hn5c : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                   = (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) + 2)%Z) by lia.
    assert (Hz5c : ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1 + 1)%Q
                   == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn5c; lia).
    assert (HkeyM : (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)
                      * (q_pow (-1) (Datatypes.S (Datatypes.S M))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                      + (q_pow (-1) (Datatypes.S (Datatypes.S M))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                    == - (q_pow (-1) (Datatypes.S M)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
    { unfold c.
      transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1)
                      * (q_pow (-1) (Datatypes.S (Datatypes.S M))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))).
      { ring. }
      rewrite Hz3c.
      rewrite (q_fact_succ (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))).
      rewrite (lw0_q_div_int_mul_gen
                 (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                 (q_pow (-1) (Datatypes.S (Datatypes.S M)))
                 (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) Hpos4).
      change (q_pow (-1) (Datatypes.S (Datatypes.S M)))
        with ((-1) * q_pow (-1) (Datatypes.S M))%Q.
      unfold Qdiv. ring. }
    assert (HzaC : ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)
                      * qpoly_eval acc x
                      + qpoly_eval acc x + qpoly_eval acc x)%Q
                   == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))) # 1)
                        * qpoly_eval acc x).
    { transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1 + 1)
                      * qpoly_eval acc x).
      { ring. }
      rewrite Hz5c. ring. }
    transitivity (- sin_partial M x
                  + (x * (x * (x * q_pow x (2 * M))))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1) * c + c)
                  + (x * (x * (x * (x * q_pow x (2 * M)))))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)
                           * qpoly_eval acc x
                         + qpoly_eval acc x + qpoly_eval acc x)
                  + (x * (x * (x * (x * (x * q_pow x (2 * M))))))
                      * qpoly_eval (qpoly_deriv acc) x)%Q.
    { ring. }
    unfold c.
    rewrite H2.
    rewrite HkeyM. rewrite HzaC.
    unfold Qdiv. ring.
Qed.

(* 交付面一：σ_N′ = γ_N（不移位）。 *)
Lemma lw0_sin_qp_deriv_eval : forall N x,
  qpoly_eval (qpoly_deriv (lw0_sin_qp N)) x == cos_partial N x.
Proof.
  intros N x. unfold lw0_sin_qp.
  rewrite (lw0_sin_aux_deriv_eval N nil x).
  change (qpoly_eval (qpoly_deriv nil) x) with 0%Q.
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (Datatypes.S (2 * N))
                 * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * N))) # 1) * 0) == 0) by ring.
  assert (H1 : q_pow x (Datatypes.S (Datatypes.S (2 * N))) * 0 == 0) by ring.
  rewrite H0. rewrite H1. ring.
Qed.

(* 交付面二：γ_{S N}′ = −σ_N（移一位）。 *)
Lemma lw0_cos_qp_deriv_eval : forall N x,
  qpoly_eval (qpoly_deriv (lw0_cos_qp (Datatypes.S N))) x == - sin_partial N x.
Proof.
  intros N x. unfold lw0_cos_qp.
  rewrite (lw0_cos_aux_deriv_eval_S N nil x).
  change (qpoly_eval (qpoly_deriv nil) x) with 0%Q.
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (2 * Datatypes.S N)
                 * ((Z.of_nat (Datatypes.S (2 * Datatypes.S N)) # 1) * 0) == 0) by ring.
  assert (H1 : q_pow x (Datatypes.S (2 * Datatypes.S N)) * 0 == 0) by ring.
  rewrite H0. rewrite H1. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 配对积绝对值包络（S05 波施工；证面＝逐项 Qabs_triangle 压制）。        *)
(* 数学内容：|<f,g>_q| = |q·Σ_j c_j q^j/(j+1)| ≤ |q|·Σ_j |c_j|·|q|^j/(j+1) *)
(* （c_j 为 mul f g 系数；右端即积分片(abs 映射 mul f g)在 |q| 的取值）。 *)
(* 引擎语句两侧取同一 ai 形：|A_k(p)(x)| ≤ A_k(map Qabs p)(|x|)——归纳步  *)
(* 段头 |a/(z#1)| 走 Qabs_Qmult＋Qabs_Qinv＋Qabs_pos 纯 == 压制（z 正时   *)
(* |z#1|==z#1），全件无除法-序拉伸（Qmult_le_compat_r 仅右乘形，左拉伸   *)
(* 无库件，遂以此形规避；升级建议形（mul(map abs f)(map abs g)）尚差系   *)
(* 数优势压制＋1/(j+1) 因子卸除两段，登记未竟（升级段不硬拼）。          *)
(* ------------------------------------------------------------------ *)

(* 表映射：逐系数作用 h。abs 映射即 qpoly_map Qabs。 *)
Fixpoint qpoly_map (h : Q -> Q) (p : qpoly) : qpoly :=
  match p with
  | nil => nil
  | cons a p' => cons (h a) (qpoly_map h p')
  end.

(* 正分母的绝对值==：|a/(z#1)| == |a|/(z#1)。 *)
Lemma lw0_q_abs_div : forall (z : Z) (a : Q),
  (0 < z)%Z -> Qabs (a / (z # 1)) == Qabs a / (z # 1).
Proof.
  intros z a Hz.
  assert (H0 : (0 <= (z # 1))%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  change (a / (z # 1)) with (a * / (z # 1)).
  change (Qabs a / (z # 1)) with (Qabs a * / (z # 1)).
  rewrite Qabs_Qmult.
  rewrite Qabs_Qinv.
  rewrite (Qabs_pos (z # 1) H0).
  reflexivity.
Qed.

(* == 到 ≤ 的桥（Z 层直读）。 *)
Lemma lw0_q_eq_le : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y Hxy.
  unfold Qeq in Hxy. unfold Qle.
  rewrite Hxy. apply Z.le_refl.
Qed.

(* 左乘单调（stdlib 仅 Qmult_le_compat_r 右乘形，左形自建）。 *)
Lemma lw0_q_mult_le_l : forall c x y : Q, (0 <= c)%Q -> x <= y -> c * x <= c * y.
Proof.
  intros c x y Hc Hxy.
  apply (Qle_trans (c * x) (x * c)).
  - apply lw0_q_eq_le. apply Qmult_comm.
  - apply (Qle_trans (x * c) (y * c)).
    + apply Qmult_le_compat_r; [exact Hxy | exact Hc].
    + apply (Qle_trans (y * c) (c * y)).
      * apply lw0_q_eq_le. apply Qmult_comm.
      * apply Qle_refl.
Qed.

(* 积分片三角引擎：|A_k(p)(x)| ≤ A_k(map Qabs p)(|x|)。 *)
Lemma lw0_qp_ai_abs_bound : forall p k x,
  Qabs (qpoly_eval (lw0_qp_ai p k) x)
  <= qpoly_eval (lw0_qp_ai (qpoly_map Qabs p) k) (Qabs x).
Proof.
  induction p as [|a p IH]; intros k x.
  - change (qpoly_eval (lw0_qp_ai nil k) x) with 0%Q.
    change (lw0_qp_ai (qpoly_map Qabs nil) k) with (@nil Q).
    change (qpoly_eval (@nil Q) (Qabs x)) with 0%Q.
    change (Qabs 0) with 0%Q.
    apply Qle_refl.
  - assert (Hpos : (0 < Z.of_nat (S k))%Z) by lia.
    change (qpoly_map Qabs (cons a p)) with (cons (Qabs a) (qpoly_map Qabs p)).
    change (lw0_qp_ai (cons (Qabs a) (qpoly_map Qabs p)) k)
      with (cons (Qabs a / (Z.of_nat (S k) # 1))
                    (lw0_qp_ai (qpoly_map Qabs p) (S k))).
    change (qpoly_eval
              (cons (Qabs a / (Z.of_nat (S k) # 1))
                    (lw0_qp_ai (qpoly_map Qabs p) (S k))) (Qabs x))
      with (Qabs a / (Z.of_nat (S k) # 1)
              + Qabs x * qpoly_eval (lw0_qp_ai (qpoly_map Qabs p) (S k)) (Qabs x)).
    rewrite (lw0_qp_ai_cons_eval a p k x).
    apply (Qle_trans
            (Qabs (a / (Z.of_nat (S k) # 1)
                    + x * qpoly_eval (lw0_qp_ai p (S k)) x))
            (Qabs (a / (Z.of_nat (S k) # 1))
              + Qabs (x * qpoly_eval (lw0_qp_ai p (S k)) x))).
    + apply Qabs_triangle.
    + rewrite (lw0_q_abs_div (Z.of_nat (S k)) a Hpos).
      rewrite (Qabs_Qmult x (qpoly_eval (lw0_qp_ai p (S k)) x)).
      apply Qplus_le_compat.
      * apply Qle_refl.
      * apply (lw0_q_mult_le_l (Qabs x)).
        -- apply Qabs_nonneg.
        -- apply IH.
Qed.

(* 交付面：配对积绝对值包络（积分片形；建议形的系数优势升级段未竟）。     *)
Lemma lw0_pair_abs_bound : forall f g q,
  Qabs (lw0_qp_pair f g q)
  <= Qabs q * qpoly_eval (lw0_qp_ai (qpoly_map Qabs (qpoly_mul f g)) 0) (Qabs q).
Proof.
  intros f g q.
  unfold lw0_qp_pair. unfold lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q).
  rewrite Qplus_0_l.
  rewrite (Qabs_Qmult q (qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q)).
  apply (lw0_q_mult_le_l (Qabs q)).
  - apply Qabs_nonneg.
  - apply (lw0_qp_ai_abs_bound (qpoly_mul f g) 0 q).
Qed.




(* ------------------------------------------------------------------ *)
(* lw0_F 系基础设施第一刀（ENDPOINT6 §D 正解路线，尾段施工）。            *)
(* deriv 穿 add 的「eval 层」可加性（m=1 层）：deriv(add p q) 与        *)
(* add(deriv p)(deriv q) 仅 eval 相等、list 不等（406-409 行诊断注记    *)
(* 在案），故只在 eval 层立。证路＝对 p 结构归纳（cons-0 核），v、x 全   *)
(* 程泛化，cons-cons 步二次取用 qpoly_eval_add＋IH＋ring。零 length 归   *)
(* 纳、零复活删件（lw0_qp_eval_deriv_iter_add/lw0_qp_deriv_iter_zero    *)
(* 均未触碰；迭代层 m 归纳版需 I∧CD 同级互归纳＋nat 次数因子，登记未竟）。*)
(* ------------------------------------------------------------------ *)

(* nil 的迭代求导恒 nil（内部桥接）。 *)
Lemma lw0_deriv_iter_nil : forall n : nat, qpoly_deriv_iter n nil = nil.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change (qpoly_deriv_iter (Datatypes.S n) nil)
      with (qpoly_deriv (qpoly_deriv_iter n nil)).
    rewrite IH.
    reflexivity.
Qed.

(* deriv 穿 add 的 eval 层可加性（m=1 层）。 *)
Lemma lw0_deriv_add_eval : forall p v x,
  qpoly_eval (qpoly_deriv (qpoly_add p v)) x ==
  qpoly_eval (qpoly_deriv p) x + qpoly_eval (qpoly_deriv v) x.
Proof.
  induction p as [|a p IH]; intros v x.
  - change (qpoly_add nil v) with v.
    change (qpoly_deriv (@nil Q)) with (@nil Q).
    change (qpoly_eval (@nil Q) x) with 0%Q.
    symmetry.
    apply Qplus_0_l.
  - destruct v as [|b v'].
    + change (qpoly_add (cons a p) nil) with (cons a p).
      change (qpoly_deriv (@nil Q)) with (@nil Q).
      change (qpoly_eval (@nil Q) x) with 0%Q.
      symmetry.
      apply Qplus_0_r.
    + change (qpoly_add (cons a p) (cons b v'))
        with (cons (a + b) (qpoly_add p v')).
      change (qpoly_deriv (cons (a + b) (qpoly_add p v')))
        with (qpoly_add (qpoly_add p v')
              (cons 0 (qpoly_deriv (qpoly_add p v')))).
      rewrite (qpoly_eval_add (qpoly_add p v')
                (cons 0 (qpoly_deriv (qpoly_add p v'))) x).
      rewrite (qpoly_eval_add p v' x).
      change (qpoly_eval (cons 0 (qpoly_deriv (qpoly_add p v'))) x)
        with (0 + x * qpoly_eval (qpoly_deriv (qpoly_add p v')) x).
      rewrite (IH v' x).
      change (qpoly_deriv (cons a p))
        with (qpoly_add p (cons 0 (qpoly_deriv p))).
      rewrite (qpoly_eval_add p (cons 0 (qpoly_deriv p)) x).
      change (qpoly_eval (cons 0 (qpoly_deriv p)) x)
        with (0 + x * qpoly_eval (qpoly_deriv p) x).
      change (qpoly_deriv (cons b v'))
        with (qpoly_add v' (cons 0 (qpoly_deriv v'))).
      rewrite (qpoly_eval_add v' (cons 0 (qpoly_deriv v')) x).
      change (qpoly_eval (cons 0 (qpoly_deriv v')) x)
        with (0 + x * qpoly_eval (qpoly_deriv v') x).
      ring.
Qed.

(* ------------------------------------------------------------------ *)
(* lw0_F 系本体（S05 终段施工；ENDPOINT6 §D 正解路线第二刀）。            *)
(* 支柱 I：deriv 穿 add 的 eval 层可加性（m 级）；支柱 CD：cons 移位     *)
(* Leibniz 式 (t·W)^{(S m)} == t·W^{(S m)} + (S m)·W^{(m)}（次数因子     *)
(* Z.of_nat (S m) # 1 不可省）。两支柱以同级合取作 m 归纳：I(S m) 的      *)
(* cons-cons 步取 CD(m)＋表内 p 归纳自举；CD(S m) 取 I(S m)＋CD(m)＋     *)
(* deriv_iter 换序。零 length 归纳、零复活删除件（两条删除件语句均未     *)
(* 重现；此处为 fresh 语句面）。                                          *)
(* ------------------------------------------------------------------ *)

Lemma lw0_deriv_iter_cons_add_joint :
  forall m : nat,
    (forall p v x,
      qpoly_eval (qpoly_deriv_iter m (qpoly_add p v)) x ==
      qpoly_eval (qpoly_deriv_iter m p) x + qpoly_eval (qpoly_deriv_iter m v) x)
    /\ (forall c w x,
      qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (cons c w)) x ==
      x * qpoly_eval (qpoly_deriv_iter (Datatypes.S m) w) x
      + (Z.of_nat (Datatypes.S m) # 1) * qpoly_eval (qpoly_deriv_iter m w) x).
Proof.
  induction m as [|m [IHadd IHcons]].
  - split.
    + intros p v x.
      change (qpoly_deriv_iter 0 (qpoly_add p v)) with (qpoly_add p v).
      change (qpoly_deriv_iter 0 p) with p.
      change (qpoly_deriv_iter 0 v) with v.
      apply qpoly_eval_add.
    + intros c w x.
      change (qpoly_deriv_iter 1 (cons c w)) with (qpoly_deriv (cons c w)).
      rewrite (qpoly_eval_deriv_cons c w x).
      change (qpoly_deriv_iter 1 w) with (qpoly_deriv w).
      change (qpoly_deriv_iter 0 w) with w.
      change (Z.of_nat 1 # 1) with 1%Q.
      rewrite Qmult_1_l.
      ring.
  - assert (Istep : forall p v x,
        qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (qpoly_add p v)) x ==
        qpoly_eval (qpoly_deriv_iter (Datatypes.S m) p) x
        + qpoly_eval (qpoly_deriv_iter (Datatypes.S m) v) x).
    { induction p as [|a p IHp]; intros v x.
      - change (qpoly_add nil v) with v.
        rewrite (lw0_deriv_iter_nil (Datatypes.S m)).
        change (qpoly_eval nil x) with 0%Q.
        symmetry. apply Qplus_0_l.
      - destruct v as [|b v'].
        + rewrite qpoly_add_r_nil.
          rewrite (lw0_deriv_iter_nil (Datatypes.S m)).
          change (qpoly_eval nil x) with 0%Q.
          symmetry. apply Qplus_0_r.
        + change (qpoly_add (cons a p) (cons b v'))
            with (cons (a + b) (qpoly_add p v')).
          rewrite (IHcons (a + b) (qpoly_add p v') x).
          rewrite (IHp v' x).
          rewrite (IHadd p v' x).
          rewrite (IHcons a p x).
          rewrite (IHcons b v' x).
          ring. }
    split.
    + exact Istep.
    + intros c w x.
      change (qpoly_deriv_iter (Datatypes.S (Datatypes.S m)) (cons c w))
        with (qpoly_deriv (qpoly_deriv_iter (Datatypes.S m) (cons c w))).
      rewrite (qpoly_deriv_iter_commute m (cons c w)).
      change (qpoly_deriv (cons c w))
        with (qpoly_add w (cons 0 (qpoly_deriv w))).
      rewrite (Istep w (cons 0 (qpoly_deriv w)) x).
      rewrite (IHcons 0 (qpoly_deriv w) x).
      rewrite <- (qpoly_deriv_iter_commute (Datatypes.S m) w).
      rewrite <- (qpoly_deriv_iter_commute m w).
      assert (Hz : Z.of_nat (Datatypes.S (Datatypes.S m))
                   = (Z.of_nat (Datatypes.S m) + 1)%Z) by lia.
      rewrite Hz.
      assert (Hcoef : ((Z.of_nat (Datatypes.S m) + 1) # 1)%Q
                      == (Z.of_nat (Datatypes.S m) # 1) + 1%Q).
      { unfold Qeq. simpl. lia. }
      rewrite Hcoef.
      ring.
Qed.

(* 支柱 I 公开语句（m 级 eval 层可加性）。 *)
Lemma lw0_deriv_iter_add_eval : forall m p v x,
  qpoly_eval (qpoly_deriv_iter m (qpoly_add p v)) x ==
  qpoly_eval (qpoly_deriv_iter m p) x + qpoly_eval (qpoly_deriv_iter m v) x.
Proof. intros m p v x. exact (proj1 (lw0_deriv_iter_cons_add_joint m) p v x). Qed.

(* 支柱 CD 公开语句（cons 移位 Leibniz 式）。 *)
Lemma lw0_deriv_iter_cons_eval : forall m c w x,
  qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (cons c w)) x ==
  x * qpoly_eval (qpoly_deriv_iter (Datatypes.S m) w) x
  + (Z.of_nat (Datatypes.S m) # 1) * qpoly_eval (qpoly_deriv_iter m w) x.
Proof. intros m c w x. exact (proj2 (lw0_deriv_iter_cons_add_joint m) c w x). Qed.

(* 次数耗尽预算谓词（双支出形）：nil 恒真；cons 头在 0 步不保证零化，      *)
(* S n 步把预算拆为子表两笔支出（S n 与 n 各一笔）。                       *)
Fixpoint lw0_die (p : qpoly) (n : nat) : bool :=
  match p with
  | nil => true
  | cons _ p' =>
      match n with
      | Datatypes.O => false
      | Datatypes.S n' => lw0_die p' (Datatypes.S n') && lw0_die p' n'
      end
  end.

(* 预算兑现：die p n = true 时 iterated deriv n 次后逐点零化（eval 层）。 *)
Lemma lw0_die_zero : forall p n x,
  lw0_die p n = true -> qpoly_eval (qpoly_deriv_iter n p) x == 0%Q.
Proof.
  induction p as [|a p IH]; intros n x Hn.
  - rewrite (lw0_deriv_iter_nil n). reflexivity.
  - destruct n as [|n'].
    + simpl in Hn. discriminate Hn.
    + simpl in Hn. apply andb_true_iff in Hn. destruct Hn as [H1 H2].
      rewrite (lw0_deriv_iter_cons_eval n' a p x).
      rewrite (IH (Datatypes.S n') x H1).
      rewrite (IH n' x H2).
      ring.
Qed.

(* 交错符号 (−1)^j 的 Q 层载件。 *)
Fixpoint lw0_alt (j : nat) : Q :=
  match j with
  | Datatypes.O => 1%Q
  | Datatypes.S j' => Qopp (lw0_alt j')
  end.

Lemma lw0_alt_opp : forall j : nat, lw0_alt (Datatypes.S j) == Qopp (lw0_alt j).
Proof. intros j. reflexivity. Qed.

(* deriv 二次穿 scalar 的 eval 层一致性（cons-0 核，表归纳）。 *)
Lemma lw0_deriv2_scalar_eval : forall c p x,
  qpoly_eval (qpoly_deriv_iter 2 (qpoly_scalar c p)) x
  == c * qpoly_eval (qpoly_deriv_iter 2 p) x.
Proof.
  intros c p. induction p as [|b p IH]; intros x.
  - change (qpoly_scalar c nil) with (@nil Q).
    rewrite (lw0_deriv_iter_nil 2).
    change (qpoly_eval nil x) with 0%Q.
    ring.
  - change (qpoly_scalar c (cons b p)) with (cons (c * b) (qpoly_scalar c p)).
    change (qpoly_deriv_iter 2 (cons (c * b) (qpoly_scalar c p)))
      with (qpoly_deriv (qpoly_deriv (cons (c * b) (qpoly_scalar c p)))).
    change (qpoly_deriv (cons (c * b) (qpoly_scalar c p)))
      with (qpoly_add (qpoly_scalar c p)
              (cons 0 (qpoly_deriv (qpoly_scalar c p)))).
    rewrite (lw0_deriv_add_eval (qpoly_scalar c p)
               (cons 0 (qpoly_deriv (qpoly_scalar c p))) x).
    rewrite (qpoly_eval_deriv_scalar c p x).
    rewrite (qpoly_eval_scalar c (qpoly_deriv p) x).
    rewrite (qpoly_eval_deriv_cons 0 (qpoly_deriv (qpoly_scalar c p)) x).
    rewrite (qpoly_eval_deriv_scalar c p x).
    rewrite (qpoly_eval_scalar c (qpoly_deriv p) x).
    change (qpoly_deriv (qpoly_deriv (qpoly_scalar c p)))
      with (qpoly_deriv_iter 2 (qpoly_scalar c p)).
    rewrite (IH x).
    change (qpoly_deriv_iter 2 (cons b p))
      with (qpoly_deriv (qpoly_deriv (cons b p))).
    change (qpoly_deriv (cons b p)) with (qpoly_add p (cons 0 (qpoly_deriv p))).
    rewrite (lw0_deriv_add_eval p (cons 0 (qpoly_deriv p)) x).
    rewrite (qpoly_eval_deriv_cons 0 (qpoly_deriv p) x).
    change (qpoly_deriv (qpoly_deriv p)) with (qpoly_deriv_iter 2 p).
    ring.
Qed.

(* 交错和算子：lw0_F f J = Σ_{j≤J} (−1)^j · f^{(2j)}（表层，低次在首）。  *)
Fixpoint lw0_F_aux (f : qpoly) (c : Q) (J : nat) : qpoly :=
  match J with
  | Datatypes.O => qpoly_scalar c f
  | Datatypes.S J' =>
      qpoly_add (lw0_F_aux f c J')
        (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
           (qpoly_deriv_iter (2 * Datatypes.S J') f))
  end.

Definition lw0_F (f : qpoly) (J : nat) : qpoly := lw0_F_aux f 1%Q J.

(* F 与其二阶导之和＝c·f＋尾项（交错相消闭式；尾项系数 (−1)^J）。 *)
Lemma lw0_F_aux_plus_deriv2 : forall J f c x,
  qpoly_eval (lw0_F_aux f c J) x
  + qpoly_eval (qpoly_deriv_iter 2 (lw0_F_aux f c J)) x ==
  c * qpoly_eval f x
  + c * lw0_alt J * qpoly_eval (qpoly_deriv_iter (2 * Datatypes.S J) f) x.
Proof.
  induction J as [|J' IH]; intros f c x.
  - change (lw0_F_aux f c 0) with (qpoly_scalar c f).
    rewrite (qpoly_eval_scalar c f x).
    rewrite (lw0_deriv2_scalar_eval c f x).
    change (lw0_alt 0%nat) with 1%Q.
    change (2 * Datatypes.S 0)%nat with 2%nat.
    ring.
  - change (lw0_F_aux f c (Datatypes.S J'))
      with (qpoly_add (lw0_F_aux f c J')
              (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                 (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    rewrite (qpoly_eval_add (lw0_F_aux f c J')
              (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                 (qpoly_deriv_iter (2 * Datatypes.S J') f)) x).
    rewrite (lw0_deriv_iter_add_eval 2 (lw0_F_aux f c J')
               (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                  (qpoly_deriv_iter (2 * Datatypes.S J') f)) x).
    transitivity (c * qpoly_eval f x
                  + c * lw0_alt J' * qpoly_eval (qpoly_deriv_iter (2 * Datatypes.S J') f) x
                  + (qpoly_eval (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                       (qpoly_deriv_iter (2 * Datatypes.S J') f)) x
                    + qpoly_eval (qpoly_deriv_iter 2
                         (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                            (qpoly_deriv_iter (2 * Datatypes.S J') f))) x)).
    + rewrite <- (IH f c x). ring.
    + rewrite (qpoly_eval_scalar (c * lw0_alt (Datatypes.S J'))%Q
                (qpoly_deriv_iter (2 * Datatypes.S J') f) x).
      rewrite (lw0_deriv2_scalar_eval (c * lw0_alt (Datatypes.S J'))%Q
                 (qpoly_deriv_iter (2 * Datatypes.S J') f) x).
      rewrite <- (lw0_qp_deriv_iter_plus 2 (2 * Datatypes.S J') f).
    replace (2 + 2 * Datatypes.S J')%nat
      with (2 * Datatypes.S (Datatypes.S J'))%nat by lia.
    rewrite (lw0_alt_opp J').
    ring.
Qed.

(* 交付面：超尾预算下 F + F 的二阶导 == f（交错相消＋尾项零化）。 *)
Lemma lw0_F_plus_deriv2 : forall f J x,
  lw0_die f (2 * Datatypes.S J) = true ->
  qpoly_eval (lw0_F f J) x + qpoly_eval (qpoly_deriv_iter 2 (lw0_F f J)) x
  == qpoly_eval f x.
Proof.
  intros f J x Hdie.
  unfold lw0_F.
  rewrite (lw0_F_aux_plus_deriv2 J f 1%Q x).
  rewrite (lw0_die_zero f (2 * Datatypes.S J) x Hdie).
  ring.
Qed.


(* ========================================================================== *)
(* 尾段施工：实层包装（lw0_*_series_real 系）—— S05 波最后一块砖               *)
(* ------------------------------------------------------------              *)
(* 使命：把 S10 级数部分和替身层包装进 S02 实数层 Real，并与 S10 双            *)
(*   Defined 壳（cauchy_real_sin / cauchy_real_cos）立逐点差为零传输壳。      *)
(* 依赖：S10_KVQuantTrig（sc_sin_partial_cauchy_bounded /                     *)
(*   sc_cos_partial_cauchy_bounded 双柯西源件；cauchy_real_sin/cos）；        *)
(*   S02_CauchyComplete（Real/real_eq/q_abs_self_zero/Qle_to_QleT'/           *)
(*   Qcompare_comp/Qlt_alt，经 S10 的 Require 面传递可见）。                  *)
(* 对标：S02 real_const 常值嵌入（Defined 可计算先例）与 real_eq_refl         *)
(*   （逐点差为零判等模式）。                                                *)
(* 构造性：全件 Defined/Qed 闭合、零承认词面；包装投影体取 S10 部分和逐点形，    *)
(*   柯西界以 B:=Qabs q 自反闭合（QleT' (Qabs q) (Qabs q)）。                 *)
(* 编译配方：同头注；S10_KVQuantTrig.vo 须在 vo 树就绪。                      *)
(* 同名异体警示：本段 Require 之后 sin_partial / cos_partial 指称即切至       *)
(*   S10 体（与本件前段替身层同名异体）；本段内所有指称均为 S10 体，为        *)
(*   传输壳 unfold 路线所需；前段已解析面固化不受影响。                       *)
(* ========================================================================== *)

(* S10 头部系 Require Import（非 Export），S02 实数层名字不随传递——         *)
(* 本段显式 Require S02（Real/real_eq/q_abs_self_zero 等）后接 S10。        *)

(* 交付面：sin 级数在 q 处的实层包装（投影体逐点 sin_partial n q）。 *)
Definition lw0_sin_series_real (q : Q) : Real.
Proof.
  exists (fun n : nat => sin_partial n q).
  intros eps Heps.
  destruct (sc_sin_partial_cauchy_bounded (Qabs q) eps
             (Qle_to_QleT' 0 (Qabs q) (Qabs_nonneg q)) Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply (HN m n Hm Hn q). apply Qle_to_QleT'. apply Qle_refl.
Defined.

(* 交付面：cos 级数在 q 处的实层包装（投影体逐点 cos_partial n q）。 *)
Definition lw0_cos_series_real (q : Q) : Real.
Proof.
  exists (fun n : nat => cos_partial n q).
  intros eps Heps.
  destruct (sc_cos_partial_cauchy_bounded (Qabs q) eps
             (Qle_to_QleT' 0 (Qabs q) (Qabs_nonneg q)) Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply (HN m n Hm Hn q). apply Qle_to_QleT'. apply Qle_refl.
Defined.

(* 传输壳：S10 双 Defined 壳与本件包装在实层相等（逐点差为零路线；          *)
(* 双侧投影 conversion 同归约——Qabs_wd＋Qeq_refl 闭合，Qcompare_comp 桥）。 *)
Lemma lw0_sin_series_real_eq : forall q : Q,
  real_eq (cauchy_real_sin (real_const q)) (lw0_sin_series_real q).
Proof.
  intros q eps Heps. exists O. intros n Hn.
  (* 双侧投影经 conversion 同归约到 sin_partial n q —— Qabs_wd 后 Qeq_refl 闭合 *)
  assert (Hz : Qabs (projT1 (cauchy_real_sin (real_const q)) n
               - projT1 (lw0_sin_series_real q) n) == 0).
  { apply (Qeq_trans _ (Qabs (sin_partial n q - sin_partial n q)) _).
    - apply Qabs_wd. apply Qeq_refl.
    - apply q_abs_self_zero. }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (projT1 (cauchy_real_sin (real_const q)) n
               - projT1 (lw0_sin_series_real q) n)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (projT1 (cauchy_real_sin (real_const q)) n
                 - projT1 (lw0_sin_series_real q) n)) eps = Qcompare 0 eps).
    { exact (Qcompare_comp _ 0 Hz eps eps (Qeq_refl eps)). }
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* 传输壳：cos 侧对称件。 *)
Lemma lw0_cos_series_real_eq : forall q : Q,
  real_eq (cauchy_real_cos (real_const q)) (lw0_cos_series_real q).
Proof.
  intros q eps Heps. exists O. intros n Hn.
  (* 双侧投影经 conversion 同归约到 cos_partial n q —— Qabs_wd 后 Qeq_refl 闭合 *)
  assert (Hz : Qabs (projT1 (cauchy_real_cos (real_const q)) n
               - projT1 (lw0_cos_series_real q) n) == 0).
  { apply (Qeq_trans _ (Qabs (cos_partial n q - cos_partial n q)) _).
    - apply Qabs_wd. apply Qeq_refl.
    - apply q_abs_self_zero. }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (projT1 (cauchy_real_cos (real_const q)) n
               - projT1 (lw0_cos_series_real q) n)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (projT1 (cauchy_real_cos (real_const q)) n
                 - projT1 (lw0_cos_series_real q) n)) eps = Qcompare 0 eps).
    { exact (Qcompare_comp _ 0 Hz eps eps (Qeq_refl eps)). }
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.


(* ================= §5 端点泛函值的整数性 ================= *)
(* 段体来源：LW0Integrality2.v 现势 932 行 md5 2f53d4d44043134dae107b28c889be14
   （K_integer 主见证在段版），取形时点 2026 09 29。内嵌适配面：qpoly_zero、
   qpoly_opp、lw0_mono 三名与 §4 段同形同名，取 §4 份，本段零重定义；
   Require 面、提取面与公理自审面并入件级尾段。以 S07 定版为准按三元组重验。 *)

(* ------------------------------------------------------------------ *)
(* S05 adaptation shell (pending merge; see header).                   *)
(* ------------------------------------------------------------------ *)


Lemma lw0_eval_opp : forall p x,
  qpoly_eval (qpoly_opp p) x == - (qpoly_eval p x).
Proof.
  intro p; induction p as [|a p IH]; intro x; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

Lemma lw0_Qmake_plus : forall x y : Z,
  (x # 1)%Q + (y # 1)%Q == ((x + y) # 1)%Q.
Proof.
  intros x y. unfold Qeq, Qeq_bool. simpl.
  repeat rewrite Z.mul_1_r. reflexivity.
Qed.

(* The Qmake-atom glue bridge: ((1+z)#1) is a Qmake atom for ring; this    *)
(* turns it into the Qplus form 1 + (z#1) that ring closes.                *)
Lemma lw0_Qmake_succ : forall z : Z, ((1 + z) # 1)%Q == 1 + (z # 1)%Q.
Proof.
  intros z. unfold Qeq, Qeq_bool. simpl.
  repeat rewrite Z.mul_1_r. reflexivity.
Qed.

(* 接手注记：Qmake 头 Qeq 引理的 setoid rewrite 会降入 Qeq_bool 展开        *)
(* 形搜索而失配（第一手 .err 实证）。故一切 (1+z)#1 原子改形不走 rewrite，   *)
(* 走下面的 Leibniz 孪生件 + 纯 replace（无 setoid 机器）。                 *)
Lemma lw0_Qmake_succ_eq : forall z : Z,
  ((1 + z) # 1)%Q = (1 + (z # 1)%Q)%Q.
Proof.
  intros z.
  replace (1 + (z # 1)%Q)%Q with (Qmake (1 * 1 + z * 1) (1 * 1))
    by reflexivity.
  apply f_equal2.
  - lia.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The coefficient functional: j-th coefficient of a coefficient list. *)
(* ------------------------------------------------------------------ *)

Fixpoint lw0_coef (j : nat) (p : QPoly) {struct p} : Q :=
  match p with
  | nil => 0%Q
  | cons a p' =>
      match j with
      | 0%nat => a
      | Datatypes.S j' => lw0_coef j' p'
      end
  end.

Lemma lw0_coef_add : forall (j : nat) (p q : QPoly),
  lw0_coef j (qpoly_add p q) == lw0_coef j p + lw0_coef j q.
Proof.
  intros j p; revert j; induction p as [|a p IH]; intros j q.
  - destruct q as [|b q]; simpl; ring.
  - destruct q as [|b q].
    + simpl. ring.
    + destruct j as [|j'].
      * simpl. reflexivity.
      * change (qpoly_add (cons a%Q p) (cons b%Q q))
          with (cons (a + b)%Q (qpoly_add p q)).
        change (lw0_coef (Datatypes.S j') (cons (a + b)%Q (qpoly_add p q)))
          with (lw0_coef j' (qpoly_add p q)).
        change (lw0_coef (Datatypes.S j') (cons a%Q p)) with (lw0_coef j' p).
        change (lw0_coef (Datatypes.S j') (cons b%Q q)) with (lw0_coef j' q).
        apply (IH j' q).
Qed.

Lemma lw0_coef_scalar : forall j a p,
  lw0_coef j (qpoly_scalar a p) == a * lw0_coef j p.
Proof.
  intros j a p; revert j; induction p as [|b p IH]; intros j.
  - simpl. ring.
  - destruct j as [|j'].
    + simpl. ring.
    + change (qpoly_scalar a (cons b%Q p))
        with (cons (a * b)%Q (qpoly_scalar a p)).
      change (lw0_coef (Datatypes.S j') (cons (a * b)%Q (qpoly_scalar a p)))
        with (lw0_coef j' (qpoly_scalar a p)).
      change (lw0_coef (Datatypes.S j') (cons b%Q p)) with (lw0_coef j' p).
      apply (IH j').
Qed.

Lemma lw0_coef_opp : forall j p,
  lw0_coef j (qpoly_opp p) == - (lw0_coef j p).
Proof.
  intros j p; revert j; induction p as [|a p IH]; intros j.
  - simpl. ring.
  - destruct j as [|j'].
    + simpl. ring.
    + change (qpoly_opp (cons a%Q p)) with (cons (- a)%Q (qpoly_opp p)).
      change (lw0_coef (Datatypes.S j') (cons (- a)%Q (qpoly_opp p)))
        with (lw0_coef j' (qpoly_opp p)).
      change (lw0_coef (Datatypes.S j') (cons a%Q p)) with (lw0_coef j' p).
      apply (IH j').
Qed.

Lemma lw0_coef_deriv : forall j p,
  lw0_coef j (qpoly_deriv p)
  == (Z.of_nat (Datatypes.S j) # 1)%Q * lw0_coef (Datatypes.S j) p.
Proof.
  intros j p; revert j; induction p as [|a p IH]; intro j; simpl.
  - ring.
  - rewrite lw0_coef_add.
    destruct j as [|j'].
    + simpl. ring.
    + simpl (lw0_coef (Datatypes.S j') (cons 0%Q (qpoly_deriv p))).
      rewrite (IH j').
      replace (Z.pos (PosDef.Pos.of_succ_nat (Datatypes.S j')))
        with (Z.of_nat (Datatypes.S (Datatypes.S j')))%Z by reflexivity.
      replace (Z.of_nat (Datatypes.S (Datatypes.S j')))
        with (1 + Z.of_nat (Datatypes.S j'))%Z by lia.
      replace ((1 + Z.of_nat (Datatypes.S j')) # 1)%Q
        with (1 + (Z.of_nat (Datatypes.S j') # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      ring.
Qed.

(* Coefficients of iterated derivatives, in multiplied form (no         *)
(* division): coefficient j of the k-th derivative carries the          *)
(* falling product q_fact (j+k) / q_fact j.                             *)
Lemma lw0_coef_iter_mul : forall k j p,
  lw0_coef j (qpoly_deriv_iter k p) * q_fact j
  == q_fact (j + k) * lw0_coef (j + k) p.
Proof.
  induction k as [|k IH]; intros j p.
  - rewrite Nat.add_0_r. rewrite Qmult_comm. reflexivity.
  - assert (IHj := IH (Datatypes.S j) p).
    replace (Datatypes.S j + k)%nat with (Datatypes.S (j + k))%nat in IHj by lia.
    replace (j + Datatypes.S k)%nat with (Datatypes.S (j + k))%nat by lia.
    simpl (qpoly_deriv_iter (Datatypes.S k) p).
    rewrite lw0_coef_deriv.
    rewrite q_fact_succ in IHj. rewrite q_fact_succ in IHj.
    rewrite (q_fact_succ (j + k)).
    rewrite (Qmult_comm (Z.of_nat (Datatypes.S j) # 1)%Q
               (lw0_coef (Datatypes.S j) (qpoly_deriv_iter k p))).
    rewrite <- (Qmult_assoc (lw0_coef (Datatypes.S j) (qpoly_deriv_iter k p))
               (Z.of_nat (Datatypes.S j) # 1)%Q (q_fact j)).
    exact IHj.
Qed.

(* THE linear law: iterated derivation is additive at the coef layer.   *)
Lemma lw0_coef_iter_add : forall k j u v,
  lw0_coef j (qpoly_deriv_iter k (qpoly_add u v))
  == lw0_coef j (qpoly_deriv_iter k u) + lw0_coef j (qpoly_deriv_iter k v).
Proof.
  induction k as [|k IH]; intros j u v; simpl.
  - apply lw0_coef_add.
  - rewrite !lw0_coef_deriv, (IH (Datatypes.S j) u v). ring.
Qed.

Lemma lw0_coef_iter_scalar : forall k j a p,
  lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p))
  == a * lw0_coef j (qpoly_deriv_iter k p).
Proof.
  induction k as [|k IH]; intros j a p; simpl.
  - apply lw0_coef_scalar.
  - rewrite lw0_coef_deriv, lw0_coef_deriv, (IH (Datatypes.S j) a p). ring.
Qed.

Lemma lw0_coef_iter_opp : forall k j p,
  lw0_coef j (qpoly_deriv_iter k (qpoly_opp p))
  == - lw0_coef j (qpoly_deriv_iter k p).
Proof.
  induction k as [|k IH]; intros j p; simpl.
  - apply lw0_coef_opp.
  - rewrite lw0_coef_deriv, lw0_coef_deriv, (IH (Datatypes.S j) p). ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The eval-layer bridge: coefficientwise equality gives pointwise     *)
(* evaluation equality; iterated-congruence and iterated additivity    *)
(* at the eval layer follow (this breaks the registered deadlock).     *)
(* ------------------------------------------------------------------ *)

Lemma lw0_eval_at_zero : forall p : QPoly, qpoly_eval p 0 == lw0_coef 0 p.
Proof.
  destruct p as [|a p]; simpl; ring.
Qed.

Lemma lw0_eval_deriv_coef0 : forall k p,
  qpoly_eval (qpoly_deriv_iter k p) 0 == q_fact k * lw0_coef k p.
Proof.
  induction k as [|k IH]; intro p.
  - rewrite lw0_eval_at_zero. simpl. ring.
  - simpl (qpoly_deriv_iter (Datatypes.S k) p).
    rewrite lw0_eval_at_zero.
    rewrite lw0_coef_deriv.
    replace (Z.of_nat (Datatypes.S 0)) with 1%Z by lia.
    assert (Hq1 : q_fact (Datatypes.S 0) == 1%Q) by (simpl; ring).
    pose proof (lw0_coef_iter_mul k (Datatypes.S 0) p) as Hm.
    rewrite Hq1 in Hm.
    replace (Datatypes.S 0 + k)%nat with (Datatypes.S k) in Hm by lia.
    rewrite Qmult_1_r in Hm.
    rewrite Hm. ring.
Qed.

Lemma lw0_eval_zero_coef : forall p x,
  (forall j, lw0_coef j p == 0) -> qpoly_eval p x == 0.
Proof.
  induction p as [|a p IH]; intros x H; simpl in *.
  - ring.
  - assert (Ha : a == 0) by (apply (H 0%nat)).
    assert (Hp : forall j, lw0_coef j p == 0)
      by (intro j; apply (H (Datatypes.S j))).
    rewrite Ha, (IH x Hp). ring.
Qed.

Lemma lw0_eval_len_indep : forall p q x,
  (forall j, lw0_coef j p == lw0_coef j q) -> qpoly_eval p x == qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x H.
  - destruct q as [|b q].
    + simpl. ring.
    + symmetry. apply lw0_eval_zero_coef. intro j. destruct j as [|j'].
      * assert (H0 := H 0%nat). simpl in H0. symmetry. exact H0.
      * assert (Hs := H (Datatypes.S j')). simpl in Hs. symmetry. exact Hs.
  - destruct q as [|b q].
    + apply lw0_eval_zero_coef. intro j. destruct j as [|j'].
      * assert (H0 := H 0%nat). simpl in H0. exact H0.
      * assert (Hs := H (Datatypes.S j')). simpl in Hs. exact Hs.
    + assert (Hab : a == b) by (apply (H 0%nat)).
      assert (Hpq : forall j, lw0_coef j p == lw0_coef j q).
      { intro j.
        assert (Hs := H (Datatypes.S j)). simpl in Hs. exact Hs. }
      simpl. rewrite Hab, (IH q x Hpq). ring.
Qed.

Lemma lw0_coef_iter_congr : forall k u v,
  (forall j, lw0_coef j u == lw0_coef j v) ->
  forall j, lw0_coef j (qpoly_deriv_iter k u)
            == lw0_coef j (qpoly_deriv_iter k v).
Proof.
  induction k as [|k IH]; intros u v H j.
  - apply H.
  - simpl. rewrite lw0_coef_deriv, (IH u v H), lw0_coef_deriv. reflexivity.
Qed.

Lemma lw0_eval_iter_congr : forall k u v x,
  (forall j, lw0_coef j u == lw0_coef j v) ->
  qpoly_eval (qpoly_deriv_iter k u) x
  == qpoly_eval (qpoly_deriv_iter k v) x.
Proof.
  intros k u v x H. apply lw0_eval_len_indep. apply (lw0_coef_iter_congr k u v H).
Qed.

(* Iterated derivation is additive at the eval layer: the coef bridge   *)
(* (coef_iter_add + coef_add + eval_len_indep) closes the registered    *)
(* deadlock shape qpoly_eval_deriv_iter_add.                            *)
Lemma lw0_eval_deriv_iter_add : forall k u v x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_add u v)) x
  == qpoly_eval (qpoly_deriv_iter k u) x + qpoly_eval (qpoly_deriv_iter k v) x.
Proof.
  intros k u v x.
  transitivity (qpoly_eval
                  (qpoly_add (qpoly_deriv_iter k u) (qpoly_deriv_iter k v)) x).
  - apply lw0_eval_len_indep. intro j.
    rewrite lw0_coef_iter_add, lw0_coef_add. reflexivity.
  - rewrite qpoly_eval_add. reflexivity.
Qed.

Lemma lw0_eval_deriv_iter_scalar : forall k a p x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_scalar a p)) x
  == a * qpoly_eval (qpoly_deriv_iter k p) x.
Proof.
  intros k a p x.
  transitivity (qpoly_eval (qpoly_scalar a (qpoly_deriv_iter k p)) x).
  - apply lw0_eval_len_indep. intro j.
    rewrite lw0_coef_iter_scalar, lw0_coef_scalar. reflexivity.
  - rewrite qpoly_eval_scalar. reflexivity.
Qed.

Lemma lw0_eval_iter_opp : forall k p x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_opp p)) x
  == - qpoly_eval (qpoly_deriv_iter k p) x.
Proof.
  intros k p x.
  transitivity (qpoly_eval (qpoly_opp (qpoly_deriv_iter k p)) x).
  - apply lw0_eval_len_indep. intro j.
    rewrite lw0_coef_iter_opp, lw0_coef_opp. reflexivity.
  - rewrite lw0_eval_opp. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The shift law for t*P and the qtail recursion, both via the bridge. *)
(* ------------------------------------------------------------------ *)

Definition lw0_pred_iter (k : nat) (w : QPoly) : QPoly :=
  match k with
  | 0%nat => w
  | Datatypes.S k' => qpoly_deriv_iter k' w
  end.

Lemma lw0_shift_deriv : forall k w x,
  qpoly_eval (qpoly_deriv_iter k (cons 0 w)) x
  == x * qpoly_eval (qpoly_deriv_iter k w) x
  + (Z.of_nat k # 1)%Q * qpoly_eval (lw0_pred_iter k w) x.
Proof.
  induction k as [|k IH]; intros w x.
  - simpl. ring.
  - rewrite qpoly_deriv_iter_commute.
    change (qpoly_deriv (cons 0 w))
      with (qpoly_add w (cons 0 (qpoly_deriv w))).
    rewrite lw0_eval_deriv_iter_add.
    rewrite (IH (qpoly_deriv w) x).
    rewrite <- (qpoly_deriv_iter_commute k w).
    destruct k as [|k'].
    + change (lw0_pred_iter 0%nat (qpoly_deriv w)) with (qpoly_deriv w).
      change (qpoly_deriv_iter (Datatypes.S 0) w) with (qpoly_deriv w).
      change (lw0_pred_iter (Datatypes.S 0) w) with (qpoly_deriv_iter 0%nat w).
      change (qpoly_deriv_iter 0%nat w) with w.
      replace (Z.of_nat 0) with 0%Z by lia.
      replace (Z.of_nat (Datatypes.S 0)) with 1%Z by lia.
      ring.
    + change (lw0_pred_iter (Datatypes.S k') (qpoly_deriv w))
        with (qpoly_deriv_iter k' (qpoly_deriv w)).
      rewrite <- (qpoly_deriv_iter_commute k' w).
      change (lw0_pred_iter (Datatypes.S (Datatypes.S k')) w)
        with (qpoly_deriv_iter (Datatypes.S k') w).
      replace (Z.of_nat (Datatypes.S (Datatypes.S k')))
        with (1 + Z.of_nat (Datatypes.S k'))%Z by lia.
      replace (Z.of_nat (Datatypes.S k')) with (1 + Z.of_nat k')%Z by lia.
      replace ((1 + (1 + Z.of_nat k')) # 1)%Q
        with (1 + ((1 + Z.of_nat k') # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      replace ((1 + Z.of_nat k') # 1)%Q
        with (1 + (Z.of_nat k' # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      ring.
Qed.

(* The rational tail polynomial P |-> q*P - t*P (the factor (q-t)). *)
Definition lw0_qtail (q : Q) (P : QPoly) : QPoly :=
  qpoly_add (qpoly_scalar q P) (cons 0 (qpoly_opp P)).

(* The one-step derivative congruence D(qtail q P) = qtail q P' - P,   *)
(* proved at the coef layer (list Leibniz is false; eval is the goal).  *)
Lemma lw0_qtail_deriv_congr : forall q P j,
  lw0_coef j (qpoly_deriv (lw0_qtail q P))
  == lw0_coef j (qpoly_add (lw0_qtail q (qpoly_deriv P)) (qpoly_opp P)).
Proof.
  intros q P j. unfold lw0_qtail.
  rewrite lw0_coef_deriv.
  rewrite lw0_coef_add. rewrite lw0_coef_add. rewrite lw0_coef_add.
  rewrite lw0_coef_scalar. rewrite lw0_coef_scalar.
  destruct j as [|j'].
  - simpl. rewrite lw0_coef_opp.
    rewrite (lw0_coef_deriv 0%nat P).
    replace (Z.of_nat (Datatypes.S 0)) with 1%Z by lia.
    ring.
  - simpl (lw0_coef (Datatypes.S (Datatypes.S j')) (cons 0%Q (qpoly_opp P))).
    simpl (lw0_coef (Datatypes.S j') (cons 0%Q (qpoly_opp (qpoly_deriv P)))).
    rewrite lw0_coef_opp. rewrite lw0_coef_opp.
    rewrite lw0_coef_deriv. rewrite lw0_coef_deriv.
    replace (Z.of_nat (Datatypes.S (Datatypes.S j')))
      with (1 + Z.of_nat (Datatypes.S j'))%Z by lia.
    replace ((1 + Z.of_nat (Datatypes.S j')) # 1)%Q
      with (1 + (Z.of_nat (Datatypes.S j') # 1))%Q
      by (symmetry; apply lw0_Qmake_succ_eq).
    ring.
Qed.

(* The qtail recursion: eval(D^k(qtail q P)) q == -k * P^(k-1) (q).     *)
(* Pinned recurrence, now closed through the coef bridge.               *)
Lemma lw0_qtail_step : forall q P k,
  qpoly_eval (qpoly_deriv_iter k (lw0_qtail q P)) q
  == - ((Z.of_nat k # 1)%Q * qpoly_eval (lw0_pred_iter k P) q).
Proof.
  intros q P k. revert P. induction k as [|k IH]; intros P.
  - unfold lw0_qtail. simpl.
    rewrite (qpoly_eval_add (qpoly_scalar q P) (cons 0%Q (qpoly_opp P)) q).
    rewrite (qpoly_eval_scalar q P q). simpl.
    rewrite (lw0_eval_opp P q). ring.
  - rewrite qpoly_deriv_iter_commute.
    rewrite (lw0_eval_iter_congr k (qpoly_deriv (lw0_qtail q P))
               (qpoly_add (lw0_qtail q (qpoly_deriv P)) (qpoly_opp P)) q
               (fun j => lw0_qtail_deriv_congr q P j)).
    rewrite (lw0_eval_deriv_iter_add k (lw0_qtail q (qpoly_deriv P))
               (qpoly_opp P) q).
    rewrite (IH (qpoly_deriv P)).
    rewrite (lw0_eval_iter_opp k P q).
    change (lw0_pred_iter (Datatypes.S k) P) with (qpoly_deriv_iter k P).
    destruct k as [|k'].
    + replace (Z.of_nat 0) with 0%Z by lia.
      replace (Z.of_nat (Datatypes.S 0)) with 1%Z by lia.
      change (lw0_pred_iter 0%nat (qpoly_deriv P)) with (qpoly_deriv P).
      change (qpoly_deriv_iter 0%nat P) with P.
      ring.
    + change (lw0_pred_iter (Datatypes.S k') (qpoly_deriv P))
        with (qpoly_deriv_iter k' (qpoly_deriv P)).
      rewrite <- (qpoly_deriv_iter_commute k' P).
      replace (Z.of_nat (Datatypes.S (Datatypes.S k')))
        with (1 + Z.of_nat (Datatypes.S k'))%Z by lia.
      replace (Z.of_nat (Datatypes.S k')) with (1 + Z.of_nat k')%Z by lia.
      replace ((1 + (1 + Z.of_nat k')) # 1)%Q
        with (1 + ((1 + Z.of_nat k') # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      replace ((1 + Z.of_nat k') # 1)%Q
        with (1 + (Z.of_nat k' # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Niven polynomial machinery: mono, q-t power, scaled product; the    *)
(* 0-endpoint zero branch (step 1, first half of the trisection).      *)
(* ------------------------------------------------------------------ *)


Lemma lw0_coef_mul_mono_lt : forall n k (W : QPoly), (k < n)%nat ->
  lw0_coef k (qpoly_mul (lw0_mono n) W) == 0.
Proof.
  induction n as [|m IH]; intros k W Hk.
  - lia.
  - destruct k as [|k'].
    + change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
      change (qpoly_mul (cons 0 (lw0_mono m)) W)
        with (qpoly_add (qpoly_scalar 0%Q W)
                        (cons 0 (qpoly_mul (lw0_mono m) W))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      simpl (lw0_coef 0%nat (cons 0%Q (qpoly_mul (lw0_mono m) W))).
      ring.
    + change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
      change (qpoly_mul (cons 0 (lw0_mono m)) W)
        with (qpoly_add (qpoly_scalar 0%Q W)
                        (cons 0 (qpoly_mul (lw0_mono m) W))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      simpl (lw0_coef (Datatypes.S k') (cons 0%Q (qpoly_mul (lw0_mono m) W))).
      assert (IH0 : lw0_coef k' (qpoly_mul (lw0_mono m) W) == 0%Q)
        by (apply (IH k' W ltac:(lia))).
      rewrite IH0.
      ring.
Qed.

Lemma lw0_coef_mul_mono_ge : forall n k (W : QPoly), (n <= k)%nat ->
  lw0_coef k (qpoly_mul (lw0_mono n) W) == lw0_coef (k - n) W.
Proof.
  induction n as [|m IH]; intros k W Hk.
  - replace (k - 0)%nat with k by lia.
    change (qpoly_mul (lw0_mono 0) W)
      with (qpoly_add (qpoly_scalar 1%Q W) (cons 0%Q (@nil Q))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct k as [|k''].
    + simpl. ring.
    + simpl (lw0_coef (Datatypes.S k'') (cons 0%Q (@nil Q))). ring.
  - destruct k as [|k']; [ lia | ].
    change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
    change (qpoly_mul (cons 0 (lw0_mono m)) W)
      with (qpoly_add (qpoly_scalar 0%Q W)
                      (cons 0 (qpoly_mul (lw0_mono m) W))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    simpl (lw0_coef (Datatypes.S k') (cons 0%Q (qpoly_mul (lw0_mono m) W))).
    rewrite (IH k' W ltac:(lia)).
    replace (Datatypes.S k' - Datatypes.S m)%nat with (k' - m)%nat by lia.
    ring.
Qed.

Fixpoint lw0_qminus_pow (q : Q) (n : nat) : QPoly :=
  match n with
  | 0%nat => cons 1 nil
  | Datatypes.S m =>
      qpoly_mul (lw0_qminus_pow q m) (cons q (cons (-1)%Q nil))
  end.

(* Named lw0_niven_f_z: the plain name lw0_niven_f denotes the Q-domain  *)
(* polynomial (q b : Q) form carried by LW0_PiAsm; this Z-base           *)
(* coefficient form takes the suffixed name.                             *)
Definition lw0_niven_f_z (q : Q) (b : Z) (n : nat) : QPoly :=
  qpoly_scalar ((Zpower_nat b n) # (Pos.of_nat (fact n)))%Q
    (qpoly_mul (lw0_mono n) (lw0_qminus_pow q n)).

(* Step 1, 0-endpoint: derivatives of order below n vanish at 0. *)
Lemma lw0_niven_deriv_zero_0 : forall q b n k, (k < n)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z q b n)) 0 == 0.
Proof.
  intros q b n k Hk. unfold lw0_niven_f_z.
  rewrite lw0_eval_deriv_iter_scalar, lw0_eval_deriv_coef0.
  assert (H0 : lw0_coef k
                 (qpoly_mul (lw0_mono n) (lw0_qminus_pow q n)) == 0%Q)
    by (apply (lw0_coef_mul_mono_lt n k (lw0_qminus_pow q n) Hk)).
  rewrite H0.
  ring.
Qed.

(* Pascal closed form of the (q-t)^n coefficients (mandate item 6). *)
Lemma lw0_coef_mul_h0 : forall (A : QPoly) q,
  lw0_coef 0%nat (qpoly_mul A (cons q (cons (-1)%Q nil)))
  == q * lw0_coef 0%nat A.
Proof.
  induction A as [|a A IH]; intro q.
  - simpl. ring.
  - change (qpoly_mul (cons a A) (cons q (cons (-1)%Q nil)))
      with (qpoly_add (qpoly_scalar a (cons q (cons (-1)%Q nil)))
                      (cons 0 (qpoly_mul A (cons q (cons (-1)%Q nil))))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    simpl (lw0_coef 0%nat (cons q (cons (-1)%Q nil))).
    simpl (lw0_coef 0%nat (cons 0%Q (qpoly_mul A (cons q (cons (-1)%Q nil))))).
    simpl (lw0_coef 0%nat (cons a%Q A)).
    ring.
Qed.

Lemma lw0_coef_mul_hS : forall (A : QPoly) q j,
  lw0_coef (Datatypes.S j) (qpoly_mul A (cons q (cons (-1)%Q nil)))
  == q * lw0_coef (Datatypes.S j) A - lw0_coef j A.
Proof.
  induction A as [|a A IH]; intros q j.
  - simpl. ring.
  - change (qpoly_mul (cons a A) (cons q (cons (-1)%Q nil)))
      with (qpoly_add (qpoly_scalar a (cons q (cons (-1)%Q nil)))
                      (cons 0 (qpoly_mul A (cons q (cons (-1)%Q nil))))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + simpl (lw0_coef (Datatypes.S 0) (cons q (cons (-1)%Q nil))).
      simpl (lw0_coef (Datatypes.S 0)
               (cons 0%Q (qpoly_mul A (cons q (cons (-1)%Q nil))))).
      simpl (lw0_coef (Datatypes.S 0) (cons a A)).
      simpl (lw0_coef 0%nat (cons a A)).
      rewrite (lw0_coef_mul_h0 A q). ring.
    + simpl (lw0_coef (Datatypes.S (Datatypes.S j'))
               (cons q (cons (-1)%Q nil))).
      simpl (lw0_coef (Datatypes.S (Datatypes.S j'))
               (cons 0%Q (qpoly_mul A (cons q (cons (-1)%Q nil))))).
      rewrite (IH q j').
      destruct j' as [|j''].
      * simpl. ring.
      * simpl (lw0_coef (Datatypes.S (Datatypes.S (Datatypes.S j'')))
                  (cons q (cons (-1)%Q nil))).
        simpl (lw0_coef (Datatypes.S (Datatypes.S (Datatypes.S j'')))
                  (cons a%Q A)).
        simpl (lw0_coef (Datatypes.S (Datatypes.S j'')) (cons a%Q A)).
        ring.
Qed.

Lemma lw0_coef_qminus_pow : forall n q j,
  lw0_coef j (lw0_qminus_pow q n)
  == bpa_binom n j * q_pow (-1)%Q j * q_pow q (n - j)%nat.
Proof.
  induction n as [|m IH]; intros q j.
  - destruct j as [|j'].
    + simpl. ring.
    + simpl (lw0_coef (Datatypes.S j') (lw0_qminus_pow q 0)).
      simpl (bpa_binom 0 (Datatypes.S j')).
      simpl (q_pow (-1)%Q (Datatypes.S j')).
      simpl (q_pow q (0 - Datatypes.S j')).
      ring.
  - change (lw0_qminus_pow q (Datatypes.S m))
      with (qpoly_mul (lw0_qminus_pow q m) (cons q (cons (-1)%Q nil))).
    destruct j as [|j'].
    + rewrite (lw0_coef_mul_h0 (lw0_qminus_pow q m) q), (IH q 0%nat).
      rewrite (bpa_binom_0 (Datatypes.S m)), (bpa_binom_0 m).
      simpl (q_pow (-1)%Q 0).
      replace (Datatypes.S m - 0)%nat with (Datatypes.S m) by lia.
      replace (m - 0)%nat with m by lia.
      rewrite q_pow_succ. ring.
    + rewrite (lw0_coef_mul_hS (lw0_qminus_pow q m) q j').
      rewrite (IH q (Datatypes.S j')), (IH q j').
      rewrite (bpa_binom_pascal m j').
      replace (Datatypes.S m - Datatypes.S j')%nat with (m - j')%nat by lia.
      simpl (q_pow (-1)%Q (Datatypes.S j')).
      destruct (Nat.leb (Datatypes.S j') m) eqn:Hb.
      * apply Nat.leb_le in Hb.
        assert (HM : q_pow q (m - Datatypes.S j')%nat * q == q_pow q (m - j')%nat).
        { replace (m - j')%nat with (Datatypes.S (m - Datatypes.S j'))%nat by lia.
          rewrite q_pow_succ. ring. }
        rewrite <- HM. ring.
      * apply Nat.leb_gt in Hb.
        assert (Ho1 : bpa_binom m (Datatypes.S j') == 0%Q)
          by (apply (bpa_binom_out m (Datatypes.S j') Hb)).
        rewrite Ho1.
        ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Factorial divisibility (step 3): q_fact k = q_fact n * (w#1), with  *)
(* the integer witness built by the nat falling product lw0_ratio      *)
(* (no division anywhere).                                             *)
(* ------------------------------------------------------------------ *)

(* lw0_ratio n k = product of i over n+1 .. k (1 when k <= n). *)
Fixpoint lw0_ratio (n k : nat) : nat :=
  match k with
  | 0%nat => 1%nat
  | Datatypes.S k' =>
      if Nat.leb n k' then (Datatypes.S k' * lw0_ratio n k')%nat else 1%nat
  end.

Lemma lw0_fact_ratio : forall k n, (n <= k)%nat ->
  fact k = (fact n * lw0_ratio n k)%nat.
Proof.
  induction k as [|k' IH]; intros n Hk.
  - replace n with 0%nat by lia. reflexivity.
  - destruct (Nat.leb n k') eqn:Hb.
    + assert (Hle : (n <= k')%nat) by (apply Nat.leb_le; exact Hb).
      assert (Hf : fact (Datatypes.S k') = (Datatypes.S k' * fact k')%nat)
        by reflexivity.
      simpl (lw0_ratio n (Datatypes.S k')). rewrite Hb.
      rewrite Hf, (IH n Hle).
      rewrite Nat.mul_assoc, (Nat.mul_comm (Datatypes.S k') (fact n)).
      rewrite <- Nat.mul_assoc. reflexivity.
    + change (lw0_ratio n (Datatypes.S k'))
        with (if Nat.leb n k' then (Datatypes.S k' * lw0_ratio n k')%nat
              else 1%nat).
      rewrite Hb.
      replace (if false then (Datatypes.S k' * lw0_ratio n k')%nat else 1%nat)
        with 1%nat by reflexivity.
      apply Nat.leb_gt in Hb.
      replace n with (Datatypes.S k') by lia.
      rewrite Nat.mul_1_r. reflexivity.
Qed.

Lemma lw0_Qmake_mul : forall x y : Z, (x # 1)%Q * (y # 1)%Q == ((x * y) # 1)%Q.
Proof. intros x y. reflexivity. Qed.

Lemma lw0_qfact_Z : forall n, q_fact n == ((Z.of_nat (fact n)) # 1)%Q.
Proof.
  induction n as [|m IH].
  - reflexivity.
  - rewrite q_fact_succ, IH.
    assert (Hf : fact (Datatypes.S m) = (Datatypes.S m * fact m)%nat)
      by reflexivity.
    rewrite Hf.
    assert (Hm : ((Z.of_nat (Datatypes.S m) # 1)%Q
                  * ((Z.of_nat (fact m)) # 1)%Q)%Q
                 == ((Z.of_nat (Datatypes.S m) * Z.of_nat (fact m)) # 1)%Q)
      by (apply (lw0_Qmake_mul (Z.of_nat (Datatypes.S m))
                  (Z.of_nat (fact m)))).
    rewrite Hm, <- Nat2Z.inj_mul. reflexivity.
Qed.

Lemma lw0_int_fact_div : forall n k, (n <= k)%nat ->
  sigT (fun w : Z => Qeq (q_fact k) (q_fact n * (w # 1)%Q)).
Proof.
  intros n k Hk.
  assert (Hr := lw0_fact_ratio k n Hk).
  exists (Z.of_nat (lw0_ratio n k)).
  assert (H1 : q_fact k == ((Z.of_nat (fact k)) # 1)%Q) by apply lw0_qfact_Z.
  assert (H2 : q_fact n == ((Z.of_nat (fact n)) # 1)%Q) by apply lw0_qfact_Z.
  assert (H3 : ((Z.of_nat (fact n)) # 1)%Q * ((Z.of_nat (lw0_ratio n k)) # 1)%Q
               == ((Z.of_nat (fact n) * Z.of_nat (lw0_ratio n k)) # 1)%Q)
    by (apply (lw0_Qmake_mul (Z.of_nat (fact n)) (Z.of_nat (lw0_ratio n k)))).
  rewrite H1, H2, H3, <- Nat2Z.inj_mul, <- Hr.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* S07 assembly: the lo/hi closed forms over the corrected errata      *)
(* formulas.  z_lo := (-1)^(k-n) * C(n,k-n) * (k!/n!) * a^(2n-k)       *)
(* * b^(k-n) (generations-pinned errata form); the division-free       *)
(* factor (k!/n!) is carried by the in-file witness lw0_ratio.  The    *)
(* nat binomial and the sign live in the minimal local block below:    *)
(* the final shape follows the pending LW2Binom delivery.              *)
(* ------------------------------------------------------------------ *)

Fixpoint lw0_binom (n k : nat) {struct n} : nat :=
  match n with
  | 0%nat =>
      match k with
      | 0%nat => 1%nat
      | Datatypes.S _ => 0%nat
      end
  | Datatypes.S n' =>
      match k with
      | 0%nat => 1%nat
      | Datatypes.S k' => (lw0_binom n' k' + lw0_binom n' (Datatypes.S k'))%nat
      end
  end.

Lemma lw0_binom_pascal : forall n k : nat,
  lw0_binom (Datatypes.S n) (Datatypes.S k)
    = (lw0_binom n k + lw0_binom n (Datatypes.S k))%nat.
Proof. intros n k. reflexivity. Qed.

Lemma lw0_binom_0 : forall n : nat, lw0_binom n 0%nat = 1%nat.
Proof. intros n. destruct n as [|n']; reflexivity. Qed.

Lemma lw0_binom_out : forall n k : nat, (n < k)%nat -> lw0_binom n k = 0%nat.
Proof.
  intros n. induction n as [|n' IH]; intros k Hk.
  - destruct k as [|k']; [ lia | reflexivity ].
  - destruct k as [|k']; [ lia | ].
    change (lw0_binom (Datatypes.S n') (Datatypes.S k'))
      with (lw0_binom n' k' + lw0_binom n' (Datatypes.S k'))%nat.
    rewrite (IH k' ltac:(lia)), (IH (Datatypes.S k') ltac:(lia)).
    reflexivity.
Qed.

(* The sign factor (-1)^m over Z (self-built stand-in for the pending  *)
(* LW2Binom zsign; nat_rect-shaped Zpower_nat refuses simpl/unfold,    *)
(* so the sign is built by its own nat recursion -- same mathematics). *)
Fixpoint lw0_zsign (m : nat) : Z :=
  match m with
  | 0%nat => 1%Z
  | Datatypes.S m' => (- lw0_zsign m')%Z
  end.

Lemma lw0_zsign_step : forall m : nat,
  lw0_zsign (Datatypes.S m) = (- lw0_zsign m)%Z.
Proof. intros m. reflexivity. Qed.

(* The corrected lo closed form (errata formula, generations-pinned):  *)
(* z_lo = (-1)^(k-n) * C(n,k-n) * (k!/n!) * a^(2n-k) * b^(k-n), with   *)
(* the (k!/n!) factor carried by the division-free witness lw0_ratio   *)
(* and glued through the in-file Qmake bridge lw0_Qmake_mul.           *)
Definition lw0_z_lo (a b : Z) (n k : nat) : Q :=
  ((lw0_zsign (k - n) * Z.of_nat (lw0_binom n (k - n))
     * Zpower_nat a ((2 * n) - k) * Zpower_nat b (k - n)) # 1)%Q
  * ((Z.of_nat (lw0_ratio n k)) # 1)%Q.

Lemma lw0_z_lo_integer : forall (a b : Z) (n k : nat),
  sigT (fun w : Z => Qeq (lw0_z_lo a b n k) ((w # 1)%Q)).
Proof.
  intros a b n k.
  exists (lw0_zsign (k - n) * Z.of_nat (lw0_binom n (k - n))
          * Zpower_nat a ((2 * n) - k) * Zpower_nat b (k - n)
          * Z.of_nat (lw0_ratio n k))%Z.
  unfold lw0_z_lo.
  apply (lw0_Qmake_mul
          (lw0_zsign (k - n) * Z.of_nat (lw0_binom n (k - n))
            * Zpower_nat a ((2 * n) - k) * Zpower_nat b (k - n))
          (Z.of_nat (lw0_ratio n k))).
Qed.

(* The hi closed form: dual of the errata formula under k <- 2n-k,     *)
(* z_hi = (-1)^(n-k) * C(n,n-k) * ((2n-k)!/n!) * a^k * b^(n-k), again  *)
(* carrying the n! in the ratio witness lw0_ratio n (2n-k).  Shape     *)
(* note: the mandate text of z_hi was not delivered with this seat;    *)
(* this dual is built by the same craft and stands until the mandate   *)
(* original is verified.                                               *)
Definition lw0_z_hi (a b : Z) (n k : nat) : Q :=
  ((lw0_zsign (n - k) * Z.of_nat (lw0_binom n (n - k))
     * Zpower_nat a k * Zpower_nat b (n - k)) # 1)%Q
  * ((Z.of_nat (lw0_ratio n (2 * n - k))) # 1)%Q.

Lemma lw0_z_hi_integer : forall (a b : Z) (n k : nat), (k <= n)%nat ->
  sigT (fun w : Z => Qeq (lw0_z_hi a b n k) ((w # 1)%Q)).
Proof.
  intros a b n k Hk.
  exists (lw0_zsign (n - k) * Z.of_nat (lw0_binom n (n - k))
          * Zpower_nat a k * Zpower_nat b (n - k)
          * Z.of_nat (lw0_ratio n (2 * n - k)))%Z.
  unfold lw0_z_hi.
  apply (lw0_Qmake_mul
          (lw0_zsign (n - k) * Z.of_nat (lw0_binom n (n - k))
            * Zpower_nat a k * Zpower_nat b (n - k))
          (Z.of_nat (lw0_ratio n (2 * n - k)))).
Qed.

(* ================================================================== *)
(* K_integer 装配段（判定实录与三元组见件头注；本段注释只述数学）。     *)
(* 语句面口径：K 值＝F(0)+F(q) 的 Q 值；F(x)=Sum_j (-1)^j f^(2j)(x)    *)
(* （偶阶格 k=2j）。lo 支＝f^(2j)(0) 闭式 lw0_z_lo a b n (2j)          *)
(* （n<=2j 支，无前提绿件）；hi 支＝f^(2j)(q) 经对偶指标 2*(n-j) 的    *)
(* lw0_z_hi a b n（k<=n 前提由守卫给出）。2j<n 支真端点值为零，由      *)
(* 已绿件 lw0_niven_deriv_zero_0 覆盖（见 lw0_K_leg_else_zero）。      *)
(* 端点求值接口靶面：qpoly_eval (qpoly_deriv_iter k f) 0，桥           *)
(* lw0_eval_deriv_coef0（已绿），连接引理沿此立。                      *)
(* ================================================================== *)

(* --- Q 有限和与 sigT 整数见证闭包（K 装配基建） --- *)

Fixpoint lw0_qsum (g : nat -> Q) (m : nat) : Q :=
  match m with
  | 0%nat => g 0%nat
  | Datatypes.S m' => lw0_qsum g m' + g (Datatypes.S m')
  end.

(* sigT 见证对 Q 加法封闭：witness = (z1+z2)，桥 lw0_Qmake_plus。 *)
Lemma lw0_sigT_plus : forall v1 v2 : Q,
  sigT (fun w : Z => Qeq v1 ((w # 1)%Q)) ->
  sigT (fun w : Z => Qeq v2 ((w # 1)%Q)) ->
  sigT (fun w : Z => Qeq (v1 + v2) ((w # 1)%Q)).
Proof.
  intros v1 v2 [z1 Hz1] [z2 Hz2].
  exists (z1 + z2)%Z.
  assert (Hs : v1 + v2 == (z1 # 1)%Q + (z2 # 1)%Q)
    by (apply Qplus_comp; assumption).
  transitivity ((z1 # 1)%Q + (z2 # 1)%Q)%Q.
  - exact Hs.
  - apply lw0_Qmake_plus.
Qed.

(* sigT 见证对 (z#1) 型 Z 原子缩放封闭：witness = (u*z)，桥 lw0_Qmake_mul。 *)
Lemma lw0_sigT_Zscale : forall (u : Z) (v : Q),
  sigT (fun w : Z => Qeq v ((w # 1)%Q)) ->
  sigT (fun w : Z => Qeq ((u # 1)%Q * v) ((w # 1)%Q)).
Proof.
  intros u v [z Hz].
  exists (u * z)%Z.
  assert (Hm : (u # 1)%Q * v == (u # 1)%Q * (z # 1)%Q)
    by (apply Qmult_comp; [apply Qeq_refl | exact Hz]).
  transitivity ((u # 1)%Q * (z # 1)%Q)%Q.
  - exact Hm.
  - apply lw0_Qmake_mul.
Qed.

(* 有限和的 sigT 见证：逐项 witnessed 则和 witnessed。 *)
Lemma lw0_qsum_integer : forall (g : nat -> Q) (m : nat),
  (forall j : nat, sigT (fun w : Z => Qeq (g j) ((w # 1)%Q))) ->
  sigT (fun w : Z => Qeq (lw0_qsum g m) ((w # 1)%Q)).
Proof.
  intros g m.
  induction m as [|m' IH]; intros Hg.
  - exact (Hg 0%nat).
  - change (lw0_qsum g (Datatypes.S m'))
      with (lw0_qsum g m' + g (Datatypes.S m'))%Q.
    apply lw0_sigT_plus.
    + apply IH. exact Hg.
    + exact (Hg (Datatypes.S m')).
Qed.

(* --- K 值闭式拟形（三点钉死，见段首）与整数性主见证 --- *)

(* 第 j 项（偶阶格 k=2j）：(-1)^j · [lo 支 f^(2j)(0) + hi 支 f^(2j)(q)]， *)
(* n<=2j 守卫支内双支齐载；2j<n 支真值零（取用件见下）。                 *)
Definition lw0_K_leg (a b : Z) (n j : nat) : Q :=
  (lw0_zsign j # 1)%Q *
  (if Nat.leb n (2 * j)
   then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
   else (0 # 1)%Q).

Definition lw0_K (a b : Z) (n : nat) : Q :=
  lw0_qsum (lw0_K_leg a b n) n.

(* F(0) 支零值取用件：2j<n 支真端点值 == else 分支 (0#1)。挂已绿件      *)
(* lw0_niven_deriv_zero_0（deriv_iter 2j 在零点求值为零）。             *)
Lemma lw0_K_leg_else_zero : forall (q : Q) (b : Z) (n j : nat),
  (2 * j < n)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j) (lw0_niven_f_z q b n)) 0 == (0 # 1)%Q.
Proof.
  intros q b n j Hj.
  rewrite (lw0_niven_deriv_zero_0 q b n (2 * j) Hj).
  reflexivity.
Qed.

(* 单项见证：守卫双支各自装配（lo 腿无前提件；hi 腿 k<=n 前提由守卫出）。 *)
Lemma lw0_K_leg_integer : forall (a b : Z) (n j : nat),
  sigT (fun w : Z => Qeq (lw0_K_leg a b n j) ((w # 1)%Q)).
Proof.
  intros a b n j. unfold lw0_K_leg.
  destruct (Nat.leb n (2 * j)) eqn:Hg.
  - apply Nat.leb_le in Hg.
    change (if true then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
            else (0 # 1)%Q)
      with (lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j)))%Q.
    apply lw0_sigT_Zscale.
    apply lw0_sigT_plus.
    + exact (lw0_z_lo_integer a b n (2 * j)).
    + assert (Hhi : (2 * (n - j) <= n)%nat) by lia.
      exact (lw0_z_hi_integer a b n (2 * (n - j)) Hhi).
  - exists 0%Z.
    change (if false then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
            else (0 # 1)%Q)
      with ((0 # 1)%Q)%Q.
    transitivity (((lw0_zsign j * 0)%Z # 1)%Q).
    + apply lw0_Qmake_mul.
    + rewrite Z.mul_0_r. reflexivity.
Qed.

(* 整数性主见证：K 值＝F(0)+F(q) 的 Q 值的 sigT 惯形，                  *)
(* lo/hi 双支合成。                                                     *)
Lemma lw0_K_integer : forall (a b : Z) (n : nat),
  sigT (fun w : Z => Qeq (lw0_K a b n) ((w # 1)%Q)).
Proof.
  intros a b n. unfold lw0_K.
  apply lw0_qsum_integer.
  intros j. apply lw0_K_leg_integer.
Qed.


(* ================= §6 下界见证与无理性装配 ================= *)
(* 显式指标选取、矛盾见证前提带与无理性装配。 *)

(* ---------- 实常数对有理序的严格序 ---------- *)

(* real_lt (real_const x) (real_const y) 的 sigT 见证给出逐点 QltT eps (y-x)，
   与 QltT 0 eps 合取后经 Qlt_trans 与 Qlt_minus_iff 得 QltT x y。 *)
Lemma lw0_real_lt_const_Qlt : forall x y : Q,
  real_lt (real_const x) (real_const y) -> QltT x y.
Proof.
  intros x y H.
  destruct H as [eps [Heps [N HN]]].
  pose proof (HN N (NatLe_lift N N (Nat.le_refl N))) as Hlt.
  cbn [projT1 real_const] in Hlt.
  assert (Hpos : Qlt 0 (y - x)%Q).
  { apply (Qlt_trans 0 eps (y - x)%Q).
    - exact (QltT_to_Qlt 0 eps Heps).
    - exact (QltT_to_Qlt eps (y - x)%Q Hlt). }
  assert (Hxy : Qlt x y).
  { exact (proj2 (Qlt_minus_iff x y) Hpos). }
  exact (Qlt_to_QltT x y Hxy).
Qed.

(* ---------- 有理点处的端点值 ---------- *)

(* sin 端点值：sin(q) = 0 经 real_sin_eq_compat 自 real_pi_geom 点传输。 *)
Lemma lw0_sin_endpoint_transport : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  real_eq (cauchy_real_sin (real_const (a / b))) real_zero.
Proof.
  intros a b Hp.
  apply (real_eq_trans (cauchy_real_sin (real_const (a / b)))
                       (cauchy_real_sin real_pi_geom) real_zero).
  - apply real_sin_eq_compat. apply real_eq_sym. exact Hp.
  - exact pi_geom_sin_pi_zero.
Qed.

(* cos 端点值：cos(q) = -1 经 real_cos_eq_compat 自 real_pi_geom 点传输。 *)
Lemma lw0_cos_endpoint_transport : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  real_eq (cauchy_real_cos (real_const (a / b))) (real_const (-1)%Q).
Proof.
  intros a b Hp.
  apply (real_eq_trans (cauchy_real_cos (real_const (a / b)))
                       (cauchy_real_cos real_pi_geom) (real_const (-1)%Q)).
  - apply real_cos_eq_compat. apply real_eq_sym. exact Hp.
  - exact pi_geom_cos_pi_neg_one.
Qed.

(* 端点值链的 And 型合取壳（装配层供件）。 *)
Lemma lw0_endpoint_transport : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  And (real_eq (cauchy_real_sin (real_const (a / b))) real_zero)
      (real_eq (cauchy_real_cos (real_const (a / b))) (real_const (-1)%Q)).
Proof.
  intros a b Hp. split.
  - apply lw0_sin_endpoint_transport. exact Hp.
  - apply lw0_cos_endpoint_transport. exact Hp.
Qed.

(* ---------- 假想有理点的双岸界 ---------- *)

(* 由 Hp 与 pi 的双岸实层界（real_pi_geom_between）经换形件得 q = a/b 的
   双岸 Q 界 3 < q < 10/3：左岸经 real_lt_eq_lt，右岸经 real_eq_lt_lt。 *)
Lemma lw0_pi_asm_q_bounds : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  And (QltT 3 (a / b)) (QltT (a / b) (10 / 3)).
Proof.
  intros a b Hp.
  destruct real_pi_geom_between as [Hgt Hlt].
  split.
  - apply lw0_real_lt_const_Qlt.
    exact (real_lt_eq_lt (real_const 3) real_pi_geom
                         (real_const (a / b)) Hgt Hp).
  - apply lw0_real_lt_const_Qlt.
    exact (real_eq_lt_lt (real_const (a / b)) real_pi_geom
                         (real_const (10 / 3))
                         (real_eq_sym real_pi_geom (real_const (a / b)) Hp)
                         Hlt).
Qed.

(* ---------- Niven 多项式族 ---------- *)

(* 单项式 t^m 的低次在首系数表：t^0 = [1]，t^{m+1} = t^m * [0;1]。 *)
Fixpoint lw0_pi_mono (m : nat) : qpoly :=
  match m with
  | 0%nat => cons 1%Q nil
  | Datatypes.S m' => qpoly_mul (lw0_pi_mono m') (cons 0%Q (cons 1%Q nil))
  end.

Lemma lw0_pi_mono_eval : forall (m : nat) (t : Q),
  qpoly_eval (lw0_pi_mono m) t == q_pow t m.
Proof.
  intros m t. induction m as [| m IH].
  - cbn [lw0_pi_mono qpoly_eval q_pow]. ring.
  - cbn [lw0_pi_mono]. rewrite qpoly_eval_mul, IH.
    cbn [qpoly_eval q_pow]. ring.
Qed.

(* 二项式 (q - t)^n 的低次在首系数表：逐次乘入表 [q; -1]。 *)
Fixpoint lw0_pi_qminus_pow (q : Q) (n : nat) : qpoly :=
  match n with
  | 0%nat => cons 1%Q nil
  | Datatypes.S m =>
      qpoly_mul (lw0_pi_qminus_pow q m) (cons q (cons (-1)%Q nil))
  end.

Lemma lw0_pi_qminus_pow_eval : forall (q t : Q) (n : nat),
  qpoly_eval (lw0_pi_qminus_pow q n) t == q_pow (q - t) n.
Proof.
  intros q t n. induction n as [| n IH].
  - cbn [lw0_pi_qminus_pow qpoly_eval q_pow]. ring.
  - cbn [lw0_pi_qminus_pow]. rewrite qpoly_eval_mul, IH.
    cbn [qpoly_eval q_pow]. ring.
Qed.

(* Niven 缩放：f_n = (b^n / n!) * t^n * (q - t)^n 的多项式承载。 *)
Definition lw0_niven_f (q b : Q) (n : nat) : qpoly :=
  qpoly_scalar (q_pow b n / q_fact n)
    (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)).

(* 求值恒等式：eval(f_n, t) == b^n * t^n * (q - t)^n / n!。 *)
Lemma lw0_niven_f_eval : forall (q b t : Q) (n : nat),
  qpoly_eval (lw0_niven_f q b n) t ==
  q_pow b n * q_pow t n * q_pow (q - t) n / q_fact n.
Proof.
  intros q b t n.
  unfold lw0_niven_f.
  rewrite qpoly_eval_scalar, qpoly_eval_mul,
          lw0_pi_mono_eval, lw0_pi_qminus_pow_eval.
  unfold Qdiv. ring.
Qed.



(* ---------- 显式指标选取 ---------- *)

(* 显式 n 选取函数：给定有理 q = a/b 的分母信息 b（nat 面）与精度阶 k，输出
   分母信息 b（nat 面）与精度阶 k，输出
       lw0_n_select b k = 22 + 2 * max k b，
   即 n 对 b 与占优阈的显式 max 函数。数学含义：输出 n 恒为偶数形
   22 + 2k'（k' = max k b），故 n >= 22 恒入阶乘占优域，且 n >= 2b >= b，
   覆盖整数性 n >= b 选取（Niven 族 f_n 的分母整除核算所需的下界）。 *)
Definition lw0_n_select (b k : nat) : nat := (22 + 2 * Nat.max k b)%nat.

(* 规格一（整数性）：n >= b——分母整除核算的 nat 侧下界，经 NatLe_lift 落
   Set 层 NatLe。 *)
Lemma lw0_n_select_ge_b : forall b k : nat,
  NatLe b (lw0_n_select b k).
Proof.
  intros b k. apply NatLe_lift. unfold lw0_n_select. lia.
Qed.

(* 规格二（阶乘占优）：输出 n 上 (10/3)^n <= n!——组合推论偶族件
   lw0_pi_bound_dominated_even 在 k' = max k b 处的直实例化（n 的偶数形
   设计使奇偶分族免分支）。 *)
Lemma lw0_n_select_dominated : forall b k : nat,
  QleT' (q_pow (10 # 3) (lw0_n_select b k)) (q_fact (lw0_n_select b k)).
Proof.
  intros b k. unfold lw0_n_select.
  exact (lw0_pi_bound_dominated_even (Nat.max k b)).
Qed.

(* 规格三（任意 q 上界参用形）：0 <= q <= 10/3 时 q^n <= n!——幂单调件
   q_pow_mono 与规格二经 qleT'_trans 复合；q 的上界 (10#3) 由
   lw0_pi_asm_q_bounds 的右岸给出（见下方降形桥）。 *)
Lemma lw0_n_select_dominated_of_qle : forall (q : Q) (b k : nat),
  QleT' 0 q -> QleT' q (10 # 3) ->
  QleT' (q_pow q (lw0_n_select b k)) (q_fact (lw0_n_select b k)).
Proof.
  intros q b k H0q Hqu.
  apply (qleT'_trans (q_pow q (lw0_n_select b k))
                     (q_pow (10 # 3) (lw0_n_select b k))
                     (q_fact (lw0_n_select b k))).
  - apply Qle_to_QleT'.
    apply q_pow_mono.
    + exact (QleT'_to_Qle 0 q H0q).
    + exact (QleT'_to_Qle q (10 # 3) Hqu).
  - exact (lw0_n_select_dominated b k).
Qed.

(* 假设面 q 界降形桥：lw0_pi_asm_q_bounds 右岸 QltT (a/b) (10/3) 降到
   QleT' (a/b) (10/3)，供规格三在终装配面的前提就位。 *)
Lemma lw0_pi_asm_q_bounds_upper_QleT' : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  QleT' (a / b) (10 # 3).
Proof.
  intros a b Hp.
  destruct (lw0_pi_asm_q_bounds a b Hp) as [Hlo Hhi].
  apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hhi.
Qed.

(* 规格四（阶乘半数底幂下界的直实例化）：输出 n 上
   (n/2)^(n/2) <= n!——lw0_fact_lower_growth 在输出点 n 的直实例化，
   供整数性核算面取用。 *)
Lemma lw0_n_select_fact_lower : forall b k : nat,
  QleT' (q_pow (lw0_q_of_nat (Nat.div2 (lw0_n_select b k)))
               (Nat.div2 (lw0_n_select b k)))
        (q_fact (lw0_n_select b k)).
Proof.
  intros b k. exact (lw0_fact_lower_growth (lw0_n_select b k)).
Qed.

(* ---------- 有理常数点的逆向换形 ---------- *)

(* 逆向换形：正向件 lw0_real_lt_const_Qlt 的逆向对偶件——
   Q 层严格序 x < y 给出实层严格序 real_lt (real_const x) (real_const y)。
   构造：eps := (y - x) * (1/2)（由 x < y 知 0 < eps < y - x 严格夹位），
   N := 0；逐点目标经 cbn [projT1 real_const] 定点归约后即为 Q 层
   半分不等式。 *)
Lemma lw0_real_lt_const_Qlt_inv : forall x y : Q,
  QltT x y -> real_lt (real_const x) (real_const y).
Proof.
  intros x y Hxy.
  assert (Hpos : Qlt 0 (y - x)%Q).
  { exact (proj1 (Qlt_minus_iff x y) (QltT_to_Qlt x y Hxy)). }
  assert (Hhalf : Qlt 0 (1 # 2)) by (unfold Qlt; reflexivity).
  assert (Hepspos : Qlt 0 ((y - x) * (1 # 2))%Q).
  { pose proof (proj2 (Qmult_lt_r 0 (y - x) (1 # 2) Hhalf) Hpos) as Hraw.
    assert (Hzero : (0 * (1 # 2) == 0)%Q) by ring.
    rewrite Hzero in Hraw. exact Hraw. }
  assert (Hepslt : (Qlt ((y - x) * (1 # 2)) (y - x))%Q).
  { apply (proj2 (Qlt_minus_iff ((y - x) * (1 # 2)) (y - x))).
    assert (Hid : ((y - x) + - ((y - x) * (1 # 2))
                   == (y - x) * (1 # 2))%Q) by ring.
    rewrite Hid. exact Hepspos. }
  exists ((y - x) * (1 # 2))%Q.
  split.
  - apply Qlt_to_QltT. exact Hepspos.
  - exists 0%nat. intros n Hn.
    cbn [projT1 real_const].
    apply Qlt_to_QltT. exact Hepslt.
Qed.


(* ---------- 有理点前提带与度量投影闭式 ---------- *)

(* 接口面：度量投影 lic 语句组自库内 UpReqIrrationalCriterion 取用。 *)

(* 左岸传递件：q 双岸界左岸 3 < q 与 0 < 3 经 Q 序传递合成 0 < q，
   即 W 序列引理显式前提带的 QltT 0 q 支。 *)
Lemma lw0_pi_asm_q_pos : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  QltT 0 (a / b).
Proof.
  intros a b Hp.
  destruct (lw0_pi_asm_q_bounds a b Hp) as [Hlo _].
  apply Qlt_to_QltT.
  apply (Qlt_trans 0 3 (a / b)).
  - unfold Qlt. reflexivity.
  - exact (QltT_to_Qlt 3 (a / b) Hlo).
Qed.

(* 前提带产出件：W 序列引理的显式前提带——QltT 0 q 合取 QleT' q (10/3)，
   两支同出 Hp（q 双岸界的传递与右岸降形）。 *)
Lemma lw0_pi_asm_q_Wband : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  And (QltT 0 (a / b)) (QleT' (a / b) (10 # 3)).
Proof.
  intros a b Hp. split.
  - apply lw0_pi_asm_q_pos. exact Hp.
  - apply lw0_pi_asm_q_bounds_upper_QleT'. exact Hp.
Qed.

(* 规格零：显式 n 选取的输出恒不低于 2（22 + 2 * max 形自动满足），
   与既有规格一（n >= b）合成整数性核算的 n 双下界。 *)
Lemma lw0_n_select_ge_2 : forall b k : nat,
  NatLe 2 (lw0_n_select b k).
Proof.
  intros b k. apply NatLe_lift. unfold lw0_n_select. lia.
Qed.

(* ---------- 压制终跳：W_0 < 1 严格形 ---------- *)

(* 严格序右乘单调：QltT x y 且 0 < z 给出 QltT (x·z) (y·z)。 *)
Lemma lw0_qmult_lt_compat_r : forall x y z : Q,
  QltT x y -> QltT 0 z -> QltT (x * z) (y * z).
Proof.
  intros x y z Hxy Hz. apply Qlt_to_QltT.
  apply Qmult_lt_compat_r; apply QltT_to_Qlt; assumption.
Qed.

(* 压制数值核：对每个自然数 t，
   (5/9)^(22+2t)·(100/9)·(23+2t) < (24+2t)·(11+t)^(11+t)。
   t=0 为具体数值一次判定；步进：左岸乘 (25/81)·(25+2t)/(23+2t) < 1
   严格压缩，右岸两因子均不降，经严格序传递合成。 *)
Lemma lw0_pi_w0_lt1_core : forall t : nat,
  QltT (q_pow (5 # 9) (22 + 2 * t) * (100 # 9) * lw0_q_of_nat (23 + 2 * t))
       (lw0_q_of_nat (24 + 2 * t)
        * q_pow (lw0_q_of_nat (11 + t)) (11 + t)).
Proof.
  intro t. induction t as [| t IH].
  - apply Qlt_to_QltT. unfold Qlt, lw0_q_of_nat. vm_compute. reflexivity.
  - (* 步进：左岸严格压缩、右岸不降 *)
    assert (Hstep : QltT ((25 # 81) * lw0_q_of_nat (23 + 2 * Datatypes.S t))
                          (lw0_q_of_nat (23 + 2 * t))).
    { apply Qlt_to_QltT. unfold Qlt, lw0_q_of_nat. cbn [Qnum Qden Qmult Qinv]. lia. }
    assert (Ezpos : QltT 0 (q_pow (5 # 9) (22 + 2 * t) * (100 # 9))).
    { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      - apply QltT_to_Qlt. apply lw0_q_pow_pos. apply Qlt_to_QltT.
        unfold Qlt. reflexivity.
      - unfold Qlt. reflexivity. }
    assert (HL : QltT (q_pow (5 # 9) (22 + 2 * Datatypes.S t) * (100 # 9)
                       * lw0_q_of_nat (23 + 2 * Datatypes.S t))%Q
                      (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)
                       * lw0_q_of_nat (23 + 2 * t))%Q).
    { replace (22 + 2 * Datatypes.S t)%nat with ((22 + 2 * t) + 2)%nat by lia.
      apply Qlt_to_QltT.
      rewrite (lw0_q_pow_add (5 # 9) (22 + 2 * t) 2).
      assert (Epow2 : q_pow (5 # 9) 2 == (25 # 81)) by (cbn [q_pow]; reflexivity).
      rewrite Epow2.
      assert (Ering : (q_pow (5 # 9) (22 + 2 * t) * (25 # 81) * (100 # 9)
                       * lw0_q_of_nat (23 + 2 * Datatypes.S t))%Q
                      == ((25 # 81) * lw0_q_of_nat (23 + 2 * Datatypes.S t)
                          * (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)))%Q) by ring.
      rewrite Ering.
      assert (Ering2 : (lw0_q_of_nat (23 + 2 * t)
                        * (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)))%Q
                       == (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)
                           * lw0_q_of_nat (23 + 2 * t))%Q) by ring.
      rewrite <- Ering2.
      apply Qmult_lt_compat_r.
      + apply QltT_to_Qlt. exact Ezpos.
      + apply QltT_to_Qlt. exact Hstep. }
    assert (HR : QleT' (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)
                        * lw0_q_of_nat (23 + 2 * t))%Q
                       (lw0_q_of_nat (24 + 2 * Datatypes.S t)
                        * q_pow (lw0_q_of_nat (11 + Datatypes.S t))
                                (11 + Datatypes.S t))).
    { apply (qleT'_trans _ (lw0_q_of_nat (24 + 2 * t)
                            * q_pow (lw0_q_of_nat (11 + t)) (11 + t))%Q).
      - apply Qle_to_QleT'. apply (Qlt_le_weak _). apply QltT_to_Qlt. exact IH.
      - apply lw0_qcompat4.
        + apply lw0_q_of_nat_nonneg.
        + apply lw0_q_of_nat_le_mono. lia.
        + apply lw0_q_pow_nonnegT. apply lw0_q_of_nat_nonneg.
        + apply (qleT'_trans _
                  (q_pow (lw0_q_of_nat (11 + t))
                         (11 + Datatypes.S t))%Q).
          * replace (11 + Datatypes.S t)%nat
              with (Datatypes.S (11 + t))%nat by lia.
            apply lw0_q_pow_le_succ_pow.
            replace (11 + t)%nat with (Datatypes.S (10 + t))%nat by lia.
            apply lw0_q_of_nat_ge_one.
          * apply lw0_q_pow_mono_base.
            -- apply lw0_q_of_nat_nonneg.
            -- apply lw0_q_of_nat_le_mono. lia. }
    apply (lw0_ltT_leT_trans _ (q_pow (5 # 9) (22 + 2 * t) * (100 # 9)
                                 * lw0_q_of_nat (23 + 2 * t))).
    + exact HL.
    + exact HR.
Qed.

(* 终跳：基座联动下 W_0 < 1 严格形（分段交付备档取消，证明体补齐）。
   链路：前提 b ≤ d 沿基座联动入幂单调（b·(100/9) ≤ d·(100/9)
   ≤ (5/9)·(n+2)，沿 20d ≤ n）；n := lw0_n_select (10*d) k 沿输出点
   偶形实例化双砖——压制数值核（(5/9)^n·(100/9)·(n+1) 严格压
   (n+2)·(n/2)^(n/2)）与双 range 分裂下界（(2n+2)! ≥
   (n+2)^(n+1)·(n/2)^(n/2)）。分子岸经幂合并（lw0_q_pow_add 双拆
   (2n+2) 指数）与幂合流（lw0_q_pow_mult）等值为 (b·(100/9))^n 形，
   经幂单调（lw0_q_pow_mono_base）压入 (5/9)^n·(n+2)^n；数值核右岸乘
   (n+2)^n 后沿幂定义性展开与分裂岸合流（沿 Ebridge 等值方程于 Qlt
   假设位改写合流），除正因子 (2n+2)! 降 1 出严格形。 *)
Lemma lw0_pi_w0_lt1 : forall (b q : Q) (d k : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3) ->
  QleT' b (lw0_q_of_nat d) ->
  QltT (lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1.
Proof.
  intros b q d k Hb Hq0 Hqu Hbd.
  unfold lw0_n_select.
  remember (22 + 2 * Nat.max k (10 * d))%nat as n eqn:Hn.
  assert (Hge : (20 * d <= n)%nat) by lia.
  assert (HnumR : QleT' 0 (100 # 9)).
  { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. }
  assert (E100 : q_pow (10 # 3) 2 == (100 # 9)) by reflexivity.
  (* 砖一：压制数值核，沿输出点偶形实例化 *)
  pose proof (lw0_pi_w0_lt1_core (Nat.max k (10 * d))) as Hcore0.
  replace (22 + 2 * Nat.max k (10 * d))%nat with n%nat in Hcore0 by lia.
  replace (23 + 2 * Nat.max k (10 * d))%nat with (Datatypes.S n)%nat in Hcore0 by lia.
  replace (24 + 2 * Nat.max k (10 * d))%nat with (Datatypes.S (Datatypes.S n))%nat in Hcore0 by lia.
  (* 砖二：双 range 分裂下界，(2n+2)! 的 (n+2)^(n+1)·(n/2)^(n/2) 分裂岸 *)
  pose proof (lw0_qfact_split_lower (23 + 2 * Nat.max k (10 * d))) as Hsplit0.
  assert (Hdv : Nat.div2 (23 + 2 * Nat.max k (10 * d)) = (11 + Nat.max k (10 * d))%nat).
  { replace (23 + 2 * Nat.max k (10 * d))%nat
      with (Datatypes.S (2 * (11 + Nat.max k (10 * d)))) by lia.
    rewrite Nat.div2_succ_double. reflexivity. }
  rewrite Hdv in Hsplit0.
  replace (23 + 2 * Nat.max k (10 * d))%nat with (Datatypes.S n)%nat in Hsplit0 by lia.
  replace (2 * Datatypes.S n)%nat with (2 * n + 2)%nat in Hsplit0 by lia.
  (* 前提 b 上界沿基座联动：b·(100/9) ≤ (5/9)·(n+2) *)
  assert (Hmono : QleT' (q_pow (b * (100 # 9)) n)
                        (q_pow ((5 # 9) * lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)).
  { apply lw0_q_pow_mono_base.
    - apply lw0_qmul_le0T.
      + apply lw0_QltT_le. exact Hb.
      + exact HnumR.
    - apply (qleT'_trans _ (lw0_q_of_nat d * (100 # 9))%Q).
      + apply lw0_qcompat_r.
        * exact Hbd.
        * exact HnumR.
      + apply Qle_to_QleT'. unfold Qle, lw0_q_of_nat.
        cbn [Qnum Qden Qmult Qinv]. lia. }
  (* 分子岸等值：b^n·(10/3)^(2n+2) == (b·(100/9))^n·(100/9) *)
  assert (Eq1 : (q_pow b n * q_pow (10 # 3) (2 * n + 2) * lw0_q_of_nat (n + 1))%Q
                == (q_pow (b * (100 # 9)) n * (100 # 9) * lw0_q_of_nat (n + 1))%Q).
  { replace (2 * n + 2)%nat with (n + (n + 2))%nat by lia.
    rewrite (lw0_q_pow_add (10 # 3) n (n + 2)%nat).
    rewrite (lw0_q_pow_add (10 # 3) n 2%nat).
    rewrite E100.
    rewrite (Qmult_assoc (q_pow b n) (q_pow (10 # 3) n)
                         (q_pow (10 # 3) n * (100 # 9))).
    rewrite (lw0_q_pow_mult b (10 # 3) n).
    rewrite (Qmult_assoc (q_pow (b * (10 # 3)) n) (q_pow (10 # 3) n) (100 # 9)).
    rewrite (lw0_q_pow_mult (b * (10 # 3)) (10 # 3) n).
    assert (E9 : ((b * (10 # 3)) * (10 # 3))%Q == (b * (100 # 9))%Q) by ring.
    rewrite E9. reflexivity. }
  (* 数值核右岸幂合并等值：(5n/9)^n == (5/9)^n·(n+2)^n *)
  assert (Eq2 : (q_pow ((5 # 9) * lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                 * (100 # 9) * lw0_q_of_nat (n + 1))%Q
                == ((q_pow (5 # 9) n * (100 # 9)
                     * lw0_q_of_nat (Datatypes.S n))
                    * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)%Q).
  { replace (lw0_q_of_nat (Datatypes.S n)) with (lw0_q_of_nat (n + 1))%Q
      by (f_equal; lia).
    rewrite <- (lw0_q_pow_mult (5 # 9)
              (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n). ring. }
  (* 分子岸压制：Num ≤ 数值核左岸·(n+2)^n *)
  assert (Hnum : QleT' (q_pow b n * q_pow (10 # 3) (2 * n + 2)
                        * lw0_q_of_nat (n + 1))
                       ((q_pow (5 # 9) n * (100 # 9)
                         * lw0_q_of_nat (Datatypes.S n))
                        * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)).
  { apply (qleT'_trans _
            (q_pow (b * (100 # 9)) n * (100 # 9) * lw0_q_of_nat (n + 1))%Q).
    - apply qeq_leT'. exact Eq1.
    - apply (qleT'_trans _
              (q_pow ((5 # 9) * lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
               * (100 # 9) * lw0_q_of_nat (n + 1))%Q).
      + apply lw0_qcompat_r.
        * apply lw0_qcompat_r; [ exact Hmono | exact HnumR ].
        * apply lw0_q_of_nat_nonneg.
      + apply qeq_leT'. exact Eq2. }
  (* 严格桥：数值核右岸乘 (n+2)^n 后与分裂岸按定义性展开合流 *)
  assert (Hppos : QltT 0 (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)).
  { apply lw0_q_pow_pos. apply lw0_q_of_nat_lt0T. lia. }
  assert (Ebridge : ((lw0_q_of_nat (Datatypes.S (Datatypes.S n))
                      * q_pow (lw0_q_of_nat (11 + Nat.max k (10 * d)))
                              (11 + Nat.max k (10 * d)))
                     * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)%Q
                    == (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                              (Datatypes.S n)
                        * q_pow (lw0_q_of_nat (11 + Nat.max k (10 * d)))
                                (11 + Nat.max k (10 * d)))%Q).
  { assert (Epow : q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                   (Datatypes.S n)
                   == (lw0_q_of_nat (Datatypes.S (Datatypes.S n))
                       * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)%Q)
      by reflexivity.
    rewrite Epow. ring. }
  assert (Hcs : QltT ((q_pow (5 # 9) n * (100 # 9)
                       * lw0_q_of_nat (Datatypes.S n))
                      * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
                     (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) (Datatypes.S n)
                      * q_pow (lw0_q_of_nat (11 + Nat.max k (10 * d)))
                              (11 + Nat.max k (10 * d)))).
  { apply Qlt_to_QltT.
    assert (Hstep : Qlt ((q_pow (5 # 9) n * (100 # 9)
                          * lw0_q_of_nat (Datatypes.S n))
                         * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
                        ((lw0_q_of_nat (Datatypes.S (Datatypes.S n))
                          * q_pow (lw0_q_of_nat (11 + Nat.max k (10 * d)))
                                  (11 + Nat.max k (10 * d)))
                         * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)%Q).
    { apply QltT_to_Qlt.
      exact (lw0_qmult_lt_compat_r
               (q_pow (5 # 9) n * (100 # 9)
                * lw0_q_of_nat (Datatypes.S n))
               (lw0_q_of_nat (Datatypes.S (Datatypes.S n))
                * q_pow (lw0_q_of_nat (11 + Nat.max k (10 * d)))
                        (11 + Nat.max k (10 * d)))
               (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
               Hcore0 Hppos). }
    rewrite Ebridge in Hstep. exact Hstep. }
  assert (Hstrict : QltT ((q_pow (5 # 9) n * (100 # 9)
                           * lw0_q_of_nat (Datatypes.S n))
                          * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
                         (q_fact (2 * n + 2))).
  { exact (lw0_ltT_leT_trans
             ((q_pow (5 # 9) n * (100 # 9) * lw0_q_of_nat (Datatypes.S n))
              * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
             (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) (Datatypes.S n)
              * q_pow (lw0_q_of_nat (11 + Nat.max k (10 * d)))
                      (11 + Nat.max k (10 * d)))
             (q_fact (2 * n + 2)) Hcs Hsplit0). }
  assert (Hlt2 : QltT (q_pow b n * q_pow (10 # 3) (2 * n + 2)
                       * lw0_q_of_nat (n + 1))
                      (q_fact (2 * n + 2))).
  { exact (lw0_leT'_ltT_trans
             (q_pow b n * q_pow (10 # 3) (2 * n + 2) * lw0_q_of_nat (n + 1))
             ((q_pow (5 # 9) n * (100 # 9) * lw0_q_of_nat (Datatypes.S n))
              * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
             (q_fact (2 * n + 2)) Hnum Hstrict). }
  (* 严格形出口：除正因子降 1，Hup 上界岸回接 *)
  assert (Hzpos : QltT 0 (q_fact (2 * n + 2))).
  { apply Qlt_to_QltT. apply q_fact_pos. }
  assert (Hfin : QltT (q_pow b n * q_pow (10 # 3) (2 * n + 2)
                       * lw0_q_of_nat (n + 1))
                      (1 * q_fact (2 * n + 2))%Q).
  { apply Qlt_to_QltT.
    pose proof (QltT_to_Qlt _ _ Hlt2) as Hstep.
    assert (E1f : (1 * q_fact (2 * n + 2))%Q == q_fact (2 * n + 2)) by ring.
    rewrite <- E1f in Hstep. exact Hstep. }
  pose proof (lw0_div_lt (q_pow b n * q_pow (10 # 3) (2 * n + 2)
                          * lw0_q_of_nat (n + 1))
                         1%Q (q_fact (2 * n + 2)) Hzpos Hfin) as Hdiv.
  exact (lw0_leT'_ltT_trans (lw0_Wb b q n 0)
           (q_pow b n * q_pow (10 # 3) (2 * n + 2) * lw0_q_of_nat (n + 1)
            / q_fact (2 * n + 2))%Q 1%Q
           (lw0_Wb0_upper b q n (lw0_QltT_le b Hb) Hb Hq0 Hqu) Hdiv).
Qed.

(* apartness 出口壳：零包装三跳链——度量投影、积投影、半周余弦
   投影逐跳换算，落 Q 面 Qabs (2 * cos_zero_seq n - q) 形，供 apartness
   出口的显式余量见证面取用。 *)
Lemma lw0_pi_geom_metric_proj : forall (q : Q) (n : nat),
  projT1 (real_metric real_pi_geom (real_const q)) n ==
  Qabs.Qabs ((2 * cos_zero_seq n - q)%Q).
Proof.
  intros q n.
  unfold real_pi_geom.
  rewrite (lic_metric_proj (real_mult (real_const 2) cos_pi_half) q n).
  rewrite (real_mult_proj (real_const 2) cos_pi_half n).
  cbn [projT1 real_const].
  rewrite cos_pi_half_proj.
  reflexivity.
Qed.


(* 交错和上界的显式压制与无理性矛盾见证的装配面。 *)

(* ================= §6 后段 终装配面 ================= *)

(* 装配态记录：七步矛盾链的步 1（q 双岸界带 lw0_pi_asm_q_Wband）、步 2
   （f_n 族与显式指标 lw0_n_select 系）、步 3＋步 4（W 序列实层双岸界，
   本段合成件 lw0_pi_chain_L_cauchy／lw0_pi_chain_L_bounds）、步 5（整数
   见证 lw0_K_integer，sigT (z#1) 形，§5 段在件）的在盘供形齐备；步 6
   双判定闭闸（lw0_pi_contra_gate）与步 7 apartness 出口
   （lw0_pi_irrational_exit）以真语句在件。主语句 lw0_pi_irrational 的
   陈述形逐字备档于段尾：其证明体差分析性等值层供件——W 序列值与 K 值
   的实层等值连接语句（S07 增量面，名 lw0_K_leg_connect，形
   real_eq (L(f_n)) (real_const K)）未在盘；conn 系九名已于本段段头
   （LW0Integrality2 1072 版连接块逐字入件）。等值层与压制终跳
   （W_0<1 严格形）齐后按备档链路一段填装即闭合。 *)

(* ---------- 连接引理块出处注：本块取自 LW0Integrality2.v 1072 行版
   （md5 f969ffc898a3e15cf4cb9750b6dab8c1）934–1072 行整段，逐字拷贝、
   零语句面改写；依赖面（bpa_binom/q_pow/q_fact/lw0_ratio/lw0_fact_ratio/
   lw0_binom/lw0_qfact_Z/lw0_zsign/lw0_Qmake_plus/lw0_eval_deriv_iter_scalar/
   lw0_eval_deriv_coef0/lw0_coef_mul_mono_ge/lw0_coef_qminus_pow）由本件
   §1/§4/§5 段与 Require 面在件供齐；Powpos 等九名经 grep 实测零碰撞。
   入位裁决：入 §6 后段段头（后段段头入位），§5 已绿段零改动。 ---------- *)

(* ================================================================== *)
(* Connection block: endpoint evaluations of the Niven polynomial meet *)
(* the lo/hi witness closed forms.  With q := (a # Z.pos b) the scaled *)
(* polynomial lw0_niven_f_z q b n is (1/n!) t^n (a - b*t)^n, whose     *)
(* k-th derivative at 0 (k >= n) equals the lo witness z_lo a b n k;   *)
(* at even order the q-endpoint value identifies with the 0-endpoint   *)
(* value (self-reciprocity of t^n (q-t)^n), and the dual-index witness *)
(* z_hi a b n (2*(n-j)) is the definitional re-indexing of z_lo.       *)
(* Division-free craft: the factorial quotient rides lw0_ratio, powers *)
(* glue through Qmake atoms, the positive power mirror is Powpos.      *)
(* ================================================================== *)

Fixpoint Powpos (p : positive) (m : nat) : positive :=
  match m with
  | 0%nat => 1%positive
  | Datatypes.S m' => p * Powpos p m'
  end.

Lemma lw0_posnat_zeq : forall m : nat, (1 <= m)%nat ->
  Zpos (Pos.of_nat m) = Z.of_nat m.
Proof.
  intros m Hm. destruct m as [|m']; [ exfalso; lia | ].
  change (Z.of_nat (Datatypes.S m')) with (Z.pos (Pos.of_succ_nat m')).
  rewrite <- Pos.of_nat_succ.
  reflexivity.
Qed.

Lemma lw0_zpower_nat_add : forall (z : Z) (m n : nat),
  Zpower_nat z (m + n) = (Zpower_nat z m * Zpower_nat z n)%Z.
Proof.
  intros z m n. induction n as [|n IH].
  - rewrite Nat.add_0_r, Z.mul_1_r. reflexivity.
  - replace (m + Datatypes.S n)%nat with (Datatypes.S (m + n))%nat by lia.
    rewrite Zpower_nat_succ_r, IH, Zpower_nat_succ_r. ring.
Qed.

Lemma lw0_zpos_pospow : forall (p : positive) (m : nat),
  Zpos (Powpos p m) = Zpower_nat (Zpos p) m.
Proof.
  intros p m. induction m as [|m IH].
  - reflexivity.
  - change (Powpos p (Datatypes.S m)) with (p * Powpos p m)%positive.
    rewrite Pos2Z.inj_mul, IH, Zpower_nat_succ_r. reflexivity.
Qed.

Lemma lw0_q_pow_qmake : forall (x : Z) (p : positive) (m : nat),
  q_pow ((x # p)%Q) m == ((Zpower_nat x m) # (Powpos p m))%Q.
Proof.
  intros x p m. induction m as [|m IH].
  - reflexivity.
  - change (q_pow (x # p)%Q (Datatypes.S m)) with ((x # p)%Q * q_pow (x # p)%Q m).
    change (Zpower_nat x (Datatypes.S m)) with (x * Zpower_nat x m)%Z.
    change (Powpos p (Datatypes.S m)) with (p * Powpos p m)%positive.
    rewrite IH. reflexivity.
Qed.

Lemma lw0_q_pow_m1 : forall m : nat, q_pow (-1)%Q m == ((lw0_zsign m) # 1)%Q.
Proof.
  intros m. induction m as [|m IH].
  - reflexivity.
  - change (q_pow (-1)%Q (Datatypes.S m)) with ((-1)%Q * q_pow (-1)%Q m).
    change (lw0_zsign (Datatypes.S m)) with (- lw0_zsign m)%Z.
    rewrite IH.
    replace ((-1)%Q * ((lw0_zsign m) # 1)%Q)
      with (((-1 * lw0_zsign m)%Z # 1)%Q) by reflexivity.
    replace (-1 * lw0_zsign m)%Z with (- lw0_zsign m)%Z by ring.
    reflexivity.
Qed.

Lemma lw0_bpa_binom_eq : forall n k : nat,
  bpa_binom n k == (Z.of_nat (lw0_binom n k) # 1)%Q.
Proof.
  intros n. induction n as [|n IH]; intros k.
  - destruct k as [|k].
    + reflexivity.
    + reflexivity.
  - destruct k as [|k].
    + reflexivity.
    + change (bpa_binom (Datatypes.S n) (Datatypes.S k))
        with (bpa_binom n k + bpa_binom n (Datatypes.S k))%Q.
      change (lw0_binom (Datatypes.S n) (Datatypes.S k))
        with (lw0_binom n k + lw0_binom n (Datatypes.S k))%nat.
      rewrite (IH k), (IH (Datatypes.S k)).
      rewrite Nat2Z.inj_add.
      apply lw0_Qmake_plus.
Qed.

Lemma lw0_conn_lo : forall (a : Z) (b : positive) (n k : nat), (n <= k)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0
  == lw0_z_lo a (Zpos b) n k.
Proof.
  intros a b n k Hk.
  assert (Hfn : (1 <= fact n)%nat) by (pose proof (fact_neq_0 n); lia).
  unfold lw0_niven_f_z.
  rewrite lw0_eval_deriv_iter_scalar.
  rewrite lw0_eval_deriv_coef0.
  rewrite (lw0_coef_mul_mono_ge n k (lw0_qminus_pow (a # b)%Q n) Hk).
  rewrite (lw0_coef_qminus_pow n (a # b)%Q (k - n)).
  replace (n - (k - n))%nat with (2 * n - k)%nat by lia.
  rewrite (lw0_bpa_binom_eq n (k - n)).
  rewrite lw0_qfact_Z.
  rewrite (lw0_q_pow_m1 (k - n)).
  rewrite (lw0_q_pow_qmake a b (2 * n - k)).
  unfold lw0_z_lo.
  destruct (Nat.leb (k - n) n) eqn:Hb2.
  - apply Nat.leb_le in Hb2.
    assert (Hf : Z.of_nat (fact k) = (Z.of_nat (fact n) * Z.of_nat (lw0_ratio n k))%Z).
    { rewrite <- Nat2Z.inj_mul. f_equal. exact (lw0_fact_ratio k n Hk). }
    assert (Hpow : (Zpower_nat (Zpos b) (k - n) * Zpower_nat (Zpos b) (2 * n - k))%Z
                   = Zpower_nat (Zpos b) n).
    { rewrite <- lw0_zpower_nat_add. f_equal. lia. }
    replace (Zpower_nat (Zpos b) n)
      with (Zpower_nat (Zpos b) (k - n) * Zpower_nat (Zpos b) (2 * n - k))%Z by exact Hpow.
    unfold Qeq, Qeq_bool. simpl.
    rewrite Pos2Z.inj_mul, (lw0_posnat_zeq (fact n) Hfn),
            lw0_zpos_pospow, Hf.
    ring.
  - apply Nat.leb_gt in Hb2.
    assert (H0 : lw0_binom n (k - n) = 0%nat) by (apply lw0_binom_out; exact Hb2).
    rewrite H0. unfold Qeq, Qeq_bool. simpl.
    first [ reflexivity | ring ].
Qed.

Lemma lw0_conn_hi : forall (a : Z) (b : positive) (n j : nat),
  (n <= 2 * j)%nat -> (j <= n)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j) (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0
  == lw0_z_hi a (Zpos b) n (2 * (n - j)).
Proof.
  intros a b n j H1 H2.
  rewrite (lw0_conn_lo a b n (2 * j) H1).
  unfold lw0_z_lo, lw0_z_hi.
  replace (2 * j - n)%nat with (n - (2 * (n - j)))%nat by lia.
  replace (2 * n - 2 * j)%nat with (2 * (n - j))%nat by lia.
  replace (2 * j)%nat with (2 * n - (2 * (n - j)))%nat by lia.
  reflexivity.
Qed.

Print Assumptions lw0_conn_lo.
Print Assumptions lw0_conn_hi.

(* ---------- 实层等值传递小壳（主语句适配件） ---------- *)

(* 等值左岸传递：R == S 时 R < T 传至 S < T。构造：见证取 eps·(1/2)
   （Qdiv 免入项，lw0_mul_lt_one 供半分严格界），等值面自带指标下界与
   原下界取 max，逐点经 Qabs_Qle_condition 降 Q 面后加法相容件合拢。 *)
Lemma lw0_real_lt_eq_transport_l : forall R S T : Real,
  real_eq R S -> real_lt R T -> real_lt S T.
Proof.
  intros R S T Hreq Hlt.
  destruct Hlt as [eps [Heps [N HN]]].
  assert (HhalfL : Qlt (eps * (1 # 2)) eps).
  { apply (lw0_mul_lt_one eps (1 # 2)).
    - exact (QltT_to_Qlt 0 eps Heps).
    - unfold Qlt. simpl. lia. }
  assert (HhalfT : QltT 0 (eps * (1 # 2))).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt 0 eps Heps).
    - unfold Qlt. simpl. lia. }
  destruct (Hreq (eps * (1 # 2))%Q HhalfT) as [N' HN'].
  exists (eps * (1 # 2))%Q. split.
  - exact HhalfT.
  - exists (Nat.max N N'). intros n Hn.
    assert (Ha : NatLe N n).
    { apply NatLe_lift. eapply Nat.le_trans;
        [ apply Nat.le_max_l | apply NatLe_drop; exact Hn ]. }
    assert (Hb : NatLe N' n).
    { apply NatLe_lift. eapply Nat.le_trans;
        [ apply Nat.le_max_r | apply NatLe_drop; exact Hn ]. }
    assert (H1 : Qlt eps (projT1 T n - projT1 R n)%Q)
      by (exact (QltT_to_Qlt _ _ (HN n Ha))).
    assert (H2 : Qle (- (eps * (1 # 2))) (projT1 R n - projT1 S n)%Q).
    { destruct (proj1 (Qabs_Qle_condition (projT1 R n - projT1 S n)
                         (eps * (1 # 2))%Q)
                 (Qlt_le_weak (Qabs (projT1 R n - projT1 S n))
                    (eps * (1 # 2))%Q (QltT_to_Qlt _ _ (HN' n Hb)))) as [Hlo _].
      exact Hlo. }
    apply Qlt_to_QltT.
    assert (Hmain : Qlt (eps + (- (eps * (1 # 2)))%Q)
                        ((projT1 T n - projT1 R n) + (projT1 R n - projT1 S n))%Q).
    { apply (Qplus_lt_le_compat eps (projT1 T n - projT1 R n)
               (- (eps * (1 # 2))) (projT1 R n - projT1 S n)).
      - exact H1.
      - exact H2. }
    assert (Hid1 : (eps * (1 # 2) == eps + (- (eps * (1 # 2))))%Q) by ring.
    assert (Hid2 : ((projT1 T n - projT1 R n) + (projT1 R n - projT1 S n)
                    == (projT1 T n - projT1 S n))%Q) by ring.
    rewrite Hid1. rewrite <- Hid2. exact Hmain.
Qed.

(* 等值右岸传递：R == S 时 T < R 传至 T < S。构造同左岸件对称形。 *)
Lemma lw0_real_lt_eq_transport_r : forall R S T : Real,
  real_eq R S -> real_lt T R -> real_lt T S.
Proof.
  intros R S T Hreq Hlt.
  destruct Hlt as [eps [Heps [N HN]]].
  assert (HhalfL : Qlt (eps * (1 # 2)) eps).
  { apply (lw0_mul_lt_one eps (1 # 2)).
    - exact (QltT_to_Qlt 0 eps Heps).
    - unfold Qlt. simpl. lia. }
  assert (HhalfT : QltT 0 (eps * (1 # 2))).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt 0 eps Heps).
    - unfold Qlt. simpl. lia. }
  destruct (Hreq (eps * (1 # 2))%Q HhalfT) as [N' HN'].
  exists (eps * (1 # 2))%Q. split.
  - exact HhalfT.
  - exists (Nat.max N N'). intros n Hn.
    assert (Ha : NatLe N n).
    { apply NatLe_lift. eapply Nat.le_trans;
        [ apply Nat.le_max_l | apply NatLe_drop; exact Hn ]. }
    assert (Hb : NatLe N' n).
    { apply NatLe_lift. eapply Nat.le_trans;
        [ apply Nat.le_max_r | apply NatLe_drop; exact Hn ]. }
    assert (H1 : Qlt eps (projT1 R n - projT1 T n)%Q)
      by (exact (QltT_to_Qlt _ _ (HN n Ha))).
    assert (H2 : Qle (projT1 R n - projT1 S n)%Q (eps * (1 # 2))).
    { destruct (proj1 (Qabs_Qle_condition (projT1 R n - projT1 S n)
                         (eps * (1 # 2))%Q)
                 (Qlt_le_weak (Qabs (projT1 R n - projT1 S n))
                    (eps * (1 # 2))%Q (QltT_to_Qlt _ _ (HN' n Hb)))) as [_ Hhi].
      exact Hhi. }
    apply Qlt_to_QltT.
    assert (Hmain : Qlt (eps + (- (eps * (1 # 2)))%Q)
                        ((projT1 R n - projT1 T n) + (projT1 S n - projT1 R n))%Q).
    { assert (Hopple : Qle (- (eps * (1 # 2))) (projT1 S n - projT1 R n)).
      { assert (Hopp0 : Qle (- (eps * (1 # 2)))
                          (- (projT1 R n - projT1 S n)))
          by exact (Qopp_le_compat (projT1 R n - projT1 S n)
                      (eps * (1 # 2)) H2).
        assert (Hswap : (- (projT1 R n - projT1 S n)
                         == (projT1 S n - projT1 R n))%Q) by ring.
        rewrite Hswap in Hopp0. exact Hopp0. }
      exact (Qplus_lt_le_compat eps (projT1 R n - projT1 T n)
               (- (eps * (1 # 2))) (projT1 S n - projT1 R n) H1 Hopple). }
    assert (Hid1 : (eps * (1 # 2) == eps + (- (eps * (1 # 2))))%Q) by ring.
    assert (Hid2 : ((projT1 R n - projT1 T n) + (projT1 S n - projT1 R n)
                    == (projT1 S n - projT1 T n))%Q) by ring.
    rewrite Hid1. rewrite <- Hid2. exact Hmain.
Qed.

(* ---------- 步 3＋步 4 合成：显式指标下的 W 序列柯西面与实层双岸界 ---------- *)

(* W 序列交错和在显式指标 lw0_n_select d k 下的柯西面。 *)
Lemma lw0_pi_chain_L_cauchy : forall (B q : Q) (d k : nat),
  QltT 0 B -> QltT 0 q -> QleT' q (10 # 3) ->
  cauchy (fun m : nat => altsum (lw0_Wb B q (lw0_n_select d k)) m).
Proof.
  intros B q d k Hb Hq Hq103.
  apply lw0_Wb_altseq_cauchy;
    [ exact Hb | exact Hq | exact Hq103 | unfold lw0_n_select; lia ].
Qed.

(* 步 3＋步 4 双岸界：0 < L(f_n) 且 L(f_n) < W_0（实层 sigT 见证形）。 *)
Lemma lw0_pi_chain_L_bounds : forall (B q : Q) (d k : nat)
                             (Hc : cauchy (fun m : nat => altsum (lw0_Wb B q (lw0_n_select d k)) m)),
  QltT 0 B -> QltT 0 q -> QleT' q (10 # 3) ->
  And (real_lt real_zero (lw0_L_of_seq (lw0_Wb B q (lw0_n_select d k)) Hc))
      (real_lt (lw0_L_of_seq (lw0_Wb B q (lw0_n_select d k)) Hc)
               (real_const (lw0_Wb B q (lw0_n_select d k) 0))).
Proof.
  intros B q d k Hc Hb Hq Hq103. split.
  - apply lw0_L_f_n_pos;
      [ exact Hb | exact Hq | exact Hq103 | unfold lw0_n_select; lia ].
  - apply lw0_L_f_n_upper;
      [ exact Hb | exact Hq | exact Hq103 | unfold lw0_n_select; lia ].
Qed.

(* ---------- 步 6：整数序＋ℚ 序双判定闭闸 ---------- *)

(* v 严格夹于 0 与 1 之间且 v 取 (z#1) 整数承载：z 的三分判定（零／负／
   正）逐支落 Id false true。零支与负支由 QltT 0 v 的逐点可判定字面归约
   反证；正支由 1 ≤ (z#1) 与 (z#1) < 1 经 Q 序传递得 QltT 1 1 反证。 *)
Lemma lw0_pi_contra_gate : forall (v : Q) (z : Z),
  QltT 0 v -> QltT v 1 -> Qeq v ((z # 1)%Q) -> Id false true.
Proof.
  intros v z Hv0 Hv1 Hz.
  destruct z as [| p | p].
  - assert (Hc : (0 ?= v)%Q = (0 ?= (0 # 1))%Q).
    { exact (Qcompare_comp 0 0 (Qeq_refl 0) v (0 # 1) Hz). }
    unfold QltT, Qlt_bool in Hv0. rewrite Hc in Hv0. cbn in Hv0. inversion Hv0.
  - assert (Hc : ((Z.pos p # 1) ?= 1)%Q = (v ?= 1)%Q).
    { exact (Qcompare_comp (Z.pos p # 1) v (Qeq_sym v (Z.pos p # 1) Hz) 1 1 (Qeq_refl 1)). }
    assert (Hge : QleT' 1 ((Z.pos p) # 1)%Q).
    { unfold QleT'. destruct p; reflexivity. }
    unfold QltT, Qlt_bool in Hv1. rewrite <- Hc in Hv1.
    assert (Hbad : QltT 1 1).
    { apply (lw0_leT'_ltT_trans 1 ((Z.pos p) # 1) 1); assumption. }
    unfold QltT, Qlt_bool in Hbad. cbn in Hbad. inversion Hbad.
  - assert (Hc : (0 ?= v)%Q = (0 ?= (Z.neg p # 1))%Q).
    { exact (Qcompare_comp 0 0 (Qeq_refl 0) v (Z.neg p # 1) Hz). }
    unfold QltT, Qlt_bool in Hv0. rewrite Hc in Hv0. cbn in Hv0. inversion Hv0.
Qed.

(* ---------- 步 7：apartness 出口（荒谬大消去） ---------- *)

(* Id false true 消去入任意 Set 目标；出口见证取 c := 1 的显式正值形。 *)
Lemma lw0_pi_irrational_exit : forall a b : Q,
  Id false true ->
  sigT (fun c : Q => And (QltT 0 c)
          (real_lt (real_const c)
             (real_metric real_pi_geom (real_const (a / b))))).
Proof.
  intros a b Habs. inversion Habs.
Qed.

(* ================= §6 末段 ② K 连接供件面 ================= *)

(* [核验裁定] real_eq 取形核实：S02_CauchyComplete
   L399 real_eq (x y : Real) : Set := forall eps : Q, QltT 0 eps ->
   sigT (fun N : nat => forall n : nat, NatLe N n ->
     QltT (Qabs (projT1 x n - projT1 y n)) eps)。即逐点 eps-差见证形：
   形 2 的处方＝尾项估计（|altsum W n - c| < eps, n >= N），非整段恒等。
   换算链（钉死）：填装面 b q : Q 实例化为 a' := Qnum q, b' := Qden q
   （b' : positive 正合 conn 系参型），(a' # b')%Q == q 由 Qmake 规范形
   直出；K 闭式 := lw0_K a' b' n_sel，n_sel := lw0_n_select (10*d) k。
   【反例裁决】形 2 粗配对 real_eq (L(f_n)) (real_const (lw0_K a' b' n_sel))
   以 n := 2、q := b := 1 实算为假：conn_lo 已证 z_lo ＝ f^(k)(0) 闭式
   （f(t)=t^2(1-t)^2/2 实算 f''(0)=1=z_lo(2)、f''''(0)=12=z_lo(4)，K :=
   lw0_qsum = -(1+1) + (12+12) = 22），而 altsum (lw0_Wb 1 1 2) 极限实算
   1/240 - 1/4032 + 1/172800 - ... 约 0.00392，异于 22——K 闭式承载
   (2j)!/n! 阶乘增长、Wb 项承载 (2n+2j+2)! 阶乘压制，两量不同标度，
   正典等值面必须携带显式归一化因子；该因子连同 Wb 项级 IBP 望远镜恒等
   全盘无备档、无在盘证明（_tlw113/156 审计同判「不同源、分析性事实」）。
   故 ② 供件形 2 系假语句不予交付；交付以下两件已证桥接引理（对应半桥＋
   real_eq 处方蒸馏件），归一化因子钉定另立后件。禁以粗配对填装
   主语句。 *)

(* 对应半桥：z_lo 与 z_hi 在偶阶格逐点等值（conn_lo/conn_hi 直推）。 *)
Lemma lw0_z_lo_hi_mirror : forall (a : Z) (b : positive) (n j : nat),
  (n <= 2 * j)%nat -> (j <= n)%nat ->
  lw0_z_lo a (Zpos b) n (2 * j) == lw0_z_hi a (Zpos b) n (2 * (n - j)).
Proof.
  intros a b n j H1 H2.
  rewrite <- (lw0_conn_hi a b n j H1 H2).
  apply Qeq_sym. apply lw0_conn_lo. exact H1.
Qed.

(* real_eq 处方蒸馏件（形 2 的 Real 层完成形）：交错和尾项估计一步升
   real_eq (L(W)) (real_const c)。逐点 eps-差见证形（S02 L399 取形）
   直拆：见证 N 照搬尾项估计的 N，逐点经投影转换化简合拢。 *)
Lemma lw0_real_eq_const_tail : forall (W : nat -> Q) (c : Q)
                             (Hc : cauchy (fun m : nat => altsum W m)),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall n : nat, NatLe N n ->
       QltT (Qabs (altsum W n - c)) eps)) ->
  real_eq (lw0_L_of_seq W Hc) (real_const c).
Proof.
  intros W c Hc Htail eps Heps.
  destruct (Htail eps Heps) as [N HN].
  exists N. intros n Hn.
  change (projT1 (lw0_L_of_seq W Hc) n) with (altsum W n).
  change (projT1 (real_const c) n) with c.
  exact (HN n Hn).
Qed.

Print Assumptions lw0_z_lo_hi_mirror.
Print Assumptions lw0_real_eq_const_tail.

(* ================= §6 末段 ② 供件二段施工面（连接桥正形） ================= *)

(* [航向正形，沿调度数学航向第 2 条] 受界对象重新对准 conn
   块同一 f 的 IBP 望远镜：L 对象取望远镜项序列 lw0_Ktel_seq——第 j 项＝
   conn 块同一闭式 lw0_z_lo a b n (2j)＋lw0_z_hi a b n (2(n−j)) 的无符号支
   （n≤2j 守卫同 lw0_K_leg，外加 j≤n 截断），与 conn 块同源同标度（项即
   f^(2j) 端点值闭式本身）。Q 层望远镜恒等：altsum Ktel (S i) == lw0_qsum
   lw0_K_leg i（i≤n；altsum 的 (−1)^j 交替恰与 K_leg 的 zsign j 逐项相消，
   符号引理 lw0_alt_zsign），i:=n 时右岸即 lw0_K（定义形）。尾截断后序列恒定，
   经在件蒸馏件 lw0_real_eq_const_tail 一步升形为 real_eq。数值判据
   （实测于 (a,b,n)=(1,1,2)）：altsum Ktel 3 == lw0_K 1 1 2 == 22
   （vm_compute 逐字闭合，见 lw0_Ktel_num22），22 vs 22 无 0.0039 型错配。
   [响亮余量备档] Wb 序列（sin 级数逐项 Beta 式，0<L<W_0 界面向已绿
   lw0_pi_chain_L_bounds）与 Ktel 序列在 π 条件
   real_eq real_pi_geom (real_const q)（q=a/b；经典内容 I(q)=F(0)−cos q·F(q)
   +sin q·F'(q)，sin π=0∧cos π=−1 时 =F(0)+F(π)=K；在件资产
   pi_geom_sin_pi_zero／pi_geom_cos_pi_neg_one／lw0_F_plus_deriv2）下的实层
   传输语句为 ② 剩余缺口，此处不超配。 *)

(* 符号桥：lw0_alt 与 lw0_zsign 在 Q 层同值（望远镜交替与 K_leg 符号
   逐项相消的桥）。 *)
Lemma lw0_alt_zsign : forall j : nat, lw0_alt j == (lw0_zsign j # 1)%Q.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - rewrite lw0_alt_opp. rewrite IH. rewrite lw0_zsign_step. reflexivity.
Qed.

(* 奇偶值件：lw0_alt 在偶/奇足标的字面值（步进沿 lw0_alt_opp；联合归纳
   绕开 destruct 对归纳假设前提的代换）。 *)
Lemma lw0_alt_parity : forall m : nat,
  (Nat.even m = true -> lw0_alt m == 1%Q) /\
  (Nat.even m = false -> lw0_alt m == (-1)%Q).
Proof.
  induction m as [|m [IH1 IH2]].
  - split; intro He.
    + reflexivity.
    + cbn in He. discriminate He.
  - split; intro He.
    + rewrite Nat.even_succ in He. rewrite <- Nat.negb_even in He.
      destruct (Nat.even m) eqn:Em; cbn [negb] in He.
      * discriminate He.
      * rewrite lw0_alt_opp. rewrite (IH2 eq_refl). reflexivity.
    + rewrite Nat.even_succ in He. rewrite <- Nat.negb_even in He.
      destruct (Nat.even m) eqn:Em; cbn [negb] in He.
      * rewrite lw0_alt_opp. rewrite (IH1 eq_refl). reflexivity.
      * discriminate He.
Qed.

Lemma lw0_alt_even_val : forall m : nat, Nat.even m = true -> lw0_alt m == 1%Q.
Proof. intros m He. exact (proj1 (lw0_alt_parity m) He). Qed.

Lemma lw0_alt_odd_val : forall m : nat, Nat.even m = false -> lw0_alt m == (-1)%Q.
Proof. intros m He. exact (proj2 (lw0_alt_parity m) He). Qed.

(* 望远镜项序列：j≤n 且 n≤2j 支载 conn 块同一闭式，尾项零截断。 *)
Definition lw0_Ktel_seq (a b : Z) (n j : nat) : Q :=
  if andb (Nat.leb j n) (Nat.leb n (2 * j))
  then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
  else (0 # 1)%Q.

(* 逐项对齐：交替交替相消——alt j·Ktel j == K_leg j（j≤n）。 *)
Lemma lw0_Ktel_leg_alt : forall (a b : Z) (n j : nat), (j <= n)%nat ->
  lw0_alt j * lw0_Ktel_seq a b n j == lw0_K_leg a b n j.
Proof.
  intros a b n j Hj. unfold lw0_Ktel_seq, lw0_K_leg.
  assert (E1 : Nat.leb j n = true) by (apply Nat.leb_le; exact Hj).
  rewrite E1. cbn [andb]. rewrite lw0_alt_zsign.
  destruct (Nat.leb n (2 * j)); ring.
Qed.

(* altsum 单步：altsum W (S m) == altsum W m + alt m·W m。 *)
Lemma lw0_acc_sgp_one : forall (W : nat -> Q) (m : nat),
  altsum_acc (altsum_sgp m) W m 1 == lw0_alt m * W m.
Proof.
  intros W m. unfold altsum_sgp. destruct (Nat.even m) eqn:Em.
  - rewrite altsum_acc_T. rewrite altsum_acc_0_eq.
    rewrite (lw0_alt_even_val m Em). ring.
  - rewrite altsum_acc_F. rewrite altsum_acc_0_eq.
    rewrite (lw0_alt_odd_val m Em). ring.
Qed.

Lemma lw0_Ktel_altsum_step : forall (W : nat -> Q) (m : nat),
  altsum W (Datatypes.S m) == altsum W m + lw0_alt m * W m.
Proof.
  intros W m.
  replace (Datatypes.S m)%nat with (m + 1)%nat by lia.
  rewrite lw0_altsum_add. rewrite lw0_acc_sgp_one. apply Qeq_refl.
Qed.

(* Q 层望远镜恒等（部分和形）：i≤n 时 altsum Ktel (S i) == qsum K_leg i。 *)
Lemma lw0_Ktel_partial : forall (a b : Z) (n i : nat), (i <= n)%nat ->
  altsum (lw0_Ktel_seq a b n) (Datatypes.S i) == lw0_qsum (lw0_K_leg a b n) i.
Proof.
  intros a b n i. induction i as [|i IH]; intro Hi.
  - cbn [lw0_qsum]. rewrite lw0_Ktel_altsum_step.
    assert (H0 : altsum (lw0_Ktel_seq a b n) 0%nat == 0)
      by (unfold altsum; apply altsum_acc_0_eq).
    rewrite H0. unfold lw0_K_leg, lw0_Ktel_seq.
    rewrite lw0_alt_zsign. cbn [lw0_zsign Nat.leb andb Nat.mul]. ring.
  - cbn [lw0_qsum]. rewrite lw0_Ktel_altsum_step.
    assert (Hi' : (i <= n)%nat) by lia.
    rewrite (IH Hi').
    apply Qplus_comp; [ apply Qeq_refl | apply lw0_Ktel_leg_alt; exact Hi ].
Qed.

(* 尾零件：j 越界（S n≤j）则 Ktel j == 0；连带 acc 尾零。 *)
Lemma lw0_Ktel_acc_zero : forall (a b : Z) (n r k : nat) (sg : bool),
  (Datatypes.S n <= k)%nat ->
  altsum_acc sg (lw0_Ktel_seq a b n) k r == 0.
Proof.
  intros a b n r. induction r as [|r IH]; intros k sg Hk.
  - apply altsum_acc_0_eq.
  - assert (Hz : lw0_Ktel_seq a b n k == 0).
    { unfold lw0_Ktel_seq.
      assert (Ef : Nat.leb k n = false) by (apply Nat.leb_gt; lia).
      rewrite Ef. cbn [andb]. reflexivity. }
    destruct sg.
    + rewrite altsum_acc_T. rewrite Hz.
      rewrite (IH (Datatypes.S k) false) by lia. ring.
    + rewrite altsum_acc_F. rewrite Hz.
      rewrite (IH (Datatypes.S k) true) by lia. ring.
Qed.

(* 尾稳定性：S n≤m 后序列恒定。 *)
Lemma lw0_Ktel_stable : forall (a b : Z) (n m : nat), (Datatypes.S n <= m)%nat ->
  altsum (lw0_Ktel_seq a b n) m == altsum (lw0_Ktel_seq a b n) (Datatypes.S n).
Proof.
  intros a b n m Hm. destruct m as [|m'].
  { inversion Hm. }
  replace (Datatypes.S m') with (Datatypes.S n + (m' - n))%nat by lia.
  rewrite lw0_altsum_add. rewrite lw0_Ktel_acc_zero by lia. ring.
Qed.

(* Q 层望远镜恒等（闭合形）：S n≤m 时 altsum Ktel m == lw0_K a b n。 *)
Lemma lw0_Ktel_tail : forall (a b : Z) (n m : nat), (Datatypes.S n <= m)%nat ->
  altsum (lw0_Ktel_seq a b n) m == lw0_K a b n.
Proof.
  intros a b n m Hm.
  rewrite (lw0_Ktel_stable a b n m Hm).
  rewrite (lw0_Ktel_partial a b n n (Nat.le_refl n)).
  unfold lw0_K. apply Qeq_refl.
Qed.

(* 柯西见证：序列尾恒定 ⟹ 柯西（见证 N := S n）。 *)
Lemma lw0_Ktel_cauchy : forall (a b : Z) (n : nat),
  cauchy (fun m : nat => altsum (lw0_Ktel_seq a b n) m).
Proof.
  intros a b n eps Heps. exists (Datatypes.S n)%nat. intros m m' Hm Hm'.
  assert (Ht1 : altsum (lw0_Ktel_seq a b n) m == lw0_K a b n)
    by (apply lw0_Ktel_tail; exact (NatLe_drop _ _ Hm)).
  assert (Ht2 : altsum (lw0_Ktel_seq a b n) m' == lw0_K a b n)
    by (apply lw0_Ktel_tail; exact (NatLe_drop _ _ Hm')).
  assert (Hz : Qabs (altsum (lw0_Ktel_seq a b n) m
                     - altsum (lw0_Ktel_seq a b n) m') == 0).
  { apply (Qeq_trans _ (Qabs (lw0_K a b n - lw0_K a b n)) _).
    - apply Qabs_wd. apply Qminus_comp; assumption.
    - apply q_abs_self_zero. }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (altsum (lw0_Ktel_seq a b n) m
                     - altsum (lw0_Ktel_seq a b n) m')) eps = Qcompare 0 eps).
  { exact (Qcompare_comp _ 0 Hz eps eps (Qeq_refl eps)). }
  rewrite Hcmp. rewrite Hcmp0. reflexivity.
Qed.

(* 等值桥正形（② 供件语句，名沿 lw0_K_leg_connect）：望远镜实现 L 与
   K 常值在实层相等。新形对照旧粗配对：L 对象由 Wb 交错序列（0.0039 型）
   改为 conn 同源望远镜序列（22 型），等值无条件成立。 *)
Lemma lw0_K_leg_connect : forall (a b : Z) (n : nat),
  real_eq (lw0_L_of_seq (lw0_Ktel_seq a b n) (lw0_Ktel_cauchy a b n))
          (real_const (lw0_K a b n)).
Proof.
  intros a b n. apply lw0_real_eq_const_tail.
  intros eps Heps. exists (Datatypes.S n)%nat. intros m Hm.
  assert (Ht : altsum (lw0_Ktel_seq a b n) m == lw0_K a b n)
    by (apply lw0_Ktel_tail; exact (NatLe_drop _ _ Hm)).
  assert (Hz : Qabs (altsum (lw0_Ktel_seq a b n) m - lw0_K a b n) == 0).
  { apply (Qeq_trans _ (Qabs (lw0_K a b n - lw0_K a b n)) _).
    - apply Qabs_wd. apply Qminus_comp; [ exact Ht | apply Qeq_refl ].
    - apply q_abs_self_zero. }
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hcmp : Qcompare (Qabs (altsum (lw0_Ktel_seq a b n) m
                     - lw0_K a b n)) eps = Qcompare 0 eps).
  { exact (Qcompare_comp _ 0 Hz eps eps (Qeq_refl eps)). }
  rewrite Hcmp. rewrite Hcmp0. reflexivity.
Qed.

(* 数值自洽判据（(a,b,n)=(1,1,2)）：两岸同为 22，vm_compute 逐字闭合。 *)
Lemma lw0_Ktel_num22 :
  (altsum (lw0_Ktel_seq 1%Z 1%Z 2%nat) 3%nat == (22 # 1)%Q) /\
  (lw0_K 1%Z 1%Z 2%nat == (22 # 1)%Q).
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions lw0_alt_zsign.
Print Assumptions lw0_alt_even_val.
Print Assumptions lw0_alt_odd_val.
Print Assumptions lw0_Ktel_leg_alt.
Print Assumptions lw0_acc_sgp_one.
Print Assumptions lw0_Ktel_altsum_step.
Print Assumptions lw0_Ktel_partial.
Print Assumptions lw0_Ktel_acc_zero.
Print Assumptions lw0_Ktel_stable.
Print Assumptions lw0_Ktel_tail.
Print Assumptions lw0_Ktel_cauchy.
Print Assumptions lw0_K_leg_connect.
Print Assumptions lw0_Ktel_num22.

Lemma lw0_Wb_norm_eq : forall (b q : Q) (n j : nat),
  QeqT (q_fact n * lw0_Wb b q n j)
       (q_pow b n * q_pow q (2*n + 2*j + 2) * q_fact (n + 2*j + 1) /
        (q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))).
Proof.
  intros b q n j. apply qeq_imp_qeqT.
  unfold lw0_Wb, Qdiv.
  rewrite <- (Qmult_assoc (q_fact n) (q_fact (2*j + 1)) (q_fact (2*n + 2*j + 2))).
  rewrite (Qinv_mult_distr (q_fact n) (q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))).
  rewrite (Qmult_comm ((q_pow b n * q_pow q (2*n + 2*j + 2)) * q_fact (n + 2*j + 1))
                      ((/ (q_fact n)) * (/ (q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))))).
  rewrite (Qmult_assoc (q_fact n)
                       ((/ (q_fact n)) * (/ (q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))))
                       ((q_pow b n * q_pow q (2*n + 2*j + 2)) * q_fact (n + 2*j + 1))).
  rewrite (Qmult_assoc (q_fact n) (/ (q_fact n))
                       (/ (q_fact (2*j + 1) * q_fact (2*n + 2*j + 2)))).
  rewrite (Qmult_inv_r (q_fact n) (lw0_q_fact_ne0 n)).
  ring.
Qed.

(* ============================================================
   [语句二切片 2] 望远镜连接核（纯 Q 层代数、零分析）：
   望远镜项＝f_n(t)=b^n t^n (q−t)^n / q_fact n 的分部积分核岸闭式——
   第 j 项＝f_n 的 (2j+1) 重零基原函数在 q 的取值，Q 层可计算形
     q_pow b n · q_pow q (2n+2j+2) · q_fact (n+2j+1) 除以
     (q_fact (2j+1) · q_fact (2n+2j+2))；
   分部积分引擎 lw0_qp_pair_ibp（配对积形式）沿核链逐项生成该序列，
   列表级逐字推演归实层课（q⁶ 两岸不等在案，Q 层不超配）。
   逐项过渡以切片 1 已绿件 lw0_Wb_norm_eq 直供（QeqT 面）；
   迭代步递推面沿 lw0_Wb_ratio_eq 经过渡平移（纯 Qmult_assoc 收尾）；
   altsum 前缀恒等照 lw0_Ktel_partial 同构。数值判据 (b,q,n)=(1,1,2)：
   j=0 项 1/120、j=1 带交替号项 -1/2016，与切片 1 双锚逐字同值，
   过渡向数值交叉印证。除法形零 ring 直证：刀面 /-形全经已绿过渡与
   vm_compute 消化，递推岸纯 Qmult_assoc。
   ============================================================ *)

Definition lw0_Wtel_seq (b q : Q) (n j : nat) : Q :=
  q_pow b n * q_pow q (2*n + 2*j + 2) * q_fact (n + 2*j + 1) /
  (q_fact (2*j + 1) * q_fact (2*n + 2*j + 2)).

(* 逐项过渡：归一 Wb 项＝望远镜项（切片 1 已绿件直供，QeqT 面）。 *)
Lemma lw0_Wtel_norm_bridge : forall (b q : Q) (n j : nat),
  QeqT (q_fact n * lw0_Wb b q n j) (lw0_Wtel_seq b q n j).
Proof. intros b q n j. exact (lw0_Wb_norm_eq b q n j). Qed.

(* 迭代步递推面：望远镜项 (S j) 项＝j 项·定比（沿 lw0_Wb_ratio_eq）。 *)
Lemma lw0_Wtel_ratio_step : forall (b q : Q) (n j : nat),
  QeqT (lw0_Wtel_seq b q n (Datatypes.S j))
       (lw0_Wtel_seq b q n j *
        (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
         (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
          lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))).
Proof.
  intros b q n j. apply qeq_imp_qeqT.
  assert (HA := qeqT_imp_qeq _ _ (lw0_Wtel_norm_bridge b q n (Datatypes.S j))).
  assert (HB := qeqT_imp_qeq _ _ (lw0_Wtel_norm_bridge b q n j)).
  assert (HR := lw0_Wb_ratio_eq b q n j).
  rewrite <- HA. rewrite HR. rewrite <- HB. apply Qmult_assoc.
Qed.

(* altsum 前缀恒等：望远镜项交替和前缀＝归一 Wb 项交替 qsum 前缀
   （照 lw0_Ktel_partial 同构，逐项经过渡件）。 *)
Lemma lw0_Wtel_altsum_prefix : forall (b q : Q) (n i : nat),
  QeqT (altsum (fun j : nat => lw0_Wtel_seq b q n j) (Datatypes.S i))
       (lw0_qsum (fun j : nat => lw0_alt j * (q_fact n * lw0_Wb b q n j)) i).
Proof.
  intros b q n i. apply qeq_imp_qeqT.
  induction i as [|i IH].
  - cbn [lw0_qsum]. rewrite lw0_Ktel_altsum_step.
    assert (H0q : QeqT (altsum (fun j : nat => lw0_Wtel_seq b q n j) 0%nat) 0%Q).
    { unfold altsum. apply qeq_imp_qeqT. apply altsum_acc_0_eq. }
    rewrite (qeqT_imp_qeq _ _ H0q).
    assert (HB := qeqT_imp_qeq _ _ (lw0_Wtel_norm_bridge b q n 0%nat)).
    rewrite HB. cbv beta. ring.
  - cbn [lw0_qsum]. rewrite lw0_Ktel_altsum_step. rewrite IH.
    assert (HB := qeqT_imp_qeq _ _ (lw0_Wtel_norm_bridge b q n (Datatypes.S i))).
    apply Qplus_comp; [ apply Qeq_refl | rewrite HB; cbv beta; apply Qeq_refl ].
Qed.

(* 数值判据双实例：(b,q,n)=(1,1,2)。 *)
Lemma lw0_Wtel_num120 :
  QeqT (lw0_Wtel_seq 1 1 2 0) (1 # 120)%Q.
Proof. vm_compute; reflexivity. Qed.

Lemma lw0_Wtel_num2016 :
  QeqT (lw0_alt 1 * lw0_Wtel_seq 1 1 2 1) (Qopp (1 # 2016)%Q).
Proof. vm_compute; reflexivity. Qed.

Print Assumptions lw0_Wtel_norm_bridge.
Print Assumptions lw0_Wtel_ratio_step.
Print Assumptions lw0_Wtel_altsum_prefix.
Print Assumptions lw0_Wtel_num120.
Print Assumptions lw0_Wtel_num2016.

(* ================= §6.5 末段 ③ B 车道引擎面（F 系泛函 IBP 路线） ================= *)
(* 出处：B 车道 F 系泛函 IBP 路线引擎块；基座依赖面见下清单，基线快照        *)
(* 核验在卷（快照与源面逐字节全等）。                                       *)
(* 插入锚＝引擎基座块之后、主语句备档区之前。命名空间 lw0_pitB_ 全隔离（与 A 车道零撞名）。  *)
(* 勘察结论：F 系 IBP 引擎级半成品在件——lw0_qp_pair_ibp（步进恒等式，泛 R S q）、    *)
(* 配对线性四件（lw0_qp_pair_add_l/r、lw0_qp_pair_scalar_l/r）、qpoly_eval_mul、              *)
(* qpoly_deriv_mul、F 系 lw0_F_plus_deriv2（F+F''=f，die 预算 lw0_die_zero）、σ/γ 导数关系   *)
(* （lw0_sin_qp_deriv_eval：σ_N′=γ_N；lw0_cos_qp_deriv_eval：γ_{SN}′=−σ_N）、实层包装与      *)
(* 端点传输（lw0_sin_series_real_eq／lw0_cos_series_real_eq／lw0_endpoint_transport）。       *)
(* 本块交付＝B 车道引擎件：二次 IBP 转移（泛 f 泛 g 泛 q）——配对积形式的步进件，纯多项式层， *)
(* 不碰级数尾项（A 车道风险点天然绕开）。余量（两项）：(α) Wb↔配对积分 Beta 桥    *)
(* （altsum Wb m ＝ <f_n, σ_{m+1}> 逐项恒等，Vandermonde 型交替项和）；(β) 三项收敛装配       *)
(* （σ_M(q)→0、γ_M(q)→−1、<F,τ_M>→0；π 前提经 lw0_endpoint_transport 于 Real 层取用；        *)
(* 柯西侧沿 (α) 与 lw0_Wb_altseq_cauchy 同列免证）。                                         *)
(* 目标形备档（终装认先到者，与 A 车道同形）：本体＝                                         *)
(*   real_eq real_pi_geom (real_const (a # b)) ->                                            *)
(*   real_eq (lw0_L_of_seq (lw0_Wb a' b' n) HcW) (lw0_L_of_seq (lw0_Ktel_seq a b n) HcK)；   *)
(* 复合＝同前提 -> real_eq (lw0_L_of_seq (lw0_Wb a' b' n_sel) HcW) (real_const (lw0_K a b n_sel)) *)
(* ＝本体＋lw0_K_leg_connect 传递（换算取：a'=Qnum q、b'=Zpos (Qden q)、    *)
(* n_sel=lw0_n_select (10*d) k）。层纪律：π 前提只经 lw0_sin_endpoint_transport／            *)
(* lw0_cos_endpoint_transport 于 Real 层取用；禁任何 Q 层 sin_Q(a/b)==0 形（π 无理性正是定理）。 *)

(* B 车道引擎件：二次 IBP 转移。证法＝lw0_qp_pair_ibp 两次实例（R:=f',S:=g 与 R:=f,S:=g'）， *)
(* 公共项 <f', g'> 经 Q 环代换消去；边界交换式＝(fg')(q)−(fg')(0)−(f'g)(q)+(f'g)(0)。       *)
Lemma lw0_pitB_ibp_dbl : forall (f g : qpoly) (q : Q),
  lw0_qp_pair f (qpoly_deriv_iter 2 g) q ==
  lw0_qp_pair (qpoly_deriv_iter 2 f) g q
  + (qpoly_eval (qpoly_mul f (qpoly_deriv g)) q
       - qpoly_eval (qpoly_mul f (qpoly_deriv g)) 0)
  - (qpoly_eval (qpoly_mul (qpoly_deriv f) g) q
       - qpoly_eval (qpoly_mul (qpoly_deriv f) g) 0).
Proof.
  intros f g q.
  change (qpoly_deriv_iter 2 f) with (qpoly_deriv (qpoly_deriv f)).
  change (qpoly_deriv_iter 2 g) with (qpoly_deriv (qpoly_deriv g)).
  assert (HA := lw0_qp_pair_ibp (qpoly_deriv f) g q).
  assert (HB := lw0_qp_pair_ibp f (qpoly_deriv g) q).
  rewrite <- HA. rewrite <- HB.
  ring.
Qed.

Print Assumptions lw0_pitB_ibp_dbl.

(* ---------- _tlw209 (alpha) Beta 桥块 ----------
   组成：引擎十二件＋桥核 lw0_pitB_bridge_aux＋主桥 lw0_pitB_bridge
   来源：引擎与主桥整件逐关验证后并入本块
   锚位：Print Assumptions lw0_pitB_ibp_dbl. 之后、主语句备档区之前
   语句面：lw0_pitB_bridge 为钉定形，逐字未改 *)

(* ===== 引擎一：二元素左乘 [0;1] 的 ai 族 ===== *)
Lemma lw0_pitB_ai_mul01 : forall g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (cons 0%Q (cons 1%Q nil)) g) k) x
  == x * qpoly_eval (lw0_qp_ai g (Datatypes.S k)) x.
Proof.
  intros g k x.
  change (qpoly_mul (cons 0%Q (cons 1%Q nil)) g)
    with (qpoly_add (qpoly_scalar 0%Q g) (cons 0%Q (qpoly_mul (cons 1%Q nil) g))).
  rewrite (lw0_qp_ai_add (qpoly_scalar 0%Q g) (cons 0%Q (qpoly_mul (cons 1%Q nil) g)) k x).
  rewrite (lw0_qp_ai_scalar 0%Q g k x).
  rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (cons 1%Q nil) g) k x).
  change (qpoly_mul (cons 1%Q nil) g)
    with (qpoly_add (qpoly_scalar 1%Q g) (cons 0%Q (qpoly_mul (@nil Q) g))).
  change (qpoly_mul (@nil Q) g) with (@nil Q).
  rewrite (lw0_qp_ai_add (qpoly_scalar 1%Q g) (cons 0%Q (@nil Q)) (Datatypes.S k) x).
  rewrite (lw0_qp_ai_scalar 1%Q g (Datatypes.S k) x).
  rewrite (lw0_qp_ai_zero_head_eval (@nil Q) (Datatypes.S k) x).
  change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S (Datatypes.S k))) x) with 0%Q.
  ring.
Qed.

(* ===== 引擎二：ai 层乘法再结合（对首表归纳，B C 泛形） ===== *)
Lemma lw0_pitB_ai_mulA : forall A B C k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_mul A B) C) k) x
  == qpoly_eval (lw0_qp_ai (qpoly_mul A (qpoly_mul B C)) k) x.
Proof.
  induction A as [|a A IH]; intros B C k x.
  - change (qpoly_mul (@nil Q) B) with (@nil Q).
    change (qpoly_mul (@nil Q) (qpoly_mul B C)) with (@nil Q).
    reflexivity.
  - change (qpoly_mul (cons a A) B)
      with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
    rewrite (lw0_qp_ai_mul_add_l (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B)) C k x).
    rewrite (lw0_qp_ai_mul_scalar_l a B C k x).
    change (qpoly_mul (cons 0%Q (qpoly_mul A B)) C)
      with (qpoly_add (qpoly_scalar 0%Q C) (cons 0%Q (qpoly_mul (qpoly_mul A B) C))).
    rewrite (lw0_qp_ai_add (qpoly_scalar 0%Q C) (cons 0%Q (qpoly_mul (qpoly_mul A B) C)) k x).
    rewrite (lw0_qp_ai_scalar 0%Q C k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_mul A B) C) k x).
    change (qpoly_mul (cons a A) (qpoly_mul B C))
      with (qpoly_add (qpoly_scalar a (qpoly_mul B C))
              (cons 0%Q (qpoly_mul A (qpoly_mul B C)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_mul B C))
               (cons 0%Q (qpoly_mul A (qpoly_mul B C))) k x).
    rewrite (lw0_qp_ai_scalar a (qpoly_mul B C) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul A (qpoly_mul B C)) k x).
    rewrite (IH B C (Datatypes.S k) x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

(* ===== 引擎三：单项式左移主引理（t^p * g 的 ai 族） ===== *)
Lemma lw0_pitB_ai_monoL : forall p g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_mono p) g) k) x
  == q_pow x p * qpoly_eval (lw0_qp_ai g (k + p)) x.
Proof.
  induction p as [|p IH]; intros g k x.
  - change (lw0_pi_mono 0) with (cons 1%Q nil).
    change (qpoly_mul (cons 1%Q nil) g)
      with (qpoly_add (qpoly_scalar 1%Q g) (cons 0%Q (qpoly_mul (@nil Q) g))).
    change (qpoly_mul (@nil Q) g) with (@nil Q).
    rewrite (lw0_qp_ai_add (qpoly_scalar 1%Q g) (cons 0%Q (@nil Q)) k x).
    rewrite (lw0_qp_ai_scalar 1%Q g k x).
    rewrite (lw0_qp_ai_zero_head_eval (@nil Q) k x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    change (q_pow x 0) with 1%Q.
    replace (k + 0)%nat with k by lia.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (lw0_pi_mono (Datatypes.S p))
      with (qpoly_mul (lw0_pi_mono p) (cons 0%Q (cons 1%Q nil))).
    rewrite (lw0_pitB_ai_mulA (lw0_pi_mono p) (cons 0%Q (cons 1%Q nil)) g k x).
    rewrite (IH (qpoly_mul (cons 0%Q (cons 1%Q nil)) g) k x).
    rewrite (lw0_pitB_ai_mul01 g (k + p)%nat x).
    rewrite (q_pow_succ x p).
    replace (k + Datatypes.S p)%nat with (Datatypes.S (k + p)) by lia.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

(* ===== 引擎四：二元素右乘族（对被乘表归纳） ===== *)
Lemma lw0_pitB_ai_pair2 : forall g a b k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul g (cons a (cons b nil))) k) x
  == a * qpoly_eval (lw0_qp_ai g k) x
     + b * (x * qpoly_eval (lw0_qp_ai g (Datatypes.S k)) x).
Proof.
  induction g as [|c g IH]; intros a b k x.
  - change (qpoly_mul (@nil Q) (cons a (cons b nil))) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons c g) (cons a (cons b nil)))
      with (qpoly_add (qpoly_scalar c (cons a (cons b nil)))
              (cons 0%Q (qpoly_mul g (cons a (cons b nil))))).
    rewrite (lw0_qp_ai_add (qpoly_scalar c (cons a (cons b nil)))
               (cons 0%Q (qpoly_mul g (cons a (cons b nil)))) k x).
    rewrite (lw0_qp_ai_scalar c (cons a (cons b nil)) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul g (cons a (cons b nil))) k x).
    rewrite (IH a b (Datatypes.S k) x).
    rewrite (lw0_qp_ai_cons_eval a (cons b nil) k x).
    rewrite (lw0_qp_ai_cons_eval b (@nil Q) (Datatypes.S k) x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S (Datatypes.S k))) x) with 0%Q.
    rewrite (lw0_qp_ai_cons_eval c g k x).
    rewrite (lw0_qp_ai_cons_eval c g (Datatypes.S k) x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_div_scale : forall a d E : Q, ~ E == 0 -> a / d == a * E / (E * d).
Proof.
  intros a d E HE.
  unfold Qdiv.
  rewrite Qinv_mult_distr.
  assert (Hm : (a * E * (Qinv E * Qinv d))%Q == ((a * (E * Qinv E)) * Qinv d)%Q) by ring.
  rewrite Hm.
  rewrite (Qmult_inv_r E HE).
  ring.
Qed.

(* ===== 引擎五：E 族——(q-t)^n 的逐项积分闭式（Beta 核） ===== *)
Lemma lw0_pitB_E : forall n q k,
  qpoly_eval (lw0_qp_ai (lw0_pi_qminus_pow q n) k) q
  == q_pow q n * q_fact n * q_fact k / q_fact (n + k + 1).
Proof.
  intros n q. induction n as [|n IH]; intros k.
  - change (lw0_pi_qminus_pow q 0) with (cons 1%Q nil).
    rewrite (lw0_qp_ai_cons_eval 1%Q (@nil Q) k q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) q) with 0%Q.
    change (q_pow q 0) with 1%Q.
    change (q_fact 0) with 1%Q.
    replace (0 + k + 1)%nat with (Datatypes.S k) by lia.
    rewrite (q_fact_succ k).
    assert (Hk0 : ~ q_fact k == 0%Q).
    { intro Hc. apply (Qlt_not_eq 0 (q_fact k) (q_fact_pos k)).
      symmetry. exact Hc. }
    assert (Hm2 : (1 * 1 * q_fact k * (Qinv (Z.of_nat (Datatypes.S k) # 1) * Qinv (q_fact k)))%Q
                  == ((1 * 1 * (q_fact k * Qinv (q_fact k))) * Qinv (Z.of_nat (Datatypes.S k) # 1))%Q) by ring.
    assert (Hbase : (1 * 1 * q_fact k / ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)
                     == 1 / (Z.of_nat (Datatypes.S k) # 1))%Q).
    { unfold Qdiv. rewrite Qinv_mult_distr. rewrite Hm2.
      rewrite (Qmult_inv_r (q_fact k) Hk0). ring. }
    rewrite Hbase. unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (lw0_pi_qminus_pow q (Datatypes.S n))
      with (qpoly_mul (lw0_pi_qminus_pow q n) (cons q (cons (-1)%Q nil))).
    rewrite (lw0_pitB_ai_pair2 (lw0_pi_qminus_pow q n) q (-1)%Q k q).
    rewrite (IH k). rewrite (IH (Datatypes.S k)).
    change (q_pow q (Datatypes.S n)) with (q * q_pow q n)%Q.
    rewrite (q_fact_succ n). rewrite (q_fact_succ k).
    replace (n + Datatypes.S k + 1)%nat with (Datatypes.S (n + k + 1)) by lia.
    replace (Datatypes.S n + k + 1)%nat with (Datatypes.S (n + k + 1)) by lia.
    rewrite (q_fact_succ (n + k + 1)).
    assert (Hz : (Z.of_nat (Datatypes.S (n + k + 1))
                  = (Z.of_nat (Datatypes.S n) + Z.of_nat (Datatypes.S k)))%Z).
    { lia. }
    assert (Hzq : (Z.of_nat (Datatypes.S (n + k + 1)) # 1)%Q
                  == ((Z.of_nat (Datatypes.S n) # 1) + (Z.of_nat (Datatypes.S k) # 1))%Q).
    { unfold Qeq. cbn [Qnum Qden Qplus Qmult]. rewrite Hz. lia. }
    rewrite Hzq.
    assert (HE : ~ ((Z.of_nat (Datatypes.S n) # 1) + (Z.of_nat (Datatypes.S k) # 1))%Q == 0%Q).
    { intros Hc.
      assert (H1 : Qlt 0 (Z.of_nat (Datatypes.S n) # 1))
        by (apply QltT_to_Qlt; apply lw0_q_of_nat_lt0T_S).
      assert (H2 : Qlt 0 (Z.of_nat (Datatypes.S k) # 1))
        by (apply QltT_to_Qlt; apply lw0_q_of_nat_lt0T_S).
      assert (Hs : Qlt (0 + 0)%Q ((Z.of_nat (Datatypes.S n) # 1)
                                   + (Z.of_nat (Datatypes.S k) # 1))%Q)
        by (apply Qplus_lt_compat; [exact H1 | exact H2]).
      rewrite Qplus_0_l in Hs.
      apply (Qlt_not_eq 0 ((Z.of_nat (Datatypes.S n) # 1)
                           + (Z.of_nat (Datatypes.S k) # 1))%Q Hs).
      symmetry. exact Hc. }
    rewrite (lw0_pitB_div_scale (q_pow q n * q_fact n * q_fact k)
                  (q_fact (n + k + 1))
                  ((Z.of_nat (Datatypes.S n) # 1) + (Z.of_nat (Datatypes.S k) # 1))%Q
                  HE).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.



(* ===== 引擎六：sin_aux 的 ai 族（纯 ai 形尾段移位） ===== *)
Lemma lw0_pitB_ai_sin_aux : forall j acc k x,
  qpoly_eval (lw0_qp_ai (lw0_sin_aux j acc) k) x
  == qpoly_eval (lw0_qp_ai (lw0_sin_qp j) k) x
     + q_pow x (Datatypes.S (Datatypes.S (2 * j)))
       * qpoly_eval (lw0_qp_ai acc (k + Datatypes.S (Datatypes.S (2 * j)))) x.
Proof.
  induction j as [|M IH]; intros acc k x.
  - change (lw0_sin_aux 0 acc)
      with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q acc)).
    rewrite (lw0_qp_ai_zero_head_eval (cons (q_pow (-1) 0 / q_fact 1)%Q acc) k x).
    rewrite (lw0_qp_ai_cons_eval (q_pow (-1) 0 / q_fact 1)%Q acc (Datatypes.S k) x).
    change (lw0_sin_qp 0) with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q))).
    rewrite (lw0_qp_ai_zero_head_eval (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q)) k x).
    rewrite (lw0_qp_ai_cons_eval (q_pow (-1) 0 / q_fact 1)%Q (@nil Q) (Datatypes.S k) x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S (Datatypes.S k))) x) with 0%Q.
    change (Datatypes.S (Datatypes.S (2 * 0))) with 2%nat.
    replace (k + 2)%nat with (Datatypes.S (Datatypes.S k)) by lia.
    cbn [q_pow].
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q).
    change (lw0_sin_aux (Datatypes.S M) acc) with (lw0_sin_aux M (cons 0%Q (cons c acc))).
    change (lw0_sin_qp (Datatypes.S M)) with (lw0_sin_aux M (cons 0%Q (cons c (@nil Q)))).
    rewrite (IH (cons 0%Q (cons c acc)) k x).
    rewrite (IH (cons 0%Q (cons c (@nil Q))) k x).
    rewrite (lw0_qp_ai_zero_head_eval (cons c acc)
               (k + Datatypes.S (Datatypes.S (2 * M))) x).
    rewrite (lw0_qp_ai_zero_head_eval (cons c (@nil Q))
               (k + Datatypes.S (Datatypes.S (2 * M))) x).
    rewrite (lw0_qp_ai_cons_eval c acc
               (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M)))) x).
    rewrite (lw0_qp_ai_cons_eval c (@nil Q)
               (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M)))) x).
    change (qpoly_eval (lw0_qp_ai (@nil Q)
              (Datatypes.S (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M)))))) x)
      with 0%Q.
    replace (Datatypes.S (Datatypes.S (2 * Datatypes.S M)))
      with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) by lia.
    replace (k + Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%nat
      with (Datatypes.S (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M))))) by lia.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * (x * q_pow x (Datatypes.S (Datatypes.S (2 * M))))%Q)%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

(* ===== 引擎七：配对积侧 sin_aux 族（F 泛形，对 F 表归纳） ===== *)
Lemma lw0_pitB_ai_mul_sin_aux : forall F j acc k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul F (lw0_sin_aux j acc)) k) x
  == qpoly_eval (lw0_qp_ai (qpoly_mul F (lw0_sin_qp j)) k) x
     + q_pow x (Datatypes.S (Datatypes.S (2 * j)))
       * qpoly_eval (lw0_qp_ai (qpoly_mul F acc)
                              (k + Datatypes.S (Datatypes.S (2 * j)))) x.
Proof.
  induction F as [|a F IH]; intros j acc k x.
  - change (qpoly_mul (@nil Q) (lw0_sin_aux j acc)) with (@nil Q).
    change (qpoly_mul (@nil Q) (lw0_sin_qp j)) with (@nil Q).
    change (qpoly_mul (@nil Q) acc) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) (k + Datatypes.S (Datatypes.S (2 * j)))) x)
      with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons a F) (lw0_sin_aux j acc))
      with (qpoly_add (qpoly_scalar a (lw0_sin_aux j acc))
              (cons 0%Q (qpoly_mul F (lw0_sin_aux j acc)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (lw0_sin_aux j acc))
               (cons 0%Q (qpoly_mul F (lw0_sin_aux j acc))) k x).
    rewrite (lw0_qp_ai_scalar a (lw0_sin_aux j acc) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (lw0_sin_aux j acc)) k x).
    rewrite (lw0_pitB_ai_sin_aux j acc k x).
    rewrite (IH j acc (Datatypes.S k) x).
    change (qpoly_mul (cons a F) (lw0_sin_qp j))
      with (qpoly_add (qpoly_scalar a (lw0_sin_qp j))
              (cons 0%Q (qpoly_mul F (lw0_sin_qp j)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (lw0_sin_qp j))
               (cons 0%Q (qpoly_mul F (lw0_sin_qp j))) k x).
    rewrite (lw0_qp_ai_scalar a (lw0_sin_qp j) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (lw0_sin_qp j)) k x).
    change (qpoly_mul (cons a F) acc)
      with (qpoly_add (qpoly_scalar a acc) (cons 0%Q (qpoly_mul F acc))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a acc) (cons 0%Q (qpoly_mul F acc))
               (k + Datatypes.S (Datatypes.S (2 * j))) x).
    rewrite (lw0_qp_ai_scalar a acc (k + Datatypes.S (Datatypes.S (2 * j))) x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F acc)
               (k + Datatypes.S (Datatypes.S (2 * j))) x).
    replace (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * j))))%nat
      with (Datatypes.S k + Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

(* ===== 引擎八：零头右乘剥离 ===== *)
Lemma lw0_pitB_ai_mul_cons0 : forall F w k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul F (cons 0%Q w)) k) x
  == x * qpoly_eval (lw0_qp_ai (qpoly_mul F w) (Datatypes.S k)) x.
Proof.
  induction F as [|a F IH]; intros w k x.
  - change (qpoly_mul (@nil Q) (cons 0%Q w)) with (@nil Q).
    change (qpoly_mul (@nil Q) w) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons a F) (cons 0%Q w))
      with (qpoly_add (qpoly_scalar a (cons 0%Q w))
              (cons 0%Q (qpoly_mul F (cons 0%Q w)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (cons 0%Q w))
               (cons 0%Q (qpoly_mul F (cons 0%Q w))) k x).
    rewrite (lw0_qp_ai_scalar a (cons 0%Q w) k x).
    rewrite (lw0_qp_ai_zero_head_eval w k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (cons 0%Q w)) k x).
    rewrite (IH w (Datatypes.S k) x).
    change (qpoly_mul (cons a F) w)
      with (qpoly_add (qpoly_scalar a w) (cons 0%Q (qpoly_mul F w))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a w) (cons 0%Q (qpoly_mul F w))
               (Datatypes.S k) x).
    rewrite (lw0_qp_ai_scalar a w (Datatypes.S k) x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F w) (Datatypes.S k) x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

(* ===== 引擎九：常数头右乘剥离 ===== *)
Lemma lw0_pitB_ai_mul_cons1 : forall F c k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul F (cons c%Q (@nil Q))) k) x
  == c * qpoly_eval (lw0_qp_ai F k) x.
Proof.
  induction F as [|a F IH]; intros c k x.
  - change (qpoly_mul (@nil Q) (cons c%Q (@nil Q))) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons a F) (cons c%Q (@nil Q)))
      with (qpoly_add (qpoly_scalar a (cons c%Q (@nil Q)))
              (cons 0%Q (qpoly_mul F (cons c%Q (@nil Q))))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (cons c%Q (@nil Q)))
               (cons 0%Q (qpoly_mul F (cons c%Q (@nil Q)))) k x).
    rewrite (lw0_qp_ai_scalar a (cons c%Q (@nil Q)) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (cons c%Q (@nil Q))) k x).
    rewrite (IH c (Datatypes.S k) x).
    rewrite (lw0_qp_ai_cons_eval c (@nil Q) k x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    rewrite (lw0_qp_ai_cons_eval a F k x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

(* ===== 引擎十：altsum 单步（尾项符号 = (-1)^m） ===== *)
Lemma lw0_pitB_acc_S : forall sg f k m,
  altsum_acc sg f k (Datatypes.S m)
  == altsum_acc sg f k m
     + (if sg then q_pow (-1) m else Qopp (q_pow (-1) m)) * f (k + m)%nat.
Proof.
  intros sg f k m. revert sg k.
  induction m as [|m IH]; intros sg k.
  - cbn [altsum_acc].
    replace (k + 0)%nat with k by lia.
    destruct sg; cbn [q_pow]; ring.
  - assert (Hstep : forall (sg0 : bool) (j n : nat),
        altsum_acc sg0 f j (Datatypes.S n)
        == (if sg0 then f j else Qopp (f j))
           + altsum_acc (negb sg0) f (Datatypes.S j) n)
      by (intros sg0 j n; destruct sg0; reflexivity).
    rewrite (Hstep sg k (Datatypes.S m)).
    rewrite (Hstep sg k m).
    rewrite (IH (negb sg) (Datatypes.S k)).
    replace (Datatypes.S k + m)%nat with (k + Datatypes.S m)%nat by lia.
    change (q_pow (-1) (Datatypes.S m)) with ((-1) * q_pow (-1) m)%Q.
    destruct sg; cbn [negb]; ring.
Qed.

Lemma lw0_pitB_altsum_S : forall W m,
  altsum W (Datatypes.S m) == altsum W m + q_pow (-1) m * W m.
Proof.
  intros W m. unfold altsum.
  rewrite (lw0_pitB_acc_S true W 0 m).
  replace (0 + m)%nat with m by lia.
  reflexivity.
Qed.

(* ===== 引擎十一：q_pow 加法分解（幂原子对齐用） ===== *)
Lemma lw0_pitB_q_pow_add : forall (x : Q) (a b : nat),
  q_pow x (a + b)%nat == q_pow x a * q_pow x b.
Proof.
  intros x a b. induction a as [|a IH].
  - replace (0 + b)%nat with b by lia.
    cbn [q_pow]. ring.
  - replace (Datatypes.S a + b)%nat with (Datatypes.S (a + b)) by lia.
    cbn [q_pow]. rewrite IH. ring.
Qed.

(* ===== 引擎十二：Qeq 非零因子消去 ===== *)
Lemma lw0_pitB_Qeq_cancel_l : forall (z X Y : Q),
  ~ z == 0 -> z * X == z * Y -> X == Y.
Proof.
  intros z X Y Hz H.
  assert (Hs : (Qinv z * (z * X))%Q == (Qinv z * (z * Y))%Q)
    by (rewrite H; reflexivity).
  assert (Hm : (Qinv z * (z * X))%Q == ((z * Qinv z) * X)%Q) by ring.
  assert (Hm2 : (Qinv z * (z * Y))%Q == ((z * Qinv z) * Y)%Q) by ring.
  rewrite Hm in Hs. rewrite Hm2 in Hs.
  rewrite (Qmult_inv_r z Hz) in Hs.
  rewrite (Qmult_1_l X) in Hs. rewrite (Qmult_1_l Y) in Hs.
  exact Hs.
Qed.

(* ===== 桥核（除法自由形，对 m 归纳） =====
   N²·altsum(S m) == b^n·q·q^n·A_m，其中 A_m = eval(ai(qmp^n · sin_qp m) n) q。 *)
Lemma lw0_pitB_bridge_aux : forall (n : nat) (b q : Q) (m : nat),
  q_fact n * (q_fact n * altsum (lw0_Wb b q n) (Datatypes.S m))
  == q_pow b n * (q * (q_pow q n
       * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n) (lw0_sin_qp m)) n) q)).
Proof.
  intros n b q. induction m as [|m IH].
  - unfold altsum. cbn [altsum_acc].
    change (lw0_sin_qp 0) with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q))).
    rewrite (lw0_pitB_ai_mul_cons0 (lw0_pi_qminus_pow q n)
               (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q)) n q).
    rewrite (lw0_pitB_ai_mul_cons1 (lw0_pi_qminus_pow q n)
               (q_pow (-1) 0 / q_fact 1)%Q (Datatypes.S n) q).
    rewrite (lw0_pitB_E n q (Datatypes.S n)).
    unfold lw0_Wb.
    replace (n + 2 * 0 + 1)%nat with (Datatypes.S n) by lia.
    replace (n + Datatypes.S n + 1)%nat with (2 * n + 2 * 0 + 2)%nat by lia.
    rewrite (q_fact_succ n).
    replace (2 * 0 + 1)%nat with 1%nat by lia.
    change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    change (q_fact 0) with 1%Q.
    change (q_pow (-1) 0) with 1%Q.
    replace (2 * n + 2 * 0 + 2)%nat with (Datatypes.S n + Datatypes.S n)%nat by lia.
    rewrite (lw0_pitB_q_pow_add q (Datatypes.S n) (Datatypes.S n)).
    rewrite (lw0_q_pow_S q n).
    unfold Qdiv. rewrite ?Qinv_mult_distr.
    assert (Hn0 : ~ q_fact n == 0%Q).
    { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
      symmetry. exact Hc. }
    assert (Hc1 : (q_pow b n * (q * q_pow q n * (q * q_pow q n)) *
                    ((Z.of_nat (S n) # 1) * q_fact n) *
                    (/ q_fact n * (/ (Z.of_nat 1 # 1) * / 1)
                       * / q_fact (S n + S n)))%Q
                  == (q_pow b n * (q * q_pow q n * (q * q_pow q n)) *
                      (Z.of_nat (S n) # 1) * (q_fact n * / q_fact n)
                      * (/ (Z.of_nat 1 # 1) * / 1) * / q_fact (S n + S n))%Q)
      by ring.
    rewrite Hc1. rewrite (Qmult_inv_r (q_fact n) Hn0).
    ring.
  - rewrite (lw0_pitB_altsum_S (lw0_Wb b q n) (Datatypes.S m)).
    assert (Hsp : (q_fact n * (q_fact n
                    * (altsum (lw0_Wb b q n) (Datatypes.S m)
                       + q_pow (-1) (Datatypes.S m) * lw0_Wb b q n (Datatypes.S m))))%Q
                  == (q_fact n * (q_fact n * altsum (lw0_Wb b q n) (Datatypes.S m))
                      + q_fact n * (q_fact n * (q_pow (-1) (Datatypes.S m) * lw0_Wb b q n (Datatypes.S m))))%Q)
      by ring.
    rewrite Hsp. rewrite IH.
    change (lw0_sin_qp (Datatypes.S m))
      with (lw0_sin_aux m (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S m)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
                 (@nil Q)))).
    rewrite (lw0_pitB_ai_mul_sin_aux (lw0_pi_qminus_pow q n) m
               (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S m)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
                     (@nil Q))) n q).
    replace (n + Datatypes.S (Datatypes.S (2 * m)))%nat with (n + 2 * m + 2)%nat by lia.
    rewrite (lw0_pitB_ai_mul_cons0 (lw0_pi_qminus_pow q n)
               (cons (q_pow (-1) (Datatypes.S m)
                       / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
                  (@nil Q)) (n + 2 * m + 2)%nat q).
    rewrite (lw0_pitB_ai_mul_cons1 (lw0_pi_qminus_pow q n)
               (q_pow (-1) (Datatypes.S m)
                / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
               (Datatypes.S (n + 2 * m + 2)) q).
    rewrite (lw0_pitB_E n q (Datatypes.S (n + 2 * m + 2))).
    replace (n + Datatypes.S (n + 2 * m + 2) + 1)%nat
      with (2 * n + 2 * Datatypes.S m + 2)%nat by lia.
    unfold lw0_Wb.
    replace (2 * Datatypes.S m + 1)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
    replace (n + 2 * Datatypes.S m + 1)%nat
      with (Datatypes.S (n + 2 * m + 2))%nat by lia.
    rewrite (q_fact_succ (n + 2 * m + 2)).
    replace (2 * n + 2 * Datatypes.S m + 2)%nat
      with (Datatypes.S n + (n + Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%nat by lia.
    rewrite (lw0_pitB_q_pow_add q (Datatypes.S n)
               (n + Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
    rewrite (lw0_pitB_q_pow_add q n
               (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
    change (q_pow q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))
      with (q * q_pow q (Datatypes.S (Datatypes.S (2 * m))))%Q.
    rewrite (lw0_q_pow_S q n).
    unfold Qdiv. rewrite ?Qinv_mult_distr.
    assert (Hn0 : ~ q_fact n == 0%Q).
    { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
      symmetry. exact Hc. }
    assert (Hc1 : (q_fact n *
                    (q_fact n *
                     (q_pow (-1) (S m) *
                      (q_pow b n * (q * q_pow q n * (q_pow q n * (q * q_pow q (S (S (2 * m)))))) *
                       ((Z.of_nat (S (n + 2 * m + 2)) # 1) * q_fact (n + 2 * m + 2)) *
                       (/ q_fact n * / q_fact (S (S (S (2 * m)))) *
                        / q_fact (S n + (n + S (S (S (2 * m))))))))))%Q
                  == (q_fact n *
                      (q_pow (-1) (S m) *
                       (q_pow b n * (q * q_pow q n * (q_pow q n * (q * q_pow q (S (S (2 * m)))))) *
                        (Z.of_nat (S (n + 2 * m + 2)) # 1) * q_fact (n + 2 * m + 2) *
                        (q_fact n * / q_fact n) * / q_fact (S (S (S (2 * m)))) *
                        / q_fact (S n + (n + S (S (S (2 * m))))))))%Q)
      by ring.
    rewrite Hc1. rewrite (Qmult_inv_r (q_fact n) Hn0).
    ring.
Qed.

(* ===== 主桥（语句面为钉定形，禁改） ===== *)
Lemma lw0_pitB_bridge : forall (m : nat) (b q : Q) (n : nat),
  altsum (lw0_Wb b q n) (Datatypes.S m)
  == 1 / q_fact n * lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q.
Proof.
  intros m b q n.
  assert (Hn0 : ~ q_fact n == 0%Q).
  { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
    symmetry. exact Hc. }
  unfold lw0_niven_f.
  rewrite (lw0_qp_pair_scalar_l (q_pow b n / q_fact n)
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) (lw0_sin_qp m) q).
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval
            (cons 0
               (lw0_qp_ai
                  (qpoly_mul
                     (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) (lw0_sin_qp m)) 0)) q)
    with (0 + q * qpoly_eval
            (lw0_qp_ai
               (qpoly_mul
                  (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) (lw0_sin_qp m)) 0) q).
  rewrite (lw0_pitB_ai_mulA (lw0_pi_mono n) (lw0_pi_qminus_pow q n) (lw0_sin_qp m) 0 q).
  rewrite (lw0_pitB_ai_monoL n (qpoly_mul (lw0_pi_qminus_pow q n) (lw0_sin_qp m)) 0 q).
  replace (0 + n)%nat with n by lia.
  assert (Haux := lw0_pitB_bridge_aux n b q m).
  assert (Hpack : (q_fact n * (q_fact n
                   * (1 / q_fact n
                      * (q_pow b n / q_fact n
                         * (0 + q * (q_pow q n
                              * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                             (lw0_sin_qp m)) n) q))))))%Q
                  == (q_pow b n * (q * (q_pow q n
                       * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                      (lw0_sin_qp m)) n) q)))%Q).
  { unfold Qdiv.
    assert (Hm : (q_fact n * (q_fact n
                  * (1 * Qinv (q_fact n)
                     * (q_pow b n * Qinv (q_fact n)
                        * (0 + q * (q_pow q n
                             * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                            (lw0_sin_qp m)) n) q))))))%Q
                 == (q_fact n * Qinv (q_fact n)
                     * (q_fact n * Qinv (q_fact n)
                        * (q_pow b n * (q * (q_pow q n
                             * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                            (lw0_sin_qp m)) n) q)))))%Q) by ring.
    rewrite Hm.
    assert (Hz1 : (q_fact n * / q_fact n)%Q == 1%Q)
      by exact (Qmult_inv_r (q_fact n) Hn0).
    rewrite Hz1. rewrite ?Qmult_1_l. reflexivity. }
  rewrite <- Hpack in Haux.
  apply (lw0_pitB_Qeq_cancel_l (q_fact n) _ _ Hn0).
  apply (lw0_pitB_Qeq_cancel_l (q_fact n) _ _ Hn0).
  exact Haux.
Qed.


(* ---------- _tlw245 (beta) Beta 块（已证定稿版）----------
   出处：β 块已证定稿版（pwi 转录＋随块 35 锚并入）。
   基座：attn/_tlw282_working.v（② 系 dc2ecc8f＋w0_lt1 活体 +157）md5 02910c6f88313ecd8ee202b393dc2231（7,326 行）。
   插入锚：Print Assumptions lw0_pitB_ibp_dbl.（L6550）之后、主语句备档 banner（L7101）之前同缝（282 坐标新表）；命名空间隔离＝β 各名全前缀实名；lw0_qp_pair 曾与 ② 底同名件（L2896）撞名，裁定 (a) 去重——删块内副本（原块 L1530-1532），块内使用面与 PA 锚改指 ② 底供件（qpoly≡QPoly 记号别名同源，282 底 L48/L695 三证钉定），去重后全件该名声明唯一＝真零冲突。
   幂等守卫依赖：GUARD_MARK 串（_tlw245 (beta) Beta 块）须在本块头注内逐字出现。 *)

(* ================= §6.6 末段 ④ B 车道三项收敛前置面================= *)
(* 清障记录：geomscale 的 Hznat 残点经 stdlib Qround                                       *)
(* Qceiling_resp_le（Qceiling 单调）＋Qceiling_Z 清障；γ 对应四件与    *)
(* pwi 配对尾引擎续补于本块。红线与工艺坑实录在卷。                                       *)
(* 出处：B 车道三项收敛前置件块；基座＝引擎块整件，                                       *)
(* 基线快照核验在卷（快照与源面逐字节全等）。                                             *)
(* 插入锚＝引擎块之后、主语句备档区之前。命名空间 lw0_pitB_conv_ 全隔离                   *)
(* （与 (α) 桥面 lw0_pitB_* 其余名、引擎件 lw0_pitB_ibp_dbl 零撞名）。                     *)
(* 使命：三项收敛装配的前置件——σ/γ 截断对象自身的实层极限引理，与 (α) 的确切措辞解耦：     *)
(*   （一）σ_M → sin 发散控：sin 截断尾逐点阶乘占优＋eps 消逝见证（sigT 面，仿               *)
(*         lw0_Wb_vanish 形）；（二）γ_M 方向控：cos 侧同型本体（端点 −1 衔接留              *)
(*         (β) 主装配，经 lw0_cos_endpoint_transport 于 Real 层取用）；（三）配对尾项 → 0：    *)
(*         <f, g_M>_q 型配对尾的 pwi 权重引擎＋阶乘占优上界＋eps 见证（τ_M 权重义务形        *)
(*         已钉：QleT' (pwi τ_M 0 c) (Wg * t_M)，(β) 主装配按此实例化）。                        *)
(* 层纪律：三条全无 π 前提（纯收敛分析，恒真）；π 前提只经 lw0_sin/cos_endpoint_transport   *)
(* 于 Real 层取用；禁任何 Q 层 sin_Q(a/b)==0 形。语句面自决权已行使：基座 σ/γ 替身层         *)
(* （lw0_sin_qp/lw0_cos_qp＋sin_partial/cos_partial/sin_term/cos_term）核验在件，零新替身。  *)
(* 数值验算先行（vm_compute，q=1 锚）：sin_partial 14 1 ≈ 0.8414709848，                     *)
(* cos_partial 14 1 ≈ 0.5403023059；尾差 |σ14−σM|(1) 对 M=0..5 实测压缩，对                  *)
(* 2/(2M+1)! 全过；cos 侧同构过；<f_2, σ14−σM>_1 实测对 60/(2M+1)! 全过                      *)
(* （_tlw193_scratch.v 十九断言一炮绿，实录 _tlw193_scratch_numbers.log）。                  *)
(* 假命题一分钟杀实录：「σ_M(1)→0」为假（真极限 sin 1），已按 Cauchy 尾形改述；              *)
(* 「γ_M→−1 无前提形」为假（γ_M(1)→cos 1），本体取 cos 收敛、−1 衔接留 (β)。                *)
(* 工艺红线（实测坑）：QleT' 目标上禁 rewrite（delta 展开吃掉匹配）——一律            *)
(* Qeq 目标改写／Qle 目标改写（库先例形）／qeq_leT'＋eq_rect 项级迁移。                       *)
(* 红线照旧：Qeq-rewrite 打不透 Id 封装走 eq-rewrite/exact 项级；%Q/%nat/Datatypes.S；       *)
(* Qabs 真=Z.abs、Qmax=gmax Qcompare。禁承认词面占位。                                       *)

(* ---------- 零件面：幂标尺与几何标尺 ---------- *)

Lemma lw0_pitB_conv_lw0_succ : forall n : nat,
  QeqT (lw0_q_of_nat (Datatypes.S n)) (1 + lw0_q_of_nat n)%Q.
Proof.
  intro n. apply qeq_imp_qeqT. unfold lw0_q_of_nat.
  assert (Ez : Z.of_nat (Datatypes.S n) = (1 + Z.of_nat n)%Z).
  { change (Datatypes.S n) with (1 + n)%nat. rewrite Nat2Z.inj_add. reflexivity. }
  rewrite Ez. apply lw0_Qmake_succ.
Qed.

Lemma lw0_pitB_conv_mult_le_l : forall (p n m : Q),
  QleT' n m -> QleT' 0 p -> QleT' (p * n) (p * m).
Proof.
  intros p n m Hn H0. apply Qle_to_QleT'.
  assert (E : (p * n)%Q == (n * p)%Q) by ring.
  assert (E2 : (p * m)%Q == (m * p)%Q) by ring.
  rewrite E, E2. apply Qmult_le_compat_r;
    [ exact (QleT'_to_Qle _ _ Hn) | exact (QleT'_to_Qle _ _ H0) ].
Qed.

Lemma lw0_pitB_conv_pow2_ge : forall L : nat,
  QleT' (lw0_q_of_nat (Datatypes.S L)) (q_pow (2#1) L).
Proof.
  intro L. induction L as [| L IH].
  - change (q_pow (2#1) 0) with 1%Q.
    change (lw0_q_of_nat 1) with (1#1)%Q.
    apply qleT'_refl.
  - apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S L)))
                       (1 + lw0_q_of_nat (Datatypes.S L))%Q
                       (q_pow (2#1) (Datatypes.S L))).
    + apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (Datatypes.S L)))
                      (1 + lw0_q_of_nat (Datatypes.S L))%Q
                      (qeqT_imp_qeq _ _ (lw0_pitB_conv_lw0_succ (Datatypes.S L)))).
    + apply Qle_to_QleT'.
      apply (Qle_trans (1 + lw0_q_of_nat (Datatypes.S L))%Q
                       (q_pow (2#1) L + q_pow (2#1) L)%Q
                       (q_pow (2#1) (Datatypes.S L))).
      * apply (Qle_trans (1 + lw0_q_of_nat (Datatypes.S L))%Q
                         (lw0_q_of_nat (Datatypes.S L) + q_pow (2#1) L)%Q _).
        -- apply Qplus_le_compat.
           ** exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one L)).
           ** exact (QleT'_to_Qle _ _ IH).
        -- apply Qplus_le_compat.
           ** exact (QleT'_to_Qle _ _ IH).
           ** apply Qle_refl.
      * change (q_pow (2#1) (Datatypes.S L)) with ((2#1) * q_pow (2#1) L)%Q.
        assert (Ec22 : QeqT (2#1)%Q (1%Q + 1%Q))
          by (unfold QeqT; cbn; reflexivity).
        rewrite (qeqT_imp_qeq _ _ Ec22).
        rewrite (Qmult_plus_distr_l 1%Q 1%Q (q_pow (2#1) L)).
        rewrite (Qmult_1_l (q_pow (2#1) L)).
        apply Qle_refl.
Qed.

Lemma lw0_pitB_conv_half_le1 : forall L : nat, QleT' (q_pow (1#2) L) 1%Q.
Proof.
  intro L. induction L as [| L IH].
  - change (q_pow (1#2) 0) with 1%Q. apply qleT'_refl.
  - apply (qleT'_trans (q_pow (1#2) (Datatypes.S L)) ((1#2) * 1%Q) 1%Q).
    + change (q_pow (1#2) (Datatypes.S L)) with ((1#2) * q_pow (1#2) L)%Q.
      apply (lw0_pitB_conv_mult_le_l (1#2) (q_pow (1#2) L) 1%Q).
      * exact IH.
      * unfold QleT'. reflexivity.
    + unfold QleT'. reflexivity.
Qed.

Lemma lw0_pitB_conv_half_mono : forall a b : nat, (b <= a)%nat ->
  QleT' (q_pow (1#2) a) (q_pow (1#2) b).
Proof.
  intros a b Hba.
  assert (E1 : a%nat = (b + (a - b))%nat).
  { rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hba. }
  assert (Eadd : q_pow (1#2) (b + (a - b))%nat
                 == q_pow (1#2) b * q_pow (1#2) (a - b)) by apply lw0_q_pow_add.
  apply (eq_rect (b + (a - b))%nat (fun n0 : nat => QleT' (q_pow (1#2) n0) (q_pow (1#2) b))).
  - apply (qleT'_trans (q_pow (1#2) (b + (a - b))%nat)
                       (q_pow (1#2) (a - b) * q_pow (1#2) b)
                       (q_pow (1#2) b)).
    + apply qeq_leT'. rewrite Eadd. ring.
    + apply Qle_to_QleT'.
      apply (Qle_trans (q_pow (1#2) (a - b) * q_pow (1#2) b)
                       (1%Q * q_pow (1#2) b) (q_pow (1#2) b)).
      * assert (H02T : QleT' 0 (1#2)%Q) by (unfold QleT'; reflexivity).
        apply (Qmult_le_compat_r (q_pow (1#2) (a - b)) 1%Q (q_pow (1#2) b));
          [ exact (QleT'_to_Qle _ _ (lw0_pitB_conv_half_le1 (a - b)))
          | apply q_pow_nonneg; exact (QleT'_to_Qle _ _ H02T) ].
      * assert (E1l : (1%Q * q_pow (1#2) b)%Q == (q_pow (1#2) b)%Q) by ring.
        rewrite E1l. apply Qle_refl.
  - exact (eq_sym E1).
Qed.

(* 阶乘占优泛化（lw0_pi_bound_dominated_odd 型去 π 化）。 *)
Lemma lw0_pitB_conv_pow_fact_domin : forall (k0 k : nat) (c : Q),
  QleT' 1 c ->
  QleT' (q_pow c k0) (q_fact k0) ->
  QleT' c (lw0_q_of_nat (Datatypes.S k0)) ->
  QleT' (q_pow c (k0 + 2 * k)%nat) (q_fact (k0 + 2 * k)%nat).
Proof.
  intros k0 k c H1 Hbase Hc.
  induction k as [| k IH].
  - assert (E0 : (k0 + 2 * 0)%nat = k0) by apply Nat.add_0_r.
    exact (eq_rect_r (fun n0 : nat => QleT' (q_pow c n0) (q_fact n0)) Hbase E0).
  - assert (E1 : (k0 + 2 * Datatypes.S k)%nat
                 = Datatypes.S (Datatypes.S (k0 + 2 * k))%nat)
      by (rewrite Nat.mul_succ_r, Nat.add_assoc;
          rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
    assert (Hgoal : QleT' (q_pow c (Datatypes.S (Datatypes.S (k0 + 2 * k))%nat))
                          (q_fact (Datatypes.S (Datatypes.S (k0 + 2 * k))%nat))).
    { apply (lw0_q_pow_fact_step2 c (k0 + 2 * k)%nat).
      - exact H1.
      - assert (E2 : (Datatypes.S k0 + 2 * k)%nat = (Datatypes.S (k0 + 2 * k))%nat) by lia.
        apply (qleT'_trans c (lw0_q_of_nat (Datatypes.S k0))
                           (lw0_q_of_nat (Datatypes.S (k0 + 2 * k))%nat)).
        + exact Hc.
        + exact (eq_rect (Datatypes.S k0 + 2 * k)%nat
                    (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S k0))
                                           (lw0_q_of_nat n0))
                    (lw0_q_of_nat_le_add (Datatypes.S k0) (2 * k)%nat)
                    (Datatypes.S (k0 + 2 * k))%nat E2).
      - exact IH. }
    exact (eq_rect_r (fun n0 : nat => QleT' (q_pow c n0) (q_fact n0)) Hgoal E1).
Qed.

(* 几何消逝标尺：0 ≤ B、0 < eps 时存在 L 使 B ≤ 2^L·eps。 *)
Lemma lw0_pitB_conv_div_mul_cancel : forall (a eps : Q),
  QltT 0 eps -> QeqT (a / eps * eps) a.
Proof.
  intros a eps Heps. apply qeq_imp_qeqT.
  assert (Hne : eps == 0%Q -> False) by (apply qltT_not_eq_zero; exact Heps).
  unfold Qdiv.
  transitivity (a * (eps * / eps))%Q.
  - rewrite <- (Qmult_assoc a%Q (/ eps)%Q eps%Q).
    apply (Qmult_comp a%Q a%Q (Qeq_refl a%Q)).
    apply Qmult_comm.
  - rewrite (Qmult_inv_r eps Hne). apply (Qmult_1_r a%Q).
Qed.

Lemma lw0_pitB_conv_geomscale : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun L : nat => QleT' B (q_pow (2#1) L * eps)).
Proof.
  intros B eps HB Heps.
  assert (HBe : Qle 0 (B / eps)).
  { apply Qmult_le_0_compat;
      [ exact (QleT'_to_Qle _ _ HB)
      | apply Qinv_le_0_compat; apply Qlt_le_weak; apply QltT_to_Qlt; exact Heps ]. }
  assert (Hznat : (0 <= Z.succ (Qceiling (B / eps)))%Z).
  { assert (Hz0 : Qceiling 0%Q = 0%Z) by reflexivity.
    pose proof (Qceiling_resp_le 0%Q (B / eps) HBe) as Hm.
    rewrite Hz0 in Hm. apply Z.le_le_succ_r. exact Hm. }
  assert (HL2 : QleT' ((Qceiling (B / eps) + 1)#1)
                      (lw0_q_of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
  { unfold lw0_q_of_nat.
    assert (EZ : Z.of_nat (Z.to_nat (Z.succ (Qceiling (B / eps))))
                 = (Qceiling (B / eps) + 1)%Z).
    { rewrite Z2Nat.id by exact Hznat. symmetry. apply Z.add_1_r. }
    apply (qeq_leT' ((Qceiling (B / eps) + 1)#1)
                    ((Z.of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))))#1)).
    rewrite EZ. apply Qeq_refl. }
  exists (Z.to_nat (Z.succ (Qceiling (B / eps)))).
  assert (Hceil : Qle (B / eps) ((Qceiling (B / eps))#1)) by apply Qle_ceiling.
  apply (qleT'_trans B (B / eps * eps)
                     (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps)).
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_div_mul_cancel B eps Heps)).
    apply Qle_refl.
  - apply (qleT'_trans (B / eps * eps) (((Qceiling (B / eps))#1) * eps)
                       (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps)).
    + apply Qle_to_QleT'. apply Qmult_le_compat_r;
        [ exact Hceil | apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps) ].
    + apply (qleT'_trans (((Qceiling (B / eps))#1) * eps)
                         (((Qceiling (B / eps) + 1)#1) * eps)
                         (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps)).
      * apply Qle_to_QleT'. apply Qmult_le_compat_r.
        -- unfold Qle. cbn [Qnum Qden]. rewrite ?Z.mul_1_r.
           apply Z.le_succ_diag_r.
        -- apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps).
      * apply (qleT'_trans (((Qceiling (B / eps) + 1)#1) * eps)
                           (lw0_q_of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps) _).
        -- apply Qle_to_QleT'. apply Qmult_le_compat_r;
             [ exact (QleT'_to_Qle _ _ HL2)
             | apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps) ].
        -- apply Qle_to_QleT'. apply Qmult_le_compat_r.
           ++ apply (Qle_trans
                        (lw0_q_of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))))
                        (lw0_q_of_nat (S (Z.to_nat (Z.succ (Qceiling (B / eps))))))
                        (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
            ** exact (QleT'_to_Qle _ _ (lw0_q_of_nat_le_succ (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
            ** exact (QleT'_to_Qle _ _ (lw0_pitB_conv_pow2_ge (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
           ++ apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps).
Qed.

(* ---------- 零件面：绝对值代数 ---------- *)

Lemma lw0_pitB_conv_qabs_pow : forall (x : Q) (k : nat),
  QeqT (Qabs (q_pow x k)) (q_pow (Qabs x) k).
Proof.
  intros x k. apply qeq_imp_qeqT. induction k as [| k IH].
  - change (q_pow x 0) with 1%Q. change (q_pow (Qabs x) 0) with 1%Q.
    simpl. reflexivity.
  - rewrite (q_pow_succ x k), (q_pow_succ (Qabs x) k), Qabs_Qmult, IH. reflexivity.
Qed.

Lemma lw0_pitB_conv_m1_cases : forall j : nat,
  sigT (fun b : bool => QeqT (q_pow (-1)%Q j) (if b then 1%Q else (-1)%Q)).
Proof.
  intro j. induction j as [| j IH].
  - exists true. unfold QeqT. cbn. reflexivity.
  - destruct IH as [b Hb]. exists (negb b). apply qeq_imp_qeqT.
    pose proof (qeqT_imp_qeq _ _ Hb) as Hb'.
    rewrite (q_pow_succ (-1)%Q j). destruct b.
    + rewrite Hb'. reflexivity.
    + rewrite Hb'. reflexivity.
Qed.

Lemma lw0_pitB_conv_t_nonneg : forall (c : Q) (k : nat),
  QleT' 0 c -> QleT' 0 (q_pow c k / q_fact k).
Proof.
  intros c k Hc. apply Qle_to_QleT'.
  apply Qmult_le_0_compat.
  - apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hc).
  - apply Qinv_le_0_compat. apply (Qlt_le_weak 0). apply q_fact_pos.
Qed.

(* ---------- 首舍项减半步（泛化 N 形：2c² ≤ (N+1)(N+2)；sin/t_vanish 奇数梯按 N=S(2j) 取用） ---------- *)

Lemma lw0_pitB_conv_tstep : forall (c : Q) (N : nat),
  QleT' 0 c ->
  QleT' (2 * q_pow c 2)
        (lw0_q_of_nat (Datatypes.S N)
         * lw0_q_of_nat (Datatypes.S (Datatypes.S N))) ->
  QleT' (q_pow c (Datatypes.S (Datatypes.S N)) / q_fact (Datatypes.S (Datatypes.S N)))
        ((1#2) * (q_pow c N / q_fact N)).
Proof.
  intros c N Hc0 H.
  set (D := lw0_q_of_nat (Datatypes.S N)
             * lw0_q_of_nat (Datatypes.S (Datatypes.S N))) in *.
  assert (Hstep : q_fact (Datatypes.S (Datatypes.S N)) == D * q_fact N).
  { unfold D. rewrite (lw0_q_fact_step2 N). ring. }
  assert (Hpos : QltT 0 D).
  { unfold D. apply Qlt_to_QltT. apply Qmult_lt_0_compat;
      [ unfold Qlt, lw0_q_of_nat; cbn; lia | unfold Qlt, lw0_q_of_nat; cbn; lia ]. }
  assert (HDne : D == 0%Q -> False) by (apply qltT_not_eq_zero; exact Hpos).
  assert (HDinv : D * / D == 1%Q) by (apply Qmult_inv_r; exact HDne).
  assert (Hinvpos : QleT' 0 (/ D)).
  { apply Qle_to_QleT'. apply Qinv_le_0_compat.
    apply (Qlt_le_weak 0). exact (QltT_to_Qlt _ _ Hpos). }
  assert (Hfactor : (q_pow c (Datatypes.S (Datatypes.S N)) / q_fact (Datatypes.S (Datatypes.S N)))%Q
                    == (c * c * / D) * (q_pow c N / q_fact N)).
  { rewrite Hstep.
    rewrite (q_pow_succ c (Datatypes.S N)), (q_pow_succ c N).
    unfold Qdiv.
    rewrite (Qinv_mult_distr D (q_fact N)).
    ring. }
  assert (H2ltT : QltT 0 (2#1)%Q) by (unfold QltT, Qlt_bool; reflexivity).
  assert (Hkey : QleT' (c * c * / D) (1#2)).
  { apply Qle_to_QleT'.
    apply (proj1 (Qmult_le_r (c * c * / D) (1#2) (2#1) (QltT_to_Qlt _ _ H2ltT))).
    assert (Er : (c * c * / D * 2%Q)%Q == (2 * c * c * / D)%Q) by ring.
    assert (E2 : q_pow c 2 == c * c)
      by (rewrite (q_pow_succ c 1), (q_pow_succ c 0);
          change (q_pow c 0) with 1%Q; ring).
    assert (H2c2 : Qle (2 * c * c) D).
    { pose proof (QleT'_to_Qle _ _ H) as Hq.
      rewrite E2 in Hq.
      assert (E23 : (2 * (c * c))%Q == (2 * c * c)%Q) by ring.
      rewrite E23 in Hq. exact Hq. }
    apply (Qle_trans (c * c * / D * 2%Q) (2 * c * c * / D) ((1#2) * 2%Q)).
    - rewrite Er. apply Qle_refl.
    - apply (Qle_trans (2 * c * c * / D) (D * / D) ((1#2) * 2%Q)).
      + apply Qmult_le_compat_r.
        * exact H2c2.
        * exact (QleT'_to_Qle _ _ Hinvpos).
      + assert (Eone : (D * / D)%Q == ((1#2) * 2%Q)%Q).
        { rewrite HDinv. reflexivity. }
        rewrite Eone. apply Qle_refl. }
  apply (qleT'_trans (q_pow c (Datatypes.S (Datatypes.S N)) / q_fact (Datatypes.S (Datatypes.S N)))
                     ((c * c * / D) * (q_pow c N / q_fact N))
                     ((1#2) * (q_pow c N / q_fact N))).
  - apply qeq_leT'. exact Hfactor.
  - apply Qle_to_QleT'. apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hkey).
    + exact (QleT'_to_Qle _ _ (lw0_pitB_conv_t_nonneg c N Hc0)).
Qed.

(* ---------- 泛型尾归纳（sin/cos 共享引擎） ---------- *)

Lemma lw0_pitB_conv_tail_gen : forall (P Pd w : nat -> Q) (D M : nat),
  (forall n : nat, P (Datatypes.S n) == P n + Pd n) ->
  (forall n : nat, Qabs (Pd n) == w n) ->
  (forall n : nat, QleT' 0 (w n)) ->
  (forall j : nat, (M <= j)%nat -> QleT' (w (Datatypes.S j)) ((1#2) * w j)) ->
  QleT' (Qabs (P (M + D)%nat - P M)) (2 * w M).
Proof.
  intros P Pd w D.
  induction D as [| D IH]; intros M Hstep Habs Hw0 Hhalf.
  - assert (E0 : (M + 0)%nat = M) by apply Nat.add_0_r.
    assert (Hbase : QleT' (Qabs (P M - P M)) (2 * w M)).
    { apply (qleT'_trans (Qabs (P M - P M)) 0%Q (2 * w M)).
      - apply qeq_leT'. apply q_abs_self_zero.
      - apply Qle_to_QleT'. apply Qmult_le_0_compat.
        + apply (Qlt_le_weak 0%Q (2#1)%Q).
          apply (QltT_to_Qlt 0%Q (2#1)%Q). unfold QltT. reflexivity.
        + exact (QleT'_to_Qle _ _ (Hw0 M)). }
    exact (eq_rect_r (fun n0 : nat => QleT' (Qabs (P n0 - P M)) (2 * w M)) Hbase E0).
  - assert (E1 : (M + Datatypes.S D)%nat = (Datatypes.S M + D)%nat)
      by (rewrite Nat.add_succ_r, Nat.add_succ_l; reflexivity).
    assert (Hmain : QleT' (Qabs (P (Datatypes.S M + D)%nat - P M)) (2 * w M)).
    { assert (Hz : (P (Datatypes.S M + D)%nat - P M)%Q
                   == Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))).
      { rewrite (Hstep M). ring. }
      apply (qleT'_trans (Qabs (P (Datatypes.S M + D)%nat - P M))
                         (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
                         (2 * w M)).
      - apply (qeq_leT' (Qabs (P (Datatypes.S M + D)%nat - P M))
                        (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))).
        rewrite Hz. apply Qeq_refl.
      - assert (Htri : Qle (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
                           (Qabs (Pd M) + Qabs (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
          by apply Qabs_triangle.
        assert (Hih := IH (Datatypes.S M) Hstep Habs Hw0
                          (fun j1 Hj1 => Hhalf j1
                             (Nat.le_trans M (Datatypes.S M) j1
                                (Nat.le_succ_diag_r M) Hj1))).
        apply (qleT'_trans (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
                           (w M + 2 * w (Datatypes.S M)) (2 * w M)).
        + apply Qle_to_QleT'.
          apply (Qle_trans _ (Qabs (Pd M) + Qabs (P (Datatypes.S M + D)%nat - P (Datatypes.S M))) _).
          * exact Htri.
          * apply Qplus_le_compat.
            -- rewrite (Habs M). apply Qle_refl.
            -- exact (QleT'_to_Qle _ _ Hih).
        + apply Qle_to_QleT'.
          apply (Qle_trans (w M + 2 * w (Datatypes.S M))
                           (w M + w M) (2 * w M)).
          * apply Qplus_le_compat.
            -- apply Qle_refl.
            -- apply QleT'_to_Qle.
               apply (qleT'_trans (2 * w (Datatypes.S M))
                                  (2%Q * ((1#2) * w M))
                                  (w M)).
               ++ apply (lw0_pitB_conv_mult_le_l 2%Q (w (Datatypes.S M))
                           ((1#2) * w M) (Hhalf M (Nat.le_refl M))).
                  unfold QleT'. reflexivity.
               ++ apply (qeq_leT' (2%Q * ((1#2) * w M)) (w M)).
                  (* Qmult_comp 终形勘定：Instance Proper (Qeq==>Qeq==>Qeq) Qmult，
                     四显参 x x' y y' 返回 x==x' -> y==y' -> x*y==x'*y'。常数腿走 QeqT 闭项证书。 *)
                  assert (Ec2h : QeqT (2%Q * (1#2))%Q 1%Q)
                    by (unfold QeqT; cbn; reflexivity).
                  rewrite (Qmult_assoc 2%Q (1#2) (w M)).
                  rewrite (qeqT_imp_qeq _ _ Ec2h).
                  apply (Qmult_1_l (w M)).
          * apply QleT'_to_Qle.
            apply (qeq_leT' (w M + w M) (2 * w M)).
            assert (Ec2q : QeqT 2%Q (1%Q + 1%Q))
              by (unfold QeqT; cbn; reflexivity).
            rewrite (qeqT_imp_qeq _ _ Ec2q).
            rewrite (Qmult_plus_distr_l 1%Q 1%Q (w M)).
            rewrite (Qmult_1_l (w M)).
            apply Qeq_refl.
    }
    exact (eq_rect_r (fun n0 : nat => QleT' (Qabs (P n0 - P M)) (2 * w M)) Hmain E1).
Qed.

(* ---------- 引理一：sin 实例（截断尾阶乘占优） ---------- *)

Lemma lw0_pitB_conv_sin_term_abs : forall (j : nat) (q : Q),
  QeqT (Qabs (sin_term j q))
       (q_pow (Qabs q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).
Proof.
  intros j q. apply qeq_imp_qeqT. unfold sin_term, Qdiv.
  rewrite Qabs_Qmult, Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_qabs_pow q (Datatypes.S (2 * j)))).
  rewrite (lw0_Qabs_pos_eq (Qinv (q_fact (Datatypes.S (2 * j)))))
    by (apply Qle_to_QleT'; apply Qinv_le_0_compat;
        apply (Qlt_le_weak 0%Q); apply q_fact_pos).
  destruct (lw0_pitB_conv_m1_cases j) as [b Hc]. destruct b;
    rewrite (qeqT_imp_qeq _ _ Hc); simpl; ring.
Qed.

Lemma lw0_pitB_conv_sin_tail : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (sin_partial (M + D) q - sin_partial M q))
        (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
Proof.
  intros q M D Hr.
  assert (Hqnn : QleT' 0 (Qabs q))
    by (apply Qle_to_QleT'; apply Qabs_nonneg).
  (* sin_partial (S m) = sin_partial m + sin_term (S m)：Pd/w 面整体 S 移位（§六.1 配方）。 *)
  assert (Hhalf : forall j : nat, (M <= j)%nat ->
           QleT' (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))
                   / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j))))
                 ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S j))
                            / q_fact (Datatypes.S (2 * Datatypes.S j))))).
  { intros j Hj.
    (* 2*S 归一到 2*j 纯净语法（add 对符号变量不化约，禁跨语法跳） *)
    assert (E2j : (2 * Datatypes.S j)%nat = Datatypes.S (Datatypes.S (2 * j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    assert (E2j2 : (2 * Datatypes.S (Datatypes.S j))%nat
                   = Datatypes.S (Datatypes.S (2 * Datatypes.S j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 1).
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2j2, E2j.
    apply (lw0_pitB_conv_tstep (Qabs q)
                 (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))).
    - exact Hqnn.
    - (* Hr：2q^2 <= (2j+1)(2j+2) 上移两跳至 (2j+4)(2j+5)（纯 2*j 语法） *)
      apply (qleT'_trans (2 * q_pow (Qabs q) 2)
                         (lw0_q_of_nat (Datatypes.S (2 * j))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
      + exact (Hr j Hj).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * j)))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (2 * j)))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j)))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
                   --- apply lw0_q_of_nat_le_succ.
                   --- apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg.
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
                   --- apply lw0_q_of_nat_le_succ.
                   --- apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg. }
  assert (HhalfM : QleT' (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S M))
                            / q_fact (Datatypes.S (2 * Datatypes.S M)))
                         ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                    / q_fact (Datatypes.S (2 * M))))).
  { assert (E2M : (2 * Datatypes.S M)%nat = Datatypes.S (Datatypes.S (2 * M))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * M) 1).
      rewrite (Nat.add_succ_r (2 * M) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2M.
    apply (lw0_pitB_conv_tstep (Qabs q) (Datatypes.S (2 * M))).
    - exact Hqnn.
    - (* Hr M：2q^2 <= (2M+1)(2M+2) 上移一跳至 (2M+2)(2M+3)（纯 2*M 语法） *)
      apply (qleT'_trans (2 * q_pow (Qabs q) 2)
                         (lw0_q_of_nat (Datatypes.S (2 * M))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
      + exact (Hr M (Nat.le_refl M)).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * M))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                            * lw0_q_of_nat (Datatypes.S (2 * M)))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
        * apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * M))
                           * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                          (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                           * lw0_q_of_nat (Datatypes.S (2 * M)))
                          (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * M)))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))))).
        * apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                     (lw0_q_of_nat (Datatypes.S (2 * M)))
                     (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
           ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * M)))
                                 (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                                 (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
              ** apply lw0_q_of_nat_le_succ.
              ** apply lw0_q_of_nat_le_succ.
           ++ apply lw0_q_of_nat_nonneg. }
  assert (Ec2h : QeqT (2%Q * (1#2))%Q 1%Q) by (unfold QeqT; cbn; reflexivity).
  apply (qleT'_trans (Qabs (sin_partial (M + D) q - sin_partial M q))
                     (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                               / q_fact (Datatypes.S (2 * M)))))
                     (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
  - apply (qleT'_trans (Qabs (sin_partial (M + D) q - sin_partial M q))
                       (2%Q * (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S M))
                                 / q_fact (Datatypes.S (2 * Datatypes.S M))))
                       (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                          / q_fact (Datatypes.S (2 * M)))))).
    + apply (lw0_pitB_conv_tail_gen (fun n => sin_partial n q)
                                    (fun n => sin_term (Datatypes.S n) q)
                                    (fun n => q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S n))
                                                / q_fact (Datatypes.S (2 * Datatypes.S n)))
                                    D M).
      * intros n. reflexivity.
      * intros n. exact (qeqT_imp_qeq _ _ (lw0_pitB_conv_sin_term_abs (Datatypes.S n) q)).
      * intros n. apply lw0_pitB_conv_t_nonneg. exact Hqnn.
      * intros j Hj. exact (Hhalf j Hj).
    + apply (lw0_pitB_conv_mult_le_l 2%Q
               (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S M))
                 / q_fact (Datatypes.S (2 * Datatypes.S M)))
               ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                          / q_fact (Datatypes.S (2 * M)))) HhalfM).
      unfold QleT'. reflexivity.
  - apply (qleT'_trans (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                          / q_fact (Datatypes.S (2 * M)))))
                       (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                       (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
    + apply (qeq_leT' (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                        / q_fact (Datatypes.S (2 * M)))))
                      (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
      rewrite (Qmult_assoc 2%Q (1#2) (q_pow (Qabs q) (Datatypes.S (2 * M))
                                          / q_fact (Datatypes.S (2 * M)))).
      rewrite (qeqT_imp_qeq _ _ Ec2h).
      apply (Qmult_1_l (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
    + apply (qleT'_trans (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                         (1%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                         (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
      * apply (qeq_leT' (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                        (1%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                        (Qeq_sym _ _ (Qmult_1_l (q_pow (Qabs q) (Datatypes.S (2 * M))
                                              / q_fact (Datatypes.S (2 * M)))))).
      * apply Qle_to_QleT'. apply Qmult_le_compat_r.
        -- assert (H12 : QltT 1%Q 2%Q) by (unfold QltT, Qlt_bool; reflexivity).
           exact (Qlt_le_weak 1%Q 2%Q (QltT_to_Qlt 1%Q 2%Q H12)).
        -- exact (QleT'_to_Qle _ _
                    (lw0_pitB_conv_t_nonneg (Qabs q) (Datatypes.S (2 * M)) Hqnn)).
Qed.

(* ---------- 减半迭代与 t 消逝（eps 见证引擎） ---------- *)

Lemma lw0_pitB_conv_half_iter : forall (t : nat -> Q) (L M : nat),
  (forall j : nat, (M <= j)%nat -> QleT' (t (Datatypes.S j)) ((1#2) * t j)) ->
  QleT' (t (M + L)%nat) (t M * q_pow (1#2) L).
Proof.
  intros t L. induction L as [| L IH]; intros M Hhalf.
  - assert (E0 : (M + 0)%nat = M) by apply Nat.add_0_r.
    assert (Hbase : QleT' (t M) (t M * q_pow (1#2) 0)).
    { change (q_pow (1#2) 0) with 1%Q.
      apply (qeq_leT' (t M) (t M * 1%Q)).
      exact (Qeq_sym _ _ (Qmult_1_r (t M))). }
    exact (eq_rect_r (fun n0 : nat => QleT' (t n0) (t M * q_pow (1#2) 0)) Hbase E0).
  - assert (E1 : (M + Datatypes.S L)%nat = (Datatypes.S (M + L))%nat)
      by (rewrite Nat.add_succ_r; reflexivity).
    assert (Hmain : QleT' (t (Datatypes.S ((M + L)%nat))) (t M * q_pow (1#2) (Datatypes.S L))).
    { apply (qleT'_trans (t (Datatypes.S ((M + L)%nat)))
                         ((1#2) * (t M * q_pow (1#2) L))
                         (t M * q_pow (1#2) (Datatypes.S L))).
      - apply (qleT'_trans (t (Datatypes.S ((M + L)%nat)))
                           ((1#2) * t ((M + L)%nat))
                           ((1#2) * (t M * q_pow (1#2) L))).
        + apply Hhalf.
          exact (Nat.le_add_r M L).
        + apply (lw0_pitB_conv_mult_le_l (1#2) (t ((M + L)%nat))
                   (t M * q_pow (1#2) L) (IH M Hhalf)).
          unfold QleT'. reflexivity.
      - apply (qeq_leT' ((1#2) * (t M * q_pow (1#2) L))
                        (t M * q_pow (1#2) (Datatypes.S L))).
        change (q_pow (1#2) (Datatypes.S L))
          with ((1#2) * q_pow (1#2) L)%Q.
        rewrite (Qmult_assoc (t M) (1#2) (q_pow (1#2) L)).
        rewrite <- (Qmult_comm (1#2) (t M)).
        rewrite <- (Qmult_assoc (1#2) (t M) (q_pow (1#2) L)).
        apply Qeq_refl. }
    exact (eq_rect_r (fun n0 : nat => QleT' (t n0) (t M * q_pow (1#2) (Datatypes.S L))) Hmain E1).
Qed.

(* ---------- 阈值族共用面（c 侧） ---------- *)

Lemma lw0_pitB_conv_qthr : forall (c : Q) (K j : nat),
  QleT' c (lw0_q_of_nat (Datatypes.S K)) -> QleT' 0 c -> (K <= j)%nat ->
  QleT' (2 * q_pow c 2)
        (lw0_q_of_nat (Datatypes.S (2 * j))
         * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))).
Proof.
  intros c K j HcK Hc0 Hj.
  assert (Hcj : QleT' c (lw0_q_of_nat (Datatypes.S j))).
  { apply (qleT'_trans c (lw0_q_of_nat (Datatypes.S K)) (lw0_q_of_nat (Datatypes.S j))).
    - exact HcK.
    - assert (Ej : Datatypes.S j%nat = (Datatypes.S K + (j - K))%nat).
      { rewrite Nat.add_succ_l. apply f_equal.
        rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hj. }
      apply (eq_rect (Datatypes.S K + (j - K))%nat
                    (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S K)) (lw0_q_of_nat n0))).
      + apply lw0_q_of_nat_le_add.
      + exact (eq_sym Ej). }
  assert (H2pos : QltT 0 (2#1)%Q) by (unfold QltT, Qlt_bool; reflexivity).
  assert (H2lw : QeqT (2%Q * lw0_q_of_nat (Datatypes.S j))
                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { assert (E2j : (2 * Datatypes.S j)%nat = Datatypes.S (Datatypes.S (2 * j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    apply (eq_rect (2 * Datatypes.S j)%nat
                   (fun n0 : nat => QeqT (2%Q * lw0_q_of_nat (Datatypes.S j))
                                         (lw0_q_of_nat n0))).
    - apply qeq_imp_qeqT. unfold lw0_q_of_nat, Qeq, Qmult. cbn [Qnum Qden].
      rewrite Nat2Z.inj_mul. reflexivity.
    - exact E2j. }
  assert (H2c : QleT' (2 * c) (2 * lw0_q_of_nat (Datatypes.S j))).
  { apply (lw0_pitB_conv_mult_le_l 2%Q c (lw0_q_of_nat (Datatypes.S j)) Hcj).
    unfold QleT'. reflexivity. }
  assert (H2c2 : Qle (2 * c)
                     (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { apply QleT'_to_Qle.
    apply (qleT'_trans (2 * c) (2 * lw0_q_of_nat (Datatypes.S j))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
    - exact H2c.
    - apply (qeq_leT' (2 * lw0_q_of_nat (Datatypes.S j))
                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
      exact (qeqT_imp_qeq _ _ H2lw). }
  assert (Emul2 : forall k : nat, (2 * k)%nat = (k + k)%nat).
  { intro k. rewrite (Nat.mul_comm 2 k). rewrite (Nat.mul_succ_r k 1).
    rewrite Nat.mul_1_r. reflexivity. }
  assert (Hj2 : (j <= 2 * j)%nat).
  { rewrite (Emul2 j). apply Nat.le_add_r. }
  assert (Ejj : (Datatypes.S j + j)%nat = Datatypes.S (2 * j)%nat).
  { rewrite Nat.add_succ_l. rewrite (Emul2 j). reflexivity. }
  assert (Hmid : QleT' (lw0_q_of_nat (Datatypes.S j))
                       (lw0_q_of_nat (Datatypes.S (2 * j)))).
  { apply (eq_rect (Datatypes.S j + j)%nat
                   (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S j))
                                          (lw0_q_of_nat n0))
                   (lw0_q_of_nat_le_add (Datatypes.S j) j)
                   (Datatypes.S (2 * j))%nat Ejj). }
  apply (qleT'_trans (2 * q_pow c 2) (c * (2 * c))
                     (lw0_q_of_nat (Datatypes.S (2 * j))
                      * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  - apply (qeq_leT' (2 * q_pow c 2) (c * (2 * c))).
    assert (E2 : q_pow c 2 == c * c)
      by (rewrite (q_pow_succ c 1), (q_pow_succ c 0);
          change (q_pow c 0) with 1%Q; ring).
    rewrite E2. rewrite (Qmult_comm c (2%Q * c)).
    rewrite <- (Qmult_assoc 2%Q c c).
    apply Qeq_refl.
  - apply Qle_to_QleT'.
    apply (Qle_trans (c * (2 * c))
                     (lw0_q_of_nat (Datatypes.S j) * (2 * c))
                     (lw0_q_of_nat (Datatypes.S (2 * j))
                      * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
    + apply Qmult_le_compat_r;
        [ exact (QleT'_to_Qle _ _ Hcj)
        | apply Qmult_le_0_compat;
            [ apply (Qlt_le_weak 0%Q (2#1)%Q); exact (QltT_to_Qlt 0%Q (2#1)%Q H2pos)
            | exact (QleT'_to_Qle _ _ Hc0) ] ].
    + apply (Qle_trans (lw0_q_of_nat (Datatypes.S j) * (2 * c))
                       (lw0_q_of_nat (Datatypes.S (2 * j)) * (2 * c)) _).
      * apply Qmult_le_compat_r;
          [ exact (QleT'_to_Qle _ _ Hmid)
          | apply Qmult_le_0_compat;
              [ apply (Qlt_le_weak 0%Q (2#1)%Q); exact (QltT_to_Qlt 0%Q (2#1)%Q H2pos)
              | exact (QleT'_to_Qle _ _ Hc0) ] ].
      * exact (QleT'_to_Qle _ _
                 (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (2 * j)))
                    (2 * c)
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                    (Qle_to_QleT' _ _ H2c2) (lw0_q_of_nat_nonneg (Datatypes.S (2 * j))))).
Qed.

(* ---------- QeqT 侧移桥（QltT 目标的 == 迁移，t_vanish/sin_vanish 共用） ---------- *)

Lemma lw0_pitB_conv_qeqL_ltT : forall (a b c : Q),
  QeqT a b -> QltT b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qle_lt_trans a b c).
  - apply (qeq_imp_qle a b). exact (qeqT_imp_qeq _ _ Hab).
  - exact (QltT_to_Qlt b c Hbc).
Qed.

Lemma lw0_pitB_conv_qeqR_ltT : forall (a b c : Q),
  QltT a b -> QeqT b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qlt_le_trans a b c).
  - exact (QltT_to_Qlt a b Hab).
  - apply (qeq_imp_qle b c). exact (qeqT_imp_qeq _ _ Hbc).
Qed.

Lemma lw0_pitB_conv_t_vanish : forall (c : Q) (eps : Q),
  QleT' 0 c -> QltT 0 eps ->
  sigT (fun M0 : nat => sigT (fun _ : QleT' c (lw0_q_of_nat (Datatypes.S M0)) =>
    forall M : nat, (M0 <= M)%nat ->
    QltT (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))) eps)).
Proof.
  intros c eps Hc0 Heps.
  assert (Hnum0 : (0 <= Qnum c)%Z).
  { assert (Hq : Qle 0 c) by exact (QleT'_to_Qle _ _ Hc0).
    unfold Qle in Hq. cbn [Qnum Qden] in Hq. rewrite Z.mul_1_r in Hq. exact Hq. }
  set (t := fun j : nat => q_pow c (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).
  set (M1 := Z.to_nat (Qnum c)).
  assert (Hc1a : Qle c ((Qnum c)#1)).
  { unfold Qle. cbn [Qnum Qden]. rewrite Z.mul_1_r.
    destruct (Z_lt_le_dec 0 (Qnum c)) as [Hpos | Hnonpos].
    - apply (proj1 (Z.le_mul_diag_r (Qnum c) (Z.pos (Qden c)) Hpos)).
      pose proof (Zgt_pos_0 (Qden c)) as Hdp.
      apply (Zlt_le_succ 0). exact (proj1 (Z.gt_lt_iff _ _) Hdp).
    - assert (Hz : Qnum c = 0%Z)
        by (apply Z.le_antisymm; [ exact Hnonpos | exact Hnum0 ]).
      rewrite Hz. apply Z.le_refl. }
  assert (Hc1 : QleT' c (lw0_q_of_nat (Datatypes.S M1))).
  { apply (qleT'_trans c ((Qnum c)#1) (lw0_q_of_nat (Datatypes.S M1))).
    - exact (Qle_to_QleT' _ _ Hc1a).
    - apply (qleT'_trans ((Qnum c)#1) (lw0_q_of_nat M1)
                         (lw0_q_of_nat (Datatypes.S M1))).
      + apply (qeq_leT' ((Qnum c)#1) (lw0_q_of_nat M1)).
        assert (EZ : Z.of_nat (Z.to_nat (Qnum c)) = Qnum c)
          by (apply Z2Nat.id; exact Hnum0).
        unfold lw0_q_of_nat, M1. rewrite EZ. apply Qeq_refl.
      + apply lw0_q_of_nat_le_succ. }
  assert (Hr : forall j : nat, (M1 <= j)%nat ->
           QleT' (2 * q_pow c 2)
                 (lw0_q_of_nat (Datatypes.S (2 * j))
                  * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { intros j Hj. exact (lw0_pitB_conv_qthr c M1 j Hc1 Hc0 Hj). }
  assert (HhalfM : forall j : nat, (M1 <= j)%nat -> QleT' (t (Datatypes.S j)) ((1#2) * t j)).
  { intros j Hj. unfold t.
    apply (eq_rect (Datatypes.S (Datatypes.S (2 * j))%nat)
                   (fun n0 : nat => QleT' (q_pow c (Datatypes.S n0) / q_fact (Datatypes.S n0))
                                          ((1#2) * (q_pow c (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))))).
    - apply (lw0_pitB_conv_tstep c (Datatypes.S (2 * j)) Hc0).
      apply (qleT'_trans (2 * q_pow c 2)
                         (lw0_q_of_nat (Datatypes.S (2 * j))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
      + exact (Hr j Hj).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (2 * j)))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
        * apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (2 * j)))
                           (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * j)))
                                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))))).
        * apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (2 * j)))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j)))
                                (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
             ++ apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_le_succ.
          -- apply lw0_q_of_nat_nonneg.
    - rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
  assert (Heps2 : QltT 0 ((1#2) * eps)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0%Q (1#2)%Q). unfold QltT. reflexivity.
    - exact (QltT_to_Qlt _ _ Heps). }
  destruct (lw0_pitB_conv_geomscale (t M1) ((1#2) * eps)
             (lw0_pitB_conv_t_nonneg c (Datatypes.S (2 * M1)) Hc0) Heps2) as [L HL].
  exists (M1 + L)%nat.
  assert (Hmono2 : QleT' (lw0_q_of_nat (Datatypes.S M1))
                         (lw0_q_of_nat (Datatypes.S (M1 + L)))).
  { apply (eq_rect (Datatypes.S M1 + L)%nat
                   (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S M1))
                                          (lw0_q_of_nat n0))).
    - apply lw0_q_of_nat_le_add.
    - apply Nat.add_succ_l. }
  exists (qleT'_trans c (lw0_q_of_nat (Datatypes.S M1))
                        (lw0_q_of_nat (Datatypes.S (M1 + L))) Hc1 Hmono2).
  intros M HM.
  assert (HMe : (M1 <= M)%nat).
  { apply (Nat.le_trans M1 (M1 + L) M).
    - apply Nat.le_add_r.
    - exact HM. }
  assert (HMm : (L <= M - M1)%nat).
  { rewrite Nat.add_comm in HM. exact (Nat.le_add_le_sub_r L M M1 HM). }
  assert (Hdec : QleT' (t M) (q_pow (1#2) L * t M1)).
  { assert (E1 : (M1 + (M - M1))%nat = M)
      by (rewrite Nat.add_comm; apply Nat.sub_add; exact HMe).
    apply (eq_rect (M1 + (M - M1))%nat
                  (fun n0 : nat => QleT' (t n0) (q_pow (1#2) L * t M1))).
    - apply (qleT'_trans (t ((M1 + (M - M1))%nat))
                         (t M1 * q_pow (1#2) ((M - M1)%nat))
                         (q_pow (1#2) L * t M1)).
      + exact (lw0_pitB_conv_half_iter t (M - M1) M1 HhalfM).
      + apply (qleT'_trans (t M1 * q_pow (1#2) ((M - M1)%nat))
                           (q_pow (1#2) ((M - M1)%nat) * t M1)
                           (q_pow (1#2) L * t M1)).
        * apply (qeq_leT' (t M1 * q_pow (1#2) ((M - M1)%nat))
                          (q_pow (1#2) ((M - M1)%nat) * t M1)).
          exact (Qmult_comm (t M1) (q_pow (1#2) ((M - M1)%nat))).
        * apply Qle_to_QleT'. apply Qmult_le_compat_r.
          -- exact (QleT'_to_Qle _ _
                      (lw0_pitB_conv_half_mono (M - M1) L HMm)).
          -- exact (QleT'_to_Qle _ _
                      (lw0_pitB_conv_t_nonneg c (Datatypes.S (2 * M1)) Hc0)).
    - exact E1. }
  assert (Hchain : QleT' (t M) ((1#2) * eps)).
  { apply (qleT'_trans (t M)
                       (q_pow (1#2) L * t M1)
                       ((1#2) * eps)).
    - exact Hdec.
    - apply (qleT'_trans (q_pow (1#2) L * t M1)
                         (q_pow (1#2) L * (q_pow (2#1) L * ((1#2) * eps)))
                         ((1#2) * eps)).
      + apply (lw0_pitB_conv_mult_le_l (q_pow (1#2) L) (t M1)
                 (q_pow (2#1) L * ((1#2) * eps)) HL).
        apply Qle_to_QleT'. apply q_pow_nonneg.
        apply (Qlt_le_weak 0%Q (1#2)%Q).
        apply (QltT_to_Qlt 0%Q (1#2)%Q).
        unfold QltT. reflexivity.
      + apply (qeq_leT' (q_pow (1#2) L * (q_pow (2#1) L * ((1#2) * eps)))
                        ((1#2) * eps)).
        assert (Ec12 : QeqT ((1#2) * (2#1))%Q 1%Q)
          by (unfold QeqT; cbn; reflexivity).
        rewrite (Qmult_assoc (q_pow (1#2) L) (q_pow (2#1) L) ((1#2) * eps)).
        rewrite (lw0_q_pow_mult (1#2) (2#1) L).
        rewrite (qeqT_imp_qeq _ _ Ec12).
        rewrite (lw0_q_pow_one L).
        apply Qmult_1_l. }
  apply (lw0_leT'_ltT_trans (t M) ((1#2) * eps) eps).
  + exact Hchain.
  + apply Qlt_to_QltT.
    apply (Qlt_le_trans ((1#2) * eps) (1%Q * eps) eps).
    * apply (Qmult_lt_compat_r (1#2)%Q 1%Q eps).
      -- exact (QltT_to_Qlt _ _ Heps).
      -- apply (QltT_to_Qlt 0%Q 1%Q). unfold QltT. reflexivity.
    * apply QleT'_to_Qle. apply (qeq_leT' (1%Q * eps) eps (Qmult_1_l eps)).
Qed.

(* ---------- 引理一终形：σ_M → sin 的 Cauchy 尾形 eps 见证 ---------- *)

Lemma lw0_pitB_conv_sin_vanish : forall (q : Q) (eps : Q), QltT 0 eps ->
  sigT (fun M0 : nat => forall M N : nat, (M0 <= M)%nat -> (M <= N)%nat ->
    QltT (Qabs (sin_partial N q - sin_partial M q)) eps).
Proof.
  intros q eps Heps.
  assert (Hqnn : QleT' 0 (Qabs q))
    by (apply Qle_to_QleT'; apply Qabs_nonneg).
  assert (Hq4 : QltT 0 ((1#4) * eps)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0%Q (1#4)%Q). unfold QltT. reflexivity.
    - exact (QltT_to_Qlt _ _ Heps). }
  destruct (lw0_pitB_conv_t_vanish (Qabs q) ((1#4) * eps) Hqnn Hq4)
    as [M0 [HcM0 HM0]].
  exists M0. intros M N HM HN.
  assert (Ed : N%nat = (M + (N - M))%nat)
    by (symmetry; rewrite Nat.add_comm; apply Nat.sub_add; exact HN).
  apply (eq_rect (M + (N - M))%nat
                 (fun n0 : nat => QltT (Qabs (sin_partial n0 q - sin_partial M q)) eps)).
  - apply (lw0_leT'_ltT_trans
             (Qabs (sin_partial (M + (N - M)) q - sin_partial M q))
             (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
             eps).
    + exact (lw0_pitB_conv_sin_tail q M (N - M)
               (fun j Hj => lw0_pitB_conv_qthr (Qabs q) M0 j HcM0
                               Hqnn (Nat.le_trans M0 M j HM Hj))).
    + assert (Hlt1 : QltT (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))
                            + q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                           (((1#4) * eps) + ((1#4) * eps))).
      { apply Qlt_to_QltT. apply Qplus_lt_compat;
          [ apply QltT_to_Qlt; exact (HM0 M HM)
          | apply QltT_to_Qlt; exact (HM0 M HM) ]. }
      assert (Ec2 : QeqT 2%Q (1%Q + 1%Q)) by (unfold QeqT; cbn; reflexivity).
      assert (E2c : QeqT (2%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                         (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))
                          + q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
      { apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ Ec2).
        rewrite (Qmult_plus_distr_l 1%Q 1%Q
                   (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
        rewrite (Qmult_1_l (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
        apply Qeq_refl. }
      assert (E3c : QeqT (((1#4) * eps) + ((1#4) * eps)) ((1#2) * eps)).
      { apply qeq_imp_qeqT.
        transitivity (((1#4) + (1#4))%Q * eps).
        - rewrite <- (Qmult_plus_distr_l (1#4) (1#4) eps). apply Qeq_refl.
        - assert (Ec24s : QeqT ((1#4) + (1#4))%Q (1#2))
            by (unfold QeqT; cbn; reflexivity).
          apply (Qmult_comp ((1#4) + (1#4))%Q (1#2)%Q
                   (qeqT_imp_qeq _ _ Ec24s) eps%Q eps%Q).
          apply Qeq_refl. }
      assert (Hlt2T : QltT ((1#2) * eps) eps).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans ((1#2) * eps) (1%Q * eps) eps).
        * apply (Qmult_lt_compat_r (1#2)%Q 1%Q eps).
          -- exact (QltT_to_Qlt _ _ Heps).
          -- apply (QltT_to_Qlt 0%Q 1%Q). unfold QltT. reflexivity.
        * apply QleT'_to_Qle. apply (qeq_leT' (1%Q * eps) eps (Qmult_1_l eps)). }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans (2%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                          ((1#2) * eps) eps).
      * apply QltT_to_Qlt.
        apply (lw0_pitB_conv_qeqL_ltT
                 (2%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                 (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))
                  + q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                 ((1#2) * eps) E2c).
        apply (lw0_pitB_conv_qeqR_ltT
                 (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))
                  + q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                 (((1#4) * eps) + ((1#4) * eps)) ((1#2) * eps) Hlt1 E3c).
      * exact (Qlt_le_weak ((1#2) * eps) eps
                 (QltT_to_Qlt ((1#2) * eps) eps Hlt2T)).
  - exact (eq_sym Ed).
Qed.

(* ---------- (γ) 引理二：γ 侧 cos 实例四件（零 Prop 直写；2j 指标沿 tstep N 泛形对应） ---------- *)

Lemma lw0_pitB_conv_cos_term_abs : forall (j : nat) (q : Q),
  QeqT (Qabs (cos_term j q))
       (q_pow (Qabs q) (2 * j) / q_fact (2 * j)).
Proof.
  intros j q. apply qeq_imp_qeqT. unfold cos_term, Qdiv.
  rewrite Qabs_Qmult, Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_qabs_pow q (2 * j))).
  rewrite (lw0_Qabs_pos_eq (Qinv (q_fact (2 * j))))
    by (apply Qle_to_QleT'; apply Qinv_le_0_compat;
        apply (Qlt_le_weak 0%Q); apply q_fact_pos).
  destruct (lw0_pitB_conv_m1_cases j) as [b Hc]. destruct b;
    rewrite (qeqT_imp_qeq _ _ Hc); simpl; ring.
Qed.

Lemma lw0_pitB_conv_cos_tail : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (cos_partial (M + D) q - cos_partial M q))
        (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
Proof.
  intros q M D Hr.
  assert (Hqnn : QleT' 0 (Qabs q))
    by (apply Qle_to_QleT'; apply Qabs_nonneg).
  assert (Hhalf : forall j : nat, (M <= j)%nat ->
           QleT' (q_pow (Qabs q) (2 * Datatypes.S (Datatypes.S j))
                   / q_fact (2 * Datatypes.S (Datatypes.S j)))
                 ((1#2) * (q_pow (Qabs q) (2 * Datatypes.S j)
                            / q_fact (2 * Datatypes.S j)))).
  { intros j Hj.
    assert (E2j : (2 * Datatypes.S j)%nat = Datatypes.S (Datatypes.S (2 * j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    assert (E2j2 : (2 * Datatypes.S (Datatypes.S j))%nat
                   = Datatypes.S (Datatypes.S (2 * Datatypes.S j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 1).
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2j2, E2j.
    apply (lw0_pitB_conv_tstep (Qabs q)
                 (Datatypes.S (Datatypes.S (2 * j)))).
    - exact Hqnn.
    - apply (qleT'_trans (2 * q_pow (Qabs q) 2)
                         (lw0_q_of_nat (Datatypes.S (2 * j))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
      + exact (Hr j Hj).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * j)))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (2 * j)))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j)))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg.
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg. }
  assert (HhalfM : QleT' (q_pow (Qabs q) (2 * Datatypes.S M)
                            / q_fact (2 * Datatypes.S M))
                         ((1#2) * (q_pow (Qabs q) (2 * M)
                                    / q_fact (2 * M)))).
  { assert (E2M : (2 * Datatypes.S M)%nat = Datatypes.S (Datatypes.S (2 * M))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * M) 1).
      rewrite (Nat.add_succ_r (2 * M) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2M.
    apply (lw0_pitB_conv_tstep (Qabs q) (2 * M)).
    - exact Hqnn.
    - exact (Hr M (Nat.le_refl M)). }
  assert (Ec2h : QeqT (2%Q * (1#2))%Q 1%Q) by (unfold QeqT; cbn; reflexivity).
  apply (qleT'_trans (Qabs (cos_partial (M + D) q - cos_partial M q))
                     (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))))
                     (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))).
  - apply (qleT'_trans (Qabs (cos_partial (M + D) q - cos_partial M q))
                       (2%Q * (q_pow (Qabs q) (2 * Datatypes.S M)
                                 / q_fact (2 * Datatypes.S M)))
                       (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M)
                                          / q_fact (2 * M))))).
    + apply (lw0_pitB_conv_tail_gen (fun n => cos_partial n q)
                                    (fun n => cos_term (Datatypes.S n) q)
                                    (fun n => q_pow (Qabs q) (2 * Datatypes.S n)
                                                / q_fact (2 * Datatypes.S n))
                                    D M).
      * intros n. reflexivity.
      * intros n. exact (qeqT_imp_qeq _ _ (lw0_pitB_conv_cos_term_abs (Datatypes.S n) q)).
      * intros n. apply lw0_pitB_conv_t_nonneg. exact Hqnn.
      * intros j Hj. exact (Hhalf j Hj).
    + apply (lw0_pitB_conv_mult_le_l 2%Q
               (q_pow (Qabs q) (2 * Datatypes.S M) / q_fact (2 * Datatypes.S M))
               ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))) HhalfM).
      unfold QleT'. reflexivity.
  - apply (qleT'_trans (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))))
                       (q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                       (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))).
    + apply (qeq_leT' (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))))
                      (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
      rewrite (Qmult_assoc 2%Q (1#2) (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
      rewrite (qeqT_imp_qeq _ _ Ec2h).
      apply (Qmult_1_l (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
    + apply (qleT'_trans (q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                         (1%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                         (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))).
      * apply (qeq_leT' (q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                        (1%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                        (Qeq_sym _ _ (Qmult_1_l (q_pow (Qabs q) (2 * M)
                                              / q_fact (2 * M))))).
      * apply Qle_to_QleT'. apply Qmult_le_compat_r.
        -- assert (H12 : QltT 1%Q 2%Q) by (unfold QltT, Qlt_bool; reflexivity).
           exact (Qlt_le_weak 1%Q 2%Q (QltT_to_Qlt 1%Q 2%Q H12)).
        -- exact (QleT'_to_Qle _ _
                    (lw0_pitB_conv_t_nonneg (Qabs q) (2 * M) Hqnn)).
Qed.

(* ---------- (γ) 阈值族偶指标版：γ 侧第三件（tstep N:=2j 直取零移位） ---------- *)

Lemma lw0_pitB_conv_t_vanish_even : forall (c : Q) (eps : Q),
  QleT' 0 c -> QltT 0 eps ->
  sigT (fun M0 : nat => sigT (fun _ : QleT' c (lw0_q_of_nat (Datatypes.S M0)) =>
    forall M : nat, (M0 <= M)%nat ->
    QltT (q_pow c (2 * M) / q_fact (2 * M)) eps)).
Proof.
  intros c eps Hc0 Heps.
  assert (Hnum0 : (0 <= Qnum c)%Z).
  { assert (Hq : Qle 0 c) by exact (QleT'_to_Qle _ _ Hc0).
    unfold Qle in Hq. cbn [Qnum Qden] in Hq. rewrite Z.mul_1_r in Hq. exact Hq. }
  set (t := fun j : nat => q_pow c (2 * j) / q_fact (2 * j)).
  set (M1 := Z.to_nat (Qnum c)).
  assert (Hc1a : Qle c ((Qnum c)#1)).
  { unfold Qle. cbn [Qnum Qden]. rewrite Z.mul_1_r.
    destruct (Z_lt_le_dec 0 (Qnum c)) as [Hpos | Hnonpos].
    - apply (proj1 (Z.le_mul_diag_r (Qnum c) (Z.pos (Qden c)) Hpos)).
      pose proof (Zgt_pos_0 (Qden c)) as Hdp.
      apply (Zlt_le_succ 0). exact (proj1 (Z.gt_lt_iff _ _) Hdp).
    - assert (Hz : Qnum c = 0%Z)
        by (apply Z.le_antisymm; [ exact Hnonpos | exact Hnum0 ]).
      rewrite Hz. apply Z.le_refl. }
  assert (Hc1 : QleT' c (lw0_q_of_nat (Datatypes.S M1))).
  { apply (qleT'_trans c ((Qnum c)#1) (lw0_q_of_nat (Datatypes.S M1))).
    - exact (Qle_to_QleT' _ _ Hc1a).
    - apply (qleT'_trans ((Qnum c)#1) (lw0_q_of_nat M1)
                         (lw0_q_of_nat (Datatypes.S M1))).
      + apply (qeq_leT' ((Qnum c)#1) (lw0_q_of_nat M1)).
        assert (EZ : Z.of_nat (Z.to_nat (Qnum c)) = Qnum c)
          by (apply Z2Nat.id; exact Hnum0).
        unfold lw0_q_of_nat, M1. rewrite EZ. apply Qeq_refl.
      + apply lw0_q_of_nat_le_succ. }
  assert (Hr : forall j : nat, (M1 <= j)%nat ->
           QleT' (2 * q_pow c 2)
                 (lw0_q_of_nat (Datatypes.S (2 * j))
                  * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { intros j Hj. exact (lw0_pitB_conv_qthr c M1 j Hc1 Hc0 Hj). }
  assert (HhalfM : forall j : nat, (M1 <= j)%nat -> QleT' (t (Datatypes.S j)) ((1#2) * t j)).
  { intros j Hj. unfold t.
    apply (eq_rect (Datatypes.S (Datatypes.S (2 * j))%nat)
                   (fun n0 : nat => QleT' (q_pow c n0 / q_fact n0)
                                          ((1#2) * (q_pow c (2 * j) / q_fact (2 * j))))).
    - apply (lw0_pitB_conv_tstep c (2 * j) Hc0). exact (Hr j Hj).
    - rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
  assert (Heps2 : QltT 0 ((1#2) * eps)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0%Q (1#2)%Q). unfold QltT. reflexivity.
    - exact (QltT_to_Qlt _ _ Heps). }
  destruct (lw0_pitB_conv_geomscale (t M1) ((1#2) * eps)
             (lw0_pitB_conv_t_nonneg c (2 * M1) Hc0) Heps2) as [L HL].
  exists (M1 + L)%nat.
  assert (Hmono2 : QleT' (lw0_q_of_nat (Datatypes.S M1))
                         (lw0_q_of_nat (Datatypes.S (M1 + L)))).
  { apply (eq_rect (Datatypes.S M1 + L)%nat
                   (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S M1))
                                          (lw0_q_of_nat n0))).
    - apply lw0_q_of_nat_le_add.
    - apply Nat.add_succ_l. }
  exists (qleT'_trans c (lw0_q_of_nat (Datatypes.S M1))
                        (lw0_q_of_nat (Datatypes.S (M1 + L))) Hc1 Hmono2).
  intros M HM.
  assert (HMe : (M1 <= M)%nat).
  { apply (Nat.le_trans M1 (M1 + L) M).
    - apply Nat.le_add_r.
    - exact HM. }
  assert (HMm : (L <= M - M1)%nat).
  { rewrite Nat.add_comm in HM. exact (Nat.le_add_le_sub_r L M M1 HM). }
  assert (Hdec : QleT' (t M) (q_pow (1#2) L * t M1)).
  { assert (E1 : (M1 + (M - M1))%nat = M)
      by (rewrite Nat.add_comm; apply Nat.sub_add; exact HMe).
    apply (eq_rect (M1 + (M - M1))%nat
                  (fun n0 : nat => QleT' (t n0) (q_pow (1#2) L * t M1))).
    - apply (qleT'_trans (t ((M1 + (M - M1))%nat))
                         (t M1 * q_pow (1#2) ((M - M1)%nat))
                         (q_pow (1#2) L * t M1)).
      + exact (lw0_pitB_conv_half_iter t (M - M1) M1 HhalfM).
      + apply (qleT'_trans (t M1 * q_pow (1#2) ((M - M1)%nat))
                           (q_pow (1#2) ((M - M1)%nat) * t M1)
                           (q_pow (1#2) L * t M1)).
        * apply (qeq_leT' (t M1 * q_pow (1#2) ((M - M1)%nat))
                          (q_pow (1#2) ((M - M1)%nat) * t M1)).
          exact (Qmult_comm (t M1) (q_pow (1#2) ((M - M1)%nat))).
        * apply Qle_to_QleT'. apply Qmult_le_compat_r.
          -- exact (QleT'_to_Qle _ _
                      (lw0_pitB_conv_half_mono (M - M1) L HMm)).
          -- exact (QleT'_to_Qle _ _
                      (lw0_pitB_conv_t_nonneg c (2 * M1) Hc0)).
    - exact E1. }
  assert (Hchain : QleT' (t M) ((1#2) * eps)).
  { apply (qleT'_trans (t M)
                       (q_pow (1#2) L * t M1)
                       ((1#2) * eps)).
    - exact Hdec.
    - apply (qleT'_trans (q_pow (1#2) L * t M1)
                         (q_pow (1#2) L * (q_pow (2#1) L * ((1#2) * eps)))
                         ((1#2) * eps)).
      + apply (lw0_pitB_conv_mult_le_l (q_pow (1#2) L) (t M1)
                 (q_pow (2#1) L * ((1#2) * eps)) HL).
        apply Qle_to_QleT'. apply q_pow_nonneg.
        apply (Qlt_le_weak 0%Q (1#2)%Q).
        apply (QltT_to_Qlt 0%Q (1#2)%Q).
        unfold QltT. reflexivity.
      + apply (qeq_leT' (q_pow (1#2) L * (q_pow (2#1) L * ((1#2) * eps)))
                        ((1#2) * eps)).
        assert (Ec12 : QeqT ((1#2) * (2#1))%Q 1%Q)
          by (unfold QeqT; cbn; reflexivity).
        rewrite (Qmult_assoc (q_pow (1#2) L) (q_pow (2#1) L) ((1#2) * eps)).
        rewrite (lw0_q_pow_mult (1#2) (2#1) L).
        rewrite (qeqT_imp_qeq _ _ Ec12).
        rewrite (lw0_q_pow_one L).
        apply Qmult_1_l. }
  apply (lw0_leT'_ltT_trans (t M) ((1#2) * eps) eps).
  + exact Hchain.
  + apply Qlt_to_QltT.
    apply (Qlt_le_trans ((1#2) * eps) (1%Q * eps) eps).
    * apply (Qmult_lt_compat_r (1#2)%Q 1%Q eps).
      -- exact (QltT_to_Qlt _ _ Heps).
      -- apply (QltT_to_Qlt 0%Q 1%Q). unfold QltT. reflexivity.
    * apply QleT'_to_Qle. apply (qeq_leT' (1%Q * eps) eps (Qmult_1_l eps)).
Qed.

(* ---------- (γ) 引理二终形：γ_M → cos 的 Cauchy 尾形 eps 见证 ---------- *)

Lemma lw0_pitB_conv_cos_vanish : forall (q : Q) (eps : Q), QltT 0 eps ->
  sigT (fun M0 : nat => forall M N : nat, (M0 <= M)%nat -> (M <= N)%nat ->
    QltT (Qabs (cos_partial N q - cos_partial M q)) eps).
Proof.
  intros q eps Heps.
  assert (Hqnn : QleT' 0 (Qabs q))
    by (apply Qle_to_QleT'; apply Qabs_nonneg).
  assert (Hq4 : QltT 0 ((1#4) * eps)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0%Q (1#4)%Q). unfold QltT. reflexivity.
    - exact (QltT_to_Qlt _ _ Heps). }
  destruct (lw0_pitB_conv_t_vanish_even (Qabs q) ((1#4) * eps) Hqnn Hq4)
    as [M0 [HcM0 HM0]].
  exists M0. intros M N HM HN.
  assert (Ed : N%nat = (M + (N - M))%nat)
    by (symmetry; rewrite Nat.add_comm; apply Nat.sub_add; exact HN).
  apply (eq_rect (M + (N - M))%nat
                 (fun n0 : nat => QltT (Qabs (cos_partial n0 q - cos_partial M q)) eps)).
  - apply (lw0_leT'_ltT_trans
             (Qabs (cos_partial (M + (N - M)) q - cos_partial M q))
             (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
             eps).
    + exact (lw0_pitB_conv_cos_tail q M (N - M)
               (fun j Hj => lw0_pitB_conv_qthr (Qabs q) M0 j HcM0
                               Hqnn (Nat.le_trans M0 M j HM Hj))).
    + assert (Hlt1 : QltT (q_pow (Qabs q) (2 * M) / q_fact (2 * M)
                            + q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                           (((1#4) * eps) + ((1#4) * eps))).
      { apply Qlt_to_QltT. apply Qplus_lt_compat;
          [ apply QltT_to_Qlt; exact (HM0 M HM)
          | apply QltT_to_Qlt; exact (HM0 M HM) ]. }
      assert (Ec2 : QeqT 2%Q (1%Q + 1%Q)) by (unfold QeqT; cbn; reflexivity).
      assert (E2c : QeqT (2%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                         (q_pow (Qabs q) (2 * M) / q_fact (2 * M)
                          + q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
      { apply qeq_imp_qeqT.
        rewrite (qeqT_imp_qeq _ _ Ec2).
        rewrite (Qmult_plus_distr_l 1%Q 1%Q
                   (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
        rewrite (Qmult_1_l (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
        apply Qeq_refl. }
      assert (E3c : QeqT (((1#4) * eps) + ((1#4) * eps)) ((1#2) * eps)).
      { apply qeq_imp_qeqT.
        transitivity (((1#4) + (1#4))%Q * eps).
        - rewrite <- (Qmult_plus_distr_l (1#4) (1#4) eps). apply Qeq_refl.
        - assert (Ec24s : QeqT ((1#4) + (1#4))%Q (1#2))
            by (unfold QeqT; cbn; reflexivity).
          apply (Qmult_comp ((1#4) + (1#4))%Q (1#2)%Q
                   (qeqT_imp_qeq _ _ Ec24s) eps%Q eps%Q).
          apply Qeq_refl. }
      assert (Hlt2T : QltT ((1#2) * eps) eps).
      { apply Qlt_to_QltT.
        apply (Qlt_le_trans ((1#2) * eps) (1%Q * eps) eps).
        * apply (Qmult_lt_compat_r (1#2)%Q 1%Q eps).
          -- exact (QltT_to_Qlt _ _ Heps).
          -- apply (QltT_to_Qlt 0%Q 1%Q). unfold QltT. reflexivity.
        * apply QleT'_to_Qle. apply (qeq_leT' (1%Q * eps) eps (Qmult_1_l eps)). }
      apply Qlt_to_QltT.
      apply (Qlt_le_trans (2%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                          ((1#2) * eps) eps).
      * apply QltT_to_Qlt.
        apply (lw0_pitB_conv_qeqL_ltT
                 (2%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                 (q_pow (Qabs q) (2 * M) / q_fact (2 * M)
                  + q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                 ((1#2) * eps) E2c).
        apply (lw0_pitB_conv_qeqR_ltT
                 (q_pow (Qabs q) (2 * M) / q_fact (2 * M)
                  + q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                 (((1#4) * eps) + ((1#4) * eps)) ((1#2) * eps) Hlt1 E3c).
      * exact (Qlt_le_weak ((1#2) * eps) eps
                 (QltT_to_Qlt ((1#2) * eps) eps Hlt2T)).
  - exact (eq_sym Ed).
Qed.

(* ---------- (γ) pwi 配对尾权重引擎＋pair 两件（零 Prop 直写；τ_M 义务形 QleT' (pwi τ 0 c) (Wg * t_M)） ---------- *)

(* pwi p k c := Σ_j |p_j|·|c|^{j+1}/(k+j+1) —— |c·eval(ai p k)(c)| 的逐项占优权重。 *)
Fixpoint lw0_pitB_conv_pwi (p : QPoly) (k : nat) (c : Q) : Q :=
  match p with
  | nil => 0%Q
  | cons a p' => Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                 + Qabs c * lw0_pitB_conv_pwi p' (Datatypes.S k) c
  end.

Lemma lw0_pitB_conv_pwi_step : forall (a : Q) (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (cons a p) k c)
       (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
        + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
Proof.
  intros a p k c. apply qeq_imp_qeqT. reflexivity.
Qed.

Lemma lw0_pitB_conv_pwi_scalar : forall (a : Q) (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (qpoly_scalar a p) k c)
       (Qabs a * lw0_pitB_conv_pwi p k c).
Proof.
  intros a p. induction p as [| b p IH]; intros k c.
  - change (lw0_pitB_conv_pwi (qpoly_scalar a nil) k c) with 0%Q.
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply qeq_imp_qeqT. ring.
  - change (lw0_pitB_conv_pwi (qpoly_scalar a (cons b p)) k c)
      with (Qabs (a * b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi (qpoly_scalar a p) (Datatypes.S k) c).
    change (Qabs a * lw0_pitB_conv_pwi (cons b p) k c)
      with (Qabs a * (Qabs b * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                       + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)).
    apply qeq_imp_qeqT.
    rewrite Qabs_Qmult.
    rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k) c)).
    ring.
Qed.

Lemma lw0_pitB_conv_pwi_opp : forall (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (qpoly_scalar (-1)%Q p) k c)
       (lw0_pitB_conv_pwi p k c).
Proof.
  intros p k c. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_scalar (-1)%Q p k c)).
  assert (Ec1 : QeqT (Qabs (-1)%Q) 1%Q) by (unfold QeqT; cbn; reflexivity).
  rewrite (qeqT_imp_qeq _ _ Ec1).
  apply (Qmult_1_l (lw0_pitB_conv_pwi p k c)).
Qed.

Lemma lw0_pitB_conv_pwi_add_le : forall (p q : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (qpoly_add p q) k c)
        (lw0_pitB_conv_pwi p k c + lw0_pitB_conv_pwi q k c).
Proof.
  intro p. induction p as [| a p IH]; intros q k c.
  - change (lw0_pitB_conv_pwi (qpoly_add nil q) k c)
      with (lw0_pitB_conv_pwi q k c).
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' (lw0_pitB_conv_pwi q k c) (0%Q + lw0_pitB_conv_pwi q k c)).
    rewrite Qplus_0_l. apply Qeq_refl.
  - destruct q as [| b q'].
    + change (lw0_pitB_conv_pwi (qpoly_add (cons a p) nil) k c)
        with (lw0_pitB_conv_pwi (cons a p) k c).
      change (lw0_pitB_conv_pwi nil k c) with 0%Q.
      apply (qeq_leT' (lw0_pitB_conv_pwi (cons a p) k c)
                      (lw0_pitB_conv_pwi (cons a p) k c + 0%Q)).
      rewrite Qplus_0_r. apply Qeq_refl.
    + assert (HH0 : QleT' 0 (Qabs c / lw0_q_of_nat (Datatypes.S k))).
      { apply Qle_to_QleT'. apply Qmult_le_0_compat.
        - apply Qabs_nonneg.
        - apply Qinv_le_0_compat. apply Qlt_le_weak.
          apply (Qlt_le_trans 0%Q 1%Q (lw0_q_of_nat (Datatypes.S k))).
          + apply QltT_to_Qlt. unfold QltT. reflexivity.
          + apply QleT'_to_Qle. apply lw0_q_of_nat_ge_one. }
      change (lw0_pitB_conv_pwi (qpoly_add (cons a p) (cons b q')) k c)
        with (Qabs (a + b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c).
      change (lw0_pitB_conv_pwi (cons a p) k c)
        with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
      change (lw0_pitB_conv_pwi (cons b q') k c)
        with (Qabs b * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c).
      apply (qleT'_trans
               (Qabs (a + b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                + Qabs c * lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c)
               ((Qabs a + Qabs b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                + (Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c
                   + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c))
               (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c
                + (Qabs b * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                   + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c))).
      * apply Qle_to_QleT'. apply Qplus_le_compat.
        -- apply Qmult_le_compat_r.
           ++ exact (Qabs_triangle a b).
           ++ exact (QleT'_to_Qle _ _ HH0).
        -- apply QleT'_to_Qle.
           apply (qleT'_trans
             (Qabs c * lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c)
             (Qabs c * (lw0_pitB_conv_pwi p (Datatypes.S k) c
                       + lw0_pitB_conv_pwi q' (Datatypes.S k) c))
             (Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c
             + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c)).
           ++ apply (lw0_pitB_conv_mult_le_l (Qabs c)
                    (lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c)
                    (lw0_pitB_conv_pwi p (Datatypes.S k) c
                     + lw0_pitB_conv_pwi q' (Datatypes.S k) c)
                    (IH q' (Datatypes.S k) c)).
              apply Qle_to_QleT'. apply Qabs_nonneg.
           ++ apply qeq_leT'. ring.
      * apply qeq_leT'. ring.
Qed.

Lemma lw0_pitB_conv_pwi_mul_le : forall (a : Q) (f g : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (qpoly_mul (cons a f) g) k c)
        (Qabs a * lw0_pitB_conv_pwi g k c
         + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c).
Proof.
  intros a f g k c.
  change (qpoly_mul (cons a f) g)
    with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))).
  apply (qleT'_trans
           (lw0_pitB_conv_pwi
              (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))) k c)
           (lw0_pitB_conv_pwi (qpoly_scalar a g) k c
            + lw0_pitB_conv_pwi (cons 0 (qpoly_mul f g)) k c)
           (Qabs a * lw0_pitB_conv_pwi g k c
            + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c)).
  - exact (lw0_pitB_conv_pwi_add_le (qpoly_scalar a g)
             (cons 0 (qpoly_mul f g)) k c).
  - change (lw0_pitB_conv_pwi (cons 0 (qpoly_mul f g)) k c)
      with (Qabs 0 * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c).
    apply (qeq_leT'
             (lw0_pitB_conv_pwi (qpoly_scalar a g) k c
              + (Qabs 0 * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                 + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c))
             (Qabs a * lw0_pitB_conv_pwi g k c
              + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c)).
    + rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_scalar a g k c)).
      assert (Ec0 : QeqT (Qabs 0%Q) 0%Q) by (unfold QeqT; cbn; reflexivity).
      rewrite (qeqT_imp_qeq _ _ Ec0).
      ring.
Qed.

Lemma lw0_pitB_conv_pwi_ai_le : forall (p : QPoly) (k : nat) (c : Q),
  QleT' (Qabs (c * qpoly_eval (lw0_qp_ai p k) c))
        (lw0_pitB_conv_pwi p k c).
Proof.
  intro p. induction p as [| a p IH]; intros k c.
  - change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' (Qabs (c * qpoly_eval (lw0_qp_ai nil k) c)) 0%Q).
    change (qpoly_eval (lw0_qp_ai nil k) c) with 0%Q.
    rewrite (Qmult_0_r c). apply Qeq_refl.
  - assert (Hltpos : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1)%Q)).
    { apply (Qlt_le_trans 0%Q 1%Q ((Z.of_nat (Datatypes.S k) # 1)%Q)).
      - apply QltT_to_Qlt. unfold QltT. reflexivity.
      - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one k)). }
    change (lw0_pitB_conv_pwi (cons a p) k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
    apply (qleT'_trans
             (Qabs (c * qpoly_eval (lw0_qp_ai (cons a p) k) c))
             (Qabs (c * (a / (Z.of_nat (Datatypes.S k) # 1)%Q))
              + Qabs (c * (c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c)))
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)).
    + apply Qle_to_QleT'.
      rewrite (lw0_qp_ai_cons_eval a p k c).
      assert (Esplit : c * (a / (Z.of_nat (Datatypes.S k) # 1)%Q
                            + c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c)
                     == c * (a / (Z.of_nat (Datatypes.S k) # 1)%Q)
                      + c * (c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c)) by ring.
      rewrite (Qabs_wd _ _ Esplit).
      apply Qabs_triangle.
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * assert (Ehead : Qabs (c * (a * / (Z.of_nat (Datatypes.S k) # 1)%Q))
                        == Qabs a * (Qabs c * / (Z.of_nat (Datatypes.S k) # 1)%Q)).
        { rewrite Qabs_Qmult, Qabs_Qmult.
          rewrite (lw0_Qabs_pos_eq (Qinv ((Z.of_nat (Datatypes.S k) # 1)%Q)))
            by (apply Qle_to_QleT'; apply Qinv_le_0_compat;
                apply Qlt_le_weak; exact Hltpos).
          ring. }
        unfold Qdiv, lw0_q_of_nat.
        rewrite Ehead. apply Qle_refl.
      * rewrite Qabs_Qmult.
        apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                 (Qabs (c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c))
                 (lw0_pitB_conv_pwi p (Datatypes.S k) c)
                 (IH (Datatypes.S k) c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.


Lemma lw0_pitB_conv_pair_weight_bound : forall (f g : QPoly) (q : Q),
  QleT' (Qabs (lw0_qp_pair f g q))
        (lw0_pitB_conv_pwi (qpoly_mul f g) 0 q).
Proof.
  intros f g q.
  apply (qleT'_trans (Qabs (lw0_qp_pair f g q))
                     (Qabs (q * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q))
                     (lw0_pitB_conv_pwi (qpoly_mul f g) 0 q)).
  - apply qeq_leT'.
    unfold lw0_qp_pair, lw0_qp_antideriv. cbn [qpoly_eval].
    apply Qabs_wd. ring.
  - exact (lw0_pitB_conv_pwi_ai_le (qpoly_mul f g) 0 q).
Qed.

Lemma lw0_pitB_conv_pair_vanish : forall (tau : nat -> QPoly) (Wg c eps : Q),
  QleT' 0 c -> QltT 0 eps -> QltT 0 Wg ->
  (forall M : nat,
     QleT' (lw0_pitB_conv_pwi (tau M) 0 c)
           (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))) ->
  sigT (fun M0 : nat => forall M : nat, (M0 <= M)%nat ->
    QltT (Qabs (c * qpoly_eval (lw0_qp_ai (tau M) 0) c)) eps).
Proof.
  intros tau Wg c eps Hc0 Heps HWg Hob.
  assert (Hne : Wg == 0%Q -> False) by (intros Hw0; exact (qltT_not_eq_zero Wg HWg Hw0)).
  assert (HepsW : QltT 0 (eps * / Wg)%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt _ _ Heps).
    - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ HWg). }
  destruct (lw0_pitB_conv_t_vanish c (eps * / Wg)%Q Hc0 HepsW)
    as [M0 [_ HM0]].
  exists M0. intros M HM.
  specialize (HM0 M HM).
  apply (lw0_leT'_ltT_trans
           (Qabs (c * qpoly_eval (lw0_qp_ai (tau M) 0) c))
           (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
           eps).
  - apply (qleT'_trans
             (Qabs (c * qpoly_eval (lw0_qp_ai (tau M) 0) c))
             (lw0_pitB_conv_pwi (tau M) 0 c)
             (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
    + exact (lw0_pitB_conv_pwi_ai_le (tau M) 0 c).
    + exact (Hob M).
  - apply (lw0_pitB_conv_qeqR_ltT
             (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
             (eps * / Wg * Wg)%Q eps).
    + apply (lw0_pitB_conv_qeqL_ltT
               (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
               (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)) * Wg)
               (eps * / Wg * Wg)%Q).
      * apply qeq_imp_qeqT. apply Qmult_comm.
      * apply Qlt_to_QltT.
        apply (Qmult_lt_compat_r
                 (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                 (eps * / Wg)%Q Wg).
        -- exact (QltT_to_Qlt _ _ HWg).
        -- exact (QltT_to_Qlt _ _ HM0).
    + apply qeq_imp_qeqT.
      rewrite <- Qmult_assoc, (Qmult_comm (/ Wg)%Q Wg), (Qmult_inv_r Wg Hne).
      apply (Qmult_1_r eps).
Qed.

(* ---------- 随块 PA 锚（N_β＝35＝声明面 25＋pwi 十件逐名追加；判定包锚数式 198＋N_β 供件） ---------- *)
Print Assumptions lw0_pitB_conv_lw0_succ.
Print Assumptions lw0_pitB_conv_mult_le_l.
Print Assumptions lw0_pitB_conv_pow2_ge.
Print Assumptions lw0_pitB_conv_half_le1.
Print Assumptions lw0_pitB_conv_half_mono.
Print Assumptions lw0_pitB_conv_pow_fact_domin.
Print Assumptions lw0_pitB_conv_div_mul_cancel.
Print Assumptions lw0_pitB_conv_geomscale.
Print Assumptions lw0_pitB_conv_qabs_pow.
Print Assumptions lw0_pitB_conv_m1_cases.
Print Assumptions lw0_pitB_conv_t_nonneg.
Print Assumptions lw0_pitB_conv_tstep.
Print Assumptions lw0_pitB_conv_tail_gen.
Print Assumptions lw0_pitB_conv_sin_term_abs.
Print Assumptions lw0_pitB_conv_sin_tail.
Print Assumptions lw0_pitB_conv_half_iter.
Print Assumptions lw0_pitB_conv_qthr.
Print Assumptions lw0_pitB_conv_qeqL_ltT.
Print Assumptions lw0_pitB_conv_qeqR_ltT.
Print Assumptions lw0_pitB_conv_t_vanish.
Print Assumptions lw0_pitB_conv_sin_vanish.
Print Assumptions lw0_pitB_conv_cos_term_abs.
Print Assumptions lw0_pitB_conv_cos_tail.
Print Assumptions lw0_pitB_conv_t_vanish_even.
Print Assumptions lw0_pitB_conv_cos_vanish.
Print Assumptions lw0_pitB_conv_pwi.
Print Assumptions lw0_pitB_conv_pwi_step.
Print Assumptions lw0_pitB_conv_pwi_scalar.
Print Assumptions lw0_pitB_conv_pwi_opp.
Print Assumptions lw0_pitB_conv_pwi_add_le.
Print Assumptions lw0_pitB_conv_pwi_mul_le.
Print Assumptions lw0_pitB_conv_pwi_ai_le.
Print Assumptions lw0_qp_pair.
Print Assumptions lw0_pitB_conv_pair_weight_bound.
Print Assumptions lw0_pitB_conv_pair_vanish.



(* [出处] 基座＝_tlw175 沙箱整件 LW0PiIrrational.v 6,577 行 md5
   2b104ee962b90d9a4129fe593d13249d（cp 入 _tlw183_sbx 前后双记全等）。
   入位锚点＝_tlw175 块（Print Assumptions lw0_Ktel_num22）之后、主语句备档区
   之前；随块无既有行改动、无 Separate Extraction 名单改动（本块零新可计算名）。 *)
(* [数学判定（本段实测）] 经典分解恒等式 I(q)=F(0)−cos q·F(q)+sin q·F'(q)
   （I(q)=∫₀^q f_n·sin，F=Σ(−1)^j f^(2j)）双路手算坐真：(a,b,n,q)=(1,1,2,1)
   时 I(1)≈0.00786 与 11−11·cos1−6·sin1≈0.007849 吻合（F(0)=11、F(1)=11、
   F'(1)=−6；K=F(0)+F(q)=22）。q=1（无 π 前提）时 I(1)≈0.00786≠22＝K——
   无前提传输命题为假，_tlw175 复证反例裁决；π 条件（sin q=0∧cos q=−1）下
   I(q)=F(0)+F(q)=K 闭合。 *)
(* [传输两语句逐字备档（终装取用形；证明体未落＝响亮缺供声明，禁假语句、
   禁承认词面，沿 _tlw175 先例）]
   [本段 vm_compute 判定（n=2,b=1,q=1 实测）]：lw0_Wb 1 1 2 0 = 1/240，
   而 ∫f_2·sin 首项 = (1/2)·B(4,3)·1 = 1/120 ⟹ Wb_j = 真级数项的 1/q_fact n 倍
   （Wb_1 = 1/4032 = (−1/2016)/2 同证；_tlw173 实测 0.00392＝altsum Wb 部分和
   与 I(1)/2＝0.00393 截断吻合）。故传输语句 K 侧必须携带 / q_fact n 归一：
   语句一（传输本体）：
   Lemma lw0_pi_transport_Wb_Ktel : forall (B q : Q) (n : nat)
     (Hc : cauchy (fun m : nat => altsum (lw0_Wb B q n) m)),
     real_eq real_pi_geom (real_const (Qnum q # Zpos (Qden q))) ->
     real_eq (lw0_L_of_seq (lw0_Wb B q n) Hc)
             (lw0_L_of_seq (lw0_Ktel_seq (Qnum q) (Zpos (Qden q)) n)
                           (lw0_Ktel_cauchy (Qnum q) (Zpos (Qden q)) n)).
   （变体：L(Wb) 与 real_const (lw0_K a' b' n / q_fact n) 的 real_eq 形——
     两形二择一，取决于 Ktel 侧是否同步乘 q_fact n，归一架桥钉定后择定。）
   语句二（复合推论，K 侧带 q_fact n 归一——终装取用形候选）：
   Lemma lw0_pi_transport_Wb_K : forall (B q : Q) (n : nat)
     (Hc : cauchy (fun m : nat => altsum (lw0_Wb B q n) m)),
     real_eq real_pi_geom (real_const (Qnum q # Zpos (Qden q))) ->
     real_eq (lw0_L_of_seq (lw0_Wb B q n) Hc)
             (real_const (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)).
   [指标面警示（响亮，后续件第一议题）]：K/n! 归一下 Kq 整数承载位
   （lw0_K_integer 给 K=(w#1)，K/n! 非必整）与主语句闸门布线的自洽性
   未钉——Wb 定义面 /n! 与 Ktel/K 面（无 /n!）的归一架桥（Wb 侧乘
   q_fact n 或 L 对象换底）须先钉定再填装，禁粗配对。） *)
(* [与 _tlw174 预跑 Hconn 对照（终装核对）] Hconn（Variable）: forall (B q : Q)
   (n : nat) (Hc : cauchy ...), real_eq (lw0_L_of_seq (lw0_Wb B q n) Hc)
   (real_const Kq)。终装替换：Hconn := fun B q n Hc =>
   lw0_pi_transport_Wb_K B q n Hc Hpi（π 前提穿到主语句假设位 Hpi：
   real_eq real_pi_geom (real_const (a / b))，与 Variable 面仅多一假设参，
   实例化 B:=Qabs b、q:=a/b、n:=lw0_n_select (10*d0) 0%nat、Hc:=步 2 柯西面
   （lw0_pi_chain_L_cauchy (Qabs b) (a/b) (10*d0) 0 Hab Hq0 Hq103）、
   Kq:=lw0_K (Qnum (a/b)) (Zpos (Qden (a/b))) (lw0_n_select (10*d0) 0)
   （整数见证 lw0_K_integer 随取）——_tlw174 六步布线（步 1／步 3+4／供件③／
   闸门）零改动。 *)

(* ---- π 条件推论砖（本段绿件）：1 + cos q == 0（实层） ----
   分解恒等式实层组装的首块砖：π 前提经 lw0_cos_endpoint_transport 降为
   cos q = −1，再经 real_plus 双边合同件 lw0_sin_plus_eq_compat 闭合
   1 + cos q == 0。sin q == 0 侧已在件（lw0_sin_endpoint_transport 绿）。 *)

Lemma lw0_real_const_refl : forall c : Q, real_eq (real_const c) (real_const c).
Proof.
  intros c. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_const]. ring.
Qed.

Lemma lw0_one_plus_neg_one_zero :
  real_eq (real_plus (real_const 1) (real_const (-1)%Q)) (real_const 0).
Proof.
  apply real_eq_of_zero_diff. intro n.
  change ((1 + (-1) - 0) == 0)%Q. ring.
Qed.

Lemma lw0_pi_one_plus_cos_zero : forall a b : Q,
  real_eq real_pi_geom (real_const (a / b)) ->
  real_eq (real_plus (real_const 1) (cauchy_real_cos (real_const (a / b))))
          (real_const 0).
Proof.
  intros a b Hp.
  apply (real_eq_trans
    (real_plus (real_const 1) (cauchy_real_cos (real_const (a / b))))
    (real_plus (real_const 1) (real_const (-1)%Q))
    (real_const 0)).
  - apply lw0_sin_plus_eq_compat.
    + apply lw0_real_const_refl.
    + apply lw0_cos_endpoint_transport. exact Hp.
  - exact lw0_one_plus_neg_one_zero.
Qed.

Print Assumptions lw0_real_const_refl.
Print Assumptions lw0_one_plus_neg_one_zero.
Print Assumptions lw0_pi_one_plus_cos_zero.

(* ================= §6 末段 ④ 归一架桥＋强化压制（_tlw190）施工面 ================= *)
(* [出处] 基座＝_tlw183 沙箱整件 LW0PiIrrational.v 6,662 行 md5
   a52dad5a5126c53aef8a3b2bff41697a（cp 入 _tlw190_sbx 前后双记全等）。
   入位锚点＝_tlw183 块（Print Assumptions lw0_pi_one_plus_cos_zero）之后、
   主语句备档区之前；随块零既有行改动、零 Separate Extraction 名单改动
   （本块全部新名为 Lemma，纯证明面，无新可计算定义名）。
   命名空间：lw0_pitS_*（π transport Scale 桥面）＋乙件主名 lw0_pi_w0n_lt1。
   [Arch-1 标定（依 _tlw183 判定结论：lw0_Wb 逐项＝∫f_n·sin 级数项的 1/q_fact n 倍，
   π 条件下 L(Wb) = K/q_fact n 非 K）] 受界对象改为缩放序列
   Wb' := fun j => q_fact n * lw0_Wb b q n j（逐项 Q 乘，cauchy 保持）：
   甲(a) 归一架桥＝altsum 逐项线性（Q 层）＋cauchy 正缩放保持＋实层桥
   real_eq (L(Wb')) (real_mult (real_const (q_fact n)) (L(Wb)))
   （real_mult 逐点形，S02 real_mult_proj 勘明后零成本落绿）；
   甲(b) 终装复合形＝scale-up ∘ 语句二传输 ∘ q_fact 消去，分解为三语句：
   S1＝lw0_pitS_scale_const（const-transport，绿）、S2＝_tlw183 备档语句二
   （传输件供体，本块以条件组装件 lw0_pitS_compose_Wbn_K 把它作假设位
   先行闭闸）、S3＝lw0_pitS_qfact_elim（Q 层消去，绿）。
   Kq 整数位自洽：终装复合形 RHS 取 real_const (lw0_K a' b' n) 直承
   （零 /n!）——/n! 全部被 Wb' 分子岸 q_fact n 吸收，lw0_K_integer 的
   (w#1) 承载位原样可用。
   [数值先行实录（本块绿件 lw0_pitS_num_* vm_compute 铁证）]
   (1,1,n) j=0 缩放值 q_fact n·Wb₀：n=2 → 1/120、n=3、n=5、n=42
   （d=1,k=0 的 lw0_n_select (10·1) 0）全 <1；桥两态：altsum Wb' 3 ==
   2·altsum Wb 3 且 Wb 3 == (1/2)·Wb' 3（漏乘 q_fact n 即错半，两态齐）；
   消去两态：q_fact 2·(lw0_K 1 1 2 / q_fact 2) == lw0_K 1 1 2 == 22。
   [乙件路线（强化压制＝③ 的 q_fact 分子岸升级，W'_0 < 1）] 闭式
   q_fact n·Wb₀ == b^n·q^(2n+2)·(n+1)!/(2n+2)!，经 lw0_q_fact_split
   因子表（(2n+2)! = (n+1)!·(n+2)⋯(2n+2)）与 lw0_fact_range_ge_pow
   尾段幂下界压到 d^n·(100/9)^(S n)/(n+2)^(S n)，再经 (5/9) 线性比
   q_of_nat d·(100/9) ≤ (5/9)·(n+2)（⟸ 20d ≤ n+2 ⟸ n = 22+2·max k (10d)
   ≥ 22+20d）与闭数值锚 (5/9)^n ≤ 5/9、500/81 < 24 ≤ n+2 收 <1。 *)

(* ---- Q 层小件 ---- *)

Lemma lw0_pitS_qne0_of_pos : forall x : Q, QltT 0 x -> ~ (x == 0).
Proof.
  intros x H Hz. exact (Qlt_not_eq 0 x (QltT_to_Qlt 0 x H) (Qeq_sym x 0 Hz)).
Qed.

Lemma lw0_pitS_q_pow_ne0 : forall (x : Q) (n : nat), ~ (x == 0) -> ~ (q_pow x n == 0).
Proof.
  intros x n H0. induction n as [|n IH].
  - intro Hz. vm_compute in Hz. discriminate.
  - intro Hz. destruct (Qmult_integral x (q_pow x n) Hz) as [Hx | Hx];
      [ exact (H0 Hx) | exact (IH Hx) ].
Qed.

Lemma lw0_pitS_qof_add : forall a b : nat,
  lw0_q_of_nat (a + b)%nat == lw0_q_of_nat a + lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qeq, Qplus. cbn [Qnum Qden].
  rewrite Nat2Z.inj_add. lia.
Qed.

Lemma lw0_pitS_qof_mul : forall a b : nat,
  lw0_q_of_nat (a * b)%nat == lw0_q_of_nat a * lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qeq, Qmult. cbn [Qnum Qden].
  rewrite Nat2Z.inj_mul. lia.
Qed.

Lemma lw0_pitS_q_pow_mul : forall (x y : Q) (t : nat),
  q_pow x t * q_pow y t == q_pow (x * y) t.
Proof.
  intros x y t. induction t as [|t IH].
  - reflexivity.
  - rewrite (q_pow_succ x t), (q_pow_succ y t), (q_pow_succ (x * y) t).
    rewrite <- IH. ring.
Qed.

Lemma lw0_pitS_qmul_div_cancel : forall c a d : Q,
  ~ (c == 0) -> ~ (d == 0) -> c * (a * / (c * d)) == a * / d.
Proof.
  intros c a d Hc0 Hd0.
  assert (Hcd : ~ (c * d == 0)).
  { intro Hz. destruct (Qmult_integral c d Hz) as [Hx | Hx];
      [ exact (Hc0 Hx) | exact (Hd0 Hx) ]. }
  assert (EL : (c * a * / (c * d)) * (c * d) == c * a).
  { rewrite <- (Qmult_assoc (c * a) (/ (c * d)) (c * d)),
      (Qmult_comm (/ (c * d)) (c * d)), (Qmult_inv_r (c * d) Hcd),
      Qmult_1_r. reflexivity. }
  assert (ER : (a * / d) * (c * d) == c * a).
  { rewrite <- (Qmult_assoc a (/ d) (c * d)), (Qmult_comm (/ d) (c * d)),
      <- (Qmult_assoc c d (/ d)), (Qmult_inv_r d Hd0).
    rewrite Qmult_1_r, (Qmult_comm a c). reflexivity. }
  assert (XL : (c * a * / (c * d) * (c * d)) * / (c * d)
               == c * a * / (c * d)).
  { rewrite <- Qmult_assoc, (Qmult_inv_r (c * d) Hcd), Qmult_1_r. reflexivity. }
  assert (XR : (a * / d * (c * d)) * / (c * d) == a * / d).
  { rewrite <- Qmult_assoc, (Qmult_inv_r (c * d) Hcd), Qmult_1_r. reflexivity. }
  assert (EY : (c * a * / (c * d) * (c * d)) * / (c * d)
               == (a * / d * (c * d)) * / (c * d)).
  { rewrite EL, ER. reflexivity. }
  apply (Qeq_trans _ (c * a * / (c * d))).
  - rewrite Qmult_assoc. reflexivity.
  - apply (Qeq_trans _ ((a * / d * (c * d)) * / (c * d))).
    + rewrite <- EY, EL. reflexivity.
    + exact XR.
Qed.

Lemma lw0_pitS_div_lt_one : forall x y : Q, QltT 0 y -> QltT x y -> QltT (x / y) 1.
Proof.
  intros x y Hy0 Hxy.
  assert (Hy : ~ (y == 0)) by (exact (lw0_pitS_qne0_of_pos y Hy0)).
  apply Qlt_to_QltT. rewrite <- (Qmult_inv_r y Hy).
  apply Qmult_lt_compat_r.
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Hy0.
  - apply QltT_to_Qlt. exact Hxy.
Qed.

Lemma lw0_pitS_qmult_reg_r : forall x y z : Q,
  QltT 0 z -> QleT' (x * z) (y * z) -> QleT' x y.
Proof.
  intros x y z Hz0 H.
  assert (Hne : ~ (z == 0)) by (exact (lw0_pitS_qne0_of_pos z Hz0)).
  assert (E : ((y * z) * / z)%Q == y).
  { rewrite <- (Qmult_assoc y z (/ z)), (Qmult_inv_r z Hne), Qmult_1_r.
    reflexivity. }
  apply (qleT'_trans _ ((y * z) * / z)%Q).
  - apply (qleT'_trans _ ((x * z) * / z)%Q).
    + apply qeq_leT'.
      rewrite <- (Qmult_assoc x z (/ z)), (Qmult_inv_r z Hne), Qmult_1_r.
      reflexivity.
    + apply Qle_to_QleT'. apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ H).
      * apply (Qlt_le_weak 0). apply Qinv_lt_0_compat.
        apply QltT_to_Qlt. exact Hz0.
  - apply qeq_leT'. exact E.
Qed.

Lemma lw0_pitS_pow_dec_helper : forall (x : Q) (t : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (q_pow x (Datatypes.S t)) (q_pow x t).
Proof.
  intros x t H0 H1.
  apply (qleT'_trans _ (x * q_pow x t)%Q).
  - apply qeq_leT'. apply q_pow_succ.
  - apply (qleT'_trans _ (1 * q_pow x t)%Q).
    + apply Qle_to_QleT'. apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ H1).
      * apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0).
    + apply qeq_leT'. rewrite Qmult_1_l. reflexivity.
Qed.

Lemma lw0_pitS_pow_le_base : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 -> (1 <= n)%nat -> QleT' (q_pow x n) x.
Proof.
  intros x n H0 H1 Hn.
  assert (Haux : forall t : nat, QleT' (q_pow x (Datatypes.S t)) x).
  { intro t. induction t as [|t IH].
    - cbn [q_pow]. apply Qle_to_QleT'.
      rewrite Qmult_1_r. apply Qle_refl.
    - apply (qleT'_trans _ (q_pow x (Datatypes.S t))).
      + apply lw0_pitS_pow_dec_helper; assumption.
      + exact IH. }
  destruct n as [|n']; [ lia | apply Haux ].
Qed.

(* ---- 甲(a)-1：altsum 逐项标量线性（Q 层） ---- *)

Lemma lw0_pitS_altsum_scale : forall (V : nat -> Q) (c : Q) (m : nat),
  altsum (fun j : nat => c * V j) m == c * altsum V m.
Proof.
  intros V c m. induction m as [|m IH].
  - unfold altsum.
    rewrite (altsum_acc_0_eq true (fun j : nat => c * V j) 0%nat),
            (altsum_acc_0_eq true V 0%nat). ring.
  - replace (Datatypes.S m)%nat with (m + 1)%nat by lia.
    rewrite lw0_altsum_add, lw0_altsum_add, !lw0_acc_sgp_one, IH. ring.
Qed.

(* ---- 甲(a)-2：cauchy 在正缩放下保持 ---- *)

Lemma lw0_pitS_cauchy_scale : forall (V : nat -> Q) (c : Q),
  QltT 0 c -> cauchy (fun m : nat => altsum V m) ->
  cauchy (fun m : nat => altsum (fun j : nat => c * V j) m).
Proof.
  intros V c Hc0 Hc eps Heps.
  assert (Hne : ~ (c == 0)) by (exact (lw0_pitS_qne0_of_pos c Hc0)).
  assert (Hepc : QltT 0 (eps / c)%Q).
  { apply Qlt_to_QltT. unfold Qdiv. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Hc0. }
  destruct (Hc (eps / c)%Q Hepc) as [N HN].
  exists N. intros m m' Hm Hm'.
  apply Qlt_to_QltT.
  rewrite (lw0_pitS_altsum_scale V c m), (lw0_pitS_altsum_scale V c m').
  assert (Hc0le : QleT' 0 c).
  { apply Qle_to_QleT'. apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact Hc0. }
  assert (Ed : (Qabs (c * altsum V m - c * altsum V m'))%Q
               == (c * Qabs (altsum V m - altsum V m'))%Q).
  { apply (Qeq_trans _ (Qabs (c * (altsum V m - altsum V m')))%Q).
    - apply Qabs_wd. ring.
    - rewrite Qabs_Qmult, (lw0_Qabs_pos_eq c Hc0le). reflexivity. }
  rewrite Ed.
  assert (Hlt : QltT (Qabs (altsum V m - altsum V m')) (eps / c)%Q)
    by (apply HN; assumption).
  assert (Hsc : Qlt (c * Qabs (altsum V m - altsum V m')) (c * (eps / c))%Q).
  { rewrite (Qmult_comm c (Qabs (altsum V m - altsum V m'))),
      (Qmult_comm c (eps / c)).
    apply Qmult_lt_compat_r;
      [ apply QltT_to_Qlt; exact Hc0 | apply QltT_to_Qlt; exact Hlt ]. }
  assert (E2 : (c * (eps / c))%Q == eps).
  { unfold Qdiv. field. exact Hne. }
  rewrite E2 in Hsc. exact Hsc.
Qed.

(* ---- 甲(a)-3：实层归一架桥（Arch-1 语句逐字：L(Wb') ≡ q_fact n·L(Wb)） ---- *)

Lemma lw0_pitS_sbridge_scale : forall (b q : Q) (n : nat)
  (Hc : cauchy (fun m : nat => altsum (lw0_Wb b q n) m)),
  real_eq (lw0_L_of_seq (fun j : nat => q_fact n * lw0_Wb b q n j)
                        (lw0_pitS_cauchy_scale (lw0_Wb b q n) (q_fact n)
                          (Qlt_to_QltT 0 (q_fact n) (q_fact_pos n)) Hc))
          (real_mult (real_const (q_fact n)) (lw0_L_of_seq (lw0_Wb b q n) Hc)).
Proof.
  intros b q n Hc. apply real_eq_of_zero_diff. intro m.
  rewrite real_mult_proj. cbn [projT1 real_const lw0_L_of_seq].
  rewrite lw0_pitS_altsum_scale. ring.
Qed.

(* ---- 甲(b)-S1：const-transport（复合形工作档；L 层最小线性） ---- *)

Lemma lw0_pitS_const_eq : forall u v : Q, u == v -> real_eq (real_const u) (real_const v).
Proof.
  intros u v H. apply real_eq_of_zero_diff. intro m.
  cbn [projT1 real_const]. rewrite H. ring.
Qed.

Lemma lw0_pitS_scale_const : forall (V : nat -> Q) (c y : Q)
  (Hc : cauchy (fun m : nat => altsum V m))
  (Hc' : cauchy (fun m : nat => altsum (fun j : nat => c * V j) m)),
  QltT 0 c ->
  real_eq (lw0_L_of_seq V Hc) (real_const y) ->
  real_eq (lw0_L_of_seq (fun j : nat => c * V j) Hc') (real_const (c * y)).
Proof.
  intros V c y Hc Hc' Hc0 H eps Heps.
  assert (Hne : ~ (c == 0)) by (exact (lw0_pitS_qne0_of_pos c Hc0)).
  assert (Hepc : QltT 0 (eps / c)%Q).
  { apply Qlt_to_QltT. unfold Qdiv. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. exact Heps.
    - apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Hc0. }
  destruct (H (eps / c)%Q Hepc) as [N HN].
  cbn [projT1 real_const] in HN.
  exists N. intros m Hm.
  cbn [projT1 lw0_L_of_seq real_const].
  apply Qlt_to_QltT.
  rewrite lw0_pitS_altsum_scale.
  assert (Hlt : QltT (Qabs (altsum V m - y)) (eps / c)%Q) by (apply HN; exact Hm).
  assert (Hc0le : QleT' 0 c).
  { apply Qle_to_QleT'. apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact Hc0. }
  assert (Ed : (Qabs (c * altsum V m - c * y))%Q
               == (c * Qabs (altsum V m - y))%Q).
  { apply (Qeq_trans _ (Qabs (c * (altsum V m - y)))%Q).
    - apply Qabs_wd. ring.
    - rewrite Qabs_Qmult, (lw0_Qabs_pos_eq c Hc0le). reflexivity. }
  rewrite Ed.
  assert (Hsc : Qlt (c * Qabs (altsum V m - y)) (c * (eps / c))%Q).
  { rewrite (Qmult_comm c (Qabs (altsum V m - y))), (Qmult_comm c (eps / c)).
    apply Qmult_lt_compat_r;
      [ apply QltT_to_Qlt; exact Hc0 | apply QltT_to_Qlt; exact Hlt ]. }
  assert (E2 : (c * (eps / c))%Q == eps).
  { unfold Qdiv. field. exact Hne. }
  rewrite E2 in Hsc. exact Hsc.
Qed.

(* ---- 甲(b)-S3：q_fact 消去（Q 层；Kq 整数位零 /n! 直承的代数根据） ---- *)

Lemma lw0_pitS_qfact_elim : forall (a b : Z) (n : nat),
  q_fact n * (lw0_K a b n / q_fact n) == lw0_K a b n.
Proof.
  intros a b n. unfold Qdiv. field.
  exact (lw0_q_fact_ne0 n).
Qed.

(* ---- 甲(b) 条件组装（绿）：语句二在位即终装复合形 ---- *)

Lemma lw0_pitS_compose_Wbn_K : forall (B q : Q) (n : nat)
  (Hc : cauchy (fun m : nat => altsum (lw0_Wb B q n) m)),
  real_eq (lw0_L_of_seq (lw0_Wb B q n) Hc)
          (real_const (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)) ->
  real_eq (lw0_L_of_seq (fun j : nat => q_fact n * lw0_Wb B q n j)
                        (lw0_pitS_cauchy_scale (lw0_Wb B q n) (q_fact n)
                          (Qlt_to_QltT 0 (q_fact n) (q_fact_pos n)) Hc))
          (real_const (lw0_K (Qnum q) (Zpos (Qden q)) n)).
Proof.
  intros B q n Hc H2.
  apply (real_eq_trans
    (lw0_L_of_seq (fun j : nat => q_fact n * lw0_Wb B q n j)
                  (lw0_pitS_cauchy_scale (lw0_Wb B q n) (q_fact n)
                    (Qlt_to_QltT 0 (q_fact n) (q_fact_pos n)) Hc))
    (real_const (q_fact n * (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)))
    (real_const (lw0_K (Qnum q) (Zpos (Qden q)) n))).
  - exact (lw0_pitS_scale_const (lw0_Wb B q n) (q_fact n)
             (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n) Hc
             (lw0_pitS_cauchy_scale (lw0_Wb B q n) (q_fact n)
               (Qlt_to_QltT 0 (q_fact n) (q_fact_pos n)) Hc)
             (Qlt_to_QltT 0 (q_fact n) (q_fact_pos n)) H2).
  - apply lw0_pitS_const_eq. apply lw0_pitS_qfact_elim.
Qed.

(* ---- 数值两态判据（vm_compute 铁证） ---- *)

Lemma lw0_pitS_num_bridge :
  (altsum (fun j : nat => q_fact 2 * lw0_Wb 1 1 2 j) 3
   == 2 * altsum (lw0_Wb 1 1 2) 3)%Q /\
  (altsum (lw0_Wb 1 1 2) 3
   == (1 # 2) * altsum (fun j : nat => q_fact 2 * lw0_Wb 1 1 2 j) 3)%Q.
Proof. split; vm_compute; reflexivity. Qed.

Lemma lw0_pitS_num_elim :
  (q_fact 2 * (lw0_K 1%Z 1%Z 2%nat / q_fact 2) == lw0_K 1%Z 1%Z 2%nat)%Q /\
  (lw0_K 1%Z 1%Z 2%nat == (22 # 1)%Q).
Proof. split; vm_compute; reflexivity. Qed.

Lemma lw0_pitS_num_w0n :
  Qlt (q_fact 2 * lw0_Wb 1 1 2 0) 1 /\
  Qlt (q_fact 3 * lw0_Wb 1 1 3 0) 1 /\
  Qlt (q_fact 5 * lw0_Wb 1 1 5 0) 1 /\
  (q_fact 2 * lw0_Wb 1 1 2 0 == (1 # 120))%Q /\
  Qlt (q_fact (lw0_n_select (10 * 1) 0)
       * lw0_Wb 1 1 (lw0_n_select (10 * 1) 0) 0) 1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ---- 乙件第 1 步闭式：j = 0 缩放恒等（q_fact 分子岸吸收定义面 /n!） ---- *)

Lemma lw0_pitS_Wbn0_scale_eq : forall (b q : Q) (n : nat),
  q_fact n * lw0_Wb b q n 0 ==
  q_pow b n * q_pow q (2 * n + 2) * q_fact (n + 1) / q_fact (2 * n + 2).
Proof.
  intros b q n. unfold lw0_Wb, Qdiv.
  replace (n + 2 * 0 + 1)%nat with (Datatypes.S n) by lia.
  replace (2 * n + 2 * 0 + 2)%nat with (Datatypes.S (Datatypes.S (2 * n))) by lia.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  replace (2 * n + 2)%nat with (Datatypes.S (Datatypes.S (2 * n))) by lia.
  replace (n + 1)%nat with (Datatypes.S n) by lia.
  assert (E1 : q_fact 1%nat == 1%Q) by reflexivity.
  rewrite E1, Qmult_1_r.
  apply (lw0_pitS_qmul_div_cancel (q_fact n)).
  - exact (lw0_q_fact_ne0 n).
  - apply lw0_pitS_qne0_of_pos. apply Qlt_to_QltT. apply q_fact_pos.
Qed.

(* ---- 乙件核：任意 n ≥ 22+20d 的强化压制 ---- *)

Lemma lw0_pitS_w0n_core : forall (b q : Q) (d n : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3) -> QleT' b (lw0_q_of_nat d) ->
  (22 + 2 * (10 * d) <= n)%nat ->
  QltT (q_fact n * lw0_Wb b q n 0) 1.
Proof.
  intros b q d n Hb Hq0 Hq103 Hbd Hn.
  assert (Hd1 : (1 <= d)%nat).
  { destruct d as [|d'].
    - exfalso.
      assert (Hz : QltT 0 (lw0_q_of_nat 0))
        by (apply (lw0_ltT_leT_trans 0 b (lw0_q_of_nat 0) Hb Hbd)).
      cbn [lw0_q_of_nat] in Hz. unfold QltT, Qlt_bool in Hz.
      cbn in Hz. inversion Hz.
    - lia. }
  assert (Hdp : QltT 0 (lw0_q_of_nat d)).
  { destruct d as [|d']; [ exfalso; lia | ].
    apply (lw0_ltT_leT_trans 0 1 (lw0_q_of_nat (Datatypes.S d'))).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply lw0_q_of_nat_ge_one. }
  assert (Hp2 : QltT 0 (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                              (Datatypes.S n))).
  { apply lw0_q_pow_pos.
    apply (lw0_ltT_leT_trans 0 1 (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply lw0_q_of_nat_ge_one. }
  assert (HRpos : QltT 0 (lw0_fact_range (Datatypes.S n) (Datatypes.S n))).
  { apply (lw0_ltT_leT_trans 0
             (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                    (Datatypes.S n)) _ Hp2
             (lw0_fact_range_ge_pow (Datatypes.S n) (Datatypes.S n))). }
  assert (Hlin : QleT' (lw0_q_of_nat d * (100 # 9))
                       ((5 # 9) * lw0_q_of_nat (n + 2))).
  { assert (E100 : ((100 # 9) * 9)%Q == 100%Q) by reflexivity.
    assert (E5x9 : ((5 # 9) * lw0_q_of_nat (n + 2) * 9)%Q
                   == (5 * lw0_q_of_nat (n + 2))%Q) by ring.
    apply (lw0_pitS_qmult_reg_r _ _ 9).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply Qle_to_QleT'.
      apply (Qle_trans _ (lw0_q_of_nat d * 100)%Q).
      + apply QleT'_to_Qle. apply qeq_leT'. ring.
      + apply (Qle_trans _ (lw0_q_of_nat (5 * (n + 2)))).
        * apply QleT'_to_Qle.
          apply (qleT'_trans _ (lw0_q_of_nat (100 * d))).
          -- apply qeq_leT'.
             assert (Eq1 : (lw0_q_of_nat d * 100)%Q
                           == lw0_q_of_nat (100 * d)%nat).
             { rewrite (lw0_pitS_qof_mul 100 d).
               replace (lw0_q_of_nat 100)%Q with 100%Q by reflexivity.
               apply Qmult_comm. }
             exact Eq1.
          -- apply lw0_q_of_nat_le_mono. lia.
        * apply QleT'_to_Qle. apply qeq_leT'.
          assert (Eq2 : (5 * lw0_q_of_nat (n + 2))%Q
                        == lw0_q_of_nat (5 * (n + 2))%nat).
          { rewrite (lw0_pitS_qof_mul 5 (n + 2)).
            replace (lw0_q_of_nat 5)%Q with 5%Q by reflexivity.
            reflexivity. }
          symmetry in Eq2.
          assert (Eall : (lw0_q_of_nat (5 * (n + 2))
                          == (5 # 9) * lw0_q_of_nat (n + 2) * 9)%Q).
          { apply (Qeq_trans _ (5 * lw0_q_of_nat (n + 2))%Q).
            - exact Eq2.
            - symmetry. exact E5x9. }
          exact Eall. }
  replace (n + 2)%nat with (Datatypes.S (Datatypes.S n))%nat in Hlin by lia.
  assert (H509 : QleT' 0 (5 # 9))
    by (apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia).
  assert (H511 : QleT' (5 # 9) 1)
    by (apply Qle_to_QleT'; unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hp : QleT' 0 (lw0_q_of_nat d * (100 # 9))%Q).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (0 * (100 # 9))%Q).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg d)).
      + apply QleT'_to_Qle. apply Qle_to_QleT'.
        unfold Qle. cbn [Qnum Qden]. lia. }
  assert (Hmono : QleT' (q_pow (lw0_q_of_nat d * (100 # 9)) n)
                        (q_pow ((5 # 9) * lw0_q_of_nat
                                  (Datatypes.S (Datatypes.S n))) n))
    by (apply lw0_q_pow_mono_base; [ exact Hp | exact Hlin ]).
  assert (Pform : (q_pow (10 / 3) (Datatypes.S n + Datatypes.S n)
                   == (100 # 9) * q_pow (100 # 9) n)%Q).
  { rewrite (lw0_q_pow_add (10 / 3) (Datatypes.S n) (Datatypes.S n)),
      (lw0_pitS_q_pow_mul (10 / 3) (10 / 3) (Datatypes.S n)).
    assert (E1009 : ((10 / 3) * (10 / 3))%Q == (100 # 9)%Q) by reflexivity.
    rewrite E1009. apply q_pow_succ. }
  assert (HMsucc : (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                    * lw0_q_of_nat (Datatypes.S (Datatypes.S n))
                    == q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                             (Datatypes.S n))%Q).
  { rewrite (Qmult_comm (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
              (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
    rewrite <- (q_pow_succ (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n).
    reflexivity. }
  assert (Hqt : forall u v w : Q, u == v -> QltT w u -> QltT w v).
  { intros u v w Huv Hwu. apply Qlt_to_QltT. rewrite <- Huv.
    apply QltT_to_Qlt. exact Hwu. }
  assert (H500 : QltT (500 # 81)
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
  { apply (lw0_ltT_leT_trans (500 # 81) (lw0_q_of_nat 24) _).
    - apply Qlt_to_QltT. vm_compute. reflexivity.
    - apply lw0_q_of_nat_le_mono. lia. }
  assert (Hstr : QltT (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                       * (500 # 81))%Q
                      (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                             (Datatypes.S n))).
  { apply (Hqt _ _ _ HMsucc).
    apply Qlt_to_QltT.
    rewrite (Qmult_comm (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
              (500 # 81)),
            (Qmult_comm (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
              (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
    apply Qmult_lt_compat_r.
    - apply QltT_to_Qlt. apply lw0_q_pow_pos.
      apply (lw0_ltT_leT_trans 0 1
               (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
      + apply Qlt_to_QltT. unfold Qlt. reflexivity.
      + apply lw0_q_of_nat_ge_one.
    - apply QltT_to_Qlt. exact H500. }
  assert (Hbig : QleT' (q_pow (lw0_q_of_nat d) n
                        * ((100 # 9) * q_pow (100 # 9) n))%Q
                       (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                        * (500 # 81))%Q).
  { apply (qleT'_trans _
      (q_pow (lw0_q_of_nat d * (100 # 9)) n * (100 # 9))%Q).
    - apply qeq_leT'.
      rewrite <- (lw0_pitS_q_pow_mul (lw0_q_of_nat d) (100 # 9) n). ring.
    - apply (qleT'_trans _
        (q_pow ((5 # 9) * lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
         * (100 # 9))%Q).
      + apply Qle_to_QleT'. apply Qmult_le_compat_r.
        * exact (QleT'_to_Qle _ _ Hmono).
        * apply QleT'_to_Qle. apply Qle_to_QleT'.
          unfold Qle. cbn [Qnum Qden]. lia.
      + apply (qleT'_trans _
          (q_pow (5 # 9) n
           * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
           * (100 # 9))%Q).
        * apply qeq_leT'.
          rewrite (lw0_pitS_q_pow_mul (5 # 9)
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n).
          reflexivity.
        * apply (qleT'_trans _
            (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
             * (q_pow (5 # 9) n * (100 # 9)))%Q).
          -- apply qeq_leT'. ring.
          -- apply (qleT'_trans _
              (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
               * ((5 # 9) * (100 # 9)))%Q).
            ++ apply Qle_to_QleT'.
               rewrite (Qmult_comm (q_pow (lw0_q_of_nat
                                            (Datatypes.S (Datatypes.S n))) n)
                         (q_pow (5 # 9) n * (100 # 9))),
                       (Qmult_comm (q_pow (lw0_q_of_nat
                                            (Datatypes.S (Datatypes.S n))) n)
                         ((5 # 9) * (100 # 9))).
               apply Qmult_le_compat_r.
               ** apply Qmult_le_compat_r.
                  assert (Hn1 : (1 <= n)%nat) by lia.
                  --- exact (QleT'_to_Qle _ _
                        (lw0_pitS_pow_le_base (5 # 9) n H509 H511 Hn1)).
                  --- apply QleT'_to_Qle. apply Qle_to_QleT'.
                     unfold Qle. cbn [Qnum Qden]. lia.
               ** exact (QleT'_to_Qle _ _
                          (lw0_q_pow_nonnegT (lw0_q_of_nat
                            (Datatypes.S (Datatypes.S n))) n
                            (lw0_q_of_nat_nonneg
                              (Datatypes.S (Datatypes.S n))))).
            ++ apply qeq_leT'. reflexivity. }
  assert (Hb0 : QleT' 0 b)
    by (apply Qle_to_QleT'; apply (Qlt_le_weak 0); apply QltT_to_Qlt; exact Hb).
  assert (Hbpow : QleT' (q_pow b n) (q_pow (lw0_q_of_nat d) n))
    by (apply lw0_q_pow_mono_base; [ exact Hb0 | exact Hbd ]).
  assert (Hqp : QleT' (q_pow q (Datatypes.S n + Datatypes.S n))
                      (q_pow (10 / 3) (Datatypes.S n + Datatypes.S n)))
    by (apply lw0_q_pow_mono_base; [ exact Hq0 | exact Hq103 ]).
  assert (Hprod : QleT' (q_pow b n * q_pow q (Datatypes.S n + Datatypes.S n))%Q
                        (q_pow (lw0_q_of_nat d) n
                         * q_pow (10 / 3) (Datatypes.S n + Datatypes.S n))%Q).
  { apply (qleT'_trans _ (q_pow (lw0_q_of_nat d) n
                          * q_pow q (Datatypes.S n + Datatypes.S n))%Q).
    - apply Qle_to_QleT'. apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hbpow).
      + apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hq0).
    - apply Qle_to_QleT'.
      rewrite (Qmult_comm (q_pow (lw0_q_of_nat d) n)
                (q_pow q (Datatypes.S n + Datatypes.S n))),
              (Qmult_comm (q_pow (lw0_q_of_nat d) n)
                (q_pow (10 / 3) (Datatypes.S n + Datatypes.S n))).
      apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hqp).
      + apply q_pow_nonneg.
        exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg d)). }
  apply Qlt_to_QltT. rewrite lw0_pitS_Wbn0_scale_eq.
  replace (2 * n + 2)%nat with (Datatypes.S n + Datatypes.S n)%nat by lia.
  replace (n + 1)%nat with (Datatypes.S n)%nat by lia.
  rewrite lw0_q_fact_split.
  apply QltT_to_Qlt.
  apply (lw0_leT'_ltT_trans _
    (q_pow (lw0_q_of_nat d) n * q_pow (10 / 3) (Datatypes.S n + Datatypes.S n)
     / q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
             (Datatypes.S n))%Q).
  - apply Qle_to_QleT'. unfold Qdiv.
    replace (10 * / 3)%Q with (10 / 3)%Q by reflexivity.
    rewrite <- (Qmult_assoc (q_pow b n * q_pow q (Datatypes.S n + Datatypes.S n))
              (q_fact (Datatypes.S n))
              (/ (q_fact (Datatypes.S n)
                  * lw0_fact_range (Datatypes.S n) (Datatypes.S n)))).
    rewrite (Qinv_mult_distr (q_fact (Datatypes.S n))
              (lw0_fact_range (Datatypes.S n) (Datatypes.S n))).
    rewrite (Qmult_assoc (q_fact (Datatypes.S n)) (/ (q_fact (Datatypes.S n)))
              (/ (lw0_fact_range (Datatypes.S n) (Datatypes.S n)))).
    rewrite (Qmult_inv_r (q_fact (Datatypes.S n))
              (lw0_q_fact_ne0 (Datatypes.S n))).
    rewrite Qmult_1_l.
    apply Qmult_le_compat_nonneg.
    + split.
      * exact (QleT'_to_Qle _ _
                (lw0_qmul_le0T (q_pow b n)
                  (q_pow q (Datatypes.S n + Datatypes.S n))
                  (lw0_q_pow_nonnegT b n Hb0)
                  (lw0_q_pow_nonnegT q (Datatypes.S n + Datatypes.S n) Hq0))).
      * exact (QleT'_to_Qle _ _ Hprod).
    + split.
      * apply (Qlt_le_weak 0). apply Qinv_lt_0_compat.
        apply QltT_to_Qlt. exact HRpos.
      * apply QleT'_to_Qle.
        exact (lw0_inv_le (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                            (Datatypes.S n))
                (lw0_fact_range (Datatypes.S n) (Datatypes.S n))
                Hp2 HRpos
                (lw0_fact_range_ge_pow (Datatypes.S n) (Datatypes.S n))).
  - apply lw0_pitS_div_lt_one.
    + exact Hp2.
    + apply (lw0_leT'_ltT_trans _
        (q_pow (lw0_q_of_nat d) n
         * ((100 # 9) * q_pow (100 # 9) n))%Q).
      * apply qeq_leT'. rewrite Pform. reflexivity.
      * apply (lw0_leT'_ltT_trans _
          (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
           * (500 # 81))%Q).
        -- exact Hbig.
        -- exact Hstr.
Qed.

(* ============================================================
   模块：lw0_pi_d0_of ／ lw0_pi_d0_absorb（d0 自然数吸收）
   使命：对任意正有理数 |b|，给出自然数阈值
         d0 := Z.to_nat (Z.succ (Qceiling (Qabs b)))（上取整加一，
         |b| 严格小于 d0 且无负截断歧义），并证明
         QleT' (Qabs b) (lw0_q_of_nat d0)——即 |b| 被 d0 的
         nat→Q 嵌入吸收；供 lw0_pi_w0n_lt1 第四前提
         QleT' b (lw0_q_of_nat d) 以 b := Qabs b、d := d0
         按 b 选阈值直接代入。
   依赖：本件 lw0_q_of_nat 界面（nat→Q 嵌入）与 QleT'/QltT
         序型及其桥接引理 Qle_to_QleT'、QltT_to_Qlt；Stdlib
         QArith（Qle_ceiling、Qle_trans、Qlt_le_weak）、
         ZArith（Z.to_nat、Z.succ、Z2Nat.id）、Lia。
   对标：Niven, A simple proof that pi is irrational（1947）
         链内阈值选择；上取整见证配方同本件 lw0_Wb_vanish
         （Qceiling 上取整＋Z.to_nat (Z.succ …)）。
   构造性：语句 Set 层承载（QltT/QleT'、nat）；零公理、
         零承认、零经典逻辑；支持 Separate Extraction。
   编译配方：coqc -Q ConstructiveWorld_vo "" LW0PiIrrational.v
         （独立预验形：Require Import LW0PiIrrational. 检验件，
         双 loadpath -Q . "" -Q ConstructiveWorld_vo ""）
   ============================================================ *)

Definition lw0_pi_d0_of (b : Q) : nat := Z.to_nat (Z.succ (Qceiling (Qabs b))).

Lemma lw0_pi_d0_absorb : forall b : Q,
  QltT 0 (Qabs b) -> QleT' (Qabs b) (lw0_q_of_nat (lw0_pi_d0_of b)).
Proof.
  intros b Hab.
  assert (Hbpos : Qlt 0 (Qabs b)) by (apply QltT_to_Qlt; exact Hab).
  assert (Hcq : Qle 0 (Qceiling (Qabs b) # 1)).
  { apply (Qle_trans 0 (Qabs b) (Qceiling (Qabs b) # 1)).
    - apply (Qlt_le_weak 0). exact Hbpos.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling (Qabs b))%Z) by (unfold Qle in Hcq; simpl in Hcq; lia).
  apply Qle_to_QleT'.
  unfold lw0_pi_d0_of, lw0_q_of_nat.
  rewrite Z2Nat.id by lia.
  apply (Qle_trans (Qabs b) (Qceiling (Qabs b) # 1)
                   ((Z.succ (Qceiling (Qabs b))) # 1)).
  - apply Qle_ceiling.
  - unfold Qle. simpl. lia.
Qed.

Print Assumptions lw0_pi_d0_absorb.

(* ---- 乙件主名：强化压制（③ 的 q_fact n 分子岸升级，W'_0 < 1） ---- *)

Lemma lw0_pi_w0n_lt1 : forall (b q : Q) (d k : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3) -> QleT' b (lw0_q_of_nat d) ->
  QltT (q_fact (lw0_n_select (10 * d) k)
        * lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1.
Proof.
  intros b q d k H1 H2 H3 H4.
  apply (lw0_pitS_w0n_core b q d (lw0_n_select (10 * d) k) H1 H2 H3 H4).
  unfold lw0_n_select. pose proof (Nat.le_max_r k (10 * d)). lia.
Qed.

Print Assumptions lw0_pitS_qne0_of_pos.
Print Assumptions lw0_pitS_q_pow_ne0.
Print Assumptions lw0_pitS_qof_add.
Print Assumptions lw0_pitS_qof_mul.
Print Assumptions lw0_pitS_q_pow_mul.
Print Assumptions lw0_pitS_qmul_div_cancel.
Print Assumptions lw0_pitS_div_lt_one.
Print Assumptions lw0_pitS_qmult_reg_r.
Print Assumptions lw0_pitS_pow_dec_helper.
Print Assumptions lw0_pitS_pow_le_base.
Print Assumptions lw0_pitS_altsum_scale.
Print Assumptions lw0_pitS_cauchy_scale.
Print Assumptions lw0_pitS_sbridge_scale.
Print Assumptions lw0_pitS_const_eq.
Print Assumptions lw0_pitS_scale_const.
Print Assumptions lw0_pitS_qfact_elim.
Print Assumptions lw0_pitS_compose_Wbn_K.
Print Assumptions lw0_pitS_num_bridge.
Print Assumptions lw0_pitS_num_elim.
Print Assumptions lw0_pitS_num_w0n.
Print Assumptions lw0_pitS_Wbn0_scale_eq.
Print Assumptions lw0_pitS_w0n_core.
Print Assumptions lw0_pi_w0n_lt1.

(* ---------- π 传输语句面（尾项估计假设形） ---------- *)
(* 模块名与数学使命：lw0_pi_transport_Wb_K_tail——π 前提下 Wb 交错和序列
   与 K 的 q_fact 归一值的实层传输语句，规范实例化形（序列 B 槽钉 q 的
   分母位 (Zpos (Qden q) # 1)）；余留分析缺口（sin/cos 部分和尾界联合给出
   的 N(eps) 显式见证，Niven 分解实层组装）以显式尾项估计假设承载——
   该假设消去即得终装传输语句。
   依赖清单：lw0_real_eq_const_tail、lw0_Wb、lw0_K、q_fact、lw0_altsum_add、
   lw0_altseq_rem_le、lw0_Wb_seq_nonneg、lw0_Wb_seq_decr、lw0_QltT_le、
   altsum、altsum_sgp（皆在件绿，均在本块之前定义）。
   对标行：语句形沿主语句备档区传输语句修正形（B 全称消除、钉
   (Zpos (Qden q) # 1) 规范实例化形）；尾项假设形沿 lw0_real_eq_const_tail
   前提位逐字。
   构造性注记：语句与两尾件全 Set 载体（QeqT/QltT/real_eq/cauchy/sigT），
   零裸 Prop；尾项配对界（任意起点的首项支配形）为 N(eps) 显式见证
   构造的机械面实例，供后续段与 π 桥合流消去尾项假设。
   编译配方：coqc -Q ConstructiveWorld_vo "" -Q . ""（本件名随所在箱）。 *)
Lemma lw0_pi_transport_Wb_K_tail : forall (q : Q) (n : nat)
  (Hc : cauchy (fun m : nat => altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) m)),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall m : nat, NatLe N m ->
       QltT (Qabs (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) m
                    - lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)) eps)) ->
  real_eq (lw0_L_of_seq (lw0_Wb (Zpos (Qden q) # 1)%Q q n) Hc)
          (real_const (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)).
Proof.
  intros q n Hc Ht.
  apply (lw0_real_eq_const_tail (lw0_Wb (Zpos (Qden q) # 1)%Q q n)
           (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n) Hc).
  exact Ht.
Qed.

(* 尾项配对界：Wb 交错和前向差的绝对值被起点项支配——非负＋递减
   下的首项支配形（余项引擎直收），N(eps) 显式见证构造的原料件。 *)
Lemma lw0_Wb_altsum_pair_tail : forall (b q : Q) (n : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10 / 3) -> (2 <= n)%nat ->
  forall (m r : nat),
  QleT' (Qabs (altsum (lw0_Wb b q n) (m + r)%nat - altsum (lw0_Wb b q n) m))
        (lw0_Wb b q n m).
Proof.
  intros b q n Hb Hq Hq103 Hn m r.
  assert (Ed : (altsum (lw0_Wb b q n) (m + r)%nat
                - altsum (lw0_Wb b q n) m)%Q
               == altsum_acc (altsum_sgp m) (lw0_Wb b q n) m r).
  { rewrite lw0_altsum_add. ring. }
  apply (qleT'_trans
           (Qabs (altsum (lw0_Wb b q n) (m + r)%nat
                  - altsum (lw0_Wb b q n) m)%Q)
           (Qabs (altsum_acc (altsum_sgp m) (lw0_Wb b q n) m r))
           (lw0_Wb b q n m)).
  - apply qeq_leT'. apply Qabs_wd. exact Ed.
  - apply lw0_altseq_rem_le.
    + intros k. apply lw0_Wb_seq_nonneg;
        [ apply lw0_QltT_le; exact Hb | exact Hq ].
    + intros k. apply lw0_Wb_seq_decr;
        [ apply lw0_QltT_le; exact Hb | exact Hq | exact Hq103 | exact Hn ].
Qed.

Print Assumptions lw0_pi_transport_Wb_K_tail.
Print Assumptions lw0_Wb_altsum_pair_tail.

(* ---------- π 桥承载块：N(eps) 值识别半·qp 配对收敛承载形（transport eps 链段 2） ----------
   模块名与数学使命：把 311 lw0_pi_transport_Wb_K_tail 之显式尾项假设 Ht 的值识别半
   做成实在战术链——主件 lw0_pi_pair_conv_altsum_tail 沿 α 桥 lw0_pitB_bridge
   （altsum(Wb)(S m) == (1/n!)·<f,σ_m>，零前提在件绿）把 Wb 侧 eps 尾项形式
   规约到 qp 配对侧收敛形式（Niven IBP 机器的原生栖息面）；承载件
   lw0_pi_transport_Wb_K_ht_gap 按 prescribed 供件接口
   （lw0_pi_transport_Wb_K_ht 同型＋一显式缺口前提位）落语句面，余留分析
   缺口（<f,σ_m>(q) → K 的实层收敛＝π 前提消项＋IBP 望远镜＋端点 K_leg
   闭合，即 ③ B 车道 (β) 三项收敛装配余量）以显式假设承载，证体一行
   （pair_conv 合流）闭合 PA 归零——GAPASUME 工艺沿 311 判例；prescribed
   名 lw0_pi_transport_Wb_K_ht 本块让出不占，终形消缺口后
   「lw0_pi_transport_Wb_K_ht q n Hpi := _ht_gap q n Hpi <niven 实例>」
   一行落供件，321 Part B 三行原样生效。
   依赖清单：lw0_pi_transport_Wb_K_tail（本块无直接使用——其使用在终形
   终形三行；本块直依赖面如下）、lw0_pitB_bridge、lw0_Wb_altseq_cauchy、
   lw0_Wb、lw0_K、lw0_niven_f、lw0_sin_qp、lw0_qp_pair、lw0_div_lt、
   NatLe_drop、NatLe_lift、Qcompare_comp、Qlt_to_QltT、QltT_to_Qlt、
   Qmult_lt_0_compat、Qmult_1_r、Qabs_wd、altsum、q_fact、q_fact_pos
   （皆在件绿，均在本块之前定义）。
   对标行：语句面沿 prescribed 供件签名逐字（π 前提带红点
   1 勘修正形 real_const ((Qnum q # Qden q)%Q)——299 草案 Zpos 形病态
   禁复活）；缺口假设形沿 lw0_pitB_conv_pair_vanish 结论同款 eps-sigT 形；
   Hab 退出使用链按 §一.8② 裁定，正性接班微件 lw0_pi_b_den_pos 构造子级
   闭合（Qcompare 0 < Zpos p）；尾界除法消去 lw0_div_lt 逐字使用。
   构造性注记：全件 Set 载体（QeqT/QltT/real_eq/cauchy/sigT），零裸 Prop；
   零承认词面（四禁词不直书）；π 前提在承载件面零消费（321 Part C 先例：
   承载不使用合规，使用位在终形缺口实例内部）；段 3 升形已被 _tail 证体
   固化（apply lw0_real_eq_const_tail），本块主件即终形 Ht 槽的机械全供。
   编译配方：coqc -Q ConstructiveWorld_vo "" -Q . ""（本件名随所在箱）。 *)

(* Hab 退出使用链接班微件（§一.8②）：钉界分母位 b' := (Zpos (Qden q) # 1)
   的正性——Qcompare 构造子级闭（Qnum 0 = Z0，Z.compare 0 (Zpos p) = Lt）。 *)
Lemma lw0_pi_b_den_pos : forall q : Q, QltT 0 ((Zpos (Qden q) # 1)%Q).
Proof.
  intros q. destruct (Qden q); reflexivity.
Qed.

(* π 前提表示桥微件：q/1 == q——端点传输件（lw0_sin_endpoint_transport 等
   a/b 形）在钉界 q 处的输入桥（Qinv (1#1) 定义归约，Qmult_1_r 收尾）。 *)
Lemma lw0_pi_qdiv_one_self : forall q : Q, (q / 1)%Q == q.
Proof.
  intros q.
  assert (E1 : (Qinv (1 # 1))%Q == (1 # 1)%Q) by reflexivity.
  unfold Qdiv. rewrite E1. apply Qmult_1_r.
Qed.

(* 钉界 b' 处柯西证书（Hc 供件；Hab 退出使用链的接班实例）：泛型件
   lw0_Wb_altseq_cauchy 在 B := b' 处实例化，正性槽喂 lw0_pi_b_den_pos。 *)
Lemma lw0_pi_b'_altseq_cauchy : forall (q : Q) (n : nat),
  QltT 0 q -> QleT' q (10 / 3) -> (2 <= n)%nat ->
  cauchy (fun m : nat => altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) m).
Proof.
  intros q n Hq Hq103 Hn.
  apply lw0_Wb_altseq_cauchy.
  - apply lw0_pi_b_den_pos.
  - exact Hq.
  - exact Hq103.
  - exact Hn.
Qed.

(* Qeq 右岸 QltT 换形微件（Qcompare_comp 轮；E446/QEQREWRITE 合规通道——
   Qeq 改写禁穿 QltT 壳，先在 Qcompare 层换岸再回注）。 *)
Lemma lw0_pi_qeq_ltT_r : forall x y e : Q, x == y -> QltT y e -> QltT x e.
Proof.
  intros x y e Hxy Hy.
  unfold QltT, Qlt_bool in Hy.
  assert (Hcmp : (x ?= e)%Q = (y ?= e)%Q)
    by exact (Qcompare_comp x y Hxy e e (Qeq_refl e)).
  unfold QltT, Qlt_bool. rewrite Hcmp. exact Hy.
Qed.

(* 主件：qp 配对收敛 ⟹ Wb 侧 eps 尾项形式（311 _tail 之 Ht 槽机械全供）。
   沿 α 桥 lw0_pitB_bridge 换岸：altsum(Wb)(S m) == (1/n!)·<f,σ_m>，差式闭于
   (1/n!)·(<f,σ_m>−c)（unfold Qdiv 后 ring）；尾界配对以 (eps·n!) 计（与
   lw0_div_lt 的 y*z 参序逐字对齐），绝对值标度闭于 Qabs_wd 面后除法消去
   lw0_div_lt 直收；后继指数经 NatLe_drop／NatLe_lift 轮换。 *)
Lemma lw0_pi_pair_conv_altsum_tail : forall (b q : Q) (n : nat) (c : Q),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun M : nat => forall m : nat, NatLe M m ->
       QltT (Qabs (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q - c)) eps)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall m' : nat, NatLe N m' ->
    QltT (Qabs (altsum (lw0_Wb b q n) m' - c / q_fact n)) eps).
Proof.
  intros b q n c Hpair eps Heps.
  assert (Hqf : QltT 0 (q_fact n)).
  { apply Qlt_to_QltT. apply q_fact_pos. }
  assert (Hscale : QltT 0 (eps * q_fact n)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. exact Heps.
    - apply q_fact_pos. }
  destruct (Hpair (eps * q_fact n) Hscale) as [M HM].
  exists (Datatypes.S M). intros m' Hm'.
  assert (Hle : (Datatypes.S M <= m')%nat) by exact (NatLe_drop _ _ Hm').
  destruct m' as [|m].
  - exfalso. lia.
  - assert (HmM : NatLe M m) by (apply NatLe_lift; lia).
    specialize (HM m HmM).
    assert (Hbr := lw0_pitB_bridge m b q n).
    apply (lw0_pi_qeq_ltT_r
             (Qabs (altsum (lw0_Wb b q n) (Datatypes.S m) - c / q_fact n))
             (Qabs (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q - c)
              / q_fact n) eps).
    + assert (HE : Qabs (altsum (lw0_Wb b q n) (Datatypes.S m) - c / q_fact n)
                   == Qabs (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q - c)
                      / q_fact n).
      { assert (Hinvpos : Qle 0 (1 * / q_fact n)).
        { apply Qmult_le_0_compat.
          - unfold Qle. cbn [Qnum Qden]. lia.
          - apply Qinv_le_0_compat. apply (Qlt_le_weak 0). apply q_fact_pos. }
        apply (Qeq_trans
                 (Qabs (altsum (lw0_Wb b q n) (Datatypes.S m) - c / q_fact n))
                 (Qabs (1 / q_fact n
                        * (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q
                           - c)))
                 (Qabs (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q - c)
                  / q_fact n)).
        - apply Qabs_wd. rewrite Hbr. unfold Qdiv. ring.
        - change (1 / q_fact n) with (1 * / q_fact n).
          rewrite Qabs_Qmult.
          rewrite (Qabs_pos (1 * / q_fact n) Hinvpos).
          unfold Qdiv. ring. }
      exact HE.
    + exact (lw0_div_lt
               (Qabs (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q - c))
               eps (q_fact n) Hqf HM).
Qed.

(* 承载件（GAPASUME 工艺沿 311 判例；321 prescribed 供件接口同型＋缺口位）：
   段 2 供件承载形——余留分析缺口＝<f,σ_m>(q) → K 的实层收敛（Niven IBP
   望远镜＋π 前提消项＋端点 K_leg 闭合，即 ③ B 车道 (β) 三项收敛装配余量，
   终形施工逐字对表本假设面）；π 前提按红点 1 勘修正形承载
   （real_const ((Qnum q # Qden q)%Q)），其使用位在终形缺口实例内部
   （lw0_sin_endpoint_transport／lw0_cos_endpoint_transport 经
   lw0_pi_qdiv_one_self 表示桥取用）。证体一行（pair_conv 合流）闭合。
   prescribed 名 lw0_pi_transport_Wb_K_ht 让出不占：终形消缺口后
   `Lemma lw0_pi_transport_Wb_K_ht : forall q n, <π前提> -> <Ht 形> :=
     fun q n Hpi => lw0_pi_transport_Wb_K_ht_gap q n Hpi <niven 实例>`
   一行落供件，321 Part B 三行原样入主件即终形活体。 *)
Lemma lw0_pi_transport_Wb_K_ht_gap : forall (q : Q) (n : nat),
  real_eq real_pi_geom (real_const ((Qnum q # Qden q)%Q)) ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun M : nat => forall m : nat, NatLe M m ->
       QltT (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp m) q
                   - lw0_K (Qnum q) (Zpos (Qden q)) n)) eps)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall m : nat, NatLe N m ->
    QltT (Qabs (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) m
                 - lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)) eps).
Proof.
  intros q n Hpi Hgap.
  exact (lw0_pi_pair_conv_altsum_tail (Zpos (Qden q) # 1)%Q q n
           (lw0_K (Qnum q) (Zpos (Qden q)) n) Hgap).
Qed.

(* ---------- 随块 PA 锚 ---------- *)
Print Assumptions lw0_pi_b_den_pos.
Print Assumptions lw0_pi_qdiv_one_self.
Print Assumptions lw0_pi_b'_altseq_cauchy.
Print Assumptions lw0_pi_qeq_ltT_r.
Print Assumptions lw0_pi_pair_conv_altsum_tail.
Print Assumptions lw0_pi_transport_Wb_K_ht_gap.

(* ---- ② π 钉点端点微件对（钉点＝(Qnum q # Qden q) 规范拼写；
        端点双件 a/b 形禁以 num/den 对实例化——值 q/(Qden q) 错点——
        本对经 compat 核直供任意钉点） ---- *)
Lemma lw0_pi_pin_sin_zero : forall q : Q,
  real_eq real_pi_geom (real_const (Qnum q # Qden q)) ->
  real_eq (cauchy_real_sin (real_const (Qnum q # Qden q))) real_zero.
Proof.
  intros q Hpi.
  apply (real_eq_trans (cauchy_real_sin (real_const (Qnum q # Qden q)))
                       (cauchy_real_sin real_pi_geom) real_zero).
  - apply real_sin_eq_compat. apply real_eq_sym. exact Hpi.
  - exact pi_geom_sin_pi_zero.
Qed.

Lemma lw0_pi_pin_cos_neg_one : forall q : Q,
  real_eq real_pi_geom (real_const (Qnum q # Qden q)) ->
  real_eq (cauchy_real_cos (real_const (Qnum q # Qden q))) (real_const (-1)%Q).
Proof.
  intros q Hpi.
  apply (real_eq_trans (cauchy_real_cos (real_const (Qnum q # Qden q)))
                       (cauchy_real_cos real_pi_geom) (real_const (-1)%Q)).
  - apply real_cos_eq_compat. apply real_eq_sym. exact Hpi.
  - exact pi_geom_cos_pi_neg_one.
Qed.

Print Assumptions lw0_pi_pin_sin_zero.
Print Assumptions lw0_pi_pin_cos_neg_one.

(* ---- ③ 主件块（终形替换完成注记）：主件终形活体已在位——行首 Theorem lw0_pi_transport_Wb_K 计 1（备档区带内，随块 PA 逐发全净 Closed）；本位原注释形态件（语句面草案＋骨架装配注记）功成拆除。 ---- *)

(* ---- ⑤ F 家族预算单调件（切片 B2 die 链第一砖） ----
   [使命] lw0_die p m = true 且 m ≤ k 则 lw0_die p k = true——F 家族使用位
   （lw0_F_plus_deriv2 的 die (2·S J) 位）供件链的预算单调基座；niven_f_z
   表长 2n+1（mono n·qminus_pow q n 卷积），B2 沿本件接 die-mul 链证
   n ≤ J -> die (lw0_niven_f_z q b n) (2·S J) = true。
   [依赖] lw0_die 定义（双支出形 Fixpoint）／andb_true_iff／NatLe 算术 lia。
   [对标] F 家族段头注记（lw0_F_aux/lw0_F_plus_deriv2 使用形）。
   [构造性注记] bool 等式面＋nat 算术，零 Q 层零 Prop 载体；零公理零经典。
   [编译配方] 同④。 *)
Lemma lw0_die_budget_mono : forall (p : QPoly) (m k : nat),
  lw0_die p m = true -> (m <= k)%nat -> lw0_die p k = true.
Proof.
  induction p as [|a p IH]; intros m k Hm Hk.
  - reflexivity.
  - destruct m as [|m'].
    + cbn [lw0_die] in Hm. discriminate Hm.
    + cbn [lw0_die] in Hm. apply andb_true_iff in Hm.
      destruct Hm as [H1 H2].
      destruct k as [|k'].
      * lia.
      * cbn [lw0_die]. apply andb_true_iff. split.
        -- apply (IH (Datatypes.S m') (Datatypes.S k')); [ exact H1 | lia ].
        -- apply (IH m' k'); [ exact H2 | lia ].
Qed.

Print Assumptions lw0_die_budget_mono.

(* ---------- die 链 sharp 形六件（自建单 §③ 证体级落地） ---------- *)
(* [使命] F 家族使用位（lw0_F_plus_deriv2 的 die (2·S J) 位）供件链六件：
   die-scalar 消去／die-add 副加（341 新勘件）／die-mul sharp 形（S(a+b) 精确
   预算——328 ⑦ 松形在迭代 mul 下预算松弛累积闭不住，341 sharp 裁定）／
   mono·qminus_pow 两支件／niven_f 终件（J:=n 直接代入形）。
   [依赖] lw0_die 定义（双支出形）／qpoly_add·scalar·mul（§1 区）／上邻块 ⑤
   lw0_die_budget_mono／lw0_pi_mono·qminus_pow·niven_f 定义面／andb_true_iff／lia。
   [对标] 328 B2 缺口清单⑥⑦之 282 侧自建形（205 箱松形异构禁混引）；
   自建单六件表与 diechain draft 语句面逐字（证体修正四处响亮登记于 347/347R
   回执；第四处＝347R：件 3 S a' 支 g0/g' 未绑定残病，实参回 g 整体）。
   [构造性注记] bool 等式面＋nat 算术，零 Q 层零 Prop 载体；零承认零假设零经典。
   [编译配方] cpu_guard 包裹；coqc -Q . "" -Q ConstructiveWorld_vo ""（9.1 全路径）。 *)
Lemma lw0_die_scalar : forall (c : Q) (p : qpoly) (M : nat),
  lw0_die (qpoly_scalar c p) M = lw0_die p M.
Proof.
  intros c p. induction p as [|b p IH]; intros M.
  - reflexivity.
  - destruct M as [|M'].
    + reflexivity.
    + cbn [lw0_die qpoly_scalar].
      rewrite (IH (Datatypes.S M')). rewrite (IH M'). reflexivity.
Qed.
Print Assumptions lw0_die_scalar.

Lemma lw0_die_add : forall (M : nat) (p q : qpoly),
  lw0_die p M = true -> lw0_die q M = true ->
  lw0_die (qpoly_add p q) M = true.
Proof.
  intros M p. revert M. induction p as [|a p' IH]; intros M q Hp Hq.
  - exact Hq.
  - destruct q as [|b q'].
    + exact Hp.
    + destruct M as [|M'].
      * cbn [lw0_die] in Hp. discriminate Hp.
      * cbn [lw0_die] in Hp. cbn [lw0_die] in Hq.
        apply andb_true_iff in Hp. destruct Hp as [Hp1 Hp2].
        apply andb_true_iff in Hq. destruct Hq as [Hq1 Hq2].
        cbn [lw0_die qpoly_add]. apply andb_true_iff. split.
        -- exact (IH (Datatypes.S M') q' Hp1 Hq1).
        -- exact (IH M' q' Hp2 Hq2).
Qed.
Print Assumptions lw0_die_add.

Lemma lw0_die_mul_sharp : forall (f g : qpoly) (a b : nat),
  lw0_die f (Datatypes.S a) = true -> lw0_die g (Datatypes.S b) = true ->
  lw0_die (qpoly_mul f g) (Datatypes.S (a + b)) = true.
Proof.
  intros f g. induction f as [|f0 f IH]; intros a b Hf Hg.
  - reflexivity.
  - destruct a as [|a'].
    + destruct f as [|x f'].
      * replace (Datatypes.S (Datatypes.O + b))%nat
          with (Datatypes.S b)%nat by lia.
        apply (lw0_die_add (Datatypes.S b) (qpoly_scalar f0 g) (cons 0%Q nil)).
        -- rewrite lw0_die_scalar. exact Hg.
        -- reflexivity.
      * cbn [lw0_die] in Hf. apply andb_true_iff in Hf.
        destruct Hf as [Hf1 Hf2]. discriminate Hf2.
    + cbn [lw0_die] in Hf. apply andb_true_iff in Hf.
      destruct Hf as [Hf1 Hf2].
      replace (Datatypes.S (Datatypes.S a' + b))%nat
        with (Datatypes.S (Datatypes.S (a' + b)))%nat by lia.
      apply (lw0_die_add (Datatypes.S (Datatypes.S (a' + b)))
               (qpoly_scalar f0 g)
               (cons 0%Q (qpoly_mul f g))).
      * rewrite lw0_die_scalar.
        apply (lw0_die_budget_mono _ (Datatypes.S b)
                 (Datatypes.S (Datatypes.S (a' + b))) Hg). lia.
      * cbn [lw0_die]. apply andb_true_iff. split.
        -- apply (lw0_die_budget_mono _ (Datatypes.S (a' + b))
                    (Datatypes.S (Datatypes.S (a' + b)))
                    (IH a' b Hf2 Hg)). lia.
        -- exact (IH a' b Hf2 Hg).
Qed.
Print Assumptions lw0_die_mul_sharp.

Lemma lw0_pi_mono_die : forall m : nat,
  lw0_die (lw0_pi_mono m) (Datatypes.S m) = true.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - cbn [lw0_pi_mono].
    replace (Datatypes.S (Datatypes.S m))%nat
      with (Datatypes.S (m + 1))%nat by lia.
    apply (lw0_die_mul_sharp (lw0_pi_mono m) (cons 0%Q (cons 1%Q nil)) m 1).
    + exact IH.
    + reflexivity.
Qed.
Print Assumptions lw0_pi_mono_die.

Lemma lw0_pi_qminus_pow_die : forall (q : Q) (n : nat),
  lw0_die (lw0_pi_qminus_pow q n) (Datatypes.S n) = true.
Proof.
  intros q n. induction n as [|n IH].
  - reflexivity.
  - cbn [lw0_pi_qminus_pow].
    replace (Datatypes.S (Datatypes.S n))%nat
      with (Datatypes.S (n + 1))%nat by lia.
    apply (lw0_die_mul_sharp (lw0_pi_qminus_pow q n)
             (cons q (cons (-1)%Q nil)) n 1).
    + exact IH.
    + reflexivity.
Qed.
Print Assumptions lw0_pi_qminus_pow_die.

Lemma lw0_niven_f_die : forall (q b : Q) (n : nat),
  lw0_die (lw0_niven_f q b n) (2 * Datatypes.S n) = true.
Proof.
  intros q b n. unfold lw0_niven_f.
  rewrite lw0_die_scalar.
  apply (lw0_die_budget_mono _ (Datatypes.S (n + n)) (2 * Datatypes.S n)).
  - apply (lw0_die_mul_sharp (lw0_pi_mono n) (lw0_pi_qminus_pow q n) n n).
    + exact (lw0_pi_mono_die n).
    + exact (lw0_pi_qminus_pow_die q n).
  - lia.
Qed.
Print Assumptions lw0_niven_f_die.

(* ---------- 段 2b 接口契约块（R1＝355 §四 R1 反号修复形逐字；R2＝GAPASUME 承载形交棒） ----------
   [谱系] 332 需求定形→341 接口正本 e1aada59→355 判定（staged 边界号整体反号致消逝面假命题，冻结）→
   本块落 355 §四 R1 修复形。落装前反测复做绿（独立反测脚本核验）：
   staged 形泛点极限非零三实例复确认（m=15：−3.080605／−155.337141／+1713.975340）；
   修复形 rtail 体 ≡ pair(F,σ_m+σ″_m) 4 实例×m=1..9 精确全等→0。
   [R1] telescope 边界两处号差＝F 项带 (-1)、F′ 项去 (-1)（staged 形整体反号；名/类型/前提/其余项零改）。
   [R2 缺口＝终形段目标形] ①HK：lw0_K (Qnum q) (Zpos (Qden q)) n ==
   F(0)+F(q)（K 闭式；对应 F0 六实例 n=0..5 精确真，在件零先例）；②Hpair：pair(f,σ_m)(q) −
   [F(0)+F′(q)σ_m(q)−F(q)σ′_m(q)] → 0（即 pair(F,σ_m+σ″_m) 消逝＝IBP 恒等式＋poly 级
   F_plus_deriv2 变体〔NOEVALIFT L1860 管辖〕＋σ″ 三件＋pwi 链装配）。承载形证体已闭
   （Qabs_wd＋lw0_pi_qeq_ltT_r＋ring 三步，零公理零缺口壳）；终形落装工艺（ht 款，9809 区先例）＝
   终形证 ①② 后一行落 `lw0_pitB_pair_rtail_vanish`（本块让出不占名位）；2c 使用形候终形，
   或带 ①② 前提上提改写。 *)

(* 接口面 1／3：尾项泛名（341 e1aada59 类型面冻结；体＝355 §四 R1 钉死形；2c 零展开 opaque） *)
Definition lw0_pitB_pair_rtail (q : Q) (n m : nat) : Q :=
  lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp m) q
  - lw0_K (Qnum q) (Zpos (Qden q)) n
  + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
      * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
  - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
      * qpoly_eval (lw0_sin_qp m) q.

(* 接口面 2／3：望远镜恒等（R1 修复形＝355 §四 R1 逐字；证体 unfold＋ring 零耗） *)
Lemma lw0_pitB_pair_telescope : forall (q : Q) (n m : nat),
  lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp m) q
  == lw0_K (Qnum q) (Zpos (Qden q)) n
     + (-1)%Q * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
         * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
     + qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
         * qpoly_eval (lw0_sin_qp m) q
     + lw0_pitB_pair_rtail q n m.
Proof.
  intros q n m.
  unfold lw0_pitB_pair_rtail.
  ring.
Qed.

(* 接口面 3／3：尾项消逝——GAPASUME 承载形（缺口＝上注 ①HK＋②Hpair；两前提承载、
   零公理；结论面＝341 e1aada59 接口面 3 语句逐字；终形名位让出不占） *)
Lemma lw0_pitB_pair_rtail_vanish_gap : forall (q : Q) (n : nat),
  lw0_K (Qnum q) (Zpos (Qden q)) n
  == qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
     + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
       QltT (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp m) q
                   - qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
                   - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                       * qpoly_eval (lw0_sin_qp m) q
                   + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                       * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n HK Hpair eps Heps.
  destruct (Hpair eps Heps) as [Mt HMt].
  exists Mt.
  intros m Hm.
  specialize (HMt m Hm).
  apply (lw0_pi_qeq_ltT_r
           (Qabs (lw0_pitB_pair_rtail q n m))
           (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp m) q
                  - qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
                  - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                      * qpoly_eval (lw0_sin_qp m) q
                  + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                      * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps).
  - apply Qabs_wd.
    unfold lw0_pitB_pair_rtail.
    rewrite HK.
    ring.
  - exact HMt.
Qed.

(* ---------- 随块 PA 锚（三新名逐发 Closed 判读） ---------- *)
Print Assumptions lw0_pitB_pair_rtail.
Print Assumptions lw0_pitB_pair_telescope.
Print Assumptions lw0_pitB_pair_rtail_vanish_gap.

(* ---------- 主语句备档（陈述形逐字；证明体候一步供件） ---------- *)

(* Theorem lw0_pi_irrational :
     forall a b : Q,
       QltT 0 (Qabs b) ->
       real_eq real_pi_geom (real_const (a / b)) ->
       sigT (fun c : Q => And (QltT 0 c)
               (real_lt (real_const c)
                  (real_metric real_pi_geom (real_const (a / b))))).

   链路备档：Hp 供 lw0_pi_asm_q_Wband 得 0 < q ≤ 10/3（步 1）；取
   n := lw0_n_select d k，lw0_niven_f 给 f_n（步 2）；B := Qabs b 供
   lw0_pi_chain_L_cauchy／lw0_pi_chain_L_bounds 得 0 < L(f_n) < W_0
   （步 3＋步 4）；lw0_K_integer 供 K = (z#1)（步 5）；W 序列值与 K 值的
   Q 层等值连接语句（S07 增量面 lw0_K_leg_connect）到位后送
   lw0_pi_contra_gate 得 Id false true（步 6），经 lw0_pi_irrational_exit
   得 apartness 出口（步 7）。 *)

(* 缺供声明（fail-loud 缺供声明）：主语句证明体
   未填装。三层结构现状：① 砖件层——连接块九名已在件（本段段头，
   LW0Integrality2 1072 版逐字入件）；② 分析性等值层——lw0_K_leg_connect
   （形 2：real_eq (lw0_L_of_seq ...) (real_const (lw0_K a' b' n))，
   Wb 交错项和与导数端点和的 IBP 望远镜恒等）缺供；③ 压制终跳——
   原记 W_0 < 1 严格形缺供（在件 lw0_Wb0_dominated 右岸 (n/2)^(n/2) 级
   压制强度不足）。现状更新：③ 部分补齐——lw0_qfact_split_lower（双
   range 分裂下界）与 lw0_pi_w0_lt1_core（压制数值核）两件已入本件绿；
   终跳件 lw0_pi_w0_lt1（W_0<1 严格形，取形
   QltT (lw0_Wb b q (lw0_n_select (10*d) k) 0) 1，前提含基座联动
   QleT' b (lw0_q_of_nat d)）证明体未落，段尾备档。主语句证明体
   仍待填装（缺 ② 与 ③ 终跳件）。另：形 1（Qeq 直连 W_0 == K）与形 3（有限截断
   altsum == K）经 n=2 数值验算为假，禁用。禁承认词面占位。 *)
     (* （备档毕·已激活引（激活于落点＝② 原生备档区死名位；本区＝③ 区随件拷贝留注释态，永禁激活）。） *)

(* 假设面与提取面：每条语句 Closed，可计算内容全量 Separate Extraction。 *)
From Stdlib Require Import Extraction.
(* 提取面按节序并集：§1 qpoly 三名｜§1 阶乘引擎三名｜§3 尾 W 机械一名｜
   §4 反导数机械三名｜§5 整数性机械十六名｜§6 前段二十二名。单命令多行形——多条 Separate
   Extraction 命令相互覆盖主产物（预演二号坑 7）。 *)
(* ---------- 主语句（已激活升格；本区＝② 原生备档区唯一激活落点） ---------- *)


     (* 缺供声明（已闭）：备档毕·已激活引——主语句证明体已按 F3 修正形填装（激活落点＝本区；③ 区随件拷贝留注释态永禁激活，激活唯一性红线 280 红点③）。 *)

(* 假设面与提取面：每条语句 Closed，可计算内容全量 Separate Extraction。 *)
From Stdlib Require Import Extraction.
(* 提取面按节序并集：§1 qpoly 三名｜§1 阶乘引擎三名｜§3 尾 W 机械一名｜
   §4 反导数机械三名｜§5 整数性机械十六名｜§6 前段二十二名。单命令多行形——多条 Separate
   Extraction 命令相互覆盖主产物（预演二号坑 7）。 *)
Print Assumptions qpoly_deriv_mul.
Print Assumptions qpoly_deriv_comp_scale.
Print Assumptions qpoly_deriv_iter_succ.
Print Assumptions qpoly_deriv_iter_commute.
Print Assumptions lw0_sin_reflection.
Print Assumptions lw0_gap_dichotomy.
Print Assumptions lw0_sin_pos_pi.
Print Assumptions lw0_fact_lower_growth.
Print Assumptions lw0_pi_bound_dominated_even.
Print Assumptions lw0_pi_bound_dominated_odd.
Print Assumptions lw0_Wb_lt01.
Print Assumptions lw0_L_f_n_pos.
Print Assumptions lw0_L_f_n_upper.
Print Assumptions lw0_Wb0_dominated.
Print Assumptions lw0_real_const_le.
Print Assumptions lw0_qp_antideriv_deriv.
Print Assumptions lw0_qp_antideriv_deriv_at.
Print Assumptions lw0_qp_pair_add_l.
Print Assumptions lw0_qp_pair_ibp.
Print Assumptions lw0_qp_pair_ibp_family.
Print Assumptions lw0_qp_ai_deriv_ft_pow.
Print Assumptions lw0_sin_aux_eval.
Print Assumptions lw0_sin_qp_eval.
Print Assumptions lw0_sin_qp_zero_eval.
Print Assumptions lw0_cos_aux_eval.
Print Assumptions lw0_cos_partial_zero.
Print Assumptions lw0_cos_qp_eval.
Print Assumptions lw0_cos_qp_zero_eval.
Print Assumptions lw0_sin_aux_deriv_eval.
Print Assumptions lw0_cos_aux_deriv_eval_S.
Print Assumptions lw0_sin_qp_deriv_eval.
Print Assumptions lw0_cos_qp_deriv_eval.
Print Assumptions lw0_real_lt_const_Qlt.
Print Assumptions lw0_sin_endpoint_transport.
Print Assumptions lw0_cos_endpoint_transport.
Print Assumptions lw0_endpoint_transport.
Print Assumptions lw0_pi_asm_q_bounds.
Print Assumptions lw0_pi_mono_eval.
Print Assumptions lw0_pi_qminus_pow_eval.
Print Assumptions lw0_niven_f.
Print Assumptions lw0_niven_f_eval.
Print Assumptions lw0_n_select.
Print Assumptions lw0_n_select_ge_b.
Print Assumptions lw0_n_select_dominated.
Print Assumptions lw0_n_select_dominated_of_qle.
Print Assumptions lw0_pi_asm_q_bounds_upper_QleT'.
Print Assumptions lw0_n_select_fact_lower.
Print Assumptions lw0_real_lt_const_Qlt_inv.
Print Assumptions lw0_pi_asm_q_pos.
Print Assumptions lw0_pi_asm_q_Wband.
Print Assumptions lw0_n_select_ge_2.
Print Assumptions lw0_pi_geom_metric_proj.

(* §4 适配三件＋§5 整数性全语句＋§3 尾消逝见证两件的 Closed 自审面。 *)
Print Assumptions qpoly_zero.
Print Assumptions qpoly_opp.
Print Assumptions lw0_mono.
Print Assumptions lw0_eval_opp.
Print Assumptions lw0_Qmake_plus.
Print Assumptions lw0_Qmake_succ.
Print Assumptions lw0_Qmake_succ_eq.
Print Assumptions lw0_coef.
Print Assumptions lw0_coef_add.
Print Assumptions lw0_coef_scalar.
Print Assumptions lw0_coef_opp.
Print Assumptions lw0_coef_deriv.
Print Assumptions lw0_coef_iter_mul.
Print Assumptions lw0_coef_iter_add.
Print Assumptions lw0_coef_iter_scalar.
Print Assumptions lw0_coef_iter_opp.
Print Assumptions lw0_eval_at_zero.
Print Assumptions lw0_eval_deriv_coef0.
Print Assumptions lw0_eval_zero_coef.
Print Assumptions lw0_eval_len_indep.
Print Assumptions lw0_coef_iter_congr.
Print Assumptions lw0_eval_iter_congr.
Print Assumptions lw0_eval_deriv_iter_add.
Print Assumptions lw0_eval_deriv_iter_scalar.
Print Assumptions lw0_eval_iter_opp.
Print Assumptions lw0_pred_iter.
Print Assumptions lw0_shift_deriv.
Print Assumptions lw0_qtail.
Print Assumptions lw0_qtail_deriv_congr.
Print Assumptions lw0_qtail_step.
Print Assumptions lw0_coef_mul_mono_lt.
Print Assumptions lw0_coef_mul_mono_ge.
Print Assumptions lw0_qminus_pow.
Print Assumptions lw0_niven_f_z.
Print Assumptions lw0_niven_deriv_zero_0.
Print Assumptions lw0_coef_mul_h0.
Print Assumptions lw0_coef_mul_hS.
Print Assumptions lw0_coef_qminus_pow.
Print Assumptions lw0_ratio.
Print Assumptions lw0_fact_ratio.
Print Assumptions lw0_Qmake_mul.
Print Assumptions lw0_qfact_Z.
Print Assumptions lw0_int_fact_div.
Print Assumptions lw0_binom.
Print Assumptions lw0_binom_pascal.
Print Assumptions lw0_binom_0.
Print Assumptions lw0_binom_out.
Print Assumptions lw0_zsign.
Print Assumptions lw0_zsign_step.
Print Assumptions lw0_z_lo.
Print Assumptions lw0_z_lo_integer.
Print Assumptions lw0_z_hi.
Print Assumptions lw0_z_hi_integer.
Print Assumptions lw0_Wb_vanish.
Print Assumptions lw0_Wb_altseq_cauchy.
(* §4 段体更新追加件＋§5 K 装配段＋§6 后段装配面：公理自审追加。 *)
Print Assumptions qpoly_map.
Print Assumptions lw0_q_abs_div.
Print Assumptions lw0_q_eq_le.
Print Assumptions lw0_q_mult_le_l.
Print Assumptions lw0_qp_ai_abs_bound.
Print Assumptions lw0_pair_abs_bound.
Print Assumptions lw0_deriv_iter_nil.
Print Assumptions lw0_deriv_add_eval.
Print Assumptions lw0_deriv_iter_cons_add_joint.
Print Assumptions lw0_deriv_iter_add_eval.
Print Assumptions lw0_deriv_iter_cons_eval.
Print Assumptions lw0_die.
Print Assumptions lw0_die_zero.
Print Assumptions lw0_alt.
Print Assumptions lw0_alt_opp.
Print Assumptions lw0_deriv2_scalar_eval.
Print Assumptions lw0_F_aux_plus_deriv2.
Print Assumptions lw0_F_plus_deriv2.
Print Assumptions lw0_sin_series_real.
Print Assumptions lw0_cos_series_real.
Print Assumptions lw0_sin_series_real_eq.
Print Assumptions lw0_cos_series_real_eq.
Print Assumptions lw0_qsum.
Print Assumptions lw0_sigT_plus.
Print Assumptions lw0_sigT_Zscale.
Print Assumptions lw0_qsum_integer.
Print Assumptions lw0_K_leg_else_zero.
Print Assumptions lw0_K_leg_integer.
Print Assumptions lw0_K_integer.
Print Assumptions lw0_pi_chain_L_cauchy.
Print Assumptions lw0_pi_chain_L_bounds.
Print Assumptions lw0_pi_contra_gate.
Print Assumptions lw0_pi_irrational_exit.
(* §6 后段连接引理块＋等值传递小壳：公理自审追加（conn_lo/conn_hi 自审
   线已随连接块在件）。 *)
Print Assumptions Powpos.
Print Assumptions lw0_posnat_zeq.
Print Assumptions lw0_zpower_nat_add.
Print Assumptions lw0_zpos_pospow.
Print Assumptions lw0_q_pow_qmake.
Print Assumptions lw0_q_pow_m1.
Print Assumptions lw0_bpa_binom_eq.
Print Assumptions lw0_real_lt_eq_transport_l.
Print Assumptions lw0_real_lt_eq_transport_r.
(* 压制终跳砖件（lw0_qfact_split_lower＋lw0_pi_w0_lt1_core）公理自审追加。 *)
Print Assumptions lw0_q_pow_add.
Print Assumptions lw0_qfact_split_lower.
Print Assumptions lw0_qmult_lt_compat_r.
Print Assumptions lw0_pi_w0_lt1_core.
Print Assumptions lw0_pi_w0_lt1.

(* ================= 361R 片一：q 端点导数事实件（M-对应主引理＋配套小件族） ================= *)
(* ================================================================== *)
(* 361R 片一：q 端点导数事实件（M-对应主引理＋配套小件族）                *)
(* 素材源：358R 冻结草稿 §2.2-2.4；工艺变更定案：                    *)
(*   ① assoc 须 D1(scalar-left)+D2(add-left) 铺底（mul 首槽递归结构判定） *)
(*   ② 边界 j=0 弃 falling/二项式读数，走 B(i,m) 自足对应族（双二项递推） *)
(*   ③ 交付件＝lw0_niven_deriv_mirror_even（eval D^(2j) f q == ... 0 形） *)
(*   ④ B/M 系数形取 lw0_alt 直乘（草稿 (lw0_alt # 1) Qmake 面 # 左参须 Z—— Z 槽笔误修正）  *)
(* 全块 born-in-place，只使用既有在件，零新公理。                        *)
(* ================================================================== *)

(* ---- 右零消去：add p nil == p（mul_add_left 铺底；cons 支定义性自反） ---- *)
Lemma lw0_add_nil_r : forall p : QPoly, qpoly_add p nil = p.
Proof.
  intro p. destruct p as [|a p].
  - reflexivity.
  - reflexivity.
Qed.

(* ---- 右零系数化：mul p nil 的 coef 全零（mul_comm 铺底；coefwise 已证） ---- *)
Lemma lw0_mul_nil_r_coef : forall (p : QPoly) (j : nat),
  lw0_coef j (qpoly_mul p nil) == 0.
Proof.
  induction p as [|a p IH]; intro j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q p) nil)
      with (qpoly_add (qpoly_scalar a nil) (cons 0%Q (qpoly_mul p nil))).
    cbn [qpoly_scalar qpoly_add].
    destruct j as [|j']; cbn [lw0_coef].
    + ring.
    + rewrite (IH j'). ring.
Qed.

(* ---- D1：scalar 穿 mul 首槽（coef 级，B 表归纳） ---- *)
Lemma lw0_mul_scalar_left : forall (a : Q) (B C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (qpoly_scalar a B) C)
  == a * lw0_coef j (qpoly_mul B C).
Proof.
  intros a B. induction B as [|b B IH]; intros C j.
  - cbn [qpoly_scalar qpoly_mul lw0_coef]. ring.
  - cbn [qpoly_scalar].
    change (qpoly_mul (cons (a * b)%Q (qpoly_scalar a B)) C)
      with (qpoly_add (qpoly_scalar (a * b)%Q C)
                      (cons 0%Q (qpoly_mul (qpoly_scalar a B) C))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    change (qpoly_mul (cons b%Q B) C)
      with (qpoly_add (qpoly_scalar b C) (cons 0%Q (qpoly_mul B C))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH C j'). ring.
Qed.

(* ---- D2：add 穿 mul 首槽（coef 级，U 表归纳，V 分支） ---- *)
Lemma lw0_mul_add_left : forall (U V C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (qpoly_add U V) C)
  == lw0_coef j (qpoly_mul U C) + lw0_coef j (qpoly_mul V C).
Proof.
  induction U as [|a U IH]; intros V C j.
  - cbn [qpoly_add qpoly_mul lw0_coef]. ring.
  - destruct V as [|c V].
    + rewrite lw0_add_nil_r.
      change (qpoly_mul (cons a%Q U) C)
        with (qpoly_add (qpoly_scalar a C) (cons 0%Q (qpoly_mul U C))).
      rewrite !lw0_coef_add, !lw0_coef_scalar.
      destruct j as [|j']; cbn [lw0_coef qpoly_mul lw0_coef]; ring.
    + cbn [qpoly_add].
      change (qpoly_mul (cons (a + c)%Q (qpoly_add U V)) C)
        with (qpoly_add (qpoly_scalar (a + c)%Q C)
                        (cons 0%Q (qpoly_mul (qpoly_add U V) C))).
      change (qpoly_mul (cons a%Q U) C)
        with (qpoly_add (qpoly_scalar a C) (cons 0%Q (qpoly_mul U C))).
      change (qpoly_mul (cons c%Q V) C)
        with (qpoly_add (qpoly_scalar c C) (cons 0%Q (qpoly_mul V C))).
      rewrite !lw0_coef_add, !lw0_coef_scalar.
      destruct j as [|j'].
      * cbn [lw0_coef]. ring.
      * cbn [lw0_coef]. rewrite (IH V C j'). ring.
Qed.

(* ---- mul-cons0 首槽：t·X 穿乘（无归纳，coef_add/scalar 直给） ---- *)
Lemma lw0_mul_cons0_left : forall (X C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (cons 0%Q X) C)
  == lw0_coef j (cons 0%Q (qpoly_mul X C)).
Proof.
  intros X C j.
  change (qpoly_mul (cons 0%Q X) C)
    with (qpoly_add (qpoly_scalar 0%Q C) (cons 0%Q (qpoly_mul X C))).
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct j as [|j']; cbn [lw0_coef]; ring.
Qed.

(* ---- A1：mul 结合律（coef 级；D1+D2+cons0_left 铺底） ---- *)
Lemma lw0_mul_assoc : forall (A B C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul A (qpoly_mul B C))
  == lw0_coef j (qpoly_mul (qpoly_mul A B) C).
Proof.
  induction A as [|a A IH]; intros B C j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q A) (qpoly_mul B C))
      with (qpoly_add (qpoly_scalar a (qpoly_mul B C))
                      (cons 0%Q (qpoly_mul A (qpoly_mul B C)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    change (qpoly_mul (cons a%Q A) B)
      with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
    rewrite lw0_mul_add_left.
    rewrite lw0_mul_scalar_left.
    rewrite lw0_mul_cons0_left.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH B C j'). ring.
Qed.

(* ---- 单位元左：[1] 穿乘（coef 级） ---- *)
Lemma lw0_mul_unit_left : forall (X : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (cons 1%Q nil) X) == lw0_coef j X.
Proof.
  intros X j.
  change (qpoly_mul (cons 1%Q nil) X)
    with (qpoly_add (qpoly_scalar 1%Q X) (cons 0%Q (qpoly_mul nil X))).
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct j as [|j']; cbn [lw0_coef qpoly_mul]; ring.
Qed.

(* ---- 单位元右：穿乘 [1]（coef 级，X 表归纳） ---- *)
Lemma lw0_mul_unit_right : forall (X : QPoly) (j : nat),
  lw0_coef j (qpoly_mul X (cons 1%Q nil)) == lw0_coef j X.
Proof.
  induction X as [|a X IH]; intros j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q X) (cons 1%Q nil))
      with (qpoly_add (qpoly_scalar a (cons 1%Q nil))
                      (cons 0%Q (qpoly_mul X (cons 1%Q nil)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH j'). ring.
Qed.

(* ---- A2：cons0 穿乘右槽（coef 级，A 表归纳） ---- *)
Lemma lw0_mul_cons0_right : forall (A B : QPoly) (j : nat),
  lw0_coef j (qpoly_mul A (cons 0%Q B))
  == lw0_coef j (cons 0%Q (qpoly_mul A B)).
Proof.
  induction A as [|a A IH]; intros B j.
  - cbn [qpoly_mul lw0_coef]. destruct j as [|j']; ring.
  - change (qpoly_mul (cons a%Q A) (cons 0%Q B))
      with (qpoly_add (qpoly_scalar a (cons 0%Q B))
                      (cons 0%Q (qpoly_mul A (cons 0%Q B)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH B j').
      change (qpoly_mul (cons a%Q A) B)
        with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      ring.
Qed.

(* ---- A-mul 交换律（coef 级；A/B 嵌套双归纳） ---- *)
Lemma lw0_mul_comm : forall (A B : QPoly) (j : nat),
  lw0_coef j (qpoly_mul A B) == lw0_coef j (qpoly_mul B A).
Proof.
  induction A as [|a A IHA]; intros B; induction B as [|b B IHB]; intros j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - rewrite lw0_mul_nil_r_coef. cbn [qpoly_mul lw0_coef]. ring.
  - rewrite lw0_mul_nil_r_coef. cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q A) (cons b%Q B))
      with (qpoly_add (qpoly_scalar a (cons b%Q B))
                      (cons 0%Q (qpoly_mul A (cons b%Q B)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    change (qpoly_mul (cons b%Q B) (cons a%Q A))
      with (qpoly_add (qpoly_scalar b (cons a%Q A))
                      (cons 0%Q (qpoly_mul B (cons a%Q A)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef].
      rewrite (IHA (cons b%Q B) j').
      change (qpoly_mul (cons b%Q B) A)
        with (qpoly_add (qpoly_scalar b A) (cons 0%Q (qpoly_mul B A))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      rewrite <- (IHB j').
      change (qpoly_mul (cons a%Q A) B)
        with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      destruct j' as [|j''].
      * cbn [lw0_coef]. ring.
      * cbn [lw0_coef]. rewrite (IHA B j''). ring.
Qed.

(* ---- A-tail：线性因子 [q;−1] 右乘 == qtail（h0/hS 直给） ---- *)
Lemma lw0_lintail_qtail : forall (q : Q) (P : QPoly) (j : nat),
  lw0_coef j (qpoly_mul P (cons q (cons (-1)%Q nil)))
  == lw0_coef j (lw0_qtail q P).
Proof.
  intros q P j. unfold lw0_qtail.
  destruct j as [|j'].
  - rewrite lw0_coef_mul_h0.
    rewrite lw0_coef_add, lw0_coef_scalar.
    cbn [lw0_coef]. ring.
  - rewrite lw0_coef_mul_hS.
    rewrite lw0_coef_add, lw0_coef_scalar.
    cbn [lw0_coef]. rewrite lw0_coef_opp. ring.
Qed.

(* ---- cons0 下 coef 外延性（小桥） ---- *)
Lemma lw0_cons0_congr : forall (A B : QPoly) (j : nat),
  (forall i, lw0_coef i A == lw0_coef i B) ->
  lw0_coef j (cons 0%Q A) == lw0_coef j (cons 0%Q B).
Proof.
  intros A B j H. destruct j as [|j'].
  - cbn [lw0_coef]. reflexivity.
  - cbn [lw0_coef]. apply H.
Qed.

(* ---- pi_mono 步进：t·t^i 形 == cons0 t^i（A2+unit_right 合成） ---- *)
Lemma lw0_pi_mono_cons0 : forall (i j : nat),
  lw0_coef j (lw0_pi_mono (Datatypes.S i))
  == lw0_coef j (cons 0%Q (lw0_pi_mono i)).
Proof.
  intros i j. cbn [lw0_pi_mono].
  rewrite lw0_mul_cons0_right.
  destruct j as [|j'].
  - cbn [lw0_coef]. reflexivity.
  - cbn [lw0_coef]. apply lw0_mul_unit_right.
Qed.

(* ---- pi_qminus 步进：×[q;−1] 形 == qtail（A-tail 直给） ---- *)
Lemma lw0_pi_qminus_qtail : forall (q : Q) (i j : nat),
  lw0_coef j (lw0_pi_qminus_pow q (Datatypes.S i))
  == lw0_coef j (lw0_qtail q (lw0_pi_qminus_pow q i)).
Proof.
  intros q i j. cbn [lw0_pi_qminus_pow]. apply lw0_lintail_qtail.
Qed.

(* ---- [0;1] 右乘 == cons0（t·X 移位合成件） ---- *)
Lemma lw0_mul_tshift : forall (X : QPoly) (j : nat),
  lw0_coef j (qpoly_mul X (cons 0%Q (cons 1%Q nil)))
  == lw0_coef j (cons 0%Q X).
Proof.
  intros X j. rewrite lw0_mul_cons0_right.
  destruct j as [|j'].
  - cbn [lw0_coef]. reflexivity.
  - cbn [lw0_coef]. apply lw0_mul_unit_right.
Qed.

(* ---- qtail 在 0 端的导数闭式（qtail 定义＋shift/opp 四件） ---- *)
Lemma lw0_qtail_eval_0 : forall (q : Q) (P : QPoly) (m : nat),
  qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (lw0_qtail q P)) 0
  == q * qpoly_eval (qpoly_deriv_iter (Datatypes.S m) P) 0
     - (Z.of_nat (Datatypes.S m) # 1)%Q * qpoly_eval (qpoly_deriv_iter m P) 0.
Proof.
  intros q P m. unfold lw0_qtail.
  rewrite lw0_eval_deriv_iter_add.
  rewrite lw0_eval_deriv_iter_scalar.
  rewrite lw0_shift_deriv.
  change (lw0_pred_iter (Datatypes.S m) (qpoly_opp P))
    with (qpoly_deriv_iter m (qpoly_opp P)).
  rewrite (lw0_eval_iter_opp m P 0).
  ring.
Qed.

(* ---- 常数多项式的导数消失件 ---- *)
Lemma lw0_deriv_iter_one : forall (m : nat) (x : Q),
  qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (cons 1%Q nil)) x == 0.
Proof.
  intros m x.
  assert (Hd : qpoly_deriv_iter (Datatypes.S m) (cons 1%Q nil) = cons 0%Q nil).
  { induction m as [|m IH].
    - reflexivity.
    - change (qpoly_deriv_iter (Datatypes.S (Datatypes.S m)) (cons 1%Q nil))
        with (qpoly_deriv (qpoly_deriv_iter (Datatypes.S m) (cons 1%Q nil))).
      rewrite IH. reflexivity. }
  rewrite Hd. cbn [qpoly_eval]. ring.
Qed.

(* ---- 偶阶符号件：alt(j+j) == 1 ---- *)
Lemma lw0_alt_double : forall j : nat, lw0_alt (j + j)%nat == 1%Q.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - replace (Datatypes.S j + Datatypes.S j)%nat with (Datatypes.S (j + Datatypes.S j)) by lia.
    rewrite lw0_alt_opp.
    replace (j + Datatypes.S j)%nat with (Datatypes.S (j + j)) by lia.
    rewrite lw0_alt_opp, IH. ring.
Qed.

(* ---- 零减幂件：q_pow (x-0) n == q_pow x（Qmul 位环态射承载，q_pow 参位非 Proper） ---- *)
Lemma lw0_q_pow_m0 : forall (x : Q) (n : nat), q_pow (x - 0)%Q n == q_pow x n.
Proof.
  intros x n. induction n as [|n IH].
  - reflexivity.
  - change (q_pow (x - 0)%Q (Datatypes.S n)) with ((x - 0)%Q * q_pow (x - 0)%Q n).
    change (q_pow x (Datatypes.S n)) with (x * q_pow x n).
    rewrite IH.
    assert (Hx0 : (x - 0)%Q == x) by ring.
    rewrite Hx0.
    reflexivity.
Qed.

(* ---- B 族：mono↔qminus 单因子对应（边界 j=0 的自足承载；系数形与 M 同） ---- *)
Lemma lw0_pi_mirror_bnd : forall (q : Q) (i m : nat),
  qpoly_eval (qpoly_deriv_iter m (lw0_pi_mono i)) q
  == lw0_alt m *
     qpoly_eval (qpoly_deriv_iter m (lw0_pi_qminus_pow q i)) 0.
Proof.
  intros q i. induction i as [|i IH]; intros m.
  - destruct m as [|m].
    + cbn [qpoly_deriv_iter lw0_pi_mono lw0_pi_qminus_pow qpoly_eval lw0_alt].
      ring.
    + cbn [lw0_pi_mono lw0_pi_qminus_pow].
      rewrite lw0_deriv_iter_one, lw0_deriv_iter_one.
      ring.
  - destruct m as [|m].
    + cbn [qpoly_deriv_iter lw0_alt].
      rewrite lw0_pi_mono_eval, lw0_pi_qminus_pow_eval.
      rewrite lw0_q_pow_m0.
      ring.
    + (* LHS：pi_mono 步进 cons0 化 → shift_deriv@q *)
      change (lw0_pi_mono (Datatypes.S i))
        with (qpoly_mul (lw0_pi_mono i) (cons 0%Q (cons 1%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S m) _
                 (cons 0%Q (lw0_pi_mono i)) q
                 (fun j => lw0_pi_mono_cons0 i j)).
      rewrite lw0_shift_deriv.
      change (lw0_pred_iter (Datatypes.S m) (lw0_pi_mono i))
        with (qpoly_deriv_iter m (lw0_pi_mono i)).
      (* RHS：pi_qminus 步进 qtail 化 → qtail_eval_0 *)
      change (lw0_pi_qminus_pow q (Datatypes.S i))
        with (qpoly_mul (lw0_pi_qminus_pow q i) (cons q (cons (-1)%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S m) _
                 (lw0_qtail q (lw0_pi_qminus_pow q i)) 0
                 (fun j => lw0_pi_qminus_qtail q i j)).
      rewrite lw0_qtail_eval_0.
      rewrite (IH (Datatypes.S m)), (IH m).
      rewrite lw0_alt_opp.
      ring.
Qed.

(* ---- M 主引理：pi_mono×pi_qminus 的 k 阶 q/0 端点对应（358R 草稿 §2.2 逐字） ---- *)
Lemma lw0_niven_mirror : forall (q : Q) (i j k : nat),
  qpoly_eval (qpoly_deriv_iter k (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j))) q
  == lw0_alt k *
     qpoly_eval (qpoly_deriv_iter k (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j))) 0.
Proof.
  intros q i j k. revert i j.
  induction k as [|k IH]; intros i j.
  - cbn [qpoly_deriv_iter].
    rewrite qpoly_eval_mul, qpoly_eval_mul.
    rewrite lw0_pi_mono_eval, lw0_pi_qminus_pow_eval,
            lw0_pi_qminus_pow_eval, lw0_pi_mono_eval.
    destruct j as [|j'].
    + cbn [q_pow lw0_alt].
      rewrite lw0_q_pow_m0. ring.
    + cbn [q_pow lw0_alt].
      assert (Hqq : (q - q)%Q == 0%Q) by ring.
      rewrite Hqq. ring.
  - destruct j as [|j'].
    + (* 边界 j=0：单位元桥（右）→ B 族 *)
      cbn [lw0_pi_qminus_pow lw0_pi_mono].
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_mono i) (cons 1%Q nil))
                 (lw0_pi_mono i) q
                 (fun j0 => lw0_mul_unit_right (lw0_pi_mono i) j0)).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_qminus_pow q i) (cons 1%Q nil))
                 (lw0_pi_qminus_pow q i) 0
                 (fun j0 => lw0_mul_unit_right (lw0_pi_qminus_pow q i) j0)).
      apply (lw0_pi_mirror_bnd q i (Datatypes.S k)).
    + (* 主步：q 端 qtail 剥 ／ 0 端 cons0 剥 *)
      change (lw0_pi_qminus_pow q (Datatypes.S j'))
        with (qpoly_mul (lw0_pi_qminus_pow q j') (cons q (cons (-1)%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_mono i)
                    (qpoly_mul (lw0_pi_qminus_pow q j') (cons q (cons (-1)%Q nil))))
                 (qpoly_mul (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))
                    (cons q (cons (-1)%Q nil))) q
                 (fun j0 => lw0_mul_assoc (lw0_pi_mono i) (lw0_pi_qminus_pow q j')
                              (cons q (cons (-1)%Q nil)) j0)).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))
                    (cons q (cons (-1)%Q nil)))
                 (lw0_qtail q (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))) q
                 (fun j0 => lw0_lintail_qtail q _ j0)).
      rewrite lw0_qtail_step.
      change (lw0_pred_iter (Datatypes.S k) (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j')))
        with (qpoly_deriv_iter k (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))).
      rewrite (IH i j').
      change (lw0_pi_mono (Datatypes.S j'))
        with (qpoly_mul (lw0_pi_mono j') (cons 0%Q (cons 1%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_qminus_pow q i)
                    (qpoly_mul (lw0_pi_mono j') (cons 0%Q (cons 1%Q nil))))
                 (qpoly_mul (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))
                    (cons 0%Q (cons 1%Q nil))) 0
                 (fun j0 => lw0_mul_assoc (lw0_pi_qminus_pow q i) (lw0_pi_mono j')
                              (cons 0%Q (cons 1%Q nil)) j0)).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))
                    (cons 0%Q (cons 1%Q nil)))
                 (cons 0%Q (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))) 0
                 (fun j0 => lw0_mul_tshift _ j0)).
      rewrite lw0_shift_deriv.
      change (lw0_pred_iter (Datatypes.S k) (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j')))
        with (qpoly_deriv_iter k (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))).
      rewrite lw0_alt_opp.
      ring.
Qed.

(* ---- 片一交付件：q 端点导数事实（偶阶，niven_f 全形） ---- *)
Lemma lw0_niven_deriv_mirror_even : forall (q b : Q) (n j : nat),
  qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f q b n)) q
  == qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f q b n)) 0.
Proof.
  intros q b n j. unfold lw0_niven_f.
  rewrite (lw0_eval_deriv_iter_scalar (2 * j)%nat _ _ q).
  rewrite (lw0_eval_deriv_iter_scalar (2 * j)%nat _ _ 0).
  rewrite (lw0_niven_mirror q n n (2 * j)%nat).
  rewrite (lw0_eval_iter_congr (2 * j)%nat
             (qpoly_mul (lw0_pi_qminus_pow q n) (lw0_pi_mono n))
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) 0
             (fun i => lw0_mul_comm (lw0_pi_qminus_pow q n) (lw0_pi_mono n) i)).
  replace (2 * j)%nat with (j + j)%nat by lia.
  rewrite lw0_alt_double.
  ring.
Qed.
Print Assumptions lw0_add_nil_r.
Print Assumptions lw0_mul_nil_r_coef.
Print Assumptions lw0_mul_scalar_left.
Print Assumptions lw0_mul_add_left.
Print Assumptions lw0_mul_cons0_left.
Print Assumptions lw0_mul_assoc.
Print Assumptions lw0_mul_unit_left.
Print Assumptions lw0_mul_unit_right.
Print Assumptions lw0_mul_cons0_right.
Print Assumptions lw0_mul_comm.
Print Assumptions lw0_lintail_qtail.
Print Assumptions lw0_cons0_congr.
Print Assumptions lw0_pi_mono_cons0.
Print Assumptions lw0_pi_qminus_qtail.
Print Assumptions lw0_mul_tshift.
Print Assumptions lw0_qtail_eval_0.
Print Assumptions lw0_deriv_iter_one.
Print Assumptions lw0_alt_double.
Print Assumptions lw0_q_pow_m0.
Print Assumptions lw0_pi_mirror_bnd.
Print Assumptions lw0_niven_mirror.
Print Assumptions lw0_niven_deriv_mirror_even.
(* ================= 365 片二：①HK K 闭式装配（lw0_K_closure_F0Fq） ================= *)
(* ================================================================== *)
(* 365 片二：K 闭式装配（358R 两片拆分·片二；使用 361R 片一 .vo 资产）      *)
(* 素材源：358R 冻结草稿 §2.5 装配件 A10-A12＋§三载荷账；语句面＝355R 回执   *)
(* §7.1.3 ①HK 槽逐字（文件复制，PROOFVAR-UNDESTRUCT 工艺）。               *)
(* 证体：F 展开＝Σ alt j·f^(2j)（A10）＋qsum 有界逐项外延（A11）＋逐项对装   *)
(* K_leg（conn_lo/conn_hi 桥＋mirror_even＋zero_0 使用；b 槽规范配对载荷位   *)
(* ——错配反例 20≠24 已手算确证，装配以 (Zpos (Qden q) # 1) 槽全程对齐）。   *)
(* 全块 born-in-place，只使用既有在件，零新公理。                          *)
(* ================================================================== *)

(* ---- cons 头系数同化：头 Q 值相等＋尾 coefwise ⇒ 整表 coefwise ---- *)
Lemma lw0_cons_coef_congr : forall (a a' : Q) (A B : QPoly),
  a == a' -> (forall i : nat, lw0_coef i A == lw0_coef i B) ->
  forall j : nat, lw0_coef j (cons a A) == lw0_coef j (cons a' B).
Proof.
  intros a a' A B Ha H j.
  destruct j as [|j'].
  - cbn [lw0_coef]. exact Ha.
  - cbn [lw0_coef]. apply H.
Qed.

(* ---- mul 第一槽 coefwise 同化（A 表归纳；D1/D2 展开式直给） ---- *)
Lemma lw0_coef_mul_congr : forall (A U V : QPoly),
  (forall i : nat, lw0_coef i U == lw0_coef i V) ->
  forall j : nat, lw0_coef j (qpoly_mul A U) == lw0_coef j (qpoly_mul A V).
Proof.
  intros A. induction A as [|c A IH]; intros U V H j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons c%Q A) U)
      with (qpoly_add (qpoly_scalar c U) (cons 0%Q (qpoly_mul A U))).
    change (qpoly_mul (cons c%Q A) V)
      with (qpoly_add (qpoly_scalar c V) (cons 0%Q (qpoly_mul A V))).
    rewrite !lw0_coef_add, !lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. rewrite (H 0%nat). apply Qeq_refl.
    + cbn [lw0_coef]. rewrite (H (Datatypes.S j')). rewrite (IH U V H j').
      apply Qeq_refl.
Qed.

(* ---- qminus 族桥：pi/mul 形与 z 形 fixpoint 结构同构，coefwise 同一 ---- *)
Lemma lw0_pi_qminus_z_bridge : forall (q : Q) (i j : nat),
  lw0_coef j (lw0_pi_qminus_pow q i) == lw0_coef j (lw0_qminus_pow q i).
Proof.
  intros q i. induction i as [|i IH]; intro j.
  - reflexivity.
  - cbn [lw0_pi_qminus_pow lw0_qminus_pow].
    rewrite (lw0_mul_comm (lw0_pi_qminus_pow q i) (cons q (cons (-1)%Q nil)) j).
    rewrite (lw0_mul_comm (lw0_qminus_pow q i) (cons q (cons (-1)%Q nil)) j).
    apply lw0_coef_mul_congr. exact IH.
Qed.

(* ---- mono 族桥：pi/t· 形与 z/cons 形（361R pi_mono_cons0＋cons0_congr 铺底） ---- *)
Lemma lw0_pi_mono_z_bridge : forall (i j : nat),
  lw0_coef j (lw0_pi_mono i) == lw0_coef j (lw0_mono i).
Proof.
  intros i. induction i as [|i IH]; intro j.
  - reflexivity.
  - rewrite lw0_pi_mono_cons0.
    change (lw0_mono (Datatypes.S i)) with (cons 0%Q (lw0_mono i)).
    exact (lw0_cons0_congr (lw0_pi_mono i) (lw0_mono i) j IH).
Qed.

(* ---- q_pow (x#1) 闭形：与 Zpower_nat 互化（Qmake_mul 定义性闭合） ---- *)
Lemma lw0_q_pow_one_base : forall (x : Z) (n : nat),
  q_pow (x # 1)%Q n == (Zpower_nat x n # 1)%Q.
Proof.
  intros x. induction n as [|n IH].
  - reflexivity.
  - change (q_pow (x # 1)%Q (Datatypes.S n))
      with ((x # 1)%Q * q_pow (x # 1)%Q n).
    rewrite IH.
    change (Zpower_nat x (Datatypes.S n)) with (x * Zpower_nat x n)%Z.
    apply lw0_Qmake_mul.
Qed.

(* ---- niven 标量桥：b^n/n! 的 Z 基闭形（除法面经 q_int_inv 消元；     ---- *)
(* ---- Qinv 对 Z.of_nat 元素不化约＝首发红点①，改 Hmul+q_int_inv 两段式） ---- *)
Lemma lw0_niven_scalar_bridge : forall (x : Z) (n : nat),
  q_pow (x # 1)%Q n / q_fact n == (Zpower_nat x n # Pos.of_nat (fact n))%Q.
Proof.
  intros x n.
  assert (Hfn : (1 <= fact n)%nat) by (pose proof (fact_neq_0 n); lia).
  assert (Hz : (0 < Z.of_nat (fact n))%Z).
  { destruct (fact n) as [|k] eqn:Ek; [ exfalso; lia | lia ]. }
  assert (Hmul : q_pow (x # 1)%Q n
                 == (Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q).
  { rewrite lw0_q_pow_one_base. unfold Qeq, Qmult. cbn [Qnum Qden].
    rewrite Pos.mul_1_r, (lw0_posnat_zeq (fact n) Hfn). ring. }
  rewrite lw0_qfact_Z, Hmul.
  change ((Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q /
          (Z.of_nat (fact n) # 1)%Q)
    with ((Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q *
          / (Z.of_nat (fact n) # 1)%Q).
  assert (Hre : (Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q *
                / (Z.of_nat (fact n) # 1)%Q
                == (Zpower_nat x n # Pos.of_nat (fact n))%Q
                   * ((Z.of_nat (fact n) # 1)%Q * / (Z.of_nat (fact n) # 1)%Q)).
  { apply Qeq_sym. apply Qmult_assoc. }
  rewrite Hre.
  rewrite (lw0_q_int_inv (Z.of_nat (fact n)) Hz).
  ring.
Qed.

(* ---- niven 族桥（A8）：pi 侧 bQ 载荷形 == z 侧 Z 基形（coefwise；b 槽规范配对位） ---- *)
Lemma lw0_niven_pi_z_bridge : forall (a : Z) (b : positive) (n j : nat),
  lw0_coef j (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)
  == lw0_coef j (lw0_niven_f_z (a # b)%Q (Zpos b) n).
Proof.
  intros a b n j. unfold lw0_niven_f, lw0_niven_f_z.
  rewrite !lw0_coef_scalar.
  rewrite (lw0_niven_scalar_bridge (Zpos b) n).
  assert (Hm : lw0_coef j (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow (a # b)%Q n))
               == lw0_coef j (qpoly_mul (lw0_mono n) (lw0_qminus_pow (a # b)%Q n))).
  { transitivity (lw0_coef j (qpoly_mul (lw0_pi_mono n) (lw0_qminus_pow (a # b)%Q n))).
    - apply lw0_coef_mul_congr. intro i. apply lw0_pi_qminus_z_bridge.
    - transitivity (lw0_coef j (qpoly_mul (lw0_qminus_pow (a # b)%Q n) (lw0_pi_mono n))).
      + apply lw0_mul_comm.
      + transitivity (lw0_coef j (qpoly_mul (lw0_qminus_pow (a # b)%Q n) (lw0_mono n))).
        * apply lw0_coef_mul_congr. intro i. apply lw0_pi_mono_z_bridge.
        * apply lw0_mul_comm. }
  rewrite Hm. apply Qeq_refl.
Qed.

(* ---- pi 侧端点事实·零支（ab 形；eval_iter_congr 过桥使用 z 侧认证件） ---- *)
Lemma lw0_niven_deriv_zero_0_ab : forall (a : Z) (b : positive) (n k : nat),
  (k < n)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0 == 0.
Proof.
  intros a b n k Hk.
  transitivity (qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0).
  - apply (lw0_eval_iter_congr k _ _ 0 (fun j => lw0_niven_pi_z_bridge a b n j)).
  - apply lw0_niven_deriv_zero_0. exact Hk.
Qed.

(* ---- pi 侧端点事实·lo 闭支（ab 形；conn_lo 直供） ---- *)
Lemma lw0_niven_deriv_conn_lo_ab : forall (a : Z) (b : positive) (n k : nat),
  (n <= k)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0
  == lw0_z_lo a (Zpos b) n k.
Proof.
  intros a b n k Hk.
  transitivity (qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0).
  - apply (lw0_eval_iter_congr k _ _ 0 (fun j => lw0_niven_pi_z_bridge a b n j)).
  - apply lw0_conn_lo. exact Hk.
Qed.

(* ---- pi 侧端点事实·hi 闭支（ab 形；conn_hi 直供） ---- *)
Lemma lw0_niven_deriv_conn_hi_ab : forall (a : Z) (b : positive) (n j : nat),
  (n <= 2 * j)%nat -> (j <= n)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0
  == lw0_z_hi a (Zpos b) n (2 * (n - j))%nat.
Proof.
  intros a b n j H1 H2.
  transitivity (qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0).
  - apply (lw0_eval_iter_congr (2 * j)%nat _ _ 0 (fun i => lw0_niven_pi_z_bridge a b n i)).
  - apply lw0_conn_hi; assumption.
Qed.

(* ---- A10：F 展开＝Σ alt j·f^(2j)（lw0_qsum 定义步；qpoly_eval_add/scalar 直给） ---- *)
Lemma lw0_F_eval_qsum : forall (f : qpoly) (J : nat) (x : Q),
  qpoly_eval (lw0_F f J) x
  == lw0_qsum (fun j : nat => lw0_alt j * qpoly_eval (qpoly_deriv_iter (2 * j)%nat f) x) J.
Proof.
  intros f J x. induction J as [|J' IH].
  - unfold lw0_F, lw0_F_aux. cbn [lw0_qsum].
    change (qpoly_deriv_iter (2 * 0)%nat f) with f.
    change (lw0_alt 0%nat) with 1%Q.
    rewrite qpoly_eval_scalar. ring.
  - unfold lw0_F. cbn [lw0_F_aux].
    change (lw0_F_aux f 1%Q J') with (lw0_F f J').
    rewrite qpoly_eval_add, qpoly_eval_scalar.
    rewrite IH. cbn [lw0_qsum]. ring.
Qed.

(* ---- A11：qsum 有界逐项外延（点态相等 j ≤ m ⇒ 和相等；两函数和拆分同件承载） ---- *)
Lemma lw0_qsum_ext2 : forall (g h1 h2 : nat -> Q) (m : nat),
  (forall j : nat, (j <= m)%nat -> g j == h1 j + h2 j) ->
  lw0_qsum g m == lw0_qsum h1 m + lw0_qsum h2 m.
Proof.
  intros g h1 h2 m. induction m as [|m IH]; intro H.
  - cbn [lw0_qsum]. apply (H 0%nat (Nat.le_0_l 0%nat)).
  - cbn [lw0_qsum].
    rewrite (IH (fun j Hj => H j (Nat.le_le_succ_r _ _ Hj))).
    rewrite (H (Datatypes.S m) (Nat.le_refl (Datatypes.S m))).
    ring.
Qed.

(* ---- ①HK 主件：K 闭式（语句面＝355R §7.1.3 ①HK 槽逐字；早 destruct 判定 (a,b) 形） ---- *)
Lemma lw0_K_closure_F0Fq : forall (q : Q) (n : nat),
  lw0_K (Qnum q) (Zpos (Qden q)) n
  == qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
     + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q.
Proof.
  intros q n. destruct q as [a b]. cbn [Qnum Qden].
  rewrite (lw0_F_eval_qsum (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n 0).
  rewrite (lw0_F_eval_qsum (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n ((a # b)%Q)).
  apply (lw0_qsum_ext2 (lw0_K_leg a (Zpos b) n)).
  intros j Hj. cbn beta. unfold lw0_K_leg.
  destruct (Nat.leb n (2 * j)) eqn:Hle.
  - apply Nat.leb_le in Hle.
    change (if true
            then lw0_z_lo a (Zpos b) n (2 * j) + lw0_z_hi a (Zpos b) n (2 * (n - j))
            else (0 # 1)%Q)
      with (lw0_z_lo a (Zpos b) n (2 * j) + lw0_z_hi a (Zpos b) n (2 * (n - j)))%Q.
    rewrite (lw0_alt_zsign j).
    rewrite (lw0_niven_deriv_conn_lo_ab a b n (2 * j)%nat Hle).
    rewrite (lw0_niven_deriv_mirror_even (a # b)%Q (Zpos b # 1)%Q n j).
    rewrite (lw0_niven_deriv_conn_hi_ab a b n j Hle Hj).
    ring.
  - apply Nat.leb_gt in Hle.
    change (if false
            then lw0_z_lo a (Zpos b) n (2 * j) + lw0_z_hi a (Zpos b) n (2 * (n - j))
            else (0 # 1)%Q)
      with (0 # 1)%Q.
    rewrite (lw0_niven_deriv_mirror_even (a # b)%Q (Zpos b # 1)%Q n j).
    rewrite (lw0_niven_deriv_zero_0_ab a b n (2 * j)%nat Hle).
    ring.
Qed.

(* ---- 随块 PA 锚（365 片二；逐发 Closed 判读） ---- *)
Print Assumptions lw0_cons_coef_congr.
Print Assumptions lw0_coef_mul_congr.
Print Assumptions lw0_pi_qminus_z_bridge.
Print Assumptions lw0_pi_mono_z_bridge.
Print Assumptions lw0_q_pow_one_base.
Print Assumptions lw0_niven_scalar_bridge.
Print Assumptions lw0_niven_pi_z_bridge.
Print Assumptions lw0_niven_deriv_zero_0_ab.
Print Assumptions lw0_niven_deriv_conn_lo_ab.
Print Assumptions lw0_niven_deriv_conn_hi_ab.
Print Assumptions lw0_F_eval_qsum.
Print Assumptions lw0_qsum_ext2.
Print Assumptions lw0_K_closure_F0Fq.

(* ---------- 段 2b-ε 终形前置机件（GAPASUME 再交棒·绕开 σ″ 路线登记） ----------
   [谱系] 355R §7.1.3 缺口目标形冻结 → 365 片二 ①HK 闭合（lw0_K_closure_F0Fq 在件）→ 本块装配。
   [形] 终形名 lw0_pitB_pair_rtail_vanish 让出不占条款维持——360 前置闸门② regex 闸
   不被前提承载形僭越（fail-loud：真形缺位须机器可见计 0）；本件＝①HK 槽在件直供消去
   （lw0_K_closure_F0Fq q n 直供 vanish_gap 首前提，类型面全等经 Check 检验）＋
   ②Hpair 槽＝355R §7.1.3 目标形逐字显式承载（本块语句面与 vanish_gap 第二前提字节
   同源，生成器单源提取禁重打，回执规范化对表全等）＋结论面＝341 e1aada59 接口面 3 逐字。
   [绕开登记] ②Hpair 全证＝E_m 等价改写〔ibp_dbl＋F_plus_deriv2_poly＋sin_deriv2〕＋
   pwi 移位权界〔未采纳〕＋conv_pair_vanish 例示，百行级工程量过大——本块
   零消费 σ″ 六件（363 落装），证体一行（vanish_gap 直供），零新分析面。
   [终形工艺] ②Hpair 闭合落 lw0_pitB_pair_conv（②Hpair 结论面闭形）后，终形三行
   turnkey（366 回执 §交接段全稿）落装——终形落装后 360 regex 闸计 1 为真满足，
   v4 块 2c-3 L213 使用拼写零改。 *)

Lemma lw0_pitB_pair_rtail_vanish_hpair : forall (q : Q) (n : nat),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
       QltT (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp m) q
                   - qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
                   - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                       * qpoly_eval (lw0_sin_qp m) q
                   + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                       * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n Hpair eps Heps.
  exact (lw0_pitB_pair_rtail_vanish_gap q n (lw0_K_closure_F0Fq q n) Hpair eps Heps).
Qed.

(* ---------- 随块 PA 锚（①HK 消去＋②Hpair 承载面 Closed 判读） ---------- *)
Print Assumptions lw0_pitB_pair_rtail_vanish_hpair.
(* ================= 363 σ″ 三件＋poly 级 F_plus_deriv2 变体 ================= *)
(* ================================================================== *)
(* 363：355R GAPASUME 交棒三类供件之二——                                 *)
(*   ① σ″ 多项式级恒等三件（语句面冻结于 _tlw341 diechain 草稿 L135-144；    *)
(*     三名 lw0_sin_qp_deriv_poly／lw0_cos_qp_deriv_poly／lw0_sin_qp_deriv2  *)
(*     逐字保留）；② poly 级 F_plus_deriv2 变体 lw0_F_plus_deriv2_poly。     *)
(* 〔对表微调令〕冻结语句面的 `==` 在 qpoly＝list Q 上无类型承载（stdlib      *)
(*   Qeq : Q -> Q -> Prop；主件 10,808 行零 poly 级 == 在件实测；L3460 区库   *)
(*   注记明载 list 层导数等式在「低次在首＋允许尾零」表示下非可靠不变量）——    *)
(*   等词载体换本块 lw0_qpoly_eq（lw0_coef 系数级逐位相等），三件名与操作数    *)
(*   结构逐字保留；使用侧经 lw0_eval_len_indep（在件）零损降岸。             *)
(* 〔工艺〕NOEVALIFT L1860 全程：零 eval 桥（lw0_sin_qp_deriv_eval／         *)
(*   lw0_cos_qp_deriv_eval 零消费），唯一路＝aux 表结构归纳直证（工艺对应＝    *)
(*   lw0_sin_aux_deriv_eval／lw0_cos_aux_deriv_eval_S 的 poly 级重走）；      *)
(*   红点位＝qpoly_deriv 的 qpoly_add 结构步（lw0_coef_deriv 系数桥消解）。   *)
(* 〔数构〕sin 表归纳 acc 泛化主引理可组合：Wp 变换 ((2j+2+r)·acc_r) 与表     *)
(*   递归前缀对 (0,σ_j) 精确吻合（(2j+3)·σ_j＝ε_j）；cos 侧 master_C 形      *)
(*   （尾项起点 2j+2）同理吻合；F 块＝无-die 闭式纯代数归纳＋die→deriv_iter   *)
(*   系数零化（lw0_die_coef_zero×lw0_coef_deriv_iter_zero）。                *)
(* 全块 born-in-place，只使用既有在件，零新公理。                           *)
(* ================================================================== *)

(* ---- D1 poly 等词载体：系数级逐位相等（对表微调令载体） ---- *)
Definition lw0_qpoly_eq (p q : qpoly) : Prop :=
  forall j : nat, lw0_coef j p == lw0_coef j q.

(* ---- D2 尾零移位：t^m·p 的系数表（低次在首） ---- *)
Fixpoint qpoly_shift (n : nat) (p : qpoly) : qpoly :=
  match n with
  | Datatypes.O => p
  | Datatypes.S m => cons 0%Q (qpoly_shift m p)
  end.

(* ---- Qmake 桥接引理三枚（Z 后继／加法／相等传输） ---- *)
Lemma lw0_qmake_Z_succ : forall n : nat,
  (Z.of_nat (Datatypes.S n) # 1)%Q == ((Z.of_nat n # 1) + 1)%Q.
Proof.
  intro n.
  assert (Hn : Z.of_nat (Datatypes.S n) = (Z.of_nat n + 1)%Z) by lia.
  unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn; lia.
Qed.

Lemma lw0_qmake_add : forall n m : nat,
  (Z.of_nat (n + m) # 1)%Q == ((Z.of_nat n # 1) + (Z.of_nat m # 1))%Q.
Proof.
  intros n m.
  assert (Hn : Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%Z) by lia.
  unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn; lia.
Qed.

Lemma lw0_qmake_eq : forall z1 z2 : Z, z1 = z2 -> (z1 # 1)%Q == (z2 # 1)%Q.
Proof.
  intros z1 z2 H. unfold Qeq; cbn [Qnum Qden]; rewrite H; lia.
Qed.

Lemma lw0_qmake_2 : (Z.of_nat (Datatypes.S (Datatypes.S Datatypes.O)) # 1)%Q
                    == (1 + 1)%Q.
Proof. unfold Qeq; cbn [Qnum Qden Qplus Qmult]; lia. Qed.

Lemma lw0_qmake_1 : (Z.of_nat (Datatypes.S Datatypes.O) # 1)%Q == 1%Q.
Proof. unfold Qeq; cbn [Qnum Qden]; lia. Qed.

(* ---- 等词三件（自反／对称／传递） ---- *)
Lemma lw0_qpoly_eq_refl : forall p : qpoly, lw0_qpoly_eq p p.
Proof. intros p j. apply Qeq_refl. Qed.

Lemma lw0_qpoly_eq_sym : forall p q : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eq q p.
Proof. intros p q H j. apply Qeq_sym. apply H. Qed.

Lemma lw0_qpoly_eq_trans : forall p q r : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eq q r -> lw0_qpoly_eq p r.
Proof. intros p q r H1 H2 j. apply Qeq_trans with (lw0_coef j q).
  apply H1. apply H2. Qed.

(* ---- cons 同余／加法同余／加法结合 ---- *)
Lemma lw0_cons_congr : forall (a b : Q) (p q : qpoly),
  a == b -> lw0_qpoly_eq p q -> lw0_qpoly_eq (cons a p) (cons b q).
Proof.
  intros a b p q Hab Hp j. destruct j as [|j'].
  - simpl. exact Hab.
  - simpl. exact (Hp j').
Qed.

Lemma lw0_qpoly_eq_add : forall p1 q1 p2 q2 : qpoly,
  lw0_qpoly_eq p1 q1 -> lw0_qpoly_eq p2 q2 ->
  lw0_qpoly_eq (qpoly_add p1 p2) (qpoly_add q1 q2).
Proof.
  intros p1 q1 p2 q2 H1 H2 j.
  rewrite lw0_coef_add, lw0_coef_add.
  apply Qeq_trans with (lw0_coef j q1 + lw0_coef j p2)%Q.
  - rewrite (H1 j). ring.
  - rewrite (H2 j). ring.
Qed.

Lemma lw0_qpoly_add_assoc : forall p q r : qpoly,
  lw0_qpoly_eq (qpoly_add (qpoly_add p q) r) (qpoly_add p (qpoly_add q r)).
Proof.
  intros p q r k. repeat rewrite lw0_coef_add. ring.
Qed.

(* ---- deriv 同余（红点位消解：lw0_coef_deriv 系数桥） ---- *)
Lemma lw0_qpoly_eq_deriv : forall p q : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eq (qpoly_deriv p) (qpoly_deriv q).
Proof.
  intros p q H j.
  rewrite lw0_coef_deriv, (H (Datatypes.S j)), lw0_coef_deriv. reflexivity.
Qed.

(* ---- 移位系数族 ---- *)
Lemma lw0_coef_shift : forall (n r : nat) (p : qpoly),
  lw0_coef (n + r)%nat (qpoly_shift n p) == lw0_coef r p.
Proof.
  induction n as [|n IH]; intros r p.
  - simpl. reflexivity.
  - replace (Datatypes.S n + r)%nat with (Datatypes.S (n + r))%nat by lia.
    simpl. exact (IH r p).
Qed.

Lemma lw0_coef_shift_1 : forall (r : nat) (p : qpoly),
  lw0_coef (Datatypes.S r) (qpoly_shift 1 p) == lw0_coef r p.
Proof. intros r p. exact (lw0_coef_shift 1 r p). Qed.

Lemma lw0_coef_shift_2 : forall (r : nat) (p : qpoly),
  lw0_coef (Datatypes.S (Datatypes.S r)) (qpoly_shift 2 p) == lw0_coef r p.
Proof. intros r p. exact (lw0_coef_shift 2 r p). Qed.

Lemma lw0_coef_shift_lt : forall (m k : nat) (p : qpoly),
  (k < m)%nat -> lw0_coef k (qpoly_shift m p) == 0%Q.
Proof.
  induction m as [|m IH]; intros k p Hk.
  - exfalso. lia.
  - destruct k as [|k'].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

(* 移位一格的均匀系数形（deriv 后 k·w_k 闭式；k=0 支 0·w_0＝0 零吸收） *)
Lemma lw0_shift1_deriv_coef : forall (k : nat) (w : qpoly),
  lw0_coef k (qpoly_shift 1 (qpoly_deriv w)) == (Z.of_nat k # 1)%Q * lw0_coef k w.
Proof.
  intros k w. destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 1 0 (qpoly_deriv w)) by lia.
    change (Z.of_nat Datatypes.O # 1)%Q with 0%Q.
    symmetry. apply Qmult_0_l.
  - rewrite lw0_coef_shift_1, lw0_coef_deriv. reflexivity.
Qed.

(* ---- 移位五件：分配／复合／推入／零表／同余 ---- *)
Lemma lw0_shift_add : forall (m : nat) (p q : qpoly),
  lw0_qpoly_eq (qpoly_shift m (qpoly_add p q))
               (qpoly_add (qpoly_shift m p) (qpoly_shift m q)).
Proof.
  induction m as [|m IH]; intros p q k.
  - reflexivity.
  - destruct k as [|k'].
    + cbn [lw0_coef qpoly_shift qpoly_add]. ring.
    + cbn [lw0_coef qpoly_shift qpoly_add]. exact (IH p q k').
Qed.

Lemma lw0_shift_shift : forall (m n : nat) (p : qpoly),
  lw0_qpoly_eq (qpoly_shift (m + n) p) (qpoly_shift m (qpoly_shift n p)).
Proof.
  induction m as [|m IH]; intros n p k.
  - reflexivity.
  - replace (Datatypes.S m + n)%nat with (Datatypes.S (m + n))%nat by lia.
    destruct k as [|k'].
    + reflexivity.
    + cbn [lw0_coef qpoly_shift]. exact (IH n p k').
Qed.

Lemma lw0_shift_push : forall (m : nat) (y : Q) (w : qpoly),
  lw0_qpoly_eq (qpoly_shift (Datatypes.S m) (cons y w))
               (qpoly_add (qpoly_shift (Datatypes.S m) (cons y nil))
                          (qpoly_shift (Datatypes.S (Datatypes.S m)) w)).
Proof.
  induction m as [|m IH]; intros y w.
  - cbn [qpoly_shift qpoly_add].
    apply lw0_cons_congr; [ring |].
    apply lw0_cons_congr; [ring | apply lw0_qpoly_eq_refl].
  - cbn [qpoly_shift qpoly_add].
    apply lw0_cons_congr; [ring | apply IH].
Qed.

Lemma lw0_shift_nil : forall m : nat, lw0_qpoly_eq (qpoly_shift m nil) nil.
Proof.
  induction m as [|m IH].
  - intro k. reflexivity.
  - intro k. destruct k as [|k'].
    + reflexivity.
    + simpl. exact (IH k').
Qed.

Lemma lw0_shift_congr : forall (m : nat) (p q : qpoly),
  lw0_qpoly_eq p q -> lw0_qpoly_eq (qpoly_shift m p) (qpoly_shift m q).
Proof.
  intros m p q H k.
  destruct (Nat.le_gt_cases m k) as [Hle | Hgt].
  - assert (Hr : k = (m + (k - m))%nat) by lia.
    rewrite Hr.
    rewrite (lw0_coef_shift m (k - m) p).
    rewrite (lw0_coef_shift m (k - m) q).
    apply H.
  - rewrite (lw0_coef_shift_lt m k p Hgt).
    rewrite (lw0_coef_shift_lt m k q Hgt). ring.
Qed.

(* ---- 二元 cons vs shift2 拆装（头对钉死形） ---- *)
Lemma lw0_cons2_shift2 : forall (a b : Q) (w : qpoly),
  lw0_qpoly_eq (cons a (cons b w))
               (qpoly_add (cons a (cons b nil)) (qpoly_shift 2 w)).
Proof.
  intros a b w k. rewrite lw0_coef_add. destruct k as [|k'].
  - cbn [lw0_coef]. rewrite (lw0_coef_shift_lt 2 0 w) by lia. ring.
  - destruct k' as [|k''].
    + cbn [lw0_coef]. rewrite (lw0_coef_shift_lt 2 1 w) by lia. ring.
    + rewrite lw0_coef_shift_2.
      cbn [lw0_coef].
      ring.
Qed.

(* ---- 标量对偶件（头对拼装） ---- *)
Lemma lw0_scal_pair_shift : forall (c x y : Q) (w : qpoly),
  lw0_qpoly_eq (qpoly_scalar c (cons x (cons y w)))
               (qpoly_add (qpoly_scalar c (cons x (cons y nil)))
                          (qpoly_shift 2 (qpoly_scalar c w))).
Proof.
  intros c x y w k. cbn [qpoly_scalar].
  rewrite lw0_coef_add. destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 2 0 (qpoly_scalar c w)) by lia.
    cbn [lw0_coef].
    ring.
  - destruct k' as [|k''].
    + rewrite (lw0_coef_shift_lt 2 1 (qpoly_scalar c w)) by lia.
      cbn [lw0_coef].
      ring.
    + rewrite lw0_coef_shift_2.
      cbn [lw0_coef].
      ring.
Qed.

(* ---- sin 表标量拼装（master_C 步进供件） ---- *)
Lemma lw0_sin_aux_scal_append : forall (j : nat) (c : Q) (w : qpoly),
  lw0_qpoly_eq (qpoly_scalar c (lw0_sin_aux j w))
               (qpoly_add (qpoly_scalar c (lw0_sin_aux j nil))
                          (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                       (qpoly_scalar c w))).
Proof.
  induction j as [|j IH]; intros c w k.
  - cbn [lw0_sin_aux qpoly_scalar].
    rewrite lw0_coef_add. destruct k as [|k'].
    + rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (0 + 0))) Datatypes.O (qpoly_scalar c w)) by lia.
      cbn [lw0_coef].
      ring.
    + destruct k' as [|k''].
      * rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (0 + 0))) (Datatypes.S Datatypes.O) (qpoly_scalar c w)) by lia.
        cbn [lw0_coef].
        ring.
      * rewrite lw0_coef_shift_2.
        cbn [lw0_coef].
        ring.
  - cbn [lw0_sin_aux].
    set (cig := (q_pow (-1) (Datatypes.S j)
                 / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q).
    rewrite (IH c (cons 0%Q (cons cig w)) k).
    rewrite (lw0_coef_add k (qpoly_scalar c (lw0_sin_aux j nil))
               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                            (qpoly_scalar c (cons 0%Q (cons cig w))))).
    rewrite (lw0_coef_add k (qpoly_scalar c (lw0_sin_aux j (cons 0%Q (cons cig nil))))
               (qpoly_shift (Datatypes.S (Datatypes.S (Datatypes.S j + Datatypes.S j)))
                            (qpoly_scalar c w))).
    rewrite (IH c (cons 0%Q (cons cig nil)) k).
    rewrite (lw0_coef_add k (qpoly_scalar c (lw0_sin_aux j nil))
               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                            (qpoly_scalar c (cons 0%Q (cons cig nil))))).
    (* S1 项的 qpoly 层恒等链（congruence 组合器逐项构造，零 forall 形 rewrite——
       屏障定律：lw0_coef/qpoly_shift 下零 morphism，forall 形引理仅根体可匹配，判例在案） *)
    pose proof (lw0_shift_congr (Datatypes.S (Datatypes.S (j + j)))
                  (qpoly_scalar c (cons 0%Q (cons cig w)))
                  (qpoly_add (qpoly_scalar c (cons 0%Q (cons cig nil)))
                             (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                          (qpoly_scalar c w)))
                  (lw0_scal_pair_shift c 0%Q cig w)) as Hid1.
    pose proof (lw0_shift_add (Datatypes.S (Datatypes.S (j + j)))
                  (qpoly_scalar c (cons 0%Q (cons cig nil)))
                  (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                               (qpoly_scalar c w))) as Hid2.
    pose proof (lw0_shift_shift (Datatypes.S (Datatypes.S (j + j)))
                  (Datatypes.S (Datatypes.S Datatypes.O)) (qpoly_scalar c w)) as Hid3.
    pose proof (lw0_qpoly_eq_sym _ _ Hid3) as Hid3s.
    pose proof (lw0_qpoly_eq_trans _ _ _ Hid1 Hid2) as Hid12.
    pose proof (lw0_qpoly_eq_add _ _ _ _
                  (lw0_qpoly_eq_refl (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                      (qpoly_scalar c (cons 0%Q (cons cig nil)))))
                  Hid3s) as HidF.
    pose proof (lw0_qpoly_eq_trans _ _ _ Hid12 HidF) as Hid.
    specialize (Hid k).
    rewrite Hid.
    rewrite (lw0_coef_add k (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                            (qpoly_scalar c (cons 0%Q (cons cig nil))))
               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)) + Datatypes.S (Datatypes.S Datatypes.O))
                            (qpoly_scalar c w))).
    replace (Datatypes.S (Datatypes.S (j + j)) + 2)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S j + Datatypes.S j)))%nat
      by lia.
    ring.
Qed.

(* ---- aux 表同余双件（master 步进供件） ---- *)
Lemma lw0_cos_aux_congr : forall (j : nat) (w1 w2 : qpoly),
  lw0_qpoly_eq w1 w2 -> lw0_qpoly_eq (lw0_cos_aux j w1) (lw0_cos_aux j w2).
Proof.
  induction j as [|j IH]; intros w1 w2 H k.
  - destruct k as [|k'].
    + reflexivity.
    + simpl. exact (H k').
  - cbn [lw0_cos_aux].
    apply IH. intro k0. destruct k0 as [|k0].
    + reflexivity.
    + destruct k0 as [|k0'].
      * reflexivity.
      * simpl. exact (H k0').
Qed.

Lemma lw0_sin_aux_congr : forall (j : nat) (w1 w2 : qpoly),
  lw0_qpoly_eq w1 w2 -> lw0_qpoly_eq (lw0_sin_aux j w1) (lw0_sin_aux j w2).
Proof.
  induction j as [|j IH]; intros w1 w2 H k.
  - destruct k as [|k'].
    + reflexivity.
    + destruct k' as [|k''].
      * reflexivity.
      * simpl. exact (H k'').
  - cbn [lw0_sin_aux].
    apply IH. intro k0. destruct k0 as [|k0].
    + reflexivity.
    + destruct k0 as [|k0'].
      * reflexivity.
      * simpl. exact (H k0').
Qed.

(* ---- D3/D4 变换器：尾项承载 ((2j+2+r)·acc_r)／((2j+3+r)·acc_r) ---- *)
Definition lw0_Wp (j : nat) (acc : qpoly) : qpoly :=
  qpoly_add (qpoly_scalar (Z.of_nat (Datatypes.S (Datatypes.S (j + j))) # 1)%Q acc)
            (qpoly_shift 1 (qpoly_deriv acc)).

Definition lw0_Xc (j : nat) (acc : qpoly) : qpoly :=
  qpoly_add (qpoly_scalar
               (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q
               acc)
            (qpoly_shift 1 (qpoly_deriv acc)).

Lemma lw0_Wp_nil : forall j : nat, lw0_qpoly_eq (lw0_Wp j nil) nil.
Proof.
  intros j k. unfold lw0_Wp.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k; simpl; ring.
Qed.

Lemma lw0_Xc_nil : forall j : nat, lw0_qpoly_eq (lw0_Xc j nil) nil.
Proof.
  intros j k. unfold lw0_Xc.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k; simpl; ring.
Qed.

(* ---- Wp 推入：Wp j (0::c::acc) ＝ 0 :: ((2j+3)·c) :: Wp (S j) acc ---- *)
Lemma lw0_Wp_push : forall (j : nat) (c : Q) (acc : qpoly),
  lw0_qpoly_eq (lw0_Wp j (cons 0%Q (cons c acc)))
               (cons 0%Q
                  (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q * c)%Q
                        (lw0_Wp (Datatypes.S j) acc))).
Proof.
  intros j c acc k.
  unfold lw0_Wp.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 1 0 (qpoly_deriv (cons 0%Q (cons c acc)))) by lia.
    cbn [lw0_coef].
    ring.
  - destruct k' as [|k''].
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      rewrite (lw0_qmake_Z_succ (Datatypes.S (Datatypes.S (j + j)))), lw0_qmake_1. ring.
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      unfold lw0_Wp.
      rewrite lw0_coef_add, lw0_coef_scalar, lw0_shift1_deriv_coef.
      cbn [lw0_coef].
      replace (Datatypes.S (Datatypes.S k''))%nat with (k'' + 2)%nat by lia.
      replace (Datatypes.S j + Datatypes.S j)%nat
        with (Datatypes.S (Datatypes.S (j + j)))%nat by lia.
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))%nat
        with ((Datatypes.S (Datatypes.S (j + j))) + 2)%nat by lia.
      rewrite (lw0_qmake_add k'' (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite (lw0_qmake_add (Datatypes.S (Datatypes.S (j + j)))
                (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite lw0_qmake_2.
      ring.
Qed.

(* ---- Xc 推入：Xc j (0::c::acc) ＝ 0 :: ((2j+4)·c) :: Xc (S j) acc ---- *)
Lemma lw0_Xc_push : forall (j : nat) (c : Q) (acc : qpoly),
  lw0_qpoly_eq (lw0_Xc j (cons 0%Q (cons c acc)))
               (cons 0%Q
                  (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))) # 1)%Q * c)%Q
                        (lw0_Xc (Datatypes.S j) acc))).
Proof.
  intros j c acc k.
  unfold lw0_Xc.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 1 0 (qpoly_deriv (cons 0%Q (cons c acc)))) by lia.
    cbn [lw0_coef].
    ring.
  - destruct k' as [|k''].
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))%nat
        with ((Datatypes.S (Datatypes.S (Datatypes.S (j + j))))
                + Datatypes.S Datatypes.O)%nat by lia.
      rewrite lw0_qmake_add, lw0_qmake_1. ring.
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      unfold lw0_Xc.
      rewrite lw0_coef_add, lw0_coef_scalar, lw0_shift1_deriv_coef.
      cbn [lw0_coef].
      replace (Datatypes.S (Datatypes.S k''))%nat with (k'' + 2)%nat by lia.
      replace (Datatypes.S j + Datatypes.S j)%nat
        with (Datatypes.S (Datatypes.S (j + j)))%nat by lia.
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))))%nat
        with ((Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) + 2)%nat by lia.
      rewrite (lw0_qmake_add k'' (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite (lw0_qmake_add (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))
                (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite lw0_qmake_2.
      ring.
Qed.

(* ---- Qmake 算术 key 双件（Hkey/Hkey2 提升为顶层；master 使用面 exact 化） ---- *)
Lemma lw0_sin_qmake_key : forall j : nat,
  ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))) # 1)%Q
    * ((q_pow (-1) (Datatypes.S j)
        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)
  == ((q_pow (-1) (Datatypes.S j)
       / q_fact (Datatypes.S (Datatypes.S (2 * j)))))%Q.
Proof.
  intros j.
  transitivity ((((Z.of_nat (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q + 1)
    * ((q_pow (-1) (Datatypes.S j)
        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)).
  - rewrite (lw0_qmake_Z_succ (Datatypes.S (Datatypes.S (j + j)))). ring.
  - replace (Datatypes.S (Datatypes.S (j + j)))%nat
      with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
    assert (Hpos : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Z) by lia.
    assert (Hn3 : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                = (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) + 1)%Z) by lia.
    assert (Hz3 : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)%Q + 1)
                == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) # 1))
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult]; rewrite Hn3; lia).
    rewrite Hz3.
    rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * j)))).
    rewrite (lw0_q_div_int_mul_gen
               (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
               (q_pow (-1) (Datatypes.S j))
               (q_fact (Datatypes.S (Datatypes.S (2 * j)))) Hpos).
    reflexivity.
Qed.

Lemma lw0_cos_qmake_key : forall j : nat,
  ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))) # 1)%Q
    * ((q_pow (-1) (Datatypes.S (Datatypes.S j))
        / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q)
  == (-1)%Q * ((q_pow (-1) (Datatypes.S j)
                / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q).
Proof.
  intros j.
  assert (Hpos : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))%Z)
    by lia.
  replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))%nat
    with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat by lia.
  replace (Datatypes.S (Datatypes.S (2 * Datatypes.S j)))%nat
    with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat by lia.
  change (q_pow (-1) (Datatypes.S (Datatypes.S j)))
    with ((-1)%Q * q_pow (-1) (Datatypes.S j))%Q.
  rewrite (q_fact_succ (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))).
  rewrite (lw0_q_div_int_mul_gen
             (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
             ((-1)%Q * q_pow (-1) (Datatypes.S j))%Q
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) Hpos).
  unfold Qdiv. ring.
Qed.

(* ---- master_S：sin 表导数 poly 级主引理（acc 泛化；NOEVALIFT 直证） ---- *)
Lemma lw0_sin_aux_deriv_poly_gen : forall (j : nat) (acc : qpoly),
  lw0_qpoly_eq (qpoly_deriv (lw0_sin_aux j acc)) (lw0_cos_aux j (lw0_Wp j acc)).
Proof.
  induction j as [|j IH]; intros acc.
  - intro k.
    change (lw0_sin_aux Datatypes.O acc)
      with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q acc)).
    change (lw0_cos_aux Datatypes.O (lw0_Wp Datatypes.O acc))
      with (cons (q_pow (-1) 0 / q_fact 0)%Q (lw0_Wp Datatypes.O acc)).
    rewrite lw0_coef_deriv.
    destruct k as [|k'].
    + change (Z.of_nat (Datatypes.S Datatypes.O)) with 1%Z.
      cbn [lw0_coef].
      change (q_pow (-1) 0 / q_fact 1) with 1%Q.
      change (q_pow (-1) 0 / q_fact 0) with 1%Q.
      ring.
    + cbn [lw0_coef].
      unfold lw0_Wp.
      rewrite lw0_coef_add, lw0_coef_scalar, lw0_shift1_deriv_coef.
      replace (Datatypes.S (Datatypes.S k'))%nat
        with (Datatypes.S (Datatypes.S (0 + 0)) + k')%nat by lia.
      rewrite lw0_qmake_add.
      ring.
  - change (lw0_sin_aux (Datatypes.S j) acc)
      with (lw0_sin_aux j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 acc))).
    change (lw0_cos_aux (Datatypes.S j) (lw0_Wp (Datatypes.S j) acc))
      with (lw0_cos_aux j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (2 * j))))%Q
                 (lw0_Wp (Datatypes.S j) acc)))).
    apply (lw0_qpoly_eq_trans _ (lw0_cos_aux j (lw0_Wp j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 acc))))).
    + exact (IH (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 acc))).
    + apply lw0_cos_aux_congr.
      apply (lw0_qpoly_eq_trans _ (cons 0%Q
              (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q
                      * (q_pow (-1) (Datatypes.S j)
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                 (lw0_Wp (Datatypes.S j) acc)))).
      * exact (lw0_Wp_push j (q_pow (-1) (Datatypes.S j)
                           / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q acc).
      * apply lw0_cons_congr.
        -- ring.
        -- apply lw0_cons_congr.
           ++ exact (lw0_sin_qmake_key j).
           ++ apply lw0_qpoly_eq_refl.
Qed.

(* ---- master_C：cos 表导数 poly 级主引理（acc 泛化；尾项起点 2j+2） ---- *)
Lemma lw0_cos_aux_deriv_S_poly_gen : forall (j : nat) (acc : qpoly),
  lw0_qpoly_eq (qpoly_deriv (lw0_cos_aux (Datatypes.S j) acc))
               (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                          (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                       (lw0_Xc j acc))).
Proof.
  induction j as [|j IH]; intros acc.
  - intro k.
    change (lw0_cos_aux (Datatypes.S Datatypes.O) acc)
      with (cons (q_pow (-1) 0 / q_fact 0)%Q
              (cons 0%Q
                 (cons (q_pow (-1) (Datatypes.S Datatypes.O)
                         / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.O))))%Q
                    acc))).
    change (lw0_sin_aux Datatypes.O nil)
      with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q nil)).
    rewrite lw0_coef_deriv.
    rewrite lw0_coef_add.
    destruct k as [|k'].
    + rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (Datatypes.O + Datatypes.O))) Datatypes.O (lw0_Xc Datatypes.O acc)) by lia.
      rewrite lw0_coef_scalar.
      cbn [lw0_coef].
      change (Z.of_nat (Datatypes.S Datatypes.O)) with 1%Z.
      ring.
    + destruct k' as [|k''].
      * rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (Datatypes.O + Datatypes.O))) (Datatypes.S Datatypes.O) (lw0_Xc Datatypes.O acc)) by lia.
        rewrite lw0_coef_scalar.
        cbn [lw0_coef].
        change (q_pow (-1) 0 / q_fact 1) with 1%Q.
        change (q_pow (-1) (Datatypes.S Datatypes.O)
                  / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.O))))
          with ((-1) # 2)%Q.
        change (Z.of_nat (Datatypes.S (Datatypes.S Datatypes.O)) # 1) with (1 + 1)%Q.
        ring.
      * rewrite lw0_coef_shift_2.
        unfold lw0_Xc.
        rewrite lw0_coef_add, !lw0_coef_scalar, lw0_shift1_deriv_coef.
        cbn [lw0_coef].
        replace (Datatypes.S (Datatypes.S (Datatypes.S k'')))%nat
          with (Datatypes.S (Datatypes.S (Datatypes.S (0 + 0))) + k'')%nat by lia.
        rewrite lw0_qmake_add.
        ring.
  - change (lw0_cos_aux (Datatypes.S (Datatypes.S j)) acc)
      with (lw0_cos_aux (Datatypes.S j) (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S (Datatypes.S j))
                      / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q
                 acc))).
    change (lw0_sin_aux (Datatypes.S j) nil)
      with (lw0_sin_aux j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 nil))).
    replace (Datatypes.S (Datatypes.S (Datatypes.S j + Datatypes.S j)))%nat
      with (Datatypes.S (Datatypes.S (j + j)) + 2)%nat by lia.
    apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil)) (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (lw0_Xc j (cons 0%Q (cons (q_pow (-1) (Datatypes.S (Datatypes.S j)) / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q acc)))))).
    + exact (IH (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S (Datatypes.S j))
                      / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q
                 acc))).
    + apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil)) (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (cons 0%Q (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q (lw0_Xc (Datatypes.S j) acc)))))).
      * apply lw0_qpoly_eq_add.
        -- apply lw0_qpoly_eq_refl.
        -- apply lw0_shift_congr.
           apply (lw0_qpoly_eq_trans _ (cons 0%Q
                    (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))) # 1)%Q
                            * (q_pow (-1) (Datatypes.S (Datatypes.S j))
                               / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q)%Q
                       (lw0_Xc (Datatypes.S j) acc)))).
           ++ exact (lw0_Xc_push j (q_pow (-1) (Datatypes.S (Datatypes.S j))
                                / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q acc).
           ++ apply lw0_cons_congr.
              ** ring.
              ** apply lw0_cons_congr.
                 --- exact (lw0_cos_qmake_key j).
                 --- apply lw0_qpoly_eq_refl.
      * apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil)) (qpoly_add (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (cons 0%Q (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q nil))) (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O)) (lw0_Xc (Datatypes.S j) acc)))))).
        -- apply lw0_qpoly_eq_add.
           ++ apply lw0_qpoly_eq_refl.
           ++ apply (lw0_qpoly_eq_trans _ (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (qpoly_add (cons 0%Q (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q nil)) (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O)) (lw0_Xc (Datatypes.S j) acc))))).
           --- apply lw0_shift_congr.
               exact (lw0_cons2_shift2 0%Q
                        ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                        (lw0_Xc (Datatypes.S j) acc)).
           --- exact (lw0_shift_add (Datatypes.S (Datatypes.S (j + j)))
                       (cons 0%Q
                          (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                             nil))
                       (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                    (lw0_Xc (Datatypes.S j) acc))).
        -- apply (lw0_qpoly_eq_trans _
                    (qpoly_add (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                            (cons ((-1)%Q * 0%Q)%Q
                                               (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j)
                                                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                                                  nil))))
                              (qpoly_shift (Datatypes.S (Datatypes.S (j + j)) + 2)
                                           (lw0_Xc (Datatypes.S j) acc)))).
           ++ apply (lw0_qpoly_eq_trans _
                       (qpoly_add (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                                  (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                               (cons 0%Q
                                                  (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j)
                                                             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                                                     nil))))
                                 (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                              (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                                           (lw0_Xc (Datatypes.S j) acc))))).
              ** exact (lw0_qpoly_eq_sym _ _
                          (lw0_qpoly_add_assoc (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                             (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                          (cons 0%Q
                                             (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j)
                                                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                                               nil)))
                             (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                          (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                                       (lw0_Xc (Datatypes.S j) acc))))).
              ** apply lw0_qpoly_eq_add.
                 --- apply lw0_qpoly_eq_add.
                     +++ apply lw0_qpoly_eq_refl.
                     +++ apply lw0_shift_congr. apply lw0_cons_congr.
                         ---- ring.
                         ---- apply lw0_qpoly_eq_refl.
                 --- exact (lw0_qpoly_eq_sym _ _
                              (lw0_shift_shift (Datatypes.S (Datatypes.S (j + j)))
                                 (Datatypes.S (Datatypes.S Datatypes.O))
                                 (lw0_Xc (Datatypes.S j) acc))).
           ++ apply lw0_qpoly_eq_add.
              ** exact (lw0_qpoly_eq_sym _ _
                          (lw0_sin_aux_scal_append j (-1)%Q
                             (cons 0%Q
                                (cons (q_pow (-1) (Datatypes.S j)
                                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                                   nil)))).
              ** apply lw0_qpoly_eq_refl.
Qed.

(* ---- σ″ 三件（冻结名；载体＝lw0_qpoly_eq，对表微调令见块头） ---- *)
Lemma lw0_sin_qp_deriv_poly : forall N : nat,
  lw0_qpoly_eq (qpoly_deriv (lw0_sin_qp N)) (lw0_cos_qp N).
Proof.
  intro N. unfold lw0_sin_qp, lw0_cos_qp.
  apply (lw0_qpoly_eq_trans _ (lw0_cos_aux N (lw0_Wp N nil))).
  - apply lw0_sin_aux_deriv_poly_gen.
  - apply (lw0_qpoly_eq_trans _ (lw0_cos_aux N nil)).
    + apply lw0_cos_aux_congr. apply lw0_Wp_nil.
    + apply lw0_qpoly_eq_refl.
Qed.

Lemma lw0_cos_qp_deriv_poly : forall N : nat,
  lw0_qpoly_eq (qpoly_deriv (lw0_cos_qp (Datatypes.S N)))
               (qpoly_scalar (-1)%Q (lw0_sin_qp N)).
Proof.
  intro N. unfold lw0_cos_qp, lw0_sin_qp.
  apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux N nil))
            (qpoly_shift (Datatypes.S (Datatypes.S (N + N))) (lw0_Xc N nil)))).
  - apply lw0_cos_aux_deriv_S_poly_gen.
  - apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux N nil)) (qpoly_shift (Datatypes.S (Datatypes.S (N + N))) (qpoly_scalar (-1)%Q nil)))).
    + apply lw0_qpoly_eq_add.
      * apply lw0_qpoly_eq_refl.
      * apply lw0_shift_congr. exact (lw0_Xc_nil N).
    + exact (lw0_qpoly_eq_sym _ _ (lw0_sin_aux_scal_append N (-1)%Q nil)).
Qed.

Lemma lw0_sin_qp_deriv2 : forall m : nat,
  lw0_qpoly_eq (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S m)))
               (qpoly_scalar (-1)%Q (lw0_sin_qp m)).
Proof.
  intro m.
  change (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S m)))
    with (qpoly_deriv (qpoly_deriv (lw0_sin_qp (Datatypes.S m)))).
  apply (lw0_qpoly_eq_trans _ (qpoly_deriv (lw0_cos_qp (Datatypes.S m)))).
  - apply lw0_qpoly_eq_deriv. apply lw0_sin_qp_deriv_poly.
  - apply lw0_cos_qp_deriv_poly.
Qed.

(* ---- F 块：die 语义系数化三件 ---- *)
Lemma lw0_die_coef_zero : forall (f : qpoly) (k : nat),
  lw0_die f k = true -> forall j : nat, (k <= j)%nat -> lw0_coef j f == 0%Q.
Proof.
  induction f as [|a f' IH]; intros k H j Hj.
  - reflexivity.
  - destruct k as [|k'].
    + simpl in H. discriminate H.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      destruct j as [|j'].
      * exfalso. lia.
      * simpl. apply (IH k' H2 j'). lia.
Qed.

Lemma lw0_coef_deriv_iter_zero : forall (n m : nat) (p : qpoly),
  lw0_coef (m + n)%nat p == 0%Q -> lw0_coef m (qpoly_deriv_iter n p) == 0%Q.
Proof.
  induction n as [|n IH]; intros m p H.
  - replace (m + 0)%nat with m in H by lia. exact H.
  - rewrite qpoly_deriv_iter_succ, lw0_coef_deriv.
    assert (H0 : lw0_coef (Datatypes.S m) (qpoly_deriv_iter n p) == 0%Q).
    { apply (IH (Datatypes.S m) p).
      replace (Datatypes.S m + n)%nat with (m + Datatypes.S n)%nat by lia.
      exact H. }
    rewrite H0. apply Qmult_0_r.
Qed.

Lemma lw0_die_deriv_iter_zero : forall (f : qpoly) (n : nat),
  lw0_die f (Datatypes.S n) = true ->
  forall m : nat, lw0_coef m (qpoly_deriv_iter (Datatypes.S n) f) == 0%Q.
Proof.
  intros f n Hf m.
  apply (lw0_coef_deriv_iter_zero (Datatypes.S n) m f).
  replace (m + Datatypes.S n)%nat with (Datatypes.S n + m)%nat by lia.
  apply (lw0_die_coef_zero f (Datatypes.S n) Hf (Datatypes.S n + m)). lia.
Qed.

(* 去重记录：本块原重名件 lw0_coef_iter_scalar 已去重——复用主件在役版
   （L4660 区，arg 序 k j a p），下方两使用位已按在役参序改写
   （病源：368 回执 §六.3 配方完备性 FAIL 第五病；363 五发早死未及此位）。 *)

(* ---- F_aux 无-die 闭式（纯代数归纳；eval 对应 lw0_F_aux_plus_deriv2 的 poly 级重走） ---- *)
Lemma lw0_F_aux_plus_deriv2_poly : forall (J : nat) (f : qpoly) (c : Q),
  lw0_qpoly_eq (qpoly_add (lw0_F_aux f c J) (qpoly_deriv_iter 2 (lw0_F_aux f c J)))
               (qpoly_add (qpoly_scalar c f)
                          (qpoly_scalar (c * lw0_alt J)%Q
                             (qpoly_deriv_iter (2 * Datatypes.S J) f))).
Proof.
  induction J as [|J' IH]; intros f c.
  - intro k.
    change (lw0_F_aux f c Datatypes.O) with (qpoly_scalar c f).
    repeat rewrite lw0_coef_add.
    rewrite (lw0_coef_iter_scalar 2 k c f).
    repeat rewrite lw0_coef_scalar.
    change (lw0_alt Datatypes.O) with 1%Q.
    change (qpoly_deriv_iter (2 * Datatypes.S Datatypes.O) f) with (qpoly_deriv_iter 2 f).
    ring.
  - intro k.
    change (lw0_F_aux f c (Datatypes.S J'))
      with (qpoly_add (lw0_F_aux f c J')
                      (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                         (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    repeat rewrite lw0_coef_add.
    rewrite (lw0_coef_iter_add 2 k (lw0_F_aux f c J')
               (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                  (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    rewrite (lw0_coef_iter_scalar 2 k (c * lw0_alt (Datatypes.S J'))%Q
               (qpoly_deriv_iter (2 * Datatypes.S J') f)).
    rewrite <- (lw0_qp_deriv_iter_plus 2 (2 * Datatypes.S J') f).
    replace (2 + 2 * Datatypes.S J')%nat
      with (2 * Datatypes.S (Datatypes.S J'))%nat by lia.
    assert (Hih : lw0_coef k (lw0_F_aux f c J')
                     + lw0_coef k (qpoly_deriv_iter 2 (lw0_F_aux f c J'))
                  == c * lw0_coef k f
                     + (c * lw0_alt J')%Q
                         * lw0_coef k (qpoly_deriv_iter (2 * Datatypes.S J') f)).
    { unfold lw0_qpoly_eq in IH. specialize (IH f c k).
      repeat rewrite lw0_coef_add in IH. repeat rewrite lw0_coef_scalar in IH. exact IH. }
    transitivity (lw0_coef k (lw0_F_aux f c J')
                 + lw0_coef k (qpoly_deriv_iter 2 (lw0_F_aux f c J'))
                 + lw0_coef k (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                                (qpoly_deriv_iter (2 * Datatypes.S J') f))
                 + (c * lw0_alt (Datatypes.S J'))%Q
                     * lw0_coef k (qpoly_deriv_iter (2 * Datatypes.S (Datatypes.S J')) f)).
    + repeat rewrite lw0_coef_add. repeat rewrite lw0_coef_scalar. ring.
    + rewrite Hih.
      repeat rewrite lw0_coef_add. repeat rewrite lw0_coef_scalar.
      rewrite (lw0_alt_opp J').
      ring.
Qed.

(* ---- 交付件：poly 级 F_plus_deriv2 变体（355R §R2 供件） ---- *)
Lemma lw0_F_plus_deriv2_poly : forall (f : qpoly) (J : nat),
  lw0_die f (2 * Datatypes.S J) = true ->
  lw0_qpoly_eq (qpoly_add (lw0_F f J) (qpoly_deriv_iter 2 (lw0_F f J))) f.
Proof.
  intros f J Hf k. unfold lw0_F.
  rewrite (lw0_F_aux_plus_deriv2_poly J f 1%Q k).
  repeat rewrite lw0_coef_add. repeat rewrite lw0_coef_scalar.
  assert (Hz : lw0_coef k (qpoly_deriv_iter (2 * Datatypes.S J) f) == 0%Q).
  { replace (2 * Datatypes.S J)%nat with (Datatypes.S (2 * J + 1))%nat by lia.
    apply (lw0_die_deriv_iter_zero f (2 * J + 1)).
    replace (Datatypes.S (2 * J + 1))%nat with (2 * Datatypes.S J)%nat by lia.
    exact Hf. }
  rewrite Hz. ring.
Qed.

(* ---- 随块 PA 锚（六名逐发 Closed 判读） ---- *)
Print Assumptions lw0_sin_qp_deriv_poly.
Print Assumptions lw0_cos_qp_deriv_poly.
Print Assumptions lw0_sin_qp_deriv2.
Print Assumptions lw0_F_plus_deriv2_poly.
Print Assumptions lw0_sin_aux_deriv_poly_gen.
Print Assumptions lw0_cos_aux_deriv_S_poly_gen.

(* 装配实例基座：f := niven_f q (1/den q) n（@11076 逐字）；F := lw0_F f n。 *)
Definition lw0_pitB_pair_conv_f (q : Q) (n : nat) : qpoly :=
  lw0_niven_f q (Zpos (Qden q) # 1)%Q n.

(* 零前缀移位：系数列整体后移 m 位，低次端补 m 个零系数。 *)
Fixpoint lw0_pitB_conv_zero_shift (m : nat) (p : QPoly) : QPoly :=
  match m with
  | Datatypes.O => p
  | Datatypes.S m' => cons 0%Q (lw0_pitB_conv_zero_shift m' p)
  end.

(* 增量单项式 δ_j = x^{2j+1}/(2j+1)!（与例示件 δ_M 同构，正系数承载）。 *)
Definition lw0_pitB_pair_conv_delta (j : nat) : qpoly :=
  qpoly_scalar (1 / q_fact (Datatypes.S (2 * j)))%Q
    (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil)).

(* δ 的主件 qpoly_shift 同构形（sin_inc coef 拆用；桥接引理回接）。 *)
Definition lw0_pitB_pair_conv_delta' (j : nat) : qpoly :=
  qpoly_scalar (1 / q_fact (Datatypes.S (2 * j)))%Q
    (qpoly_shift (Datatypes.S (2 * j)) (cons 1%Q nil)).

(* ---- 增补段〇：系数级等词 Type 载体（主会话裁决标准面） ---- *)

Definition lw0_qpoly_eqT (p q : qpoly) : Type :=
  forall j : nat, QeqT (lw0_coef j p) (lw0_coef j q).

Lemma lw0_qpoly_eqT_of_prop : forall p q : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eqT p q.
Proof.
  intros p q H j. apply qeq_imp_qeqT. exact (H j).
Qed.

Lemma lw0_qpoly_eq_prop_of_eqT : forall p q : qpoly,
  lw0_qpoly_eqT p q -> lw0_qpoly_eq p q.
Proof.
  intros p q H j. apply qeqT_imp_qeq. apply H.
Qed.

Lemma lw0_qpoly_eqT_refl : forall p : qpoly, lw0_qpoly_eqT p p.
Proof.
  intro p. apply lw0_qpoly_eqT_of_prop. apply lw0_qpoly_eq_refl.
Qed.

Lemma lw0_qpoly_eqT_sym : forall p q : qpoly,
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT q p.
Proof.
  intros p q H. apply lw0_qpoly_eqT_of_prop.
  apply lw0_qpoly_eq_sym. apply lw0_qpoly_eq_prop_of_eqT. exact H.
Qed.

Lemma lw0_qpoly_eqT_trans : forall p q r : qpoly,
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT q r -> lw0_qpoly_eqT p r.
Proof.
  intros p q r H1 H2. apply lw0_qpoly_eqT_of_prop.
  apply (lw0_qpoly_eq_trans p q r).
  - apply lw0_qpoly_eq_prop_of_eqT. exact H1.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H2.
Qed.

Lemma lw0_qpoly_eqT_add : forall p1 q1 p2 q2 : qpoly,
  lw0_qpoly_eqT p1 q1 -> lw0_qpoly_eqT p2 q2 ->
  lw0_qpoly_eqT (qpoly_add p1 p2) (qpoly_add q1 q2).
Proof.
  intros p1 q1 p2 q2 H1 H2. apply lw0_qpoly_eqT_of_prop.
  apply lw0_qpoly_eq_add.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H1.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H2.
Qed.

Lemma lw0_qpoly_eqT_cons_congr : forall (a b : Q) (p q : qpoly),
  a == b -> lw0_qpoly_eqT p q -> lw0_qpoly_eqT (cons a p) (cons b q).
Proof.
  intros a b p q Hab H. apply lw0_qpoly_eqT_of_prop.
  apply lw0_cons_congr.
  - exact Hab.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H.
Qed.

(* ---- 增补段一：poly 级同余件族（mul 双变元／scalar／ai／pair 双变元） ---- *)

Lemma lw0_pitB_pair_conv_scalar_congr : forall (c : Q) (p q : qpoly),
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT (qpoly_scalar c p) (qpoly_scalar c q).
Proof.
  intros c p q H j. apply qeq_imp_qeqT.
  rewrite lw0_coef_scalar, lw0_coef_scalar.
  rewrite (qeqT_imp_qeq _ _ (H j)). reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_mul_r : forall (f g1 g2 : qpoly),
  lw0_qpoly_eqT g1 g2 -> lw0_qpoly_eqT (qpoly_mul f g1) (qpoly_mul f g2).
Proof.
  intros f. induction f as [|a f IH]; intros g1 g2 H.
  - cbn [qpoly_mul]. apply lw0_qpoly_eqT_refl.
  - cbn [qpoly_mul]. apply lw0_qpoly_eqT_add.
    + apply lw0_pitB_pair_conv_scalar_congr. exact H.
    + apply lw0_qpoly_eqT_cons_congr.
      * reflexivity.
      * apply IH. exact H.
Qed.

(* mul 左变元同余（槽①供件；coef 级 lw0_mul_comm 铺底三跳）。 *)
Lemma lw0_pitB_pair_conv_mul_comm_eqT : forall A B : qpoly,
  lw0_qpoly_eqT (qpoly_mul A B) (qpoly_mul B A).
Proof.
  intros A B j. apply qeq_imp_qeqT.
  rewrite (lw0_mul_comm A B j). reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_mul_l : forall (g f1 f2 : qpoly),
  lw0_qpoly_eqT f1 f2 -> lw0_qpoly_eqT (qpoly_mul f1 g) (qpoly_mul f2 g).
Proof.
  intros g f1 f2 H.
  apply (lw0_qpoly_eqT_trans _ (qpoly_mul g f1)).
  - apply lw0_pitB_pair_conv_mul_comm_eqT.
  - apply (lw0_qpoly_eqT_trans _ (qpoly_mul g f2)).
    + apply lw0_pitB_pair_conv_mul_r. exact H.
    + apply lw0_pitB_pair_conv_mul_comm_eqT.
Qed.

(* ai 系数展开：第 j 系＝p_j / (S (j+k) # 1)（递归次数指标 k 携带）。 *)
Lemma lw0_pitB_pair_conv_coef_ai : forall (p : qpoly) (k j : nat),
  lw0_coef j (lw0_qp_ai p k)
  == lw0_coef j p / (Z.of_nat (Datatypes.S (j + k)) # 1)%Q.
Proof.
  induction p as [|a p IH]; intros k j.
  - cbn [lw0_qp_ai]. destruct j as [|j']; reflexivity.
  - destruct j as [|j'].
    + reflexivity.
    + cbn [lw0_qp_ai lw0_coef].
      replace (Datatypes.S (Datatypes.S j' + k))%nat
        with (Datatypes.S (j' + Datatypes.S k))%nat by lia.
      rewrite <- (IH (Datatypes.S k) j').
      reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_ai_congr : forall (p q : qpoly) (k : nat),
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT (lw0_qp_ai p k) (lw0_qp_ai q k).
Proof.
  intros p q k H j. apply qeq_imp_qeqT.
  rewrite lw0_pitB_pair_conv_coef_ai, lw0_pitB_pair_conv_coef_ai.
  rewrite (qeqT_imp_qeq _ _ (H j)). reflexivity.
Qed.

(* pair 对第二变元的 poly 级同余（mul_r→ai_congr→cons 0→eval_len_indep
   降岸链；零 eval 外延桥——单向 poly→eval）。 *)
Lemma lw0_pitB_pair_conv_pair_congr_r : forall (f g1 g2 : qpoly) (x : Q),
  lw0_qpoly_eqT g1 g2 -> QeqT (lw0_qp_pair f g1 x) (lw0_qp_pair f g2 x).
Proof.
  intros f g1 g2 x H. apply qeq_imp_qeqT. apply lw0_eval_len_indep.
  intro j. unfold lw0_qp_pair, lw0_qp_antideriv.
  destruct j as [|j'].
  - reflexivity.
  - apply lw0_cons_congr.
    + reflexivity.
    + apply lw0_qpoly_eq_prop_of_eqT.
      apply lw0_pitB_pair_conv_ai_congr. apply lw0_pitB_pair_conv_mul_r. exact H.
Qed.

(* pair 对第一变元的 poly 级同余（槽①供件；mul_l 对应链）。 *)
Lemma lw0_pitB_pair_conv_pair_congr_l : forall (f1 f2 g : qpoly) (x : Q),
  lw0_qpoly_eqT f1 f2 -> QeqT (lw0_qp_pair f1 g x) (lw0_qp_pair f2 g x).
Proof.
  intros f1 f2 g x H. apply qeq_imp_qeqT. apply lw0_eval_len_indep.
  intro j. unfold lw0_qp_pair, lw0_qp_antideriv.
  destruct j as [|j'].
  - reflexivity.
  - apply lw0_cons_congr.
    + reflexivity.
    + apply lw0_qpoly_eq_prop_of_eqT.
      apply lw0_pitB_pair_conv_ai_congr. apply lw0_pitB_pair_conv_mul_l. exact H.
Qed.

(* ---- 增补段二：zero_shift↔qpoly_shift 桥（结构同构 cons 链） ---- *)

Lemma lw0_pitB_pair_conv_zshift_bridge : forall (n : nat) (p : qpoly),
  lw0_qpoly_eqT (lw0_pitB_conv_zero_shift n p) (qpoly_shift n p).
Proof.
  induction n as [|n IH]; intros p.
  - cbn [lw0_pitB_conv_zero_shift qpoly_shift]. apply lw0_qpoly_eqT_refl.
  - cbn [lw0_pitB_conv_zero_shift qpoly_shift].
    apply lw0_qpoly_eqT_cons_congr.
    + reflexivity.
    + apply IH.
Qed.

Lemma lw0_pitB_pair_conv_delta_br : forall j : nat,
  lw0_qpoly_eqT (lw0_pitB_pair_conv_delta j) (lw0_pitB_pair_conv_delta' j).
Proof.
  intro j. apply lw0_pitB_pair_conv_scalar_congr.
  apply lw0_pitB_pair_conv_zshift_bridge.
Qed.

(* ---- 增补段三：sin_aux coef 拼接件（acc 出口深度 2j+2；hi 先位供 lo 界段使用） ---- *)

Lemma lw0_pitB_pair_conv_sin_aux_hi : forall (j : nat) (acc : qpoly) (r : nat),
  lw0_coef ((2 * j + 2 + r)%nat) (lw0_sin_aux j acc)
  == lw0_coef ((2 * j + 2 + r)%nat) (lw0_sin_aux j nil) + lw0_coef r acc.
Proof.
  induction j as [|j IH]; intros acc r.
  - replace (2 * 0 + 2 + r)%nat with (Datatypes.S (Datatypes.S r))%nat by lia.
    cbn [lw0_sin_aux lw0_coef]. ring.
  - cbn [lw0_sin_aux].
    replace (2 * Datatypes.S j + 2 + r)%nat
      with (2 * j + 2 + (r + 2))%nat by lia.
    rewrite (IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     acc)) (r + 2)%nat).
    rewrite (IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     nil)) (r + 2)%nat).
    replace (r + 2)%nat with (Datatypes.S (Datatypes.S r))%nat by lia.
    cbn [lw0_coef]. ring.
Qed.

Lemma lw0_pitB_pair_conv_sin_aux_lo : forall (j : nat) (acc : qpoly) (k : nat),
  (k < Datatypes.S (Datatypes.S (2 * j)))%nat ->
  lw0_coef k (lw0_sin_aux j acc) == lw0_coef k (lw0_sin_aux j nil).
Proof.
  induction j as [|j IH]; intros acc k Hk.
  - destruct k as [|k'].
    + reflexivity.
    + destruct k' as [|k''].
      * reflexivity.
      * exfalso. lia.
  - cbn [lw0_sin_aux].
    destruct (le_lt_dec (Datatypes.S (Datatypes.S (2 * j)))%nat k) as [Hge | Hlt].
    + replace k with ((2 * j + 2 + (k - (2 * j + 2)))%nat) by lia.
      rewrite (lw0_pitB_pair_conv_sin_aux_hi j (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     acc)) (k - (2 * j + 2))%nat).
      rewrite (lw0_pitB_pair_conv_sin_aux_hi j (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     nil)) (k - (2 * j + 2))%nat).
      destruct (k - (2 * j + 2))%nat as [|b] eqn:HD.
      * cbn [lw0_coef]. ring.
      * destruct b as [|b'] eqn:HD2.
        -- cbn [lw0_coef]. ring.
        -- exfalso. lia.
    + assert (Hk' : (k < Datatypes.S (Datatypes.S (2 * j)))%nat) by lia.
      assert (H1 := IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     acc)) k Hk').
      assert (H2 := IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     nil)) k Hk').
      rewrite H1, H2. reflexivity.
Qed.

(* ---- 增补段四：σ 增量件（poly 级；实形＝(−1)^{S j}·δ_{S j}） ---- *)

(* 除法右逆微件：a/d 与 a·(1/d) 的 Qeq 对齐（环标准形差异；Qdiv 展开
   Qinv 后 ring 闭合——sin_inc 主元档除法对齐用）。 *)
Lemma lw0_pitB_pair_conv_qdiv_mult_inv : forall a d : Q, a / d == a * (1 / d)%Q.
Proof.
  intros a d. unfold Qdiv. ring.
Qed.

Lemma lw0_pitB_pair_conv_sin_inc : forall j : nat,
  lw0_qpoly_eqT (qpoly_add (lw0_sin_qp (Datatypes.S j))
                            (qpoly_scalar (-1)%Q (lw0_sin_qp j)))
                (qpoly_scalar (q_pow (-1) (Datatypes.S j))%Q
                              (lw0_pitB_pair_conv_delta' (Datatypes.S j))).
Proof.
  intro j. unfold lw0_sin_qp, lw0_pitB_pair_conv_delta'.
  cbn [lw0_sin_aux]. intro k.
  apply qeq_imp_qeqT.
  rewrite lw0_coef_add, lw0_coef_scalar, lw0_coef_scalar.
  destruct (le_lt_dec (Datatypes.S (Datatypes.S (2 * j)))%nat k) as [Hge | Hlt].
  - replace k with ((Datatypes.S (Datatypes.S (2 * j)) + (k - Datatypes.S (Datatypes.S (2 * j))))%nat)
      by lia.
    replace (Datatypes.S (Datatypes.S (2 * j)))%nat
      with (2 * j + 2)%nat by lia.
    rewrite lw0_pitB_pair_conv_sin_aux_hi.
    rewrite lw0_pitB_pair_conv_sin_aux_hi.
    rewrite lw0_coef_scalar.
    destruct (k - (2 * j + 2))%nat as [|b] eqn:HD.
    + rewrite lw0_coef_shift_lt by lia. cbn [lw0_coef]. ring.
    + replace (2 * j + 2 + Datatypes.S b)%nat
        with (Datatypes.S (2 * Datatypes.S j) + b)%nat by lia.
      rewrite lw0_coef_shift.
      destruct b as [|b'] eqn:HD2.
      * cbn [lw0_coef].
        replace (Datatypes.S (2 * j + 2))%nat
          with (Datatypes.S (2 * Datatypes.S j))%nat by lia.
        rewrite Qmult_1_r.
        rewrite <- (lw0_pitB_pair_conv_qdiv_mult_inv
                      (q_pow (-1) (Datatypes.S j))%Q
                      (q_fact (Datatypes.S (2 * Datatypes.S j)))).
        assert (Hcancel : forall A : Q,
                   (A + 0%Q + (q_pow (-1) (Datatypes.S j)
                                / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q)
                   + (-1)%Q * (A + 0%Q)
                   == (q_pow (-1) (Datatypes.S j)
                       / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q)
          by (intro A; ring).
        apply Hcancel.
      * cbn [lw0_coef]. ring.
  - rewrite lw0_pitB_pair_conv_sin_aux_lo by exact Hlt.
    rewrite lw0_coef_scalar.
    replace (Datatypes.S (Datatypes.S (2 * j)))%nat
      with (2 * j + 2)%nat by lia.
    rewrite lw0_coef_shift_lt by lia.
    ring.
Qed.

(* ---- 增补段五：|q_pow (−1) (S j)|＝1（符号因子吞号件） ---- *)

Lemma lw0_pitB_pair_conv_qabs_sign1 : forall j : nat,
  Qabs (q_pow (-1) (Datatypes.S j)) == 1%Q.
Proof.
  intro j.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_qabs_pow (-1)%Q (Datatypes.S j))).
  change (Qabs (-1)%Q) with 1%Q. apply lw0_q_pow_one.
Qed.

(* ---- 增补段六：槽②消去供件（σ″-pair 岸；lw0_sin_qp_deriv2 直供） ---- *)

Lemma lw0_pitB_pair_conv_sig2 : forall (q : Q) (n j : nat) (x : Q),
  QeqT (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) x
        + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x)
       0%Q.
Proof.
  intros q n j x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _
            (lw0_pitB_pair_conv_pair_congr_r
               (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j)))
               (qpoly_scalar (-1)%Q (lw0_sin_qp j)) x
               (lw0_qpoly_eqT_of_prop _ _ (lw0_sin_qp_deriv2 j)))).
  rewrite (lw0_qp_pair_scalar_r (-1)%Q
             (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x).
  ring.
Qed.

(* ---- 增补段七：槽③消去供件（σ 增量-pair 岸带符号因子） ---- *)

Lemma lw0_pitB_pair_conv_sinc : forall (q : Q) (n j : nat) (x : Q),
  QeqT (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
          (lw0_sin_qp (Datatypes.S j)) x
        - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x)
       ((q_pow (-1) (Datatypes.S j))%Q
        * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
            (lw0_pitB_pair_conv_delta (Datatypes.S j)) x).
Proof.
  intros q n j x. apply qeq_imp_qeqT.
  rewrite <- (lw0_qp_pair_scalar_r (q_pow (-1) (Datatypes.S j))%Q
                (lw0_F (lw0_pitB_pair_conv_f q n) n)
                (lw0_pitB_pair_conv_delta (Datatypes.S j)) x).
  rewrite (qeqT_imp_qeq _ _
            (lw0_pitB_pair_conv_pair_congr_r
               (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (qpoly_scalar (q_pow (-1) (Datatypes.S j))%Q
                  (lw0_pitB_pair_conv_delta (Datatypes.S j)))
               (qpoly_add (lw0_sin_qp (Datatypes.S j))
                          (qpoly_scalar (-1)%Q (lw0_sin_qp j))) x
               (lw0_qpoly_eqT_trans _ _ _
                  (lw0_pitB_pair_conv_scalar_congr (q_pow (-1) (Datatypes.S j))%Q
                     (lw0_pitB_pair_conv_delta (Datatypes.S j))
                     (lw0_pitB_pair_conv_delta' (Datatypes.S j))
                     (lw0_pitB_pair_conv_delta_br (Datatypes.S j)))
                  (lw0_qpoly_eqT_sym _ _ (lw0_pitB_pair_conv_sin_inc j))))).
  rewrite (lw0_qp_pair_add_r (lw0_F (lw0_pitB_pair_conv_f q n) n)
             (lw0_sin_qp (Datatypes.S j))
             (qpoly_scalar (-1)%Q (lw0_sin_qp j)) x).
  rewrite (lw0_qp_pair_scalar_r (-1)%Q
             (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x).
  ring.
Qed.

(* 核心链（槽① GAPASUME 保留位）：E_m == pair(F,σ″_m) + pair(F,σ_m)。 *)
Lemma lw0_pitB_pair_conv_core : forall (q : Q) (n m : nat),
  (forall x : Q,
     QeqT (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_pitB_pair_conv_f q n) n)) (lw0_sin_qp m) x
          + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) x)
          (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) x)) ->
  lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) q
  - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
  - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
    * qpoly_eval (lw0_sin_qp m) q
  + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
    * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q
  == lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q
     + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
         (qpoly_deriv_iter 2 (lw0_sin_qp m)) q.
Proof.
  intros q n m HF2.
  assert (Hz0 : qpoly_eval (lw0_sin_qp m) 0 == 0)
    by (apply lw0_sin_qp_zero_eval).
  assert (Ho1 : qpoly_eval (qpoly_deriv (lw0_sin_qp m)) 0 == 1%Q)
    by (rewrite (lw0_sin_qp_deriv_eval m 0); apply lw0_cos_partial_zero).
  assert (HA := lw0_pitB_ibp_dbl (lw0_F (lw0_pitB_pair_conv_f q n) n)
                                 (lw0_sin_qp m) q).
  assert (HB := qeqT_imp_qeq _ _ (HF2 q)).
  assert (HAm : lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_pitB_pair_conv_f q n) n)) (lw0_sin_qp m) q
                == lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) q
                 - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q).
  { transitivity (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_pitB_pair_conv_f q n) n)) (lw0_sin_qp m) q
                  + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q
                  - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q).
    - ring.
    - rewrite HB. ring. }
  rewrite HAm in HA.
  rewrite (qpoly_eval_mul (lw0_F (lw0_pitB_pair_conv_f q n) n)
             (qpoly_deriv (lw0_sin_qp m)) q) in HA.
  rewrite (qpoly_eval_mul (lw0_F (lw0_pitB_pair_conv_f q n) n)
             (qpoly_deriv (lw0_sin_qp m)) 0) in HA.
  rewrite (qpoly_eval_mul (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n))
             (lw0_sin_qp m) q) in HA.
  rewrite (qpoly_eval_mul (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n))
             (lw0_sin_qp m) 0) in HA.
  rewrite Ho1 in HA. rewrite Hz0 in HA.
  rewrite HA. ring.
Qed.

(* ---- 增补段八：Qabs 桥微件（stdlib 无 Qabs_wd 名面——Qabs_case 机械路自建） ---- *)

Lemma lw0_pitB_pair_conv_qabs_canon : forall x : Q,
  Qabs x == (if Qle_bool 0 x then x else (- x)%Q).
Proof.
  intro x.
  apply (Qabs_case x (fun z => z == (if Qle_bool 0 x then x else (- x)%Q))).
  - intros Hx. rewrite (proj2 (Qle_bool_iff 0 x) Hx). reflexivity.
  - intros Hx0. destruct (Qle_bool 0 x) eqn:E.
    + assert (Hz : x == 0%Q).
      { apply (Qle_antisym x 0).
        - exact Hx0.
        - exact (Qle_bool_imp_le 0 x E). }
      rewrite Hz. reflexivity.
    + reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_qabs_wd : forall (x y : Q), x == y -> Qabs x == Qabs y.
Proof.
  intros x y Hxy.
  rewrite (lw0_pitB_pair_conv_qabs_canon x).
  rewrite (lw0_pitB_pair_conv_qabs_canon y).
  destruct (Qle_bool 0 x) eqn:Ex; destruct (Qle_bool 0 y) eqn:Ey.
  - exact Hxy.
  - exfalso.
    assert (Hx0 : 0 <= x) by (apply (Qle_bool_imp_le 0 x Ex)).
    assert (Hby : Qle_bool 0 y = Qle_bool 0 x) by (rewrite Hxy; reflexivity).
    rewrite Hby in Ey. rewrite (proj2 (Qle_bool_iff 0 x) Hx0) in Ey. discriminate Ey.
  - exfalso.
    assert (Hy0 : 0 <= y) by (apply (Qle_bool_imp_le 0 y Ey)).
    assert (Hbx : Qle_bool 0 x = Qle_bool 0 y) by (rewrite Hxy; reflexivity).
    rewrite Hbx in Ex. rewrite (proj2 (Qle_bool_iff 0 y) Hy0) in Ex. discriminate Ex.
  - rewrite Hxy. reflexivity.
Qed.

(* ---- 贴装闭包·fbound 16 件（_tlw376 跑匣 80a07e22 源剥壳；语句面证明体逐字未动） ---- *)

(* ---------- 移位占优砖原件拷入（零前缀移位与分母单调组） ---------- *)

(* 零头系数对权重无贡献：移位一位时权重恰乘 |c| 且指标后移一位。 *)
Lemma lw0_pitB_conv_pwi_shift1_eq : forall (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (cons 0%Q p) k c)
       (Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
Proof.
  intros p k c. apply qeq_imp_qeqT.
  change (lw0_pitB_conv_pwi (cons 0%Q p) k c)
    with (Qabs 0%Q * (Qabs c / lw0_q_of_nat (Datatypes.S k))
          + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
  assert (E0 : QeqT (Qabs 0%Q) 0%Q) by (unfold QeqT; cbn; reflexivity).
  rewrite (qeqT_imp_qeq _ _ E0).
  ring.
Qed.

(* 移位换形：前置 m 个零系数恰把权重乘 |c|^m 并把指标平移 m。 *)
Lemma lw0_pitB_conv_pwi_zero_shift_eq : forall (m : nat) (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m p) k c)
       (q_pow (Qabs c) m * lw0_pitB_conv_pwi p (k + m)%nat c).
Proof.
  intro m. induction m as [| m IH]; intros p k c.
  - change (lw0_pitB_conv_zero_shift 0 p) with p.
    change (q_pow (Qabs c) 0) with 1%Q.
    rewrite Nat.add_0_r.
    apply qeq_imp_qeqT. ring.
  - change (lw0_pitB_conv_zero_shift (Datatypes.S m) p)
      with (cons 0%Q (lw0_pitB_conv_zero_shift m p)).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
              (lw0_pitB_conv_pwi_shift1_eq (lw0_pitB_conv_zero_shift m p) k c)).
    rewrite (qeqT_imp_qeq _ _ (IH p (Datatypes.S k) c)).
    assert (E1 : (Datatypes.S k + m)%nat = Datatypes.S (k + m)%nat) by lia.
    rewrite E1.
    rewrite (Nat.add_succ_r k m).
    rewrite (q_pow_succ (Qabs c) m).
    ring.
Qed.

(* 非负分子关于正分母的逐项反单调：分母大者商不增。 *)
Lemma lw0_pitB_conv_div_den_mono : forall (x d1 d2 : Q),
  QleT' 0 x -> QleT' 1 d1 -> QleT' d1 d2 ->
  QleT' (x / d2) (x / d1).
Proof.
  intros x d1 d2 Hx0 Hd1 Hd12.
  apply Qle_to_QleT'.
  assert (H01 : Qlt 0 1%Q) by (apply QltT_to_Qlt; unfold QltT; reflexivity).
  assert (Hlt1 : Qlt 0 d1).
  { apply (Qlt_le_trans 0%Q 1%Q d1).
    - exact H01.
    - exact (QleT'_to_Qle _ _ Hd1). }
  assert (Hlt2 : Qlt 0 d2).
  { apply (Qlt_le_trans 0%Q 1%Q d2).
    - exact H01.
    - apply QleT'_to_Qle. exact (qleT'_trans 1%Q d1 d2 Hd1 Hd12). }
  assert (Hne1 : d1 == 0%Q -> False).
  { intros H. apply (qltT_not_eq_zero d1). apply Qlt_to_QltT. exact Hlt1. exact H. }
  assert (Hne2 : d2 == 0%Q -> False).
  { intros H. apply (qltT_not_eq_zero d2). apply Qlt_to_QltT. exact Hlt2. exact H. }
  assert (HstepA : QleT' (d1 * / d2) 1%Q).
  { apply (qleT'_trans (d1 * / d2)%Q (/ d2 * d2)%Q 1%Q).
    - apply (qleT'_trans (d1 * / d2)%Q (/ d2 * d1)%Q (/ d2 * d2)%Q).
      + apply qeq_leT'. ring.
      + apply (lw0_pitB_conv_mult_le_l (/ d2) d1 d2 Hd12).
        apply Qle_to_QleT'. apply Qinv_le_0_compat.
        apply (Qlt_le_weak 0). exact Hlt2.
    - apply qeq_leT'. rewrite (Qmult_comm (/ d2) d2).
      apply Qmult_inv_r. exact Hne2. }
  assert (HstepB : QleT' (/ d2) (/ d1)).
  { apply (qleT'_trans (/ d2)%Q (/ d1 * (d1 * / d2))%Q (/ d1)%Q).
    - apply qeq_leT'.
      rewrite (Qmult_assoc (/ d1) d1 (/ d2)).
      rewrite (Qmult_comm (/ d1) d1).
      rewrite (Qmult_inv_r d1 Hne1).
      ring.
    - apply (qleT'_trans (/ d1 * (d1 * / d2))%Q (/ d1 * 1)%Q (/ d1)%Q).
      + apply (lw0_pitB_conv_mult_le_l (/ d1) (d1 * / d2)%Q 1%Q HstepA).
        apply Qle_to_QleT'. apply Qinv_le_0_compat.
        apply (Qlt_le_weak 0). exact Hlt1.
      + apply qeq_leT'. ring. }
  apply QleT'_to_Qle.
  apply (lw0_pitB_conv_mult_le_l x (/ d2) (/ d1) HstepB Hx0).
Qed.

(* 分母指标单调：权重泛函随分母指标递增而不增。 *)
Lemma lw0_pitB_conv_pwi_k_mono : forall (p : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi p (Datatypes.S k) c) (lw0_pitB_conv_pwi p k c).
Proof.
  intro p. induction p as [| a p IH]; intros k c.
  - change (lw0_pitB_conv_pwi nil (Datatypes.S k) c) with 0%Q.
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' 0%Q 0%Q). apply Qeq_refl.
  - change (lw0_pitB_conv_pwi (cons a p) (Datatypes.S k) c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S (Datatypes.S k)) c).
    change (lw0_pitB_conv_pwi (cons a p) k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
    apply (qleT'_trans
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S (Datatypes.S k)) c)
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)).
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                 (lw0_pitB_conv_pwi p (Datatypes.S (Datatypes.S k)) c)
                 (lw0_pitB_conv_pwi p (Datatypes.S k) c)
                 (IH (Datatypes.S k) c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs a)
                 (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
                 (Qabs c / lw0_q_of_nat (Datatypes.S k))).
        -- apply (lw0_pitB_conv_div_den_mono (Qabs c)
                    (lw0_q_of_nat (Datatypes.S k))
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S k)))).
           ++ apply Qle_to_QleT'. apply Qabs_nonneg.
           ++ exact (lw0_q_of_nat_ge_one k).
           ++ exact (lw0_q_of_nat_le_succ (Datatypes.S k)).
        -- apply Qle_to_QleT'. apply Qabs_nonneg.
      * apply Qle_refl.
Qed.

(* 多步分母指标单调：指标加 j 后权重不超过原指标下的权重。 *)
Lemma lw0_pitB_conv_pwi_add_k_mono : forall (p : QPoly) (k j : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi p (k + j)%nat c) (lw0_pitB_conv_pwi p k c).
Proof.
  intros p k j. induction j as [| j IH]; intro c.
  - rewrite Nat.add_0_r. apply Qle_to_QleT'. apply Qle_refl.
  - assert (E : (k + Datatypes.S j)%nat = Datatypes.S (k + j)%nat) by lia.
    rewrite E.
    apply (qleT'_trans (lw0_pitB_conv_pwi p (Datatypes.S (k + j)) c)
                       (lw0_pitB_conv_pwi p (k + j) c)
                       (lw0_pitB_conv_pwi p k c)).
    + exact (lw0_pitB_conv_pwi_k_mono p (k + j) c).
    + exact (IH c).
Qed.

(* ---------- 系数权界组（本件新面） ---------- *)

(* 权重非负：权重为逐项绝对值加权和，恒非负。 *)
Lemma lw0_pitB_conv_pwi_nonneg : forall (p : QPoly) (k : nat) (c : Q),
  QleT' 0 (lw0_pitB_conv_pwi p k c).
Proof.
  intro p. induction p as [| a p IH]; intros k c.
  - change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' 0%Q 0%Q). apply Qeq_refl.
  - change (lw0_pitB_conv_pwi (cons a p) k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
    assert (Hd : Qle 0 (Qabs c / lw0_q_of_nat (Datatypes.S k))).
    { apply Qmult_le_0_compat.
      - apply Qabs_nonneg.
      - apply Qinv_le_0_compat.
        apply Qlt_le_weak.
        apply (Qlt_le_trans 0%Q 1%Q (lw0_q_of_nat (Datatypes.S k))).
        + apply QltT_to_Qlt. unfold QltT. reflexivity.
        + apply QleT'_to_Qle. apply lw0_q_of_nat_ge_one. }
    assert (Hsum : Qle (0 + 0)%Q
              (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
               + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)%Q).
    { apply Qplus_le_compat.
      - apply Qmult_le_0_compat.
        + apply Qabs_nonneg.
        + exact Hd.
      - apply Qmult_le_0_compat.
        + apply Qabs_nonneg.
        + exact (QleT'_to_Qle _ _ (IH (Datatypes.S k) c)). }
    apply Qle_to_QleT'. rewrite Qplus_0_l in Hsum. exact Hsum.
Qed.

(* 单位单项式权重：x = 1 的权重恰为 |c| 除以下一分母指标。 *)
Lemma lw0_pitB_conv_pwi_one_eq : forall (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (cons 1%Q nil) k c)
       (Qabs c / lw0_q_of_nat (Datatypes.S k)).
Proof.
  intros k c. apply qeq_imp_qeqT.
  change (lw0_pitB_conv_pwi (cons 1%Q nil) k c)
    with (Qabs 1%Q * (Qabs c / lw0_q_of_nat (Datatypes.S k))
          + Qabs c * lw0_pitB_conv_pwi nil (Datatypes.S k) c).
  change (lw0_pitB_conv_pwi nil (Datatypes.S k) c) with 0%Q.
  assert (E1 : QeqT (Qabs 1%Q) 1%Q) by (unfold QeqT; cbn; reflexivity).
  rewrite (qeqT_imp_qeq _ _ E1).
  ring.
Qed.

(* 逐系数遥括：对右因子 g，f 的权重按 |f_j|·|c|^j·pwi g (k+j) c 展开。 *)
Fixpoint lw0_pitB_conv_pwi_muliter (f g : QPoly) (k : nat) (c : Q) : Q :=
  match f with
  | nil => 0%Q
  | cons a f' => Qabs a * lw0_pitB_conv_pwi g k c
                 + Qabs c * lw0_pitB_conv_pwi_muliter f' g (Datatypes.S k) c
  end.

(* 乘积权重嵌遥括和：乘积权重不超过逐系数遥括和。 *)
Lemma lw0_pitB_conv_pwi_mul_le_iter : forall (f g : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (qpoly_mul f g) k c)
        (lw0_pitB_conv_pwi_muliter f g k c).
Proof.
  intro f. induction f as [| a f' IH]; intros g k c.
  - change (lw0_pitB_conv_pwi (qpoly_mul nil g) k c) with 0%Q.
    change (lw0_pitB_conv_pwi_muliter nil g k c) with 0%Q.
    apply (qeq_leT' 0%Q 0%Q). apply Qeq_refl.
  - apply (qleT'_trans
             (lw0_pitB_conv_pwi (qpoly_mul (cons a f') g) k c)
             (Qabs a * lw0_pitB_conv_pwi g k c
              + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f' g) (Datatypes.S k) c)
             (Qabs a * lw0_pitB_conv_pwi g k c
              + Qabs c * lw0_pitB_conv_pwi_muliter f' g (Datatypes.S k) c)).
    + exact (lw0_pitB_conv_pwi_mul_le a f' g k c).
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                 (lw0_pitB_conv_pwi (qpoly_mul f' g) (Datatypes.S k) c)
                 (lw0_pitB_conv_pwi_muliter f' g (Datatypes.S k) c)).
        -- exact (IH g (Datatypes.S k) c).
        -- apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

(* 移位单位式点态压回：m 位移位单位式在任一指标下的权重不超过
   |c|^m 倍的单位式权重（移位幂恰由分母单调逐项压回）。 *)
Lemma lw0_pitB_conv_pwi_shift_one_domin : forall (m j : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) j c)
        (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) j c).
Proof.
  intros m j c.
  apply (qleT'_trans
          (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) j c)
          (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) (j + m)%nat c)
          (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) j c)).
  - apply qeq_leT'. apply qeqT_imp_qeq.
    exact (lw0_pitB_conv_pwi_zero_shift_eq m (cons 1%Q nil) j c).
  - apply (lw0_pitB_conv_mult_le_l (q_pow (Qabs c) m)
             (lw0_pitB_conv_pwi (cons 1%Q nil) (j + m)%nat c)
             (lw0_pitB_conv_pwi (cons 1%Q nil) j c)
             (lw0_pitB_conv_pwi_add_k_mono (cons 1%Q nil) j m c)).
    apply Qle_to_QleT'. apply q_pow_nonneg. apply Qabs_nonneg.
Qed.

(* 遥括和标量外提：右因子带标量倍时标量绝对值整体外提。 *)
Lemma lw0_pitB_conv_pwi_muliter_scalar : forall (f : QPoly) (s : Q) (m : nat) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi_muliter f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
       (Qabs s * lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c).
Proof.
  intro f. induction f as [| a f' IH]; intros s m k c.
  - change (lw0_pitB_conv_pwi_muliter nil (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
      with 0%Q.
    change (lw0_pitB_conv_pwi_muliter nil (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with 0%Q.
    apply qeq_imp_qeqT. rewrite Qmult_0_r. apply Qeq_refl.
  - change (lw0_pitB_conv_pwi_muliter (cons a f')
              (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
      with (Qabs a * lw0_pitB_conv_pwi (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c
            + Qabs c * lw0_pitB_conv_pwi_muliter f'
                (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) (Datatypes.S k) c).
    change (Qabs s * lw0_pitB_conv_pwi_muliter (cons a f')
              (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with (Qabs s * (Qabs a * lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c
                      + Qabs c * lw0_pitB_conv_pwi_muliter f'
                          (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c)).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
              (lw0_pitB_conv_pwi_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)).
    rewrite (qeqT_imp_qeq _ _ (IH s m (Datatypes.S k) c)).
    ring.
Qed.

(* 遥括和移位幂压回：右因子为 m 位移位单位式时至多付 |c|^m 幂因子。 *)
Lemma lw0_pitB_conv_pwi_muliter_shift : forall (f : QPoly) (m : nat) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
        (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c).
Proof.
  intro f. induction f as [| a f' IH]; intros m k c.
  - change (lw0_pitB_conv_pwi_muliter nil (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with 0%Q.
    change (lw0_pitB_conv_pwi_muliter nil (cons 1%Q nil) k c) with 0%Q.
    apply (qeq_leT' 0%Q (q_pow (Qabs c) m * 0%Q)).
    rewrite Qmult_0_r. apply Qeq_refl.
  - change (lw0_pitB_conv_pwi_muliter (cons a f')
              (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with (Qabs a * lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c
            + Qabs c * lw0_pitB_conv_pwi_muliter f'
                (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c).
    apply (qleT'_trans
            (Qabs a * lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c
             + Qabs c * lw0_pitB_conv_pwi_muliter f'
                 (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c)
            (Qabs a * (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) k c)
             + Qabs c * (q_pow (Qabs c) m
                         * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c))
            (q_pow (Qabs c) m
             * (Qabs a * lw0_pitB_conv_pwi (cons 1%Q nil) k c
                + Qabs c * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c))).
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs a)
                   (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
                   (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) k c)
                   (lw0_pitB_conv_pwi_shift_one_domin m k c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                   (lw0_pitB_conv_pwi_muliter f'
                     (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c)
                   (q_pow (Qabs c) m
                    * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c)
                   (IH m (Datatypes.S k) c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
    + apply qeq_leT'. ring.
Qed.

(* 遥括和还原恒等：对单位式右因子，遥括和恰等于原权重。 *)
Lemma lw0_pitB_conv_pwi_muliter_eq : forall (f : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c)
       (lw0_pitB_conv_pwi f k c).
Proof.
  intro f. induction f as [| a f' IH]; intros k c.
  - change (lw0_pitB_conv_pwi_muliter nil (cons 1%Q nil) k c) with 0%Q.
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply qeq_imp_qeqT. apply Qeq_refl.
  - change (lw0_pitB_conv_pwi_muliter (cons a f') (cons 1%Q nil) k c)
      with (Qabs a * lw0_pitB_conv_pwi (cons 1%Q nil) k c
            + Qabs c * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_one_eq k c)).
    rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k) c)).
    change (lw0_pitB_conv_pwi (cons a f') k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi f' (Datatypes.S k) c).
    ring.
Qed.

(* 系数权界主件：乘单项式 s·x^m 的权重至多付 |s|·|c|^m 倍。 *)
Lemma lw0_pitB_conv_pwi_mul_shift_domin : forall (f : QPoly) (s : Q) (m : nat) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi
          (qpoly_mul f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)))) k c)
        (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi f k c)).
Proof.
  intros f s m k c.
  apply (qleT'_trans
          (lw0_pitB_conv_pwi
            (qpoly_mul f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)))) k c)
          (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c))
          (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi f k c))).
  - apply (qleT'_trans
            (lw0_pitB_conv_pwi
              (qpoly_mul f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)))) k c)
            (lw0_pitB_conv_pwi_muliter f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
            (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c))).
    + exact (lw0_pitB_conv_pwi_mul_le_iter f
               (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c).
    + apply (qleT'_trans
              (lw0_pitB_conv_pwi_muliter f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
              (Qabs s * lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
              (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c))).
      * apply qeq_leT'. apply qeqT_imp_qeq.
        exact (lw0_pitB_conv_pwi_muliter_scalar f s m k c).
      * apply (lw0_pitB_conv_mult_le_l (Qabs s)
                 (lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
                 (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c)
                 (lw0_pitB_conv_pwi_muliter_shift f m k c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
  - apply qeq_leT'.
    rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_muliter_eq f k c)).
    ring.
Qed.

(* 规范化尾项权界：f 与 δ_M = x^{2M+1}/(2M+1)! 相乘的权重不超过
   (1+pwi f 0 c)·c^{2M+1}/(2M+1)!（权因子取严格正承载形）。 *)
Lemma lw0_pitB_conv_pair_deltamul_weight : forall (F : QPoly) (M : nat) (c : Q),
  QleT' 0 c ->
  QleT' (lw0_pitB_conv_pwi
          (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                         (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M)) (cons 1%Q nil)))) 0 c)
        ((1 + lw0_pitB_conv_pwi F 0 c)
         * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q).
Proof.
  intros F M c Hc0.
  assert (H01 : Qlt 0 1%Q) by (apply QltT_to_Qlt; unfold QltT; reflexivity).
  assert (Hs0 : QleT' 0 (1 / q_fact (Datatypes.S (2 * M)))).
  { apply Qle_to_QleT'. apply Qmult_le_0_compat.
    - exact (Qlt_le_weak 0%Q 1%Q H01).
    - apply Qinv_le_0_compat.
      apply (Qle_trans 0%Q 1%Q (q_fact (Datatypes.S (2 * M)))).
      + exact (Qlt_le_weak 0%Q 1%Q H01).
      + exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one (Datatypes.S (2 * M)))). }
  apply (qleT'_trans
          (lw0_pitB_conv_pwi
            (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                           (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M)) (cons 1%Q nil)))) 0 c)
          (lw0_pitB_conv_pwi F 0 c
           * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)
          ((1 + lw0_pitB_conv_pwi F 0 c)
           * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
  - apply (qleT'_trans
            (lw0_pitB_conv_pwi
              (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                             (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M)) (cons 1%Q nil)))) 0 c)
            (Qabs (1 / q_fact (Datatypes.S (2 * M)))
             * (q_pow (Qabs c) (Datatypes.S (2 * M)) * lw0_pitB_conv_pwi F 0 c))
            (lw0_pitB_conv_pwi F 0 c
             * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
    + exact (lw0_pitB_conv_pwi_mul_shift_domin F (1 / q_fact (Datatypes.S (2 * M)))
               (Datatypes.S (2 * M)) 0 c).
    + apply qeq_leT'.
      rewrite (lw0_Qabs_pos_eq (1 / q_fact (Datatypes.S (2 * M))) Hs0).
      rewrite (lw0_Qabs_pos_eq c Hc0).
      unfold Qdiv. ring.
  - apply (qleT'_trans
            (lw0_pitB_conv_pwi F 0 c
             * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)
            ((q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
             * lw0_pitB_conv_pwi F 0 c)
            ((1 + lw0_pitB_conv_pwi F 0 c)
             * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
    + apply qeq_leT'. apply Qmult_comm.
    + apply (qleT'_trans
              ((q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
               * lw0_pitB_conv_pwi F 0 c)
              ((q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
               * (1 + lw0_pitB_conv_pwi F 0 c))
              ((1 + lw0_pitB_conv_pwi F 0 c)
               * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
      * apply (lw0_pitB_conv_mult_le_l
                 (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
                 (lw0_pitB_conv_pwi F 0 c) (1 + lw0_pitB_conv_pwi F 0 c)).
        -- apply Qle_to_QleT'.
           assert (Hle : Qle (lw0_pitB_conv_pwi F 0 c)
                             (lw0_pitB_conv_pwi F 0 c + 1%Q)).
           { apply (Qle_trans (lw0_pitB_conv_pwi F 0 c)
                              (lw0_pitB_conv_pwi F 0 c + 0%Q)
                              (lw0_pitB_conv_pwi F 0 c + 1%Q)).
             - rewrite Qplus_0_r. apply Qle_refl.
             - apply Qplus_le_compat.
               + apply Qle_refl.
               + exact (Qlt_le_weak 0%Q 1%Q H01). }
           rewrite (Qplus_comm 1%Q (lw0_pitB_conv_pwi F 0 c)). exact Hle.
        -- apply Qle_to_QleT'. apply Qmult_le_0_compat.
           ++ exact (q_pow_nonneg c (Datatypes.S (2 * M)) (QleT'_to_Qle _ _ Hc0)).
           ++ apply Qinv_le_0_compat.
              apply (Qle_trans 0%Q 1%Q (q_fact (Datatypes.S (2 * M)))).
              ** exact (Qlt_le_weak 0%Q 1%Q H01).
              ** exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one (Datatypes.S (2 * M)))).
      * apply qeq_leT'. apply Qmult_comm.
Qed.

(* ---- 贴装闭包·vanish_ex 1 件（_tlw380 跑匣 b85fb0b7 源剥壳） ---- *)

(* 规范化尾项消逝例示：尾项族 F·x^{2M+1}/(2M+1)! 自某项起任意小。 *)
Lemma lw0_pitB_conv_pair_vanish_deltam : forall (F : QPoly) (eps q : Q),
  QltT 0 eps ->
  sigT (fun M0 : nat => forall M : nat, (M0 <= M)%nat ->
    QltT (Qabs (Qabs q * qpoly_eval (lw0_qp_ai
             (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                            (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M))
                               (cons 1%Q nil)))) 0)
             (Qabs q))) eps).
Proof.
  intros F eps q Heps.
  apply (lw0_pitB_conv_pair_vanish
           (fun M : nat => qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                          (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M))
                             (cons 1%Q nil))))
           (1 + lw0_pitB_conv_pwi F 0 (Qabs q)) (Qabs q) eps).
  - apply Qle_to_QleT'. apply Qabs_nonneg.
  - exact Heps.
  - apply Qlt_to_QltT.
    apply (Qlt_le_trans 0%Q 1%Q (1 + lw0_pitB_conv_pwi F 0 (Qabs q))).
    + apply QltT_to_Qlt. unfold QltT. reflexivity.
    + apply (Qle_trans 1%Q (1 + 0%Q) (1 + lw0_pitB_conv_pwi F 0 (Qabs q))).
      * rewrite Qplus_0_r. apply Qle_refl.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact (QleT'_to_Qle _ _ (lw0_pitB_conv_pwi_nonneg F 0 (Qabs q))).
  - intro M. exact (lw0_pitB_conv_pair_deltamul_weight F M (Qabs q)
             (Qle_to_QleT' 0 (Qabs q) (Qabs_nonneg q))).
Qed.

(* ---- 贴装闭包·fplus 15 件（语句面载体 lw0_qpoly_eq 依 §五.3 逐字同构结论统一改写为 lw0_qpoly_eqT——draft 块 L67 载体定义为唯一载体，fplus 侧同名 Definition 已删） ---- *)

(* ---- q_fact 非零件（Qmult_integral_l 消去保航） ---- *)
Lemma lw385_q_fact_neq : forall j : nat, ~ q_fact j == 0%Q.
Proof.
  intro j. intro Hq.
  apply (Qlt_not_eq 0%Q (q_fact j) (q_fact_pos j)).
  apply Qeq_sym. exact Hq.
Qed.

(* ---- Qeq 右加法同余（原子级 rewrite，规避复合和改写撞 Z 展开形） ---- *)
Lemma lw385_Qplus_eq_compat_r : forall x y z : Q, x == y -> x + z == y + z.
Proof. intros x y z H. rewrite H. reflexivity. Qed.

Lemma lw385_Qplus_eq_compat2 : forall a b c d : Q,
  a == b -> a + c + d == b + c + d.
Proof. intros a b c d H. rewrite H. reflexivity. Qed.

(* ---- bool 等词的 Id 桥（主件 die 位 Prop 等式入 Set 层） ---- *)
Lemma lw385_eq_Id : forall b : bool, b = true -> Id b true.
Proof. intros b H. destruct H. apply id_refl. Qed.

Lemma lw385_andb_Id : forall b1 b2 : bool,
  Id (andb b1 b2) true -> And (Id b1 true) (Id b2 true).
Proof.
  intros b1 b2 H. destruct b1; destruct b2.
  - exact (id_refl, id_refl).
  - inversion H.
  - inversion H.
  - inversion H.
Qed.

(* ---- die 预算的表长兑现（die p n = true -> length p <= n） ---- *)
Lemma lw385_die_length : forall (p : qpoly) (n : nat),
  Id (lw0_die p n) true -> (length p <= n)%nat.
Proof.
  induction p as [|a p IH]; intros n Hd.
  - simpl. apply Nat.le_0_l.
  - destruct n as [|n'].
    + inversion Hd.
    + assert (Hs := lw385_andb_Id _ _ Hd).
      destruct Hs as [H1 H2].
      assert (Hl1 := IH (Datatypes.S n') H1).
      assert (Hl2 := IH n' H2).
      simpl. lia.
Qed.

(* ---- 表长界外的系数零 ---- *)
Lemma lw385_coef_len_zero : forall (p : qpoly) (k : nat),
  (length p <= k)%nat -> lw0_coef k p == 0%Q.
Proof.
  induction p as [|a p IH]; intros k Hk.
  - reflexivity.
  - destruct k as [|k'].
    + simpl in Hk. lia.
    + simpl in Hk. simpl. apply (IH k'). lia.
Qed.

(* ---- die 预算的系数级兑现：n 次迭代求导后系数逐位零化 ---- *)
Lemma lw385_die_coef_zero : forall (p : qpoly) (n j : nat),
  Id (lw0_die p n) true -> lw0_coef j (qpoly_deriv_iter n p) == 0%Q.
Proof.
  intros p n j Hd.
  assert (Hlen := lw385_die_length p n Hd).
  assert (Hc0 : lw0_coef (j + n) p == 0%Q)
    by (apply lw385_coef_len_zero; lia).
  pose proof (lw0_coef_iter_mul n j p) as H1.
  rewrite Hc0 in H1. rewrite Qmult_0_r in H1.
  rewrite (Qmult_comm (lw0_coef j (qpoly_deriv_iter n p)) (q_fact j)) in H1.
  apply (Qmult_integral_l _ _ (lw385_q_fact_neq j) H1).
Qed.

(* ---- 核心链：F_aux 二阶导望远镜（系数级逐位；尾项显式承载） ----
   数学形：D²(F_aux J) + F_aux J == c·f + c·(−1)^J·D^{2(S J)} f，
   与主件 eval 级 lw0_F_aux_plus_deriv2（@4349）逐项同构。 *)
Lemma lw385_F_aux_plus_deriv2_coef : forall (J : nat) (f : qpoly) (c : Q),
  lw0_qpoly_eqT
    (qpoly_add (qpoly_deriv_iter 2 (lw0_F_aux f c J)) (lw0_F_aux f c J))
    (qpoly_add (qpoly_scalar c f)
       (qpoly_scalar (c * lw0_alt J)%Q
          (qpoly_deriv_iter (2 * Datatypes.S J) f))).
Proof.
  induction J as [|J' IH]; intros f c j; apply qeq_imp_qeqT.
  - change (lw0_F_aux f c 0%nat) with (qpoly_scalar c f).
    change (2 * Datatypes.S 0)%nat with 2%nat.
    change (lw0_alt 0%nat) with 1%Q.
    rewrite !lw0_coef_add.
    rewrite (lw0_coef_iter_scalar 2 j c f).
    rewrite !lw0_coef_scalar.
    ring.
  - change (lw0_F_aux f c (Datatypes.S J'))
      with (qpoly_add (lw0_F_aux f c J')
              (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                 (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    rewrite !lw0_coef_add.
    rewrite (lw0_coef_iter_add 2 j (lw0_F_aux f c J')
               (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                  (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    rewrite !lw0_coef_scalar.
    rewrite (lw0_coef_iter_scalar 2 j (c * lw0_alt (Datatypes.S J'))%Q
               (qpoly_deriv_iter (2 * Datatypes.S J') f)).
    rewrite <- (lw0_qp_deriv_iter_plus 2 (2 * Datatypes.S J') f).
    replace (2 + 2 * Datatypes.S J')%nat
      with (2 * Datatypes.S (Datatypes.S J'))%nat by lia.
    assert (IHj := qeqT_imp_qeq _ _ (IH f c j)).
    transitivity (lw0_coef j (qpoly_deriv_iter 2 (lw0_F_aux f c J'))
                  + lw0_coef j (lw0_F_aux f c J')
                  + (c * lw0_alt (Datatypes.S J'))%Q
                    * lw0_coef j (qpoly_deriv_iter (2 * Datatypes.S J') f)
                  + (c * lw0_alt (Datatypes.S J'))%Q
                    * lw0_coef j (qpoly_deriv_iter
                         (2 * Datatypes.S (Datatypes.S J')) f)).
    + rewrite (lw0_alt_opp J'). ring.
    + transitivity (c * lw0_coef j f
                    + (c * lw0_alt J')%Q
                      * lw0_coef j (qpoly_deriv_iter (2 * Datatypes.S J') f)
                    + (c * lw0_alt (Datatypes.S J'))%Q
                      * lw0_coef j (qpoly_deriv_iter (2 * Datatypes.S J') f)
                    + (c * lw0_alt (Datatypes.S J'))%Q
                      * lw0_coef j (qpoly_deriv_iter
                           (2 * Datatypes.S (Datatypes.S J')) f)).
      * rewrite !lw0_coef_add in IHj. rewrite !lw0_coef_scalar in IHj.
        apply (lw385_Qplus_eq_compat2 _ _ _ _ IHj).
      * rewrite (lw0_alt_opp J'). ring.
Qed.

(* ---- 槽①主件：F + F″ == f（poly 级；die 前提 Set 层 Id 承载） ---- *)
Lemma lw385_F_plus_deriv2_coef : forall (f : qpoly) (J : nat),
  Id (lw0_die f (2 * Datatypes.S J)) true ->
  lw0_qpoly_eqT (qpoly_add (qpoly_deriv_iter 2 (lw0_F f J)) (lw0_F f J)) f.
Proof.
  intros f J Hd j. apply qeq_imp_qeqT.
  unfold lw0_F.
  assert (Haux := qeqT_imp_qeq _ _
    (lw385_F_aux_plus_deriv2_coef J f 1%Q j)).
  rewrite !lw0_coef_add in Haux.
  rewrite (lw0_coef_scalar j 1%Q f) in Haux.
  rewrite (lw0_coef_scalar j (1 * lw0_alt J)%Q
             (qpoly_deriv_iter (2 * Datatypes.S J) f)) in Haux.
  rewrite !lw0_coef_add.
  rewrite Haux.
  assert (Hz := lw385_die_coef_zero f (2 * Datatypes.S J) j Hd).
  rewrite Hz. ring.
Qed.

(* ---- niven 实例（die 位经 lw0_niven_f_die ＝ eq→Id 桥直供） ---- *)
Lemma lw385_F_plus_deriv2_coef_niven : forall (q b : Q) (n : nat),
  lw0_qpoly_eqT
    (qpoly_add (qpoly_deriv_iter 2 (lw0_F (lw0_niven_f q b n) n))
               (lw0_F (lw0_niven_f q b n) n))
    (lw0_niven_f q b n).
Proof.
  intros q b n. apply lw385_F_plus_deriv2_coef.
  apply lw385_eq_Id. apply lw0_niven_f_die.
Qed.

(* ---- ai·mul 零系数消去（congr 的缺配长支） ---- *)
Lemma lw385_ai_mul_zero : forall (g p : qpoly),
  (forall j : nat, lw0_coef j p == 0%Q) ->
  forall (k : nat) (x : Q),
    qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) x == 0%Q.
Proof.
  intros g p. induction p as [|a p IH]; intros Hz k x.
  - reflexivity.
  - assert (Ha : a == 0%Q) by (apply (Hz 0%nat)).
    change (qpoly_mul (cons a p) g)
      with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g)
               (cons 0%Q (qpoly_mul p g)) k x).
    rewrite (lw0_qp_ai_scalar a g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k x).
    rewrite Ha.
    rewrite (IH (fun j => Hz (Datatypes.S j)) (Datatypes.S k) x).
    ring.
Qed.

(* ---- eqT 的 ai·mul 逐点同值（pair 岸 congr 的内核步） ---- *)
Lemma lw385_ai_mul_congr_eval : forall (g p f : qpoly),
  lw0_qpoly_eqT p f ->
  forall (k : nat) (x : Q),
    qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) x
    == qpoly_eval (lw0_qp_ai (qpoly_mul f g) k) x.
Proof.
  intros g p. induction p as [|a p IH]; intros f Hp k x.
  - destruct f as [|b f].
    + apply Qeq_refl.
    + assert (Hz : forall j : nat, lw0_coef j (cons b f) == 0%Q)
        by (intro j; apply Qeq_sym; apply qeqT_imp_qeq; apply Hp).
      transitivity 0%Q.
      * reflexivity.
      * symmetry. exact (lw385_ai_mul_zero g (cons b f) Hz k x).
  - destruct f as [|b f].
    + assert (Hz : forall j : nat, lw0_coef j (cons a p) == 0%Q)
        by (intro j; apply qeqT_imp_qeq; apply Hp).
      transitivity 0%Q.
      * exact (lw385_ai_mul_zero g (cons a p) Hz k x).
      * reflexivity.
    + assert (Hab : a == b%Q) by (apply qeqT_imp_qeq; apply (Hp 0%nat)).
      assert (Htail : lw0_qpoly_eqT p f)
        by (intro j; exact (Hp (Datatypes.S j))).
      change (qpoly_mul (cons a p) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
      change (qpoly_mul (cons b f) g)
        with (qpoly_add (qpoly_scalar b g) (cons 0%Q (qpoly_mul f g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul p g)) k x).
      rewrite (lw0_qp_ai_add (qpoly_scalar b g)
                 (cons 0%Q (qpoly_mul f g)) k x).
      rewrite (lw0_qp_ai_scalar a g k x).
      rewrite (lw0_qp_ai_scalar b g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g) k x).
      rewrite Hab.
      rewrite (IH f Htail (Datatypes.S k) x).
      reflexivity.
Qed.

(* ---- pair 第一变元的系数级 congr ---- *)
Lemma lw385_pair_congr_l : forall (p f g : qpoly) (x : Q),
  lw0_qpoly_eqT p f -> QeqT (lw0_qp_pair p g x) (lw0_qp_pair f g x).
Proof.
  intros p f g x Hp. apply qeq_imp_qeqT.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0%Q (lw0_qp_ai (qpoly_mul p g) 0)) x)
    with (0 + x * qpoly_eval (lw0_qp_ai (qpoly_mul p g) 0) x)%Q.
  change (qpoly_eval (cons 0%Q (lw0_qp_ai (qpoly_mul f g) 0)) x)
    with (0 + x * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) x)%Q.
  rewrite (lw385_ai_mul_congr_eval g p f Hp 0%nat x).
  reflexivity.
Qed.

(* ---- 槽①pair 岸兑付形（380 骨架 GAPASUME① 前提位逐字可消去） ---- *)
Lemma lw385_pair_F_plus_deriv2 : forall (f g : qpoly) (J : nat) (x : Q),
  Id (lw0_die f (2 * Datatypes.S J)) true ->
  QeqT (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F f J)) g x
        + lw0_qp_pair (lw0_F f J) g x)
       (lw0_qp_pair f g x).
Proof.
  intros f g J x Hd. apply qeq_imp_qeqT.
  transitivity (lw0_qp_pair (qpoly_add (qpoly_deriv_iter 2 (lw0_F f J))
                              (lw0_F f J)) g x).
  - exact (Qeq_sym _ _ (lw0_qp_pair_add_l (qpoly_deriv_iter 2 (lw0_F f J))
               (lw0_F f J) g x)).
  - exact (qeqT_imp_qeq _ _
             (lw385_pair_congr_l (qpoly_add (qpoly_deriv_iter 2 (lw0_F f J))
                                  (lw0_F f J)) f g x
                (lw385_F_plus_deriv2_coef f J Hd))).
Qed.

(* ---- 槽①turnkey：niven 基座实例（＝骨架 HF2 面逐字，die 位内消） ---- *)
Lemma lw385_pair_F_plus_deriv2_niven :
  forall (q b : Q) (n m : nat) (x : Q),
  QeqT (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_niven_f q b n) n))
                    (lw0_sin_qp m) x
        + lw0_qp_pair (lw0_F (lw0_niven_f q b n) n) (lw0_sin_qp m) x)
       (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) x).
Proof.
  intros q b n m x. apply (lw385_pair_F_plus_deriv2).
  apply lw385_eq_Id. apply lw0_niven_f_die.
Qed.

(* ---- 贴装闭包·sign_sym 12 件（_tlw392 跑匣 c767fce8 源剥壳；零载体零重命名） ---- *)

(* ---- 系数符号交替翻转型 flip（b = true：t ↦ −t 替身） ---- *)
Fixpoint lw385_flip_aux (b : bool) (p : qpoly) : qpoly :=
  match p with
  | nil => nil
  | cons a p' =>
      match b with
      | true => cons a (lw385_flip_aux false p')
      | false => cons (- a)%Q (lw385_flip_aux true p')
      end
  end.

(* ---- 偶/奇次幂的负底规约 ---- *)
Lemma lw385_q_pow_neg_even : forall (n : nat) (x : Q),
  q_pow (- x)%Q (2 * n) == q_pow x (2 * n).
Proof.
  induction n as [|n IH]; intros x.
  - reflexivity.
  - replace (2 * Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    rewrite (q_pow_succ (- x)%Q (Datatypes.S (2 * n))).
    rewrite (q_pow_succ (- x)%Q (2 * n)).
    rewrite IH.
    rewrite (q_pow_succ x (Datatypes.S (2 * n))).
    rewrite (q_pow_succ x (2 * n)).
    ring.
Qed.

Lemma lw385_q_pow_neg_odd : forall (n : nat) (x : Q),
  q_pow (- x)%Q (Datatypes.S (2 * n)) == (- q_pow x (Datatypes.S (2 * n)))%Q.
Proof.
  intros n x.
  rewrite (q_pow_succ (- x)%Q (2 * n)).
  rewrite (lw385_q_pow_neg_even n x).
  rewrite (q_pow_succ x (2 * n)).
  ring.
Qed.

(* ---- 零前缀移位的积分片（ai 零前缀 n 阶抬升） ---- *)
Lemma lw385_ai_zero_shift : forall (n : nat) (p : qpoly) (k : nat) (x : Q),
  qpoly_eval (lw0_qp_ai (lw0_pitB_conv_zero_shift n p) k) x
  == q_pow x n * qpoly_eval (lw0_qp_ai p (k + n)%nat) x.
Proof.
  induction n as [|n IH]; intros p k x.
  - change (lw0_pitB_conv_zero_shift 0 p) with p.
    change (q_pow x 0) with 1%Q.
    rewrite Nat.add_0_r. rewrite Qmult_1_l. reflexivity.
  - change (lw0_pitB_conv_zero_shift (Datatypes.S n) p)
      with (cons 0%Q (lw0_pitB_conv_zero_shift n p)).
    rewrite (lw0_qp_ai_zero_head_eval (lw0_pitB_conv_zero_shift n p) k x).
    rewrite (IH p (Datatypes.S k) x).
    replace (Datatypes.S k + n)%nat with (k + Datatypes.S n)%nat by lia.
    rewrite (q_pow_succ x n).
    ring.
Qed.

(* ---- 奇单项式证书：δ_j 型 t^{2j+1} 的 ai 族奇性 ---- *)
Lemma lw385_ai_delta_odd : forall (j : nat) (c : Q) (k : nat) (x : Q),
  qpoly_eval (lw0_qp_ai (qpoly_scalar c
    (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))) k)
    (- x)%Q
  == (- qpoly_eval (lw0_qp_ai (qpoly_scalar c
        (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))) k)
        x)%Q.
Proof.
  intros j c k x.
  rewrite (lw0_qp_ai_scalar c
             (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))
             k (- x)%Q).
  rewrite (lw0_qp_ai_scalar c
             (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))
             k x).
  rewrite (lw385_ai_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil) k (- x)%Q).
  rewrite (lw385_ai_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil) k x).
  rewrite (lw385_q_pow_neg_odd j x).
  rewrite (lw0_qp_ai_cons_eval 1%Q nil
             (k + Datatypes.S (2 * j))%nat (- x)%Q).
  rewrite (lw0_qp_ai_cons_eval 1%Q nil
             (k + Datatypes.S (2 * j))%nat x).
  cbn [lw0_qp_ai qpoly_eval].
  ring.
Qed.

(* ---- 核心链：mul·ai 的翻岸不变量（bool 交替消 s² 记录） ----
   数学形：[ai(p·g, k)](−x) == ±[ai(flip p·g, k)](x)，g 的 ai 族
   奇性前提下逐级 ring 闭合（flip 的系数 (−1)^k 交替由 b 翻转承载）。 *)
Lemma lw385_ai_mul_flip_aux : forall (p : qpoly) (b : bool) (g : qpoly)
                                     (k : nat) (x : Q),
  (forall (j : nat) (y : Q),
     QeqT (qpoly_eval (lw0_qp_ai g j) (- y)%Q)
          (- qpoly_eval (lw0_qp_ai g j) y)%Q) ->
  qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) (- x)%Q
  == (if b then 1 else (-1))%Q
     * qpoly_eval (lw0_qp_ai
          (qpoly_mul (lw385_flip_aux (negb b) p) g) k) x.
Proof.
  induction p as [|a p IH]; intros b g k x Hodd.
  - cbn [qpoly_mul lw385_flip_aux lw0_qp_ai qpoly_eval]. ring.
  - destruct b.
    + change (qpoly_mul (cons a p) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
      change (lw385_flip_aux (negb true) (cons a p))
        with (cons (- a)%Q (lw385_flip_aux true p)).
      change (qpoly_mul (cons (- a)%Q (lw385_flip_aux true p)) g)
        with (qpoly_add (qpoly_scalar (- a)%Q g)
               (cons 0%Q (qpoly_mul (lw385_flip_aux true p) g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul p g)) k (- x)%Q).
      rewrite (lw0_qp_ai_add (qpoly_scalar (- a)%Q g)
                 (cons 0%Q (qpoly_mul (lw385_flip_aux true p) g)) k x).
      rewrite (lw0_qp_ai_scalar a g k (- x)%Q).
      rewrite (lw0_qp_ai_scalar (- a)%Q g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k (- x)%Q).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (lw385_flip_aux true p) g)
                 k x).
      rewrite (qeqT_imp_qeq _ _ (Hodd k x)).
      rewrite (IH false g (Datatypes.S k) x Hodd).
      change (negb false) with true.
      change (if false then 1 else (-1))%Q with (-1)%Q.
      change (if true then 1 else (-1))%Q with 1%Q.
      ring.
    + change (qpoly_mul (cons a p) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
      change (lw385_flip_aux (negb false) (cons a p))
        with (cons a (lw385_flip_aux false p)).
      change (qpoly_mul (cons a (lw385_flip_aux false p)) g)
        with (qpoly_add (qpoly_scalar a g)
               (cons 0%Q (qpoly_mul (lw385_flip_aux false p) g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul p g)) k (- x)%Q).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul (lw385_flip_aux false p) g)) k x).
      rewrite (lw0_qp_ai_scalar a g k (- x)%Q).
      rewrite (lw0_qp_ai_scalar a g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k (- x)%Q).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (lw385_flip_aux false p) g)
                 k x).
      rewrite (qeqT_imp_qeq _ _ (Hodd k x)).
      rewrite (IH true g (Datatypes.S k) x Hodd).
      change (negb true) with false.
      change (if true then 1 else (-1))%Q with 1%Q.
      change (if false then 1 else (-1))%Q with (-1)%Q.
      ring.
Qed.

Lemma lw385_ai_mul_flip : forall (p g : qpoly) (k : nat) (x : Q),
  (forall (j : nat) (y : Q),
     QeqT (qpoly_eval (lw0_qp_ai g j) (- y)%Q)
          (- qpoly_eval (lw0_qp_ai g j) y)%Q) ->
  qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) (- x)%Q
  == qpoly_eval (lw0_qp_ai (qpoly_mul (lw385_flip_aux false p) g) k) x.
Proof.
  intros p g k x Hodd.
  apply Qeq_trans with
    (1%Q * qpoly_eval (lw0_qp_ai (qpoly_mul (lw385_flip_aux (negb true) p) g) k) x)%Q.
  - exact (lw385_ai_mul_flip_aux p true g k x Hodd).
  - apply Qmult_1_l.
Qed.

(* ---- pair 的 q 槽同值传导（Qeq 改写无 Proper 实例，Horner 结构直证） ---- *)
Lemma lw385_qp_eval_q_wd : forall (E : qpoly) (q q' : Q),
  q == q' -> qpoly_eval E q == qpoly_eval E q'.
Proof.
  induction E as [|a E IH]; intros q q' Hq.
  - reflexivity.
  - change (qpoly_eval (cons a E) q) with (a + q * qpoly_eval E q)%Q.
    change (qpoly_eval (cons a E) q') with (a + q' * qpoly_eval E q')%Q.
    rewrite (IH q q' Hq). rewrite Hq. reflexivity.
Qed.

Lemma lw385_pair_q_wd : forall (p g : qpoly) (q q' : Q),
  q == q' -> QeqT (lw0_qp_pair p g q) (lw0_qp_pair p g q').
Proof.
  intros p g q q' Hq. apply qeq_imp_qeqT.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  exact (lw385_qp_eval_q_wd _ _ _ Hq).
Qed.

(* ---- 槽④(α) 正岸支：0 ≤ x 时 pair 在 x 与 |x| 同值 ---- *)
Lemma lw385_pair_abs_shore : forall (p g : qpoly) (x : Q),
  QleT' 0 x -> QeqT (lw0_qp_pair p g x) (lw0_qp_pair p g (Qabs x)).
Proof.
  intros p g x Hx.
  apply (lw385_pair_q_wd p g x (Qabs x)).
  apply Qeq_sym. apply Qabs_pos. apply QleT'_to_Qle. exact Hx.
Qed.

(* ---- 槽④(β) 翻岸支：pair p g (−x) == −pair(flip p, g)(x) ---- *)
Lemma lw385_pair_flip_shore : forall (p g : qpoly) (x : Q),
  (forall (j : nat) (y : Q),
     QeqT (qpoly_eval (lw0_qp_ai g j) (- y)%Q)
          (- qpoly_eval (lw0_qp_ai g j) y)%Q) ->
  QeqT (lw0_qp_pair p g (- x)%Q)
       (- lw0_qp_pair (lw385_flip_aux false p) g x)%Q.
Proof.
  intros p g x Hodd. apply qeq_imp_qeqT.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0%Q (lw0_qp_ai (qpoly_mul p g) 0)) (- x)%Q)
    with (0 + (- x)%Q * qpoly_eval (lw0_qp_ai (qpoly_mul p g) 0) (- x)%Q)%Q.
  change (qpoly_eval
            (cons 0%Q (lw0_qp_ai (qpoly_mul (lw385_flip_aux false p) g) 0)) x)
    with (0 + x * qpoly_eval
            (lw0_qp_ai (qpoly_mul (lw385_flip_aux false p) g) 0) x)%Q.
  rewrite (lw385_ai_mul_flip p g 0%nat x Hodd).
  ring.
Qed.

(* ---- 槽④turnkey：δ_j 型奇单项式 g 的翻岸支（落装例示 g := δ_j） ---- *)
Lemma lw385_pair_flip_shore_mono : forall (j : nat) (c : Q) (p : qpoly) (x : Q),
  QeqT (lw0_qp_pair p (qpoly_scalar c
          (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil)))
          (- x)%Q)
       (- lw0_qp_pair (lw385_flip_aux false p) (qpoly_scalar c
          (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))) x)%Q.
Proof.
  intros j c p x. apply lw385_pair_flip_shore.
  intros j0 y. apply qeq_imp_qeqT. apply lw385_ai_delta_odd.
Qed.


(* ---- 全装配终形（四槽全消：②③供件在本块直供；①HF2 turnkey 入槽；
   ④α/β 双支实例化（vanish 机 G:=F／G:=flip F 双例示）；语句面零前提零 Prop。
   结论面＝@11076 Hpair 参数位逐字（基座 f 经 lw0_pitB_pair_conv_f δ 承载）。） ---- *)

Lemma lw0_pitB_pair_conv : forall (q : Q) (n : nat),
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) q
                - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
                - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
                  * qpoly_eval (lw0_sin_qp m) q
                + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
                  * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps).
Proof.
  intros q n eps Heps.
  assert (HF2 := lw385_pair_F_plus_deriv2_niven q (Zpos (Qden q) # 1)%Q n).
  assert (Hcore := lw0_pitB_pair_conv_core q n).
  assert (Hsig2 := lw0_pitB_pair_conv_sig2 q n).
  assert (Hsinc := lw0_pitB_pair_conv_sinc q n).
  destruct (Qle_bool 0 q) eqn:Hqb.
  - (* 槽④ α 支（q ≥ 0）：vanish 机例示 G := F；Hsym 腿换 lw385_pair_abs_shore。 *)
    destruct (lw0_pitB_conv_pair_vanish_deltam
                (lw0_F (lw0_pitB_pair_conv_f q n) n) eps q Heps) as [M0 HM0].
    exists (Datatypes.S M0). intros m Hm.
    destruct m as [|j].
    + exfalso. assert (Hle := NatLe_drop _ _ Hm). lia.
    + assert (Hj : (M0 <= Datatypes.S j)%nat).
      { assert (Hle := NatLe_drop _ _ Hm). lia. }
      assert (Hchain :
        lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
        - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
        - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
          * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
        + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
          * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q
        == (q_pow (-1) (Datatypes.S j))%Q
           * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (lw0_pitB_pair_conv_delta (Datatypes.S j)) q).
      { rewrite (Hcore (Datatypes.S j) (HF2 (Datatypes.S j))).
        assert (HSneg : lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                        == (- lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q).
        { transitivity (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                          + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q
                          - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q.
          - ring.
          - rewrite (qeqT_imp_qeq _ _ (Hsig2 j q)). ring. }
        rewrite HSneg.
        rewrite <- (qeqT_imp_qeq _ _ (Hsinc j q)).
        ring. }
      assert (Habs : QeqT
        (Qabs (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
              - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
              - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
                * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
              + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
                * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q))
        (Qabs ((q_pow (-1) (Datatypes.S j))%Q
               * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                   (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))).
      { apply qeq_imp_qeqT. apply lw0_pitB_pair_conv_qabs_wd. exact Hchain. }
      assert (Hfin :
        QeqT (Qabs ((q_pow (-1) (Datatypes.S j))%Q
                      * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))
             (Qabs (Qabs q * qpoly_eval (lw0_qp_ai
                         (qpoly_mul (lw0_F (lw0_pitB_pair_conv_f q n) n)
                            (lw0_pitB_pair_conv_delta (Datatypes.S j))) 0)
                     (Qabs q)))).
      { apply qeq_imp_qeqT.
        transitivity (Qabs (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_pitB_pair_conv_delta (Datatypes.S j)) q)).
        - rewrite Qabs_Qmult.
          rewrite lw0_pitB_pair_conv_qabs_sign1. ring.
        - apply lw0_pitB_pair_conv_qabs_wd.
          transitivity (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (lw0_pitB_pair_conv_delta (Datatypes.S j)) (Qabs q)).
          + exact (qeqT_imp_qeq _ _
                     (lw385_pair_abs_shore (lw0_F (lw0_pitB_pair_conv_f q n) n)
                        (lw0_pitB_pair_conv_delta (Datatypes.S j)) q
                        (Qle_to_QleT' 0 q (Qle_bool_imp_le 0 q Hqb)))).
          + unfold lw0_qp_pair, lw0_qp_antideriv. cbn [qpoly_eval]. ring. }
      exact (lw0_pitB_conv_qeqL_ltT _ _ _ Habs
               (lw0_pitB_conv_qeqL_ltT _ _ _ Hfin (HM0 (Datatypes.S j) Hj))).
  - (* 槽④ β 支（q < 0）：vanish 机第二例示 G := flip F；翻岸支搬岸＋Qabs_opp 吞号。 *)
    assert (Hnle : ~ (0 <= q)%Q).
    { intros Hc. rewrite (proj2 (Qle_bool_iff 0 q) Hc) in Hqb. discriminate Hqb. }
    assert (Hq_u : q == (- Qabs q)%Q).
    { apply (Qabs_case q (fun z => (q == - z)%Q)).
      - intros Hc. rewrite (proj2 (Qle_bool_iff 0 q) Hc) in Hqb. discriminate Hqb.
      - intros Hq0. ring. }
    destruct (lw0_pitB_conv_pair_vanish_deltam
                (lw385_flip_aux false (lw0_F (lw0_pitB_pair_conv_f q n) n)) eps q Heps)
      as [M0 HM0].
    exists (Datatypes.S M0). intros m Hm.
    destruct m as [|j].
    + exfalso. assert (Hle := NatLe_drop _ _ Hm). lia.
    + assert (Hj : (M0 <= Datatypes.S j)%nat).
      { assert (Hle := NatLe_drop _ _ Hm). lia. }
      assert (Hchain :
        lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
        - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
        - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
          * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
        + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
          * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q
        == (q_pow (-1) (Datatypes.S j))%Q
           * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (lw0_pitB_pair_conv_delta (Datatypes.S j)) q).
      { rewrite (Hcore (Datatypes.S j) (HF2 (Datatypes.S j))).
        assert (HSneg : lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                        == (- lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q).
        { transitivity (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                          + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q
                          - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q.
          - ring.
          - rewrite (qeqT_imp_qeq _ _ (Hsig2 j q)). ring. }
        rewrite HSneg.
        rewrite <- (qeqT_imp_qeq _ _ (Hsinc j q)).
        ring. }
      assert (Habs : QeqT
        (Qabs (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
              - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
              - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
                * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
              + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
                * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q))
        (Qabs ((q_pow (-1) (Datatypes.S j))%Q
               * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                   (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))).
      { apply qeq_imp_qeqT. apply lw0_pitB_pair_conv_qabs_wd. exact Hchain. }
      assert (Hfin :
        QeqT (Qabs ((q_pow (-1) (Datatypes.S j))%Q
                      * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))
             (Qabs (Qabs q * qpoly_eval (lw0_qp_ai
                         (qpoly_mul (lw385_flip_aux false
                                       (lw0_F (lw0_pitB_pair_conv_f q n) n))
                            (lw0_pitB_pair_conv_delta (Datatypes.S j))) 0)
                     (Qabs q)))).
      { apply qeq_imp_qeqT.
        transitivity (Qabs (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_pitB_pair_conv_delta (Datatypes.S j)) q)).
        - rewrite Qabs_Qmult.
          rewrite lw0_pitB_pair_conv_qabs_sign1. ring.
        - transitivity (Qabs (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                                (lw0_pitB_pair_conv_delta (Datatypes.S j))
                                (- Qabs q)%Q)).
          + apply lw0_pitB_pair_conv_qabs_wd.
            exact (qeqT_imp_qeq _ _
                     (lw385_pair_q_wd (lw0_F (lw0_pitB_pair_conv_f q n) n)
                        (lw0_pitB_pair_conv_delta (Datatypes.S j)) q
                        (- Qabs q)%Q Hq_u)).
          + transitivity (Qabs (- lw0_qp_pair (lw385_flip_aux false
                                    (lw0_F (lw0_pitB_pair_conv_f q n) n))
                                (lw0_pitB_pair_conv_delta (Datatypes.S j))
                                (Qabs q))%Q).
            * apply lw0_pitB_pair_conv_qabs_wd.
              exact (qeqT_imp_qeq _ _
                       (lw385_pair_flip_shore_mono (Datatypes.S j)
                          (1 / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q
                          (lw0_F (lw0_pitB_pair_conv_f q n) n) (Qabs q))).
            * change (lw0_pitB_pair_conv_delta (Datatypes.S j))
                with (qpoly_scalar (1 / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q
                        (lw0_pitB_conv_zero_shift (Datatypes.S (2 * Datatypes.S j))
                           (cons 1%Q nil))).
              rewrite Qabs_opp.
              apply lw0_pitB_pair_conv_qabs_wd.
              unfold lw0_qp_pair, lw0_qp_antideriv. cbn [qpoly_eval]. ring. }
      exact (lw0_pitB_conv_qeqL_ltT _ _ _ Habs
               (lw0_pitB_conv_qeqL_ltT _ _ _ Hfin (HM0 (Datatypes.S j) Hj))).
Qed.

(* ---- §7.3 turnkey（389 交接处方：rtail_vanish_hpair 使用直证——终形三行照抄） ---- *)

Lemma lw0_pitB_pair_conv_turnkey : forall (q : Q) (n : nat),
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n eps Heps.
  exact (lw0_pitB_pair_rtail_vanish_hpair q n (lw0_pitB_pair_conv q n) eps Heps).
Qed.

(* ---- 随块 PA 锚（②Hpair 落装块；Δ=4） ---- *)
Print Assumptions lw0_pitB_pair_conv_sig2.
Print Assumptions lw0_pitB_pair_conv_sinc.
Print Assumptions lw0_pitB_pair_conv.
Print Assumptions lw0_pitB_pair_conv_turnkey.

Lemma lw0_pitB_pair_rtail_vanish : forall (q : Q) (n : nat), forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n eps Heps.
  exact (lw0_pitB_pair_rtail_vanish_hpair q n (lw0_pitB_pair_conv q n) eps Heps).
Qed.

(* ---------- transport F3 段 2c：⟨f,σ_m⟩(q)→K 收敛装配骨架（纯文本 staged 稿·未编译·编译检验先行后落装） ----------

   [使命] 把段 2 唯一余留真数学缺口——qp 配对收敛 ⟨f_n,σ_m⟩(q) → K′（记号：
   f_n := lw0_niven_f q (Zpos (Qden q) # 1)%Q n，σ_m := lw0_sin_qp m，
   K′ := lw0_K (Qnum q) (Zpos (Qden q)) n）——装配为 Hgap 闭合主件
   lw0_pitB_pair_conv_K（语句面＝lw0_pi_transport_Wb_K_ht_gap 之缺口前提位
   逐字），并随之落 _ht 供件一行与终形三行。装配四步：
     ① 望远镜恒等（上游 2b 供件 lw0_pitB_pair_telescope：零 π 前提的纯 Qeq
       恒等，端点闭值 K′ 已由其语句面内承；目标差式经其换岸化归为三支——
       F(q)·(σ_m′(q)+1)、(−1)·F′(q)·σ_m(q)、尾项 lw0_pitB_pair_rtail q n m）；
     ② σ/γ 截断消逝（本块 sin_tail/cos_tail 两件：π 前提经 compat 核
       （real_sin_eq_compat／real_cos_eq_compat＋pi_geom_* 常值件）于 Real 层
       取值（sin q=0、cos q=−1），real_eq 逐点 eps-差见证形解包＋钉点→裸点
       换岸＋σ_m/σ_m′ 求值桥（lw0_sin_qp_eval／lw0_sin_qp_deriv_eval）；
     ③ ⟨F,τ_M⟩ 尾→0（上游 2b 供件 lw0_pitB_pair_rtail_vanish：其体内沿
       lw0_pitB_conv_pair_weight_bound→pwi 权重义务形→t_vanish 阶乘占优链
       闭合，本块零重复）；
     ④ 端点闭值（K′ 认定由 2b 望远镜语句面内承；z_lo/z_hi 偶阶格＋Ktel 链
       （lw0_Ktel_leg_alt/lw0_Ktel_partial/lw0_Ktel_tail/lw0_K_leg_connect）
       使用账在 2b 侧，本块零重复）。
   [依赖] 上游在件（行号系 2a 落装态 md5 a9a3649e／10,028 行实测，落装前重测）：
   lw0_sin_qp_eval(L3561)／lw0_sin_qp_deriv_eval(L3974)／real_sin_eq_compat・
   real_cos_eq_compat・pi_geom_sin_pi_zero・pi_geom_cos_pi_neg_one（S02/S10
   导入面）／lw0_sin_endpoint_transport(L5404) 样范／lw0_pi_qeq_ltT_r(L9663，
   2a 落)／lw0_pi_transport_Wb_K_ht_gap(L9740，2a 落)／
   lw0_pi_transport_Wb_K_tail(L9557)／lw0_leT'_ltT_trans(L1193)／
   Qabs_Qmult／Qabs_triangle／Qminus_0_r／Qmult_lt_0_compat／Qlt_to_QltT／
   QltT_to_Qlt／Qcompare_comp／Qlt_le_weak／Qle_refl／Qlt_refl／
   Qplus_le_compat／Qplus_lt_compat_l／Qplus_lt_compat_r／Qmult_le_compat_l／
   Qmult_lt_compat_r／Qmult_inv_r／Qinv_mult_distr／Qlt_not_eq／Qle_trans／
   Qlt_le_trans／Qlt_trans／Qabs_wd／Qplus_0_r／Qmult_1_l／Qmult_1_r／
   Qabs_nonneg／NatLe_drop／NatLe_lift（stdlib／导入面，使用先例＝2a 主件
   体内与 lw0_pitB_conv_pair_vanish 体内 L8745 区与
   lw0_pitB_conv_div_mul_cancel 体内 L7354 区）。
   上游 2b 供件接口（本块使用面；语句面需求侧定形、2b 落装时对本形负责或
   对表微调后更新本块使用名实参——对表微调见段 2c 施工单）：
     Lemma lw0_pitB_pair_telescope : forall (q : Q) (n m : nat),
       lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp m) q
       == lw0_K (Qnum q) (Zpos (Qden q)) n
          + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
              * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
          + (-1)%Q * qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
              * qpoly_eval (lw0_sin_qp m) q
          + lw0_pitB_pair_rtail q n m.
     Lemma lw0_pitB_pair_rtail_vanish : forall (q : Q) (n : nat),
       forall eps : Q, QltT 0 eps ->
       sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
         QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
   其中 lw0_pitB_pair_rtail : Q -> nat -> nat -> Q 系 2b 块 Definition 供出的
   尾项泛名（本块零展开、只经上两件使用）；两接口均零 q 界前提（t_vanish/
   pair_weight_bound 只需 QleT' 0 (Qabs q)，Qabs_nonneg 免费在件——施工单
   2b 草案之 QltT 0 q／QleT' q (10/3) 前提在本岸消去，对表微调已核算）。
   [对标] 语句面＝lw0_pi_transport_Wb_K_ht_gap 缺口前提位逐字（GAPASUME
   工艺缺口面）；π 前提修正形 real_const ((Qnum q # Qden q)%Q)；Real 层解包
   取形＝real_eq 逐点 eps-差见证形（S02 L399 取形卡）；eps 分割压界沿
   lw0_pitB_conv_sin_vanish 体内 (1#4)*eps 同族工艺（L8106-8110 在件先例）；
   Qeq 换岸轮沿 2a 主件 HE 轮同型（Qabs_wd＋Qcompare_comp 双证位）；div 消
   去沿 lw0_pitB_conv_div_mul_cancel（L7354）体内 transitivity 拆环＋
   Qmult_inv_r 闭合工艺。
   [构造性注记] 全件 Set 载体（QeqT/QltT/real_eq/sigT），零裸 Prop 分支；
   π 前提只经 compat 核于 Real 层取值（禁 Q 层 sin_Q(q)==0 形）；Qeq 改写
   禁穿 QltT/QleT' 壳（换岸一律 lw0_pi_qeq_ltT_r／Qcompare_comp）；零承认
   终端、零中止、零公理化壳、零新参数面；〔红点预案 #n〕占位仅为首发检验
   预期病灶注记，非证明缺位。
   [编译配方] born-in-place 检验先行（独立件 Require 主件态一发判定后再落
   主件）；落装序＝2a（已落）→ 2b → 本块（含 _ht／终形随块）；落装后四关
   双发＋第五证；插入锚（串锚内容，落前重测禁抄行号）＝2a 块尾 PA 行
   Print Assumptions lw0_pi_transport_Wb_K_ht_gap. 之后、主语句备档区头
   banner 之前同缝（2b 块居本块之前，依赖序零前向引用）。 *)

(* ============ 2c-0 表示换点微件对：sin/cos 部分和对钉点拼写与裸点同值 ============ *)

(* Qeq 面顶层改写（QltT 壳零涉；sin_partial/cos_partial 对 Q 同值项同一求值）。 *)
Lemma lw0_pitB_pair_pin_sin : forall (P q : Q) (m : nat),
  P == q -> sin_partial m P == sin_partial m q.
Proof.
  intros P q m Hpq. rewrite Hpq. apply Qeq_refl.
Qed.

Lemma lw0_pitB_pair_pin_cos : forall (P q : Q) (m : nat),
  P == q -> cos_partial m P == cos_partial m q.
Proof.
  intros P q m Hpq. rewrite Hpq. apply Qeq_refl.
Qed.

(* ============ 2c-1 σ 截断尾件（π 前提 sin q = 0 的实层取值 → Q 层逐点尾界） ============ *)

(* Real 层 real_eq 逐点 eps-差见证形解包（S02 L399 取形）。解包投影面——
   cauchy_real_sin (real_const P) 第 m 项对 sin_partial m P 的 change 表、
   real_zero 投影零面——为首发检验判定位〔红点预案 #4〕。 *)
Lemma lw0_pitB_pair_sin_tail : forall q : Q,
  real_eq (cauchy_real_sin (real_const ((Qnum q # Qden q)%Q))) real_zero ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M : nat => forall m : nat, NatLe M m ->
    QltT (Qabs (qpoly_eval (lw0_sin_qp m) q)) eps).
Proof.
  intros q Hsin0 eps Heps.
  assert (Hr : (Qnum q # Qden q)%Q == q) by reflexivity.
  unfold real_eq in Hsin0.
  destruct (Hsin0 eps Heps) as [N HN].  (* 〔349R 修复 R1：real_eq 前提面＝QltT（S02 L399 源面勘定），QltT_to_Qlt 降岸形类型错位——直接代入 Heps〕 *)
  (* 〔红点预案 #4：real_eq 展开形之 eps 前提型（Qlt/iff 桥）与参序以检验
     Check 判定；iff 形改 proj 拆取，Qlt 形直接代入。〕 *)
  exists N. intros m Hm.
  specialize (HN m Hm).
  apply (lw0_pi_qeq_ltT_r (Qabs (qpoly_eval (lw0_sin_qp m) q))
                          (Qabs (sin_partial m ((Qnum q # Qden q)%Q) - 0%Q)) eps).
  - assert (HE : Qabs (qpoly_eval (lw0_sin_qp m) q)
                 == Qabs (sin_partial m ((Qnum q # Qden q)%Q) - 0%Q)).
    { apply Qabs_wd.
      rewrite (lw0_pitB_pair_pin_sin _ q m Hr).  (* 〔349R 修复 R8（检验二战果）：pin 先行——原序 rewrite <- (lw0_sin_qp_eval m q) 找 sin_partial m q 而目标为 sin_partial m P（P≠q 句法位），Found no subterm 实测；对调后 eval 消去即达；cos_tail 同位系前向 rewrite 无此病（检验二对照）〕 *)
      rewrite <- (lw0_sin_qp_eval m q).
      symmetry. apply Qplus_0_r. }  (* 〔349R 修复 R3：Qminus_0_r 9.1 stdlib 无实名（QArith_base 全源零命中）；x-0 转换可达 x+0，主件 @4220 同型先例〕 *)
    exact HE.
  - change (sin_partial m ((Qnum q # Qden q)%Q) - 0%Q)
      with (projT1 (cauchy_real_sin (real_const ((Qnum q # Qden q)%Q))) m
            - projT1 real_zero m).
    (* 〔红点预案 #4：change 表两支以检验判定——若投影定义归约即达
       sin_partial m P／0，change 直过；否则沿定义面 unfold 一步。〕 *)
    exact HN.
Qed.

(* ============ 2c-2 γ 截断尾件（π 前提 cos q = −1 的实层取值 → Q 层逐点尾界） ============ *)

(* σ_m′ 求值桥＝lw0_sin_qp_deriv_eval（eval(deriv(σ_m)) x == cos_partial m x，
   L3974 在件逐字）；cos 值 −1 经 real_const (-1) 投影零面。 *)
Lemma lw0_pitB_pair_cos_tail : forall q : Q,
  real_eq (cauchy_real_cos (real_const ((Qnum q # Qden q)%Q))) (real_const (-1)%Q) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M : nat => forall m : nat, NatLe M m ->
    QltT (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) eps).
Proof.
  intros q Hcosm1 eps Heps.
  assert (Hr : (Qnum q # Qden q)%Q == q) by reflexivity.
  unfold real_eq in Hcosm1.
  destruct (Hcosm1 eps Heps) as [N HN].  (* 〔349R 修复 R2：同 R1〕 *)
  exists N. intros m Hm.
  specialize (HN m Hm).
  apply (lw0_pi_qeq_ltT_r
           (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))
           (Qabs (cos_partial m ((Qnum q # Qden q)%Q) - (-1)%Q)) eps).
  - assert (HE : Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                 == Qabs (cos_partial m ((Qnum q # Qden q)%Q) - (-1)%Q)).
    { apply Qabs_wd.
      rewrite (lw0_sin_qp_deriv_eval m q).
      rewrite (lw0_pitB_pair_pin_cos _ q m Hr).
      ring. }
    exact HE.
  - change (cos_partial m ((Qnum q # Qden q)%Q) - (-1)%Q)
      with (projT1 (cauchy_real_cos (real_const ((Qnum q # Qden q)%Q))) m
            - projT1 (real_const (-1)%Q) m).
    (* 〔红点预案 #4 同位：cos 侧投影 change 表检验判定。〕 *)
    exact HN.
Qed.

(* ============ 2c-3 主件（Hgap 闭合器）：⟨f,σ_m⟩(q) → K′ ============ *)

(* 望远镜换岸（2b-A，Qeq 面 rewrite 于 Qabs_wd 支）＋三支 eps 三分压界：
   X1 := 1 + (|Fq|+|Fdq|)，D := 3·X1，eps1 := eps·/D；合拢
   |Fq|·eps1 + (|Fdq|·eps1 + eps1) == (1/3)·eps（div 消去沿
   lw0_pitB_conv_div_mul_cancel 体内工艺：transitivity 拆环＋Qmult_inv_r），
   尾关 (1/3)·eps < eps（Qmult_lt_compat_r，0<z→x<y→x·z<y·z 单调向）。 *)
Lemma lw0_pitB_pair_conv_K : forall (q : Q) (n : nat),
  real_eq real_pi_geom (real_const ((Qnum q # Qden q)%Q)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M : nat => forall m : nat, NatLe M m ->
    QltT (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                            (lw0_sin_qp m) q
                - lw0_K (Qnum q) (Zpos (Qden q)) n)) eps).
Proof.
  intros q n Hpi eps Heps.
  (* —— π 端点值对（compat 核直供钉点；314 段 0 pose 块工艺，钉点拼写
     用 QMAKEPOS 修正形） —— *)
  assert (Hsin0 : real_eq (cauchy_real_sin (real_const ((Qnum q # Qden q)%Q)))
                          real_zero).
  { apply (real_eq_trans (cauchy_real_sin (real_const ((Qnum q # Qden q)%Q)))
                         (cauchy_real_sin real_pi_geom) real_zero).
    - apply real_sin_eq_compat. apply real_eq_sym. exact Hpi.
    - exact pi_geom_sin_pi_zero. }
  assert (Hcosm1 : real_eq (cauchy_real_cos (real_const ((Qnum q # Qden q)%Q)))
                           (real_const (-1)%Q)).
  { apply (real_eq_trans (cauchy_real_cos (real_const ((Qnum q # Qden q)%Q)))
                         (cauchy_real_cos real_pi_geom) (real_const (-1)%Q)).
    - apply real_cos_eq_compat. apply real_eq_sym. exact Hpi.
    - exact pi_geom_cos_pi_neg_one. }
  (* —— eps 三分基准：X1 := 1 + (|Fq|+|Fdq|)，D := 3·X1，eps1 := eps·/D —— *)
  pose (Fq := qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q).
  pose (Fdq := qpoly_eval
                 (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q).
  pose (X1 := (1 + (Qabs Fq + Qabs Fdq))%Q).
  assert (H1le : Qle 1%Q X1).
  { apply (Qle_trans 1%Q (1 + 0%Q)%Q X1).
    - rewrite Qplus_0_r. apply Qle_refl.
    - unfold X1. apply Qplus_le_compat.
      + apply Qle_refl.
      + apply (Qplus_le_compat 0%Q (Qabs Fq) 0%Q (Qabs Fdq)); apply Qabs_nonneg. }
  (* 〔红点预案 #7：Qplus_le_compat／Qle_refl 桥名参序首发检验判定；红则
     沿 Qle_refl＋Qplus_ge_compat_r 组装或 cbn[lia] 兜底（Qle 是 Prop 面）。〕 *)
  assert (HX1lt : Qlt 0%Q X1).
  { apply (Qlt_le_trans 0%Q 1%Q X1).
    - apply (QltT_to_Qlt 0%Q 1%Q). unfold QltT. reflexivity.
    - exact H1le. }
  assert (HX1ne : ~ X1 == 0%Q) by (intro Hc; exact (Qlt_not_eq 0%Q X1 HX1lt (Qeq_sym X1 0%Q Hc))).
  assert (HD : QltT 0 (3 * X1)%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0%Q 3%Q). unfold QltT. reflexivity.
    - exact HX1lt. }
  pose (eps1 := (eps * / (3 * X1))%Q).
  assert (Heps1 : QltT 0 eps1).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt _ _ Heps).
    - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ HD). }
  (* —— 三尾见证取 M := 后继 max（NatLe_lift 轮沿 2a 主件体内同型） —— *)
  destruct (lw0_pitB_pair_rtail_vanish q n eps1 Heps1) as [Mt HMt].
  destruct (lw0_pitB_pair_cos_tail q Hcosm1 eps1 Heps1) as [Mc HMc].
  destruct (lw0_pitB_pair_sin_tail q Hsin0 eps1 Heps1) as [Ms HMs].
  exists (Datatypes.S (Nat.max Mt (Nat.max Mc Ms))). intros m Hm.
  assert (Hmle : (Datatypes.S (Nat.max Mt (Nat.max Mc Ms)) <= m)%nat) by exact (NatLe_drop (Datatypes.S (Nat.max Mt (Nat.max Mc Ms))) m Hm).
  assert (HmMt : NatLe Mt m) by (apply NatLe_lift; lia).
  assert (HmMc : NatLe Mc m) by (apply NatLe_lift; lia).
  assert (HmMs : NatLe Ms m) by (apply NatLe_lift; lia).
  specialize (HMt m HmMt). specialize (HMc m HmMc). specialize (HMs m HmMs).
  apply (lw0_pi_qeq_ltT_r
           (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
           (Qabs ((-1)%Q * Fq * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                  + (Fdq * qpoly_eval (lw0_sin_qp m) q
                     + lw0_pitB_pair_rtail q n m))) eps).  (* 〔349R 修补 E1（R3·仲裁令授权）：355R R1 反号形下真恒等式 pair−K' == −Fq(σ'+1)+Fdqσ+rtail——RHS 双边界反号；355 拟 Qabs_opp 轮在 rtail 项不成立（括号内 +rtail 取负即反），构造级勘定响亮登记〕 *)
  - assert (HE : Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp m) q
                    - lw0_K (Qnum q) (Zpos (Qden q)) n)
                 == Qabs ((-1)%Q * Fq * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                          + (Fdq * qpoly_eval (lw0_sin_qp m) q
                             + lw0_pitB_pair_rtail q n m))).  (* 〔349R 修补 E2（R3）：同 E1——HE 证体零改（Qabs_wd＋telescope rewrite＋ring 在 R1 形下闭合）〕 *)
    { apply Qabs_wd.
      rewrite (lw0_pitB_pair_telescope q n m).
      (* 〔红点预案 #6：2b-A 落装形对表——Qeq setoid 实例缺失回退展开形时，
         改 unfold Qeq＋transitivity 拆环（328 c3/c4 零 rewrite 工艺在案）；
         号记录若与 2b 实装 ± 形差一律 ring 面吸收。〕 *)
      unfold Fq, Fdq, X1. ring. }
    exact HE.
  - (* —— 三角压界合流：|A+B+C| ≤ |Fq|·eps1 + (|Fdq|·eps1 + |尾|) < eps —— *)
    assert (HabsA : Qle (Qabs ((-1)%Q * Fq * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)))
                        (Qabs Fq * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))).
    { (* 〔349R 修补 E4a（R3）：Habs 随 (−1) 移位重述；免 Qmult_assoc（old HabsB 该战术对左结合三积项无 x*(y*z) 子项匹配——staged 必红位勘定）显式路由〕 *)
      rewrite (Qabs_Qmult ((-1)%Q * Fq)
                (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)).
      rewrite (Qabs_Qmult (-1)%Q Fq).
      change (Qabs (-1)%Q) with 1%Q. rewrite Qmult_1_l.
      apply Qle_refl. }
    assert (HabsB : Qle (Qabs (Fdq * qpoly_eval (lw0_sin_qp m) q))
                        (Qabs Fdq * Qabs (qpoly_eval (lw0_sin_qp m) q))).
    { rewrite Qabs_Qmult. apply Qle_refl. }  (* 〔349R 修补 E4b（R3）：同 E4a——old HabsA 模式代入〕 *)
    assert (Hle : Qle (Qabs ((-1)%Q * Fq * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                              + (Fdq * qpoly_eval (lw0_sin_qp m) q
                                  + lw0_pitB_pair_rtail q n m)))  (* 〔349R 修补 E3（R3）：同 E1〕 *)
                       (Qabs Fq * eps1
                        + (Qabs Fdq * eps1
                           + Qabs (lw0_pitB_pair_rtail q n m)))).
    { apply (Qle_trans _
               (Qabs ((-1)%Q * Fq * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))
                + Qabs (Fdq * qpoly_eval (lw0_sin_qp m) q
                        + lw0_pitB_pair_rtail q n m))).
      - apply Qabs_triangle.
      - apply Qplus_le_compat.
        + apply (Qle_trans _
                    (Qabs Fq * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))).
          * exact HabsA.
          * (* 〔红点预案 #8：Qmult_le_compat_l／_r 参序首发检验判定——
               本环境在件使用先例＝CONVGEOM 卡 L1769 ⑤（漏桥即 positive
               错位）；目标形 x·y ≤ x·z 走 _l（y≤z→0≤x）。〕 *)
            rewrite !(Qmult_comm (Qabs Fq)).  (* 〔349R 修复 R4：stdlib 无 Qmult_le_compat_l——comm 换岸走 _r，主件 @439 同型先例〕 *)
            apply Qmult_le_compat_r.
            -- exact (Qlt_le_weak _ _ (QltT_to_Qlt _ _ HMc)).
            -- apply Qabs_nonneg.
        + apply (Qle_trans _
                    (Qabs (Fdq * qpoly_eval (lw0_sin_qp m) q)
                     + Qabs (lw0_pitB_pair_rtail q n m))).
          * apply Qabs_triangle.
          * apply Qplus_le_compat.
            -- apply (Qle_trans _ (Qabs Fdq * Qabs (qpoly_eval (lw0_sin_qp m) q))).
               ++ exact HabsB.
               ++ rewrite !(Qmult_comm (Qabs Fdq)).  (* 〔349R 修复 R5：同 R4〕 *)
                  apply Qmult_le_compat_r.
                  ** exact (Qlt_le_weak _ _ (QltT_to_Qlt _ _ HMs)).
                  ** apply Qabs_nonneg.
            -- apply Qle_refl. }
    assert (Hlt1 : Qlt (Qabs Fq * eps1
                        + (Qabs Fdq * eps1
                           + Qabs (lw0_pitB_pair_rtail q n m)))
                       (Qabs Fq * eps1 + (Qabs Fdq * eps1 + eps1))).
    { apply (proj2 (Qplus_lt_r _ _ _)).  (* 〔349R 修复 R6：stdlib 无 Qplus_lt_compat_l/r——Qplus_lt_r（QArith_base L1192 iff）proj2 两连 r 形拆分，语义同构〕 *)
      apply (proj2 (Qplus_lt_r _ _ _)).
      exact (QltT_to_Qlt _ _ HMt). }
    assert (Hsum : Qeq (Qabs Fq * eps1 + (Qabs Fdq * eps1 + eps1))
                       ((1 # 3) * eps)%Q).
    { unfold eps1.
      transitivity (eps * (X1 * Qinv (3 * X1)))%Q.
      - unfold X1. ring.
      - rewrite Qinv_mult_distr.
        transitivity (eps * (Qinv 3%Q * (X1 * Qinv X1)))%Q.
        + unfold X1. ring.
        + rewrite (Qmult_inv_r X1 HX1ne).
          rewrite Qmult_1_r.
          change (Qinv 3%Q) with (1 # 3)%Q.
          ring. }
    (* 〔红点预案 #8：Hsum 之 Qinv_mult_distr 无前提面以检验判定（QREWRITE
       卡条 4 记其在册无前提；红则 unfold Qdiv 后按 div_mul_cancel 体内
       transitivity 拆环工艺重走）。〕 *)
    apply Qlt_to_QltT.
    assert (Hlt2 : Qlt ((1 # 3) * eps)%Q eps%Q).
    { assert (Hlt0 : Qlt ((1 # 3) * eps)%Q (1 * eps)%Q).  (* 〔349R 修复 R7：原 1*eps 中转第二腿 eps<eps 恒假（数学病）——Qmult_lt_compat_r 显式实例直证＋Qmult_1_l 桥（Qeq 改写 Qlt 面 L1848 在案）〕 *)
      { apply (Qmult_lt_compat_r (1 # 3)%Q 1%Q eps).
        - exact (QltT_to_Qlt _ _ Heps).
        - unfold Qlt. reflexivity. }
      rewrite Qmult_1_l in Hlt0. exact Hlt0. }
    apply (Qlt_trans _ (Qabs Fq * eps1 + (Qabs Fdq * eps1 + eps1))).
    + apply (Qle_lt_trans _
               (Qabs Fq * eps1
                + (Qabs Fdq * eps1 + Qabs (lw0_pitB_pair_rtail q n m)))).
      * exact Hle.
      * exact Hlt1.
    + rewrite Hsum. exact Hlt2.
Qed.

(* ============ 2c-4 `_ht` 供件一行（prescribed 名位；施工单 §六.1 逐字） ============ *)

Lemma lw0_pi_transport_Wb_K_ht : forall (q : Q) (n : nat),
  real_eq real_pi_geom (real_const ((Qnum q # Qden q)%Q)) ->
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m : nat, NatLe N m ->
      QltT (Qabs (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) m
                   - lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)) eps).
Proof.
  intros q n Hpi.
  apply (lw0_pi_transport_Wb_K_ht_gap q n Hpi).
  exact (lw0_pitB_pair_conv_K q n Hpi).
Qed.

(* ============ 2c-5 终形三行（321 Part B 原样；π 前提修正形；Theorem 守卫账随更） ============ *)

Theorem lw0_pi_transport_Wb_K : forall (q : Q) (n : nat)
  (Hc : cauchy (fun m : nat =>
           altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) m)),
  real_eq real_pi_geom (real_const ((Qnum q # Qden q)%Q)) ->
  real_eq (lw0_L_of_seq (lw0_Wb (Zpos (Qden q) # 1)%Q q n) Hc)
          (real_const (lw0_K (Qnum q) (Zpos (Qden q)) n / q_fact n)).
Proof.
  intros q n Hc Hpi. apply lw0_pi_transport_Wb_K_tail.
  exact (lw0_pi_transport_Wb_K_ht q n Hpi).
Qed.

(* ============ 随块 PA 锚（七线） ============ *)
Print Assumptions lw0_pitB_pair_pin_sin.
Print Assumptions lw0_pitB_pair_pin_cos.
Print Assumptions lw0_pitB_pair_sin_tail.
Print Assumptions lw0_pitB_pair_cos_tail.
Print Assumptions lw0_pitB_pair_conv_K.
Print Assumptions lw0_pi_transport_Wb_K_ht.
Print Assumptions lw0_pi_transport_Wb_K.
Theorem lw0_pi_irrational :
  forall a b : Q,
    QltT 0 (Qabs b) ->
    real_eq real_pi_geom (real_const (a / b)) ->
    sigT (fun c : Q => And (QltT 0 c)
            (real_lt (real_const c)
               (real_metric real_pi_geom (real_const (a / b))))).
Proof.
  intros a b Hab Hpi.
  (* 卡 2｜步 1 前提带 [L5633] *)
  destruct (lw0_pi_asm_q_Wband a b Hpi) as [Hq0 Hq103].
  (* Hq0 : QltT 0 (a / b)   Hq103 : QleT' (a / b) (10 # 3) *)
  (* 卡 3｜步 2-4 指标与界面（F3 连带：B 槽钉 b'，Hab 退出使用链留前提面） *)
  pose (b' := (Zpos (Qden (a / b)) # 1)%Q).
  assert (Hb'pos : QltT 0 b') by reflexivity.
  (* Zpos 构造子级：0 ?= Zpos (Qden (a/b)) * 1 在 Zpos 头归约 Lt（314 §二.2.1） *)
  pose (d0 := lw0_pi_d0_of b').
  pose (Hd0abs := lw0_pi_d0_absorb b' Hb'pos).
  assert (Hd0abs' : QleT' b' (lw0_q_of_nat d0)).
  { exact Hd0abs. }
  pose (n_sel := lw0_n_select (10 * d0) 0).
  pose (Hc' := lw0_pi_chain_L_cauchy b' (a / b) (10 * d0) 0 Hb'pos Hq0 Hq103).
  destruct (lw0_pi_chain_L_bounds b' (a / b) (10 * d0) 0 Hc' Hb'pos Hq0 Hq103)
    as [Hlow Hup].
  (* 卡 4｜步 5 整数见证 *)
  destruct (lw0_K_integer (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel) as [z Hz].
  (* 卡 5｜步 6 位 1 输入：P2 桥三行（兼验形 exact Hpi 直过则删桥——314 红点2） *)
  assert (Hpitr : real_eq real_pi_geom
                  (real_const (Qnum (a / b) # Qden (a / b)))).
  { apply (real_eq_trans real_pi_geom (real_const (a / b))
                                  (real_const (Qnum (a / b) # Qden (a / b)))).
    - exact Hpi.
    - apply lw0_pitS_const_eq. reflexivity. }
  pose (H2 := lw0_pi_transport_Wb_K (a / b) n_sel Hc' Hpitr).
  pose (Hw0n := lw0_pi_w0n_lt1 b' (a / b) d0 0 Hb'pos
                (lw0_QltT_le (a / b) Hq0) Hq103 Hd0abs').
  (* ——Q 侧换岸块＝303 §2.1 R3-R8（B 参面已由骨架换 b'；HeqK 共享先证）—— *)
  assert (HeqK : ((lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel)
                  * q_fact n_sel)%Q
                 == lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel).
  { rewrite (Qmult_comm (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel)
                        (q_fact n_sel)).
    apply lw0_pitS_qfact_elim. }
  pose (Qposf := Qlt_to_QltT 0 (q_fact n_sel) (q_fact_pos n_sel)).
  (* R3 下界实层过 H2 ＋ R4 换岸（P1 零岸接缝：①δ 直过首响，红则 303 P1 ②③桥） *)
  pose (HlowT := lw0_real_lt_eq_transport_r
                   (lw0_L_of_seq (lw0_Wb b' (a / b) n_sel) Hc')
                   (real_const (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel
                                  / q_fact n_sel)) real_zero H2 Hlow).
  pose (Hqf := lw0_real_lt_const_Qlt 0
                  (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel)
                  HlowT).
  (* R5 下界乘序＋消分母（Qcompare_comp 样范＝gate 体） *)
  assert (H0lt : QltT 0 (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel)).
  { pose (Hm0 := lw0_qmult_lt_compat_r 0 (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel) (q_fact n_sel) Hqf Qposf).
    apply Qlt_to_QltT.
    apply QltT_to_Qlt in Hm0.
    rewrite Qmult_0_l in Hm0.
    rewrite HeqK in Hm0.
    exact Hm0. }
  (* R6 上界实层过 H2 ＋ R7 换岸 ＋ R8 乘序消分母 *)
  pose (HupT := lw0_real_lt_eq_transport_l
                  (lw0_L_of_seq (lw0_Wb b' (a / b) n_sel) Hc')
                  (real_const (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel
                                 / q_fact n_sel))
                  (real_const (lw0_Wb b' (a / b) n_sel 0)) H2 Hup).
  pose (Hqf' := lw0_real_lt_const_Qlt
                  (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel)
                  (lw0_Wb b' (a / b) n_sel 0) HupT).
  assert (H1' : QltT (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel)
                   (q_fact n_sel * lw0_Wb b' (a / b) n_sel 0)).
  { apply Qlt_to_QltT.
    pose (Hm1 := lw0_qmult_lt_compat_r
                   (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel)
                   (lw0_Wb b' (a / b) n_sel 0) (q_fact n_sel) Hqf' Qposf).
    assert (Hc1 : (((lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel / q_fact n_sel)
                    * q_fact n_sel) ?= (lw0_Wb b' (a / b) n_sel 0 * q_fact n_sel))%Q
                  = (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel
                     ?= (q_fact n_sel * lw0_Wb b' (a / b) n_sel 0))%Q).
    { exact (Qcompare_comp _ _ HeqK _ _ (Qmult_comm _ _)). }
    apply QltT_to_Qlt in Hm1.
    rewrite HeqK in Hm1.
    rewrite (Qmult_comm (lw0_Wb b' (a / b) n_sel 0) (q_fact n_sel)) in Hm1.
    exact Hm1. }
  (* Qlt 传递性合并（H1'＋Hw0n） *)
  assert (H1lt : QltT (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel) 1).
  { apply Qlt_to_QltT.
    apply Qlt_trans with (q_fact n_sel * lw0_Wb b' (a / b) n_sel 0).
    - apply QltT_to_Qlt. exact H1'.
    - apply QltT_to_Qlt. exact Hw0n. }
  (* 卡 6｜步 7 出口闭合：反证门 lw0_pi_contra_gate ＋ 出口 lw0_pi_irrational_exit *)
  pose (Hcontra := lw0_pi_contra_gate
                     (lw0_K (Qnum (a / b)) (Zpos (Qden (a / b))) n_sel) z H0lt H1lt Hz).
  exact (lw0_pi_irrational_exit a b Hcontra).
Qed.
Print Assumptions lw0_pi_irrational.
Separate Extraction qpoly_mul qpoly_deriv qpoly_eval
  lw0_fact_lower_growth lw0_pi_bound_dominated_even lw0_pi_bound_dominated_odd
  lw0_Wb_ratio_bound
  lw0_qp_antideriv lw0_qp_ai lw0_qp_pair
  lw0_real_lt_const_Qlt lw0_sin_endpoint_transport
  lw0_cos_endpoint_transport lw0_endpoint_transport lw0_pi_asm_q_bounds
  lw0_pi_mono lw0_pi_mono_eval lw0_pi_qminus_pow lw0_pi_qminus_pow_eval
  lw0_niven_f lw0_niven_f_eval
  lw0_n_select lw0_n_select_ge_b lw0_n_select_dominated
  lw0_n_select_dominated_of_qle lw0_pi_asm_q_bounds_upper_QleT'
  lw0_n_select_fact_lower lw0_real_lt_const_Qlt_inv
  lw0_pi_asm_q_pos lw0_pi_asm_q_Wband
  lw0_n_select_ge_2 lw0_pi_geom_metric_proj
  qpoly_zero qpoly_opp lw0_coef lw0_pred_iter lw0_qtail lw0_mono
  lw0_qminus_pow lw0_niven_f_z lw0_ratio lw0_binom lw0_zsign lw0_z_lo
  lw0_z_hi lw0_int_fact_div lw0_z_lo_integer lw0_z_hi_integer
  qpoly_map lw0_alt lw0_die lw0_F_aux lw0_F lw0_sin_series_real
  lw0_cos_series_real lw0_deriv_iter_nil lw0_deriv_add_eval
  lw0_deriv_iter_cons_add_joint lw0_deriv_iter_add_eval
  lw0_deriv_iter_cons_eval lw0_deriv2_scalar_eval lw0_q_abs_div
  lw0_q_eq_le lw0_q_mult_le_l lw0_qp_ai_abs_bound lw0_pair_abs_bound
  lw0_qsum lw0_K_leg lw0_K lw0_Ktel_seq
  lw0_pi_chain_L_cauchy lw0_pi_chain_L_bounds lw0_pi_contra_gate
  lw0_pi_irrational_exit lw0_pi_irrational
  Powpos lw0_posnat_zeq lw0_zpower_nat_add lw0_zpos_pospow
  lw0_q_pow_qmake lw0_q_pow_m1 lw0_bpa_binom_eq
  lw0_conn_lo lw0_conn_hi
  lw0_real_lt_eq_transport_l lw0_real_lt_eq_transport_r
  lw0_q_pow_add lw0_qfact_split_lower lw0_qmult_lt_compat_r
  lw0_pi_w0_lt1_core.
