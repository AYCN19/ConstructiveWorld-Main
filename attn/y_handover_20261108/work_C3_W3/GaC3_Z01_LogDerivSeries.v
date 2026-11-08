(* ConstructiveWorld-Main - Dirichlet-series face of the logarithmic derivative of zeta. *)

(** * GaC3_Z01_LogDerivSeries: the Dirichlet-series face of -zeta'/zeta.

    Mission.  Node C3-Z01 (segment C3): the Dirichlet-series face of the
    logarithmic derivative -zeta'/zeta and its absolute-convergence bound.
    The von Mangoldt weight carrier is the tree lcm power difference
    [z01_lam] (Lambda(n) := ln lcm(1..n) - ln lcm(1..n-1)), carried by the
    D1-B3 fold [zz_lcm_range] with the positivity item [zz_lcm_range_pos].
    Named faces: the weight bound Lambda(n) <= ln n, the telescope
    identity sum_{n<=N} Lambda(n) = ln lcm(1..N) [z01_telescope], the
    Lambda-weighted real tail sums, the absolute-convergence bounds for
    sigma > 1 ([z01_absconv_bound] at the exact condensation constant;
    [z01_absconv_uniform] for sigma0 <= sigma), and the Cx Cauchy
    rational-margin face under the registered triangle premise
    [z01_cauchy_bound].  The full object -zeta'/zeta awaits the C2.05
    limit assembly and a complex-log differentiation face (open supply
    faces of the Z-line).

    Dependencies.  [S01_BaseRing] ([NatLe], selective import),
    [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
    [CxRealPairCore] + [CxRealPairExpLog] (base pair), [GaC2_Iface_DS]
    (C2.01 partial sums, C2.02 condensation engine), [piu_zz_pnt_lcmpow] +
    [piu_zz_padic_clearing] (D1-B3 lcm carrier; the C2.02 leaf faces load
    through the interface slice); Stdlib [QArith], [ZArith], [Arith],
    [Lia].

    References.  ZZ theory (AFP PNT_with_Remainder, Song & Yao):
    [fds_mangoldt_eq] :29, [abs_conv_abscissa_log_deriv] :39,
    [logderiv_zeta_bound] :409 (1 < sigma <= 23/20 => |logderiv| <= 5/4 *
    1/(sigma-1), the explicit-constant discipline mirrored by [z01_bound]
    and the certificate band); drafts_C3.md C3-Z01 card; the psi(N)
    identity context of piu_zz_padic_clearing.

    Constructivity.  Every named construction is carried by [Set]; all
    predicates are Set-sorted ([real_lt] / [real_le] / [QltT] / [NatLe]);
    zero assumed constants, zero abandoned proofs, zero classical choice.
    The Section premise declarations are the GAPASUME family, discharged
    as explicit premise arguments at End, so Print Assumptions of every
    named item reads Closed under the global context; [Hlnmono] /
    [Hln2pos] are L0-stock instantiable; [Hnormlam] is the honest open
    n-fold-triangle supply face (C1.4 convergence-extension supply route).

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_Z01_LogDerivSeries.v] compiles cleanly (exit 0) from the work
    directory (sandbox pair), single compile lane under the cpu_guard v3
    wrapper. *)

Require S01_BaseRing.
(* Selective import (the S01 state-space field S shadows the nat          *)
(* constructor under a full import; only the Set-sorted nat bound face is *)
(* consumed). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Import GaC2_02_AbsConvTailBound_b.
Import GaC2_02_AbsConvTailBound_c.
Require Import piu_zz_pnt_lcmpow.
Require Import piu_zz_padic_clearing.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The von Mangoldt weight carrier: the lcm power difference.  *)
(* ===================================================================== *)

Lemma z01_z2nat_ofnat : forall n : nat, Z.to_nat (Z.of_nat n) = n.
Proof.
  intro n.
  assert (H1 : (Z.to_nat (Z.of_nat n) <= n)%nat).
  { destruct (Nat.le_gt_cases (Z.to_nat (Z.of_nat n)) n) as [H | H]; [exact H | exfalso].
    pose proof (Znat.inj_lt n (Z.to_nat (Z.of_nat n)) H) as Hz.
    rewrite Z2Nat.id in Hz by apply Nat2Z.is_nonneg. lia. }
  assert (H2 : (n <= Z.to_nat (Z.of_nat n))%nat).
  { destruct (Nat.le_gt_cases n (Z.to_nat (Z.of_nat n))) as [H | H]; [exact H | exfalso].
    pose proof (Znat.inj_lt (Z.to_nat (Z.of_nat n)) n H) as Hz.
    rewrite Z2Nat.id in Hz by apply Nat2Z.is_nonneg. lia. }
  apply Nat.le_antisymm; [ exact H1 | exact H2 ].
Qed.

Lemma z01_zofnat_S_pos : forall n : nat, (0 < Z.of_nat (S n))%Z.
Proof. intro n. exact (Znat.inj_lt 0 (S n) (Nat.lt_0_succ n)). Qed.

(* Small Z-level helper: a positive divisor of a positive integer is at   *)
(* most the integer. *)
Lemma z01_zdiv_le : forall d m : Z,
  (0 < d)%Z -> (0 < m)%Z -> (d | m)%Z -> (d <= m)%Z.
Proof.
  intros d m Hd Hm [q Hq]. rewrite Z.mul_comm in Hq.
  assert (Hq0 : (0 < q)%Z).
  { destruct (Z.lt_trichotomy 0 q) as [Hq1 | [Hq1 | Hq1]].
    - exact Hq1.
    - exfalso. rewrite <- Hq1 in Hq. lia.
    - exfalso.
      assert (Hdq : (d * q <= d * 0)%Z).
      { apply (proj1 (Z.mul_le_mono_pos_l q 0 d Hd)). lia. }
      rewrite Z.mul_0_r in Hdq. lia. }
  rewrite Hq.
  assert (H1 : (d * 1 <= d * q)%Z).
  { apply (proj1 (Z.mul_le_mono_pos_l 1 q d Hd)). lia. }
  rewrite Z.mul_1_r in H1. exact H1.
Qed.

(* The least-common-multiple fold 1..K (D1-B3 carrier) transported to nat *)
(* for the tree real line. *)
Definition z01_lcmn (n : nat) : nat :=
  Z.to_nat (piu_zz_padic_clearing.zz_lcm_range n).

Lemma z01_lcm_nonneg : forall n : nat,
  (0 <= piu_zz_padic_clearing.zz_lcm_range n)%Z.
Proof. intro n. pose proof (zz_lcm_range_pos n). lia. Qed.

Lemma z01_lcm_ge1 : forall n : nat, NatLe 1 (z01_lcmn n).
Proof.
  intro n. apply NatLe_lift.
  assert (Hle : (Z.to_nat 1 <= Z.to_nat (piu_zz_padic_clearing.zz_lcm_range n))%nat).
  { apply (proj1 (Z2Nat.inj_le 1 (piu_zz_padic_clearing.zz_lcm_range n)
                    (Nat2Z.is_nonneg 1) (z01_lcm_nonneg n))).
    exact (zz_lcm_range_pos n). }
  change (Z.to_nat 1) with 1%nat in Hle. exact Hle.
Qed.

Lemma z01_lcm_pos_l : forall n : nat,
  real_lt real_zero (nat_real (z01_lcmn n)).
Proof. intro n. apply nat_real_pos. apply z01_lcm_ge1. Qed.

(* The lcm step bound: lcm(1..S n) <= (S n) * lcm(1..n), from the fold    *)
(* head Z.lcm and the positivity item zz_lcm_range_pos of piu_zz_pnt_    *)
(* lcmpow (D1-B3). *)
Lemma z01_lcm_step_le : forall n : nat,
  (piu_zz_padic_clearing.zz_lcm_range (S n)
     <= Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)%Z.
Proof.
  intro n. cbn [piu_zz_padic_clearing.zz_lcm_range].
  apply (z01_zdiv_le
           (Z.lcm (piu_zz_padic_clearing.zz_lcm_range n) (Z.of_nat (S n)))
           (Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)).
  - pose proof (zz_lcm_range_pos (S n)) as Hp.
    cbn [piu_zz_padic_clearing.zz_lcm_range] in Hp. lia.
  - pose proof (zz_lcm_range_pos n) as Ha.
    assert (Hprod : (1 <= Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)%Z).
    { apply (Z.le_trans 1 (Z.of_nat (S n))
               (Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)).
      - pose proof (z01_zofnat_S_pos n). lia.
      - pose proof (proj1 (Z.mul_le_mono_pos_l 1
                             (piu_zz_padic_clearing.zz_lcm_range n)
                             (Z.of_nat (S n)) (z01_zofnat_S_pos n)) Ha) as Hm.
        rewrite Z.mul_1_r in Hm. exact Hm. }
    lia.
  - apply Z.lcm_least.
    + exact (Z.divide_mul_r (piu_zz_padic_clearing.zz_lcm_range n)
               (Z.of_nat (S n)) (piu_zz_padic_clearing.zz_lcm_range n)
               (Z.divide_refl (piu_zz_padic_clearing.zz_lcm_range n))).
    + rewrite Z.mul_comm.
      exact (Z.divide_mul_r (Z.of_nat (S n))
               (piu_zz_padic_clearing.zz_lcm_range n) (Z.of_nat (S n))
               (Z.divide_refl (Z.of_nat (S n)))).
Qed.

(* The fold is divisibility-monotone; hence the nat transport is monotone. *)
Lemma z01_lcm_div_step : forall n : nat,
  (piu_zz_padic_clearing.zz_lcm_range n
     | piu_zz_padic_clearing.zz_lcm_range (S n))%Z.
Proof. intro n. cbn [piu_zz_padic_clearing.zz_lcm_range]. apply Z.divide_lcm_l. Qed.

Lemma z01_lcm_div_mono : forall m k : nat, (m <= k)%nat ->
  (piu_zz_padic_clearing.zz_lcm_range m
     | piu_zz_padic_clearing.zz_lcm_range k)%Z.
Proof.
  intros m k H. revert H. induction k as [|k IH]; intro H.
  - assert (Hm : m = 0%nat) by lia. subst m. apply Z.divide_refl.
  - destruct (Nat.eq_dec m (S k)) as [Heq | Hne].
    + rewrite Heq. apply Z.divide_refl.
    + apply (Z.divide_trans (piu_zz_padic_clearing.zz_lcm_range m)
               (piu_zz_padic_clearing.zz_lcm_range k)
               (piu_zz_padic_clearing.zz_lcm_range (S k))).
      * apply IH. lia.
      * apply z01_lcm_div_step.
Qed.

Lemma z01_lcmn_mono : forall m k : nat, (m <= k)%nat ->
  (z01_lcmn m <= z01_lcmn k)%nat.
Proof.
  intros m k H. unfold z01_lcmn.
  apply (proj1 (Z2Nat.inj_le (piu_zz_padic_clearing.zz_lcm_range m)
                  (piu_zz_padic_clearing.zz_lcm_range k)
                  (z01_lcm_nonneg m) (z01_lcm_nonneg k))).
  apply z01_zdiv_le.
  - pose proof (zz_lcm_range_pos m). lia.
  - pose proof (zz_lcm_range_pos k). lia.
  - apply z01_lcm_div_mono. exact H.
Qed.

(* The nat-level step bound: lcm(1..S n) <= (S n) * lcm(1..n). *)
Lemma z01_lcmn_step : forall n : nat,
  (z01_lcmn (S n) <= S n * z01_lcmn n)%nat.
Proof.
  intro n.
  assert (Hprod0 : (0 <= Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)%Z).
  { pose proof (zz_lcm_range_pos n) as Ha.
    assert (H1 : (1 <= Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)%Z).
    { apply (Z.le_trans 1 (Z.of_nat (S n))
               (Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)).
      - pose proof (z01_zofnat_S_pos n). lia.
      - pose proof (proj1 (Z.mul_le_mono_pos_l 1
                             (piu_zz_padic_clearing.zz_lcm_range n)
                             (Z.of_nat (S n)) (z01_zofnat_S_pos n)) Ha) as Hm.
        rewrite Z.mul_1_r in Hm. exact Hm. }
    lia. }
  assert (Hmul : Z.to_nat (Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)
                 = (S n * Z.to_nat (piu_zz_padic_clearing.zz_lcm_range n))%nat).
  { rewrite (Z2Nat.inj_mul (Z.of_nat (S n))
               (piu_zz_padic_clearing.zz_lcm_range n)
               (Nat2Z.is_nonneg (S n)) (z01_lcm_nonneg n)).
    rewrite z01_z2nat_ofnat. reflexivity. }
  unfold z01_lcmn. eapply Nat.le_trans.
  - apply (proj1 (Z2Nat.inj_le
                    (piu_zz_padic_clearing.zz_lcm_range (S n))
                    (Z.of_nat (S n) * piu_zz_padic_clearing.zz_lcm_range n)
                    (z01_lcm_nonneg (S n)) Hprod0)).
    exact (z01_lcm_step_le n).
  - rewrite Hmul. apply Nat.le_refl.
Qed.

(* Monotone transfer of nat bounds into the embedded nat reals. *)
Lemma z01_natreal_le : forall m k : nat, (m <= k)%nat ->
  real_le (nat_real m) (nat_real k).
Proof.
  intros m k H. destruct (Nat.eq_dec m k) as [Heq | Hne].
  - apply r_le_of_eq. rewrite Heq. apply real_eq_refl.
  - assert (Hlt : (S m <= k)%nat) by lia.
    apply (real_lt_le_iff (nat_real m) (nat_real k)). left.
    apply nat_real_lt. apply NatLe_lift. exact Hlt.
Qed.

(* Weak monotonicity of the tree real log on positive arguments. *)
Lemma z01_log_le_mono : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab. unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - apply (real_lt_le_iff (real_log a Ha) (real_log b Hb)). left.
    apply real_log_lt_mono. exact Hlt.
  - apply r_le_of_eq. apply real_log_wd. exact Heq.
Qed.

(* Subtraction move: a <= b + c implies a - c <= b (Set-sorted reals). *)
Lemma z01_le_plus_opp_r : forall a b c : Real,
  real_le a (real_plus b c) ->
  real_le (real_plus a (real_opp c)) b.
Proof.
  intros a b c H.
  apply (real_le_trans (real_plus a (real_opp c))
          (real_plus (real_plus b c) (real_opp c)) b).
  - apply real_le_plus_compat; [exact H | apply real_le_refl].
  - apply r_le_of_eq.
    apply (real_eq_trans (real_plus (real_plus b c) (real_opp c))
            (real_plus b (real_plus c (real_opp c))) b).
    + exact (real_eq_sym (real_plus b (real_plus c (real_opp c)))
               (real_plus (real_plus b c) (real_opp c))
               (real_plus_assoc b c (real_opp c))).
    + apply (real_eq_trans (real_plus b (real_plus c (real_opp c)))
              (real_plus b real_zero) b).
      * exact (RealSetoid.real_eq_plus_compat b (real_plus c (real_opp c)) b real_zero
                 (real_eq_refl b) (real_plus_opp c)).
      * apply (real_eq_trans (real_plus b real_zero) b b).
        { apply r_plus_zero_r_gen. }
        { apply real_eq_refl. }
Qed.

(* Addition cancel on the right: y + (x - y) == x. *)
Lemma z01_add_cancel_r : forall x y : Real,
  real_eq (real_plus y (real_plus x (real_opp y))) x.
Proof.
  intros x y.
  apply (real_eq_trans (real_plus y (real_plus x (real_opp y)))
          (real_plus (real_plus y x) (real_opp y)) x).
  - exact (real_plus_assoc y x (real_opp y)).
  - apply (real_eq_trans (real_plus (real_plus y x) (real_opp y))
            (real_plus (real_plus x y) (real_opp y)) x).
    + exact (RealSetoid.real_eq_plus_compat (real_plus y x) (real_opp y)
               (real_plus x y) (real_opp y) (real_plus_comm y x)
               (real_eq_refl (real_opp y))).
    + apply (real_eq_trans (real_plus (real_plus x y) (real_opp y))
              (real_plus x (real_plus y (real_opp y))) x).
      * exact (real_eq_sym (real_plus x (real_plus y (real_opp y)))
                 (real_plus (real_plus x y) (real_opp y))
                 (real_plus_assoc x y (real_opp y))).
      * apply (real_eq_trans (real_plus x (real_plus y (real_opp y)))
                 (real_plus x real_zero) x).
        { exact (RealSetoid.real_eq_plus_compat x (real_plus y (real_opp y)) x real_zero
                   (real_eq_refl x) (real_plus_opp y)). }
        { apply r_plus_zero_r_gen. }
Qed.

(* The weight carrier: Lambda(n) = ln lcm(1..n) - ln lcm(1..n-1), with   *)
(* the canonical positivity witnesses; total in n (Lambda(0) = 0).       *)
Definition z01_lam (n : nat) : Real :=
  real_plus
    (real_log (nat_real (z01_lcmn n)) (z01_lcm_pos_l n))
    (real_opp
       (real_log (nat_real (z01_lcmn (Nat.pred n))) (z01_lcm_pos_l (Nat.pred n)))).

(* The weight bound: Lambda(S n) <= ln (S n) (the termwise input of the   *)
(* absolute-convergence machine). *)
Lemma z01_lam_le_S : forall n : nat,
  real_le (z01_lam (S n))
          (real_log (nat_real (S n)) (nat_real_pos (S n) (NatLe_one_S n))).
Proof.
  intro n. unfold z01_lam. cbn [Nat.pred].
  assert (Hstep : (z01_lcmn (S n) <= S n * z01_lcmn n)%nat)
    by exact (z01_lcmn_step n).
  apply z01_le_plus_opp_r.
  apply (real_le_trans
           (real_log (nat_real (z01_lcmn (S n))) (z01_lcm_pos_l ((S n))))
           (real_log (real_mult (nat_real (S n)) (nat_real (z01_lcmn n)))
              (real_mult_positive (nat_real (S n)) (nat_real (z01_lcmn n))
                 (nat_real_pos (S n) (NatLe_one_S n))
                 (z01_lcm_pos_l n)))
           (real_plus (real_log (nat_real (S n)) (nat_real_pos (S n) (NatLe_one_S n)))
                      (real_log (nat_real (z01_lcmn n))
                         (z01_lcm_pos_l n)))).
  - apply z01_log_le_mono.
    apply (real_le_trans (nat_real (z01_lcmn (S n)))
             (nat_real (S n * z01_lcmn n))
             (real_mult (nat_real (S n)) (nat_real (z01_lcmn n)))).
    + apply z01_natreal_le. exact Hstep.
    + apply r_le_of_eq. apply nat_real_mul.
  - apply r_le_of_eq. apply real_log_mult.
Qed.

(* The weight is nonnegative (the fold is monotone). *)
Lemma z01_lam_ge0 : forall n : nat, real_le real_zero (z01_lam n).
Proof.
  intro n. unfold z01_lam. cbn [Nat.pred].
  apply (RealSetoid.real_le_compat
           (real_plus (real_log (nat_real (z01_lcmn (Nat.pred n)))
                        (z01_lcm_pos_l (Nat.pred n)))
                      (real_opp (real_log (nat_real (z01_lcmn (Nat.pred n)))
                                   (z01_lcm_pos_l (Nat.pred n)))))
           real_zero
           (real_plus (real_log (nat_real (z01_lcmn n)) (z01_lcm_pos_l n))
                      (real_opp (real_log (nat_real (z01_lcmn (Nat.pred n)))
                                   (z01_lcm_pos_l (Nat.pred n)))))
           (real_plus (real_log (nat_real (z01_lcmn n)) (z01_lcm_pos_l n))
                      (real_opp (real_log (nat_real (z01_lcmn (Nat.pred n)))
                                   (z01_lcm_pos_l (Nat.pred n)))))
           (real_plus_opp (real_log (nat_real (z01_lcmn (Nat.pred n)))
                               (z01_lcm_pos_l (Nat.pred n))))
           (real_eq_refl _)).
  apply real_le_plus_compat.
  - apply z01_log_le_mono.
    apply z01_natreal_le. apply z01_lcmn_mono.
    destruct n; [ apply Nat.le_refl | apply Nat.le_succ_diag_r ].
  - apply real_le_refl.
Qed.

(* ===================================================================== *)
(* Section 2. The unweighted telescope: the psi face of the Lambda series.*)
(* ===================================================================== *)

Fixpoint z01_mansum (N : nat) : Real :=
  match N with
  | O => real_zero
  | S m => real_plus (z01_mansum m) (z01_lam (S m))
  end.

(* The telescope identity: sum_{n<=N} Lambda(n) = ln lcm(1..N).  This is  *)
(* the tree-native finite form of the ZZ theory fds_mangoldt_eq identity  *)
(* route (the psi face). *)
Theorem z01_telescope : forall N : nat,
  real_eq (z01_mansum N)
          (real_log (nat_real (z01_lcmn N)) (z01_lcm_pos_l N)).
Proof.
  intro N. induction N as [|N IH].
  - cbn [z01_mansum].
    apply (real_eq_trans real_zero (real_log real_one real_lt_zero_one)
             (real_log (nat_real (z01_lcmn 0)) (z01_lcm_pos_l 0))).
    + apply real_eq_sym. apply real_log_one.
    + apply real_log_wd. apply real_eq_sym. apply nat_real_one.
  - cbn [z01_mansum].
    apply (real_eq_trans (real_plus (z01_mansum N) (z01_lam (S N)))
             (real_plus (real_log (nat_real (z01_lcmn N)) (z01_lcm_pos_l N))
                        (z01_lam (S N)))
             (real_log (nat_real (z01_lcmn (S N))) (z01_lcm_pos_l (S N)))).
    + exact (RealSetoid.real_eq_plus_compat (z01_mansum N) (z01_lam (S N))
               (real_log (nat_real (z01_lcmn N)) (z01_lcm_pos_l N))
               (z01_lam (S N)) IH (real_eq_refl (z01_lam (S N)))).
    + exact (z01_add_cancel_r
               (real_log (nat_real (z01_lcmn (S N))) (z01_lcm_pos_l (S N)))
               (real_log (nat_real (z01_lcmn N)) (z01_lcm_pos_l N))).
Qed.

(* ===================================================================== *)
(* Section 3. The convergence faces (premise-parametrised, GAPASUME       *)
(* family; every premise declaration leaves as an explicit argument).     *)
(* ===================================================================== *)

Section Z01Conv.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable sig : Real.
Hypothesis Hsig1 : real_lt real_one sig.
(* GAPASUME slot L-Z01-A (L0 stock, the C2.02 slot L-C2.02-A shape):       *)
(* strict monotonicity of the tree real log on the embedded naturals. *)
Hypothesis Hlnmono :
  forall (m n : nat) (Hm : real_lt real_zero (nat_real m))
    (Hn : real_lt real_zero (nat_real n)),
    real_lt (nat_real m) (nat_real n) ->
    real_lt (real_log (nat_real m) Hm) (real_log (nat_real n) Hn).
(* GAPASUME slot L-Z01-B (L0 stock, the C2.02 slot L-C2.02-B shape):       *)
(* ln 2 > 0. *)
Hypothesis Hln2pos :
  real_lt real_zero (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1))).

(* ---- Wrapper faces: one registered qualified consumption row each ---- *)

Definition z01_ln (n : nat) (Hn : NatLe 1 n) : Real :=
  real_log (nat_real n) (Hnpos n Hn).

Definition z01_npow (n : nat) (Hn : NatLe 1 n) : Real :=
  r_npow Hnpos sig n Hn.

Definition z01_rtsum (M N : nat) : Real := r_tsum Hnpos sig M N.

Definition z01_rtail (M N : nat) : Real := r_tail Hnpos sig M N.

Definition z01_m1sig (M : nat) (HM : NatLe 1 M) : Real := r_m1sig Hnpos sig M HM.

Definition z01_geom : Real := r_geom_const Hnpos sig Hsig1 Hln2pos.

Definition z01_m1sig0 (sig0 : Real) (M : nat) (HM : NatLe 1 M) : Real :=
  r_m1sig Hnpos sig0 M HM.

Definition z01_geom0 (sig0 : Real) (Hs01 : real_lt real_one sig0) : Real :=
  r_geom_const Hnpos sig0 Hs01 Hln2pos.

(* The premise witness of the Section and the canonical Section-1 witness  *)
(* agree on the log (real_log is witness-sensitive; the congruence closes  *)
(* the gap). *)
Lemma z01_ln_lam_le : forall (n : nat) (Hn : NatLe 1 n),
  real_le (z01_lam n) (z01_ln n Hn).
Proof.
  intros n Hn. destruct n as [|n'].
  - destruct (NatLe_1_zero_empty Hn).
  - apply (RealSetoid.real_le_compat (z01_lam (S n')) (z01_lam (S n'))
             (real_log (nat_real (S n')) (nat_real_pos (S n') (NatLe_one_S n')))
             (z01_ln (S n') Hn)
             (real_eq_refl (z01_lam (S n')))
             (real_log_wd (nat_real (S n')) (nat_real (S n'))
                (nat_real_pos (S n') (NatLe_one_S n')) (Hnpos (S n') Hn)
                (real_eq_refl (nat_real (S n'))))).
    apply z01_lam_le_S.
Qed.

(* The log weight of S N is positive once N >= 1 (the S N >= 2 face). *)
Lemma z01_ln_sn_pos : forall (N : nat), NatLe 1 N ->
  real_lt real_zero (z01_ln (S N) (NatLe_one_S N)).
Proof.
  intros N HN1. destruct N as [|n]; [ destruct (NatLe_1_zero_empty HN1) |].
  destruct n as [|n'].
  - exact Hln2pos.
  - apply (real_lt_trans real_zero
             (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))
             (real_log (nat_real (S (S (S n'))))
                       (Hnpos (S (S (S n'))) (NatLe_one_S (S (S n')))))).
    + exact Hln2pos.
    + apply real_log_lt_mono. apply nat_real_lt. apply NatLe_lift. lia.
Qed.

(* ---- The Lambda-weighted real tail sums ---- *)

Fixpoint z01_rmantail (M N : nat) : Real :=
  match N with
  | O => real_zero
  | S m => real_plus (z01_rmantail M m)
             (if Nat.ltb M (S m) then
                real_mult (z01_lam (S m)) (z01_npow (S m) (NatLe_one_S m))
              else real_zero)
  end.

Lemma z01_rtsum_S : forall M N : nat,
  z01_rtsum M (S N) =
  real_plus (z01_rtsum M N)
    (if Nat.ltb M (S N) then z01_npow (S N) (NatLe_one_S N) else real_zero).
Proof. reflexivity. Qed.

Lemma z01_rtsum_zero : forall M N : nat, NatLe N M ->
  real_eq (z01_rtsum M N) real_zero.
Proof. intros M N H. exact (r_tsum_zero_le Hnpos sig M N H). Qed.

Lemma z01_rmantail_zero : forall M N : nat, NatLe N M ->
  real_eq (z01_rmantail M N) real_zero.
Proof.
  intros M N. revert M. induction N as [|N IH]; intros M HNM.
  - cbn [z01_rmantail]. apply real_eq_refl.
  - cbn [z01_rmantail].
    assert (HLtb : Nat.ltb M (S N) = false)
      by (apply Nat.ltb_ge; apply NatLe_drop; exact HNM).
    rewrite HLtb.
    apply (real_eq_trans (real_plus (z01_rmantail M N) real_zero)
             (z01_rmantail M N) real_zero).
    + apply r_plus_zero_r_gen.
    + apply IH. apply NatLe_lift.
      apply Nat.le_trans with (S N);
        [ apply Nat.le_succ_diag_r | apply NatLe_drop; exact HNM ].
Qed.

(* The weighted tail is nonnegative. *)
Lemma z01_rmantail_ge0 : forall M N : nat, real_le real_zero (z01_rmantail M N).
Proof.
  intros M. induction N as [|N IH].
  - cbn [z01_rmantail]. apply real_le_refl.
  - cbn [z01_rmantail]. destruct (Nat.ltb M (S N)).
    + apply (real_le_trans real_zero (real_plus real_zero real_zero)
               (real_plus (z01_rmantail M N)
                  (real_mult (z01_lam (S N)) (z01_npow (S N) (NatLe_one_S N))))).
      * apply r_le_of_eq. apply real_eq_sym. apply r_plus_zero_l_gen.
      * apply real_le_plus_compat; [ exact IH |].
        apply (real_le_trans real_zero
                 (real_mult real_zero (z01_npow (S N) (NatLe_one_S N)))
                 (real_mult (z01_lam (S N)) (z01_npow (S N) (NatLe_one_S N)))).
        { apply r_le_of_eq. apply real_eq_sym.
          apply (real_eq_trans
                   (real_mult real_zero (z01_npow (S N) (NatLe_one_S N)))
                   (real_mult (z01_npow (S N) (NatLe_one_S N)) real_zero) real_zero).
          - apply real_mult_comm.
          - apply real_mult_zero. }
        { apply (real_le_mult_compat_weak real_zero (z01_lam (S N))
                   (z01_npow (S N) (NatLe_one_S N))).
          - apply (real_lt_le_iff real_zero (z01_npow (S N) (NatLe_one_S N))). left.
            exact (r_npow_pos Hnpos sig (S N) (NatLe_one_S N)).
          - exact (z01_lam_ge0 (S N)). }
    + apply (RealSetoid.real_le_compat real_zero real_zero
               (z01_rmantail M N) (real_plus (z01_rmantail M N) real_zero)
               (real_eq_refl real_zero)
               (real_eq_sym _ _ (r_plus_zero_r_gen (z01_rmantail M N)))).
      exact IH.
Qed.

(* Termwise dominance: Lambda(j) * j^-sig <= ln(S N) * j^-sig on the block. *)
Lemma z01_term_le_ln : forall (N j : nat) (Hj : NatLe 1 j),
  NatLe j N ->
  real_le (real_mult (z01_lam j) (z01_npow j Hj))
          (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_npow j Hj)).
Proof.
  intros N j Hj HjN.
  apply (real_le_mult_compat_weak (z01_lam j)
           (z01_ln (S N) (NatLe_one_S N)) (z01_npow j Hj)).
  - apply (real_lt_le_iff real_zero (z01_npow j Hj)). left.
    exact (r_npow_pos Hnpos sig j Hj).
  - apply (real_le_trans (z01_lam j) (z01_ln j Hj)
             (z01_ln (S N) (NatLe_one_S N))).
    + exact (z01_ln_lam_le j Hj).
    + apply z01_log_le_mono.
      apply z01_natreal_le.
      apply Nat.le_trans with N;
        [ apply NatLe_drop; exact HjN | apply Nat.le_succ_diag_r ].
Qed.

(* Block dominance: the weighted tail is at most c * (unweighted tail)    *)
(* whenever the terms are dominated termwise. *)
Lemma z01_rmantail_le_scale : forall (N M : nat) (c : Real), NatLe M N ->
  (forall (j : nat) (Hj : NatLe 1 j), NatLe (S M) j -> NatLe j N ->
     real_le (real_mult (z01_lam j) (z01_npow j Hj))
             (real_mult c (z01_npow j Hj))) ->
  real_le (z01_rmantail M N) (real_mult c (z01_rtsum M N)).
Proof.
  intros N. induction N as [|N IH]; intros M c Hle Hbnd.
  - cbn [z01_rmantail]. unfold z01_rtsum. cbn [r_tsum].
    apply r_le_of_eq. apply real_eq_sym. apply real_mult_zero.
  - rewrite z01_rtsum_S. cbn [z01_rmantail].
    destruct (Nat.ltb M (S N)) eqn:HLtb.
    + assert (Hlt : (M < S N)%nat) by exact (proj1 (Nat.ltb_lt M (S N)) HLtb).
      assert (HMN : NatLe M N) by (apply NatLe_lift; lia).
      assert (Hdist : real_eq
               (real_mult c (real_plus (z01_rtsum M N)
                            (z01_npow (S N) (NatLe_one_S N))))
               (real_plus (real_mult c (z01_rtsum M N))
                          (real_mult c (z01_npow (S N) (NatLe_one_S N))))).
      { apply (real_eq_trans
                 (real_mult c (real_plus (z01_rtsum M N)
                              (z01_npow (S N) (NatLe_one_S N))))
                 (real_mult (real_plus (z01_rtsum M N)
                              (z01_npow (S N) (NatLe_one_S N))) c)).
        - apply real_mult_comm.
        - exact (real_eq_trans
                   (real_mult (real_plus (z01_rtsum M N)
                                (z01_npow (S N) (NatLe_one_S N))) c)
                   (real_plus (real_mult (z01_rtsum M N) c)
                              (real_mult (z01_npow (S N) (NatLe_one_S N)) c))
                   (real_plus (real_mult c (z01_rtsum M N))
                              (real_mult c (z01_npow (S N) (NatLe_one_S N))))
                   (r_mult_plus_distr (z01_rtsum M N)
                      (z01_npow (S N) (NatLe_one_S N)) c)
                   (RealSetoid.real_eq_plus_compat
                      (real_mult (z01_rtsum M N) c)
                      (real_mult (z01_npow (S N) (NatLe_one_S N)) c)
                      (real_mult c (z01_rtsum M N))
                      (real_mult c (z01_npow (S N) (NatLe_one_S N)))
                      (real_mult_comm (z01_rtsum M N) c)
                      (real_mult_comm (z01_npow (S N) (NatLe_one_S N)) c))). }
      apply (real_le_trans
               (real_plus (z01_rmantail M N)
                  (real_mult (z01_lam (S N)) (z01_npow (S N) (NatLe_one_S N))))
               (real_plus (real_mult c (z01_rtsum M N))
                          (real_mult c (z01_npow (S N) (NatLe_one_S N))))).
      * apply real_le_plus_compat.
        { apply IH; [ exact HMN |].
          intros j Hj Hj1 Hj2.
          apply Hbnd; [ exact Hj1 | apply NatLe_lift; apply Nat.le_trans with N;
                        [ apply NatLe_drop; exact Hj2 | apply Nat.le_succ_diag_r ] ]. }
        { apply (Hbnd (S N) (NatLe_one_S N)).
          - apply NatLe_lift. lia.
          - apply NatLe_lift. apply Nat.le_refl. }
      * apply r_le_of_eq. apply real_eq_sym. exact Hdist.
    + assert (Hge : (S N <= M)%nat) by exact (proj1 (Nat.ltb_ge M (S N)) HLtb).
      assert (HMeq : M = S N)
        by (apply Nat.le_antisymm; [ apply NatLe_drop; exact Hle | exact Hge ]).
      subst M. cbn [z01_rmantail].
      apply r_le_of_eq.
      apply (real_eq_trans
               (real_plus (z01_rmantail (S N) N) real_zero)
               real_zero
               (real_mult c (real_plus (z01_rtsum (S N) N) real_zero))).
      * apply (real_eq_trans (real_plus (z01_rmantail (S N) N) real_zero)
                 (z01_rmantail (S N) N) real_zero).
        { apply r_plus_zero_r_gen. }
        { apply z01_rmantail_zero. apply NatLe_lift. apply Nat.le_succ_diag_r. }
      * apply real_eq_sym.
        apply (real_eq_trans
                 (real_mult c (real_plus (z01_rtsum (S N) N) real_zero))
                 (real_mult c (z01_rtsum (S N) N)) real_zero).
        { exact (RealSetoid.real_eq_mult_compat c
                   (real_plus (z01_rtsum (S N) N) real_zero) c
                   (z01_rtsum (S N) N) (real_eq_refl c)
                   (r_plus_zero_r_gen (z01_rtsum (S N) N))). }
        { apply (real_eq_trans (real_mult c (z01_rtsum (S N) N))
                   (real_mult c real_zero) real_zero).
          { exact (RealSetoid.real_eq_mult_compat c (z01_rtsum (S N) N) c real_zero
                     (real_eq_refl c)
                     (z01_rtsum_zero (S N) N
                        (NatLe_lift N (S N) (Nat.le_succ_diag_r N)))). }
          { apply real_mult_zero. } }
Qed.

(* The block form of the dominance at the log weight. *)
Lemma z01_rmantail_le_lnrtail : forall (M N : nat)
    (HM : NatLe 1 M) (HMN : NatLe M N),
  real_le (z01_rmantail M N)
          (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_rtail M N)).
Proof.
  intros M N HM HMN.
  assert (H : real_le (z01_rmantail M N)
                (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_rtsum M N))).
  { apply (z01_rmantail_le_scale N M (z01_ln (S N) (NatLe_one_S N)) HMN).
    intros j Hj Hj1 Hj2. apply z01_term_le_ln. exact Hj2. }
  apply (RealSetoid.real_le_compat
           (z01_rmantail M N) (z01_rmantail M N)
           (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_rtsum M N))
           (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_rtail M N))
           (real_eq_refl (z01_rmantail M N))).
  - apply (RealSetoid.real_eq_mult_compat (z01_ln (S N) (NatLe_one_S N))
             (z01_rtsum M N) (z01_ln (S N) (NatLe_one_S N)) (z01_rtail M N)
             (real_eq_refl (z01_ln (S N) (NatLe_one_S N)))).
    exact (r_tsum_r_tail Hnpos sig M N).
  - exact H.
Qed.

(* ---- The explicit bound constant ---- *)

Definition z01_bound (M N : nat) (HM : NatLe 1 M) : Real :=
  real_mult (z01_ln (S N) (NatLe_one_S N))
            (real_mult (z01_m1sig M HM) z01_geom).

Definition z01_bound0 (sig0 : Real) (Hs01 : real_lt real_one sig0)
    (M N : nat) (HM : NatLe 1 M) : Real :=
  real_mult (z01_ln (S N) (NatLe_one_S N))
            (real_mult (z01_m1sig0 sig0 M HM) (z01_geom0 sig0 Hs01)).

(* ---- Main theorem 1 (the absolute-convergence bound at sigma) ---- *)

Theorem z01_absconv_bound : forall (M N : nat) (HM : NatLe 1 M) (HMN : NatLe M N),
  real_lt (z01_rmantail M N) (z01_bound M N HM).
Proof.
  intros M N HM HMN.
  assert (HN1 : NatLe 1 N)
    by (apply NatLe_lift;
        apply Nat.le_trans with M;
          [ apply NatLe_drop; exact HM | apply NatLe_drop; exact HMN ]).
  apply (real_le_lt_trans (z01_rmantail M N)
           (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_rtail M N))
           (z01_bound M N HM)).
  - exact (z01_rmantail_le_lnrtail M N HM HMN).
  - unfold z01_bound. apply real_lt_mult_compat.
    + exact (z01_ln_sn_pos N HN1).
    + exact (condensation_tail_bound Hnpos sig Hsig1 Hlnmono Hln2pos M N HM HMN).
Qed.

(* ---- Main theorem 2 (the uniform face: sigma0 <= sigma; the card's     *)
(*      Re s >= 1 + delta face is the instance sigma0 = 1 + delta) ----   *)

Theorem z01_absconv_uniform : forall (sig0 : Real) (Hs01 : real_lt real_one sig0)
    (Hs0s : real_le sig0 sig) (M N : nat) (HM : NatLe 1 M) (HMN : NatLe M N),
  real_lt (z01_rmantail M N) (z01_bound0 sig0 Hs01 M N HM).
Proof.
  intros sig0 Hs01 Hs0s M N HM HMN.
  assert (HN1 : NatLe 1 N)
    by (apply NatLe_lift;
        apply Nat.le_trans with M;
          [ apply NatLe_drop; exact HM | apply NatLe_drop; exact HMN ]).
  apply (real_le_lt_trans (z01_rmantail M N)
           (real_mult (z01_ln (S N) (NatLe_one_S N)) (z01_rtail M N))
           (z01_bound0 sig0 Hs01 M N HM)).
  - exact (z01_rmantail_le_lnrtail M N HM HMN).
  - unfold z01_bound0. apply real_lt_mult_compat.
    + exact (z01_ln_sn_pos N HN1).
    + exact (tail_bound_uniform Hnpos sig Hsig1 Hlnmono Hln2pos
               sig0 Hs01 Hs0s M N HM HMN).
Qed.

(* ---- The Cx Lambda-weighted series (complex exponent s) ---- *)

Fixpoint z01_manpart (N : nat) (s : Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (z01_manpart m s)
             (c_scale (z01_lam (S m)) (c_powq Hnpos (S m) (NatLe_one_S m) s))
  end.

Fixpoint z01_mantail (M N : nat) (s : Cx) : Cx :=
  match N with
  | O => c_zero
  | S m => c_plus (z01_mantail M m s)
             (if Nat.ltb M (S m) then
                c_scale (z01_lam (S m)) (c_powq Hnpos (S m) (NatLe_one_S m) s)
              else c_zero)
  end.

Lemma z01_mantail_zero : forall (N M : nat) (s : Cx), NatLe N M ->
  c_eq (z01_mantail M N s) c_zero.
Proof.
  intros N M s. revert M. induction N as [|N IH]; intros M HNM.
  - cbn [z01_mantail]. apply c_eq_refl.
  - cbn [z01_mantail].
    assert (HLtb : Nat.ltb M (S N) = false)
      by (apply Nat.ltb_ge; apply NatLe_drop; exact HNM).
    rewrite HLtb.
    apply (c_eq_trans (c_plus (z01_mantail M N s) c_zero)
             (z01_mantail M N s) c_zero).
    + apply c_plus_zero_r.
    + apply IH. apply NatLe_lift.
      apply Nat.le_trans with (S N);
        [ apply Nat.le_succ_diag_r | apply NatLe_drop; exact HNM ].
Qed.

(* Tail difference identity for the Lambda-weighted Cx partial sums       *)
(* (mirrors the C2.01 tail identity). *)
Lemma z01_mantail_diff : forall (N M : nat) (s : Cx), NatLe M N ->
  c_eq (c_plus (z01_manpart N s) (c_opp (z01_manpart M s)))
       (z01_mantail M N s).
Proof.
  intros N M s HMN. revert M HMN.
  induction N as [|N IH]; intros M HMN.
  - assert (HM0 : M = 0%nat) by (apply Nat.le_0_r; apply NatLe_drop; exact HMN).
    subst M. cbn [z01_manpart z01_mantail]. apply c_plus_opp.
  - cbn [z01_manpart]. destruct (Nat.ltb M (S N)) eqn:HLtb.
    + cbn [z01_mantail]. rewrite HLtb.
      assert (Hlt : (M < S N)%nat) by exact (proj1 (Nat.ltb_lt M (S N)) HLtb).
      assert (HMN0 : NatLe M N) by (apply NatLe_lift; lia).
      apply (c_eq_trans
               (c_plus (c_plus (z01_manpart N s)
                          (c_scale (z01_lam (S N))
                             (c_powq Hnpos (S N) (NatLe_one_S N) s)))
                       (c_opp (z01_manpart M s)))
               (c_plus (z01_manpart N s)
                  (c_plus (c_scale (z01_lam (S N))
                               (c_powq Hnpos (S N) (NatLe_one_S N) s))
                          (c_opp (z01_manpart M s))))).
      * apply c_eq_sym. apply c_plus_assoc.
      * apply (c_eq_trans
                 (c_plus (z01_manpart N s)
                    (c_plus (c_scale (z01_lam (S N))
                                 (c_powq Hnpos (S N) (NatLe_one_S N) s))
                            (c_opp (z01_manpart M s))))
                 (c_plus (z01_manpart N s)
                    (c_plus (c_opp (z01_manpart M s))
                       (c_scale (z01_lam (S N))
                          (c_powq Hnpos (S N) (NatLe_one_S N) s))))).
        { apply c_plus_congr; [ apply c_eq_refl | apply c_plus_comm ]. }
        { apply (c_eq_trans
                   (c_plus (z01_manpart N s)
                      (c_plus (c_opp (z01_manpart M s))
                         (c_scale (z01_lam (S N))
                            (c_powq Hnpos (S N) (NatLe_one_S N) s))))
                   (c_plus (c_plus (z01_manpart N s) (c_opp (z01_manpart M s)))
                      (c_scale (z01_lam (S N))
                         (c_powq Hnpos (S N) (NatLe_one_S N) s)))
                   (c_plus (z01_mantail M N s)
                      (c_scale (z01_lam (S N))
                         (c_powq Hnpos (S N) (NatLe_one_S N) s)))).
          { apply c_plus_assoc. }
          { apply c_plus_congr; [ apply IH; exact HMN0 | apply c_eq_refl ]. } }
    + assert (Hge : (S N <= M)%nat) by exact (proj1 (Nat.ltb_ge M (S N)) HLtb).
      assert (HMSm : S N = M)
        by (apply Nat.le_antisymm; [ exact Hge | apply NatLe_drop; exact HMN ]).
      rewrite <- HMSm. cbn [z01_manpart z01_mantail].
      assert (HLtb2 : Nat.ltb (S N) (S N) = false)
        by (apply Nat.ltb_ge; apply Nat.le_refl).
      rewrite HLtb2.
      apply (c_eq_trans
               (c_plus (c_plus (z01_manpart N s)
                          (c_scale (z01_lam (S N))
                             (c_powq Hnpos (S N) (NatLe_one_S N) s)))
                       (c_opp (c_plus (z01_manpart N s)
                                  (c_scale (z01_lam (S N))
                                     (c_powq Hnpos (S N) (NatLe_one_S N) s)))))
               c_zero).
      * apply c_plus_opp.
      * apply c_eq_sym.
        apply (c_eq_trans (c_plus (z01_mantail (S N) N s) c_zero)
                 (z01_mantail (S N) N s) c_zero).
        { apply c_plus_zero_r. }
        { apply z01_mantail_zero. apply NatLe_lift. apply Nat.le_succ_diag_r. }
Qed.

(* ---- Main theorem 3 (the Cx Cauchy rational-margin face) ---- *)
(* GAPASUME slot L-Z01-C (open supply face, the weighted sibling of the    *)
(* C2.02 slot L-C2.02-C): the n-fold triangle inequality in rational-      *)
(* margin form for the Lambda-weighted tail.  The tree has no real_abs     *)
(* face and no n-fold Cauchy-Schwarz face; supply route = the C1.4         *)
(* convergence-engine extension (GaC1_14 style). *)
Hypothesis Hnormlam :
  forall (M N : nat) (s : Cx) (d : Q), real_eq (cRe s) sig -> QltT 0 d ->
    real_lt (c_norm_sq (z01_mantail M N s))
            (real_plus (real_mult (z01_rmantail M N) (z01_rmantail M N))
                       (real_const d)).

Theorem z01_cauchy_bound : forall (M N : nat) (HM : NatLe 1 M) (HMN : NatLe M N)
    (s : Cx) (d : Q),
  real_eq (cRe s) sig -> QltT 0 d ->
  real_lt (c_norm_sq (c_plus (z01_manpart N s) (c_opp (z01_manpart M s))))
          (real_plus (real_mult (z01_bound M N HM) (z01_bound M N HM))
                     (real_const d)).
Proof.
  intros M N HM HMN s d Hs Hd.
  assert (Hdiff : c_eq (c_plus (z01_manpart N s) (c_opp (z01_manpart M s)))
                       (z01_mantail M N s))
    by exact (z01_mantail_diff N M s HMN).
  apply (real_lt_le_trans
           (c_norm_sq (c_plus (z01_manpart N s) (c_opp (z01_manpart M s))))
           (real_plus (real_mult (z01_rmantail M N) (z01_rmantail M N))
                      (real_const d))
           (real_plus (real_mult (z01_bound M N HM) (z01_bound M N HM))
                      (real_const d))).
  - apply (real_eq_lt_lt _ (c_norm_sq (z01_mantail M N s))).
    { apply c_norm_sq_wd. exact Hdiff. }
    { exact (Hnormlam M N s d Hs Hd). }
  - assert (HN1 : NatLe 1 N)
      by (apply NatLe_lift;
          apply Nat.le_trans with M;
            [ apply NatLe_drop; exact HM | apply NatLe_drop; exact HMN ]).
    assert (HB : real_le (z01_rmantail M N) (z01_bound M N HM))
      by (apply (real_lt_le_iff (z01_rmantail M N) (z01_bound M N HM)); left;
          exact (z01_absconv_bound M N HM HMN)).
    assert (HT0 : real_le real_zero (z01_rmantail M N))
      by exact (z01_rmantail_ge0 M N).
    assert (HB0 : real_lt real_zero (z01_bound M N HM)).
    { unfold z01_bound. apply real_mult_positive.
      - exact (z01_ln_sn_pos N HN1).
      - apply real_mult_positive;
          [ exact (r_m1sig_pos Hnpos sig M HM)
          | exact (r_geom_const_pos Hnpos sig Hsig1 Hln2pos) ]. }
    assert (HB0le : real_le real_zero (z01_bound M N HM))
      by (apply (real_lt_le_iff real_zero (z01_bound M N HM)); left; exact HB0).
    apply real_le_plus_compat; [| apply real_le_refl].
    apply (real_le_trans
             (real_mult (z01_rmantail M N) (z01_rmantail M N))
             (real_mult (z01_bound M N HM) (z01_rmantail M N))
             (real_mult (z01_bound M N HM) (z01_bound M N HM))).
    + exact (real_le_mult_compat_weak (z01_rmantail M N) (z01_bound M N HM)
               (z01_rmantail M N) HT0 HB).
    + apply (RealSetoid.real_le_compat
               (real_mult (z01_rmantail M N) (z01_bound M N HM))
               (real_mult (z01_bound M N HM) (z01_rmantail M N))
               (real_mult (z01_bound M N HM) (z01_bound M N HM))
               (real_mult (z01_bound M N HM) (z01_bound M N HM))
               (real_mult_comm (z01_rmantail M N) (z01_bound M N HM))
               (real_eq_refl (real_mult (z01_bound M N HM) (z01_bound M N HM)))).
      exact (real_le_mult_compat_weak (z01_rmantail M N) (z01_bound M N HM)
               (z01_bound M N HM) HB0le HB).
Qed.

End Z01Conv.
