(* sl1_lzn_assembly.v - the L_n band assembly from the two band faces.
   Ticket: SL12 ticket SL1 (psi band + Phi window construction seat).
   Mission: prove the assembly theorem of the SL1 topology: the lcm
   band at base B, the Phi-window band at base C from the offset N,
   and the exact division planb4_LZn = planb4_L / planb4_Phi jointly
   yield the L_n band at base B / C. Every premise is a Set-carried
   certificate; the two heavy band certificates remain honestly open
   debts. The Q-side toolkit (power step, monotonicity, power division,
   inverse monotonicity, sign transfers) is built transparently from
   stdlib Q lemmas; one field identity closes by the field normalizer
   as bookkeeping.
   Inventory: 1 Theorem (sl1_lzn_from_bands, Defined) + 11 lemmas,
   1 anchor Example.
   Dependencies: S02_CauchyComplete; planb4_g1_witness; sl1_phase_faces;
   sl1_phi_divides_L; stdlib QArith, ZArith, Qpower, List, Lia,
   QArith.Qring (field normalizer on the auxiliary identity only).
   References: slot statement draft SL12 section 1 (joint topology);
   survey volume sections 4.1/5 (budget coupling; integer pairing
   B = 65, C = 34/25, B/C = 1625/34 <= 48).
   NOT claimed: no band certificate is supplied; they are hypotheses.
   Constructivity: Set-carried; zero global assumptions; solvers only
   as bookkeeping (nat/Z lia, one auxiliary Q field identity); the
   mission theorem closes by explicit combinator chains, Defined.
   Build: coqc -native-compiler no -q -Q world "" -Q out_sl1 ""
   sl1_lzn_assembly.v (E952 script form; after faces + divisibility). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
From Stdlib Require Import QArith.Qring.
Require Import S02_CauchyComplete.
Require Import planb4_g1_witness.
Require Import sl1_phase_faces.
Require Import sl1_phi_divides_L.

(* ==== Section 0: the head positivity anchor ==== *)

(* planb4_L 1 = 12 > 0, machine-checked; anchors the base positivity
   of B through the lcm face at n = 1. *)
Example sl1_L1_pos :
  S02_CauchyComplete.QltT 0 (inject_Z (Z.abs (planb4_L 1))).
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 1: Q-side power toolkit ==== *)

Lemma sl1_qpower_1 : forall x : Q, Qpower x 1 == x.
Proof. intros x. reflexivity. Defined.

Lemma sl1_qneq0_of_qltT0 :
  forall x : Q, S02_CauchyComplete.QltT 0 x -> ~ (x == 0)%Q.
Proof.
  intros x H Hx0.
  pose proof (S02_CauchyComplete.qeq_ltT x 0 Hx0 H) as H0.
  vm_compute in H0. inversion H0.
Defined.

Lemma sl1_qpower_step :
  forall (x : Q) (k : nat), ~ (x == 0)%Q ->
    Qpower x (Z.of_nat (S k)) == Qpower x (Z.of_nat k) * x.
Proof.
  intros x k Hx.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1)%Z by lia.
  rewrite (Qpower_plus x (Z.of_nat k) 1 Hx).
  rewrite sl1_qpower_1. reflexivity.
Defined.

Lemma sl1_qpower_pos_of_pos :
  forall (x : Q) (k : nat),
    S02_CauchyComplete.QltT 0 x ->
    S02_CauchyComplete.QltT 0 (Qpower x (Z.of_nat k)).
Proof.
  intros x k Hx. induction k as [|k IH].
  - pose proof (S02_CauchyComplete.qeq_ltT 1 (Qpower x (Z.of_nat 0))) as Hq.
    apply Hq.
    + reflexivity.
    + exact S02_CauchyComplete.qltT_0_1.
  - pose proof (S02_CauchyComplete.qeq_ltT
                  (Qpower x (Z.of_nat k) * x)
                  (Qpower x (Z.of_nat (S k)))) as Hq.
    apply Hq.
    + symmetry. exact (sl1_qpower_step x k (sl1_qneq0_of_qltT0 x Hx)).
    + apply S02_CauchyComplete.qmult_ltT_0_compat; assumption.
Defined.

Lemma sl1_qpower_neq0 :
  forall (x : Q) (k : nat),
    ~ (x == 0)%Q -> ~ (Qpower x (Z.of_nat k) == 0)%Q.
Proof.
  intros x k Hx. induction k as [|k IH].
  - intro Hz. vm_compute in Hz. inversion Hz.
  - intro Hz.
    rewrite (sl1_qpower_step x k Hx) in Hz.
    apply Qmult_integral in Hz.
    destruct Hz as [H1 | H2].
    + apply (IH H1).
    + contradiction.
Defined.

Lemma sl1_qpower_le_mono :
  forall (u v : Q) (k : nat),
    S02_CauchyComplete.QltT 0 u ->
    S02_CauchyComplete.QleT' u v ->
    S02_CauchyComplete.QleT'
      (Qpower u (Z.of_nat k)) (Qpower v (Z.of_nat k)).
Proof.
  intros u v k Hu Huv.
  assert (Hv : S02_CauchyComplete.QltT 0 v)
    by (apply (S02_CauchyComplete.qltT_leT'_ltT 0 u v); assumption).
  induction k as [|k IH].
  - apply S02_CauchyComplete.qeq_leT'. reflexivity.
  - apply S02_CauchyComplete.qleT'_trans
      with (Qpower u (Z.of_nat k) * u).
    + apply S02_CauchyComplete.qeq_leT'.
      apply sl1_qpower_step.
      intro Hz. exact (sl1_qneq0_of_qltT0 u Hu Hz).
    + apply S02_CauchyComplete.qleT'_trans
        with (Qpower v (Z.of_nat k) * u).
      * apply S02_CauchyComplete.qleT'_mult_compat_r.
        -- apply S02_CauchyComplete.qltT_leT'. exact Hu.
        -- exact IH.
      * apply S02_CauchyComplete.qleT'_trans
          with (Qpower v (Z.of_nat k) * v).
        -- apply S02_CauchyComplete.qleT'_mult_compat_l.
           ++ apply S02_CauchyComplete.qltT_leT'.
              apply sl1_qpower_pos_of_pos. exact Hv.
           ++ exact Huv.
        -- apply S02_CauchyComplete.qeq_leT'.
           symmetry.
           exact (sl1_qpower_step v k (sl1_qneq0_of_qltT0 v Hv)).
Defined.

(* ==== Section 2: Q-side inverse toolkit ==== *)

Lemma sl1_qinv_pos :
  forall z : Q,
    S02_CauchyComplete.QltT 0 z -> S02_CauchyComplete.QltT 0 (/ z).
Proof.
  intros z H.
  apply S02_CauchyComplete.Qlt_to_QltT.
  apply Qinv_lt_0_compat.
  apply S02_CauchyComplete.QltT_to_Qlt. exact H.
Defined.

Lemma sl1_qmul_div_cancel :
  forall x y : Q,
    ~ (x == 0)%Q -> ~ (y == 0)%Q -> y * / (x * y) == / x.
Proof.
  intros x y Hx Hy.
  assert (Hprem : x * (y * / (x * y)) == x * / x).
  { rewrite Qmult_assoc.
    rewrite (Qmult_inv_r (x * y))
      by (intro Hz; apply Qmult_integral in Hz;
          destruct Hz as [H1 | H2];
          [ contradiction | contradiction ]).
    rewrite (Qmult_inv_r x) by exact Hx.
    reflexivity. }
  exact (proj1 (Qmult_inj_l (y * / (x * y)) (/ x) x Hx) Hprem).
Defined.

Lemma sl1_qinv_le :
  forall x y : Q,
    S02_CauchyComplete.QltT 0 x ->
    S02_CauchyComplete.QltT 0 y ->
    S02_CauchyComplete.QleT' y x ->
    S02_CauchyComplete.QleT' (/ x) (/ y).
Proof.
  intros x y Hx Hy Hyx.
  assert (Hxy0 : S02_CauchyComplete.QltT 0 (x * y)).
  { apply S02_CauchyComplete.qmult_ltT_0_compat; assumption. }
  assert (Hm : S02_CauchyComplete.QleT' 0 (/ (x * y))).
  { apply S02_CauchyComplete.qltT_leT'.
    apply sl1_qinv_pos.
    exact Hxy0. }
  apply S02_CauchyComplete.qleT'_trans with (y * / (x * y)).
  - apply S02_CauchyComplete.qeq_leT'.
    symmetry.
    exact (sl1_qmul_div_cancel x y
             (sl1_qneq0_of_qltT0 x Hx) (sl1_qneq0_of_qltT0 y Hy)).
  - apply S02_CauchyComplete.qleT'_trans with (x * / (x * y)).
    + apply S02_CauchyComplete.qleT'_mult_compat_r.
      * exact Hm.
      * exact Hyx.
    + apply S02_CauchyComplete.qeq_leT'.
      rewrite (Qmult_comm x y).
      exact (sl1_qmul_div_cancel y x
               (sl1_qneq0_of_qltT0 y Hy) (sl1_qneq0_of_qltT0 x Hx)).
Defined.

(* ==== Section 3: the power-division identity (auxiliary field
       identity, bookkeeping normalizer) ==== *)

Lemma sl1_qdiv_mul_eq :
  forall a b c d : Q,
    ~ (c == 0)%Q -> ~ (d == 0)%Q ->
    (a / c) * (b / d) == (a * b) / (c * d).
Proof.
  intros a b c d Hc Hd. field.
  split.
  - exact Hd.
  - exact Hc.
Defined.

Lemma sl1_qpower_div_eq :
  forall (B C : Q) (k : nat),
    ~ (B == 0)%Q -> ~ (C == 0)%Q ->
    Qpower (B / C) (Z.of_nat k)
    == Qpower B (Z.of_nat k) / Qpower C (Z.of_nat k).
Proof.
  intros B C k HB HC.
  assert (HBC : ~ (B / C == 0)%Q).
  { intro Hz.
    unfold Qdiv in Hz.
    apply Qmult_integral in Hz.
    destruct Hz as [H1 | H2].
    - contradiction.
    - assert (Hc1 : (C * / C == 1)%Q) by (apply Qmult_inv_r; exact HC).
      rewrite H2 in Hc1.
      rewrite Qmult_0_r in Hc1.
      vm_compute in Hc1. inversion Hc1. }
  induction k as [|k IH].
  - reflexivity.
  - rewrite (sl1_qpower_step (B / C) k HBC).
    rewrite (sl1_qpower_step B k HB).
    rewrite (sl1_qpower_step C k HC).
    rewrite IH.
    rewrite (sl1_qdiv_mul_eq (Qpower B (Z.of_nat k)) B
               (Qpower C (Z.of_nat k)) C
               (sl1_qpower_neq0 C k HC) HC).
    reflexivity.
Defined.

(* ==== Section 4: injectivity bridge ==== *)

Lemma sl1_inject_Z_of_eq :
  forall a b : Z, a = b -> inject_Z a == inject_Z b.
Proof.
  intros a b H. subst. apply Qeq_refl.
Defined.

(* ==== Section 5: the assembly theorem (the SL1 conditional core) === *)

Theorem sl1_lzn_from_bands :
  forall (B C : Q) (N : nat),
    sl1_lcm_pow_bound_face B ->
    S02_CauchyComplete.QltT 0 C ->
    sl1_phi_pow_lower_from N C ->
    sl1_lzn_pow_bound_from N (B / C).
Proof.
  intros B C N Hcm Hc0 Hph n Hn.
  assert (HCn0 : S02_CauchyComplete.QltT 0 (Qpower C (Z.of_nat n)))
    by (apply sl1_qpower_pos_of_pos; exact Hc0).
  assert (HPhi0 : S02_CauchyComplete.QltT 0 (inject_Z (planb4_Phi n)))
    by apply sl1_phi_pos.
  assert (HB1lt : S02_CauchyComplete.QltT 0 (Qpower B (Z.of_nat 1))).
  { apply (S02_CauchyComplete.qltT_leT'_ltT 0 (inject_Z (Z.abs (planb4_L 1))) (Qpower B (Z.of_nat 1))).
    - exact sl1_L1_pos.
    - apply Hcm. }
  assert (HBpos : S02_CauchyComplete.QltT 0 B).
  { pose proof (S02_CauchyComplete.qeq_ltT (Qpower B (Z.of_nat 1)) B) as Hq.
    apply Hq.
    - apply sl1_qpower_1.
    - exact HB1lt. }
  assert (HBne : ~ (B == 0)%Q) by (apply (sl1_qneq0_of_qltT0 B HBpos)).
  assert (HCne : ~ (C == 0)%Q) by (apply (sl1_qneq0_of_qltT0 C Hc0)).
  assert (HBn0 : (0 <= Qpower B (Z.of_nat n))%Q).
  { apply S02_CauchyComplete.QleT'_to_Qle.
    apply S02_CauchyComplete.qleT'_trans
      with (inject_Z (Z.abs (planb4_L n))).
    - apply sl1_abs_L_nonneg.
    - apply Hcm. }
  assert (HabsL : inject_Z (Z.abs (planb4_L n)) == inject_Z (planb4_L n)).
  { apply sl1_inject_Z_of_eq.
    apply Z.abs_eq.
    pose proof (sl1_lcm_ge1 n). lia. }
  assert (HLle : (inject_Z (planb4_L n) <= Qpower B (Z.of_nat n))%Q).
  { apply S02_CauchyComplete.QleT'_to_Qle.
    apply S02_CauchyComplete.qleT'_trans
      with (inject_Z (Z.abs (planb4_L n))).
    - apply S02_CauchyComplete.qeq_leT'.
      symmetry. exact HabsL.
    - apply Hcm. }
  assert (HCle : (Qpower C (Z.of_nat n) <= inject_Z (planb4_Phi n))%Q)
    by (apply S02_CauchyComplete.QleT'_to_Qle; apply Hph; exact Hn).
  assert (Hinv : (/ inject_Z (planb4_Phi n)
                   <= / Qpower C (Z.of_nat n))%Q).
  { apply S02_CauchyComplete.QleT'_to_Qle.
    apply sl1_qinv_le.
    - exact HPhi0.
    - exact HCn0.
    - apply S02_CauchyComplete.Qle_to_QleT'. exact HCle. }
  assert (Hinv0 : (0 <= / inject_Z (planb4_Phi n))%Q).
  { apply S02_CauchyComplete.QleT'_to_Qle.
    apply S02_CauchyComplete.qltT_leT'.
    apply sl1_qinv_pos. exact HPhi0. }
  assert (HabsZ : inject_Z (Z.abs (planb4_LZn n)) == inject_Z (planb4_LZn n)).
  { apply sl1_inject_Z_of_eq.
    apply Z.abs_eq.
    pose proof (sl1_lzn_ge1 n). lia. }
  apply S02_CauchyComplete.Qle_to_QleT'.
  rewrite (sl1_qpower_div_eq B C n HBne HCne).
  rewrite HabsZ, sl1_lzn_exact.
  unfold Qdiv.
  apply Qle_trans
    with (Qpower B (Z.of_nat n) * / inject_Z (planb4_Phi n)).
  - apply Qmult_le_compat_r.
    + exact HLle.
    + exact Hinv0.
  - rewrite (Qmult_comm (Qpower B (Z.of_nat n)) (/ inject_Z (planb4_Phi n))).
    rewrite (Qmult_comm (Qpower B (Z.of_nat n)) (/ Qpower C (Z.of_nat n))).
    apply Qmult_le_compat_r.
    + exact Hinv.
    + exact HBn0.
Defined.

Print Assumptions sl1_lzn_from_bands.
Print Assumptions sl1_qinv_le.
Print Assumptions sl1_qpower_le_mono.
Print Assumptions sl1_qpower_div_eq.
