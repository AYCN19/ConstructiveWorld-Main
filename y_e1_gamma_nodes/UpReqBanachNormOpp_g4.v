(* ConstructiveWorld-Main - UpReqBanachNormOpp_g4: gate-clean cast of UpReqBanachNormOpp (Qred uniqueness + norm-of-opposite face). *)
(** * UpReqBanachNormOpp_g4.
    Mission.  The Id-well-definedness key for a norm [bnorm := Qred o Qabs]: uniqueness of
      the reduced form [bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y]
      (Leibniz codomain), assembled from three legs: the coprime-pair uniqueness machine
      (Zis_gcd recipe) of UpReqBanachInstB, the bnorm_opp attack chain of
      UpReqBanachInstReal, and the canonical-pair characterization of [Qred]
      (Qcanon.Qred_iff + Qreduction.Qred_correct); plus companion laws (positivity and
      order bridges on Z, canonical outputs of Qred, eq-form and Id-form of the
      norm-of-opposite invariance) and the engine lemmas closing the harmonic escape
      statement [bno_sum_inv_fact_escape] (explicit sigT witness, constructive, zero LPO).
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp, UpReqBanachInstB,
      UpReqBanachInstReal; Stdlib QArith/Qabs/Qcanon/ZArith/Znumtheory/Lia/Extraction/Qring.
    References.  Boxed face UpReqBanachNormOpp.v (md5 1aaf4479): statement surface (25 items)
      and every proof body conserved byte-verbatim; only the Chinese comment face re-cast
      (bound-surgery discipline, gate chain-4).  Stem carries the _g4 suffix: Coq 9.3 hard-errors on one
      logical module mapped by two -Q faces (same-stem shadow test) and l0_local
      already holds the boxed stem; consumers (SumInvFactEscape, UpReqIrrationalCriterion)
      keep requiring the boxed module (name-level consumer scan, zero breakage).
    Constructivity.  Zero axioms, nothing left open, no classical logic; Set/eq/Id/Qeq
      statement forms; Print Assumptions Closed at every exit; Separate Extraction with
      zero Obj.magic on the scalar face.
    Build.  coqc -native-compiler no -q via cpu_guard_v3 (TempLimit 96).
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qcanon
  ZArith.ZArith ZArith.Znumtheory.
From Stdlib Require Import Lia.

(* ========== S0: Z-level coprime tools (canonical-pair uniqueness machine, bxib_cross_unique recipe) ========== *)
(* >0 bridge (compare_gt_iff, bxib style) *)
Lemma bno_gt0_of_lt0 : forall d : Z, 0 < d -> (d > 0)%Z.
Proof. intros d H. exact (proj2 (Z.compare_gt_iff d 0) H). Qed.
(* gcd = 1 -> coprime (Zis_gcd_intro recipe; rel_prime := Zis_gcd .. 1) *)
Lemma bno_rel_prime_of_gcd1 : forall n d : Z, Z.gcd n d = 1%Z -> rel_prime n d.
Proof.
  intros n d H.
  exact (Zis_gcd_intro n d 1%Z (Z.divide_1_l n) (Z.divide_1_l d)
    (fun z Hz1 Hz2 =>
       match Zgcd_is_gcd n d with
       | Zis_gcd_intro _ _ _ _ _ Hdiv =>
           eq_ind (Z.gcd n d) (fun g => (z | g)%Z)
             (Hdiv z Hz1 Hz2) 1%Z H
       end)).
Qed.
(* canonical-pair cross-product uniqueness: both pairs coprime to 1 with positive denominators and equal cross products => the pairs are equal (Gauss/rel_prime_cross_prod, direct) *)
Lemma bno_canon_pair_unique : forall n1 d1 n2 d2 : Z,
  Z.gcd n1 d1 = 1%Z -> Z.gcd n2 d2 = 1%Z -> (d1 > 0)%Z -> (d2 > 0)%Z ->
  (n1 * d2 = n2 * d1)%Z -> n1 = n2 /\ d1 = d2.
Proof.
  intros n1 d1 n2 d2 H1 H2 P1 P2 Hc.
  exact (let E := rel_prime_cross_prod n1 d1 n2 d2
             (bno_rel_prime_of_gcd1 n1 d1 H1)
             (bno_rel_prime_of_gcd1 n2 d2 H2) P1 P2
             (eq_ind (n2 * d1) (fun x => (n1 * d2 = x)%Z) Hc (d1 * n2) (Z.mul_comm n2 d1)) in
         conj (proj1 E) (proj2 E)).
Qed.

(* ========== S1: main piece - Qred uniqueness (INS L45 leftover closed) ========== *)
(* the output of Qred is always a canonical pair (idempotence feeds Qred_iff) *)
Lemma bno_qred_canon : forall x : Q,
  Z.gcd (Qnum (Qred x)) (Z.pos (Qden (Qred x))) = 1%Z.
Proof.
  intro x.
  assert (Hi : Qred (Qred x) = Qred x) by (apply Qred_complete, Qred_correct).
  exact (proj1 (Qred_iff (Qred x)) Hi).
Qed.
(* main piece: Qred uniqueness (Qeq in, Leibniz eq out - the Id-well-definedness key) *)
Lemma bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y.
Proof.
  intros x y Hxy.
  pose proof (bno_qred_canon x) as Hc1.
  pose proof (bno_qred_canon y) as Hc2.
  assert (Hr : Qred x == Qred y).
  { apply (Qeq_trans _ x).
    - apply Qred_correct.
    - rewrite Hxy. apply (Qeq_sym (Qred y) y). apply Qred_correct. }
  destruct (Qred x) as [n1 d1] eqn:Ex.
  destruct (Qred y) as [n2 d2] eqn:Ey.
  simpl in Hc1, Hc2.
  unfold Qeq in Hr; simpl in Hr.
  destruct (bno_canon_pair_unique n1 (Z.pos d1) n2 (Z.pos d2)
    Hc1 Hc2 ltac:(apply bno_gt0_of_lt0; lia) ltac:(apply bno_gt0_of_lt0; lia)
    Hr) as [E1 E2].
  apply Pos2Z.inj in E2. rewrite E1, E2. reflexivity.
Qed.
(* Id face of the main piece (eq -> Id bridge, InstReal ready limb) *)
Lemma bno_qred_unique_id : forall x y : Q, x == y -> Id (Qred x) (Qred y).
Proof. intros x y H. exact (@bxra_id_of_eq Q (Qred x) (Qred y) (bno_qred_unique x y H)). Qed.

(* ========== S2: the bnorm Opp/inverse face (discharge of the bnorm := Qred o Qabs bnorm_opp slot + transcription of the InstReal attack chain) ========== *)
(* new: negation invariance of Qred o Qabs (eq form) - the Q-carrier bnorm_opp field slot *)
Lemma bno_qred_abs_opp : forall u : Q, Qred (Qabs (Qopp u)) = Qred (Qabs u).
Proof.
  intro u. apply Qred_complete.
  destruct u as [n d]. cbn [Qopp Qabs].
  unfold Qeq; simpl. rewrite Z.abs_opp. reflexivity.
Qed.
(* Id form of the same (eq -> Id bridge) *)
Lemma bno_qred_abs_opp_id : forall u : Q,
  Id (Qred (Qabs (Qopp u))) (Qred (Qabs u)).
Proof. intro u. exact (@bxra_id_of_eq Q (Qred (Qabs (Qopp u))) (Qred (Qabs u))
                     (bno_qred_abs_opp u)). Qed.
(* dependency transcription 1 (direct use of the InstReal ready limb; statement keeps the in-library Id form: Qabs-norm invariance under Qopp and qnorm) *)
Lemma bno_qabs_qnorm_opp : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof. intro u. exact (bxra_qabs_opp_norm u). Qed.
(* dependency transcription 2 (Real-carrier face: bnorm(opp x) = bnorm x, in-library Id form) *)
Lemma bno_bnorm_opp_real : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof. intro a. exact (bxra_f_norm_opp a). Qed.

(* ========== S3: leftover form of piece two (AA8 B5 roster statement face; proof handover was honest leftover, later closed in S5; zero ad-hoc constructs; raw material: q_fact_pos / exp_series family (S03_QExp), the n! * s_n integralization engine, the q == s_n decidable fork) ========== *)

Definition bno_sum_inv_fact_escape : Type :=
  forall q : Q,
    sigT (fun n : nat => Qlt 1 (Qabs (q_fact n * (q - exp_series n 1))%Q)).
(* ---- piece-two engine lemmas (three closed within budget; the escape main piece closed in S5) ---- *)
(* engine 1: the power of one normalizes to one *)
Lemma bno_q_pow_one : forall n : nat, q_pow 1%Q n == 1%Q.
Proof.
  intro n.
  exact (nat_ind (fun k => q_pow 1%Q k == 1%Q) (Qeq_refl 1%Q)
    (fun (m : nat) (IH : q_pow 1%Q m == 1%Q) =>
       Qeq_trans (1%Q * q_pow 1%Q m)%Q (q_pow 1%Q m) 1%Q
         (Qmult_1_l (q_pow 1%Q m)) IH) n).
Qed.
(* engine 2 pre-lemma: q * (1/q) normalizes to one (Qdiv definition unfolding; the Qmult_inv_r neq is Qeq-formed) *)
Lemma bno_mul_div_self : forall q : Q, ~ (q == 0%Q) -> q * (1%Q / q) == 1%Q.
Proof.
  intros q Hq. unfold Qdiv. rewrite Qmult_1_l. apply Qmult_inv_r. exact Hq.
Qed.
(* engine 2: one-step fractional form of exp_series (B := 1 slot) *)
Lemma bno_exp_series_succ_frac : forall n : nat,
  exp_series (Datatypes.S n) 1%Q
    == exp_series n 1%Q + 1%Q / q_fact (Datatypes.S n)%Q.
Proof.
  intro n. cbn [exp_series]. rewrite bno_q_pow_one. reflexivity.
Qed.
(* engine 3: integralization of n! * s_n (core ingredient of the sum-1/k! escape - n! times the partial sum lands in Z) *)
Lemma bno_exp_scale_Z : forall n : nat,
  sigT (fun z : Z => QeqT (q_fact n * exp_series n 1)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. apply qeq_imp_qeqT. unfold Qeq. cbn [q_fact exp_series Qnum Qden Qmult]. reflexivity.
  - destruct IH as [z Hz].
    exists (Z.of_nat (Datatypes.S m) * z + 1)%Z.
    apply qeq_imp_qeqT.
    rewrite q_fact_succ.
    rewrite bno_exp_series_succ_frac.
    assert (Hq0 : ~ ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m == 0%Q)).
    { intro Hc. apply (Qlt_not_eq 0%Q _ (q_fact_pos (Datatypes.S m))).
      apply Qeq_sym. exact Hc. }
    assert (Hs : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * (1%Q / ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q) == 1%Q).
    { apply bno_mul_div_self. exact Hq0. }
    assert (Hm : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * exp_series m 1%Q == ((Z.of_nat (Datatypes.S m) * z) # 1)%Q).
    { apply (Qeq_trans _ ((Z.of_nat (Datatypes.S m) # 1)%Q
                          * (q_fact m * exp_series m 1)%Q)%Q).
      - apply Qeq_sym. apply Qmult_assoc.
      - apply (@Qmult_comp (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Qeq_refl (Z.of_nat (Datatypes.S m) # 1)%Q)
                           (q_fact m * exp_series m 1)%Q ((z # 1)%Q)
                           (qeqT_imp_qeq (q_fact m * exp_series m 1)%Q
                                ((z # 1)%Q) Hz)). }
    rewrite Qmult_plus_distr_r.
    rewrite Hs.
    rewrite Hm.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult].
    first [lia | ring | reflexivity].
Qed.

(* ========== S4: extraction check + assumption-surface self-audit (G3 face) ========== *)

From Stdlib Require Import Extraction.
(* extraction discipline (INST5/AA3 style): scalar/lemma-level items only; Id/eq value items extract with zero carrier dependencies; Obj.magic expected double-zero. *)
Separate Extraction bno_qred_unique bno_qred_unique_id bno_canon_pair_unique
  bno_rel_prime_of_gcd1 bno_gt0_of_lt0 bno_qred_canon bno_qred_abs_opp
  bno_qred_abs_opp_id bno_qabs_qnorm_opp bno_bnorm_opp_real.

Print Assumptions bno_qred_unique.
Print Assumptions bno_qred_unique_id.
Print Assumptions bno_canon_pair_unique.
Print Assumptions bno_qred_abs_opp.
Print Assumptions bno_qred_abs_opp_id.
Print Assumptions bno_qabs_qnorm_opp.
Print Assumptions bno_bnorm_opp_real.
Print Assumptions bno_q_pow_one.
Print Assumptions bno_exp_series_succ_frac.
Print Assumptions bno_mul_div_self.
Print Assumptions bno_exp_scale_Z.

(* ========== S5: piece-two closing section (B5R) - the AA8 B5 sigT explicit escape form is officially closed: bno_sum_inv_fact_escape. ========== *)
(* Proof method (constructive, zero LPO, zero decidable forks): 1) engine probe bno_scale_q_int - for any q = p/d pick n >= d so that n! * q lands in Z (bno_qfact_int: n! is an integer; bno_qfact_scale_d: Z-witness w of d | n!; bno_pos_d_nat: the denominator probe via Z.to_nat).  2) iteration step bno_tail_step: T_{k+1} = (k+1) * T_k - 1 (T_k := k! * (q - s_k); Qring ring + bno_mul_div_self).  3) two-step swallow bno_two_step: after two steps any integer z satisfies |b * (a*z - 1) - 1| >= 2 > 1 (a >= 2, b >= 3) - z = 0 is swallowed too; the q == s_k decidable fork disappears entirely (stronger than the original roster plan, zero LPO).  4) strict lower bound bno_lt1_int_abs: integer-slot |w| >= 2 => Qlt 1 (Qabs t); monotone assembly via Z.mul_le_mono_nonneg_r (right-multiply form, QLeg precedent), three explicit branches z >= 1 / z = 0 / z <= -1, zero nia non-linear reflection.  5) main piece bno_sum_inv_fact_escape_close: n! * q minus the engine piece bno_exp_scale_Z (n! * s_n in Z) gives T_n0 in Z; shift one step, feed the two-step swallow; witness index := S(S(S n0)). *)
(* assumption self-audit: this section has zero axiom declarations and zero global assumption declarations of any kind; statement surface Type/sigT/Qlt forms; the main piece exits Closed. *)
(* extraction discipline (INST5 style): sigT witness lemmas (qfact_int / qfact_scale_d / pos_d_nat / scale_q_int / close) stay out of the Separate Extraction unit; Print Assumptions carries the assumption face; Qeq/Qlt scalar items are extracted. *)
(* territory discipline: pure addition; the 11 built items untouched. *)

From Stdlib Require Import Qring.
(* P1: n! itself is an integer *)
Lemma bno_qfact_int : forall n : nat,
  sigT (fun z : Z => Qeq (q_fact n)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. reflexivity.
  - destruct IH as [z Hz]. exists (Z.of_nat (Datatypes.S m) * z)%Z.
    rewrite q_fact_succ. rewrite Hz. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P2: n! contains the multiple of denominator d (d <= n) *)
Lemma bno_qfact_scale_d : forall (n : nat) (d : Z),
  (1 <= d)%Z -> (d <= Z.of_nat n)%Z ->
  sigT (fun w : Z => Qeq (q_fact n)%Q (((d * w)%Z # 1)%Q)).
Proof.
  induction n as [| m IH]; intros d Hd Hle.
  - lia.
  - destruct (Z.eq_dec d (Z.of_nat (Datatypes.S m))) as [HdEq | HdNe].
    + destruct (bno_qfact_int m) as [z Hz]. subst d.
      exists z. rewrite q_fact_succ. rewrite Hz.
      unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
    + assert (Hlt : (d <= Z.of_nat m)%Z).
      { rewrite Nat2Z.inj_succ in Hle.
        assert (Hne : (d <> Z.succ (Z.of_nat m))%Z).
        { rewrite <- Nat2Z.inj_succ. exact HdNe. }
        lia. }
      destruct (IH d Hd Hlt) as [w Hw].
      exists (Z.of_nat (Datatypes.S m) * w)%Z.
      rewrite q_fact_succ. rewrite Hw. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P3: any rational times a large enough n! is an integer *)
Lemma bno_pos_d_nat : forall d : positive, sigT (fun n : nat => (Z.pos d <= Z.of_nat n)%Z).
Proof.
  intro d.
  exact (existT (fun n : nat => (Z.pos d <= Z.of_nat n)%Z) (Z.to_nat (Z.pos d))
    (eq_ind (Z.pos d) (fun z => (Z.pos d <= z)%Z) (Z.le_refl (Z.pos d))
       (Z.of_nat (Z.to_nat (Z.pos d)))
       (eq_sym (Z2Nat.id (Z.pos d)
          (Z.lt_le_incl 0 (Z.pos d) (Pos2Z.is_pos d)))))).
Qed.

Lemma bno_scale_q_int : forall q : Q,
  sigT (fun n : nat => sigT (fun z : Z => Qeq (q_fact n * q)%Q ((z # 1)%Q))).
Proof.
  intro q. destruct q as [p d].
  destruct (bno_pos_d_nat d) as [n Hn].
  destruct (bno_qfact_scale_d n (Z.pos d)
    ltac:(pose proof (Pos2Z.is_pos d); lia) Hn) as [w0 Hw].
  exists n, (w0 * p)%Z.
  rewrite Hw. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P4: iteration step T_{k+1} = (k+1) * T_k - 1 *)
Lemma bno_tail_step : forall (n : nat) (q : Q),
  (q_fact (Datatypes.S n) * (q - exp_series (Datatypes.S n) 1))%Q
  == ((Z.of_nat (Datatypes.S n) # 1) * (q_fact n * (q - exp_series n 1)) - 1%Q)%Q.
Proof.
  intros n q.
  assert (Hinv : (q_fact (Datatypes.S n) * (1%Q / q_fact (Datatypes.S n)))%Q == 1%Q).
  { apply bno_mul_div_self. intro H0.
    apply (Qlt_not_eq 0%Q _ (q_fact_pos (Datatypes.S n))).
    apply Qeq_sym. exact H0. }
  rewrite bno_exp_series_succ_frac.
  apply (Qeq_trans _ (q_fact (Datatypes.S n) * (q - exp_series n 1)%Q
                      - q_fact (Datatypes.S n) * (1%Q / q_fact (Datatypes.S n))%Q)%Q).
  - ring.
  - rewrite Hinv. rewrite q_fact_succ. ring.
Qed.

(* P5: an integer value (>= 2) gives a strictly >1 absolute value *)
Lemma bno_lt1_int_abs : forall (w : Z) (t : Q),
  t == (w # 1)%Q -> (1 < Z.abs w)%Z -> Qlt 1%Q (Qabs t).
Proof.
  intros w [tn td] Heq Hw.
  unfold Qeq in Heq. cbn [Qnum Qden Qmult] in Heq.
  rewrite Z.mul_1_r in Heq.
  unfold Qlt, Qabs. cbn [Qnum Qden Qmult].
  rewrite Heq, Z.abs_mul, Z.mul_1_r.
  replace (Z.abs (Z.pos td)) with (Z.pos td)
    by (rewrite Z.abs_eq; pose proof (Pos2Z.is_pos td); lia).
  pose proof (Pos2Z.is_pos td) as Hp.
  pose proof (Z.mul_le_mono_nonneg_r 2 (Z.abs w) (Z.pos td) ltac:(lia) ltac:(lia)) as Hmono.
  lia.
Qed.

(* P5.5: constructor bridging lemmas (Qeq arithmetic on Z#1 forms; all constructor reductions, zero opaque projections) *)
Lemma bno_z1_step_eq : forall x y : Z,
  (((x # 1)%Q * (y # 1)%Q - 1%Q)%Q) == (((x * y - 1)%Z # 1)%Q).
Proof.
  intros x y. unfold Qeq.
  cbn [Qnum Qden Qmult Qminus Qopp Qplus Pos.mul]. lia.
Qed.

Lemma bno_z1_minus_eq : forall x y : Z,
  ((x # 1)%Q - (y # 1)%Q)%Q == (((x - y)%Z # 1)%Q).
Proof.
  intros x y. unfold Qeq.
  cbn [Qnum Qden Qminus Qopp Qplus Pos.mul]. lia.
Qed.

(* P6: two iterations swallow every integer (including 0) *)
Lemma bno_two_step : forall (n : nat) (q : Q) (z : Z),
  (1 <= Z.of_nat n)%Z ->
  (q_fact n * (q - exp_series n 1))%Q == (z # 1)%Q ->
  Qlt 1%Q (Qabs (q_fact (Datatypes.S (Datatypes.S n))
                   * (q - exp_series (Datatypes.S (Datatypes.S n)) 1))%Q).
Proof.
  intros n q z Hn Hz.
  pose proof (bno_tail_step n q) as H1. rewrite Hz in H1.
  assert (Hw1 : (q_fact (Datatypes.S n) * (q - exp_series (Datatypes.S n) 1))%Q
              == (((Z.of_nat (Datatypes.S n) * z - 1)%Z # 1)%Q)).
  { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S n) # 1) * (z # 1) - 1%Q)%Q)).
    - exact H1.
    - apply bno_z1_step_eq. }
  pose proof (bno_tail_step (Datatypes.S n) q) as H2. rewrite Hw1 in H2.
  apply (bno_lt1_int_abs
    (Z.of_nat (Datatypes.S (Datatypes.S n)) * (Z.of_nat (Datatypes.S n) * z - 1) - 1)%Z
    (q_fact (Datatypes.S (Datatypes.S n))
     * (q - exp_series (Datatypes.S (Datatypes.S n)) 1))%Q).
  - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                          * (((Z.of_nat (Datatypes.S n) * z - 1)%Z # 1)%Q)
                          - 1%Q)%Q)).
    + exact H2.
    + apply bno_z1_step_eq.
  - rewrite !Nat2Z.inj_succ.
    (* a := Z.succ (Z.of_nat n) >= 2, b := Z.succ a >= 3; three-branch explicit monotonicity (right-multiply form) *)
    destruct (Z_lt_le_dec z 0) as [Hzneg | Hznonneg].
    + assert (Hm1 : (z * Z.succ (Z.of_nat n) <= (-1) * Z.succ (Z.of_nat n))%Z)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hm2 : ((Z.succ (Z.of_nat n) * z - 1) * Z.succ (Z.succ (Z.of_nat n))
                     <= (-3) * Z.succ (Z.succ (Z.of_nat n)))%Z)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite Z.abs_neq by lia. lia.
    + destruct (Z.eq_dec z 0) as [Hz0 | Hz0ne].
      * subst z. rewrite Z.mul_0_r.
        replace (0 - 1)%Z with (-1)%Z by lia.
        rewrite Z.abs_neq by lia. lia.
      * assert (Hm1 : (1 * Z.succ (Z.of_nat n) <= z * Z.succ (Z.of_nat n))%Z)
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Z.mul_1_l in Hm1.
        assert (Hprod : (1 <= Z.succ (Z.of_nat n) * z - 1)%Z) by lia.
        assert (Hm2 : (1 * Z.succ (Z.succ (Z.of_nat n))
                       <= (Z.succ (Z.of_nat n) * z - 1) * Z.succ (Z.succ (Z.of_nat n)))%Z)
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Z.mul_1_l in Hm2.
        rewrite Z.abs_eq by lia. lia.
Qed.

(* P7 main piece: piece-two escape closure (explicit sigT witness, zero LPO) *)
Theorem bno_sum_inv_fact_escape_close : bno_sum_inv_fact_escape.
Proof.
  unfold bno_sum_inv_fact_escape. intro q.
  destruct (bno_scale_q_int q) as [n0 [z1 Hz1]].
  pose proof (bno_exp_scale_Z n0) as Hs. destruct Hs as [z2 Hz2].
  assert (Hs' : (q_fact n0 * exp_series n0 1)%Q == (z2 # 1)%Q)
    by (apply qeqT_imp_qeq; exact Hz2).
  assert (HT0 : (q_fact n0 * (q - exp_series n0 1))%Q == (((z1 - z2)%Z # 1)%Q)).
  { apply (Qeq_trans _ (q_fact n0 * q - q_fact n0 * exp_series n0 1)%Q).
    - ring.
    - rewrite Hz1, Hs'. apply bno_z1_minus_eq. }
  pose proof (bno_tail_step n0 q) as Hts. rewrite HT0 in Hts.
  assert (HT1 : (q_fact (Datatypes.S n0) * (q - exp_series (Datatypes.S n0) 1))%Q
              == (((Z.of_nat (Datatypes.S n0) * (z1 - z2) - 1)%Z # 1)%Q)).
  { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S n0) # 1)
                          * (((z1 - z2)%Z # 1)%Q) - 1%Q)%Q)).
    - exact Hts.
    - apply bno_z1_step_eq. }
  exists (Datatypes.S (Datatypes.S (Datatypes.S n0))).
  apply (bno_two_step (Datatypes.S n0) q
    (Z.of_nat (Datatypes.S n0) * (z1 - z2) - 1)%Z).
  - rewrite Nat2Z.inj_succ. lia.
  - exact HT1.
Qed.


(* ========== S6: extraction check + assumption-surface self-audit (G3 face, B5R section) ========== *)

(* extraction discipline (INST5/AA11 style): only Qeq/Qlt scalar/lemma-level new items are extracted; sigT witness lemmas stay out of the extraction unit (existT inherent-magic risk); Print Assumptions carries the assumption face. *)
Separate Extraction bno_tail_step bno_lt1_int_abs bno_two_step
  bno_z1_step_eq bno_z1_minus_eq.

Print Assumptions bno_pos_d_nat.
Print Assumptions bno_qfact_int.
Print Assumptions bno_qfact_scale_d.
Print Assumptions bno_scale_q_int.
Print Assumptions bno_tail_step.
Print Assumptions bno_lt1_int_abs.
Print Assumptions bno_z1_step_eq.
Print Assumptions bno_z1_minus_eq.
Print Assumptions bno_two_step.
Print Assumptions bno_sum_inv_fact_escape_close.