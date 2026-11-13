(* ConstructiveWorld-Main - the division-free positive-tail lower bound
   of the quadratic Pade remainder. *)

(** * UpReqPadeLower: strict lower bound of the exponential times the
      Pade denominator over the Pade numerator.

    Mission.  [cpl_lower_even]: for every rational [y] with [0 < y]
      the exponential times the quadratic Pade denominator exceeds
      the quadratic Pade numerator by more than the explicit witness
      [y^5 / 720], in the [real_lt] sigT witness form with rank
      [N = 6].  Supporting kit: Q-level equality-to-order transfer
      bridges and congruence, power positivity, the closed form
      [Q2(y) = 1 - y/2 + y*y/12] with positivity on the positive
      ray, partial-sum monotonicity and extension, and the identity
      [exp6 * Q2 - P2 == y^5/720 + y^6/1440 + y^8/8640].
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp, the
      S04-S15 module chain, UpReqPadeExp, UpReqQExpTail,
      UpReqPadeQLeg; Stdlib QArith, Arith, Lia, Setoid.
    References.  Statement face conserved verbatim from the live-tree
      module of the same name; numeric anchors in the certificate
      companion UpReqPadeLower_cert.
    Constructivity.  Pure Set-level content.  Strict order is
      carried by QltT/Qlt witnesses inside the sigT form of
      [real_lt]; no classical principles, no integrals, no division
      on the Real face; every audited name is Closed under the
      global context.
    Build.  coqc -q -native-compiler no with the l0_local face plus
      the node build face, Coq 9.3.0, wrapped by the temperature
      guard.
*)

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
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeLower.

(* ===== B0 transfer bridges (Qeq to Qlt; single-step Q monotonicity
   legs, no Psatz/micromega closure introduced; statement faces all
   unchanged) ===== *)

(* Right transfer under equality: 0 < a carries to 0 < b when a == b
   (same proof shape as pql_qlt0_eq_r, self-contained). *)
Lemma cpl_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* Left transfer under equality: x < b carries to a < b when x == a. *)
Lemma cpl_qlt_eq_l : forall x a b : Q, x == a -> Qlt x b -> Qlt a b.
Proof.
  intros x a b Hxa Hlt.
  exact (pql_qlt_eq_l x a b Hxa Hlt).
Qed.

(* Additive/subtractive/multiplicative congruence for Qeq: the Proper
   instances of QArith_base used directly as functions
   (Qplus_comp / Qminus_comp / Qmult_comp), zero nia. *)
Lemma cpl_qplus_comp : forall w x y z : Q, w == x -> y == z -> w + y == x + z.
Proof. intros w x y z H1 H2. apply Qplus_comp; assumption. Qed.

Lemma cpl_qminus_comp : forall w x y z : Q, w == x -> y == z -> w - y == x - z.
Proof. intros w x y z H1 H2. apply Qminus_comp; assumption. Qed.

Lemma cpl_qmult_comp : forall w x y z : Q, w == x -> y == z -> w * y == x * z.
Proof. intros w x y z H1 H2. apply Qmult_comp; assumption. Qed.

(* Strict right transfer at a left endpoint x: a == b implies
   Qlt x a -> Qlt x b (single step through pql_qlt_eq_r). *)
Lemma cpl_qlt_eq_sr : forall (x a b : Q), a == b -> Qlt x a -> Qlt x b.
Proof.
  intros x a b Hab Ha.
  exact (pql_qlt_eq_r a b x Hab Ha).
Qed.

(* Power nonnegative: 0 <= y implies 0 <= y^k (base module of the
   termwise-nonnegative monotonicity chain). *)
Lemma cpl_qpow_nonneg : forall (y : Q) (k : nat), Qle 0 y -> Qle 0 (q_pow y k).
Proof.
  intros y k Hy. induction k as [| k IH].
  - change (q_pow y 0%nat) with 1%Q. apply Qle_0_1.
  - change (q_pow y (Datatypes.S k)) with (y * q_pow y k).
    apply Qmult_le_0_compat.
    + exact Hy.
    + exact IH.
Qed.

(* Power strictly positive: 0 < y implies 0 < y^k (source of the
   strictness witnesses). *)
Lemma cpl_qpow_pos : forall (y : Q) (k : nat), Qlt 0 y -> Qlt 0 (q_pow y k).
Proof.
  intros y k Hy. induction k as [| k IH].
  - change (q_pow y 0%nat) with 1%Q. unfold Qlt. simpl. lia.
  - change (q_pow y (Datatypes.S k)) with (y * q_pow y k).
    apply Qmult_lt_0_compat.
    + exact Hy.
    + exact IH.
Qed.

(* Strict to weak: Qlt x y -> Qle x y (same Z-level expansion). *)
Lemma cpl_qlt_le : forall x y : Q, Qlt x y -> Qle x y.
Proof.
  intros x y H. unfold Qlt, Qle in *.
  destruct x as [nx dx]. destruct y as [ny dy]. simpl in *. lia.
Qed.

(* Square nonnegative: decidable pointwise Q order (Qlt_le_dec), no
   LPO face; the negative branch goes through the -t * -t dual. *)
Lemma cpl_sq_nonneg : forall t : Q, Qle 0 (t * t).
Proof.
  intro t. destruct t as [tn td].
  destruct (Qlt_le_dec 0 (tn#td)) as [Hlt | Hle].
  - apply cpl_qlt_le. apply Qmult_lt_0_compat; exact Hlt.
  - assert (Hnn : Qle 0 (- (tn#td))).
    { unfold Qle, Qopp in *. simpl in Hle |- *. lia. }
    apply (Qle_trans 0 ((- (tn#td)) * (- (tn#td))) ((tn#td) * (tn#td))).
    + apply Qmult_le_0_compat; exact Hnn.
    + apply qeq_le. ring.
Qed.

(* ===== B1 numeric anchors: the two Pade coefficient anchors; the
   vm_compute cross-checks of the polynomial identity live in the
   certificate companion UpReqPadeLower_cert. ===== *)

(* Pade coefficient anchors (formula plus bounded-sum plus alternating
   sign, end to end). *)
Lemma cpl_sent_s_b1 : pade_num 1%nat (1#2) == (5#4).
Proof. exact pade_num_1_half. Qed.

Lemma cpl_sent_s_b2 : pade_den 1%nat (1#2) == (3#4).
Proof. exact pade_den_1_half. Qed.

(* n = 0 degenerate face: E0 == 1, i.e. P0 = Q0 = 1 (the existing
   pade_num_0_one / pade_den_0_one used directly, plus the partial-sum
   base instance anchor). *)
Lemma cpl_sent_exp0 : forall y : Q, exp_partial 0%nat y == 1%Q.
Proof. intro y. exact (Qeq_refl 1%Q). Qed.

(* ===== B2 main Q-level algebra ===== *)

(* Closed-form expansion of the quadratic denominator: the interface
   gap (pdp_den_pos covers only [0,1]); this instance gives the whole
   positive ray, Q2(y) = 1 - y/2 + y*y/12 = ((y-3)^2 + 3)/12 > 0. *)
Lemma cpl_den2_expl : forall y : Q,
  pade_den 2%nat y == 1%Q + (- (1#2)%Q) * y + (1#12)%Q * (y * y).
Proof.
  intro y.
  unfold pade_den, pade_coeff.
  cbn [sum_upto q_pow q_fact Z.of_nat Nat.sub Nat.mul Nat.add]. cbv beta.
  field.
Qed.

Lemma cpl_den2_pos : forall y : Q, Qlt 0 y -> Qlt 0 (pade_den 2%nat y).
Proof.
  intros y Hy.
  assert (Hexpl : pade_den 2%nat y == 1%Q + (- (1#2)%Q) * y + (1#12)%Q * (y * y))
    by (apply cpl_den2_expl).
  (* 12 * the explicit form == (y-3)^2 + 3 > 0 *)
  assert (H12 : Qlt 0 (12 * (1%Q + - (1#2)%Q * y + (1#12)%Q * (y * y)))).
  { apply (cpl_qlt0_eq_r ((y + -3) * (y + -3) + 3)
                         (12 * (1 + - (1#2) * y + (1#12) * (y * y)))).
    - field.
    - assert (Hsq : Qle 0 ((y + -3) * (y + -3))) by (apply cpl_sq_nonneg).
      assert (H3 : Qlt 0 3%Q) by (unfold Qlt; simpl; lia).
      apply (cpl_qlt0_eq_r (3 + (y + -3) * (y + -3))%Q
                           ((y + -3) * (y + -3) + 3)%Q).
      + ring.
      + apply (Qlt_le_trans 0 3%Q (3 + (y + -3) * (y + -3))%Q).
        * exact H3.
        * apply (qtail_le_plus_r 3%Q ((y + -3) * (y + -3))). exact Hsq. }
  (* Qlt 0 ((12*E)*(1/12)) implies Qlt 0 E implies Qlt 0 pade_den (right transfer chain) *)
  apply (cpl_qlt0_eq_r ((12 * (1 + - (1#2) * y + (1#12) * (y * y))) * (1#12))
                       (pade_den 2%nat y)).
  - transitivity (1%Q + - (1#2)%Q * y + (1#12)%Q * (y * y)).
    + unfold Qdiv. field.
    + apply Qeq_sym. exact Hexpl.
  - apply (Qmult_lt_0_compat _ (1#12)).
    + exact H12.
    + unfold Qlt. simpl. lia.
Qed.

(* Partial-sum step is nondecreasing: 0 <= y implies E_m <= E_{m+1}
   (the Q-level half of the identification lemma). *)
Lemma cpl_ep_step_le : forall (y : Q) (m : nat),
  Qle 0 y -> Qle (exp_partial m y) (exp_partial (Datatypes.S m) y).
Proof.
  intros y m Hy.
  change (exp_partial (Datatypes.S m) y)
    with (exp_partial m y + q_pow y (Datatypes.S m) / q_fact (Datatypes.S m)).
  apply (qtail_le_plus_r (exp_partial m y) (q_pow y (Datatypes.S m) / q_fact (Datatypes.S m))).
  unfold Qdiv. apply Qmult_le_0_compat.
  - apply (cpl_qpow_nonneg y (Datatypes.S m) Hy).
  - apply cpl_qlt_le. apply (Qinv_lt_0_compat (q_fact (Datatypes.S m))).
    apply q_fact_pos.
Qed.

(* Partial sums monotone: 0 <= y and a <= b imply E_a <= E_b (the
   Q-level core of the N := 6 slot of the main statement). *)
Lemma cpl_ep_mono : forall (y : Q) (a b : nat),
  Qle 0 y -> (a <= b)%nat -> Qle (exp_partial a y) (exp_partial b y).
Proof.
  intros y a b Hy Hab.
  revert a Hab. induction b as [| b' IH].
  - intros a Hab. assert (Ha0 : a = 0%nat) by lia. subst a. apply Qle_refl.
  - intros a Hab. destruct (Nat.eq_dec a (Datatypes.S b')) as [Heq | Hne].
    + rewrite Heq. apply Qle_refl.
    + assert (Hab' : (a <= b')%nat) by lia.
      apply (Qle_trans _ (exp_partial b' y)).
      * apply IH. exact Hab'.
      * apply (cpl_ep_step_le y b' Hy).
Qed.

(* Core polynomial identity (second interface gap: E6*Q2 - P2 is the
   division-free positive-tail polynomial; cross-checked by the
   numeric anchors of the certificate companion). *)
Lemma cpl_g6_identity : forall y : Q,
  exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y ==
  q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640.
Proof.
  intro y.
  unfold pade_den, pade_num, pade_coeff.
  cbn [exp_partial sum_upto q_pow q_fact Z.of_nat Nat.sub Nat.mul Nat.add]. cbv beta.
  field.
Qed.

(* Pointwise extension of powers: a == b implies y^k congruent. *)
Lemma cpl_qpow_ext : forall (k : nat) (a b : Q), a == b -> q_pow a k == q_pow b k.
Proof.
  intros k a b Hab. induction k as [| k IH].
  - reflexivity.
  - apply Qmult_comp.
    + exact Hab.
    + exact IH.
Qed.

(* Pointwise extension of partial sums: a == b implies E_m(a) == E_m(b)
   (lifts a pointwise equality into exp_partial). *)
Lemma cpl_ep_ext : forall (m : nat) (a b : Q), a == b -> exp_partial m a == exp_partial m b.
Proof.
  intros m a b Hab. induction m as [| m IH].
  - reflexivity.
  - apply Qplus_comp.
    + exact IH.
    + unfold Qdiv. apply cpl_qmult_comp.
      * change (q_pow a (Datatypes.S m)) with (a * q_pow a m).
        change (q_pow b (Datatypes.S m)) with (b * q_pow b m).
        apply cpl_qmult_comp.
        -- exact Hab.
        -- exact (cpl_qpow_ext m a b Hab).
      * apply Qeq_refl.
Qed.

(* ===== C Real-level main statement (cpl_lower_even, division-free
   real_lt sigT witness form) ===== *)

(* Statement: exp y * Q2(y) - P2(y) > y^5/720 with witness
   eps := y^5/720 and rank N := 6, both explicit and computable; the
   Q subtraction inside real_lt is intrinsic and division-free. *)
Theorem cpl_lower_even : forall y : Q,
  QltT 0 y ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult (cauchy_real_exp (real_const y)) (real_const (pade_den 2%nat y))).
Proof.
  intros y Hy.
  assert (Hylt : Qlt 0 y) by (apply QltT_to_Qlt; exact Hy).
  assert (Hy0 : Qle 0 y) by (apply cpl_qlt_le; exact Hylt).
  (* direct witness construction: open real_const, project pointwise *)
  assert (Hc : forall k, projT1 (real_const y) k == y) by (intro k; apply real_const_proj).
  destruct (real_const y) as [u Hu] eqn:Eu.
  (* destruct rewrote real_const y inside Hc; project directly *)
  cbn [projT1] in Hc.
  unfold real_lt.
  exists (q_pow y 5%nat / 720)%Q.
  split.
  - (* witness positivity: 0 < y^5/720 *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (q_pow y 5%nat) (1#720)).
    + apply (cpl_qpow_pos y 5%nat Hylt).
    + apply (Qinv_lt_0_compat (720#1)). unfold Qlt. simpl. lia.
  - exists 6%nat.
    intros m Hm.
    assert (Hle : (6 <= m)%nat) by (apply NatLe_drop; exact Hm).
    (* projection assembly through the qeq bridge: the QltT face forbids rewrite *)
    (* and the setoid instances are unavailable; self-contained Qeq combinators *)
    (* with fully explicit Qeq_trans; S02 real_mult_proj and real_const_proj *)
    assert (Hexp : projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                   == exp_partial m (u m)).
    { unfold cauchy_real_exp. reflexivity. }
    assert (Hexp2 : projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    == exp_partial m y)
      by (apply (Qeq_trans _ (exp_partial m (u m)) _ Hexp (cpl_ep_ext m (u m) y (Hc m)))).
    assert (HDe : projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                    (real_const (pade_den 2%nat y))) m
                    - projT1 (real_const (pade_num 2%nat y)) m
                  == exp_partial m y * pade_den 2%nat y - pade_num 2%nat y).
    { apply (Qeq_trans _
              (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                 * projT1 (real_const (pade_den 2%nat y)) m
                 - projT1 (real_const (pade_num 2%nat y)) m) _).
      - apply (cpl_qminus_comp
                 (projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                    (real_const (pade_den 2%nat y))) m)
                 (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    * projT1 (real_const (pade_den 2%nat y)) m)).
        + apply (real_mult_proj (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                (real_const (pade_den 2%nat y)) m).
        + apply Qeq_refl.
      - apply (cpl_qminus_comp
                 (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    * projT1 (real_const (pade_den 2%nat y)) m)
                 (exp_partial m y * pade_den 2%nat y)).
        + apply (cpl_qmult_comp
                   (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m)
                   (exp_partial m y)
                   (projT1 (real_const (pade_den 2%nat y)) m) (pade_den 2%nat y)).
          * exact Hexp2.
          * apply (real_const_proj (pade_den 2%nat y) m).
        + apply (real_const_proj (pade_num 2%nat y) m). }
    assert (Hchain : Qlt (q_pow y 5%nat / 720)
                       (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y)).
    { (* Q-level completion chain (inside the Prop proof) *)
    assert (Hident : exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y ==
                     q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)
      by (apply cpl_g6_identity).
    assert (Hmono : Qle (exp_partial 6%nat y) (exp_partial m y))
      by (apply (cpl_ep_mono y 6%nat m Hy0 Hle)).
    assert (Hden : Qle 0 (pade_den 2%nat y))
      by (apply cpl_qlt_le; apply (cpl_den2_pos y Hylt)).
    assert (Hstep1 : Qle (exp_partial 6%nat y * pade_den 2%nat y)
                         (exp_partial m y * pade_den 2%nat y))
      by (apply (Qmult_le_compat_r _ _ (pade_den 2%nat y)); assumption).
    assert (Hstep2 : Qle (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y)
                         (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y))
      by (apply (proj2 (Qplus_le_l _ _ (- pade_num 2%nat y))); exact Hstep1).
    assert (Hstep3 : Qle (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)
                         (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y))
      by (apply (Qle_trans _ (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y));
          [apply qeq_le; apply Qeq_sym; exact Hident | exact Hstep2]).
    (* strict step: 0 < y^6/1440 gives A < A + y^6/1440 *)
    assert (Hb : Qlt 0 (q_pow y 6%nat / 1440)).
    { unfold Qdiv. apply Qmult_lt_0_compat.
      - apply (cpl_qpow_pos y 6%nat Hylt).
      - apply (Qinv_lt_0_compat (1440#1)). unfold Qlt. simpl. lia. }
    assert (Hc1 : Qlt (q_pow y 5%nat / 720)
                      (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720)).
    { apply (cpl_qlt_eq_l (0 + q_pow y 5%nat / 720)%Q).
      - ring.
      - apply (proj2 (Qplus_lt_l 0%Q (q_pow y 6%nat / 1440) (q_pow y 5%nat / 720))).
        exact Hb. }
    assert (Hswap : Qle (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720)
                        (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440))
      by (apply qeq_le; ring).
    apply (Qlt_le_trans _ (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440)).
    - exact (Qlt_le_trans _ (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720) _ Hc1 Hswap).
    - apply (Qle_trans _ (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)).
      + apply (qtail_le_plus_r _ (q_pow y 8%nat / 8640)).
        unfold Qdiv. apply Qmult_le_0_compat.
        * apply (cpl_qpow_nonneg y 8%nat Hy0).
        * apply cpl_qlt_le. apply (Qinv_lt_0_compat (8640#1)). unfold Qlt. simpl. lia.
      + exact Hstep3.
    }
    assert (Hpt : Qlt (q_pow y 5%nat / 720)
                      (projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                          (real_const (pade_den 2%nat y))) m
                        - projT1 (real_const (pade_num 2%nat y)) m)).
    { apply (cpl_qlt_eq_sr (q_pow y 5%nat / 720)
              (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y)).
      - exact (Qeq_sym _ _ HDe).
      - exact Hchain. }
    apply Qlt_to_QltT. exact Hpt.
Qed.

End PadeLower.
