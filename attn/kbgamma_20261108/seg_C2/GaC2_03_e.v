(* ConstructiveWorld-Main - the Cx-layer multiplicative term law of the
   Dirichlet term. *)
(** * GaC2_03_e: the multiplicative-law leaf of node C2.03.
    Mission.  The Cx-layer multiplicative law of the Dirichlet term
      consumed by the finite Euler product stem's prime-table
      induction body: the nat-embedding product face [nat_real_mul]
      (a * b embeds to the Real product), the Set-sorted [NatLe]
      witness for products [natle_mul], the [c_of_real] faces
      [c_of_real_wd]/[c_of_real_plus], the exponential injectivity
      face on the Real carrier [cauchy_real_exp_inj]
      (weak-trichotomy route), the embedded log-product law
      ln(a*b) = ln a + ln b at the c_powq premises
      [real_log_nat_real_mult_gen], and the term law
      [c_powq_mult_law_gen] ((a*b)^{-s} = a^{-s} * b^{-s}).
    Dependencies.  Stdlib [Arith.Arith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import),
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [CxRealPairCore], [CxRealPairExpLog],
      [GaC2_01_DirichletPartialSum] ([c_powq]/[c_exp_wd]/
      [nat_real]), and [GaC2_03_d] ([natle_mul]) of this development.
    References.  Card C2.03 (finite Euler identity needs the
      multiplicative term law), drafts_C2.md C2.03.  Statement
      provenance: [nat_real_mul] is a within-segment re-cast of
      GaC2_02_AbsConvTailBound_a's [nat_real_mul] (this node does not
      Require the C2.02 leaf, so the face is re-cast here).  The
      exponential-injectivity route is the tree's log_inv route
      (S07_RealSetoidExpLog [log_inv_exp_neg_thm], strict monotonicity
      + weak trichotomy), statement generalized; proof bodies
      re-derived from tree faces, zero transplant.
    Constructivity.  Every named construction is carried by [Set];
      negations are written P -> False (zero not/~ tokens); no
      vm_compute; every proof closes under the global context;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_e.v] compiles cleanly (exit 0), wrapped by
      [cpu_guard v3] (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce
      0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_03_d.
From Stdlib Require Import QArith_base.
From Stdlib Require Import Qring.
From Stdlib Require Import BinInt.
Close Scope Q_scope.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ==== Section 1. Embedding and witness faces ==== *)

(* The nat embedding is multiplicative.  (Wave-rule-forced within-segment   *)
(* re-cast; the C2.02 leaf carries the original, see header.)               *)
Lemma nat_real_mul : forall a b : nat,
  real_eq (nat_real (a * b)) (real_mult (nat_real a) (nat_real b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n. unfold nat_real.
  rewrite real_mult_proj, !real_const_proj.
  assert (Hm : Z.of_nat (a * b) = (Z.of_nat a * Z.of_nat b)%Z) by lia.
  rewrite Hm. unfold Qeq. simpl. ring.
Qed.

(* The Set-sorted positivity witness is multiplicative. *)
Lemma natle_mul : forall a b : nat, NatLe 1 a -> NatLe 1 b -> NatLe 1 (a * b).
Proof.
  intros a b Ha Hb.
  apply NatLe_drop in Ha. apply NatLe_drop in Hb.
  apply NatLe_lift.
  assert ((1 * b <= a * b)%nat) by (apply Nat.mul_le_mono_r; exact Ha).
  lia.
Qed.

(* c_of_real respects the Real equality. *)
Lemma c_of_real_wd : forall x y : Real, real_eq x y ->
  c_eq (c_of_real x) (c_of_real y).
Proof.
  intros x y H. unfold c_of_real, c_eq, cRe, cIm. split.
  - exact H.
  - apply real_eq_refl.
Qed.

(* c_of_real turns Real addition into Cx addition. *)
Lemma c_of_real_plus : forall x y : Real,
  c_eq (c_of_real (real_plus x y)) (c_plus (c_of_real x) (c_of_real y)).
Proof.
  intros x y.
  unfold c_of_real, c_eq, cRe, cIm, c_plus. split;
  apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

(* ==== Section 2. Exponential injectivity and the embedded log law ==== *)

(* The exponential is injective up to real_eq (weak-trichotomy route; the   *)
(* tree's log_inv route with the statement generalized).                    *)
Lemma cauchy_real_exp_inj : forall u v : Real,
  real_eq (cauchy_real_exp u) (cauchy_real_exp v) -> real_eq u v.
Proof.
  intros u v Heq. apply (real_weak_trich u v).
  - intro Hult.
    apply (real_lt_not_eq (cauchy_real_exp u) (cauchy_real_exp v)).
    + apply (cauchy_real_exp_mono u v). exact Hult.
    + exact Heq.
  - intro Hvlt.
    apply (real_lt_not_eq (cauchy_real_exp v) (cauchy_real_exp u)).
    + apply (cauchy_real_exp_mono v u). exact Hvlt.
    + apply real_eq_sym. exact Heq.
Qed.

(* The embedded log is additive: ln(a*b) = ln a + ln b, at the c_powq       *)
(* premises (real_log_mult via exponential injectivity; the positivity      *)
(* premises stay exactly the consumer's, witness-parametric in Hab, no      *)
(* transport needed).                                                       *)
Lemma real_log_nat_real_mult_gen :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (a b : nat) (Ha : NatLe 1 a) (Hb : NatLe 1 b) (Hab : NatLe 1 (a * b)),
  real_eq (real_log (nat_real (a * b)) (Hnpos (a * b) Hab))
          (real_plus (real_log (nat_real a) (Hnpos a Ha))
                     (real_log (nat_real b) (Hnpos b Hb))).
Proof.
  intros Hnpos a b Ha Hb Hab.
  apply cauchy_real_exp_inj.
  apply (real_eq_trans _ (nat_real (a * b))).
  - exact (cw_log_exp_right (nat_real (a * b)) (Hnpos (a * b) Hab)).
  - apply (real_eq_trans _ (real_mult (nat_real a) (nat_real b))).
    + exact (nat_real_mul a b).
    + apply (real_eq_trans _
               (real_mult (cauchy_real_exp (real_log (nat_real a) (Hnpos a Ha)))
                          (cauchy_real_exp (real_log (nat_real b) (Hnpos b Hb))))).
      * apply RealSetoid.real_eq_mult_compat;
          [ apply real_eq_sym; exact (cw_log_exp_right (nat_real a) (Hnpos a Ha))
          | apply real_eq_sym; exact (cw_log_exp_right (nat_real b) (Hnpos b Hb)) ].
      * apply real_eq_sym.
        exact (cauchy_real_exp_plus (real_log (nat_real a) (Hnpos a Ha))
                 (real_log (nat_real b) (Hnpos b Hb))).
Qed.

(* ==== Section 3. The term law ==== *)

(* (a*b)^{-s} = a^{-s} * b^{-s} (the multiplicativity face of the           *)
(* Dirichlet term, consumed by the stem's divisor-sum split;                *)
(* witness-parametric in Hab).                                              *)
Lemma c_powq_mult_law_gen :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (a b : nat) (Ha : NatLe 1 a) (Hb : NatLe 1 b) (Hab : NatLe 1 (a * b))
         (s : Cx),
  c_eq (c_powq Hnpos (a * b) Hab s)
       (c_mult (c_powq Hnpos a Ha s) (c_powq Hnpos b Hb s)).
Proof.
  intros Hnpos a b Ha Hb Hab s.
  unfold c_powq.
  apply (c_eq_trans _
           (c_exp (c_plus
              (c_scale (real_opp real_one)
                 (c_mult s (c_of_real (real_log (nat_real a) (Hnpos a Ha)))))
              (c_scale (real_opp real_one)
                 (c_mult s (c_of_real (real_log (nat_real b) (Hnpos b Hb)))))))).
  - apply c_exp_wd.
    apply (c_eq_trans _
             (c_scale (real_opp real_one)
                (c_mult s (c_of_real (real_plus
                   (real_log (nat_real a) (Hnpos a Ha))
                   (real_log (nat_real b) (Hnpos b Hb))))))).
    + apply c_scale_wd. apply c_mult_congr; [ apply c_eq_refl | ].
      apply c_of_real_wd.
      exact (real_log_nat_real_mult_gen Hnpos a b Ha Hb Hab).
    + apply (c_eq_trans _
               (c_scale (real_opp real_one)
                  (c_plus (c_mult s (c_of_real (real_log (nat_real a) (Hnpos a Ha))))
                          (c_mult s (c_of_real (real_log (nat_real b) (Hnpos b Hb))))))).
      * apply c_scale_wd.
        apply (c_eq_trans _
                 (c_mult (c_plus (c_of_real (real_log (nat_real a) (Hnpos a Ha)))
                                 (c_of_real (real_log (nat_real b) (Hnpos b Hb)))) s)).
        -- apply (c_eq_trans _
                     (c_mult s (c_plus (c_of_real (real_log (nat_real a) (Hnpos a Ha)))
                                       (c_of_real (real_log (nat_real b) (Hnpos b Hb)))))).
           ++ apply c_mult_congr; [ apply c_eq_refl | apply c_of_real_plus ].
           ++ apply c_mult_comm.
        -- apply (c_eq_trans _
                     (c_plus (c_mult (c_of_real (real_log (nat_real a) (Hnpos a Ha))) s)
                             (c_mult (c_of_real (real_log (nat_real b) (Hnpos b Hb))) s))).
           ++ apply c_mult_distrib_l.
           ++ apply c_plus_congr; apply c_mult_comm.
      * apply c_eq_sym. apply c_scale_plus.
  - apply c_exp_plus.
Qed.

(* ==== Section 4. Supply-face audit tail ==== *)

(* Named-item census of this leaf:
   7 Lemmas (nat_real_mul, natle_mul, c_of_real_wd, c_of_real_plus,
   cauchy_real_exp_inj, real_log_nat_real_mult_gen, c_powq_mult_law_gen);
   zero statements beyond them, zero vm_compute, zero assumed constants. *)
