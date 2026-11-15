(** * GaC2_10_MtestGeomTail: the Weierstrass M-test machine faces of node C2-10.

    Mission.  The reachable segment of the node C2-10 construction ticket (the
    Weierstrass M-test double-series lane): the machine faces closing now over
    [GaC2_10_EtaContinuation]: (1) the sign machine of the eta partial sum column
    [d10_eta_sgn] with the name-reality bond to the C2-07 sign column [eta_sgn_cx];
    (2) the power-series algebra of the (b) row carriers [d10_cpow] / [d10_psum]
    (the step face, the squared-modulus growth face, the closed-form geometric
    telescope identity); (3) the decidable rational margin band of the geometric
    tail; (4) the M-test consumption face [d10_mtest_unif_face], the GAPASUME slot
    carrier of the uniform Cauchy conjunct of [zeta_tilde_analytic], with
    coefficient domination and scalar tail smallness as explicit premises; the
    three named statement rows of the node stay statement carriers.
    Dependencies.  [GaC2_10_EtaContinuation] (the node statement face, cast at
    the main-line commit 8e70342; consumed carriers [d10_eta_sgn], [d10_cpow],
    [d10_psum]); [S01_BaseRing] (NatLe import), [S02_CauchyComplete],
    [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC2_01_DirichletPartialSum],
    [GaC2_02_AbsConvTailBound_a]; from [GaC2_07_DirichletTestAbel] come [alt_sign] /
    [eta_sgn_cx], from [GaC2_09_DenomZeroSet_b] comes [d09_opp_opp]; Stdlib [QArith.QArith].

    References.  drafts_C2.md C2.10 row (b); cards_C2.md C2.10 row (b) (the
    Weierstrass M-test constructive land); GaC1_15_PowSeriesConv (the mirrored
    GAPASUME slot form); GaC2_02_AbsConvTailBound_c (the real-scalar tail segment).

    Constructivity.  The algebra faces close by pointwise ring or definitional
    steps; the margin band closes by vm_compute; zero assumed constants, zero
    proof abandonment; the consumption face is an honest slot carrier.

    Build.  coqc -native-compiler no -q -Q <closure root> "" GaC2_10_MtestGeomTail.v
    (flat build directory over the node require closure, thermal-guard wrapped). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_07_DirichletTestAbel.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_10_EtaContinuation.
From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The sign machine of the eta partial sum column.             *)
(* ===================================================================== *)

(* Double negation collapses on the complex carrier (pointwise ring).   *)
Lemma d10_mtest_opp_opp : forall z : Cx, c_eq (c_opp (c_opp z)) z.
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Defined.

(* The sign column negates at every step.                               *)
Lemma d10_mtest_sgn_step :
  forall n : nat, c_eq (d10_eta_sgn (S n)) (c_opp (d10_eta_sgn n)).
Proof.
  intro n. induction n as [|m IH].
  - simpl. exact (c_eq_sym _ _ (d10_mtest_opp_opp c_one)).
  - simpl. apply c_opp_congr. apply (c_eq_sym _ _ IH).
Defined.

(* The sign column is 2-periodic.                                       *)
Lemma d10_mtest_sgn_parity :
  forall n : nat, c_eq (d10_eta_sgn (S (S n))) (d10_eta_sgn n).
Proof.
  intro n. simpl. apply d10_mtest_opp_opp.
Defined.

(* Negation preserves the squared modulus (pointwise ring).             *)
Lemma d10_mtest_norm_sq_opp :
  forall z : Cx, real_eq (c_norm_sq (c_opp z)) (c_norm_sq z).
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Defined.

(* Negation of the real-line wrapper lands on the negated real scalar    *)
(* (pointwise ring; the imaginary component is the zero face).           *)
Lemma d10_mtest_opp_c_of_real :
  forall r : Real, c_eq (c_opp (c_of_real r)) (c_of_real (real_opp r)).
Proof.
  intro r. destruct r as [u Hu].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Defined.

(* The name-reality bond: the node sign column IS the C2-07 sign column *)
(* wrapped on the real line.  This hands the C2-07 parity supply rows    *)
(* ([abssum_alt_pair], [eta_sgn_bounded_pair]) to the node cluster.      *)
(* Route: both columns negate at every step and share the base value.    *)
Lemma d10_mtest_sgn_is_eta_sgn_cx :
  forall n : nat, c_eq (d10_eta_sgn n) (eta_sgn_cx n).
Proof.
  intro n. induction n as [|m IH].
  - unfold c_eq. split; apply real_eq_of_zero_diff; intro n0; simpl; ring.
  - apply (c_eq_trans _ (c_opp (eta_sgn_cx m))).
    + apply (c_eq_trans _ (c_opp (d10_eta_sgn m))).
      * apply d10_mtest_sgn_step.
      * apply c_opp_congr. exact IH.
    + exact (d10_mtest_opp_c_of_real (alt_sign m)).
Defined.

(* ===================================================================== *)
(* Section 2. The power-series algebra of the (b) row carriers.           *)
(* ===================================================================== *)

(* The partial-sum step face (definitional, the machine-cluster shape). *)
Lemma d10_mtest_psum_step : forall (c_n : nat -> Cx) (w : Cx) (N : nat),
  c_eq (d10_psum c_n w (S N))
       (c_plus (d10_psum c_n w N) (c_mult (c_n (S N)) (d10_cpow w (S N)))).
Proof. intros c_n w N. apply c_eq_refl. Qed.

(* The squared modulus of the monomial grows multiplicatively.          *)
Lemma d10_mtest_norm_sq_cpow_succ : forall (w : Cx) (k : nat),
  real_eq (c_norm_sq (d10_cpow w (S k)))
          (real_mult (c_norm_sq (d10_cpow w k)) (c_norm_sq w)).
Proof. intros w k. exact (c_norm_sq_mul (d10_cpow w k) w). Qed.

(* Multiplication against a negated factor commutes with negation        *)
(* (pointwise ring over variable pairs).                                 *)
Lemma d10_mtest_mult_opp_r : forall z w : Cx,
  c_eq (c_mult z (c_opp w)) (c_opp (c_mult z w)).
Proof.
  intros [a b] [c d].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Defined.

(* The four-term addition shuffle (pointwise ring over variable pairs).  *)
Lemma d10_mtest_cplus_shuffle : forall a b c d : Cx,
  c_eq (c_plus (c_plus a b) (c_plus c d)) (c_plus (c_plus a c) (c_plus b d)).
Proof.
  intros [a1 a2] [b1 b2] [c1 c2] [d1 d2].
  destruct a1 as [ua1 Ha1]; destruct a2 as [ua2 Ha2];
    destruct b1 as [ub1 Hb1]; destruct b2 as [ub2 Hb2];
    destruct c1 as [uc1 Hc1]; destruct c2 as [uc2 Hc2];
    destruct d1 as [ud1 Hd1]; destruct d2 as [ud2 Hd2].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Defined.

(* Distributing a plus-minus factor: (a - b) * x = a * x - b * x, all   *)
(* at the C level (no pointwise step on a stuck fixpoint atom).          *)
Lemma d10_mtest_mult_plus_opp_l : forall a b x : Cx,
  c_eq (c_mult (c_plus a (c_opp b)) x)
       (c_plus (c_mult a x) (c_opp (c_mult b x))).
Proof.
  intros a b x.
  apply (c_eq_trans _ (c_mult x (c_plus a (c_opp b)))).
  - apply c_mult_comm.
  - apply (c_eq_trans _ (c_plus (c_mult x a) (c_mult x (c_opp b)))).
    + apply c_distrib.
    + apply c_plus_congr.
      * apply c_mult_comm.
      * apply (c_eq_trans _ (c_opp (c_mult x b))).
        -- apply d10_mtest_mult_opp_r.
        -- apply c_opp_congr. apply (c_eq_sym _ _ (c_mult_comm b x)).
Defined.

(* The geometric telescope identity: the unit-coefficient partial sums   *)
(* satisfy (1 - w) * S_N = 1 - w^(N+1).  This is the closed-form algebra *)
(* core of the M-test tail estimate for the denominator geometric series *)
(* of the (b) row.  The inductive step is a C-level algebra chain: the   *)
(* monomial atom (a stuck fixpoint application) blocks pointwise         *)
(* reduction, so every real-level ring closer stays on variable pairs    *)
(* inside the three helper lemmas above.                                 *)
Lemma d10_mtest_geom_telescope : forall (w : Cx) (N : nat),
  c_eq (c_mult (c_plus c_one (c_opp w)) (d10_psum (fun _ : nat => c_one) w N))
       (c_plus c_one (c_opp (d10_cpow w (S N)))).
Proof.
  intros w N. induction N as [|m IH].
  - destruct w as [a b].
    destruct a as [ua Ha]; destruct b as [ub Hb].
    unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
  - apply (c_eq_trans _
      (c_plus (c_mult (c_plus c_one (c_opp w))
                      (d10_psum (fun _ : nat => c_one) w m))
              (c_mult (c_plus c_one (c_opp w)) (c_mult c_one (d10_cpow w (S m)))))).
    + apply c_distrib.
    + apply (c_eq_trans _
        (c_plus (c_plus c_one (c_opp (d10_cpow w (S m))))
                (c_mult (c_plus c_one (c_opp w)) (d10_cpow w (S m))))).
      * apply c_plus_congr.
        -- exact IH.
        -- apply c_mult_congr.
           ++ apply c_eq_refl.
           ++ apply c_mult_one.
      * assert (Hs1 : c_eq (c_mult (c_plus c_one (c_opp w)) (d10_cpow w (S m)))
                           (c_plus (d10_cpow w (S m))
                                   (c_opp (c_mult (d10_cpow w (S m)) w)))).
        { apply (c_eq_trans _
            (c_plus (c_mult c_one (d10_cpow w (S m)))
                    (c_opp (c_mult w (d10_cpow w (S m)))))).
          - exact (d10_mtest_mult_plus_opp_l c_one w (d10_cpow w (S m))).
          - apply c_plus_congr.
            + apply c_mult_one.
            + apply c_opp_congr. apply c_mult_comm. }
        apply (c_eq_trans _
          (c_plus (c_plus c_one (c_opp (d10_cpow w (S m))))
                  (c_plus (d10_cpow w (S m))
                          (c_opp (c_mult (d10_cpow w (S m)) w))))).
        { apply c_plus_congr.
          - apply c_eq_refl.
          - exact Hs1. }
        apply (c_eq_trans _
          (c_plus (c_plus c_one (d10_cpow w (S m)))
                  (c_plus (c_opp (d10_cpow w (S m)))
                          (c_opp (c_mult (d10_cpow w (S m)) w))))).
        { exact (d10_mtest_cplus_shuffle c_one (c_opp (d10_cpow w (S m)))
                   (d10_cpow w (S m)) (c_opp (c_mult (d10_cpow w (S m)) w))). }
        apply (c_eq_trans _
          (c_plus c_one
             (c_plus (d10_cpow w (S m))
                     (c_plus (c_opp (d10_cpow w (S m)))
                             (c_opp (c_mult (d10_cpow w (S m)) w)))))).
        { exact (c_eq_sym _ _ (c_plus_assoc c_one (d10_cpow w (S m))
                   (c_plus (c_opp (d10_cpow w (S m)))
                           (c_opp (c_mult (d10_cpow w (S m)) w))))). }
        apply (c_eq_trans _
          (c_plus c_one
             (c_plus (c_plus (d10_cpow w (S m)) (c_opp (d10_cpow w (S m))))
                     (c_opp (c_mult (d10_cpow w (S m)) w))))).
        { apply c_plus_congr.
          - apply c_eq_refl.
          - exact (c_plus_assoc (d10_cpow w (S m)) (c_opp (d10_cpow w (S m)))
                     (c_opp (c_mult (d10_cpow w (S m)) w))). }
        apply (c_eq_trans _ (c_plus c_one (c_opp (c_mult (d10_cpow w (S m)) w)))).
        { apply c_plus_congr.
          - apply c_eq_refl.
          - apply (c_eq_trans _ (c_plus c_zero (c_opp (c_mult (d10_cpow w (S m)) w)))).
            ++ apply c_plus_congr.
               ** apply c_plus_opp.
               ** apply c_eq_refl.
            ++ apply c_plus_zero. }
        apply c_eq_refl.
Defined.

(* ===================================================================== *)
(* Section 3. The M-test margin band and the consumption face.            *)
(* ===================================================================== *)

(* The natural-power carrier on the rationals (the exponent notation     *)
(* of [QArith] carries a Z exponent in this tree, so the margin form     *)
(* uses this explicit recursion; vm_compute-friendly by construction).   *)
Fixpoint d10_qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S m => q * d10_qpow q m
  end.

(* The closed-form margin form of the geometric tail: the value of       *)
(* 2 * q^(M+1) / (1 - q) at the rational disk ratio q and the            *)
(* cutoff M.                                                             *)
Definition d10_mtest_margin_form (q : Q) (M : nat) : Q :=
  2 * d10_qpow q (M + 1) / (1 - q).

(* The decidable margin band at the sample q = 1/4, M = 12: the tail     *)
(* margin closes below one millionth (the strict face as the negated     *)
(* weak order, the certificate-face idiom of the node).                  *)
Lemma d10_mtest_margin_band_q1_4 :
  negb (Qle_bool (1#1000000) (d10_mtest_margin_form (1#4) 12)) = true.
Proof. vm_compute; reflexivity. Qed.

(* The M-test consumption face of the (b) row, in the GaC1-15 GAPASUME   *)
(* slot form.  The coefficient domination Hdom (each term of the power   *)
(* series dominated by the real sequence m_b on the column u) and the    *)
(* scalar tail smallness Htail enter as explicit premise arguments, so   *)
(* the carrier is born clean: zero assumption, zero abandonment.  The    *)
(* conclusion is verbatim the uniform Cauchy conjunct of                 *)
(* [zeta_tilde_analytic].  The discharge route of the body is the        *)
(* n-fold linear triangle supply row family (the C2-02-c segment, whose  *)
(* real-scalar block is closed) plus the eta disk family of the C2-07    *)
(* leaf; the body lands at mother-chain integration and is NOT claimed   *)
(* here.                                                                 *)
Definition d10_mtest_unif_face
  (c_n : nat -> Cx) (u : Cx) (m_b : nat -> Real)
  (Hdom : forall k : nat,
     real_le (c_norm_sq (c_mult (c_n k) (d10_cpow u k))) (m_b k))
  (Htail : forall eps : Q, QltT 0 eps ->
     sigT (fun M0 : nat => forall n : nat, NatLe M0 n ->
       real_lt (m_b n) (real_const eps))) : Set :=
  forall d : Q, QltT 0 d ->
    sigT (fun M0 : nat => forall N M : nat, NatLe M0 M -> NatLe M N ->
      real_lt (c_norm_sq
                 (c_plus (d10_psum c_n u N) (c_opp (d10_psum c_n u M))))
              (real_const d)).

(* End-of-file kernel audit on the two substantive machine faces.        *)
Print Assumptions d10_mtest_geom_telescope.
Print Assumptions d10_mtest_sgn_is_eta_sgn_cx.
