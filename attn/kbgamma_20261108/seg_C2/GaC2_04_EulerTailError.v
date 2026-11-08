(* ConstructiveWorld-Main - the partial-product error estimate of the finite
   Euler product (smooth-tail face). *)
(** * GaC2_04_EulerTailError: the smooth-tail error estimate.
    Mission.  Card C2.04, zero-new-slot carrier: the smooth tail [R_N]
      of the C2.03 stem is bounded by the condensation tail bound at
      M = N.  The complex n-fold triangle is NOT available in the tree
      (the C2.02 slot L-C2.02-C stays open and is NOT consumed here),
      so the numeric face is carried on the real part: cRe (R_N Hnpos N
      (c_of_real sig)) <= [r_stail] N M_N M_N (filtered sigma-sum
      dominates: the real part of each n^{-sig} term is n^{-sig} > 0
      by exp-positivity) < [r_m1sig] N * [r_geom_const],
      with r_stail N M0 m = sum_{N < d <= m, dvdb d M0} d^{-sig}, the
      two filters of the R_N summand, and the condensation chain
      replayed from the _c engine faces ([r_tail_mono]/
      [r_tail_dyadic]/[r_gsum_lt_geom], the Hnormtri-free core of the
      stem's [condensation_tail_bound]).  The identity face is
      re-exported from the C2.03 stem:
      [zeta_part_add_R_N] : D(M_N) = zeta_part N + R_N.  Both faces
      together are the C2.05 consumption carrier.
    Dependencies.  Stdlib [Arith.Arith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import),
      [S02_CauchyComplete], [S03_QExp] ([cauchy_real_exp_pos]),
      [S07_RealSetoidExpLog], [CxRealPairCore], [CxRealPairExpLog],
      [GaC2_01_DirichletPartialSum] ([c_powq]/[c_zeta_part]/
      [NatLe_one_S]), [GaC2_02_AbsConvTailBound_a] ([nat_real_lt]/
      [real_log_wd]/[nat_dyadic_cover]),
      [GaC2_02_AbsConvTailBound_b] ([r_ln]/[r_npow]/[r_npow_slice]/
      [r_tsum]/[r_tsum_r_tail]), [GaC2_02_AbsConvTailBound_c]
      ([r_tail_mono]/[r_tail_dyadic]/[r_gsum_lt_geom]/[r_m1sig]/
      [r_geom_const]/[r_q1]/pos faces), [GaC2_03_a] ([cxsum]/
      [dvdb]), [GaC2_03_b] ([dvd_le]),
      [GaC2_03_FiniteEulerProduct] ([dpow]/[dpow_S]/[R_N]/
      [zeta_part_add_R_N]), [HansonLcm]/[abl_Pr_lcm_eq]
      ([hl_lcm_upto]/[hl_lcm_divide_all]/[plq_lcm_pos]) of this
      development.
    References.  Card C2.04, drafts_C2.md C2.04; the real-part carrier
      mirrors the C2.02 (b) assembly shape with the triangle slot
      removed.
    Constructivity.  Every named construction is carried by [Set]; the
      slot fillers [g2_hlnmono]/[g2_hln2pos] are L0 stock castings
      ([real_log_lt_mono] S07:6540 + [real_log_one] S07:7894 +
      [real_lt_zero_one] S07:6967, the probe-verified shapes); no
      vm_compute; every proof closes under the global context;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_04_EulerTailError.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98 -AllowG3
      -GearForce 0 -CoreN 2). *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_02_AbsConvTailBound_b.
Require Import GaC2_02_AbsConvTailBound_c.
Require Import GaC2_03_a.
Require Import GaC2_03_b.
Require Import GaC2_03_FiniteEulerProduct.
Require Import HansonLcm.
Require Import abl_Pr_lcm_eq.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* ==== Section 0. The L0 slot fillers (probe-verified shapes) ==== *)

(* The log-monotonicity slot of the _b/_c engine leaves, cast from the S07  *)
(* L0 stock (real_log is the definitional alias of cw_log, S07:7881).       *)
Definition g2_hlnmono :
  forall (m n : nat) (Hm : real_lt real_zero (nat_real m))
         (Hn : real_lt real_zero (nat_real n)),
    real_lt (nat_real m) (nat_real n) ->
    real_lt (real_log (nat_real m) Hm) (real_log (nat_real n) Hn) :=
  fun m n Hm Hn H => real_log_lt_mono (nat_real m) (nat_real n) Hm Hn H.

(* The ln-2 positivity slot: nat_real 1 < nat_real 2 (the _a order face),   *)
(* log-monotonicity, and the unit-log collapse (real_log_one).              *)
Definition g2_hln2pos (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n)) :
  real_lt real_zero (r_ln Hnpos 2 (NatLe_one_S 1)).
Proof.
  assert (H12 : real_lt (real_log (nat_real 1) (Hnpos 1 (NatLe_one_S 0)))
                         (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))).
  { apply (real_log_lt_mono (nat_real 1) (nat_real 2)).
    exact (nat_real_lt 1 2 (NatLe_lift 2 2 (Nat.le_refl 2))). }
  apply (real_eq_lt_lt real_zero
           (real_log (nat_real 1) (Hnpos 1 (NatLe_one_S 0)))
           (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))).
  - apply real_eq_sym.
    apply (real_eq_trans _ real_zero).
    + apply (real_eq_trans _ (real_log real_one real_lt_zero_one)).
      * exact (real_log_wd (nat_real 1) real_one (Hnpos 1 (NatLe_one_S 0))
                 real_lt_zero_one GaC2_03_f.nat_real_one).
      * exact (real_log_one real_lt_zero_one).
    + apply real_eq_refl.
  - exact H12.
Defined.

(* ==== Section 1. The smooth sigma-tail sum ==== *)

Section EulerTailError.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable sig : Real.
Hypothesis Hsig1 : real_lt real_one sig.

(* The dvdb-filtered sigma tail: sum_{N < d <= m, d | M0} d^{-sig}          *)
(* (both filters of the R_N summand; the unfiltered scale is the _b         *)
(* r_tsum).                                                                 *)
Fixpoint r_stail (N M0 m : nat) : Real :=
  match m with
  | O => real_zero
  | S m' => real_plus (r_stail N M0 m')
              (if Nat.ltb N (S m') then
                 (if dvdb (S m') M0 then r_npow Hnpos sig (S m') (NatLe_one_S m')
                  else real_zero)
               else real_zero)
  end.

(* Each term is strictly positive (exp-positivity, S03). *)
Lemma r_npow_pos : forall (n : nat) (Hn : NatLe 1 n),
  real_lt real_zero (r_npow Hnpos sig n Hn).
Proof.
  intros n Hn. exact (cauchy_real_exp_pos (real_mult (real_opp sig) (r_ln Hnpos n Hn))).
Qed.

(* The filtered sum is bounded by the unfiltered one (deleting positive     *)
(* summands; both are climbed over the same range). *)
Lemma r_stail_le_rtail : forall N M : nat,
  real_le (r_stail N M M) (r_tsum Hnpos sig N M).
Proof.
  intros N M.
  assert (Hgen : forall m : nat, real_le (r_stail N M m) (r_tsum Hnpos sig N m)).
  { induction m as [|m IH].
    - cbn [r_stail r_tsum]. apply real_le_refl.
    - cbn [r_stail r_tsum]. destruct (Nat.ltb N (S m)) eqn:Hlt.
      + destruct (dvdb (S m) M) eqn:Ed.
        * apply real_le_plus_compat; [ exact IH | apply real_le_refl ].
        * apply real_le_plus_compat; [ exact IH | ].
          apply (real_lt_le_iff (real_zero)
                   (r_npow Hnpos sig (S m) (NatLe_one_S m))).
          left. exact (r_npow_pos (S m) (NatLe_one_S m)).
      + apply real_le_plus_compat; [ exact IH | apply real_le_refl ]. }
  exact (Hgen M).
Qed.

(* The real part of the smooth tail dominates zero termwise, hence is       *)
(* bounded by the filtered sigma sum (r_npow_slice: cRe (n^{-sig}) =        *)
(* n^{-sig}). *)
Lemma cRe_R_le_stail : forall N M : nat,
  real_le (cRe (cxsum (fun d => if Nat.ltb N d then
                                  (if dvdb d M then dpow Hnpos (c_of_real sig) d else c_zero)
                                else c_zero) M))
          (r_stail N M M).
Proof.
  intros N M.
  assert (Hgen : forall m : nat,
    real_le (cRe (cxsum (fun d => if Nat.ltb N d then
                                    (if dvdb d M then dpow Hnpos (c_of_real sig) d else c_zero)
                                  else c_zero) m))
            (r_stail N M m)).
  { induction m as [|m IH].
  - cbn [cxsum r_stail]. apply real_le_refl.
  - assert (Hslice : forall d' : nat,
      real_eq (cRe (dpow Hnpos (c_of_real sig) (S d')))
              (r_npow Hnpos sig (S d') (NatLe_one_S d'))).
    { intros d'. cbn [dpow].
      exact (r_npow_slice Hnpos sig (S d') (NatLe_one_S d')). }
    cbn [cxsum r_stail cRe c_plus].
    destruct (Nat.ltb N (S m)) eqn:Hlt.
    + destruct (dvdb (S m) M) eqn:Ed.
      * apply (real_le_trans _
                 (real_plus (cRe (cxsum (fun d => if Nat.ltb N d then
                                             (if dvdb d M then
                                                dpow Hnpos (c_of_real sig) d
                                              else c_zero) else c_zero) m))
                            (cRe (dpow Hnpos (c_of_real sig) (S m))))).
        -- apply (RealSetoid.real_eq_le _ _
                    (real_plus_comm (cRe (dpow Hnpos (c_of_real sig) (S m)))
                                 (cRe (cxsum (fun d => if Nat.ltb N d then
                                                     (if dvdb d M then
                                                        dpow Hnpos (c_of_real sig) d
                                                      else c_zero) else c_zero) m)))).
        -- apply real_le_plus_compat.
           ++ exact IH.
           ++ apply (RealSetoid.real_eq_le _ _ (Hslice m)).
      * apply (real_le_trans _
                 (real_plus (cRe (cxsum (fun d => if Nat.ltb N d then
                                             (if dvdb d M then
                                                dpow Hnpos (c_of_real sig) d
                                              else c_zero) else c_zero) m))
                            (cRe c_zero))).
        -- apply (RealSetoid.real_eq_le _ _
                    (real_plus_comm (cRe c_zero)
                                 (cRe (cxsum (fun d => if Nat.ltb N d then
                                                     (if dvdb d M then
                                                        dpow Hnpos (c_of_real sig) d
                                                      else c_zero) else c_zero) m)))).
        -- apply real_le_plus_compat.
           ++ exact IH.
           ++ cbn [cRe c_zero]. apply real_le_refl.
    + apply (real_le_trans _
               (real_plus (cRe (cxsum (fun d => if Nat.ltb N d then
                                           (if dvdb d M then
                                              dpow Hnpos (c_of_real sig) d
                                            else c_zero) else c_zero) m))
                          (cRe c_zero))).
      -- apply (RealSetoid.real_eq_le _ _
                  (real_plus_comm (cRe c_zero)
                               (cRe (cxsum (fun d => if Nat.ltb N d then
                                                   (if dvdb d M then
                                                      dpow Hnpos (c_of_real sig) d
                                                    else c_zero) else c_zero) m)))).
      -- apply real_le_plus_compat.
         ++ exact IH.
         ++ cbn [cRe c_zero]. apply real_le_refl. }
  exact (Hgen M).
Qed.

(* The condensation chain at the smooth tail (the Hnormtri-free core of     *)
(* the stem's condensation_tail_bound, replayed from the _c engine). *)
Lemma smooth_tail_condensation : forall (N : nat) (HN : NatLe 1 N),
  real_lt (r_stail N (hl_lcm_upto N) (hl_lcm_upto N))
          (real_mult (r_m1sig Hnpos sig N HN)
                     (r_geom_const Hnpos sig Hsig1 (g2_hln2pos Hnpos))).
Proof.
  intros N HN.
  assert (HN1 : (1 <= N)%nat) by (apply NatLe_drop; exact HN).
  assert (HNM : Nat.divide N (hl_lcm_upto N))
    by (apply (hl_lcm_divide_all N N); [ exact HN1 | apply Nat.le_refl ]).
  assert (HBN : (N <= hl_lcm_upto N)%nat).
  { apply (dvd_le N (hl_lcm_upto N)); [ exact HN1 | apply plq_lcm_pos | exact HNM ]. }
  assert (HNL : NatLe N (hl_lcm_upto N)) by (apply NatLe_lift; exact HBN).
  destruct (nat_dyadic_cover N (hl_lcm_upto N) HN) as [K HK].
  apply (real_le_lt_trans _ (r_tail Hnpos sig N (hl_lcm_upto N))).
  - apply (real_le_trans _ (r_tsum Hnpos sig N (hl_lcm_upto N))).
    + exact (r_stail_le_rtail N (hl_lcm_upto N)).
    + exact (RealSetoid.real_eq_le _ _ (r_tsum_r_tail Hnpos sig N (hl_lcm_upto N))).
  - apply (real_le_lt_trans _
             (real_mult (r_m1sig Hnpos sig N HN) (r_gsum (r_q1 Hnpos sig) K))).
    + apply (real_le_trans _
               (r_tail Hnpos sig N (N * Nat.pow 2 K))).
      * exact (r_tail_mono Hnpos sig N (hl_lcm_upto N) (N * Nat.pow 2 K) HNL HK).
      * exact (r_tail_dyadic Hnpos sig Hsig1 g2_hlnmono N HN K).
    + apply (real_lt_mult_compat _ _ _ (r_m1sig_pos Hnpos sig N HN)).
      exact (r_gsum_lt_geom Hnpos sig Hsig1 (g2_hln2pos Hnpos) K).
Qed.

(* ==== Section 2. The error estimate (the C2.04 main face) ==== *)

(* The main face: the real part of the smooth tail is below the condensation *)
(* tail bound at M = N (strict). *)
Lemma euler_tail_error_bound : forall (N : nat) (HN : NatLe 1 N),
  real_lt (cRe (R_N Hnpos N (c_of_real sig)))
          (real_mult (r_m1sig Hnpos sig N HN)
                     (r_geom_const Hnpos sig Hsig1 (g2_hln2pos Hnpos))).
Proof.
  intros N HN.
  apply (real_le_lt_trans _ (r_stail N (hl_lcm_upto N) (hl_lcm_upto N))).
  - unfold R_N. exact (cRe_R_le_stail N (hl_lcm_upto N)).
  - exact (smooth_tail_condensation N HN).
Qed.

(* The identity face (re-exported from the C2.03 stem; the C2.05 consumption *)
(* carrier: D(M_N) = zeta_part N + R_N). *)
Lemma zeta_part_add_R_N_stem : forall (N : nat) (s : Cx), (1 <= N)%nat ->
  c_eq (dsumCx (dpow Hnpos s) (hl_lcm_upto N))
       (c_plus (c_zeta_part Hnpos N s) (R_N Hnpos N s)).
Proof.
  intros N s HN1.
  exact (GaC2_03_FiniteEulerProduct.zeta_part_add_R_N Hnpos N s HN1).
Qed.

End EulerTailError.

(* ==== Supply-face audit tail ==== *)

(* Named-item census of this leaf:
   1 Fixpoint (r_stail) + 2 Definitions (g2_hlnmono, g2_hln2pos -- the L0    *)
(* slot castings, Section-external) + 6 Lemmas (r_npow_pos, r_stail_le_     *)
(* rtail, cRe_R_le_stail, smooth_tail_condensation, euler_tail_error_bound, *)
(* zeta_part_add_R_N_stem); the Section carries the three C2.02-family      *)
(* slots (Hnpos / sig / Hsig1) and zero new GAPASUME slots; zero vm_compute,*)
(* zero assumed constants and zero abandoned proofs.                        *)
