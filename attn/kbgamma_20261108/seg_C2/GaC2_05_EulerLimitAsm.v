(* ConstructiveWorld-Main - the Euler limit assembly for zeta (finite faces;
   the full lim theorem is an open supply face). *)
(** * GaC2_05_EulerLimitAsm: the Euler limit assembly (finite faces).
    Mission.  Card C2.05: the assembly of zeta = lim prod (1 - p^-s)^-1.
      Tree levers: [real_cauchy_complete] (S02:3084, the constructive
      diagonal limit: a real-level Cauchy difference clause yields an
      existing limit point l with [real_lim] u l); the difference =
      tail identity [r_tail_chain]; the condensation chain replayed in
      GaC2_04.  NOT carried by the tree (honest
      open-supply note, the segment-end consumer's obligation): the
      vanishing m1sig M -> 0 as M -> infinity (equivalently ln
      unboundedness on [nat_real]); no log_lower/1-n
      limit face exists in S02/S03/S07.  The lim theorem is NOT closed
      here; this leaf supplies every finite face the lim
      assembly consumes, all zero-new-slot: (1) [r_zeta_seq] := r_tsum
      0 N, the real zeta partial-sum column; (2) [r_zeta_seq_eq_cRe]:
      r_zeta_seq N = cRe (c_zeta_part N (c_of_real sig)); (3)
      [r_zeta_diff_eq]: r_zeta_seq N - r_zeta_seq M = r_tail M N for
      M <= N (the Cauchy difference clause carrier); (4)
      [prod_zeta_diff]: eprod(Ktab) + (- zeta_part N) = R_N, the exact
      identity behind "lim prod - lim zeta = smooth tail"
      ([fin_euler_prod_eq_dsum] + [zeta_part_sub_dsum]; zero triangle);
      (5) [prod_zeta_diff_real]: cRe (eprod + (-zeta_part)) < the
      condensation bound at M = N (GaC2_04's [euler_tail_error_bound]).
      The downstream consumer completes the assembly: m1sig-vanishing
      -> Cauchy clause via (3) -> [real_cauchy_complete] -> [real_lim];
      the product column follows by (4)/(5).
    Dependencies.  Stdlib [Arith.Arith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import), [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [CxRealPairCore],
      [CxRealPairExpLog], [GaC2_01_DirichletPartialSum],
      [GaC2_02_AbsConvTailBound_b] ([r_tsum]/[r_tail]/[r_ln]/
      [r_npow]/[r_npow_slice]), [GaC2_02_AbsConvTailBound_c]
      ([r_tail_chain]), [GaC2_03_a] ([cxsum]/[dvdb]),
      [GaC2_03_c_eq_shim], [GaC2_03_FiniteEulerProduct] ([eprod]/
      [dpow]/[R_N]/[fin_euler_prod_eq_dsum]/[zeta_part_sub_dsum]), and
      [GaC2_04_EulerTailError] ([euler_tail_error_bound]/
      [g2_hln2pos]) of this development.
    References.  Card C2.05, drafts_C2.md C2.05; the lim carrier
      [real_lim] is the S02:884 Q-eps double-sided Set form (alignment
      only).
    Constructivity.  All constructions Set-carried; no vm_compute; every
      proof closes under the global context; [coqchk] reports zero assumed
      constants; the open-supply note is tree-face coverage, not an admission.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_05_EulerLimitAsm.v] compiles cleanly (exit 0),
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
Require Import GaC2_02_AbsConvTailBound_b.
Require Import GaC2_02_AbsConvTailBound_c.
Require Import GaC2_03_a.
Require Import GaC2_03_c_eq_shim.
Require Import GaC2_03_FiniteEulerProduct.
Require Import GaC2_04_EulerTailError.
Require Import HansonLcm.
Require Import abl_Pr_lcm_eq.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_enum_02.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Section EulerLimitAsm.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable sig : Real.
Hypothesis Hsig1 : real_lt real_one sig.

(* ==== Section 1. The real zeta column ==== *)

(* The real zeta partial sums: the sigma-series from zero. *)
Definition r_zeta_seq : nat -> Real := fun N => r_tsum Hnpos sig 0 N.

(* The cxsum-of-dpow bridge: the real part of the cxsum-carried zeta sum   *)
(* is the sigma series (pointwise r_npow_slice induction).                 *)
Lemma cRe_cxsum_dpow_tsum : forall N : nat,
  real_eq (cRe (cxsum (fun d => dpow Hnpos (c_of_real sig) d) N))
          (r_tsum Hnpos sig 0 N).
Proof.
  intro N. induction N as [|N IH].
  - cbn [cxsum r_tsum]. apply real_eq_refl.
  - cbn [cxsum cRe c_plus]. cbn [r_tsum Nat.ltb].
    assert (Hs : real_eq (cRe (dpow Hnpos (c_of_real sig) (S N)))
                         (r_npow Hnpos sig (S N) (NatLe_one_S N))).
    { cbn [dpow]. exact (r_npow_slice Hnpos sig (S N) (NatLe_one_S N)). }
    (* cxsum climbs new-term-first; r_tsum climbs old-term-first: the      *)
    (* trans re-bases the right side to the new-first order, then compat.  *)
    apply (real_eq_trans _
             (real_plus (r_npow Hnpos sig (S N) (NatLe_one_S N))
                        (r_tsum Hnpos sig 0 N))).
    + exact (RealSetoid.real_eq_plus_compat _ _ _ _ Hs IH).
    + exact (real_plus_comm (r_npow Hnpos sig (S N) (NatLe_one_S N))
                            (r_tsum Hnpos sig 0 N)).
Qed.

(* It is the real part of the complex partial sum (the stem cxsum face). *)
Lemma r_zeta_seq_eq_cRe : forall N : nat,
  real_eq (r_zeta_seq N)
          (cRe (c_zeta_part Hnpos N (c_of_real sig))).
Proof.
  intro N. unfold r_zeta_seq.
  apply (real_eq_trans _ (cRe (cxsum (fun d => dpow Hnpos (c_of_real sig) d) N))).
  - apply real_eq_sym. exact (cRe_cxsum_dpow_tsum N).
  - apply real_eq_sym. apply cRe_wd.
    exact (GaC2_03_FiniteEulerProduct.c_zeta_part_cxsum Hnpos N (c_of_real sig)).
Qed.

(* The Cauchy difference clause carrier: the column difference is exactly   *)
(* the sigma tail over (M, N]  (r_tail_chain 0 M N, re-based to r_tsum).    *)
Lemma r_zeta_diff_eq : forall M N : nat, NatLe M N ->
  real_eq (real_plus (r_zeta_seq N) (real_opp (r_zeta_seq M)))
          (r_tail Hnpos sig M N).
Proof.
  intros M N HMN. unfold r_zeta_seq.
  assert (H0M : NatLe 0 M) by (apply NatLe_lift; apply Nat.le_0_l).
  assert (E3 : real_eq (r_tail Hnpos sig 0 N)
                (real_plus (r_tsum Hnpos sig 0 M) (r_tail Hnpos sig M N))).
  { apply (real_eq_trans _
             (real_plus (r_tail Hnpos sig 0 M) (r_tail Hnpos sig M N))).
    - exact (r_tail_chain Hnpos sig 0 M N H0M HMN).
    - exact (RealSetoid.real_eq_plus_compat _ _ _ _
               (real_eq_sym _ _ (r_tsum_r_tail Hnpos sig 0 M))
               (real_eq_refl _)). }
  apply (real_eq_trans _
           (real_plus (real_plus (r_tsum Hnpos sig 0 M) (r_tail Hnpos sig M N))
                      (real_opp (r_tsum Hnpos sig 0 M)))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + exact (real_eq_trans (r_tsum Hnpos sig 0 N) (r_tail Hnpos sig 0 N)
               (real_plus (r_tsum Hnpos sig 0 M) (r_tail Hnpos sig M N))
               (r_tsum_r_tail Hnpos sig 0 N) E3).
    + apply real_eq_refl.
  - (* (X + Y) + (- X) = Y  by comm-reorder, assoc, opp, zero. *)
    apply (real_eq_trans _
             (real_plus (r_tail Hnpos sig M N) real_zero)).
    + apply (real_eq_trans _
               (real_plus (r_tail Hnpos sig M N)
                  (real_plus (r_tsum Hnpos sig 0 M)
                             (real_opp (r_tsum Hnpos sig 0 M))))).
      * apply (real_eq_trans _
                 (real_plus (real_plus (r_tail Hnpos sig M N)
                            (r_tsum Hnpos sig 0 M))
                           (real_opp (r_tsum Hnpos sig 0 M)))).
        -- apply (RealSetoid.real_eq_plus_compat _ _ _ _).
           ++ exact (real_plus_comm (r_tsum Hnpos sig 0 M)
                                    (r_tail Hnpos sig M N)).
           ++ apply real_eq_refl.
        -- apply (real_eq_sym _ _).
           exact (real_plus_assoc (r_tail Hnpos sig M N)
                                  (r_tsum Hnpos sig 0 M)
                                  (real_opp (r_tsum Hnpos sig 0 M))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)).
        exact (real_plus_opp (r_tsum Hnpos sig 0 M)).
    + exact (real_plus_zero (r_tail Hnpos sig M N)).
Qed.

(* ==== Section 2. The product-minus-zeta identity (complex, exact) ==== *)

(* eprod(Ktab) + (- zeta_part N) = R_N: the finite face of "lim prod -     *)
(* lim zeta = smooth tail"  (two trans legs over the stem's own faces).    *)
Lemma prod_zeta_diff : forall (N : nat) (s : Cx), (1 <= N)%nat ->
  c_eq (c_plus (eprod Hnpos (pen_primes_upto N)
                      (fun p => plm_v p (hl_lcm_upto N)) s)
               (c_opp (c_zeta_part Hnpos N s)))
       (R_N Hnpos N s).
Proof.
  intros N s HN1.
  apply (c_eq_trans _
           (c_plus (dsumCx (dpow Hnpos s) (hl_lcm_upto N))
                   (c_opp (c_zeta_part Hnpos N s)))).
  - apply c_plus_congr.
    + exact (fin_euler_prod_eq_dsum Hnpos N s).
    + apply c_eq_refl.
  - apply c_eq_sym. exact (zeta_part_sub_dsum Hnpos N s HN1).
Qed.

(* ==== Section 3. The real-part error face of the assembly ==== *)

(* The real part of the assembly difference is below the condensation      *)
(* bound at M = N (consuming GaC2_04's main face through cRe_wd).          *)
Lemma prod_zeta_diff_real : forall (N : nat) (HN : NatLe 1 N),
  real_lt (cRe (c_plus (eprod Hnpos (pen_primes_upto N)
                              (fun p => plm_v p (hl_lcm_upto N))
                              (c_of_real sig))
                       (c_opp (c_zeta_part Hnpos N (c_of_real sig)))))
          (real_mult (r_m1sig Hnpos sig N HN)
                     (r_geom_const Hnpos sig Hsig1 (g2_hln2pos Hnpos))).
Proof.
  intros N HN.
  assert (HN1 : (1 <= N)%nat) by (apply NatLe_drop; exact HN).
  apply (real_eq_lt_lt
           (cRe (c_plus (eprod Hnpos (pen_primes_upto N)
                           (fun p => plm_v p (hl_lcm_upto N)) (c_of_real sig))
                    (c_opp (c_zeta_part Hnpos N (c_of_real sig)))))
           (cRe (R_N Hnpos N (c_of_real sig)))
           (real_mult (r_m1sig Hnpos sig N HN)
                      (r_geom_const Hnpos sig Hsig1 (g2_hln2pos Hnpos)))).
  - apply cRe_wd. exact (prod_zeta_diff N (c_of_real sig) HN1).
  - exact (euler_tail_error_bound Hnpos sig Hsig1 N HN).
Qed.

End EulerLimitAsm.

(* ==== Supply-face audit tail ==== *)

(* Named-item census of this leaf:
   1 Definition (r_zeta_seq) + 5 Lemmas (cRe_cxsum_dpow_tsum,
   r_zeta_seq_eq_cRe, r_zeta_diff_eq, prod_zeta_diff, prod_zeta_diff_real);
   1 Section (EulerLimitAsm: variables Hnpos / sig, hypothesis Hsig1,
   discharged at End); zero vm_compute, zero assumed constants and zero
   abandoned proofs.  The open-supply note in the header stands: the
   vanishing face (m1sig M -> 0) is absent from the tree and is the
   downstream consumer's obligation. *)
