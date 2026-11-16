(** * cast_bridge: the strong cross-index bridge amplifying mach_edge_one.

    Mission.  Amplify the same-index convergence statement mach_edge_one
    (mach_fold_chain.v:280: 4 * mach_pi_quarter == cauchy_real_pi_leibniz
    as real_eq) into the strong cross-index rational bridge

      |mdot k - xL j| <= w k + 4 * pie_mag (2 * j + 2)   for all k, j,

    where mdot k = 16*S_k(1/5) - 4*S_k(1/239) is the Machin partial sum
    (the projection of the left side of mach_edge_one), xL j = lp_four *
    lp_odd j is the Leibniz partial sum (the projection of the right
    side), w k = 16*atan_mag(S k)(1/5) + 4*atan_mag(S k)(1/239) is the
    Machin own modulus, and 4 * pie_mag (2*j+2) = 4/(4j+5) is the
    Leibniz tail window e_j.  Statement faces are transcriptions of the
    exploration-volume section-two lines (chong1_exit_core.py:65/:73/
    :77/:84/:97, grid-checked there) per the M1:438 prescription: the
    bridge is assembled from mach_edge_one plus the two own moduli
    (atan_tail_bound on the Machin side, pie_tail4 on the Leibniz side)
    and Q order decidability for the limit elimination.  No new
    analytic content: every inequality used is an in-library statement.

    Dependencies.  S01_BaseRing (NatLe, NatLe_lift), S02_CauchyComplete
    (Real, real_eq and its projection lemmas, QltT/QleT'/QeqT carriers
    and bridges, qeq_imp_qle), S10_KVQuantTrig (cauchy_real_pi_leibniz,
    real_pi_leibniz_proj), S11_TP3B5 (arctan_partial, atan_mag,
    atan_tail_bound, arctan_real_proj), mach_fold_q (mach_pi_quarter,
    mach_pt_bound witnesses), mach_fold_chain (mach_edge_one),
    LW0MLicBridge (lw0m_xL), PiEnvelope (pie_mag, pie_tail4, pie_v_eq).

    References.  mach_edge_one = mach_fold_chain.v:280; atan_tail_bound
    = S11_TP3B5.v:301; lw0m_xL = LW0MLicBridge.v:20; pie_tail4 /
    pie_v_eq = PiEnvelope.v:517/:720; projection lemmas =
    S02_CauchyComplete.v:1305-1323; M1:438 prescription (P7 bridge-level
    assembly) and exploration-volume section-two statement faces.

    Constructivity.  Zero axioms, zero admitted goals; all statements
    are Set-carried (QleT' / sigT / sumbool); the Q order decision is
    built from Z.leb (mach_q_le_dec, Set-carried sumbool).  The Prop
    predicates Qle/Qlt appear only as interior scaffolding consumed
    from in-library statements, never as named-statement conclusions.
    No vm_compute on large constants; the proof is fully symbolic, so
    the evaluation budget of the 3695-bit numerator route is never
    touched.

    Build.  coqc -native-compiler no -q -Q . "" cast_bridge.v  (world
    directory holding S01-S15, UpReqIrrationalCriterion, PiEnvelope,
    mach_fold_q, mach_atan_addsub, mach_fold_chain compiled). *)

Require Import S01_BaseRing S02_CauchyComplete S03_QExp S10_KVQuantTrig
               S11_TP3B5 mach_fold_q mach_fold_chain LW0MLicBridge PiEnvelope.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax ZArith.
From Stdlib Require Import Lqa.

(* ============================================================ *)
(* Section 1.  Statement-face definitions (transcriptions).      *)
(* ============================================================ *)

(* Machin partial sum: mdot k = 16*S_k(1/5) - 4*S_k(1/239); this is
   the pointwise projection of real_mult (real_const 4) mach_pi_quarter,
   the left side of mach_edge_one. *)
Definition mach_mdot (k : nat) : Q :=
  16 * arctan_partial k (1 # 5) - 4 * arctan_partial k (1 # 239).

(* Machin own modulus: w k = 16*a_{k+1}(1/5) + 4*a_{k+1}(1/239), the
   atan_tail_bound tail width of the Machin sequence from depth k. *)
Definition mach_own_modulus (k : nat) : Q :=
  16 * atan_mag (Datatypes.S k) (1 # 5)
  + 4 * atan_mag (Datatypes.S k) (1 # 239).

(* Q order decision, Set-carried sumbool, from the computable Z cross
   products; used only for the limit elimination of Section 6. *)
Definition mach_q_le_dec (u v : Q) : sumbool (Qle u v) (Qlt v u).
Proof.
  destruct u as [nu du]. destruct v as [nv dv].
  destruct (Z.leb (nu * Zpos dv) (nv * Zpos du)) eqn:Hb.
  - apply left. unfold Qle. simpl.
    apply (proj1 (Z.leb_le (nu * Zpos dv) (nv * Zpos du))).
    exact Hb.
  - apply right. unfold Qlt. simpl.
    apply (proj1 (Z.nle_gt (nu * Zpos dv) (nv * Zpos du))).
    apply (proj1 (Z.leb_nle (nu * Zpos dv) (nv * Zpos du))).
    exact Hb.
Defined.

(* ============================================================ *)
(* Section 2.  Projection bridges (definitional bookkeeping).    *)
(* ============================================================ *)

(* The Machin vertex projection: projT1 mach_pi_quarter n. *)
Lemma mach_pi_quarter_proj : forall n : nat,
  projT1 mach_pi_quarter n ==
  4 * arctan_partial n (1 # 5) - arctan_partial n (1 # 239).
Proof.
  intro n.
  unfold mach_pi_quarter, mach_atan_one_fifth, mach_atan_1_239.
  rewrite (real_plus_proj (real_mult (real_const 4)
             (cauchy_real_arctan (real_const (1 # 5)) mach_pt_bound_1_5))
             (real_opp (cauchy_real_arctan (real_const (1 # 239))
                         mach_pt_bound_1_239)) n).
  rewrite (real_mult_proj (real_const 4)
             (cauchy_real_arctan (real_const (1 # 5)) mach_pt_bound_1_5) n).
  rewrite (real_const_proj 4 n).
  rewrite (real_opp_proj (cauchy_real_arctan (real_const (1 # 239))
                          mach_pt_bound_1_239) n).
  rewrite (arctan_real_proj (real_const (1 # 5)) mach_pt_bound_1_5 n).
  rewrite (arctan_real_proj (real_const (1 # 239)) mach_pt_bound_1_239 n).
  rewrite (real_const_proj (1 # 5) n).
  rewrite (real_const_proj (1 # 239) n).
  ring.
Qed.

(* The left side of mach_edge_one projects to mach_mdot. *)
Lemma mach_edge_lhs_proj : forall n : nat,
  projT1 (real_mult (real_const 4) mach_pi_quarter) n == mach_mdot n.
Proof.
  intro n.
  rewrite (real_mult_proj (real_const 4) mach_pi_quarter n).
  rewrite (real_const_proj 4 n).
  rewrite (mach_pi_quarter_proj n).
  unfold mach_mdot.
  ring.
Qed.

(* The right side of mach_edge_one projects to lw0m_xL. *)
Lemma mach_xl_proj : forall n : nat,
  projT1 cauchy_real_pi_leibniz n == lw0m_xL n.
Proof.
  intro n.
  rewrite (real_pi_leibniz_proj n).
  reflexivity.
Qed.

(* ============================================================ *)
(* Section 3.  Unit-domain witnesses for the tail bounds.        *)
(* ============================================================ *)

Lemma mach_abs_1_5_unit : QleT' (Qabs (1 # 5)) 1.
Proof.
  pose proof (QltT_to_Qlt 0 (1 # 5) mach_q_pos_1_5) as Hp.
  apply Qle_to_QleT'.
  rewrite (Qabs_pos (1 # 5) (Qlt_le_weak 0 (1 # 5) Hp)).
  change (1 * 1 <= 1 * 5)%Z.
  lia.
Qed.

Lemma mach_abs_1_239_unit : QleT' (Qabs (1 # 239)) 1.
Proof.
  pose proof (QltT_to_Qlt 0 (1 # 239) mach_q_range_0_lt_1_239T) as Hp.
  apply Qle_to_QleT'.
  rewrite (Qabs_pos (1 # 239) (Qlt_le_weak 0 (1 # 239) Hp)).
  change (1 * 1 <= 1 * 239)%Z.
  lia.
Qed.

(* ============================================================ *)
(* Section 4.  The two own moduli.                               *)
(* ============================================================ *)

(* Machin own modulus, from atan_tail_bound on both component series. *)
Lemma mach_mdot_own_modulus : forall k n : nat, (k <= n)%nat ->
  QleT' (Qabs (mach_mdot k - mach_mdot n)) (mach_own_modulus k).
Proof.
  intros k n Hkn.
  apply Qle_to_QleT'.
  pose proof (atan_tail_bound (1 # 5) k n mach_abs_1_5_unit Hkn) as HA.
  pose proof (atan_tail_bound (1 # 239) k n mach_abs_1_239_unit Hkn) as HB.
  assert (Habs16 : Qabs 16 == 16)
    by (apply Qabs_pos; change (0 * 1 <= 16 * 1)%Z; lia).
  assert (Habs4 : Qabs 4 == 4)
    by (apply Qabs_pos; change (0 * 1 <= 4 * 1)%Z; lia).
  rewrite (Qabs_Qminus (mach_mdot k) (mach_mdot n)).
  assert (Hexp : mach_mdot n - mach_mdot k ==
                 16 * (arctan_partial n (1 # 5) - arctan_partial k (1 # 5))
                 - 4 * (arctan_partial n (1 # 239)
                        - arctan_partial k (1 # 239)))
    by (unfold mach_mdot; ring).
  rewrite Hexp.
  assert (Htri : Qle (Qabs (16 * (arctan_partial n (1 # 5)
                                 - arctan_partial k (1 # 5))
                          - 4 * (arctan_partial n (1 # 239)
                                 - arctan_partial k (1 # 239))))
                      (16 * Qabs (arctan_partial n (1 # 5)
                                  - arctan_partial k (1 # 5))
                       + 4 * Qabs (arctan_partial n (1 # 239)
                                   - arctan_partial k (1 # 239)))).
  { assert (Hpm : 16 * (arctan_partial n (1 # 5) - arctan_partial k (1 # 5))
                  - 4 * (arctan_partial n (1 # 239)
                         - arctan_partial k (1 # 239))
                  == 16 * (arctan_partial n (1 # 5) - arctan_partial k (1 # 5))
                     + (- (4 * (arctan_partial n (1 # 239)
                                - arctan_partial k (1 # 239)))))
      by ring.
    rewrite Hpm.
    apply (Qle_trans _ (Qabs (16 * (arctan_partial n (1 # 5)
                                    - arctan_partial k (1 # 5)))
                        + Qabs (- (4 * (arctan_partial n (1 # 239)
                                       - arctan_partial k (1 # 239))))) _).
    - apply Qabs_triangle.
    - rewrite (Qabs_Qmult 16 (arctan_partial n (1 # 5)
                              - arctan_partial k (1 # 5))).
      rewrite Habs16.
      rewrite (Qabs_opp (4 * (arctan_partial n (1 # 239)
                             - arctan_partial k (1 # 239)))).
      rewrite (Qabs_Qmult 4 (arctan_partial n (1 # 239)
                             - arctan_partial k (1 # 239))).
      rewrite Habs4.
      apply qeq_imp_qle. ring. }
  apply (Qle_trans _ (16 * Qabs (arctan_partial n (1 # 5)
                                    - arctan_partial k (1 # 5))
                      + 4 * Qabs (arctan_partial n (1 # 239)
                                  - arctan_partial k (1 # 239))) _).
  - exact Htri.
  - apply Qplus_le_compat.
    + rewrite (Qmult_comm 16 (Qabs (arctan_partial n (1 # 5)
                                   - arctan_partial k (1 # 5)))).
      rewrite (Qmult_comm 16 (atan_mag (Datatypes.S k) (1 # 5))).
      apply Qmult_le_compat_r.
      * exact HA.
      * change (0 * 1 <= 16 * 1)%Z.
        lia.
    + rewrite (Qmult_comm 4 (Qabs (arctan_partial n (1 # 239)
                                   - arctan_partial k (1 # 239)))).
      rewrite (Qmult_comm 4 (atan_mag (Datatypes.S k) (1 # 239))).
      apply Qmult_le_compat_r.
      * exact HB.
      * change (0 * 1 <= 4 * 1)%Z.
        lia.
Qed.

(* Leibniz tail window: |xL n - xL j| <= 4/(4j+5) = 4*pie_mag(2j+2)
   for j <= n, from pie_tail4 via the pie_v_eq sequence identity. *)
Lemma mach_xl_tail : forall j n : nat, (j <= n)%nat ->
  QleT' (Qabs (lw0m_xL n - lw0m_xL j)) (4 * pie_mag (2 * j + 2)).
Proof.
  intros j n Hjn.
  apply Qle_to_QleT'.
  assert (Hidx : (2 * j + 2 <= 2 * n + 2)%nat) by lia.
  pose proof (pie_tail4 (2 * j + 2) (2 * n + 2) Hidx) as HT.
  rewrite <- (pie_v_eq n) in HT.
  rewrite <- (pie_v_eq j) in HT.
  unfold lw0m_xL.
  exact HT.
Qed.

(* ============================================================ *)
(* Section 5.  The weak same-index bridge, from mach_edge_one.   *)
(* ============================================================ *)

(* mach_edge_one says the two sides are equal as reals; by definition
   of real_eq this means the same-index gaps |mdot n - xL n| eventually
   fall below every positive rational eta.  The projection equalities
   are transported through the QltT carrier with the S02 congruence
   lemma qltT_eq_compat_l (rewrites run in plain top-level Qeq goals,
   never inside the Id carrier). *)
Definition mach_edge_weak_gap : forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (Qabs (mach_mdot n - lw0m_xL n)) eps).
Proof.
  intros eps Heps.
  pose proof mach_edge_one as H1.
  unfold real_eq in H1.
  specialize (H1 eps Heps).
  destruct H1 as [N HN].
  exists N.
  intros n HNn.
  specialize (HN n HNn).
  assert (Hpt : (projT1 (real_mult (real_const 4) mach_pi_quarter) n
                 - projT1 cauchy_real_pi_leibniz n)
                == (mach_mdot n - lw0m_xL n)).
  { rewrite (mach_edge_lhs_proj n).
    rewrite (mach_xl_proj n).
    ring. }
  pose proof (Qabs_wd _ _ Hpt) as Habspt.
  exact (qltT_eq_compat_l _ _ _ Habspt HN).
Qed.

(* ============================================================ *)
(* Section 6.  The strong bridge (limit elimination).            *)
(* ============================================================ *)

Theorem mach_edge_bridge_amplify : forall (k j : nat),
  QleT' (Qabs (mach_mdot k - lw0m_xL j))
        (mach_own_modulus k + 4 * pie_mag (2 * j + 2)).
Proof.
  intros k j.
  apply Qle_to_QleT'.
  destruct (mach_q_le_dec (Qabs (mach_mdot k - lw0m_xL j))
             (mach_own_modulus k + 4 * pie_mag (2 * j + 2)))
    as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    (* Hgt : v < u with u = |mdot k - xL j|, v = w k + e j.
       Halve the gap: eta = (u - v)/2 > 0. *)
    assert (Heta0 : Qlt 0
             ((1 # 2) * (Qabs (mach_mdot k - lw0m_xL j)
                         - (mach_own_modulus k + 4 * pie_mag (2 * j + 2)))))
      by lra.
    destruct (mach_edge_weak_gap
               ((1 # 2) * (Qabs (mach_mdot k - lw0m_xL j)
                           - (mach_own_modulus k + 4 * pie_mag (2 * j + 2))))
               (Qlt_to_QltT 0 _
                 Heta0)) as [N HN].
    remember (Nat.max N (Nat.max k j)) as n eqn:Hndef.
    assert (HnN : NatLe N n) by (apply NatLe_lift; lia).
    assert (Hkn : (k <= n)%nat) by lia.
    assert (Hjn : (j <= n)%nat) by lia.
    pose proof (HN n HnN) as HgapT.
    pose proof (QltT_to_Qlt _ _ HgapT) as Hgap.
    (* three-point triangles, built from Qabs_triangle with ring rewrites *)
    assert (Hr1 : (mach_mdot k - mach_mdot n)
                  + (mach_mdot n - lw0m_xL j) == mach_mdot k - lw0m_xL j)
      by ring.
    assert (T1 : Qle (Qabs (mach_mdot k - lw0m_xL j))
                     (Qabs (mach_mdot k - mach_mdot n)
                      + Qabs (mach_mdot n - lw0m_xL j))).
    { pose proof (Qabs_triangle (mach_mdot k - mach_mdot n)
                                (mach_mdot n - lw0m_xL j)) as HT.
      rewrite Hr1 in HT. exact HT. }
    assert (Hr2 : (mach_mdot n - lw0m_xL n)
                  + (lw0m_xL n - lw0m_xL j) == mach_mdot n - lw0m_xL j)
      by ring.
    assert (T2 : Qle (Qabs (mach_mdot n - lw0m_xL j))
                     (Qabs (mach_mdot n - lw0m_xL n)
                      + Qabs (lw0m_xL n - lw0m_xL j))).
    { pose proof (Qabs_triangle (mach_mdot n - lw0m_xL n)
                                (lw0m_xL n - lw0m_xL j)) as HT.
      rewrite Hr2 in HT. exact HT. }
    pose proof (mach_mdot_own_modulus k n Hkn) as HownT.
    pose proof (QleT'_to_Qle _ _ HownT) as Hown.
    pose proof (mach_xl_tail j n Hjn) as HtailT.
    pose proof (QleT'_to_Qle _ _ HtailT) as Htail.
    (* second triangle leg: |mdot n - xL j| <= eta + e j *)
    assert (H2 : Qle (Qabs (mach_mdot n - lw0m_xL j))
                     ((1 # 2) * (Qabs (mach_mdot k - lw0m_xL j)
                                 - (mach_own_modulus k
                                    + 4 * pie_mag (2 * j + 2)))
                      + 4 * pie_mag (2 * j + 2))).
    { apply (Qle_trans _ (Qabs (mach_mdot n - lw0m_xL n)
                          + Qabs (lw0m_xL n - lw0m_xL j)) _).
      - exact T2.
      - apply Qplus_le_compat.
        + apply Qlt_le_weak. exact Hgap.
        + exact Htail. }
    (* first triangle leg: u <= v + eta *)
    assert (H1 : Qle (Qabs (mach_mdot k - lw0m_xL j))
                     (mach_own_modulus k + 4 * pie_mag (2 * j + 2)
                      + (1 # 2) * (Qabs (mach_mdot k - lw0m_xL j)
                                  - (mach_own_modulus k
                                     + 4 * pie_mag (2 * j + 2))))).
    { apply (Qle_trans _ (Qabs (mach_mdot k - mach_mdot n)
                          + Qabs (mach_mdot n - lw0m_xL j)) _).
      - exact T1.
      - apply (Qle_trans _ (mach_own_modulus k
                            + ((1 # 2) * (Qabs (mach_mdot k - lw0m_xL j)
                                        - (mach_own_modulus k
                                           + 4 * pie_mag (2 * j + 2)))
                               + 4 * pie_mag (2 * j + 2))) _).
        + apply Qplus_le_compat.
          * exact Hown.
          * exact H2.
        + apply qeq_imp_qle. ring. }
    (* v + eta < u (halving), so u < u: contradiction. *)
    assert (Hcontr : Qlt (mach_own_modulus k + 4 * pie_mag (2 * j + 2)
                          + (1 # 2) * (Qabs (mach_mdot k - lw0m_xL j)
                                      - (mach_own_modulus k
                                         + 4 * pie_mag (2 * j + 2))))
                         (Qabs (mach_mdot k - lw0m_xL j)))
      by lra.
    assert (Huu : Qlt (Qabs (mach_mdot k - lw0m_xL j))
                      (Qabs (mach_mdot k - lw0m_xL j)))
      by (apply (Qle_lt_trans _ _ _ H1 Hcontr)).
    exact (Qlt_irrefl _ Huu).
Defined.

Print Assumptions mach_edge_bridge_amplify.
