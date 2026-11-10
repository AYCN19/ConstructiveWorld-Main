(* ConstructiveWorld-Main - discharge and racing face of the three-cosine nonvanishing line engine. *)
(** * GaC3_Z03_NonzeroLine_race: the discharge and racing face of node
    C3-Z03.

    Mission.  The discharge and racing face of the three-cosine
    nonvanishing argument (node C3-Z03, segment C3).  Part 1 tail (the
    nonnegativity discharge): the weight factor is nonnegative
    ([z03_ew_pos]: the von Mangoldt weight is nonnegative and the
    exponential factor is positive), the square-form sum is
    asymptotically nonnegative ([z03_sqsum_ge0]), and Main face 1: the
    combined real part is asymptotically nonnegative
    ([z03_comb_nonneg], assumption-free, the tree-native form of the
    ZZ logderiv_zeta_ineq architecture).  Part 2: the racing
    contradiction in explicit-radius slot form ([z03_racing_contra])
    under Section Z03_Race with the registered premise slots (the
    four-term main part at the offset d [Hmain4], the sigma-term
    [Hsig3] and the doubled-ordinate [Htwo] upper bounds): under the
    explicit window arithmetic 3*B3 + B2 < 4*m0 (m0 = 1/(2d), positive
    by [Hd]), the nonnegativity face yields False.  The literal
    zeta-carrier statement of the card (drafts_C3.md C3-Z03) awaits
    the eta-continuation supply face (GaC2_10_EtaContinuation, not yet
    in the tree); the slot form is the registered consumption shape of
    the certified V03 pattern, and the eta-side supply line
    [GaC2_Iface_Eta] is held on the stem for the discharge.

    Dependencies.  The stem [GaC3_Z03_NonzeroLine] ([z03_comb],
    [z03_sqsum], [z03_comb_sqsum_eq], the [z03_pt] normalisation
    face), leaf b [GaC3_Z03_NonzeroLine_b] ([z03npos], [z03_eterm],
    [z03_le_mult_l], [z03_relax0_plus], [z03_wy_relax],
    [z03_lt_add_r], [z03_lt_eq_r], [z03_eq_relax_sym],
    [z03_relax_lt_false]), [S01_BaseRing] ([NatLe], selective import),
    [S02_CauchyComplete] ([real_lt_le_iff], [real_le_plus_compat],
    [QltT]/[QeqT]), [S07_RealSetoidExpLog] ([real_ge_relax],
    [real_ge_relax_of_pointwise], RealSetoid compat faces,
    [real_const_pos]), [S10_KVQuantTrig] ([cauchy_real_exp_pos]),
    [CxRealPairCore] ([real_zero_pt], [real_one_pt]),
    [CxRealPairExpLog] ([c_scale]),
    [GaC2_Iface_DS] ([NatLe_one_S] via the leaf import),
    [GaC3_Z01_LogDerivSeries] ([z01_lam], [z01_lam_ge0],
    [z01_manpart]), [GaC3_Z02_ThreeCosine]
    ([GaC3_Z02_sq_pointwise_nonneg]); Stdlib [QArith] (with [Qring]),
    [Setoid], [Morphisms], [Arith], [Lia].

    References.  ZZ theory (AFP PNT_with_Remainder) [logderiv_zeta_ineq]
    :136-163 (the three-cosine weighted inequality); drafts_C3.md C3-Z03
    (racing skeleton, explicit-radius obligation); cards_C3 C3-Z03
    (multiplicity main part: the zero-neighborhood main part -1/(2d)
    is the registered open supply face of the zero factorization
    route).

    Constructivity.  Every named construction is carried by [Set]; the
    nonnegativity face is carried by [real_ge_relax] (the asymptotic
    order, per the Z02 precedent).  Zero assumed constants, zero
    abandoned proofs, zero classical choice; the Section premises
    discharge as explicit premise arguments at End, so Print
    Assumptions of every named item reads Closed under the global
    context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_Z03_NonzeroLine_race.v] from the work directory through the
    dependency-closure build (50_toolkit/build_deposit.py); acceptance
    runs use 50_toolkit/accept_node.py and write accept/<node>.json. *)

Require S01_BaseRing.
(* Selective import (the S01 state-space field S shadows the nat          *)
(* constructor under a full import; only the Set-sorted nat bound face is *)
(* consumed). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z03_NonzeroLine_a.
Require Import GaC3_Z03_NonzeroLine_b.
Require Import GaC3_Z03_NonzeroLine.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_Z02_ThreeCosine.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* The weight factor is nonnegative: the von Mangoldt weight is         *)
(* nonnegative and the exponential factor is positive. *)
Lemma z03_ew_pos : forall (n : nat) (Hn : NatLe 1 n) (sg : Real),
  real_le real_zero (real_mult (z01_lam n) (z03_eterm n Hn sg)).
Proof.
  intros n Hn sg. destruct (z01_lam_ge0 n) as [Hlt | Heq].
  - apply (real_lt_le_iff real_zero (real_mult (z01_lam n) (z03_eterm n Hn sg))).
    left.
    apply (real_lt_eq_lt real_zero (real_mult (z03_eterm n Hn sg) (z01_lam n))
             (real_mult (z01_lam n) (z03_eterm n Hn sg))
             (real_eq_lt_lt real_zero
                (real_mult (z03_eterm n Hn sg) real_zero)
                (real_mult (z03_eterm n Hn sg) (z01_lam n))
                (real_eq_sym _ _ (real_mult_zero (z03_eterm n Hn sg)))
                (real_lt_mult_compat real_zero (z01_lam n)
                   (z03_eterm n Hn sg)
                   (cauchy_real_exp_pos
                      (real_mult (real_opp sg) (z03_lnreal n Hn))) Hlt))
             (real_mult_comm (z03_eterm n Hn sg) (z01_lam n))).
  - apply (RealSetoid.real_eq_le real_zero
             (real_mult (z01_lam n) (z03_eterm n Hn sg))).
    apply real_eq_sym.
    apply (real_eq_trans (real_mult (z01_lam n) (z03_eterm n Hn sg))
             (real_mult real_zero (z03_eterm n Hn sg)) real_zero).
    + exact (RealSetoid.real_eq_mult_compat (z01_lam n) (z03_eterm n Hn sg)
               real_zero (z03_eterm n Hn sg) (real_eq_sym real_zero (z01_lam n) Heq)
               (real_eq_refl _)).
    + exact (real_eq_trans (real_mult real_zero (z03_eterm n Hn sg))
               (real_mult (z03_eterm n Hn sg) real_zero) real_zero
               (real_mult_comm real_zero (z03_eterm n Hn sg))
               (real_mult_zero (z03_eterm n Hn sg))).
Qed.

(* The square-form sum is asymptotically nonnegative. *)
Theorem z03_sqsum_ge0 : forall (N : nat) (sg t : Real),
  real_ge_relax (z03_sqsum N sg t) real_zero.
Proof.
  intro N. induction N as [| N IH]; intros sg t.
  - cbn [z03_sqsum].
    apply (real_ge_relax_of_pointwise real_zero real_zero 0).
    intros n Hn. apply Qle_refl.
  - cbn [z03_sqsum]. apply z03_relax0_plus.
    + apply IH.
    + apply z03_wy_relax.
      * apply z03_ew_pos.
      * intro k.
        exact (GaC3_Z02_sq_pointwise_nonneg
                 (real_mult (real_opp t) (z03_lnreal (Datatypes.S N) (NatLe_one_S N))) k).
Qed.

(* Main face 1: the combined real part is asymptotically nonnegative. *)
Theorem z03_comb_nonneg : forall (N : nat) (sg t : Real),
  real_ge_relax (cRe (z03_comb N sg t)) real_zero.
Proof.
  intros N sg t.
  apply (z03_eq_relax_sym _ _ (real_eq_sym _ _ (z03_comb_sqsum_eq N sg t))).
  exact (z03_sqsum_ge0 N sg t).
Qed.

(* ===================================================================== *)
(* Part 2. The racing contradiction in explicit-radius slot form.         *)
(* ===================================================================== *)

Section Z03_Race.

(* The ordinate and the racing offset: the point family sigma + i*t     *)
(* with sigma = 1 + d and d > 0 rational. *)
Variable t : Real.
Variable d : Q.
Hypothesis Hd : QltT 0 d.

(* The balancing truncation and the two upper-bound slots (the          *)
(* sigma-term and the doubled-ordinate term). *)
Variable Nrace : nat.
Variables B3 B2 : Real.

(* The three racing points. *)
Definition z03_sg : Real := real_plus real_one (real_const d).
Definition z03_p0 : Cx := (z03_sg, real_zero).
Definition z03_p1 : Cx := (z03_sg, t).
Definition z03_p2 : Cx := (z03_sg, real_plus t t).

(* The four-term main-part slot: the real part of the von Mangoldt      *)
(* partial sum at sigma + i*t stays below the explicit m >= 1 main      *)
(* part -1/(2d) at the balancing truncation (the registered open        *)
(* supply face; the zero factorization route discharges it). *)
Hypothesis Hmain4 :
  real_le (cRe (z01_manpart z03npos Nrace z03_p1))
          (real_opp (real_const (Qinv (2 * d)))).

(* The sigma-term and doubled-ordinate upper-bound slots. *)
Hypothesis Hsig3 :
  real_le (cRe (z01_manpart z03npos Nrace z03_p0)) B3.
Hypothesis Htwo :
  real_le (cRe (z01_manpart z03npos Nrace z03_p2)) B2.

(* The racing margin constant m0 = 1/(2d), positive by Hd. *)
Definition z03_m0 : Real := real_const (Qinv (2 * d)).

Lemma z03_m0_pos : real_lt real_zero z03_m0.
Proof.
  apply QltT_to_Qlt in Hd.
  assert (H2 : Qlt 0 2) by reflexivity.
  assert (H2d : Qlt 0 (2 * d)) by exact (Qmult_lt_0_compat 2 d H2 Hd).
  exact (real_const_pos (Qinv (2 * d))
           (Qlt_to_QltT _ _ (Qinv_lt_0_compat (2 * d) H2d))).
Qed.

(* The racing contradiction: under the explicit window arithmetic       *)
(* 3*B3 + B2 < 4*m0 the nonnegativity face of Part 1 fails. *)
Theorem z03_racing_contra :
  real_lt (real_plus (real_mult (real_const 3) B3) B2)
          (real_mult (real_const 4) z03_m0) ->
  False.
Proof.
  intro Hwin.
  assert (Hnneg : real_ge_relax (cRe (z03_comb Nrace z03_sg t)) real_zero)
    by exact (z03_comb_nonneg Nrace z03_sg t).
  (* the split of the combined real part *)
  assert (Hsplit : real_eq (cRe (z03_comb Nrace z03_sg t))
    (real_plus (real_mult (real_const 3) (cRe (z01_manpart z03npos Nrace z03_p0)))
               (real_plus (real_mult (real_const 4)
                            (cRe (z01_manpart z03npos Nrace z03_p1)))
                          (cRe (z01_manpart z03npos Nrace z03_p2))))).
  { apply real_eq_of_zero_diff. intro k.
    cbn [z03_comb c_plus c_scale cRe cIm fst snd].
    unfold z03_p0, z03_p1, z03_p2. z03_pt. }
  (* the upper-bound chain *)
  assert (Hupper : real_le
    (real_plus (real_mult (real_const 3) (cRe (z01_manpart z03npos Nrace z03_p0)))
               (real_plus (real_mult (real_const 4)
                            (cRe (z01_manpart z03npos Nrace z03_p1)))
                          (cRe (z01_manpart z03npos Nrace z03_p2))))
    (real_plus (real_mult (real_const 3) B3)
               (real_plus (real_mult (real_const 4) (real_opp z03_m0)) B2))).
  { apply real_le_plus_compat.
    - apply z03_le_mult_l.
      + apply real_const_pos. compute. reflexivity.
      + exact Hsig3.
    - apply real_le_plus_compat.
      + apply z03_le_mult_l.
        * apply real_const_pos. compute. reflexivity.
        * exact Hmain4.
      + exact Htwo. }
  (* the association to the window shape *)
  assert (Hassoc : real_eq
    (real_plus (real_mult (real_const 3) B3)
               (real_plus (real_mult (real_const 4) (real_opp z03_m0)) B2))
    (real_plus (real_plus (real_mult (real_const 3) B3) B2)
               (real_mult (real_const 4) (real_opp z03_m0)))).
  { apply real_eq_of_zero_diff. intro k. z03_pt. }
  assert (Hle : real_le (cRe (z03_comb Nrace z03_sg t))
    (real_plus (real_plus (real_mult (real_const 3) B3) B2)
               (real_mult (real_const 4) (real_opp z03_m0)))).
  { apply (real_le_trans
             (cRe (z03_comb Nrace z03_sg t))
             (real_plus (real_mult (real_const 3)
                          (cRe (z01_manpart z03npos Nrace z03_p0)))
                        (real_plus (real_mult (real_const 4)
                             (cRe (z01_manpart z03npos Nrace z03_p1)))
                          (cRe (z01_manpart z03npos Nrace z03_p2))))).
    - apply (RealSetoid.real_eq_le _ _ Hsplit).
    - apply (real_le_trans _
               (real_plus (real_mult (real_const 3) B3)
                          (real_plus (real_mult (real_const 4) (real_opp z03_m0)) B2)) _).
      + exact Hupper.
      + apply (RealSetoid.real_eq_le _ _ Hassoc). }
  (* the shifted window *)
  assert (Hlt0 : real_lt (real_plus (real_plus (real_mult (real_const 3) B3) B2)
                                  (real_mult (real_const 4) (real_opp z03_m0)))
                         real_zero).
  { apply (z03_lt_eq_r (real_plus (real_plus (real_mult (real_const 3) B3) B2)
                          (real_mult (real_const 4) (real_opp z03_m0)))
              (real_plus (real_mult (real_const 4) z03_m0)
                         (real_mult (real_const 4) (real_opp z03_m0))) real_zero).
    - apply (z03_lt_add_r (real_plus (real_mult (real_const 3) B3) B2)
               (real_mult (real_const 4) z03_m0)
               (real_mult (real_const 4) (real_opp z03_m0)) Hwin).
    - apply (real_eq_trans
               (real_plus (real_mult (real_const 4) z03_m0)
                          (real_mult (real_const 4) (real_opp z03_m0)))
               (real_plus (real_mult (real_const 4) z03_m0)
                          (real_opp (real_mult (real_const 4) z03_m0)))).
      + apply real_eq_of_zero_diff. intro k. z03_pt.
      + apply real_plus_opp. }
  (* the joint incompatibility *)
  apply (z03_relax_lt_false (cRe (z03_comb Nrace z03_sg t)) Hnneg).
  apply (real_le_lt_trans _ _ _ Hle Hlt0).
Qed.

End Z03_Race.
