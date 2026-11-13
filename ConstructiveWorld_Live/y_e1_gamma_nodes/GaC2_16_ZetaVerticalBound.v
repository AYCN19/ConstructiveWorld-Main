(** * GaC2_16_ZetaVerticalBound: the zeta vertical-line bound faces.

    Mission.  Card C2.16, the explicit segmented vertical-line bound
      band: the three draft roster items [zeta_vert_high] /
      [zeta_vert_mid] / [zeta_vert_near1], with the six
      statement-shape materializations (i)-(vi) registered in the
      Notes block.

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia];
      [S01_BaseRing] (selective [NatLe]), [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [CxRealPairCore],
      [CxRealPairExpLog], [GaC2_01_DirichletPartialSum],
      [GaC2_02_AbsConvTailBound_a/_b/_c], [GaC2_02_AbsConvTailBound],
      [GaC2_05_EulerLimitAsm].

    References.  cards_C2.md C2.16; drafts_C2.md C2.16 (draft-2
      statement face, draft-4 acceptance); the F9 sSupNormIm and
      F6/F8 statement shapes (alignment only).

    Constructivity.  Every named construction is carried by [Set];
      order predicates are the Set-sorted [real_lt] / [real_le] /
      [QltT]; the Section slots (sig0 / Hs0 / Hnpos / Htri) discharge
      at End as explicit premise arguments so every audited lemma
      stays Closed under the global context; zero assumed constants,
      zero abandoned proofs, zero classical principles.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build shadow> "" GaC2_16_ZetaVerticalBound.v] from the
      flat build shadow, wrapped by [cpu_guard v3]. *)

Require S01_BaseRing.
(** Notes.  Statement-shape materializations, routes and consumables.

    (i) The zeta limit carrier is absent from the tree (the C2.05
    honest header keeps the lim face open supply), so the bound
    faces land on [c_zeta_part], uniform in N.
    (ii) [Hnpos] gains the [NatLe 1] premise (the C2.01/C2.06 rework
    ruling: the draft unconditional form is uninhabited at n = 0).
    (iii) The strict face lands in the rational-margin carrier (the
    GaC1_14 / GaC2_02(b) house form; the margin-free weak face
    follows by [real_lt_le_iff], so the draft [real_le] shape is
    dominated).
    (iv) The complex modulus face is conditional on the n-fold
    triangle slot [Htri] (the L-C2.16-A slot, the GaC2_02 L-C2.02-C
    register: the n-fold triangle is not L0 stock; the slot
    discharges at End as an explicit premise argument).
    (v) The draft Q2R embedding face lands as [real_const] Q
    literals (no Q2R bridge in the tree) and the draft division
    carrier lands as the positive-inverse carrier (the C2.18
    alignment).
    (vi) The draft Require entry [GaC2_07_DirichletTestAbel] is
    absent from the live dependency surface (absent from the build
    shadow, the deposit segments, the nodes face and the L0 face),
    so the entry is dropped from the Require header and kept only as
    the registered route of the (b)/(c) carriers - zero silent
    substitution.

    Proof status: (a) [zeta_vert_high] is a proven Lemma.  F9
    alignment (alignment only): the explicit corridor replaces the
    sup carrier, the C2.11 bearing-difference register.

    (a) detail: [zeta_vert_high] states that the squared modulus of
    the Dirichlet partial sums is strictly below the squared
    explicit condensation corridor 1 + M^(1-sig0) * C(sig0) at M = 1
    plus a rational margin, uniform in N and in the imaginary
    coordinate (the premise rides on [cRe] only; the draft s_at-t
    projection lands as the explicit point argument).  The corridor
    consumes the GaC2_02 condensation engine ([tail_bound_uniform]
    at M = 1) over the GaC2_05 zeta column [r_zeta_seq]; the unit
    front term of the column is normalized by [zeta16_npow_one]
    (1^(-sig) = 1).
    (b)/(c) detail: the log-shaped corridors sq (C1 * log t) and
    sq (C2 * log t) over the window premise
    1 - c_win / log t <= sig < 1 stay well-formed statement carriers
    (the C2.18 convention); the proof routes (the harmonic-log face
    plus the Abel machine of the C2.07 stem) are registered on the
    carriers [zeta_vert_mid] / [zeta_vert_near1]; the bodies promote
    to Lemma form when those mother stems land.

    Registered open: the ZetaAsymp retrieval re-check stays
    registered per the drafts fail-honest list.  Zero
    functional-equation dependence on this face (the cards_C2.md
    C2.16 proposition band).

    Named consumables: from [GaC2_01_DirichletPartialSum]:
    [nat_real], [c_powq], [c_zeta_part], [c_tail],
    [c_zeta_part_tail_eq], [NatLe_one_S]; from the GaC2_02 stem:
    [r_tsum], [r_tail], [r_ln], [r_npow], [r_m1sig], [r_geom_const],
    the condensation engine, [tail_bound_uniform]; from [S03_QExp]:
    the [cauchy_real_exp] band, [real_inv_pos]; from
    [S07_RealSetoidExpLog]: [real_log], [real_log_lt_mono],
    [real_log_one], [real_log_wd] and the Setoid compat band; from
    [S02_CauchyComplete]: the Real order kit, [real_const], [QltT],
    the compat faces.  No vm_compute word in this proof-topology
    face (the numeric corridor band lives in the certificate stem). *)

(* Selective import: a full import would shadow the nat constructor S    *)
(* (the GaC2_01 precedent).                                              *)
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
Require Import GaC2_02_AbsConvTailBound.
Require Import GaC2_05_EulerLimitAsm.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

Local Open Scope Q_scope.

Section ZetaVerticalBound.

(* The draft roster slots, verbatim names; Hnpos carries the NatLe 1     *)
(* premise per materialization (ii).                                     *)
Variable sig0 : Real.
Hypothesis Hs0 : real_lt real_one sig0.
Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).

(* The L-C2.16-A consumption slot: the n-fold triangle at the Dirichlet  *)
(* partial sums in rational-margin form (the GaC2_02 L-C2.02-C register; *)
(* not L0 stock, discharged at End as an explicit premise argument).     *)
Hypothesis Htri :
  forall (N : nat) (s : Cx) (d : Q), QltT 0 d ->
    real_lt (c_norm_sq (c_zeta_part Hnpos N s))
            (real_plus (real_mult (r_tsum Hnpos (cRe s) 0 N)
                                  (r_tsum Hnpos (cRe s) 0 N))
                       (real_const d)).

(* ==== The sketch carrier block (the draft pseudo-names materialized) === *)

(* The square carrier (the draft [sq] name; the C2.18 alignment).        *)
Definition sq (x : Real) : Real := real_mult x x.

(* The real-argument scalar face (the draft [c_scale'] name; the born    *)
(* [c_scale] stays the complex face).                                    *)
Definition c_scale' (a x : Real) : Real := real_mult a x.

(* The premise-carrying log wrapper (the draft [log_t] name; the         *)
(* positivity premise rides the strict floor one < t).                   *)
Definition log_t (t : Real) (Ht1 : real_lt real_one t) : Real :=
  real_log t (real_lt_trans real_zero real_one t real_lt_zero_one Ht1).

(* ==== Witness band: the ln faces from pure L0 stock ==== *)

(* ln 1 = 0 on the embedded unit. *)
Lemma zeta16_ln_one :
  real_eq (r_ln Hnpos 1 (NatLe_one_S 0)) real_zero.
Proof.
  unfold r_ln.
  apply (real_eq_trans _ (real_log real_one real_lt_zero_one)).
  - apply real_log_wd. exact nat_real_one.
  - exact (real_log_one real_lt_zero_one).
Qed.

(* 1^(-sig) = 1: the unit front term of the column. *)
Lemma zeta16_npow_one : forall sig : Real,
  real_eq (r_npow Hnpos sig 1 (NatLe_one_S 0)) real_one.
Proof.
  intro sig. unfold r_npow.
  apply (real_eq_trans _ (cauchy_real_exp real_zero)).
  - apply cauchy_real_exp_wd.
    apply (real_eq_trans _ (real_mult (real_opp sig) real_zero)).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _
               (real_eq_refl _) (zeta16_ln_one)).
    + exact (real_mult_zero (real_opp sig)).
  - exact cauchy_real_exp_zero.
Qed.

(* ln 2 > 0: the GaC2_02 L-C2.02-B slot witness from L0 stock. *)
Lemma zeta16_ln2_pos :
  real_lt real_zero (r_ln Hnpos 2 (NatLe_one_S 1)).
Proof.
  assert (H22 : NatLe 2 2) by (apply NatLe_lift; apply Nat.le_refl).
  assert (H12 : real_lt (nat_real 1) (nat_real 2))
    by exact (nat_real_lt 1 2 H22).
  assert (H1 : real_lt real_zero (nat_real 1))
    by exact (Hnpos 1 (NatLe_one_S 0)).
  assert (H2 : real_lt real_zero (nat_real 2))
    by exact (Hnpos 2 (NatLe_one_S 1)).
  assert (Hmono : real_lt (cw_log (nat_real 1) H1)
                 (cw_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1))))
    by exact (real_log_lt_mono (nat_real 1) (nat_real 2) H1
                (Hnpos 2 (NatLe_one_S 1)) H12).
  assert (Hln1z : real_eq (cw_log (nat_real 1) H1) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one)).
    - apply real_log_wd. exact nat_real_one.
    - exact (real_log_one real_lt_zero_one). }
  exact (real_eq_lt_lt real_zero (cw_log (nat_real 1) H1)
           (r_ln Hnpos 2 (NatLe_one_S 1)) (real_eq_sym _ _ Hln1z) Hmono).
Qed.

(* ==== The uniform column face (the (a) corridor carrier) ==== *)

(* The zeta column sits below the explicit condensation corridor         *)
(* 1 + M^(1-sig0) * C(sig0) at M = 1, uniformly in N and in the          *)
(* imaginary coordinate (the premise rides on cRe only).                 *)
Lemma zeta_col_uniform : forall (s : Cx) (Hsg : real_le sig0 (cRe s)) (N : nat),
  real_le (r_zeta_seq Hnpos (cRe s) N)
          (real_plus real_one
             (real_mult (r_m1sig Hnpos sig0 1 (NatLe_one_S 0))
                        (r_geom_const Hnpos sig0 Hs0 zeta16_ln2_pos))).
Proof.
  intros s Hsg N.
  assert (Hsg1 : real_lt real_one (cRe s))
    by exact (real_lt_le_trans real_one sig0 (cRe s) Hs0 Hsg).
  assert (Hzero_one : NatLe 0 1) by (apply NatLe_lift; apply Nat.le_0_l).
  set (B := real_mult (r_m1sig Hnpos sig0 1 (NatLe_one_S 0))
                      (r_geom_const Hnpos sig0 Hs0 zeta16_ln2_pos)).
  assert (HB0 : real_lt real_zero B).
  { apply real_mult_positive.
    - exact (r_m1sig_pos Hnpos sig0 1 (NatLe_one_S 0)).
    - exact (r_geom_const_pos Hnpos sig0 Hs0 zeta16_ln2_pos). }
  assert (HB0le : real_le real_zero B) by exact (real_lt_le_iff _ _ (inl HB0)).
  destruct N as [|m].
  - (* the empty column: zero, and zero <= 1 + B *)
    assert (Hzero : real_eq (r_zeta_seq Hnpos (cRe s) 0) real_zero)
      by (cbn [r_zeta_seq r_tsum]; apply real_eq_refl).
    assert (HZB : real_le real_zero (real_plus real_one B))
      by exact (real_lt_le_iff _ _ (inl
                (real_lt_le_trans real_zero real_one (real_plus real_one B)
                   real_lt_zero_one (r_le_plus_nonneg real_one B HB0le)))).
    exact (RealSetoid.real_le_compat real_zero (r_zeta_seq Hnpos (cRe s) 0)
             (real_plus real_one B) (real_plus real_one B)
             (real_eq_sym _ _ Hzero) (real_eq_refl _) HZB).
  - (* the unit front term is exactly one, the block (1, S m] rides the   *)
    (* condensation engine at M = 1.                                     *)
    assert (Ht01 : real_eq (r_tail Hnpos (cRe s) 0 1) real_one).
    { apply (real_eq_trans _ (r_npow Hnpos (cRe s) 1 (NatLe_one_S 0))).
      - apply (real_eq_trans _ (r_tsum Hnpos (cRe s) 0 1)).
        + exact (real_eq_sym _ _ (r_tsum_r_tail Hnpos (cRe s) 0 1)).
        + cbn [r_tsum]. apply r_plus_zero_l_gen.
      - exact (zeta16_npow_one (cRe s)). }
    assert (Htail1 : real_lt (r_tail Hnpos (cRe s) 1 (S m)) B).
    { exact (tail_bound_uniform Hnpos (cRe s) Hsg1
               (fun m0 n0 Hm0 Hn0 Hmn0 =>
                   real_log_lt_mono (nat_real m0) (nat_real n0) Hm0 Hn0 Hmn0)
               zeta16_ln2_pos sig0 Hs0 Hsg 1 (S m)
               (NatLe_one_S 0) (NatLe_one_S m)). }
    assert (Ht1le : real_le (r_tail Hnpos (cRe s) 1 (S m)) B)
      by exact (real_lt_le_iff _ _ (inl Htail1)).
    assert (Hchain : real_eq (r_tail Hnpos (cRe s) 0 (S m))
                       (real_plus (r_tail Hnpos (cRe s) 0 1)
                                  (r_tail Hnpos (cRe s) 1 (S m))))
      by exact (r_tail_chain Hnpos (cRe s) 0 1 (S m) Hzero_one (NatLe_one_S m)).
    assert (Hle2 : real_le (real_plus (r_tail Hnpos (cRe s) 0 1)
                                 (r_tail Hnpos (cRe s) 1 (S m)))
                           (real_plus real_one B)).
    { apply real_le_plus_compat.
      - apply r_le_of_eq. exact Ht01.
      - exact Ht1le. }
    assert (Hsum : real_eq (r_zeta_seq Hnpos (cRe s) (S m))
                     (real_plus (r_tail Hnpos (cRe s) 0 1)
                                (r_tail Hnpos (cRe s) 1 (S m)))).
    { apply (real_eq_trans _ (r_tail Hnpos (cRe s) 0 (S m))).
      - exact (r_tsum_r_tail Hnpos (cRe s) 0 (S m)).
      - exact Hchain. }
    exact (RealSetoid.real_le_compat
             (real_plus (r_tail Hnpos (cRe s) 0 1)
                        (r_tail Hnpos (cRe s) 1 (S m)))
             (r_zeta_seq Hnpos (cRe s) (S m))
             (real_plus real_one B) (real_plus real_one B)
             (real_eq_sym _ _ Hsum) (real_eq_refl _) Hle2).
Qed.

(* ==== (a) The draft roster item zeta_vert_high ==== *)

(* The squared modulus of the Dirichlet partial sums is strictly below   *)
(* the squared corridor plus the rational margin, on the whole vertical  *)
(* line sig >= sig0 > 1, uniform in N and in the imaginary coordinate.   *)
Lemma zeta_vert_high : forall (N : nat) (s : Cx) (Hsg : real_le sig0 (cRe s))
                       (d : Q) (Hd : QltT 0 d),
  real_lt (c_norm_sq (c_zeta_part Hnpos N s))
          (real_plus (sq (real_plus real_one
             (real_mult (r_m1sig Hnpos sig0 1 (NatLe_one_S 0))
                        (r_geom_const Hnpos sig0 Hs0 zeta16_ln2_pos))))
                     (real_const d)).
Proof.
  intros N s Hsg d Hd.
  set (C := real_plus real_one
             (real_mult (r_m1sig Hnpos sig0 1 (NatLe_one_S 0))
                        (r_geom_const Hnpos sig0 Hs0 zeta16_ln2_pos))).
  set (T := r_tsum Hnpos (cRe s) 0 N).
  apply (real_lt_le_trans _ (real_plus (real_mult T T) (real_const d))).
  - exact (Htri N s d Hd).
  - apply real_le_plus_compat.
    + assert (HT : real_le T C) by exact (zeta_col_uniform s Hsg N).
      assert (HT0 : real_le real_zero T) by exact (r_tsum_ge0 Hnpos (cRe s) 0 N).
      assert (HC0 : real_lt real_zero C).
      { apply (real_lt_le_trans real_zero real_one C); [exact real_lt_zero_one |].
        apply r_le_plus_nonneg. apply (real_lt_le_iff _ _). left.
        apply real_mult_positive.
        - exact (r_m1sig_pos Hnpos sig0 1 (NatLe_one_S 0)).
        - exact (r_geom_const_pos Hnpos sig0 Hs0 zeta16_ln2_pos). }
      assert (HC0le : real_le real_zero C)
        by exact (real_lt_le_iff _ _ (inl HC0)).
      assert (Hstep1 : real_le (real_mult T T) (real_mult C T))
        by exact (real_le_mult_compat_weak T C T HT0 HT).
      assert (Hstep2 : real_le (real_mult T C) (real_mult C C))
        by exact (real_le_mult_compat_weak T C C HC0le HT).
      exact (real_le_trans _ _ _ Hstep1
               (RealSetoid.real_le_compat (real_mult T C) (real_mult C T)
                  (real_mult C C) (real_mult C C)
                  (real_mult_comm T C) (real_eq_refl _) Hstep2)).
    + apply real_le_refl.
Qed.

(* ==== (b) The draft roster item zeta_vert_mid (statement carrier) ==== *)

(* The log corridor face over the segment  1 <= sig <= 2, t >= 2:  the   *)
(* squared modulus of the partial sums below sq (C1 * log t), uniform    *)
(* in N.  Statement carrier per the C2.18 convention: the proof route    *)
(* (the harmonic-log face on the main term plus the C2.07 Abel machine   *)
(* on the tail, the card route) is registered; the body promotes when    *)
(* the mother stems land.  C1 enters as the explicit constant argument   *)
(* (the constants-as-arguments ruling).                                  *)
Definition zeta_vert_mid (t : Real) (Ht2 : real_le (real_const (2#1)) t)
           (Ht1 : real_lt real_one t)
           (Hlogpos : real_lt real_zero (log_t t Ht1))
           (C1 : Real) (s : Cx) (Hs1 : real_le real_one (cRe s))
           (Hs2 : real_le (cRe s) (real_const (2#1))) : Set :=
  forall N : nat,
    real_le (c_norm_sq (c_zeta_part Hnpos N s))
            (sq (c_scale' C1 (log_t t Ht1))).

(* ==== (c) The draft roster item zeta_vert_near1 (statement carrier) === *)

(* The dVp window face  1 - c_win / log t <= sig < 1:  the squared       *)
(* modulus below sq (C2 * log t), uniform in N.  The draft division      *)
(* carrier lands as the positive-inverse carrier; C2 / c_win enter as    *)
(* the explicit constant arguments.  Same carrier register as (b).       *)
Definition zeta_vert_near1 (t : Real) (Ht1 : real_lt real_one t)
           (Hlogpos : real_lt real_zero (log_t t Ht1))
           (c_win C2 : Real) (s : Cx)
           (Hwin : real_le (real_plus real_one
                     (real_opp (c_scale' c_win
                        (real_inv_pos (log_t t Ht1) Hlogpos))))
                    (cRe s))
           (Hslt : real_lt (cRe s) real_one) : Set :=
  forall N : nat,
    real_le (c_norm_sq (c_zeta_part Hnpos N s))
            (sq (c_scale' C2 (log_t t Ht1))).

End ZetaVerticalBound.

(* ==== Named-item census ==== *)

(* 3 Definitions (sq / c_scale' / log_t) + 5 Lemmas (zeta16_ln_one,      *)
(* zeta16_npow_one, zeta16_ln2_pos, zeta_col_uniform, zeta_vert_high)    *)
(* + 2 statement carriers (zeta_vert_mid / zeta_vert_near1); 1 Section   *)
(* (ZetaVerticalBound: slots sig0 / Hs0 / Hnpos / Htri, discharged at    *)
(* End); zero vm_compute words, zero assumed constants and zero          *)
(* abandoned proofs.  The (b)/(c) routes stay registered on the          *)
(* carriers; the L-C2.16-A triangle slot and the absent C2.07 stem stay  *)
(* registered in the Notes block. *)
