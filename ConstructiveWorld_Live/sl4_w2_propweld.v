(* ========================================================================= *)
(* ConstructiveWorld-Main outbound package - SL4 row D-SL4-5 wrap-up weld:  *)
(* the transition face between the proven proportional half and the         *)
(* denominator anchor family (row D-SL4-4).                                 *)
(* Mission      : sl4_d5_proportional landed the rank-one pair lemma under  *)
(*                the disclosed base-row-nonzero premise.  This file adds  *)
(*                the weld: across a zero-determinant step the reduced      *)
(*                denominator d_n = |B n| / gcd(|A n|, |B n|) is INVARIANT  *)
(*                while the anchor threshold 2^((5n-1)/2) grows >= 4x per   *)
(*                step.  Decidable premises only; the forall-n nonzero      *)
(*                account (rows D-SL4-3/4/7) stays outside, unclaimed.      *)
(* Statements   : planb4_sl4_w2_div_exact; ..._gcd_pos_of_row_nz;           *)
(*                ..._row_denom_stable (bare-Z invariance);                 *)
(*                ..._denom_stable_on_zero (carrier form);                  *)
(*                ..._threshold_step (the >= 4x jump); ..._propweld (the    *)
(*                landed proportionality witness plus the invariance);      *)
(*                ..._zero_step_threshold_carry/clears_quadruple (the       *)
(*                anchor-form faces, composing with the anchors directly).  *)
(* Dependencies : planb4_sl4_skeleton; planb4_g1_ab_def; sl4_d5_proportional*)
(*                (sub_eq and rank1_pair consumed by name); the anchor-     *)
(*                family files are not required.  Source routing: kept in   *)
(*                the delivery receipt per the comment law, nothing         *)
(*                written here.                                             *)
(* References   : survey volume SL4 sections 2/5/9; skeleton Sections 1/4/5.*)
(* Constructivity: decidable Z case analysis, rewrite chains, ring/lia      *)
(*                only at leaf steps, never a finisher; all items Defined.  *)
(* Build        : coqc -native-compiler no -q -Q <sandbox root> ""          *)
(*                sl4_w2_propweld.v (Rocq 9.3.0, scripted form).            *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import Lia.
Require Import planb4_sl4_skeleton.
Require Import planb4_g1_ab_def.
Require Import sl4_d5_proportional.

(* ================================================================== *)
(* Section 1. Bare-Z tools: exact quotients and gcd positivity.       *)
(* ================================================================== *)

(* An exact product pins the quotient: the zero-remainder face of     *)
(* the division spec.                                                 *)
Lemma planb4_sl4_w2_div_exact :
  forall g x q : Z, (0 < g)%Z -> x = (g * q)%Z -> (x / g)%Z = q.
Proof.
  intros g x q Hg Hx.
  assert (Hlt : ((0 <= 0 < g)%Z \/ (g < 0 <= 0)%Z))
    by (left; split; lia).
  assert (Heq : x = (g * q + 0)%Z) by (rewrite Z.add_0_r; exact Hx).
  symmetry. exact (Z.div_unique x g q 0 Hlt Heq).
Defined.

(* A gcd over absolute values is positive as soon as the row is not   *)
(* identically zero: a zero gcd divides only zero.                    *)
Lemma planb4_sl4_w2_gcd_pos_of_row_nz :
  forall x y : Z,
    (x <> 0%Z \/ y <> 0%Z)%Z ->
    (0 < Z.gcd (Z.abs x) (Z.abs y))%Z.
Proof.
  intros x y Hnz.
  assert (Hge : (0 <= Z.gcd (Z.abs x) (Z.abs y))%Z) by apply Z.gcd_nonneg.
  destruct (Z.eq_dec (Z.gcd (Z.abs x) (Z.abs y)) 0%Z) as [Hg0|Hgne].
  - exfalso. destruct Hnz as [Hx|Hy].
    + destruct (Z.gcd_divide_l (Z.abs x) (Z.abs y)) as [p Hp].
      rewrite Hg0, Z.mul_0_r in Hp.
      destruct x as [|a|a].
      * exact (Hx eq_refl).
      * cbn in Hp. discriminate Hp.
      * cbn in Hp. discriminate Hp.
    + destruct (Z.gcd_divide_r (Z.abs x) (Z.abs y)) as [p Hp].
      rewrite Hg0, Z.mul_0_r in Hp.
      destruct y as [|b|b].
      * exact (Hy eq_refl).
      * cbn in Hp. discriminate Hp.
      * cbn in Hp. discriminate Hp.
  - lia.
Defined.

(* ================================================================== *)
(* Section 2. The bare-Z invariance: a rank-one step keeps the        *)
(*            reduced denominator |b| / gcd(|a|, |b|) unchanged.      *)
(* ================================================================== *)

Lemma planb4_sl4_w2_row_denom_stable :
  forall a b c d : Z,
    (a * d = c * b)%Z ->
    (a <> 0%Z \/ b <> 0%Z)%Z ->
    (c <> 0%Z \/ d <> 0%Z)%Z ->
    (Z.abs d / Z.gcd (Z.abs c) (Z.abs d))%Z =
    (Z.abs b / Z.gcd (Z.abs a) (Z.abs b))%Z.
Proof.
  intros a b c d Hdet Hnz1 Hnz2.
  (* the absolute-value product identity A*D = C*B *)
  assert (HADCB : (Z.abs a * Z.abs d = Z.abs c * Z.abs b)%Z).
  { rewrite <- (Z.abs_mul a d), <- (Z.abs_mul c b).
    rewrite Hdet. reflexivity. }
  assert (Hg1 : (0 < Z.gcd (Z.abs a) (Z.abs b))%Z)
    by (apply planb4_sl4_w2_gcd_pos_of_row_nz; exact Hnz1).
  assert (Hg2 : (0 < Z.gcd (Z.abs c) (Z.abs d))%Z)
    by (apply planb4_sl4_w2_gcd_pos_of_row_nz; exact Hnz2).
  destruct (Z.eq_dec (Z.abs b) 0%Z) as [HB0|HBne].
  - (* degenerate branch: b = 0 forces d = 0 and both sides are zero.   *)
    assert (Hb0 : b = 0%Z)
      by (destruct b as [|p|p]; [reflexivity
                                | cbn in HB0; discriminate HB0
                                | cbn in HB0; discriminate HB0]).
    assert (HAne : Z.abs a <> 0%Z).
    { intro Habs0. destruct Hnz1 as [Hx|Hy].
      - apply Hx. destruct a as [|p|p].
        + reflexivity.
        + cbn in Habs0. discriminate Habs0.
        + cbn in Habs0. discriminate Habs0.
      - exact (Hy Hb0). }
    assert (HD0 : Z.abs d = 0%Z).
    { rewrite Hb0 in HADCB. cbn [Z.abs] in HADCB.
      rewrite Z.mul_0_r in HADCB.
      apply Z.mul_eq_0 in HADCB.
      destruct HADCB as [HA0|HD0x]; [|exact HD0x].
      exfalso. apply HAne. exact HA0. }
    assert (Hd0 : d = 0%Z)
      by (destruct d as [|p|p]; [reflexivity
                                | cbn in HD0; discriminate HD0
                                | cbn in HD0; discriminate HD0]).
    assert (HCne : Z.abs c <> 0%Z).
    { intro Habs0. destruct Hnz2 as [Hw|Hw].
      - apply Hw. destruct c as [|p|p].
        + reflexivity.
        + cbn in Habs0. discriminate Habs0.
        + cbn in Habs0. discriminate Habs0.
      - exact (Hw Hd0). }
    rewrite Hb0, Hd0.
    cbn [Z.abs].
    rewrite !Z.gcd_0_r.
    assert (Hcc : Z.abs (Z.abs c) = Z.abs c)
      by (rewrite Z.abs_eq by apply Z.abs_nonneg; reflexivity).
    assert (Haa : Z.abs (Z.abs a) = Z.abs a)
      by (rewrite Z.abs_eq by apply Z.abs_nonneg; reflexivity).
    rewrite Hcc, Haa.
    rewrite !Z.div_0_l by assumption.
    reflexivity.
  - (* main branch: B > 0, D > 0; gcd scaling gives g1*D = g2*B,        *)
    (* the two exact quotients then agree.                              *)
    assert (HB : (0 < Z.abs b)%Z)
      by (assert (Hge := Z.abs_nonneg b); lia).
    assert (HD : (0 < Z.abs d)%Z).
    { destruct (Z.eq_dec (Z.abs d) 0%Z) as [Hd0abs|Hdne].
      - exfalso.
        assert (Hd0x : d = 0%Z)
          by (destruct d as [|p|p]; [reflexivity
                                    | cbn in Hd0abs; discriminate Hd0abs
                                    | cbn in Hd0abs; discriminate Hd0abs]).
        rewrite Hd0x in HADCB. cbn [Z.abs] in HADCB.
        rewrite Z.mul_0_r in HADCB.
        symmetry in HADCB. apply Z.mul_eq_0 in HADCB.
        destruct HADCB as [HC0|HB0x].
        + destruct Hnz2 as [Hw|Hw].
          * apply Hw.
            destruct c as [|p|p]; cbn in HC0;
              [reflexivity | discriminate HC0 | discriminate HC0].
          * exact (Hw Hd0x).
        + lia.
      - assert (Hge := Z.abs_nonneg d). lia. }
    (* gcd scaling: gcd(A*D, B*D) = g1*D and gcd(C*B, D*B) = g2*B,       *)
    (* and A*D = C*B identifies the two left sides.                      *)
    assert (Hs1 : (Z.gcd (Z.abs a * Z.abs d) (Z.abs b * Z.abs d)
                   = Z.gcd (Z.abs a) (Z.abs b) * Z.abs d)%Z)
      by (apply Z.gcd_mul_mono_r_nonneg; lia).
    assert (Hs2 : (Z.gcd (Z.abs c * Z.abs b) (Z.abs d * Z.abs b)
                   = Z.gcd (Z.abs c) (Z.abs d) * Z.abs b)%Z)
      by (apply Z.gcd_mul_mono_r_nonneg; lia).
    assert (Hs3 : (Z.gcd (Z.abs a * Z.abs d) (Z.abs b * Z.abs d)
                   = Z.gcd (Z.abs c * Z.abs b) (Z.abs d * Z.abs b))%Z).
    { rewrite HADCB, (Z.mul_comm (Z.abs b) (Z.abs d)). reflexivity. }
    assert (Hscale : (Z.gcd (Z.abs a) (Z.abs b) * Z.abs d
                      = Z.gcd (Z.abs c) (Z.abs d) * Z.abs b)%Z).
    { rewrite <- Hs1, <- Hs2. exact Hs3. }
    (* exact quotients out of the divisibility facts *)
    destruct (Z.gcd_divide_r (Z.abs a) (Z.abs b)) as [q1 Hq1].
    destruct (Z.gcd_divide_r (Z.abs c) (Z.abs d)) as [q2 Hq2].
    assert (Hq1' : Z.abs b = (Z.gcd (Z.abs a) (Z.abs b) * q1)%Z)
      by (rewrite (Z.mul_comm (Z.gcd (Z.abs a) (Z.abs b)) q1); exact Hq1).
    assert (Hq2' : Z.abs d = (Z.gcd (Z.abs c) (Z.abs d) * q2)%Z)
      by (rewrite (Z.mul_comm (Z.gcd (Z.abs c) (Z.abs d)) q2); exact Hq2).
    assert (Hq1e : (Z.abs b / Z.gcd (Z.abs a) (Z.abs b))%Z = q1)
      by (apply planb4_sl4_w2_div_exact; [exact Hg1 | exact Hq1']).
    assert (Hq2e : (Z.abs d / Z.gcd (Z.abs c) (Z.abs d))%Z = q2)
      by (apply planb4_sl4_w2_div_exact; [exact Hg2 | exact Hq2']).
    rewrite Hq1e, Hq2e.
    (* substitute the exact quotients back into the scaled gcd identity,  *)
    (* replacing only the multiplicand positions (the rewrite patterns    *)
    (* g1*q1 / g2*q2 do not occur inside the gcd arguments).              *)
    assert (Hsub : (Z.gcd (Z.abs a) (Z.abs b)
                    * (Z.gcd (Z.abs c) (Z.abs d) * q2)
                    = Z.gcd (Z.abs c) (Z.abs d)
                    * (Z.gcd (Z.abs a) (Z.abs b) * q1))%Z).
    { rewrite <- Hq2'. rewrite <- Hq1'. exact Hscale. }
    rewrite !Z.mul_assoc in Hsub.
    rewrite (Z.mul_comm (Z.gcd (Z.abs c) (Z.abs d))
                        (Z.gcd (Z.abs a) (Z.abs b))) in Hsub.
    assert (Hgg : (Z.gcd (Z.abs a) (Z.abs b) * Z.gcd (Z.abs c) (Z.abs d)
                   <> 0%Z)%Z).
    { intro Hc. apply Z.mul_eq_0 in Hc.
      destruct Hc as [Hc|Hc]; [lia | lia]. }
    exact (proj1 (Z.mul_cancel_l q2 q1
            ((Z.gcd (Z.abs a) (Z.abs b) * Z.gcd (Z.abs c) (Z.abs d))%Z) Hgg)
            Hsub).
Defined.

(* ================================================================== *)
(* Section 3. The carrier-level weld: a zero determinant keeps the    *)
(*            reduced denominator invariant across the step.          *)
(* ================================================================== *)

Theorem planb4_sl4_w2_denom_stable_on_zero :
  forall n : nat,
    planb4_sl4_delta n = 0%Z ->
    (planb4_g1_A n <> 0%Z \/ planb4_g1_B n <> 0%Z)%Z ->
    (planb4_g1_A (S n) <> 0%Z \/ planb4_g1_B (S n) <> 0%Z)%Z ->
    planb4_sl4_denom_reduced (S n) = planb4_sl4_denom_reduced n.
Proof.
  intros n H0 Hnz1 Hnz2.
  unfold planb4_sl4_denom_reduced.
  apply planb4_sl4_w2_row_denom_stable.
  - unfold planb4_sl4_delta in H0.
    apply planb4_sl4_d5_sub_eq. exact H0.
  - exact Hnz1.
  - exact Hnz2.
Defined.

(* ================================================================== *)
(* Section 4. The anchor criterion threshold grows by at least a      *)
(*            factor 4 per step (pure arithmetic, no premises).       *)
(* ================================================================== *)

Lemma planb4_sl4_w2_threshold_step :
  forall n : nat,
    (2 ^ ((Z.of_nat n * 5 - 1) / 2) * 4 <=
     2 ^ ((Z.of_nat (S n) * 5 - 1) / 2))%Z.
Proof.
  intros n.
  destruct n as [|m].
  - (* n = 0: both sides are ground values. *)
    vm_compute. discriminate.
  - (* n = S m >= 1: the floor-exponent arithmetic path. *)
    rewrite (Nat2Z.inj_succ (S m)).
    assert (Hge1 : (1 <= Z.of_nat (S m))%Z)
      by (rewrite Nat2Z.inj_succ; change ((1 <= Z.of_nat m + 1)%Z); lia).
    assert (Ha0 : (0 <= Z.of_nat (S m) * 5 - 1)%Z) by lia.
    assert (He0 : (0 <= (Z.of_nat (S m) * 5 - 1) / 2)%Z)
      by (apply Z.div_pos; lia).
    assert (Hsplit :
      ((Z.of_nat (S m) * 5 - 1) / 2 + 2
       = ((Z.of_nat (S m) * 5 - 1) + 2 * 2) / 2)%Z).
    { replace (((Z.of_nat (S m) * 5 - 1) + 2 * 2)%Z)
        with ((2 * 2 + ((Z.of_nat (S m) * 5 - 1) + 0))%Z) by lia.
      rewrite Z.add_0_r, Z.div_add_l by lia. lia. }
    assert (He : ((Z.of_nat (S m) * 5 - 1) / 2 + 2
                  <= (Z.succ (Z.of_nat (S m)) * 5 - 1) / 2)%Z).
    { rewrite Hsplit. apply Z.div_le_mono; lia. }
    assert (Hpow : (2 ^ ((Z.of_nat (S m) * 5 - 1) / 2) * 4
                    = 2 ^ ((Z.of_nat (S m) * 5 - 1) / 2 + 2))%Z).
    { replace 4%Z with (2 ^ 2)%Z by reflexivity.
      symmetry. apply Z.pow_add_r; [exact He0 | lia]. }
    rewrite Hpow.
    apply Z.pow_le_mono_r; [lia | exact He].
Defined.

(* ================================================================== *)
(* Section 5. The packaged weld: the landed proportionality face and  *)
(*            the denominator invariance in one consumption shape.    *)
(* ================================================================== *)

Theorem planb4_sl4_w2_propweld :
  forall n : nat,
    planb4_sl4_delta n = 0%Z ->
    (planb4_g1_A n <> 0%Z \/ planb4_g1_B n <> 0%Z)%Z ->
    (planb4_g1_A (S n) <> 0%Z \/ planb4_g1_B (S n) <> 0%Z)%Z ->
    (exists l : Q,
       Qeq (inject_Z (planb4_g1_A (S n)))
           (Qmult l (inject_Z (planb4_g1_A n))) /\
       Qeq (inject_Z (planb4_g1_B (S n)))
           (Qmult l (inject_Z (planb4_g1_B n)))) /\
    planb4_sl4_denom_reduced (S n) = planb4_sl4_denom_reduced n.
Proof.
  intros n H0 Hnz1 Hnz2.
  split.
  - unfold planb4_sl4_delta in H0.
    exact (planb4_sl4_d5_rank1_pair (planb4_g1_A n) (planb4_g1_B n)
             (planb4_g1_A (S n)) (planb4_g1_B (S n)) H0 Hnz1).
  - exact (planb4_sl4_w2_denom_stable_on_zero n H0 Hnz1 Hnz2).
Defined.

(* ================================================================== *)
(* Section 6. Anchor-form consumption faces: what the weld lets the   *)
(*            denominator anchor family conclude across a zero step.  *)
(* ================================================================== *)

(* A certified bound at n carries verbatim to the next step: under a  *)
(* zero determinant the denominator is frozen, so the certified       *)
(* threshold_n lower bound keeps holding at S n (the threshold itself *)
(* grows, which is the registered tension row D-SL4-7 consumes).      *)
Theorem planb4_sl4_w2_zero_step_threshold_carry :
  forall n : nat,
    planb4_sl4_delta n = 0%Z ->
    (planb4_g1_A n <> 0%Z \/ planb4_g1_B n <> 0%Z)%Z ->
    (planb4_g1_A (S n) <> 0%Z \/ planb4_g1_B (S n) <> 0%Z)%Z ->
    Z.leb (2 ^ ((Z.of_nat n * 5 - 1) / 2)%Z) (planb4_sl4_denom_reduced n) = true ->
    Z.leb (2 ^ ((Z.of_nat n * 5 - 1) / 2)%Z) (planb4_sl4_denom_reduced (S n)) = true.
Proof.
  intros n H0 Hnz1 Hnz2 Hanc.
  rewrite (planb4_sl4_w2_denom_stable_on_zero n H0 Hnz1 Hnz2).
  exact Hanc.
Defined.

(* If the next-step anchor form holds, a zero step forces the current *)
(* denominator to clear a quadrupled threshold: the frozen value must *)
(* clear the grown criterion.                                         *)
Theorem planb4_sl4_w2_zero_step_clears_quadruple :
  forall n : nat,
    planb4_sl4_delta n = 0%Z ->
    (planb4_g1_A n <> 0%Z \/ planb4_g1_B n <> 0%Z)%Z ->
    (planb4_g1_A (S n) <> 0%Z \/ planb4_g1_B (S n) <> 0%Z)%Z ->
    Z.leb (2 ^ ((Z.of_nat (S n) * 5 - 1) / 2)%Z)
          (planb4_sl4_denom_reduced (S n)) = true ->
    (2 ^ ((Z.of_nat n * 5 - 1) / 2) * 4 <= planb4_sl4_denom_reduced n)%Z.
Proof.
  intros n H0 Hnz1 Hnz2 Hanc.
  apply Z.le_trans with ((2 ^ ((Z.of_nat (S n) * 5 - 1) / 2))%Z).
  - apply planb4_sl4_w2_threshold_step.
  - apply Z.leb_le in Hanc.
    rewrite (planb4_sl4_w2_denom_stable_on_zero n H0 Hnz1 Hnz2) in Hanc.
    exact Hanc.
Defined.

(* The concrete composition instance at the landed anchor Example     *)
(* planb4_sl4_d4_denom_anchor_1 is a one-line application of the      *)
(* carry face (its type matches the carry premise verbatim) and is    *)
(* registered in the delivery receipt rather than compiled here, so   *)
(* that this file compiles on the minimal skeleton closure; the       *)
(* anchor family itself needs the calibration-window segments, still  *)
(* compiling at write time.                                           *)

(* ================================================================== *)
(* Section 7. Assumption audit (kernel verdicts, printed at build).   *)
(* ================================================================== *)

Print Assumptions planb4_sl4_w2_div_exact.
Print Assumptions planb4_sl4_w2_gcd_pos_of_row_nz.
Print Assumptions planb4_sl4_w2_row_denom_stable.
Print Assumptions planb4_sl4_w2_denom_stable_on_zero.
Print Assumptions planb4_sl4_w2_threshold_step.
Print Assumptions planb4_sl4_w2_propweld.
Print Assumptions planb4_sl4_w2_zero_step_threshold_carry.
Print Assumptions planb4_sl4_w2_zero_step_clears_quadruple.

(* ============ end of the D-SL4-5 wrap-up weld face ================ *)
