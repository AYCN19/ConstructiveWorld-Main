(* ConstructiveWorld-Main - the Q corridor certificate band of the Abel    *)
(* tail supply face.                                                       *)
(** * GaC2_07_AbelTailSupply_cert: the certificate face of the Abel supply.

    Mission.  The certificate band of [GaC2_07_AbelTailSupply]: Band 1 the
    premise-closing unfold faces of the supply theorem and the triangle face;
    Band 2 the decidable Q replicas - the machine replica of the counterexample
    behind the nonnegativity premise (a n = 2 - n, b n = alt_sign n, B = 1,
    M = 1, N = 3: both carried premises hold at the rational sample while the
    carried bound fails 1 <= 0), the positive unit-coefficient replica, and the
    sign-column samples; Band 3 the composite certificate bool list.  Honest
    scope: these literals certify the decidable Q skeleton and the unfold faces,
    not the Real-line order facts (Print Assumptions in the supply module).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List]; requires
    [S01_BaseRing] (selective [NatLe] import), [S02_CauchyComplete],
    [CxRealPairCore], [GaC2_01_DirichletPartialSum], [GaC2_02_AbsConvTailBound_a],
    [GaC2_06_AltMonoFace], the stem [GaC2_07_DirichletTestAbel], and the supply
    face [GaC2_07_AbelTailSupply].

    References.  drafts_C2.md C2.07 certificate row conventions; the precedents
    [GaC2_07_DirichletTestAbel_cert] and [GaC2_16_ZetaVerticalBound_cert];
    cards_C2.md C2.07.

    Constructivity.  Every named construction is carried by [Set]; the band
    statements are bool equations and Q identities at the Q level; the Q bands
    close with vm_compute, the unfold bands with definitional transparency.

    Build.  [coqc -native-compiler no -q -Q <build root> ""
    GaC2_07_AbelTailSupply_cert.v] (flat build directory). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Require S01_BaseRing.
Import S01_BaseRing (NatLe).
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_06_AltMonoFace.
Require Import GaC2_07_DirichletTestAbel.
Require Import GaC2_07_AbelTailSupply.

Local Open Scope Q_scope.

(* ==== Band 1: the premise-closing unfold faces ==== *)

(* The carried statement type unfolds to its premise-closing functor      *)
(* (mirroring the stem certificate's carrier unfold face).               *)
Lemma ga2_07s_cert_carrier_unfold :
  forall (a : nat -> Real) (b : nat -> Cx) (B : Real)
         (Ha_anti : forall m n : nat, NatLe m n -> real_le (a n) (a m))
         (Hb_bounded : forall N : nat,
            real_le (c_norm_sq (c_abssum N b)) (real_mult B B)),
    abel_tail a b B Ha_anti Hb_bounded =
    (forall (M N : nat), NatLe (S M) N ->
       real_le (c_norm_sq (c_wsum M N a b))
               (sq (real_mult (real_const (2#1))
                      (real_mult B (a (S M)))))).
Proof. intros a b B Ha_anti Hb_bounded. reflexivity. Qed.

(* The supply theorem premise-closes the carried statement.             *)
Lemma ga2_07s_cert_supply_inhabits :
  forall (a : nat -> Real) (b : nat -> Cx) (B : Real)
         (Ha_anti : forall m n : nat, NatLe m n -> real_le (a n) (a m))
         (Hb_bounded : forall N : nat,
            real_le (c_norm_sq (c_abssum N b)) (real_mult B B))
         (Ha_nonneg : forall n : nat, real_le real_zero (a n))
         (HB_nonneg : real_le real_zero B)
         (Htri : abel_tri_pair_face),
    abel_tail a b B Ha_anti Hb_bounded.
Proof.
  intros a b B Ha_anti Hb_bounded Ha_nonneg HB_nonneg Htri.
  exact (abel_tail_supply a b B Ha_anti Hb_bounded Ha_nonneg HB_nonneg Htri).
Qed.

(* The triangle face unfolds to its four-premise conjunction form.       *)
Lemma ga2_07s_cert_tri_face_unfold :
  abel_tri_pair_face =
  (forall (x y : Cx) (rx ry : Real),
     real_le real_zero rx -> real_le real_zero ry ->
     real_le (c_norm_sq x) (sq rx) -> real_le (c_norm_sq y) (sq ry) ->
     real_le (c_norm_sq (c_plus x y)) (sq (real_plus rx ry))).
Proof. reflexivity. Qed.

(* ==== Band 2: the counterexample replica (the nonnegativity premise   *)
(* is necessary) ====                                                    *)

(* The counterexample coefficient column a n = 2 - n (antitone, dips     *)
(* negative inside the window) and the sign column b n = alt_sign n.     *)
Definition ga2_07s_a_counter (n : nat) : Real :=
  real_const ((2 - Z.of_nat n) # 1)%Q.
Definition ga2_07s_b_col : nat -> Cx := eta_sgn_cx.
Definition ga2_07s_B_one : Real := real_const 1.

(* The prefix sums of the sign column stay within the unit band (the     *)
(* carried premise holds at the samples 0..3).                           *)
Lemma ga2_07s_cert_counter_prefix :
  Qle_bool (Qabs (projT1 (cRe (c_abssum 3 ga2_07s_b_col)) 4%nat)) (1#1) = true.
Proof. vm_compute. reflexivity. Qed.

(* The coefficient column is antitone at the sample pair (3, 2).         *)
Lemma ga2_07s_cert_counter_anti :
  Qle_bool ((2 - Z.of_nat 3)#1) ((2 - Z.of_nat 2)#1) = true.
Proof. vm_compute. reflexivity. Qed.

(* The window sum at M = 1, N = 3 carries value -1 on the real axis.     *)
Lemma ga2_07s_cert_counter_wsum :
  projT1 (cRe (c_wsum 1 3 ga2_07s_a_counter ga2_07s_b_col)) 4%nat = ((-1)#1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* The carried bound collapses to zero: sq (2 * B * a 2) = 0.            *)
Lemma ga2_07s_cert_counter_rhs :
  projT1 (sq (real_mult (real_const (2#1))
                 (real_mult ga2_07s_B_one (ga2_07s_a_counter 2)))) 4%nat
  = (0#1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* The squared-modulus gate fails: 1 <= 0 is false.  This is the machine *)
(* replica of the exact-rational mirror check behind the nonnegativity   *)
(* premise of [abel_tail_supply].                                        *)
Lemma ga2_07s_cert_counter_gate :
  Qle_bool (projT1 (c_norm_sq (c_wsum 1 3 ga2_07s_a_counter ga2_07s_b_col)) 4%nat)
           (projT1 (sq (real_mult (real_const (2#1))
                      (real_mult ga2_07s_B_one (ga2_07s_a_counter 2)))) 4%nat)
  = false.
Proof. vm_compute. reflexivity. Qed.

(* The positive replica: the constant unit coefficient satisfies the     *)
(* nonnegativity premise and the bound holds (0 <= 4 at the sample).     *)
Definition ga2_07s_a_unit : nat -> Real := fun _ => real_const 1.

Lemma ga2_07s_cert_positive_wsum :
  projT1 (cRe (c_wsum 1 3 ga2_07s_a_unit ga2_07s_b_col)) 4%nat = (0#1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma ga2_07s_cert_positive_gate :
  Qle_bool (projT1 (c_norm_sq (c_wsum 1 3 ga2_07s_a_unit ga2_07s_b_col)) 4%nat)
           (projT1 (sq (real_mult (real_const (2#1))
                      (real_mult ga2_07s_B_one (ga2_07s_a_unit 2)))) 4%nat)
  = true.
Proof. vm_compute. reflexivity. Qed.

(* ==== Band 3: the composite certificate bool list ==== *)

Definition zz_ga2_07s_cert_samples : list bool :=
  (Qeq_bool (projT1 (cRe (c_wsum 1 3 ga2_07s_a_counter ga2_07s_b_col)) 4%nat)
            ((-1)#1))
  :: (Qeq_bool (projT1 (sq (real_mult (real_const (2#1))
                     (real_mult ga2_07s_B_one (ga2_07s_a_counter 2)))) 4%nat)
            (0#1))
  :: (Qle_bool (projT1 (c_norm_sq (c_wsum 1 3 ga2_07s_a_counter ga2_07s_b_col))
                    4%nat)
             (projT1 (sq (real_mult (real_const (2#1))
                        (real_mult ga2_07s_B_one (ga2_07s_a_counter 2)))) 4%nat))
  :: (Qle_bool (projT1 (c_norm_sq (c_wsum 1 3 ga2_07s_a_unit ga2_07s_b_col))
                    4%nat)
             (projT1 (sq (real_mult (real_const (2#1))
                        (real_mult ga2_07s_B_one (ga2_07s_a_unit 2)))) 4%nat))
  :: nil.

Lemma zz_ga2_07s_cert_samples_true :
  zz_ga2_07s_cert_samples = true :: true :: false :: true :: nil.
Proof. vm_compute. reflexivity. Qed.
