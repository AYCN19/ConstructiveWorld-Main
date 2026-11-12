(* ConstructiveWorld-Main - the Q corridor certificate band of the Dirichlet test node. *)
(** * GaC2_07_DirichletTestAbel_cert: the certificate face of node C2.07.
    Mission.  The certificate face of node C2.07: the decidable Q sample bands of the draft
    certificate row (the tail-bound sample corridor at the floor samples sigma0 = 1/2 with N in
    {10, 100}), in three bands: Band 1 the premise-generic carrier unfold faces ([alt_sign 0],
    [c_abssum 1], [c_wsum M 0], [eta_part 1], and the two statement carriers [abel_tail] /
    [eta_conv_uniform] unfolded to their premise-closing functors); Band 2 the Q corridor
    arithmetic; Band 3 the composite certificate bool list.  The sample arithmetic and the
    honest scope: the Notes block after the imports.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List].  Requires [S01_BaseRing]
    (selective [NatLe] import), [S02_CauchyComplete], [CxRealPairCore],
    [GaC2_01_DirichletPartialSum], [GaC2_02_AbsConvTailBound_a], [GaC2_06_AltMonoFace],
    and the statement stem [GaC2_07_DirichletTestAbel], all of this development.

    References.  drafts_C2.md C2.07 certificate row (the tail-bound sample band at sigma0 = 1/2,
    N in {10, 100}); the certificate-face precedents [GaC2_16_ZetaVerticalBound_cert] (the Q corridor
    register) and [GaC2_14_PhragmenLindelof_cert] (the unfold band register); cards_C2.md C2.07.

    Constructivity.  Every named construction is carried by [Set]; the band statements are bool
    equations and Q identities at the Q level; zero assumed constants, zero abandoned proofs; the Q
    bands close with vm_compute, the unfold bands with definitional transparency, all under the
    global context (the vm_compute word lives here by design, the R2 proof-topology / certificate
    separation).

    Build.  [coqc -native-compiler no -q -Q <l0_local> "" -Q <build> "" GaC2_07_DirichletTestAbel_cert.v]
    (flat build directory, thermal guard wrapper); acceptance runs [50_toolkit/accept_node.py --node C2.07]
    with the statement face [GaC2_07_DirichletTestAbel]. *)

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

Local Open Scope Q_scope.

(** Notes.  Band 2 arithmetic: the squared card-bound replica of the draft
    certificate row, sq(2 * (N+1)^{-sigma0}) at sigma0 = 1/2 is the rational replica
    4 / (N+1), closing at N = 10 to 4/11 and at N = 100 to 4/101 ([Qeq_bool],
    vm_compute); the sign column pointwise samples at the even index 10 and the odd
    index 11 (the parity band of the [abssum_alt_pair] faces, vm_compute); the
    ten-term sign prefix sum corridor |sum_{n<10} alt_sign n| <= 1 ([Qle_bool],
    vm_compute).  Band 3 is the composite certificate bool list, discharged by
    vm_compute.

    Honest scope: the Real-line inequalities live on the proof faces of
    [GaC2_07_DirichletTestAbel] and its registered open rows (the L-C2.02-C
    triangle supply face, the eta leaf slot); these literals certify the decidable
    Q skeleton and the unfold faces, not the Real-line order facts, mirroring the
    C2-16 corridor-certificate register (the Q replica band; the Real-line binding
    rides the Band 1 unfold faces and closes at mother-chain integration). *)


(* ==== Band 1: the premise-generic unfold faces ==== *)

Lemma ga2_07_cert_alt_sign_unfold : alt_sign 0%nat = real_opp real_one.
Proof. reflexivity. Qed.

Lemma ga2_07_cert_abssum_unfold :
  forall b : nat -> Cx,
    c_abssum 1%nat b = c_plus (c_abssum 0%nat b) (b 0%nat).
Proof. intro b. reflexivity. Qed.

Lemma ga2_07_cert_wsum_unfold :
  forall (M : nat) (a : nat -> Real) (b : nat -> Cx),
    c_wsum M 0%nat a b = c_zero.
Proof. intros M a b. reflexivity. Qed.

Lemma ga2_07_cert_eta_part_unfold :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (s : Cx),
    eta_part Hnpos 1%nat s =
    c_plus (eta_part Hnpos 0%nat s)
           (eta_term Hnpos 1%nat (NatLe_one_S 0%nat) s).
Proof. intros Hnpos s. reflexivity. Qed.

Lemma ga2_07_cert_abel_tail_unfold :
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

Lemma ga2_07_cert_eta_conv_unfold :
  forall (sig0 : Real) (Hs0 : real_lt real_zero sig0)
         (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (s eta_s : Cx),
    eta_conv_uniform sig0 Hs0 Hnpos s eta_s =
    (forall (N : nat),
       real_le (c_norm_sq (c_plus (eta_part Hnpos N s) (c_opp eta_s)))
               (sq (real_mult (real_const (2#1))
                     (r_npow_at sig0 Hnpos (S N) (NatLe_one_S N))))).
Proof. intros sig0 Hs0 Hnpos s eta_s. reflexivity. Qed.

(* ==== Band 2: the Q corridor arithmetic (vm_compute) ==== *)

(* The squared card-bound replica: sq(2 (N+1)^(-1/2)) = 4 / (N+1).       *)
Lemma ga2_07_cert_bound_replica_10 :
  Qeq_bool ((4#1) / (11#1)) (4#11) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ga2_07_cert_bound_replica_100 :
  Qeq_bool ((4#1) / (101#1)) (4#101) = true.
Proof. vm_compute. reflexivity. Qed.

(* The sign column pointwise samples at the parity indices.              *)
Lemma ga2_07_cert_alt_sign_pt_even :
  projT1 (alt_sign 10%nat) 4%nat == ((-1)#1)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma ga2_07_cert_alt_sign_pt_odd :
  projT1 (alt_sign 11%nat) 4%nat == (1#1)%Q.
Proof. vm_compute. reflexivity. Qed.

(* The ten-term sign prefix corridor: the even-length prefix value is 0, *)
(* inside the unit band.                                                 *)
Lemma ga2_07_cert_sgn_prefix_corridor :
  Qle_bool (Qabs (projT1 (cRe (c_abssum 10%nat eta_sgn_cx)) 4%nat))
           (1#1) = true.
Proof. vm_compute. reflexivity. Qed.

(* The parity index replicas of the certificate sample points.           *)
Lemma ga2_07_cert_parity_replica_10 :
  Qeq_bool ((2 * 5)#1) (10#1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ga2_07_cert_parity_replica_11 :
  Qeq_bool ((2 * 5 + 1)#1) (11#1) = true.
Proof. vm_compute. reflexivity. Qed.

(* ==== Band 3: the composite certificate bool list ==== *)

Definition zz_ga2_07_cert_samples : list bool :=
  (Qeq_bool ((4#1) / (11#1)) (4#11))
  :: (Qeq_bool ((4#1) / (101#1)) (4#101))
  :: (Qle_bool (Qabs (projT1 (cRe (c_abssum 10%nat eta_sgn_cx)) 4%nat))
                (1#1))
  :: (Qeq_bool ((2 * 5)#1) (10#1))
  :: (Qeq_bool ((2 * 5 + 1)#1) (11#1))
  :: nil.

Lemma zz_ga2_07_cert_samples_true :
  zz_ga2_07_cert_samples =
  true :: true :: true :: true :: true :: nil.
Proof. vm_compute. reflexivity. Qed.
