(* ConstructiveWorld-Main - the Q corridor certificate band of the zeta    *)
(* vertical-line bound node (the R2 numeric face, vm_compute by design).   *)

(** * GaC2_16_ZetaVerticalBound_cert: the certificate stem.

    Mission.  The certificate face of node C2.16 (the draft certificate
    band: the C1 / C2 / segment-point literal samples at the t samples
    2 / 10 / 100 and three sigma samples, closed by vm_compute).  Two
    bands.  Band 1: the premise-generic carrier unfold faces - the
    zeta column ([r_zeta_seq] unfolds to the [r_tsum] block form), the
    log wrapper ([log_t] unfolds to [real_log] on the strict-floor
    premise), the square and scalar carriers ([sq], [c_scale'] unfold
    to [real_mult]) - the binding faces that tie the numeric band to
    the certified carriers of the main stem.  Band 2: the Q corridor
    arithmetic.  The condensation corridor constant of the (a) face at
    the Q replica  1 + q / (1 - q)  with q = 2^(1 - sigma): at the
    sigma samples 2 / 3 / 4 the corridor closes at 2 / 4-3 / 8-7
    (Qeq_bool, vm_compute).  The log-corridor arithmetic of the (b)/(c)
    faces: the C1 = 4 sample product at the t samples (4 x 693 = 2772,
    4 x 2303 = 9212, 4 x 4605 = 18420, at the thousandth numerals) and
    the C2 = 6 sample products (4158, 27630) - the corridor numerals
    enter as literals, so the certified content is the corridor
    arithmetic itself, not a claim that the numerals equal the tree
    real_log values; the binding rides the Band 1 unfold faces and
    closes at mother-chain integration (the corridor-certificate
    register of the toolkit cert pair precedent).  The segment-point
    band: the t samples 2 <= 10 <= 100 (Qle_bool, vm_compute).

    Dependencies.  Stdlib [QArith.QArith].  Requires [S01_BaseRing]
    (selective [NatLe] import), [S02_CauchyComplete] ([real_eq]),
    [S07_RealSetoidExpLog] ([real_log]), [GaC2_01_DirichletPartialSum]
    ([nat_real], the positivity premise shape), [GaC2_02_AbsConvTailBound_b]
    ([r_tsum]), [GaC2_05_EulerLimitAsm] ([r_zeta_seq]), and the main
    stem [GaC2_16_ZetaVerticalBound] ([sq], [c_scale'], [log_t]).

    References.  drafts_C2.md C2.16 draft-4 acceptance (the certificate
    band item: the C1 / C2 / segment-point literal samples, vm_compute,
    the positive exemplar register); the toolkit cert pair precedent
    (the Q band closes with vm_compute, the premise-generic unfold
    band rides cbn / reflexivity).

    Constructivity.  Every named construction is carried by [Set]; the
    band statements are bool equations at the Q level; zero assumed
    constants; zero abandoned proofs; the vm_compute word lives here by
    design (the R2 proof-topology / certificate separation).

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
    -Q <build shadow> "" GaC2_16_ZetaVerticalBound_cert.v] compiles
    cleanly (exit 0) after the main stem, wrapped by [cpu_guard v3]
    per the acceptance gate. *)

From Stdlib Require Import QArith.QArith.
Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_b.
Require Import GaC2_05_EulerLimitAsm.
Require Import GaC2_16_ZetaVerticalBound.

Local Open Scope Q_scope.

(* ==== Band 1: the premise-generic carrier unfold faces ==== *)

(* The zeta column unfolds to the block-form sigma sum. *)
Lemma GaC2_16_cert_zcol_unfold :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (sig : Real) (N : nat),
    real_eq (r_zeta_seq Hnpos sig N) (r_tsum Hnpos sig 0 N).
Proof.
  intros Hnpos sig N. unfold r_zeta_seq. apply real_eq_refl.
Qed.

(* The log wrapper unfolds to the tree real_log on the strict floor. *)
Lemma GaC2_16_cert_log_t_unfold :
  forall (t : Real) (Ht1 : real_lt real_one t),
    real_eq (log_t t Ht1)
            (real_log t (real_lt_trans real_zero real_one t real_lt_zero_one Ht1)).
Proof.
  intros t Ht1. unfold log_t. apply real_eq_refl.
Qed.

(* The square and scalar carriers unfold to the real product. *)
Lemma GaC2_16_cert_sq_unfold :
  forall x : Real, real_eq (sq x) (real_mult x x).
Proof.
  intro x. unfold sq. apply real_eq_refl.
Qed.

Lemma GaC2_16_cert_cscale_unfold :
  forall a x : Real, real_eq (c_scale' a x) (real_mult a x).
Proof.
  intros a x. unfold c_scale'. apply real_eq_refl.
Qed.

(* ==== Band 2: the Q corridor arithmetic (vm_compute) ==== *)

(* The Q replica of the condensation corridor constant: 1 + q / (1 - q)  *)
(* at q = 2^(1 - sigma); the sigma samples 2 / 3 / 4 give q =            *)
(* 1/2 / 1/4 / 1/8.                                                      *)
Definition GaC2_16_qcorridor (q : Q) : Q := (1 + q * Qinv (1 - q))%Q.

(* sigma = 2: the corridor closes at 2. *)
Lemma GaC2_16_cert_corridor_s2 :
  Qeq_bool (GaC2_16_qcorridor (1#2)%Q) (2#1)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* sigma = 3: the corridor closes at 4/3. *)
Lemma GaC2_16_cert_corridor_s3 :
  Qeq_bool (GaC2_16_qcorridor (1#4)%Q) (4#3)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* sigma = 4: the corridor closes at 8/7. *)
Lemma GaC2_16_cert_corridor_s4 :
  Qeq_bool (GaC2_16_qcorridor (1#8)%Q) (8#7)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* The segment-point band: the t samples 2 <= 10 <= 100. *)
Lemma GaC2_16_cert_tband :
  Qle_bool (2#1)%Q (10#1)%Q && Qle_bool (10#1)%Q (100#1)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* The C1 = 4 log-corridor sample products at the t samples (the         *)
(* thousandth corridor numerals for ln 2 / ln 10 / ln 100). *)
Lemma GaC2_16_cert_c1_band :
  Qeq_bool ((4#1)%Q * (693#1000)%Q) (2772#1000)%Q = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC2_16_cert_c1_band_10 :
  Qeq_bool ((4#1)%Q * (2303#1000)%Q) (9212#1000)%Q = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC2_16_cert_c1_band_100 :
  Qeq_bool ((4#1)%Q * (4605#1000)%Q) (18420#1000)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* The C2 = 6 log-corridor sample products at the t = 2 / t = 100        *)
(* samples. *)
Lemma GaC2_16_cert_c2_band :
  Qeq_bool ((6#1)%Q * (693#1000)%Q) (4158#1000)%Q = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC2_16_cert_c2_band_100 :
  Qeq_bool ((6#1)%Q * (4605#1000)%Q) (27630#1000)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* ==== Named-item census ==== *)

(* 1 Definition (GaC2_16_qcorridor) + 4 Band-1 unfold lemmas + 9 Band-2  *)
(* corridor lemmas; zero assumed constants, zero abandoned proofs; the   *)
(* nine Band-2 statements close with vm_compute (the R2 word-face lives  *)
(* in this stem by design). *)
