(** * cast_parity: the family-three 3a parity-interleave faces of the
      Machin partial-sum sequence.

    Mission.  Cast the exploration-volume section-two family-three 3a
    parity-interleave faces (canonical script chong1_exit_core.py:254-258,
    grid-checked there; numerical anchors chong1_run1.log L54-L58) as the
    named theorem parity_interleave_mdot, a Set-carried bundle of the
    j = 0 instance faces:

      parity   : Mdot(0) > Mdot(40) + w(40)  and  Mdot(1) + w(40) < Mdot(40)
                 (the canonical form is Mdot(2j) > PI > Mdot(2j+1) with
                 reference depth PI = Mdot(2600) and own-modulus margin
                 w(2600), exit_core.py:87/:255)
      pair-mono: Mdot(2) < Mdot(0)  and  Mdot(1) < Mdot(3)
                 (exit_core.py:256: Mdot(2j+2) < Mdot(2j) and
                 Mdot(2j+3) > Mdot(2j+1))
      cross    : Mdot(1) < Mdot(0)  (exit_core.py:257: Mdot(2j'+1) <
                 Mdot(2j) for all j, j' < 60)
      width    : Mdot(0) - Mdot(1) == 16*a_1(1/5) - 4*a_1(1/239)
                 (exit_core.py:266-269: the W_j closed form
                 W_j == Mdot(2j) - Mdot(2j+1))

    where Mdot(k) = 16*S_k(1/5) - 4*S_k(1/239) is the Machin partial
    sum (arctan_partial, S11_TP3B5.v:53) and w(k) = 16*a_{k+1}(1/5) +
    4*a_{k+1}(1/239) is the atan_tail_bound own modulus (S11_TP3B5.v:301
    width faces, exit_core.py:73).  No new analytic content: every
    statement is an instance of the canonical section-two faces above.

    Registered downgrade (evaluation-budget clause, 20261114).  The
    canonical reference depth is 2600 (exit_core.py:87: PI = Mdot(2600)).
    The vm_compute evaluation of the depth-2600 reference faces exceeded
    the seconds-level evaluation budget by more than 100x (probe run
    _rv_parity_probe2.log: over 600s on the first depth-2600 face; the
    in-library arctan_partial is a Qsum with per-operation rational
    normalization, unlike the integer-accumulating canonical script).
    Per the evaluation-budget rule the reference depth was downgraded to
    40 (same face form, own-modulus margin w(40)); the depth is a free
    instance parameter of the canonical quantified face.  This downgrade
    is registered for adjudication in the seat receipt; it is not a
    silent substitution.

    Dependencies.  S01_BaseRing (And as the Set-level product),
    S02_CauchyComplete (QltT / QeqT / QleT' Set carriers),
    S03_QExp (q_pow), S11_TP3B5 (arctan_partial, atan_mag).

    References.  arctan_partial = S11_TP3B5.v:53; atan_mag =
    S11_TP3B5.v:60; Mdot face = chong1_exit_core.py:65; own-modulus
    face = chong1_exit_core.py:73; reference PI = Mdot(2600) =
    chong1_exit_core.py:87; family-three 3a faces = chong1_exit_core.py
    :254-258; W_j closed form = chong1_exit_core.py:266-269; numerical
    anchors = chong1_run1.log L54-L58; M1:438 prescription (P7
    bridge-level assembly).

    Constructivity.  Zero axioms, zero admitted goals; every named
    statement is Set-carried (QltT / QeqT / QleT' are Id-carriers over
    the decidable Q comparisons, And is the S01 Set-level product).
    Each face is certified by an exact vm_compute arithmetic closure
    (the machine, not hand arithmetic, evaluates every rational); the
    proofs are definitional closures, disclosed as such.  No Prop named
    statements; the 3695-bit family-one numerator route and the
    forbidden family-two / family-four routes are never touched.

    Build.  coqc -native-compiler no -q -Q . "" cast_parity.v  (world
    directory holding S01-S15, UpReqIrrationalCriterion, PiEnvelope,
    mach_fold_q, mach_atan_addsub, mach_fold_chain compiled). *)

Require Import S01_BaseRing S02_CauchyComplete S03_QExp S11_TP3B5.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax ZArith.
From Stdlib Require Import Lqa.

(* ============================================================ *)
(* Section 1.  Statement-face definitions (transcriptions).      *)
(* ============================================================ *)

(* Machin partial sum: Mdot k = 16*S_k(1/5) - 4*S_k(1/239)
   (canonical script chong1_exit_core.py:65). *)
Definition mach_mdot (k : nat) : Q :=
  16 * arctan_partial k (1 # 5) - 4 * arctan_partial k (1 # 239).

(* Own modulus of the Machin sequence: w k = 16*a_{k+1}(1/5) +
   4*a_{k+1}(1/239), the atan_tail_bound tail width
   (canonical script chong1_exit_core.py:73). *)
Definition mach_own_modulus (k : nat) : Q :=
  16 * atan_mag (Datatypes.S k) (1 # 5)
  + 4 * atan_mag (Datatypes.S k) (1 # 239).

(* ============================================================ *)
(* Section 2.  The parity faces (canonical 3a, j = 0 instance).  *)
(* ============================================================ *)

(* Parity, upper leg: Mdot(0) > Mdot(40) + w(40).  The canonical
   reference depth is 2600 (exit_core.py:87); downgraded to 40 per the
   registered evaluation-budget clause (see header). *)
Lemma parity_face_even0 : QltT (mach_mdot 40)
                               (mach_mdot 0 - mach_own_modulus 40).
Proof.
  unfold mach_mdot, mach_own_modulus.
  vm_compute. reflexivity.
Qed.

(* Parity, lower leg: Mdot(1) + w(40) < Mdot(40). *)
Lemma parity_face_odd0 : QltT (mach_mdot 1 + mach_own_modulus 40)
                              (mach_mdot 40).
Proof.
  unfold mach_mdot, mach_own_modulus.
  vm_compute. reflexivity.
Qed.

(* Pair monotonicity: Mdot(2) < Mdot(0) and Mdot(1) < Mdot(3)
   (exit_core.py:256 instance at j = 0). *)
Lemma parity_face_mono0 :
  And (QltT (mach_mdot 2) (mach_mdot 0))
      (QltT (mach_mdot 1) (mach_mdot 3)).
Proof.
  split;
    (unfold mach_mdot; vm_compute; reflexivity).
Qed.

(* Cross interlacing: Mdot(1) < Mdot(0) (exit_core.py:257 instance at
   j = j' = 0). *)
Lemma parity_face_cross0 : QltT (mach_mdot 1) (mach_mdot 0).
Proof.
  unfold mach_mdot.
  vm_compute. reflexivity.
Qed.

(* Width closed form: Mdot(0) - Mdot(1) == 16*a_1(1/5) - 4*a_1(1/239)
   (exit_core.py:266-269, the W_0 closed form W_0 == Mdot(0) -
   Mdot(1)). *)
Lemma parity_face_width0 :
  QeqT (mach_mdot 0 - mach_mdot 1)
       (16 * atan_mag 1 (1 # 5)%Q - 4 * atan_mag 1 (1 # 239)%Q).
Proof.
  unfold mach_mdot.
  vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* Section 3.  The named theorem (the 3a instance bundle).       *)
(* ============================================================ *)

Theorem parity_interleave_mdot :
  And (QltT (mach_mdot 40) (mach_mdot 0 - mach_own_modulus 40))
  (And (QltT (mach_mdot 1 + mach_own_modulus 40) (mach_mdot 40))
  (And (And (QltT (mach_mdot 2) (mach_mdot 0))
            (QltT (mach_mdot 1) (mach_mdot 3)))
  (And (QltT (mach_mdot 1) (mach_mdot 0))
       (QeqT (mach_mdot 0 - mach_mdot 1)
             (16 * atan_mag 1 (1 # 5)%Q
              - 4 * atan_mag 1 (1 # 239)%Q))))).
Proof.
  split.  exact parity_face_even0.
  split.  exact parity_face_odd0.
  split.  exact parity_face_mono0.
  split.  exact parity_face_cross0.
          exact parity_face_width0.
Defined.

Print Assumptions parity_interleave_mdot.
