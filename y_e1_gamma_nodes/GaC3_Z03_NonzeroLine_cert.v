(* ConstructiveWorld-Main - certificate face of the nonvanishing line node. *)

(** * GaC3_Z03_NonzeroLine_cert: certificate face of node C3-Z03.
    Mission.  Certificate face of node C3-Z03: the explicit-radius
    literal band of the three-cosine racing engine (the explicit-radius
    obligation of the card, the Q-level window witness).  Bands: (1) the
    radius literal [z03_radius_lit] = 1/64; (2) the positivity face
    [z03_radius_pos] (the racing offset stays positive); (3) the racing
    margin face [z03_radius_margin] (the margin 4 * (1/(2d)) computes to
    128 at d = 1/64).
    Dependencies.  [S02_CauchyComplete] ([QltT], [QeqT]); Stdlib
    [QArith.QArith] only beyond that (the band statements are
    base-standalone rational identities).
    References.  drafts_C3.md C3-Z03 acceptance lines (the
    explicit-radius obligation: the quantitative version carries an
    explicit contradiction radius, the certificate band closes the
    literal); the tree precedent [GaC2_18_ZetaDerivBound_cert] (the
    certificate-face shape of the constant and radius sample bands).
    Constructivity.  Set-sorted rational identities; zero assumed
    constants, zero abandoned proofs; the bands close by the compute
    tactic under the global context (the R2 word-face lives here by
    design, the certificate-face discipline).
    Build.  coqc -native-compiler no -q -Q . "" -Q <boot_src> "" GaC3_Z03_NonzeroLine_cert.v (work directory, dependency-closure build). *)

From Stdlib Require Import QArith.QArith.
(** Notes.  Honest scope (fail-loud): these bands certify the rational
    window witness only; the Real-line racing contradiction lives on the
    race face with the premise slots, and the discharge of the main-part
    slot awaits the eta-continuation supply face (the registered open
    supply face of the zero factorization route). *)
Require Import S02_CauchyComplete.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Part 3. The explicit radius literal (the Q-level window witness).      *)
(* ===================================================================== *)

(* The radius literal d = 1/64: the offset stays positive and the       *)
(* racing margin 4*(1/(2d)) computes to 128. *)
Definition z03_radius_lit : Q := (1 # 64)%Q.

Lemma z03_radius_pos : QltT 0 z03_radius_lit.
Proof. unfold z03_radius_lit. vm_compute. reflexivity. Qed.

Lemma z03_radius_margin :
  QeqT (4 * Qdiv 1 (2 * z03_radius_lit)) (Qmake 128 1)%Q.
Proof. unfold z03_radius_lit. vm_compute. reflexivity. Qed.
