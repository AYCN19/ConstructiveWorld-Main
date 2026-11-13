(* ConstructiveWorld-Main - certificate face of the trigonometric bridge node. *)
(** * LW2TrigBridge_cert: certificate face of node LW2TrigBridge.

    Mission.  The numeric point facts of node LW2TrigBridge: the
    literal Q-identity [Qabs (1 # 2) == 1 # 2], the modulus-halving
    factor consumed by the half-scalar contract
    [lw2_half_mult_eq_compat] of the statement face.  The statement
    faces of the node are untouched; this face only adds the numeric
    certificate and carries no statement of its own beyond it.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs].  One-way
    edge: the statement face [LW2TrigBridge] requires this
    certificate; the certificate is statement-free and requires
    nothing back, so the dependency stays acyclic.

    References.  The certificate-face precedents
    [GaC2_14_PhragmenLindelof_cert] and [GaC2_10_EtaContinuation_cert];
    mathlib [Real.cos_pi_half] composition facts (statement shape
    only).

    Constructivity.  The Q identity closes by kernel evaluation;
    zero axioms, zero admitted goals, zero classical principles; the
    identity is a point fact at the Q equality level, consumed inside
    proofs of the statement face, whose carriers stay Set-typed.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
    -Q <build dir> "" LW2TrigBridge_cert.v] from the flat build
    directory; acceptance runs [50_toolkit/accept_node.py --node
    LW2TrigBridge] with both faces of the node. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.

(* ---- The literal half-scalar identity ----
   Consumed by [lw2_half_mult_eq_compat] of the statement face, where
   the Cauchy approximation modulus is halved pointwise. *)
Lemma lw2_qabs_half : (Qabs (1 # 2) == (1 # 2))%Q.
Proof. vm_compute; reflexivity. Qed.
