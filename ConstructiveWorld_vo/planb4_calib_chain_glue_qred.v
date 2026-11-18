(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: glue, part 3 of 3 *)
(** * planb4_calib_chain_glue_qred: canonicalization bridge for the chain faces: the Set-equality projector between the zzId carrier and the propositional equality, plus the Qred faces the chain consumers rely on: the Qred insertion law at Qeq_bool face and the Qnum-of-canonicalized-integer injection face.  Also carries the canonical-form transfer bridge: a boolean Q equality carries to syntactic equality of the Qred forms (stdlib Qred_complete), the assembly law a windowed fold consumer of the sum glue would reduce through.

    Mission.  canonicalization bridge for the chain faces: the Set-equality projector between the zzId carrier and the propositional equality, plus the Qred faces the chain consumers rely on: the Qred insertion law at Qeq_bool face and the Qnum-of-canonicalized-integer injection face.  Also carries the canonical-form transfer bridge: a boolean Q equality carries to syntactic equality of the Qred forms (stdlib Qred_complete), the assembly law a windowed fold consumer of the sum glue would reduce through.

    Dependencies.  zzm1_gauss (zzId carrier, zzIdR, zzId_from_eq); stdlib QArith.Qcanon (Qred_correct, Qred_identity, Qred_complete, Qeq_eq_bool, Qeq_bool_eq); ZArith (Z.eqb_eq, Z.gcd_1_r).

    References.  zzm1_gauss.v:27-55 (zzId carrier and its bool projector precedent zzId_true); planb4_g1_laur_extract.v:26 (Qred usage face); planb4_g1_ab_def.v:60-67 (the Qred-canonicalized assemblies this bridge serves).

    Constructivity.  One match-defined projector, one stdlib-citation proof, and one bridge Definition; no axioms, no admits; expected Print Assumptions output: Closed for every statement.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_glue_qred.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
Require Import zzm1_gauss.

Open Scope Q_scope.

(* Generic projector: the zzId carrier reflects to propositional
   equality.  The bool-sorted special case zzId_true exists in
   zzm1_gauss; the chain consumers rewrite through this list-level
   generalization. *)
Definition pb4cwin_zzId_eq {A : Set} {x y : A} (p : zzId x y) : x = y :=
  match p in zzId _ y' return x = y' with
  | zzIdR => eq_refl
  end.

(* Qred insertion at boolean face: Qred x and x agree as rationals. *)
Lemma pb4cwin_qred_correct_b : forall x : Q, zzId (Qeq_bool (Qred x) x) true.
Proof.
  intros x. apply zzId_from_eq. apply Qeq_eq_bool. apply Qred_correct.
Qed.

(* Qnum of the canonicalized integer injection lands on the integer. *)
Lemma pb4cwin_qnum_qred_inj_b :
  forall z : Z, zzId (Z.eqb (Qnum (Qred (inject_Z z))) z) true.
Proof.
  intros z. apply zzId_from_eq. apply Z.eqb_eq.
  rewrite (Qred_identity (inject_Z z) (Z.gcd_1_r z)).
  reflexivity.
Qed.

(* Canonical-form transfer: boolean rational equality of p and q forces
   syntactic equality of their Qred forms (the assembly law that turns
   Qeq-carried window sums back into rewrite-material equalities). *)
Definition pb4cwin_qred_canon_eq (p q : Q) (h : zzId (Qeq_bool p q) true)
  : Qred p = Qred q :=
  Qred_complete p q (Qeq_bool_eq p q (zzId_true h)).

Print Assumptions pb4cwin_zzId_eq.
Print Assumptions pb4cwin_qred_correct_b.
Print Assumptions pb4cwin_qnum_qred_inj_b.
Print Assumptions pb4cwin_qred_canon_eq.
