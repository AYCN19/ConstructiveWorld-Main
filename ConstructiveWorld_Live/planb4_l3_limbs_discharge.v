(* ConstructiveWorld-Main - unif L3 piece: the three-limb package file. *)

(** * planb4_l3_limbs_discharge: Hp/Htri re-exports, the exit slot face,
    and the three-limb envelope at the concrete lw0m_xL binding.

    Mission.  L3 lane deliverable (01 work order, section 1, lane L3)
    per rulings dwfq-0917860f-1 and dwfq-0917860f-2: Hp := l2_dv_hp and
    Htri := l2_dv_htri are pure re-exports (no reproof, no duplication);
    the exit limb is the born Set-typed slot face planb4_l3_hexit_slot,
    the l2_dv_hexit_face body transcribed at xL := lw0m_xL (verbatim the
    top-theorem premise shape; never presented as a closed limb); the
    envelope planb4_l3_limbs_bundle packages the triple under the
    explicit honest interface form (the piu1932_uncond_zz six-premise
    precedent): an exit witness yields the limb triple.
    Wall registration.  The exit slot is refuted at (a,b) = (100,1):
    |b - a| = 99 while the tree faces squeeze lw0m_xL into [8/3, 52/15]
    (S10 sc_lp_odd_chain / sc_lp_odd_mono / sc_lp_odd_le_s2, with
    lp_odd 0 = 2/3 definitional), so 100 - xL(k) stays below 99 for
    every k and no threshold K exists.  Mechanical evidence: the
    scratch probe probe_l3_hexit_wall.v (wall_all_k,
    wall_face_uninhabited) closes under the global context (EXIT=0,
    magic 436f7121 000160bc).  The slot awaits supply from the L6
    ledger (ZZ2020 dual-pairing general-anchor or carrier rebinding;
    planb3_g1_g2_design.v:132-137) - not claimed here.
    Constructivity.  Set-carried throughout; proof bodies are witness
    injections only; postulate-free.  Build.  coqc -q -native-compiler
    no -Q <Live> "" planb4_l3_limbs_discharge.v (Rocq 9.3.0, E952). *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import LW0MLicBridge.
Require Import planb4_l2_dv_cast.

(* ================================================================== *)
(* Section 1. The exit slot face (born statement, honestly unproven;  *)
(*            the wall is registered in the header - not a closure).  *)
(*            The L2 face l2_dv_hexit_face is a Set element (a Pi     *)
(*            statement), not a type family, so the binding is given  *)
(*            by transcription at xL := lw0m_xL - beta-convertible    *)
(*            with the face body and verbatim with the top-theorem    *)
(*            premise shape piu1932_uncond_zz.v:84-86.                *)
(* ================================================================== *)

Definition planb4_l3_hexit_slot : Set :=
  forall (a b : Z), (1 <= b)%Z ->
    sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      S02_CauchyComplete.QleT' (l2_dv b (- a)%Z)
        (Qabs (inject_Z b * lw0m_xL k - inject_Z a))).

(* ================================================================== *)
(* Section 2. The two closed limbs (pure re-exports; the born proofs  *)
(*            live in planb4_l2_dv_cast - no reproof, no duplication). *)
(* ================================================================== *)

Definition planb4_l3_hp : forall a b : Z, piu_mu_QleT 0 (l2_dv a b) :=
  l2_dv_hp.

Definition planb4_l3_htri : forall (a b p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
    ((inject_Z (Z.of_nat q) * l2_dv a b
      + inject_Z (Z.abs b) * l2_dv (Z.of_nat q) (- p)%Z)%Q) :=
  l2_dv_htri.

(* ================================================================== *)
(* Section 3. The Set-carried three-limb envelope (explicit honest    *)
(*            interface form): an exit witness yields the triple.     *)
(* ================================================================== *)

(* The envelope is an inhabited package (transparent for L6 consumers):  *)
(* the type is the Set-carried triple face, the value is the pairing     *)
(* of the two closed re-exports with the exit witness handed over.       *)
Definition planb4_l3_limbs_bundle
  : forall Hex : planb4_l3_hexit_slot,
      sigT (fun Hp : forall a b : Z, piu_mu_QleT 0 (l2_dv a b) =>
        sigT (fun Htri : forall (a b p : Z) (q : nat), (1 <= q)%nat ->
          piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
            ((inject_Z (Z.of_nat q) * l2_dv a b
              + inject_Z (Z.abs b) * l2_dv (Z.of_nat q) (- p)%Z)%Q) =>
          planb4_l3_hexit_slot)).
Proof.
  intros Hex. exists l2_dv_hp. exists l2_dv_htri. exact Hex.
Defined.

(* ================================================================== *)
(* Section 4. Assumption audit (per-statement, tail).                 *)
(* ================================================================== *)

Print Assumptions planb4_l3_hexit_slot.
Print Assumptions planb4_l3_hp.
Print Assumptions planb4_l3_htri.
Print Assumptions planb4_l3_limbs_bundle.
