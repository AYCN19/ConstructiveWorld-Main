(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: glue, part 2 of 3 *)
(** * planb4_calib_chain_glue_sumf: index-shift additivity for the finite-sum fold zz_sumf: the fold over [0, n1+n2) equals up to rational equality the n1-prefix sum plus the shifted fold over [n1, n1+n2).  Since Qplus reassociation changes the Q representation, the landing faces carry the equality on canonical forms (zzId on the Qred images, a syntactic equality) and at boolean face (zzId on Qeq_bool); this is the glue a windowed fold consumer of the linform reduction uses to split the principal part into per-window certificates.

    Mission.  index-shift additivity for the finite-sum fold zz_sumf: the fold over [0, n1+n2) equals up to rational equality the n1-prefix sum plus the shifted fold over [n1, n1+n2).  Since Qplus reassociation changes the Q representation, the landing faces carry the equality on canonical forms (zzId on the Qred images, a syntactic equality) and at boolean face (zzId on Qeq_bool); this is the glue a windowed fold consumer of the linform reduction uses to split the principal part into per-window certificates.

    Dependencies.  zzm1_gauss (zzId carrier); zzm1b_linform_bridge (zz_sumf); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); stdlib QArith (Qred_correct, Qred_complete, Qeq_eq_bool, Qeq_refl, Qplus_assoc, Qplus_0_r), Arith.PeanoNat (Nat.add_0_r, Nat.add_succ_r).

    References.  zzm1b_linform_bridge.v:43-47 (the fold definition); probe_glue_sumf.v (verified prototype of the same equation at propositional face).

    Constructivity.  One induction over the definitional fold equation with Qplus reassociation; the propositional Qeq derivation lives inside the proof bodies and both landed statements are Set-borne; no axioms, no admits; expected Print Assumptions output: Closed.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_glue_sumf.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
From Stdlib Require Import Arith.PeanoNat.
Require Import zzm1_gauss.
Require Import zzm1b_linform_bridge.
Require Import planb4_calib_chain_glue_qred.

Open Scope Q_scope.

(* Fold additivity with an index shift, on canonical forms: the Qred
   image of the window [0, n1+n2) fold equals the Qred image of the
   split sum.  The nat additions carry the %nat mark: Q_scope is open
   here, so a bare + would parse as Qplus. *)
Lemma pb4cwin_sumf_shift_split :
  forall (f : nat -> Q) (n1 n2 : nat),
    zzId (Qred (zz_sumf f (n1 + n2)%nat))
         (Qred (zz_sumf f n1
                + zz_sumf (fun k => f ((n1 + k)%nat)) n2)).
Proof.
  intros f n1 n2; revert f n1.
  induction n2 as [| k IH]; intros f n1.
  - rewrite Nat.add_0_r. cbn [zz_sumf].
    apply zzId_from_eq. apply Qred_complete.
    symmetry. apply Qplus_0_r.
  - rewrite Nat.add_succ_r. cbn [zz_sumf].
    apply zzId_from_eq. apply Qred_complete.
    assert (Hceq : zz_sumf f (n1 + k)%nat ==
                   zz_sumf f n1
                   + zz_sumf (fun t => f ((n1 + t)%nat)) k).
    { rewrite <- (Qred_correct (zz_sumf f (n1 + k)%nat)).
      rewrite <- (Qred_correct (zz_sumf f n1
                    + zz_sumf (fun t => f ((n1 + t)%nat)) k)).
      rewrite (pb4cwin_zzId_eq (IH f n1)).
      apply Qeq_refl. }
    rewrite Hceq. symmetry. apply Qplus_assoc.
Qed.

(* Boolean face of the same equation over the bare sums. *)
Lemma pb4cwin_sumf_shift_split_b :
  forall (f : nat -> Q) (n1 n2 : nat),
    zzId (Qeq_bool (zz_sumf f (n1 + n2)%nat)
                   (zz_sumf f n1
                    + zz_sumf (fun k => f ((n1 + k)%nat)) n2)) true.
Proof.
  intros f n1 n2. apply zzId_from_eq. apply Qeq_eq_bool.
  rewrite <- (Qred_correct (zz_sumf f (n1 + n2)%nat)).
  rewrite <- (Qred_correct (zz_sumf f n1
                + zz_sumf (fun k => f ((n1 + k)%nat)) n2)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_sumf_shift_split f n1 n2)).
  apply Qeq_refl.
Qed.

Print Assumptions pb4cwin_sumf_shift_split.
Print Assumptions pb4cwin_sumf_shift_split_b.
