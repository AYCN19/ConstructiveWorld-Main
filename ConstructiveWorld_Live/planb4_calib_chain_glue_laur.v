(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: glue, part 1 of 3 *)
(** * planb4_calib_chain_glue_laur: fuel-split composition for the Laurent readout stepper: the (k1+k2)-step readout of planb4_g1_laur_go splits into the k1-step prefix appended to the k2-step readout taken from the k1-step remainder state; pb4cwin_rem iterates the tail update and carries the intermediate state.  This is the glue lemma every assembling rewrite in the build files consumes in place of one full-chain bite.

    Mission.  fuel-split composition for the Laurent readout stepper: the (k1+k2)-step readout of planb4_g1_laur_go splits into the k1-step prefix appended to the k2-step readout taken from the k1-step remainder state; pb4cwin_rem iterates the tail update and carries the intermediate state.  This is the glue lemma every assembling rewrite in the build files consumes in place of one full-chain bite.

    Dependencies.  zzm1_gauss (zzId carrier); zzm2_qpoly (consumed definitions-only); planb4_g1_laur_extract (planb4_g1_laur_go, planb4_g1_laur_sub); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); stdlib QArith, Arith.PeanoNat, List.

    References.  planb4_g1_laur_extract.v:73-80 (the stepper definition); planb4_g1_laur_extract.v:55-68 (the tail update); piu_zz_tau_segaddsplit.v:21 (the Z-product addsplit this equation mirrors); probe_glue_laur.v (verified prototype of the same equation).

    Constructivity.  One structural Fixpoint and one induction over the definitional stepper equation; list equality carried by zzId; no axioms, no admits; expected Print Assumptions output: Closed.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_glue_laur.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.
Require Import zzm1_gauss.
Require Import zzm2_qpoly.
Require Import planb4_g1_laur_extract.
Require Import planb4_calib_chain_glue_qred.

Open Scope Q_scope.

(* Remainder state after k steps of the Laurent stepper: the quotient
   coefficient is recomputed from the current state head at every step,
   exactly as in laur_go. *)
Fixpoint pb4cwin_rem (den : list Q) (d0 : Q) (k : nat) (rem : list Q)
  : list Q :=
  match k with
  | O => rem
  | S k' =>
      pb4cwin_rem den d0 k'
        (planb4_g1_laur_sub (Qred (hd 0%Q rem / d0)) (tl rem) (tl den))
  end.

(* Fuel-split composition: the readout over k1+k2 steps is the k1
   prefix plus the k2 readout from the k1 remainder state. *)
Lemma pb4cwin_laur_go_split :
  forall (k1 k2 : nat) (den : list Q) (d0 : Q) (rem : list Q),
    zzId (planb4_g1_laur_go den d0 (k1 + k2)%nat rem)
         (planb4_g1_laur_go den d0 k1 rem
          ++ planb4_g1_laur_go den d0 k2
               (pb4cwin_rem den d0 k1 rem)).
Proof.
  induction k1 as [| k1 IH]; intros k2 den d0 rem.
  - apply zzIdR.
  - cbn [Nat.add planb4_g1_laur_go app].
    rewrite (pb4cwin_zzId_eq (IH k2 den d0
      (planb4_g1_laur_sub (Qred (hd 0%Q rem / d0)) (tl rem) (tl den)))).
    apply zzIdR.
Qed.

Print Assumptions pb4cwin_laur_go_split.
