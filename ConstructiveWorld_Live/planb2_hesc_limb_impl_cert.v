(* ConstructiveWorld-Main - planb2 numeric-certainty companion: the exact window and witness spot faces proven by vm_compute. *)

(** * planb2_hesc_limb_impl_cert: numeric spot faces for the Hesc limb.

    Mission.  The vm_compute-verified numeric faces split out of
      planb2_hesc_limb_impl: the q = 1 window face (2*1*(3/20)^1 =
      3/10 <= 1, exact) and the witness landing spots at the first two
      heights (piu_zz_ec_nescD 1 = 1, piu_zz_ec_nescD 2 = 1).

    Dependencies.  planb2_hesc_limb_impl of this development; stdlib
      QArith.QArith, QArith.Qabs.

    References.  planb2_hesc_limb_impl.v (the limb chain these spot
      faces anchor).

    Constructivity.  All proofs close by vm_compute; admission-free
      and postulate-free throughout.

    Build.  coqc -native-compiler no -q -Q . ""
      planb2_hesc_limb_impl_cert.v (Rocq 9.3.0, single lane under
      cpu_guard_v3). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
Require Import S02_CauchyComplete.
Require Import piu_zz_ec_escwin_nescD.
Require Import planb2_hesc_limb_impl.

(* the window face at q = 1 computes EXACT: 2*1*(3/20)^1 = 3/10 <= 1. *)
Example planb2_q1_window_face :
  planb2_theta_window_face (planb2_theta_at 1).
Proof.
  unfold planb2_theta_window_face, planb2_theta_at.
  apply S02_CauchyComplete.Qle_to_QleT'.
  vm_compute. intro Hc. discriminate Hc.
Qed.

(* the witness landing spot at the first two heights. *)
Example planb2_witness_spots :
  piu_zz_ec_nescD 1 = 1%nat /\ piu_zz_ec_nescD 2 = 1%nat.
Proof. split; vm_compute; reflexivity. Qed.

(* assumption audit *)
Print Assumptions planb2_q1_window_face.
Print Assumptions planb2_witness_spots.
