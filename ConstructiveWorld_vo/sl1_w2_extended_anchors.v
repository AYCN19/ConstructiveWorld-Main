(* sl1_w2_extended_anchors.v - extended head-band anchors for the SL1
   tight L_n instance and the bounded table-domain supply faces.
   Mission: extend the machine-verified head ranges of the SL1 family
   beyond the registered anchors: the direct boolean check of
   |LZn n| <= 48^n over the full shared table domain n = 0..40 (the
   registered anchor covers only n = 0..14), the three band faces
   extended to the horizon K = 121 (lcm and L_n bands n = 0..120, the
   Phi-window band n = 15..120), and the bounded supply face in the
   QleT' dialect derived from each boolean anchor through the
   registered transfer lemma. The horizon is budget-measured (the
   K = 601 probe exceeded the per-anchor compute budget; frozen at the
   measured green point).
   Dependencies: S02_CauchyComplete; planb4_g1_witness; sl1_phase_faces;
   stdlib QArith, ZArith, Qpower, List.
   References: slot statement draft SL12 sections 1.1/1.3 (the forall-n
   consumption face this unit does NOT discharge); survey volume
   sections 4.1/5; ground-truth table tools/sl1_ground_truth.py
   (Python-level zero violations through n = 600; the Rocq-side
   machine horizon is 120 here).
   NOT claimed: no forall-n band certificate is supplied; the two
   heavy premises of the conditional chain theorem remain open debts.
   Constructivity: boolean pins over transparent informative
   definitions (Qed kept per the upstream anchor registration); the
   bounded face and its bridge lemma are Defined; zero global
   assumptions, zero proof surrender, zero solver closers.
   Build: coqc -native-compiler no -q -Q world ""
   sl1_w2_extended_anchors.v (E952 script form; after sl1_phase_faces). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
Require Import S02_CauchyComplete.
Require Import planb4_g1_witness.
Require Import sl1_phase_faces.

(* ==== Section 1: the table-domain anchor of the tight instance ==== *)

(* The direct boolean check of the tight L_n instance over the full
   shared table domain n = 0..40. The registered anchor covers only
   n = 0..14; this extends the direct machine evidence across the
   15..40 window without any premise. *)
Example sl1_w2_lzn48_table_anchor :
  sl1_lzn_head_ok ((48 # 1)%Q) 41 = true.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 2: the bounded supply face in the QleT' dialect ==== *)

(* The table-domain supply form of the tight instance: |LZn n| <= 48^n
   for every n below the horizon K, unconditionally. Set-carried; the
   head offset form mirrors sl1_lzn_pow_bound_from with the tail range
   replaced by the finite table domain. *)
Definition sl1_w2_lzn48_bounded_face (K : nat) : Set :=
  forall n : nat, (n < K)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_LZn n)))
      (Qpower ((48 # 1)%Q) (Z.of_nat n)).

(* The bridge from a boolean anchor to the bounded face: the transfer
   lemma of the registered faces unit applied at the fixed base 48. *)
Lemma sl1_w2_lzn48_bounded_face_of_anchor :
  forall K : nat,
    sl1_lzn_head_ok ((48 # 1)%Q) K = true ->
    sl1_w2_lzn48_bounded_face K.
Proof.
  intros K HK n Hn.
  exact (sl1_lzn_head_transfer ((48 # 1)%Q) K n HK Hn).
Defined.

(* The unconditional table-domain face. *)
Example sl1_w2_lzn48_table_face : sl1_w2_lzn48_bounded_face 41.
Proof. exact (sl1_w2_lzn48_bounded_face_of_anchor 41 sl1_w2_lzn48_table_anchor). Defined.

(* ==== Section 3: the extended-horizon band anchors (K = 121) ==== *)

(* The lcm band at B = 65 over n = 0..120. *)
Example sl1_w2_lcm65_ext_anchor :
  sl1_lcm_head_ok ((65 # 1)%Q) 121 = true.
Proof. vm_compute. reflexivity. Qed.

(* The Phi-window band at c = 34/25 over n = 15..120 (seq 15 106). *)
Example sl1_w2_phi_ext_anchor :
  sl1_phi_band_head_ok ((34 # 25)%Q) 15 106 = true.
Proof. vm_compute. reflexivity. Qed.

(* The tight L_n instance over n = 0..120: the direct machine horizon
   of the tight instance moves from 40 to 120. *)
Example sl1_w2_lzn48_ext_anchor :
  sl1_lzn_head_ok ((48 # 1)%Q) 121 = true.
Proof. vm_compute. reflexivity. Qed.

(* The unconditional extended-horizon face. *)
Example sl1_w2_lzn48_ext_face : sl1_w2_lzn48_bounded_face 121.
Proof. exact (sl1_w2_lzn48_bounded_face_of_anchor 121 sl1_w2_lzn48_ext_anchor). Defined.

Print Assumptions sl1_w2_lzn48_table_anchor.
Print Assumptions sl1_w2_lzn48_table_face.
Print Assumptions sl1_w2_lzn48_bounded_face_of_anchor.
Print Assumptions sl1_w2_lcm65_ext_anchor.
Print Assumptions sl1_w2_phi_ext_anchor.
Print Assumptions sl1_w2_lzn48_ext_anchor.
Print Assumptions sl1_w2_lzn48_ext_face.
