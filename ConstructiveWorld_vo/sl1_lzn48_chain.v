(* sl1_lzn48_chain.v - the conditional chain to the tight L_n instance.
   Ticket: SL12 ticket SL1 (psi band + Phi window construction seat).
   Mission: assemble the SL1 conditional core at the budget-compatible
   integer pairing: GIVEN the lcm band at B = 65 (psi-band face; the
   forall-n supply is the registered heavy debt), the Phi-window band
   at C = 34/25 from the pinned offset sl1_N0 = 15 (second heavy debt),
   and the machine anchors, the draft face sl1_lzn_pow_bound_face at
   b = 48 holds for ALL n. The tail n >= 15 rides the assembly theorem
   at base 1625/34 plus the monotonicity transfer to 48; the head
   n < 15 rides the machine anchor through the transfer lemma. No debt
   is discharged silently.
   Inventory: 1 Theorem (sl1_lzn48_conditional, Defined).
   Dependencies: S02_CauchyComplete; planb4_g1_witness; sl1_phase_faces;
   sl1_lzn_assembly; sl1_head_anchors; stdlib QArith, ZArith, Qpower,
   List, Lia.
   References: slot statement draft SL12 sections 1.1/1.3 (main face
   and instance pairing); survey volume sections 4.1/5 (ln 48 <=
   3.871322 on the shared 0.516622 nat/n account).
   NOT claimed: the two band certificates remain the open debts.
   Constructivity: Set-carried; zero global assumptions; closes by
   explicit combinator chains, Defined (informative content).
   Build: coqc -native-compiler no -q -Q world "" -Q out_sl1 ""
   sl1_lzn48_chain.v (E952 script form; last of the SL1 family). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
Require Import S02_CauchyComplete.
Require Import planb4_g1_witness.
Require Import sl1_phase_faces.
Require Import sl1_lzn_assembly.
Require Import sl1_head_anchors.

(* ==== Section 1: the conditional chain theorem ==== *)

Theorem sl1_lzn48_conditional :
  sl1_lcm_pow_bound_face ((65 # 1)%Q) ->
  S02_CauchyComplete.QltT 0 ((34 # 25)%Q) ->
  sl1_phi_pow_lower_from sl1_N0 ((34 # 25)%Q) ->
  sl1_lzn_pow_bound_face ((48 # 1)%Q).
Proof.
  intros Hcm Hc0 Hph n.
  destruct (le_lt_dec sl1_N0 n) as [Hge | Hlt].
  - apply S02_CauchyComplete.qleT'_trans
      with (Qpower ((65 # 1)%Q / (34 # 25)%Q) (Z.of_nat n)).
    + apply (sl1_lzn_from_bands (65 # 1)%Q (34 # 25)%Q sl1_N0
               Hcm Hc0 Hph). exact Hge.
    + apply sl1_qpower_le_mono.
      * exact sl1_anchor_base_pos.
      * exact sl1_anchor_base_le48.
  - apply (sl1_lzn_head_transfer ((48 # 1)%Q) sl1_N0 n).
    + exact sl1_lzn48_head_anchor.
    + exact Hlt.
Defined.

Print Assumptions sl1_lzn48_conditional.
