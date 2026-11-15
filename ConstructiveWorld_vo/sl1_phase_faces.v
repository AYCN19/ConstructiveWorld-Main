(* sl1_phase_faces.v - SL12 slot-draft section-1 statement faces for
   the SL1 supply line (lcm band, Phi-window band, L_n band).
   Ticket: SL12 ticket SL1 (psi band + Phi window construction seat).
   Mission: transcribe the three draft faces (its sections 1.1/1.2) as
   Set-carried QleT' faces over planb4_g1_witness; add the honest
   head-offset supply faces and boolean head-check faces for machine
   anchors; register the falsification certificate forcing the offset
   form (the draft Phi face is machine-false at n = 5 for c = 34/25:
   the P_n window is empty there, planb4_Phi 5 = 1).
   Inventory: 9 Definitions, 3 transfer lemmas (Defined), 1 anchor.
   Dependencies: S02_CauchyComplete (QleT'/QltT bridges);
   planb4_g1_witness (planb4_L/planb4_Phi/planb4_LZn); stdlib QArith,
   ZArith, Qpower, List, Lia.
   References: slot statement draft SL12 sections 1.1-1.2 (faces
   verbatim modulo the sl1_ namespace); survey volume section 4.1
   (budget line ln b <= 3.871322, b = 48 tight integer instance);
   ground-truth table tools/sl1_ground_truth.py (sl1_N0 = 15).
   NOT claimed: no band certificate is supplied; the two forall-n
   band supplies stay open debts (seat appendix).
   Constructivity: all faces Set-carried; zero global assumptions,
   zero proof surrender, zero solver closers; anchors are Qed-kept
   extraction-erased pins per the upstream registration.
   Build: coqc -native-compiler no -q -Q world "" -Q out_sl1 ""
   sl1_phase_faces.v (E952 script form, first of the SL1 family). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
Require Import S02_CauchyComplete.
Require Import planb4_g1_witness.

(* ==== Section 1: the three draft faces (draft sections 1.1/1.2) ==== *)

(* SL1 main face: |LZn n| <= b^n for all n, with b an explicit Q base.
   Budget line: ln b <= 4 - 0.6452756 + 0.516622 = 3.871322, so b = 48
   is the tight integer instance. *)
Definition sl1_lzn_pow_bound_face (b : Q) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_LZn n)))
      (Qpower b (Z.of_nat n)).

(* SL1 upper-band face: |lcm(1..4n)| <= b^n for all n (the psi(4n)
   Chebyshev-band certificate in integer idiom). Budget-compatible
   band: ln b <= 4 * (1 + eps_psi) with 4*eps_psi <= 0.516622 -
   delta_Phi on the shared decay account. *)
Definition sl1_lcm_pow_bound_face (b : Q) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_L n)))
      (Qpower b (Z.of_nat n)).

(* SL1 lower-band face (draft form): c^n <= Phi n for all n. Honesty
   note: this face is machine-false for every c > 1 (the P_n window is
   empty at n = 1, 2, 3, 5 with Phi = 1; the falsification anchor in
   Section 4 pins the n = 5 counterexample at the budget-compatible
   instance c = 34/25). The face is registered verbatim as the draft
   requires; the supply face is the offset form in Section 2. *)
Definition sl1_phi_pow_lower_face (c : Q) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT'
      (Qpower c (Z.of_nat n))
      (inject_Z (planb4_Phi n)).

(* ==== Section 2: honest head-offset supply faces ==== *)

(* Supply form of the Phi-window band: c^n <= Phi n for n >= N, the
   head range n < N being discharged by separate machine anchors. The
   offset is forced by the empty-window indices; for the
   budget-compatible instance c = 34/25 the tight offset is N = 15
   (violations exactly at n in {1, 2, 3, 5, 13, 14}, ground-truth
   table). *)
Definition sl1_phi_pow_lower_from (N : nat) (c : Q) : Set :=
  forall n : nat, (N <= n)%nat ->
    S02_CauchyComplete.QleT'
      (Qpower c (Z.of_nat n))
      (inject_Z (planb4_Phi n)).

(* Supply form of the L_n band on the same split: the tail range is
   discharged by the assembly theorem (conditional on the two band
   certificates), the head range by the machine anchors. *)
Definition sl1_lzn_pow_bound_from (N : nat) (b : Q) : Set :=
  forall n : nat, (N <= n)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_LZn n)))
      (Qpower b (Z.of_nat n)).

(* The pinned head offset for c = 34/25. *)
Definition sl1_N0 : nat := 15.

(* ==== Section 3: boolean head-check faces (machine-anchor targets) == *)

(* forallb faces over an initial segment; each closes by vm_compute in
   the anchors unit and lifts through the transfer lemmas of Section 4. *)
Definition sl1_lcm_head_ok (b : Q) (K : nat) : bool :=
  forallb (fun n => S02_CauchyComplete.Qle_bool
                     (inject_Z (Z.abs (planb4_L n)))
                     (Qpower b (Z.of_nat n))) (seq 0 K).

Definition sl1_lzn_head_ok (b : Q) (K : nat) : bool :=
  forallb (fun n => S02_CauchyComplete.Qle_bool
                     (inject_Z (Z.abs (planb4_LZn n)))
                     (Qpower b (Z.of_nat n))) (seq 0 K).

(* The band window [N, N + len) of the Phi face. *)
Definition sl1_phi_band_head_ok (c : Q) (N len : nat) : bool :=
  forallb (fun n => S02_CauchyComplete.Qle_bool
                     (Qpower c (Z.of_nat n))
                     (inject_Z (planb4_Phi n))) (seq N len).

(* ==== Section 4: transfer lemmas (boolean face -> QleT' face) ==== *)

Lemma sl1_lcm_head_transfer :
  forall (b : Q) (K n : nat),
    sl1_lcm_head_ok b K = true -> (n < K)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_L n))) (Qpower b (Z.of_nat n)).
Proof.
  intros b K n HK Hn.
  unfold sl1_lcm_head_ok in HK.
  rewrite forallb_forall in HK.
  assert (Hin : In n (seq 0 K)) by (apply in_seq; lia).
  specialize (HK n Hin).
  unfold S02_CauchyComplete.QleT'.
  rewrite HK. constructor.
Defined.

Lemma sl1_lzn_head_transfer :
  forall (b : Q) (K n : nat),
    sl1_lzn_head_ok b K = true -> (n < K)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_LZn n))) (Qpower b (Z.of_nat n)).
Proof.
  intros b K n HK Hn.
  unfold sl1_lzn_head_ok in HK.
  rewrite forallb_forall in HK.
  assert (Hin : In n (seq 0 K)) by (apply in_seq; lia).
  specialize (HK n Hin).
  unfold S02_CauchyComplete.QleT'.
  rewrite HK. constructor.
Defined.

Lemma sl1_phi_band_head_transfer :
  forall (c : Q) (N len n : nat),
    sl1_phi_band_head_ok c N len = true -> (N <= n < N + len)%nat ->
    S02_CauchyComplete.QleT'
      (Qpower c (Z.of_nat n)) (inject_Z (planb4_Phi n)).
Proof.
  intros c N len n HK Hn.
  unfold sl1_phi_band_head_ok in HK.
  rewrite forallb_forall in HK.
  assert (Hin : In n (seq N len)) by (apply in_seq; lia).
  specialize (HK n Hin).
  unfold S02_CauchyComplete.QleT'.
  rewrite HK. constructor.
Defined.

(* ==== Section 5: the falsification certificate (draft face) ==== *)

(* The draft Phi face at the budget-compatible instance c = 34/25 is
   machine-false at n = 5: planb4_Phi 5 = 1 < (34/25)^5. This pins the
   honest boundary of the draft face as stated and justifies the head
   offset form of Section 2. *)
Example sl1_phi_face_falsified_n5 :
  S02_CauchyComplete.QltT (inject_Z (planb4_Phi 5))
    (Qpower ((34 # 25)%Q) 5).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions sl1_lcm_head_transfer.
Print Assumptions sl1_lzn_head_transfer.
Print Assumptions sl1_phi_band_head_transfer.
Print Assumptions sl1_phi_face_falsified_n5.
