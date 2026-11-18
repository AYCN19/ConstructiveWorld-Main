(* sl12_w3_sl1_certs.v - the two SL1 conditional-chain premise
   certificates: K = 121 frozen-domain instances and forall-n reduction bodies with named tail premises.
   Ticket: SL12 ticket SL1 supply line (T3 certificate delivery, wave
   three; GD single number external per provenance).
   Mission: supply the two open premises of the in-tree conditional
   chain theorem at the machine-verified freeze point and reduce their
   forall-n forms to named tail premises: the lcm band at B = 65 and
   the Phi-window band at c = 34/25 from N0 = 15 (bounded certificates
   plus reduction bodies; the Phi tail lives on the prime window
   product (3n/2, 2n] via the window-inclusion lemma).
   Statement inventory: sl12_w3_QleT'_of_Zle; sl12_w3_win_gate;
   sl12_w3_winprodf; sl12_w3_winprodf_le_zzprodf; sl12_w3_winprodf_le_Phi;
   the lcm65 and phi bounded faces with anchors at K = 121;
   sl12_w3_lcm_face_split; sl12_w3_phi_face_reduced; the pairing pins.
   NOT claimed: neither forall-n premise certificate is discharged;
   the tail premises remain the registered heavy debts (margin account
   in the external receipt); the pins only register assembly margins.
   Dependencies: S02_CauchyComplete; piu_zz_padic_clearing;
   planb4_g1_witness; sl1_phase_faces; sl1_phi_divides_L;
   sl1_w2_extended_anchors; sl12_w3_zz2020_transcript.
   References: slot statement draft SL12 sections 1.1/1.3; survey
   volume sections 4.1/5.1; the in-tree conditional chain snapshot.
   Constructivity: Set-carried QleT'/QltT faces; zero global
   assumptions, zero proof surrender, zero solver closers; the named
   tail premises are explicit hypotheses; definitions, faces, and
   lemmas are Defined.
   Build: coqc -native-compiler no -q -Q world "" sl12_w3_sl1_certs.v
   (script driver form; output to the sandbox OUT; after the transcript unit).
   Related registrations: consumes the wave-two SL1 world closure and
   the transcript unit; the Phi reduction feeds the SL2-b supply line. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
Require Import S02_CauchyComplete.
Require Import piu_zz_padic_clearing.
Require Import planb4_g1_witness.
Require Import sl1_phase_faces.
Require Import sl1_phi_divides_L.
Require Import sl1_w2_extended_anchors.
Require Import sl12_w3_zz2020_transcript.

Import ListNotations.

(* ==== Section 1: the Z-to-Q monotone bridge ==== *)

Lemma sl12_w3_QleT'_of_Zle : forall a b : Z, (a <= b)%Z ->
  S02_CauchyComplete.QleT' (inject_Z a) (inject_Z b).
Proof.
  intros a b Hab.
  apply S02_CauchyComplete.Qle_to_QleT'.
  unfold Qle, inject_Z. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. exact Hab.
Defined.

(* ==== Section 2: the prime-window product and its containment in Phi ==== *)

(* The window gate: primes p with 3n < 2p and p <= 2n, i.e. the window
   (3n/2, 2n]. *)
Definition sl12_w3_win_gate (n p : nat) : bool :=
  andb (zz_primeb p)
       (andb (Nat.ltb (3 * n) (2 * p)) (Nat.leb p (2 * n))).

(* The window product over [1, K] as a gated running product (same
   fold shape as zz_prodf). *)
Fixpoint sl12_w3_winprodf (n K : nat) : Z :=
  match K with
  | O => 1%Z
  | S K' =>
      if sl12_w3_win_gate n (S K')
      then sl12_w3_winprodf n K' * Z.of_nat (S K')
      else sl12_w3_winprodf n K'
  end.

(* Containment: the window product never exceeds the ZZ2020 P_n-window
   product, because every window member belongs to P_n for n >= 4
   (the window-inclusion lemma of the transcript unit). *)
Lemma sl12_w3_winprodf_le_zzprodf : forall n K : nat, (4 <= n)%nat ->
  (sl12_w3_winprodf n K <= zz_prodf n K)%Z.
Proof.
  intros n K Hn. induction K as [|K IH].
  - cbn [sl12_w3_winprodf zz_prodf]. lia.
  - cbn [sl12_w3_winprodf zz_prodf].
    destruct (sl12_w3_win_gate n (S K)) eqn:Hw;
      destruct (zz_in_Pn n (S K)) eqn:Hz.
    + assert (Hp0 : (0 <= Z.of_nat (S K))%Z) by lia.
      nia.
    + exfalso.
      apply Bool.andb_true_iff in Hw. destruct Hw as [Hp Hr].
      apply Bool.andb_true_iff in Hr. destruct Hr as [Hwin Hle2].
      apply (proj1 (Nat.ltb_lt (3 * n) (2 * S K))) in Hwin.
      apply (proj1 (Nat.leb_le (S K) (2 * n))) in Hle2.
      pose proof (sl12_w3_window_in_Pn n (S K) Hn Hp Hwin Hle2) as Hin.
      apply BidT_elim in Hin. rewrite Hin in Hz. discriminate.
    + pose proof (zz_prodf_pos n K) as Hpos.
      assert (Hp1 : (1 <= Z.of_nat (S K))%Z) by lia.
      assert (Hstep : (zz_prodf n K * 1 <= zz_prodf n K * Z.of_nat (S K))%Z)
        by nia.
      rewrite Z.mul_1_r in Hstep.
      transitivity (zz_prodf n K); [exact IH | exact Hstep].
    + exact IH.
Defined.

(* The Phi-form instance: planb4_Phi n = zz_Phi n = zz_prodf n (2n). *)
Lemma sl12_w3_winprodf_le_Phi : forall n : nat, (4 <= n)%nat ->
  (sl12_w3_winprodf n (2 * n) <= planb4_Phi n)%Z.
Proof.
  intros n Hn. rewrite sl1_planb4_Phi_eq_zz_Phi. unfold zz_Phi.
  apply sl12_w3_winprodf_le_zzprodf. exact Hn.
Defined.

(* ==== Section 3: the premise certificates at the K = 121 freeze point ==== *)

(* The lcm band at B = 65, bounded form: the unconditional
   machine-verified instance lives over n = 0..120. *)
Definition sl12_w3_lcm65_bounded_face (K : nat) : Set :=
  forall n : nat, (n < K)%nat ->
    S02_CauchyComplete.QleT'
      (inject_Z (Z.abs (planb4_L n)))
      (Qpower ((65 # 1)%Q) (Z.of_nat n)).

Lemma sl12_w3_lcm65_bounded_face_of_anchor : forall K : nat,
  sl1_lcm_head_ok ((65 # 1)%Q) K = true -> sl12_w3_lcm65_bounded_face K.
Proof.
  intros K HK n Hn.
  exact (sl1_lcm_head_transfer ((65 # 1)%Q) K n HK Hn).
Defined.

Example sl12_w3_lcm65_bounded_121 : sl12_w3_lcm65_bounded_face 121.
Proof.
  exact (sl12_w3_lcm65_bounded_face_of_anchor 121 sl1_w2_lcm65_ext_anchor).
Defined.

(* The Phi-window band at c = 34/25 from N0 = 15, bounded form: the
   unconditional machine-verified instance lives over n = 15..120. *)
Definition sl12_w3_phi_bounded_face (K : nat) : Set :=
  forall n : nat, (15 <= n)%nat -> (n < K)%nat ->
    S02_CauchyComplete.QleT'
      (Qpower ((34 # 25)%Q) (Z.of_nat n))
      (inject_Z (planb4_Phi n)).

Lemma sl12_w3_phi_bounded_face_of_anchor : forall K : nat,
  sl1_phi_band_head_ok ((34 # 25)%Q) 15 (K - 15)%nat = true ->
  sl12_w3_phi_bounded_face K.
Proof.
  intros K HK n Hn1 Hn2.
  assert (Hrng : (15 <= n < 15 + (K - 15))%nat).
  { split; [exact Hn1 |]. replace (15 + (K - 15))%nat with K by lia.
    exact Hn2. }
  exact (sl1_phi_band_head_transfer ((34 # 25)%Q) 15 (K - 15) n HK Hrng).
Defined.

Example sl12_w3_phi_bounded_121 : sl12_w3_phi_bounded_face 121.
Proof.
  exact (sl12_w3_phi_bounded_face_of_anchor 121 sl1_w2_phi_ext_anchor).
Defined.

(* ==== Section 4: the forall-n reduction bodies (named tail premises) ==== *)

(* The lcm band split body: the full face follows from the machine
   anchors over n = 0..120 plus the named tail premise over n >= 121.
   The tail premise is stated in the same integer-idiom face form (no
   narrower decidable tail idiom exists without the explicit-error
   psi-band machinery; see the receipt margin account). *)
Theorem sl12_w3_lcm_face_split :
  (forall n : nat, (121 <= n)%nat ->
     S02_CauchyComplete.QleT'
       (inject_Z (Z.abs (planb4_L n)))
       (Qpower ((65 # 1)%Q) (Z.of_nat n))) ->
  sl1_lcm_pow_bound_face ((65 # 1)%Q).
Proof.
  intros Htail n.
  destruct (le_lt_dec 121 n) as [Hge | Hlt].
  - exact (Htail n Hge).
  - exact (sl1_lcm_head_transfer ((65 # 1)%Q) 121 n
             sl1_w2_lcm65_ext_anchor Hlt).
Defined.

(* The Phi-window reduction body: the full face follows from the
   machine anchors over n = 15..120 plus the named tail premise in the
   NARROWED window-product form - a theta-window lower bound over the
   prime window (3n/2, 2n], which the window-inclusion lemma lifts to
   the full P_n product.  This narrows the SL1-b supply target from
   the Phi-window band to the literature-certifiable window bound. *)
Theorem sl12_w3_phi_face_reduced :
  (forall n : nat, (121 <= n)%nat ->
     S02_CauchyComplete.QleT'
       (Qpower ((34 # 25)%Q) (Z.of_nat n))
       (inject_Z (sl12_w3_winprodf n (2 * n)))) ->
  sl1_phi_pow_lower_from sl1_N0 ((34 # 25)%Q).
Proof.
  intros Htail n Hn.
  destruct (le_lt_dec 121 n) as [Hge | Hlt].
  - apply S02_CauchyComplete.qleT'_trans
      with (inject_Z (sl12_w3_winprodf n (2 * n))).
    + exact (Htail n Hge).
    + apply sl12_w3_QleT'_of_Zle. apply sl12_w3_winprodf_le_Phi. lia.
  - exact (sl1_phi_band_head_transfer ((34 # 25)%Q) 15 106 n
             sl1_w2_phi_ext_anchor (conj Hn Hlt)).
Defined.

(* ==== Section 5: the pairing pins ==== *)

(* Why the two premises at B = 65 and c = 34/25 assemble to the 48
   instance of the conditional chain: the pairing base 65/(34/25) =
   1625/34 is positive and does not exceed 48 (the chain consumes
   these two margins in its tail transfer). *)
Example sl12_w3_pairing_pos :
  S02_CauchyComplete.QltT 0 ((65 # 1)%Q / (34 # 25)%Q).
Proof. vm_compute. reflexivity. Qed.

Example sl12_w3_pairing_le_48 :
  S02_CauchyComplete.QleT' ((65 # 1)%Q / (34 # 25)%Q) ((48 # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions sl12_w3_QleT'_of_Zle.
Print Assumptions sl12_w3_winprodf_le_zzprodf.
Print Assumptions sl12_w3_winprodf_le_Phi.
Print Assumptions sl12_w3_lcm65_bounded_face_of_anchor.
Print Assumptions sl12_w3_lcm65_bounded_121.
Print Assumptions sl12_w3_phi_bounded_face_of_anchor.
Print Assumptions sl12_w3_phi_bounded_121.
Print Assumptions sl12_w3_lcm_face_split.
Print Assumptions sl12_w3_phi_face_reduced.
Print Assumptions sl12_w3_pairing_pos.
Print Assumptions sl12_w3_pairing_le_48.
