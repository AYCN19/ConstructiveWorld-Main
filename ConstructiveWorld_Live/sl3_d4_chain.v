(* ================================================================== *)
(* Ticket: D-SL3-4 - the N2c chain assembly 37 to 17 (universal n).    *)
(* Statement list, proven: sl3_d4_qpow2_form; sl3_d4_qpow2_le_mono_   *)
(*   natT; sl3_d4_allj_uplift; sl3_d4_face_from_qleT_face;             *)
(*   sl3_d4_crude37_qpower_face; sl3_d4_n2c_sharp_via_gf_qleT (MAIN -  *)
(*   the universal sharp face under the explicit GF premise);          *)
(*   sl3_d4_sharp_b2_face_via_gf_qleT; sl3_d4_fallback_from_sharp.     *)
(* Statement list, born Set contract faces: sl3_d4_gf_allj_qleT_face;  *)
(*   sl3_d4_gf_allj_face; sl3_d4_fallback_19n_face (retained tier).    *)
(* Mission: assemble the universal N2c chain - GF entry over the b0    *)
(*   bridge, form transitivity onto the Qpower form, sharp at 17, fallback at 19. *)
(* Dependencies: Stdlib QArith ZArith Arith Lia Qpower List; units     *)
(*   S02_CauchyComplete, piu_zz_kernel_sum, piu_zz_sigma_decay,        *)
(*   piu_zz_n2c_sigma_assembly.                                        *)
(* References: tree faces piu_zz_n2c_crude_size_sharp and              *)
(*   piu_zz_n2b_A_allj_le17_face; the b0 bridge; the 37n relay; the bite lemma. *)
(* Source routing: tree statement faces consumed verbatim (zero tree   *)
(*   write); the GF premise shape follows the slot-statement draft     *)
(*   section 1.3 with one type correction (noted at the face); paths   *)
(*   live in the external provenance ledger of the delivery receipt.   *)
(* Build: coqc -native-compiler no -q -Q <vo-closure-root> "" -o       *)
(*   <sandbox-out>/sl3_d4_chain.vo sl3_d4_chain.v (see the ledger).    *)
(* Related registrations: the GF carrier is delivered with n = 1, 2    *)
(*   machine anchors; the universal pole domination and identity stay  *)
(*   open there, so the sharp face lands here premise-carried; the     *)
(*   2^(19n) fallback tier stays retained (KB41b item 7).              *)
(* Constructivity: all objects Set-carried; the three contract faces   *)
(*   are born and honestly unproven; all eight proofs are real         *)
(*   derivation chains, solver only in bookkeeping sides, Defined.     *)
(* ================================================================== *)

From Stdlib Require Import QArith ZArith Arith Lia List.
From Stdlib Require Import Qpower.
From Stdlib Require Import QArith.Qabs.
Require Import S02_CauchyComplete.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_sigma_decay.
Require Import piu_zz_n2c_sigma_assembly.

(* ================================================================== *)
(* Section 1. Form bridges between the two Q statement forms.         *)
(* The tree relay lemma closes in the literal-Q form (2^(s*n) # 1);   *)
(* the sharp face is stated in the Qpower form. The bridge below is   *)
(* the symbolic-n version of the tree n = 1 form witness.             *)
(* ================================================================== *)

(* The dyadic Qpower form equals the literal-Q form for every nat     *)
(* exponent: (inject_Z 2)^(Z.of_nat m) == (Z.of_nat (2 ^ m) # 1).     *)
Lemma sl3_d4_qpow2_form :
  forall m : nat,
    ((Z.of_nat (2 ^ m)) # 1 == Qpower (inject_Z 2) (Z.of_nat m))%Q.
Proof.
  intros m.
  rewrite Nat2Z.inj_pow.
  apply Zpower_Qpower.
  apply Nat2Z.is_nonneg.
Defined.

(* Dyadic monotonicity in the QleT' dialect: a <= b over nat gives    *)
(* 2^a <= 2^b over Q. Engine: split b = a + d, expand the power over  *)
(* Q (the base is nonzero), then 1 <= 2^d and 0 <= 2^a.               *)
Lemma sl3_d4_qpow2_le_mono_natT :
  forall a b : nat, (a <= b)%nat ->
    S02_CauchyComplete.QleT' (Qpower (inject_Z 2) (Z.of_nat a))
      (Qpower (inject_Z 2) (Z.of_nat b)).
Proof.
  intros a b Hab.
  apply S02_CauchyComplete.Qle_to_QleT'.
  replace b with (a + (b - a))%nat by lia.
  rewrite Nat2Z.inj_add.
  assert (H2nz : ~ (inject_Z 2 == 0)%Q).
  { intros Hc. unfold Qeq, inject_Z in Hc. cbn in Hc. discriminate. }
  rewrite (Qpower_plus (inject_Z 2) (Z.of_nat a) (Z.of_nat (b - a)) H2nz).
  assert (Hge : (1 <= Qpower (inject_Z 2) (Z.of_nat (b - a)))%Q).
  { apply (Qpower_1_le (inject_Z 2) (Z.of_nat (b - a))).
    - unfold Qle, inject_Z. cbn. lia.
    - apply Nat2Z.is_nonneg. }
  assert (Hpos : (0 <= Qpower (inject_Z 2) (Z.of_nat a))%Q).
  { apply (Qpower_0_le (inject_Z 2) (Z.of_nat a)).
    unfold Qle, inject_Z. cbn. lia. }
  pose proof (Qmult_le_compat_r 1 (Qpower (inject_Z 2) (Z.of_nat (b - a)))
              (Qpower (inject_Z 2) (Z.of_nat a)) Hge Hpos) as Hm.
  rewrite Qmult_1_l in Hm.
  rewrite (Qmult_comm (Qpower (inject_Z 2) (Z.of_nat (b - a)))
                      (Qpower (inject_Z 2) (Z.of_nat a))) in Hm.
  exact Hm.
Defined.

(* ================================================================== *)
(* Section 2. The GF supply interface faces (born contract faces).    *)
(* These are the registered supply-side premise shapes for the chain  *)
(* assembly; they are honestly unproven here and their discharge is   *)
(* the GF decomposition supply obligation. At s = 17 the second face  *)
(* is definitionally the tree sharp face statement body.              *)
(* Type correction against the slot-statement draft section 1.3: the  *)
(* draft wrote inject_Z (Z.abs (piu_zz_Aj n j)), but the tree Aj      *)
(* carrier is Q-valued, so the registered form below uses Qabs        *)
(* directly; the Qpower side is unchanged.                            *)
(* ================================================================== *)

Definition sl3_d4_gf_allj_qleT_face (s : nat) : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    piu_zz_kernel_sum.qleT (Qabs (piu_zz_Aj n j))
      ((Z.of_nat (2 ^ (s * n))) # 1)%Q.

Definition sl3_d4_gf_allj_face (s : nat) : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (s * n))).

(* ================================================================== *)
(* Section 3. The chain assemblies.                                   *)
(* ================================================================== *)

(* The upward envelope lift: a supply face at s discharges the face   *)
(* at s' >= s (the dyadic carrier is monotone over Q).                *)
Theorem sl3_d4_allj_uplift :
  forall s s' : nat, (s <= s')%nat ->
    sl3_d4_gf_allj_face s -> sl3_d4_gf_allj_face s'.
Proof.
  intros s s' Hss Hface.
  unfold sl3_d4_gf_allj_face in *.
  intros n j Hj.
  specialize (Hface n j Hj).
  apply (S02_CauchyComplete.qleT'_trans _
          (Qpower (inject_Z 2) (Z.of_nat (s * n)))).
  - exact Hface.
  - apply sl3_d4_qpow2_le_mono_natT.
    apply Nat.mul_le_mono_r.
    exact Hss.
Defined.

(* The b0 bridge entry: a qleT-dialect supply face lifts into the     *)
(* QleT' Qpower-dialect face over the form bridge (transitivity       *)
(* assembly over piu_zz_n2b_qleT_to_QleT' and sl3_d4_qpow2_form).     *)
Theorem sl3_d4_face_from_qleT_face :
  forall s : nat, sl3_d4_gf_allj_qleT_face s -> sl3_d4_gf_allj_face s.
Proof.
  intros s Hgf.
  unfold sl3_d4_gf_allj_face.
  intros n j Hj.
  apply (S02_CauchyComplete.qleT'_trans _
          ((Z.of_nat (2 ^ (s * n))) # 1)%Q).
  - apply piu_zz_n2b_qleT_to_QleT'.
    exact (Hgf n j Hj).
  - apply S02_CauchyComplete.qeq_leT'.
    apply sl3_d4_qpow2_form.
Defined.

(* The proven chain leg at s = 37: the tree 37n relay lemma, lifted   *)
(* through the same b0 and form bridges, in the Qpower statement      *)
(* form. This face is unconditionally proven.                         *)
Theorem sl3_d4_crude37_qpower_face :
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (37 * n))).
Proof.
  intros n j Hj.
  apply (S02_CauchyComplete.qleT'_trans _
          ((Z.of_nat (2 ^ (37 * n))) # 1)%Q).
  - apply piu_zz_n2c_crude_relay_37.
    exact Hj.
  - apply S02_CauchyComplete.qeq_leT'.
    apply sl3_d4_qpow2_form.
Defined.

(* Main statement: the universal sharp face assembly. The premise is  *)
(* the explicit GF supply slot at s = 17 (born contract face, the     *)
(* registered supply obligation); the conclusion is the tree sharp    *)
(* face Definition consumed verbatim. Proof shape: b0 bridge, then    *)
(* the form transitivity onto the Qpower form.                        *)
Theorem sl3_d4_n2c_sharp_via_gf_qleT :
  sl3_d4_gf_allj_qleT_face 17 -> piu_zz_n2c_crude_size_sharp.
Proof.
  intros Hgf.
  unfold piu_zz_n2c_crude_size_sharp.
  intros n j Hj.
  apply (S02_CauchyComplete.qleT'_trans _
          ((Z.of_nat (2 ^ (17 * n))) # 1)%Q).
  - apply piu_zz_n2b_qleT_to_QleT'.
    exact (Hgf n j Hj).
  - apply S02_CauchyComplete.qeq_leT'.
    apply sl3_d4_qpow2_form.
Defined.

(* The b2 consumption face form of the assembly: the tree records the *)
(* sharp face and the b2 face as definitionally equal (the interface  *)
(* bite lemma closes by reflexivity), so this is a bookkeeping        *)
(* conversion, declared as such.                                      *)
Theorem sl3_d4_sharp_b2_face_via_gf_qleT :
  sl3_d4_gf_allj_qleT_face 17 -> piu_zz_n2b_A_allj_le17_face.
Proof.
  intros Hgf.
  exact (sl3_d4_n2c_sharp_via_gf_qleT Hgf).
Defined.

(* ================================================================== *)
(* Section 4. The retained fallback tier at s = 19.                   *)
(* The tree assembly unit retains the 2^(19n) fallback margin tier    *)
(* (the margin-tier registration KB41b item 7, downstream notes of    *)
(* the tree unit) until the universal GF supply lands. The face is    *)
(* born; the theorem below attaches the tier to the chain: a proven   *)
(* sharp face at s = 17 discharges the fallback face at s = 19.       *)
(* ================================================================== *)

Definition sl3_d4_fallback_19n_face : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (19 * n))).

Theorem sl3_d4_fallback_from_sharp :
  piu_zz_n2c_crude_size_sharp -> sl3_d4_fallback_19n_face.
Proof.
  intros Hsharp.
  unfold sl3_d4_fallback_19n_face.
  intros n j Hj.
  specialize (Hsharp n j Hj).
  apply (S02_CauchyComplete.qleT'_trans _
          (Qpower (inject_Z 2) (Z.of_nat (17 * n)))).
  - exact Hsharp.
  - apply sl3_d4_qpow2_le_mono_natT.
    apply Nat.mul_le_mono_r.
    lia.
Defined.

(* ================================================================== *)
(* Section 5. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions sl3_d4_qpow2_form.
Print Assumptions sl3_d4_qpow2_le_mono_natT.
Print Assumptions sl3_d4_allj_uplift.
Print Assumptions sl3_d4_face_from_qleT_face.
Print Assumptions sl3_d4_crude37_qpower_face.
Print Assumptions sl3_d4_n2c_sharp_via_gf_qleT.
Print Assumptions sl3_d4_sharp_b2_face_via_gf_qleT.
Print Assumptions sl3_d4_fallback_from_sharp.
