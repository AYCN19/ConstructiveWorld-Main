(* ================================================================== *)
(* Ticket: D-SL3-3 remainder - the identity small-sample tier (the     *)
(*   machine anchors for the exact pole-extraction weld, extended      *)
(*   from the landed n = 1, 2 tier to n = 3, 4 all-j and n = 5 head    *)
(*   samples, with an n = 2 cross-check against the landed tier).      *)
(* Statement list: sl3_w2_ident_n2_x0, sl3_w2_ident_n2_x3 (cross-check *)
(*   against the landed anchor tier); sl3_w2_ident_n3_j0 ..            *)
(*   sl3_w2_ident_n3_j9 (all j at n = 3); sl3_w2_ident_n4_j0 ..        *)
(*   sl3_w2_ident_n4_j12 (all j at n = 4); sl3_w2_ident_n5_j15,        *)
(*   sl3_w2_ident_n5_j14, sl3_w2_ident_n5_j13 (head samples at n = 5). *)
(*   All statements are Set-carried equality certificates over the     *)
(*   piu_zz_gauss_pair.qeqT carrier (the landed anchor tier states     *)
(*   the same identities over the Prop Qeq; this unit keeps the        *)
(*   born-clean Set carrier and consumes the PROVEN binary-carrier     *)
(*   agreement sl3_aj_bin_agree to reach the tree carrier piu_zz_Aj).  *)
(* Source routing: the identity shape (sign, mirror index, exact       *)
(*   power of ten) mirrors the landed GF anchor tier verbatim; the     *)
(*   pole fold is the per-factor folded object of                     *)
(*   sl3_w2_body_pole_dom; exact document paths live in the external   *)
(*   provenance ledger attached to the delivery receipt.               *)
(* Build: coqc -native-compiler no -q -Q ConstructiveWorld_Live ""     *)
(*   -Q _build "" -o _build/sl3_w2_body_identity_anchors.vo            *)
(*   sl3_w2_body_identity_anchors.v (full line in the provenance      *)
(*   ledger).                                                          *)
(* Related registrations: each anchor is one instance of the born      *)
(*   face sl3_w2_pole_weld_face (the registered identity obligation);  *)
(*   the anchors certify the head samples only and claim no universal  *)
(*   identity.  The machine-outside integer pre-verification of the    *)
(*   same identities is the numeric guardrail, NOT a proof.            *)
(* Mission: extend the machine-checked identity tier of the GF         *)
(*   decomposition by one full all-j band (n = 3), a second full band  *)
(*   (n = 4), and head samples at n = 5, so that the universal        *)
(*   identity obligation carries machine evidence at small samples    *)
(*   before the structural proof effort begins.                        *)
(* Dependencies: Stdlib QArith, ZArith, Arith, Lia, List, Qpower,      *)
(*   Qabs; project units piu_mu_criterion, S02_CauchyComplete,         *)
(*   piu_zz_kernel_sum, sl3_d3_gf_carrier, sl3_d2_flag,                *)
(*   sl3_w2_body_pole_dom.                                             *)
(* References: the landed GF anchor tier (n = 1, 2); the landed        *)
(*   binary-flag unit (the carrier agreement weld sl3_aj_bin_agree);   *)
(*   the kernel-sum coefficient carrier piu_zz_Aj.                     *)
(* Constructivity: every statement is Set-carried; the proofs are      *)
(*   exact machine computations (vm_compute over the Z-domain binary   *)
(*   carrier and the folded pole table) closed by reflexivity - the    *)
(*   decidable-equality certificate form of the landed anchor tier;    *)
(*   zero assumption surfaces, zero proof surrender, all Defined.      *)
(* ================================================================== *)

From Stdlib Require Import QArith ZArith Arith Lia List.
From Stdlib Require Import Qpower.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Morphisms Setoid.
Import ListNotations.
Require Import piu_mu_criterion.
Require Import S02_CauchyComplete.
Require Import piu_zz_kernel_sum.
Require Import sl3_d3_gf_carrier.
Require Import sl3_d2_flag.
Require Import sl3_w2_body_pole_dom.

(* ================================================================== *)
(* Section 1. Cross-check against the landed anchor tier (n = 2).      *)
(* Template note: each anchor goes through the binary carrier in two   *)
(* steps - a qeqT_intro with vm_compute over the binary-computable     *)
(* sides (the folded pole table and sl3_aj_bin), then qeqT_mul_r over  *)
(* the PROVEN universal agreement sl3_aj_bin_agree - so no setoid      *)
(* rewriting over the indexed qeqT family is ever performed (first-hand *)
(* finding: that rewrite is exponentially expensive here).  The        *)
(* statement groups the sign and the power of ten as one multiplier,   *)
(* value-identical to the landed anchor tier shape.                    *)
(* ================================================================== *)

Lemma sl3_w2_ident_n2_x0 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 2%nat ((3 * 2%nat) - 0%nat)))
    (piu_zz_Aj 2%nat 0%nat
     * ((if Nat.odd ((3 * 2%nat) - 0%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 2%nat) + 1%nat + ((3 * 2%nat) - 0%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 2%nat ((3 * 2%nat) - 0%nat)))
           (sl3_aj_bin 2%nat 0%nat
            * ((if Nat.odd ((3 * 2%nat) - 0%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 2%nat) + 1%nat + ((3 * 2%nat) - 0%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 2%nat 0%nat)).
Defined.

Lemma sl3_w2_ident_n2_x3 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 2%nat ((3 * 2%nat) - 3%nat)))
    (piu_zz_Aj 2%nat 3%nat
     * ((if Nat.odd ((3 * 2%nat) - 3%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 2%nat) + 1%nat + ((3 * 2%nat) - 3%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 2%nat ((3 * 2%nat) - 3%nat)))
           (sl3_aj_bin 2%nat 3%nat
            * ((if Nat.odd ((3 * 2%nat) - 3%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 2%nat) + 1%nat + ((3 * 2%nat) - 3%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 2%nat 3%nat)).
Defined.

(* ================================================================== *)
(* Section 2. The n = 3 band: all j = 0..9.                            *)
(* ================================================================== *)

Lemma sl3_w2_ident_n3_j0 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 0%nat)))
    (piu_zz_Aj 3%nat 0%nat
     * ((if Nat.odd ((3 * 3%nat) - 0%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 0%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 0%nat)))
           (sl3_aj_bin 3%nat 0%nat
            * ((if Nat.odd ((3 * 3%nat) - 0%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 0%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 0%nat)).
Defined.

Lemma sl3_w2_ident_n3_j1 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 1%nat)))
    (piu_zz_Aj 3%nat 1%nat
     * ((if Nat.odd ((3 * 3%nat) - 1%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 1%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 1%nat)))
           (sl3_aj_bin 3%nat 1%nat
            * ((if Nat.odd ((3 * 3%nat) - 1%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 1%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 1%nat)).
Defined.

Lemma sl3_w2_ident_n3_j2 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 2%nat)))
    (piu_zz_Aj 3%nat 2%nat
     * ((if Nat.odd ((3 * 3%nat) - 2%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 2%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 2%nat)))
           (sl3_aj_bin 3%nat 2%nat
            * ((if Nat.odd ((3 * 3%nat) - 2%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 2%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 2%nat)).
Defined.

Lemma sl3_w2_ident_n3_j3 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 3%nat)))
    (piu_zz_Aj 3%nat 3%nat
     * ((if Nat.odd ((3 * 3%nat) - 3%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 3%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 3%nat)))
           (sl3_aj_bin 3%nat 3%nat
            * ((if Nat.odd ((3 * 3%nat) - 3%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 3%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 3%nat)).
Defined.

Lemma sl3_w2_ident_n3_j4 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 4%nat)))
    (piu_zz_Aj 3%nat 4%nat
     * ((if Nat.odd ((3 * 3%nat) - 4%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 4%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 4%nat)))
           (sl3_aj_bin 3%nat 4%nat
            * ((if Nat.odd ((3 * 3%nat) - 4%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 4%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 4%nat)).
Defined.

Lemma sl3_w2_ident_n3_j5 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 5%nat)))
    (piu_zz_Aj 3%nat 5%nat
     * ((if Nat.odd ((3 * 3%nat) - 5%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 5%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 5%nat)))
           (sl3_aj_bin 3%nat 5%nat
            * ((if Nat.odd ((3 * 3%nat) - 5%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 5%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 5%nat)).
Defined.

Lemma sl3_w2_ident_n3_j6 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 6%nat)))
    (piu_zz_Aj 3%nat 6%nat
     * ((if Nat.odd ((3 * 3%nat) - 6%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 6%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 6%nat)))
           (sl3_aj_bin 3%nat 6%nat
            * ((if Nat.odd ((3 * 3%nat) - 6%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 6%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 6%nat)).
Defined.

Lemma sl3_w2_ident_n3_j7 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 7%nat)))
    (piu_zz_Aj 3%nat 7%nat
     * ((if Nat.odd ((3 * 3%nat) - 7%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 7%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 7%nat)))
           (sl3_aj_bin 3%nat 7%nat
            * ((if Nat.odd ((3 * 3%nat) - 7%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 7%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 7%nat)).
Defined.

Lemma sl3_w2_ident_n3_j8 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 8%nat)))
    (piu_zz_Aj 3%nat 8%nat
     * ((if Nat.odd ((3 * 3%nat) - 8%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 8%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 8%nat)))
           (sl3_aj_bin 3%nat 8%nat
            * ((if Nat.odd ((3 * 3%nat) - 8%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 8%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 8%nat)).
Defined.

Lemma sl3_w2_ident_n3_j9 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 9%nat)))
    (piu_zz_Aj 3%nat 9%nat
     * ((if Nat.odd ((3 * 3%nat) - 9%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 9%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 3%nat ((3 * 3%nat) - 9%nat)))
           (sl3_aj_bin 3%nat 9%nat
            * ((if Nat.odd ((3 * 3%nat) - 9%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 3%nat) + 1%nat + ((3 * 3%nat) - 9%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 3%nat 9%nat)).
Defined.

(* ================================================================== *)
(* Section 3. The n = 4 band: all j = 0..12.                           *)
(* ================================================================== *)

Lemma sl3_w2_ident_n4_j0 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 0%nat)))
    (piu_zz_Aj 4%nat 0%nat
     * ((if Nat.odd ((3 * 4%nat) - 0%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 0%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 0%nat)))
           (sl3_aj_bin 4%nat 0%nat
            * ((if Nat.odd ((3 * 4%nat) - 0%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 0%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 0%nat)).
Defined.

Lemma sl3_w2_ident_n4_j1 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 1%nat)))
    (piu_zz_Aj 4%nat 1%nat
     * ((if Nat.odd ((3 * 4%nat) - 1%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 1%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 1%nat)))
           (sl3_aj_bin 4%nat 1%nat
            * ((if Nat.odd ((3 * 4%nat) - 1%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 1%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 1%nat)).
Defined.

Lemma sl3_w2_ident_n4_j2 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 2%nat)))
    (piu_zz_Aj 4%nat 2%nat
     * ((if Nat.odd ((3 * 4%nat) - 2%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 2%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 2%nat)))
           (sl3_aj_bin 4%nat 2%nat
            * ((if Nat.odd ((3 * 4%nat) - 2%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 2%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 2%nat)).
Defined.

Lemma sl3_w2_ident_n4_j3 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 3%nat)))
    (piu_zz_Aj 4%nat 3%nat
     * ((if Nat.odd ((3 * 4%nat) - 3%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 3%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 3%nat)))
           (sl3_aj_bin 4%nat 3%nat
            * ((if Nat.odd ((3 * 4%nat) - 3%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 3%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 3%nat)).
Defined.

Lemma sl3_w2_ident_n4_j4 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 4%nat)))
    (piu_zz_Aj 4%nat 4%nat
     * ((if Nat.odd ((3 * 4%nat) - 4%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 4%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 4%nat)))
           (sl3_aj_bin 4%nat 4%nat
            * ((if Nat.odd ((3 * 4%nat) - 4%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 4%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 4%nat)).
Defined.

Lemma sl3_w2_ident_n4_j5 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 5%nat)))
    (piu_zz_Aj 4%nat 5%nat
     * ((if Nat.odd ((3 * 4%nat) - 5%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 5%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 5%nat)))
           (sl3_aj_bin 4%nat 5%nat
            * ((if Nat.odd ((3 * 4%nat) - 5%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 5%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 5%nat)).
Defined.

Lemma sl3_w2_ident_n4_j6 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 6%nat)))
    (piu_zz_Aj 4%nat 6%nat
     * ((if Nat.odd ((3 * 4%nat) - 6%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 6%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 6%nat)))
           (sl3_aj_bin 4%nat 6%nat
            * ((if Nat.odd ((3 * 4%nat) - 6%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 6%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 6%nat)).
Defined.

Lemma sl3_w2_ident_n4_j7 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 7%nat)))
    (piu_zz_Aj 4%nat 7%nat
     * ((if Nat.odd ((3 * 4%nat) - 7%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 7%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 7%nat)))
           (sl3_aj_bin 4%nat 7%nat
            * ((if Nat.odd ((3 * 4%nat) - 7%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 7%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 7%nat)).
Defined.

Lemma sl3_w2_ident_n4_j8 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 8%nat)))
    (piu_zz_Aj 4%nat 8%nat
     * ((if Nat.odd ((3 * 4%nat) - 8%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 8%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 8%nat)))
           (sl3_aj_bin 4%nat 8%nat
            * ((if Nat.odd ((3 * 4%nat) - 8%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 8%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 8%nat)).
Defined.

Lemma sl3_w2_ident_n4_j9 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 9%nat)))
    (piu_zz_Aj 4%nat 9%nat
     * ((if Nat.odd ((3 * 4%nat) - 9%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 9%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 9%nat)))
           (sl3_aj_bin 4%nat 9%nat
            * ((if Nat.odd ((3 * 4%nat) - 9%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 9%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 9%nat)).
Defined.

Lemma sl3_w2_ident_n4_j10 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 10%nat)))
    (piu_zz_Aj 4%nat 10%nat
     * ((if Nat.odd ((3 * 4%nat) - 10%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 10%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 10%nat)))
           (sl3_aj_bin 4%nat 10%nat
            * ((if Nat.odd ((3 * 4%nat) - 10%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 10%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 10%nat)).
Defined.

Lemma sl3_w2_ident_n4_j11 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 11%nat)))
    (piu_zz_Aj 4%nat 11%nat
     * ((if Nat.odd ((3 * 4%nat) - 11%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 11%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 11%nat)))
           (sl3_aj_bin 4%nat 11%nat
            * ((if Nat.odd ((3 * 4%nat) - 11%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 11%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 11%nat)).
Defined.

Lemma sl3_w2_ident_n4_j12 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 12%nat)))
    (piu_zz_Aj 4%nat 12%nat
     * ((if Nat.odd ((3 * 4%nat) - 12%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 12%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 4%nat ((3 * 4%nat) - 12%nat)))
           (sl3_aj_bin 4%nat 12%nat
            * ((if Nat.odd ((3 * 4%nat) - 12%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 4%nat) + 1%nat + ((3 * 4%nat) - 12%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 4%nat 12%nat)).
Defined.

(* ================================================================== *)
(* Section 4. The n = 5 head samples (the cheap tuple-count corner:    *)
(* j = 3n carries a single tuple, j = 3n-1 six tuples, j = 3n-2        *)
(* twenty-one tuples).                                                 *)
(* ================================================================== *)

Lemma sl3_w2_ident_n5_j15 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 5%nat ((3 * 5%nat) - 15%nat)))
    (piu_zz_Aj 5%nat 15%nat
     * ((if Nat.odd ((3 * 5%nat) - 15%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 5%nat) + 1%nat + ((3 * 5%nat) - 15%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 5%nat ((3 * 5%nat) - 15%nat)))
           (sl3_aj_bin 5%nat 15%nat
            * ((if Nat.odd ((3 * 5%nat) - 15%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 5%nat) + 1%nat + ((3 * 5%nat) - 15%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 5%nat 15%nat)).
Defined.

Lemma sl3_w2_ident_n5_j14 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 5%nat ((3 * 5%nat) - 14%nat)))
    (piu_zz_Aj 5%nat 14%nat
     * ((if Nat.odd ((3 * 5%nat) - 14%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 5%nat) + 1%nat + ((3 * 5%nat) - 14%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 5%nat ((3 * 5%nat) - 14%nat)))
           (sl3_aj_bin 5%nat 14%nat
            * ((if Nat.odd ((3 * 5%nat) - 14%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 5%nat) + 1%nat + ((3 * 5%nat) - 14%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 5%nat 14%nat)).
Defined.

Lemma sl3_w2_ident_n5_j13 :
  piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ 5%nat ((3 * 5%nat) - 13%nat)))
    (piu_zz_Aj 5%nat 13%nat
     * ((if Nat.odd ((3 * 5%nat) - 13%nat) then (-1)#1 else (1)#1)
        * inject_Z (10 ^ Z.of_nat ((3 * 5%nat) + 1%nat + ((3 * 5%nat) - 13%nat)))))%Q.
Proof.
  apply (piu_zz_gauss_pair.qeqT_trans
           (inject_Z (sl3_w2_poleZ 5%nat ((3 * 5%nat) - 13%nat)))
           (sl3_aj_bin 5%nat 13%nat
            * ((if Nat.odd ((3 * 5%nat) - 13%nat) then (-1)#1 else (1)#1)
               * inject_Z (10 ^ Z.of_nat ((3 * 5%nat) + 1%nat + ((3 * 5%nat) - 13%nat)))))).
  - apply piu_zz_gauss_pair.qeqT_intro. vm_compute. reflexivity.
  - apply (piu_zz_gauss_pair.qeqT_mul_r _ _ _ (sl3_aj_bin_agree 5%nat 13%nat)).
Defined.

Print Assumptions sl3_w2_ident_n2_x0.
Print Assumptions sl3_w2_ident_n2_x3.
Print Assumptions sl3_w2_ident_n3_j0.
Print Assumptions sl3_w2_ident_n3_j1.
Print Assumptions sl3_w2_ident_n3_j2.
Print Assumptions sl3_w2_ident_n3_j3.
Print Assumptions sl3_w2_ident_n3_j4.
Print Assumptions sl3_w2_ident_n3_j5.
Print Assumptions sl3_w2_ident_n3_j6.
Print Assumptions sl3_w2_ident_n3_j7.
Print Assumptions sl3_w2_ident_n3_j8.
Print Assumptions sl3_w2_ident_n3_j9.
Print Assumptions sl3_w2_ident_n4_j0.
Print Assumptions sl3_w2_ident_n4_j1.
Print Assumptions sl3_w2_ident_n4_j2.
Print Assumptions sl3_w2_ident_n4_j3.
Print Assumptions sl3_w2_ident_n4_j4.
Print Assumptions sl3_w2_ident_n4_j5.
Print Assumptions sl3_w2_ident_n4_j6.
Print Assumptions sl3_w2_ident_n4_j7.
Print Assumptions sl3_w2_ident_n4_j8.
Print Assumptions sl3_w2_ident_n4_j9.
Print Assumptions sl3_w2_ident_n4_j10.
Print Assumptions sl3_w2_ident_n4_j11.
Print Assumptions sl3_w2_ident_n4_j12.
Print Assumptions sl3_w2_ident_n5_j15.
Print Assumptions sl3_w2_ident_n5_j14.
Print Assumptions sl3_w2_ident_n5_j13.
