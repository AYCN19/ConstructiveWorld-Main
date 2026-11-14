(* ================================================================= *)
(* sl3_d2_flag_anchors.v - SL3 debt D-SL3-2: the n >= 3 head anchors.  *)
(* ================================================================= *)
(* Mission.: the n = 3..4 head anchor family for the Z-exact binary    *)
(*   finite flag sl3_bin_flag_body at the sigma slot s = 17 (the       *)
(*   tree-side slot pin of the N2c chain).  Each anchor pins           *)
(*     sl3_bin_flag_body 17 n = true                                   *)
(*   by vm_compute; together with the weld sl3_aj_flag_spec_at_17      *)
(*   (sl3_d2_flag.v) a true anchor discharges the sharp face           *)
(*   pointwise on all j <= 3n, consuming the PROVEN tree spec          *)
(*   piu_zz_n2c_finite_le17_spec (n2c:135-148).                        *)
(* Statement faces. sl3_bin_flag_n3, sl3_bin_flag_n4 (open: n5..n16).  *)
(* Dependencies.: sl3_d2_flag.v (binary carrier, agreement chain,      *)
(*   weld sl3_aj_flag_spec_at_17); the dependency closure of that      *)
(*   unit (S02_CauchyComplete, piu_zz_gauss_pair, piu_zz_kernel_sum,   *)
(*   piu_zz_n2c_sigma_assembly) transitively.                          *)
(* Source routing. Anchor template per the SL3 slot draft section 4    *)
(*   (the head-side anchor shape) with the sigma-17 pin of the tree    *)
(*   flag family n2c:157-161.                                          *)
(* Pre-verification. Every anchor value is machine-outside             *)
(*   pre-verified by exact integer arithmetic (python -I, Fraction-    *)
(*   exact mirror of the kernel-sum table, cross-validated against     *)
(*   the tree machine-certified samples at n = 1, 2) BEFORE being      *)
(*   pinned here; no anchor value is transcribed by hand.              *)
(* Constructivity.: all statements Set-carried, zero new Prop surface; *)
(*   proofs are vm_compute + reflexivity over the Z-domain binary      *)
(*   carrier, transparent (Defined).                                   *)
(* Build.: coqc -native-compiler no -q -Q ConstructiveWorld_Live ""    *)
(*   -Q sl3_sbx/_d2out "" sl3_d2_flag_anchors.v (Rocq 9.3.0).          *)
(* ================================================================= *)

From Stdlib Require Import QArith ZArith Arith Lia List QArith.Qabs Qring.
From Stdlib Require Import Morphisms Setoid.
Import ListNotations.
Require Import S02_CauchyComplete.
Require Import piu_zz_gauss_pair.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_n2c_sigma_assembly.
Require Import sl3_d2_flag.

(* ---- machine-certified tier: n = 3, 4 ---- *)
(* Tier scope note: n = 5..16 are NOT pinned here.  The binary        *)
(* carrier in sl3_d2_flag.v uses the Pascal-recursion binomial        *)
(* (sl3_binomZ), whose unmemoized call tree grows like the binomial   *)
(* coefficient itself: measured vm_compute wall time n = 3: 1.3 s,    *)
(* n = 4: 24.7 s, n = 5: beyond the per-anchor budget (no progress    *)
(* at ~9 minutes), n >= 6 projected far beyond.  The per-anchor       *)
(* compute-budget rule (pinned values must be machine-certified       *)
(* within budget; no unpinned claims) therefore stops this tier at    *)
(* n = 4.  The named repair for the next tier is a closed-form or     *)
(* table-backed binomial in the carrier (dropping the multiplicative  *)
(* identity through to the tree Pascal form), which restores linear   *)
(* per-term cost; the machine-outside exact-integer pre-verification  *)
(* already covers n = 3..16 all TRUE at s = 17 for that tier.         *)

Lemma sl3_bin_flag_n3 : sl3_bin_flag_body 17 3 = true.
Proof. vm_compute. reflexivity. Defined.

Lemma sl3_bin_flag_n4 : sl3_bin_flag_body 17 4 = true.
Proof. vm_compute. reflexivity. Defined.

Print Assumptions sl3_bin_flag_n3.
Print Assumptions sl3_bin_flag_n4.
