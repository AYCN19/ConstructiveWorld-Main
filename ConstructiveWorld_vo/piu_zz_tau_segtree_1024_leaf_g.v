(* piu_zz_tau_segtree_1024_leaf_g.v — leaf lane g of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 72..83 of 96 — the 16-wide
      segment products piu_zz_zprod_seg 1024 (512 + 16*j) 16 of the 1024
      face, each equal to its literal piu_zz_lit_segA*.
   2. Dependencies: piu_zz_tau_enclosure_bank4, piu_zz_tau_segaddsplit,
      piu_zz_poincare_engine, piu_zz_padic_clearing; Stdlib QArith, ZArith,
      Arith, PArith, Lia, List.
   3. References: cited by piu_zz_tau_segtree_1024_merge.v (the 95-node
      balanced merge); certificate shape follows
      piu_zz_tau_enclosure_literals.v.
   4. Constructivity: assumption-free, zero classical logic; every proof is
      vm_compute normalisation closed by reflexivity (extraction-clean).
   5. Build: coqc -time -native-compiler no -q
      -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
      -Q . "" piu_zz_tau_segtree_1024_leaf_g.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA72 : Z := 2782223%Z.
Lemma piu_zz_segleaf_1024_72 : piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 16%nat = piu_zz_lit_segA72.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA73 : Z := 1693%Z.
Lemma piu_zz_segleaf_1024_73 : piu_zz_zprod_seg 1024%nat ((512%nat + 1152%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA73.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA74 : Z := 4927393927%Z.
Lemma piu_zz_segleaf_1024_74 : piu_zz_zprod_seg 1024%nat (512%nat + 1184%nat) 16%nat = piu_zz_lit_segA74.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA75 : Z := 2965283%Z.
Lemma piu_zz_segleaf_1024_75 : piu_zz_zprod_seg 1024%nat ((512%nat + 1184%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA75.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA76 : Z := 3017153%Z.
Lemma piu_zz_segleaf_1024_76 : piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 16%nat = piu_zz_lit_segA76.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA77 : Z := 5386921669%Z.
Lemma piu_zz_segleaf_1024_77 : piu_zz_zprod_seg 1024%nat ((512%nat + 1216%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA77.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA78 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_78 : piu_zz_zprod_seg 1024%nat (512%nat + 1248%nat) 16%nat = piu_zz_lit_segA78.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA79 : Z := 10129165428713%Z.
Lemma piu_zz_segleaf_1024_79 : piu_zz_zprod_seg 1024%nat ((512%nat + 1248%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA79.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA80 : Z := 1801%Z.
Lemma piu_zz_segleaf_1024_80 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 16%nat = piu_zz_lit_segA80.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA81 : Z := 3301453%Z.
Lemma piu_zz_segleaf_1024_81 : piu_zz_zprod_seg 1024%nat ((512%nat + 1280%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA81.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA82 : Z := 1831%Z.
Lemma piu_zz_segleaf_1024_82 : piu_zz_zprod_seg 1024%nat (512%nat + 1312%nat) 16%nat = piu_zz_lit_segA82.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA83 : Z := 1847%Z.
Lemma piu_zz_segleaf_1024_83 : piu_zz_zprod_seg 1024%nat ((512%nat + 1312%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA83.
Proof. vm_compute. reflexivity. Qed.
