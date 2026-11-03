(* piu_zz_tau_segtree_1024_leaf_h.v — leaf lane h of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 84..95 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_h.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA84 : Z := 6500765177%Z.
Lemma piu_zz_segleaf_1024_84 : piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 16%nat = piu_zz_lit_segA84.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA85 : Z := 6605851859%Z.
Lemma piu_zz_segleaf_1024_85 : piu_zz_zprod_seg 1024%nat ((512%nat + 1344%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA85.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA86 : Z := 3590989%Z.
Lemma piu_zz_segleaf_1024_86 : piu_zz_zprod_seg 1024%nat (512%nat + 1376%nat) 16%nat = piu_zz_lit_segA86.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA87 : Z := 3648091%Z.
Lemma piu_zz_segleaf_1024_87 : piu_zz_zprod_seg 1024%nat ((512%nat + 1376%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA87.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA88 : Z := 3732623%Z.
Lemma piu_zz_segleaf_1024_88 : piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 16%nat = piu_zz_lit_segA88.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA89 : Z := 3802499%Z.
Lemma piu_zz_segleaf_1024_89 : piu_zz_zprod_seg 1024%nat ((512%nat + 1408%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA89.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA90 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_90 : piu_zz_zprod_seg 1024%nat (512%nat + 1440%nat) 16%nat = piu_zz_lit_segA90.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA91 : Z := 3904567%Z.
Lemma piu_zz_segleaf_1024_91 : piu_zz_zprod_seg 1024%nat ((512%nat + 1440%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA91.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA92 : Z := 15808695152273%Z.
Lemma piu_zz_segleaf_1024_92 : piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 16%nat = piu_zz_lit_segA92.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA93 : Z := 4028033%Z.
Lemma piu_zz_segleaf_1024_93 : piu_zz_zprod_seg 1024%nat ((512%nat + 1472%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA93.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA94 : Z := 8295483311%Z.
Lemma piu_zz_segleaf_1024_94 : piu_zz_zprod_seg 1024%nat (512%nat + 1504%nat) 16%nat = piu_zz_lit_segA94.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA95 : Z := 2039%Z.
Lemma piu_zz_segleaf_1024_95 : piu_zz_zprod_seg 1024%nat ((512%nat + 1504%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA95.
Proof. vm_compute. reflexivity. Qed.
