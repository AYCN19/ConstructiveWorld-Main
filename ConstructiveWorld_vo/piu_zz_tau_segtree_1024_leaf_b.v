(* piu_zz_tau_segtree_1024_leaf_b.v — leaf lane b of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 12..23 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_b.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA12 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_12 : piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 16%nat = piu_zz_lit_segA12.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA13 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_13 : piu_zz_zprod_seg 1024%nat ((512%nat + 192%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA13.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA14 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_14 : piu_zz_zprod_seg 1024%nat (512%nat + 224%nat) 16%nat = piu_zz_lit_segA14.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA15 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_15 : piu_zz_zprod_seg 1024%nat ((512%nat + 224%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA15.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA16 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_16 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 16%nat = piu_zz_lit_segA16.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA17 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_17 : piu_zz_zprod_seg 1024%nat ((512%nat + 256%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA17.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA18 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_18 : piu_zz_zprod_seg 1024%nat (512%nat + 288%nat) 16%nat = piu_zz_lit_segA18.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA19 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_19 : piu_zz_zprod_seg 1024%nat ((512%nat + 288%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA19.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA20 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_20 : piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 16%nat = piu_zz_lit_segA20.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA21 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_21 : piu_zz_zprod_seg 1024%nat ((512%nat + 320%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA21.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA22 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_22 : piu_zz_zprod_seg 1024%nat (512%nat + 352%nat) 16%nat = piu_zz_lit_segA22.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA23 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_23 : piu_zz_zprod_seg 1024%nat ((512%nat + 352%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA23.
Proof. vm_compute. reflexivity. Qed.
