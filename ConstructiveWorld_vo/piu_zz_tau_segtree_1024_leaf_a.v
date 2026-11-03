(* piu_zz_tau_segtree_1024_leaf_a.v — leaf lane a of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 0..11 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_a.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA0 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_0 : piu_zz_zprod_seg 1024%nat 512%nat 16%nat = piu_zz_lit_segA0.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA1 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_1 : piu_zz_zprod_seg 1024%nat (512%nat + 16%nat) 16%nat = piu_zz_lit_segA1.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA2 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_2 : piu_zz_zprod_seg 1024%nat (512%nat + 32%nat) 16%nat = piu_zz_lit_segA2.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA3 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_3 : piu_zz_zprod_seg 1024%nat ((512%nat + 32%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA3.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA4 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_4 : piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 16%nat = piu_zz_lit_segA4.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA5 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_5 : piu_zz_zprod_seg 1024%nat ((512%nat + 64%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA5.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA6 : Z := 381923%Z.
Lemma piu_zz_segleaf_1024_6 : piu_zz_zprod_seg 1024%nat (512%nat + 96%nat) 16%nat = piu_zz_lit_segA6.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA7 : Z := 631%Z.
Lemma piu_zz_segleaf_1024_7 : piu_zz_zprod_seg 1024%nat ((512%nat + 96%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA7.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA8 : Z := 174135158033%Z.
Lemma piu_zz_segleaf_1024_8 : piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 16%nat = piu_zz_lit_segA8.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA9 : Z := 435599%Z.
Lemma piu_zz_segleaf_1024_9 : piu_zz_zprod_seg 1024%nat ((512%nat + 128%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA9.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA10 : Z := 455621%Z.
Lemma piu_zz_segleaf_1024_10 : piu_zz_zprod_seg 1024%nat (512%nat + 160%nat) 16%nat = piu_zz_lit_segA10.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA11 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_11 : piu_zz_zprod_seg 1024%nat ((512%nat + 160%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA11.
Proof. vm_compute. reflexivity. Qed.
