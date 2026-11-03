(* piu_zz_tau_segtree_1024_leaf_c.v — leaf lane c of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 24..35 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_c.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA24 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_24 : piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 16%nat = piu_zz_lit_segA24.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA25 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_25 : piu_zz_zprod_seg 1024%nat ((512%nat + 384%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA25.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA26 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_26 : piu_zz_zprod_seg 1024%nat (512%nat + 416%nat) 16%nat = piu_zz_lit_segA26.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA27 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_27 : piu_zz_zprod_seg 1024%nat ((512%nat + 416%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA27.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA28 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_28 : piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 16%nat = piu_zz_lit_segA28.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA29 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_29 : piu_zz_zprod_seg 1024%nat ((512%nat + 448%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA29.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA30 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_30 : piu_zz_zprod_seg 1024%nat (512%nat + 480%nat) 16%nat = piu_zz_lit_segA30.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA31 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_31 : piu_zz_zprod_seg 1024%nat ((512%nat + 480%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA31.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA32 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_32 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 16%nat = piu_zz_lit_segA32.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA33 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_33 : piu_zz_zprod_seg 1024%nat ((512%nat + 512%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA33.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA34 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_34 : piu_zz_zprod_seg 1024%nat (512%nat + 544%nat) 16%nat = piu_zz_lit_segA34.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA35 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_35 : piu_zz_zprod_seg 1024%nat ((512%nat + 544%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA35.
Proof. vm_compute. reflexivity. Qed.
