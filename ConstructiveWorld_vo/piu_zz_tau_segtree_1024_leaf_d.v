(* piu_zz_tau_segtree_1024_leaf_d.v — leaf lane d of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 36..47 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_d.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA36 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_36 : piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 16%nat = piu_zz_lit_segA36.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA37 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_37 : piu_zz_zprod_seg 1024%nat ((512%nat + 576%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA37.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA38 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_38 : piu_zz_zprod_seg 1024%nat (512%nat + 608%nat) 16%nat = piu_zz_lit_segA38.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA39 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_39 : piu_zz_zprod_seg 1024%nat ((512%nat + 608%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA39.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA40 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_40 : piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 16%nat = piu_zz_lit_segA40.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA41 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_41 : piu_zz_zprod_seg 1024%nat ((512%nat + 640%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA41.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA42 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_42 : piu_zz_zprod_seg 1024%nat (512%nat + 672%nat) 16%nat = piu_zz_lit_segA42.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA43 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_43 : piu_zz_zprod_seg 1024%nat ((512%nat + 672%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA43.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA44 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_44 : piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 16%nat = piu_zz_lit_segA44.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA45 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_45 : piu_zz_zprod_seg 1024%nat ((512%nat + 704%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA45.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA46 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_46 : piu_zz_zprod_seg 1024%nat (512%nat + 736%nat) 16%nat = piu_zz_lit_segA46.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA47 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_47 : piu_zz_zprod_seg 1024%nat ((512%nat + 736%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA47.
Proof. vm_compute. reflexivity. Qed.
