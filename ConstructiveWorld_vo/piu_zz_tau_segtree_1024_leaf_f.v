(* piu_zz_tau_segtree_1024_leaf_f.v — leaf lane f of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 60..71 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_f.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA60 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_60 : piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 16%nat = piu_zz_lit_segA60.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA61 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_61 : piu_zz_zprod_seg 1024%nat ((512%nat + 960%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA61.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA62 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_62 : piu_zz_zprod_seg 1024%nat (512%nat + 992%nat) 16%nat = piu_zz_lit_segA62.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA63 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_63 : piu_zz_zprod_seg 1024%nat ((512%nat + 992%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA63.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA64 : Z := 2390107%Z.
Lemma piu_zz_segleaf_1024_64 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 16%nat = piu_zz_lit_segA64.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA65 : Z := 3793906009%Z.
Lemma piu_zz_segleaf_1024_65 : piu_zz_zprod_seg 1024%nat ((512%nat + 1024%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA65.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA66 : Z := 3926804047%Z.
Lemma piu_zz_segleaf_1024_66 : piu_zz_zprod_seg 1024%nat (512%nat + 1056%nat) 16%nat = piu_zz_lit_segA66.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA67 : Z := 1597%Z.
Lemma piu_zz_segleaf_1024_67 : piu_zz_zprod_seg 1024%nat ((512%nat + 1056%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA67.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA68 : Z := 6677249744819%Z.
Lemma piu_zz_segleaf_1024_68 : piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 16%nat = piu_zz_lit_segA68.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA69 : Z := 4269897173%Z.
Lemma piu_zz_segleaf_1024_69 : piu_zz_zprod_seg 1024%nat ((512%nat + 1088%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA69.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA70 : Z := 1637%Z.
Lemma piu_zz_segleaf_1024_70 : piu_zz_zprod_seg 1024%nat (512%nat + 1120%nat) 16%nat = piu_zz_lit_segA70.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA71 : Z := 2755591%Z.
Lemma piu_zz_segleaf_1024_71 : piu_zz_zprod_seg 1024%nat ((512%nat + 1120%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA71.
Proof. vm_compute. reflexivity. Qed.
