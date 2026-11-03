(* piu_zz_tau_segtree_1024_leaf_e.v — leaf lane e of the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: literal certificates for leaves 48..59 of 96 — the 16-wide
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
      -Q . "" piu_zz_tau_segtree_1024_leaf_e.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.

Definition piu_zz_lit_segA48 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_48 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 16%nat = piu_zz_lit_segA48.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA49 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_49 : piu_zz_zprod_seg 1024%nat ((512%nat + 768%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA49.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA50 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_50 : piu_zz_zprod_seg 1024%nat (512%nat + 800%nat) 16%nat = piu_zz_lit_segA50.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA51 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_51 : piu_zz_zprod_seg 1024%nat ((512%nat + 800%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA51.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA52 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_52 : piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 16%nat = piu_zz_lit_segA52.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA53 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_53 : piu_zz_zprod_seg 1024%nat ((512%nat + 832%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA53.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA54 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_54 : piu_zz_zprod_seg 1024%nat (512%nat + 864%nat) 16%nat = piu_zz_lit_segA54.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA55 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_55 : piu_zz_zprod_seg 1024%nat ((512%nat + 864%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA55.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA56 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_56 : piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 16%nat = piu_zz_lit_segA56.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA57 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_57 : piu_zz_zprod_seg 1024%nat ((512%nat + 896%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA57.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA58 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_58 : piu_zz_zprod_seg 1024%nat (512%nat + 928%nat) 16%nat = piu_zz_lit_segA58.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_segA59 : Z := 1%Z.
Lemma piu_zz_segleaf_1024_59 : piu_zz_zprod_seg 1024%nat ((512%nat + 928%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA59.
Proof. vm_compute. reflexivity. Qed.
