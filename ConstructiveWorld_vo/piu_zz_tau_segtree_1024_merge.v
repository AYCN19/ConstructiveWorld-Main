(* piu_zz_tau_segtree_1024_merge.v — balanced merge tree of the zzPhi_1024
   leaf factorisation.
   1. Mission: the 95 interior nodes (levels L1..L6 plus the root) of the
      64+32 balanced merge over the 96 leaf certificates; each node is a
      literal certificate proved from its two children via
      piu_zz_zprod_seg_addsplit, and the root piu_zz_segroot_1024 states
      piu_zz_zprod_seg 1024 512 1536 = piu_zz_lit_segroot_1024 (466019358449499161219416843802933941126124938819010411389576778901548717596419299037600247417718190415659730905352862267026183003996370196407919017272806068866538344582596949009120661077582192368800955531281827217310314763808351876369227770981490451%Z),
      the product of all 96 leaves.
   2. Dependencies: piu_zz_tau_enclosure_bank4, piu_zz_tau_segaddsplit,
      piu_zz_tau_segtree_1024_leaf_a..h, piu_zz_poincare_engine,
      piu_zz_padic_clearing; Stdlib QArith, ZArith, Arith, PArith, Lia, List.
   3. References: cited by zzphi_e_slim_equiv.v and
      piu_zz_tau_enclosure_phi1024_slim.v (the zzPhi_1024 merge citation);
      children are piu_zz_tau_segtree_1024_leaf_a..h.
   4. Constructivity: assumption-free, zero classical logic; every node proof
      cites its two child certificates (change and rewrite) closed by a small
      vm_compute normalisation (extraction-clean).
   5. Build: coqc -time -native-compiler no -q
      -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
      -Q . "" piu_zz_tau_segtree_1024_merge.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segaddsplit.
Require Import piu_zz_tau_segtree_1024_leaf_a.
Require Import piu_zz_tau_segtree_1024_leaf_b.
Require Import piu_zz_tau_segtree_1024_leaf_c.
Require Import piu_zz_tau_segtree_1024_leaf_d.
Require Import piu_zz_tau_segtree_1024_leaf_e.
Require Import piu_zz_tau_segtree_1024_leaf_f.
Require Import piu_zz_tau_segtree_1024_leaf_g.
Require Import piu_zz_tau_segtree_1024_leaf_h.

Definition piu_zz_lit_segnode_L1_0 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_0 : piu_zz_zprod_seg 1024%nat 512%nat 32%nat = piu_zz_lit_segnode_L1_0.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 32%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_0.
  rewrite piu_zz_segleaf_1024_1.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_1 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_1 : piu_zz_zprod_seg 1024%nat (512%nat + 32%nat) 32%nat = piu_zz_lit_segnode_L1_1.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 32%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 32%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 32%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_2.
  rewrite piu_zz_segleaf_1024_3.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_2 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_2 : piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 32%nat = piu_zz_lit_segnode_L1_2.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 64%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_4.
  rewrite piu_zz_segleaf_1024_5.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_3 : Z := 240993413%Z.
Lemma piu_zz_segnode_1024_L1_3 : piu_zz_zprod_seg 1024%nat (512%nat + 96%nat) 32%nat = piu_zz_lit_segnode_L1_3.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 96%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 96%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 96%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_6.
  rewrite piu_zz_segleaf_1024_7.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_4 : Z := 75853100704016767%Z.
Lemma piu_zz_segnode_1024_L1_4 : piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 32%nat = piu_zz_lit_segnode_L1_4.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 128%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_8.
  rewrite piu_zz_segleaf_1024_9.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_5 : Z := 455621%Z.
Lemma piu_zz_segnode_1024_L1_5 : piu_zz_zprod_seg 1024%nat (512%nat + 160%nat) 32%nat = piu_zz_lit_segnode_L1_5.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 160%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 160%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 160%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_10.
  rewrite piu_zz_segleaf_1024_11.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_6 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_6 : piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 32%nat = piu_zz_lit_segnode_L1_6.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 192%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_12.
  rewrite piu_zz_segleaf_1024_13.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_7 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_7 : piu_zz_zprod_seg 1024%nat (512%nat + 224%nat) 32%nat = piu_zz_lit_segnode_L1_7.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 224%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 224%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 224%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_14.
  rewrite piu_zz_segleaf_1024_15.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_8 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_8 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 32%nat = piu_zz_lit_segnode_L1_8.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 256%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_16.
  rewrite piu_zz_segleaf_1024_17.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_9 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_9 : piu_zz_zprod_seg 1024%nat (512%nat + 288%nat) 32%nat = piu_zz_lit_segnode_L1_9.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 288%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 288%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 288%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_18.
  rewrite piu_zz_segleaf_1024_19.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_10 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_10 : piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 32%nat = piu_zz_lit_segnode_L1_10.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 320%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_20.
  rewrite piu_zz_segleaf_1024_21.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_11 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_11 : piu_zz_zprod_seg 1024%nat (512%nat + 352%nat) 32%nat = piu_zz_lit_segnode_L1_11.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 352%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 352%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 352%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_22.
  rewrite piu_zz_segleaf_1024_23.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_12 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_12 : piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 32%nat = piu_zz_lit_segnode_L1_12.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 384%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_24.
  rewrite piu_zz_segleaf_1024_25.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_13 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_13 : piu_zz_zprod_seg 1024%nat (512%nat + 416%nat) 32%nat = piu_zz_lit_segnode_L1_13.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 416%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 416%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 416%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_26.
  rewrite piu_zz_segleaf_1024_27.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_14 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_14 : piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 32%nat = piu_zz_lit_segnode_L1_14.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 448%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_28.
  rewrite piu_zz_segleaf_1024_29.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_15 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_15 : piu_zz_zprod_seg 1024%nat (512%nat + 480%nat) 32%nat = piu_zz_lit_segnode_L1_15.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 480%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 480%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 480%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_30.
  rewrite piu_zz_segleaf_1024_31.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_16 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_16 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 32%nat = piu_zz_lit_segnode_L1_16.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 512%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_32.
  rewrite piu_zz_segleaf_1024_33.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_17 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_17 : piu_zz_zprod_seg 1024%nat (512%nat + 544%nat) 32%nat = piu_zz_lit_segnode_L1_17.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 544%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 544%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 544%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_34.
  rewrite piu_zz_segleaf_1024_35.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_18 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_18 : piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 32%nat = piu_zz_lit_segnode_L1_18.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 576%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_36.
  rewrite piu_zz_segleaf_1024_37.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_19 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_19 : piu_zz_zprod_seg 1024%nat (512%nat + 608%nat) 32%nat = piu_zz_lit_segnode_L1_19.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 608%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 608%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 608%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_38.
  rewrite piu_zz_segleaf_1024_39.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_20 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_20 : piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 32%nat = piu_zz_lit_segnode_L1_20.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 640%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_40.
  rewrite piu_zz_segleaf_1024_41.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_21 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_21 : piu_zz_zprod_seg 1024%nat (512%nat + 672%nat) 32%nat = piu_zz_lit_segnode_L1_21.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 672%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 672%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 672%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_42.
  rewrite piu_zz_segleaf_1024_43.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_22 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_22 : piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 32%nat = piu_zz_lit_segnode_L1_22.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 704%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_44.
  rewrite piu_zz_segleaf_1024_45.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_23 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_23 : piu_zz_zprod_seg 1024%nat (512%nat + 736%nat) 32%nat = piu_zz_lit_segnode_L1_23.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 736%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 736%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 736%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_46.
  rewrite piu_zz_segleaf_1024_47.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_24 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_24 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 32%nat = piu_zz_lit_segnode_L1_24.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 768%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_48.
  rewrite piu_zz_segleaf_1024_49.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_25 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_25 : piu_zz_zprod_seg 1024%nat (512%nat + 800%nat) 32%nat = piu_zz_lit_segnode_L1_25.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 800%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 800%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 800%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_50.
  rewrite piu_zz_segleaf_1024_51.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_26 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_26 : piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 32%nat = piu_zz_lit_segnode_L1_26.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 832%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_52.
  rewrite piu_zz_segleaf_1024_53.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_27 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_27 : piu_zz_zprod_seg 1024%nat (512%nat + 864%nat) 32%nat = piu_zz_lit_segnode_L1_27.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 864%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 864%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 864%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_54.
  rewrite piu_zz_segleaf_1024_55.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_28 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_28 : piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 32%nat = piu_zz_lit_segnode_L1_28.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 896%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_56.
  rewrite piu_zz_segleaf_1024_57.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_29 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_29 : piu_zz_zprod_seg 1024%nat (512%nat + 928%nat) 32%nat = piu_zz_lit_segnode_L1_29.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 928%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 928%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 928%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_58.
  rewrite piu_zz_segleaf_1024_59.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_30 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_30 : piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 32%nat = piu_zz_lit_segnode_L1_30.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 960%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_60.
  rewrite piu_zz_segleaf_1024_61.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_31 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L1_31 : piu_zz_zprod_seg 1024%nat (512%nat + 992%nat) 32%nat = piu_zz_lit_segnode_L1_31.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 992%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 992%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 992%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_62.
  rewrite piu_zz_segleaf_1024_63.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_32 : Z := 9067841309452963%Z.
Lemma piu_zz_segnode_1024_L1_32 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 32%nat = piu_zz_lit_segnode_L1_32.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1024%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_64.
  rewrite piu_zz_segleaf_1024_65.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_33 : Z := 6271106063059%Z.
Lemma piu_zz_segnode_1024_L1_33 : piu_zz_zprod_seg 1024%nat (512%nat + 1056%nat) 32%nat = piu_zz_lit_segnode_L1_33.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1056%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1056%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1056%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_66.
  rewrite piu_zz_segleaf_1024_67.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_34 : Z := 28511169808817619496687%Z.
Lemma piu_zz_segnode_1024_L1_34 : piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 32%nat = piu_zz_lit_segnode_L1_34.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1088%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_68.
  rewrite piu_zz_segleaf_1024_69.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_35 : Z := 4510902467%Z.
Lemma piu_zz_segnode_1024_L1_35 : piu_zz_zprod_seg 1024%nat (512%nat + 1120%nat) 32%nat = piu_zz_lit_segnode_L1_35.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1120%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1120%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1120%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_70.
  rewrite piu_zz_segleaf_1024_71.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_36 : Z := 4710303539%Z.
Lemma piu_zz_segnode_1024_L1_36 : piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 32%nat = piu_zz_lit_segnode_L1_36.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1152%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_72.
  rewrite piu_zz_segleaf_1024_73.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_37 : Z := 14611117446036341%Z.
Lemma piu_zz_segnode_1024_L1_37 : piu_zz_zprod_seg 1024%nat (512%nat + 1184%nat) 32%nat = piu_zz_lit_segnode_L1_37.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1184%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1184%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1184%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_74.
  rewrite piu_zz_segleaf_1024_75.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_38 : Z := 16253166874388357%Z.
Lemma piu_zz_segnode_1024_L1_38 : piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 32%nat = piu_zz_lit_segnode_L1_38.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1216%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_76.
  rewrite piu_zz_segleaf_1024_77.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_39 : Z := 10129165428713%Z.
Lemma piu_zz_segnode_1024_L1_39 : piu_zz_zprod_seg 1024%nat (512%nat + 1248%nat) 32%nat = piu_zz_lit_segnode_L1_39.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1248%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1248%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1248%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_78.
  rewrite piu_zz_segleaf_1024_79.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_40 : Z := 5945916853%Z.
Lemma piu_zz_segnode_1024_L1_40 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 32%nat = piu_zz_lit_segnode_L1_40.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1280%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_80.
  rewrite piu_zz_segleaf_1024_81.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_41 : Z := 3381857%Z.
Lemma piu_zz_segnode_1024_L1_41 : piu_zz_zprod_seg 1024%nat (512%nat + 1312%nat) 32%nat = piu_zz_lit_segnode_L1_41.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1312%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1312%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1312%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_82.
  rewrite piu_zz_segleaf_1024_83.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_42 : Z := 42943091729407914043%Z.
Lemma piu_zz_segnode_1024_L1_42 : piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 32%nat = piu_zz_lit_segnode_L1_42.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1344%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_84.
  rewrite piu_zz_segleaf_1024_85.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_43 : Z := 13100254651999%Z.
Lemma piu_zz_segnode_1024_L1_43 : piu_zz_zprod_seg 1024%nat (512%nat + 1376%nat) 32%nat = piu_zz_lit_segnode_L1_43.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1376%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1376%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1376%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_86.
  rewrite piu_zz_segleaf_1024_87.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_44 : Z := 14193295224877%Z.
Lemma piu_zz_segnode_1024_L1_44 : piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 32%nat = piu_zz_lit_segnode_L1_44.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1408%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_88.
  rewrite piu_zz_segleaf_1024_89.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_45 : Z := 3904567%Z.
Lemma piu_zz_segnode_1024_L1_45 : piu_zz_zprod_seg 1024%nat (512%nat + 1440%nat) 32%nat = piu_zz_lit_segnode_L1_45.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1440%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1440%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1440%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_90.
  rewrite piu_zz_segleaf_1024_91.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_46 : Z := 63677945760295669009%Z.
Lemma piu_zz_segnode_1024_L1_46 : piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 32%nat = piu_zz_lit_segnode_L1_46.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1472%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_92.
  rewrite piu_zz_segleaf_1024_93.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L1_47 : Z := 16914490471129%Z.
Lemma piu_zz_segnode_1024_L1_47 : piu_zz_zprod_seg 1024%nat (512%nat + 1504%nat) 32%nat = piu_zz_lit_segnode_L1_47.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1504%nat) 32%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1504%nat) (16%nat + 16%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1504%nat)%nat 16%nat 16%nat).
  rewrite piu_zz_segleaf_1024_94.
  rewrite piu_zz_segleaf_1024_95.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_0 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_0 : piu_zz_zprod_seg 1024%nat 512%nat 64%nat = piu_zz_lit_segnode_L2_0.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 64%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 32%nat 32%nat).
  rewrite piu_zz_segnode_1024_L1_0.
  rewrite piu_zz_segnode_1024_L1_1.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_1 : Z := 240993413%Z.
Lemma piu_zz_segnode_1024_L2_1 : piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 64%nat = piu_zz_lit_segnode_L2_1.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 64%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 64%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 64%nat)%nat + 32%nat)%nat with (512%nat + 96%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_2.
  rewrite piu_zz_segnode_1024_L1_3.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_2 : Z := 34560265595864823397307%Z.
Lemma piu_zz_segnode_1024_L2_2 : piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 64%nat = piu_zz_lit_segnode_L2_2.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 128%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 128%nat)%nat + 32%nat)%nat with (512%nat + 160%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_4.
  rewrite piu_zz_segnode_1024_L1_5.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_3 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_3 : piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 64%nat = piu_zz_lit_segnode_L2_3.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 192%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 192%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 192%nat)%nat + 32%nat)%nat with (512%nat + 224%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_6.
  rewrite piu_zz_segnode_1024_L1_7.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_4 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_4 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 64%nat = piu_zz_lit_segnode_L2_4.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 256%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 256%nat)%nat + 32%nat)%nat with (512%nat + 288%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_8.
  rewrite piu_zz_segnode_1024_L1_9.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_5 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_5 : piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 64%nat = piu_zz_lit_segnode_L2_5.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 320%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 320%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 320%nat)%nat + 32%nat)%nat with (512%nat + 352%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_10.
  rewrite piu_zz_segnode_1024_L1_11.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_6 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_6 : piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 64%nat = piu_zz_lit_segnode_L2_6.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 384%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 384%nat)%nat + 32%nat)%nat with (512%nat + 416%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_12.
  rewrite piu_zz_segnode_1024_L1_13.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_7 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_7 : piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 64%nat = piu_zz_lit_segnode_L2_7.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 448%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 448%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 448%nat)%nat + 32%nat)%nat with (512%nat + 480%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_14.
  rewrite piu_zz_segnode_1024_L1_15.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_8 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_8 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 64%nat = piu_zz_lit_segnode_L2_8.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 512%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 512%nat)%nat + 32%nat)%nat with (512%nat + 544%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_16.
  rewrite piu_zz_segnode_1024_L1_17.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_9 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_9 : piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 64%nat = piu_zz_lit_segnode_L2_9.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 576%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 576%nat)%nat + 32%nat)%nat with (512%nat + 608%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_18.
  rewrite piu_zz_segnode_1024_L1_19.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_10 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_10 : piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 64%nat = piu_zz_lit_segnode_L2_10.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 640%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 640%nat)%nat + 32%nat)%nat with (512%nat + 672%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_20.
  rewrite piu_zz_segnode_1024_L1_21.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_11 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_11 : piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 64%nat = piu_zz_lit_segnode_L2_11.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 704%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 704%nat)%nat + 32%nat)%nat with (512%nat + 736%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_22.
  rewrite piu_zz_segnode_1024_L1_23.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_12 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_12 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 64%nat = piu_zz_lit_segnode_L2_12.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 768%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 768%nat)%nat + 32%nat)%nat with (512%nat + 800%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_24.
  rewrite piu_zz_segnode_1024_L1_25.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_13 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_13 : piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 64%nat = piu_zz_lit_segnode_L2_13.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 832%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 832%nat)%nat + 32%nat)%nat with (512%nat + 864%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_26.
  rewrite piu_zz_segnode_1024_L1_27.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_14 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_14 : piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 64%nat = piu_zz_lit_segnode_L2_14.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 896%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 896%nat)%nat + 32%nat)%nat with (512%nat + 928%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_28.
  rewrite piu_zz_segnode_1024_L1_29.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_15 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L2_15 : piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 64%nat = piu_zz_lit_segnode_L2_15.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 960%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 960%nat)%nat + 32%nat)%nat with (512%nat + 992%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_30.
  rewrite piu_zz_segnode_1024_L1_31.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_16 : Z := 56865394614567338119872393817%Z.
Lemma piu_zz_segnode_1024_L2_16 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 64%nat = piu_zz_lit_segnode_L2_16.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1024%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1024%nat)%nat + 32%nat)%nat with (512%nat + 1056%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_32.
  rewrite piu_zz_segnode_1024_L1_33.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_17 : Z := 128611106227651318140672686626829%Z.
Lemma piu_zz_segnode_1024_L2_17 : piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 64%nat = piu_zz_lit_segnode_L2_17.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1088%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1088%nat)%nat + 32%nat)%nat with (512%nat + 1120%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_34.
  rewrite piu_zz_segnode_1024_L1_35.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_18 : Z := 68822798214809618534910799%Z.
Lemma piu_zz_segnode_1024_L2_18 : piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 64%nat = piu_zz_lit_segnode_L2_18.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1152%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1152%nat)%nat + 32%nat)%nat with (512%nat + 1184%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_36.
  rewrite piu_zz_segnode_1024_L1_37.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_19 : Z := 164631016011157872351560694541%Z.
Lemma piu_zz_segnode_1024_L2_19 : piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 64%nat = piu_zz_lit_segnode_L2_19.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1216%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1216%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1216%nat)%nat + 32%nat)%nat with (512%nat + 1248%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_38.
  rewrite piu_zz_segnode_1024_L1_39.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_20 : Z := 20108240530736021%Z.
Lemma piu_zz_segnode_1024_L2_20 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 64%nat = piu_zz_lit_segnode_L2_20.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1280%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1280%nat)%nat + 32%nat)%nat with (512%nat + 1312%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_40.
  rewrite piu_zz_segnode_1024_L1_41.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_21 : Z := 562565437199395808055697470121957%Z.
Lemma piu_zz_segnode_1024_L2_21 : piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 64%nat = piu_zz_lit_segnode_L2_21.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1344%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1344%nat)%nat + 32%nat)%nat with (512%nat + 1376%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_42.
  rewrite piu_zz_segnode_1024_L1_43.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_22 : Z := 55418672156312313259%Z.
Lemma piu_zz_segnode_1024_L2_22 : piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 64%nat = piu_zz_lit_segnode_L2_22.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1408%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1408%nat)%nat + 32%nat)%nat with (512%nat + 1440%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_44.
  rewrite piu_zz_segnode_1024_L1_45.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L2_23 : Z := 1077080006783590398598378654541161%Z.
Lemma piu_zz_segnode_1024_L2_23 : piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 64%nat = piu_zz_lit_segnode_L2_23.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) 64%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1472%nat) (32%nat + 32%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1472%nat)%nat 32%nat 32%nat).
  replace ((512%nat + 1472%nat)%nat + 32%nat)%nat with (512%nat + 1504%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L1_46.
  rewrite piu_zz_segnode_1024_L1_47.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_0 : Z := 240993413%Z.
Lemma piu_zz_segnode_1024_L3_0 : piu_zz_zprod_seg 1024%nat 512%nat 128%nat = piu_zz_lit_segnode_L3_0.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 128%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 64%nat 64%nat).
  rewrite piu_zz_segnode_1024_L2_0.
  rewrite piu_zz_segnode_1024_L2_1.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_1 : Z := 34560265595864823397307%Z.
Lemma piu_zz_segnode_1024_L3_1 : piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 128%nat = piu_zz_lit_segnode_L3_1.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 128%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 128%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 128%nat)%nat + 64%nat)%nat with (512%nat + 192%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_2.
  rewrite piu_zz_segnode_1024_L2_3.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_2 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L3_2 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 128%nat = piu_zz_lit_segnode_L3_2.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 256%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 256%nat)%nat + 64%nat)%nat with (512%nat + 320%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_4.
  rewrite piu_zz_segnode_1024_L2_5.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_3 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L3_3 : piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 128%nat = piu_zz_lit_segnode_L3_3.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 384%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 384%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 384%nat)%nat + 64%nat)%nat with (512%nat + 448%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_6.
  rewrite piu_zz_segnode_1024_L2_7.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_4 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L3_4 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 128%nat = piu_zz_lit_segnode_L3_4.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 512%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 512%nat)%nat + 64%nat)%nat with (512%nat + 576%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_8.
  rewrite piu_zz_segnode_1024_L2_9.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_5 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L3_5 : piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 128%nat = piu_zz_lit_segnode_L3_5.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 640%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 640%nat)%nat + 64%nat)%nat with (512%nat + 704%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_10.
  rewrite piu_zz_segnode_1024_L2_11.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_6 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L3_6 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 128%nat = piu_zz_lit_segnode_L3_6.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 768%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 768%nat)%nat + 64%nat)%nat with (512%nat + 832%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_12.
  rewrite piu_zz_segnode_1024_L2_13.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_7 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L3_7 : piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 128%nat = piu_zz_lit_segnode_L3_7.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 896%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 896%nat)%nat + 64%nat)%nat with (512%nat + 960%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_14.
  rewrite piu_zz_segnode_1024_L2_15.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_8 : Z := 7313521307451431107668513506938524668302370407828675205916293%Z.
Lemma piu_zz_segnode_1024_L3_8 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 128%nat = piu_zz_lit_segnode_L3_8.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1024%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 1024%nat)%nat + 64%nat)%nat with (512%nat + 1088%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_16.
  rewrite piu_zz_segnode_1024_L2_17.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_9 : Z := 11330367194835009743332861277376710630880235351921248259%Z.
Lemma piu_zz_segnode_1024_L3_9 : piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 128%nat = piu_zz_lit_segnode_L3_9.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1152%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 1152%nat)%nat + 64%nat)%nat with (512%nat + 1216%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_18.
  rewrite piu_zz_segnode_1024_L2_19.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_10 : Z := 11312201125484120454710612868165762297973842913097%Z.
Lemma piu_zz_segnode_1024_L3_10 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 128%nat = piu_zz_lit_segnode_L3_10.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1280%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 1280%nat)%nat + 64%nat)%nat with (512%nat + 1344%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_20.
  rewrite piu_zz_segnode_1024_L2_21.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L3_11 : Z := 59690343782058438707635233794272350736328901141553699%Z.
Lemma piu_zz_segnode_1024_L3_11 : piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 128%nat = piu_zz_lit_segnode_L3_11.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) 128%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1408%nat) (64%nat + 64%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1408%nat)%nat 64%nat 64%nat).
  replace ((512%nat + 1408%nat)%nat + 64%nat)%nat with (512%nat + 1472%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L2_22.
  rewrite piu_zz_segnode_1024_L2_23.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L4_0 : Z := 8328796360133942477159268938791%Z.
Lemma piu_zz_segnode_1024_L4_0 : piu_zz_zprod_seg 1024%nat 512%nat 256%nat = piu_zz_lit_segnode_L4_0.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 256%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (128%nat + 128%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 128%nat 128%nat).
  rewrite piu_zz_segnode_1024_L3_0.
  rewrite piu_zz_segnode_1024_L3_1.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L4_1 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L4_1 : piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 256%nat = piu_zz_lit_segnode_L4_1.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) 256%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 256%nat) (128%nat + 128%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 256%nat)%nat 128%nat 128%nat).
  replace ((512%nat + 256%nat)%nat + 128%nat)%nat with (512%nat + 384%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L3_2.
  rewrite piu_zz_segnode_1024_L3_3.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L4_2 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L4_2 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 256%nat = piu_zz_lit_segnode_L4_2.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 256%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) (128%nat + 128%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 512%nat)%nat 128%nat 128%nat).
  replace ((512%nat + 512%nat)%nat + 128%nat)%nat with (512%nat + 640%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L3_4.
  rewrite piu_zz_segnode_1024_L3_5.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L4_3 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L4_3 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 256%nat = piu_zz_lit_segnode_L4_3.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 256%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) (128%nat + 128%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 768%nat)%nat 128%nat 128%nat).
  replace ((512%nat + 768%nat)%nat + 128%nat)%nat with (512%nat + 896%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L3_6.
  rewrite piu_zz_segnode_1024_L3_7.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L4_4 : Z := 82864881900674544320472838784478716268775813748807512270236385037584401324739127272741465754824602449200694425983887%Z.
Lemma piu_zz_segnode_1024_L4_4 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 256%nat = piu_zz_lit_segnode_L4_4.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 256%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) (128%nat + 128%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1024%nat)%nat 128%nat 128%nat).
  replace ((512%nat + 1024%nat)%nat + 128%nat)%nat with (512%nat + 1152%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L3_8.
  rewrite piu_zz_segnode_1024_L3_9.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L4_5 : Z := 675229174111935541537857772615646169832571226346907235345531792532681660457577245330290185990815895803%Z.
Lemma piu_zz_segnode_1024_L4_5 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 256%nat = piu_zz_lit_segnode_L4_5.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 256%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) (128%nat + 128%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1280%nat)%nat 128%nat 128%nat).
  replace ((512%nat + 1280%nat)%nat + 128%nat)%nat with (512%nat + 1408%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L3_10.
  rewrite piu_zz_segnode_1024_L3_11.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L5_0 : Z := 8328796360133942477159268938791%Z.
Lemma piu_zz_segnode_1024_L5_0 : piu_zz_zprod_seg 1024%nat 512%nat 512%nat = piu_zz_lit_segnode_L5_0.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 512%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (256%nat + 256%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 256%nat 256%nat).
  rewrite piu_zz_segnode_1024_L4_0.
  rewrite piu_zz_segnode_1024_L4_1.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L5_1 : Z := 1%Z.
Lemma piu_zz_segnode_1024_L5_1 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 512%nat = piu_zz_lit_segnode_L5_1.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 512%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) (256%nat + 256%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 512%nat)%nat 256%nat 256%nat).
  replace ((512%nat + 512%nat)%nat + 256%nat)%nat with (512%nat + 768%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L4_2.
  rewrite piu_zz_segnode_1024_L4_3.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L5_2 : Z := 55952785768675548034361900412474715052995675344307026774161847000580527642131154391315105228623328659734182119927787832095832935246092242086318822758131301712820890655029940504800548928719936786135693259988877548926261%Z.
Lemma piu_zz_segnode_1024_L5_2 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 512%nat = piu_zz_lit_segnode_L5_2.
Proof.
  change (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 512%nat)
    with (piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) (256%nat + 256%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat (512%nat + 1024%nat)%nat 256%nat 256%nat).
  replace ((512%nat + 1024%nat)%nat + 256%nat)%nat with (512%nat + 1280%nat)%nat by lia.
  rewrite piu_zz_segnode_1024_L4_4.
  rewrite piu_zz_segnode_1024_L4_5.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segnode_L6_0 : Z := 8328796360133942477159268938791%Z.
Lemma piu_zz_segnode_1024_L6_0 : piu_zz_zprod_seg 1024%nat 512%nat 1024%nat = piu_zz_lit_segnode_L6_0.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 1024%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (512%nat + 512%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 512%nat 512%nat).
  rewrite piu_zz_segnode_1024_L5_0.
  rewrite piu_zz_segnode_1024_L5_1.
  vm_compute. reflexivity.
Qed.

Definition piu_zz_lit_segroot_1024 : Z := 466019358449499161219416843802933941126124938819010411389576778901548717596419299037600247417718190415659730905352862267026183003996370196407919017272806068866538344582596949009120661077582192368800955531281827217310314763808351876369227770981490451%Z.
Lemma piu_zz_segroot_1024 : piu_zz_zprod_seg 1024%nat 512%nat 1536%nat = piu_zz_lit_segroot_1024.
Proof.
  change (piu_zz_zprod_seg 1024%nat 512%nat 1536%nat)
    with (piu_zz_zprod_seg 1024%nat 512%nat (1024%nat + 512%nat)%nat).
  rewrite (piu_zz_zprod_seg_addsplit 1024%nat 512%nat 1024%nat 512%nat).
  rewrite piu_zz_segnode_1024_L6_0.
  rewrite piu_zz_segnode_1024_L5_2.
  vm_compute. reflexivity.
Qed.
