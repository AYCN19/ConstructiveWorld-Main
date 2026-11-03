(* zzphi_e_leaf91.v — literal certificate for leaf 91 of 96, the balanced-tree
   factorisation of zzPhi_1024.
   1. Mission: piu_zz_zprod_seg 1024%nat ((512%nat + 1440%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA91
      (= 3904567%Z) — the 16-wide segment product of the 1024 face starting at
      index ((512%nat + 1440%nat)%nat + 16%nat) (statement carried as a Set-level Z equality).
   2. Dependencies: piu_zz_tau_enclosure_bank4, piu_zz_poincare_engine,
      piu_zz_padic_clearing; Stdlib QArith, ZArith, Arith, PArith, Lia, List.
   3. References: statement twin of the inline certificate
      piu_zz_segleaf_1024_91 in piu_zz_tau_segtree_1024_leaf_h.v;
      certificate shape follows piu_zz_tau_enclosure_literals.v.
   4. Constructivity: assumption-free, zero classical logic; the proof body
      is vm_compute normalisation closed by reflexivity, so the certificate
      value is machine-checked at compile time (extraction-clean).
   5. Build: coqc -time -native-compiler no -q
      -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
      -Q . "" zzphi_e_leaf91.v  (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

Definition piu_zz_lit_segA91 : Z := 3904567%Z.
Lemma piu_zz_segleaf_1024_91 : piu_zz_zprod_seg 1024%nat ((512%nat + 1440%nat)%nat + 16%nat) 16%nat = piu_zz_lit_segA91.
Proof. vm_compute. reflexivity. Qed.
