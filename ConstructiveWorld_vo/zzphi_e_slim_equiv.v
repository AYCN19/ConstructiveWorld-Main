(* zzphi_e_slim_equiv.v — merge-citation twin of piu_zz_tau_enclosure_phi1024_slim.v.
   1. Mission: statement face identical to piu_zz_tau_enclosure_phi1024_slim.v
      (piu_zz_lit_Phibase_1024, piu_zz_Phibase_1024, piu_zz_lit_Phi_1024,
      piu_zz_zzPhi_1024); the zzPhi_1024 proof cites the balanced merge root
      piu_zz_segroot_1024 instead of the linear 389-step split chain.
   2. Dependencies: piu_zz_tau_enclosure_bank4, piu_zz_tau_hb_wave1..8,
      piu_zz_tau_segtree_1024_merge, piu_zz_poincare_engine,
      piu_zz_padic_clearing; Stdlib QArith, ZArith, Arith, PArith, Lia, List.
   3. References: piu_zz_tau_enclosure_phi1024_slim.v zzPhi_1024
      (statement-identical twin); piu_zz_tau_segtree_1024_merge.v
      piu_zz_segroot_1024.
   4. Constructivity: assumption-free, zero classical logic; the proof body is
      five rewrites plus one small vm_compute normalisation
      (extraction-clean); statement faces are byte-identical to the twin.
   5. Build: coqc -time -native-compiler no -q
      -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
      -Q . "" zzphi_e_slim_equiv.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Import piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Require Import piu_zz_tau_segtree_1024_merge.
Definition piu_zz_lit_Phibase_1024 : Z := 2676424583214047812886498025277%Z.
Lemma piu_zz_Phibase_1024 : zz_prodf 1024 512 = piu_zz_lit_Phibase_1024.
Proof. vm_compute. reflexivity. Qed.

Definition piu_zz_lit_Phi_1024 : Z := 1247265667207878743564411746639630465837680150403967205716038259439454683881228755169778368855472723728093086558056377142445765017511506443750179754482867083617905365271468235023582470869802861523534438052014857889150368227303863291555158486883485396025660116039962900929732129927%Z.
Lemma piu_zz_zzPhi_1024 : zz_Phi 1024 = piu_zz_lit_Phi_1024.
Proof.
  unfold zz_Phi.
  replace (2 * 1024)%nat with (512 + 1536)%nat by lia.
  rewrite (piu_zz_zprod_merge 1024%nat 512%nat 1536%nat).
  rewrite piu_zz_Phibase_1024.
  rewrite piu_zz_segroot_1024.
  vm_compute. reflexivity.
Qed.
