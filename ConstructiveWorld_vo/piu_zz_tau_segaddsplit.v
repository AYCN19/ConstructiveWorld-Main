(* piu_zz_tau_segaddsplit.v — shared additive-splitting lemma for segment products.
   1. Mission: for all n x a b : nat, piu_zz_zprod_seg n x (a + b) =
      piu_zz_zprod_seg n x a * piu_zz_zprod_seg n (x + a) b, universal in n;
      the single registered statement behind the leaf lanes, the merge tree
      and the zzPhi_1024 consumer proof.
   2. Dependencies: piu_zz_tau_enclosure_bank4, piu_zz_poincare_engine,
      piu_zz_padic_clearing; Stdlib QArith, ZArith, Arith, PArith, Lia, List.
   3. References: consolidates the inline copies of this identity in
      piu_zz_tau_enclosure_head.v and piu_zz_tau_enclosure_phi1024_slim.v.
   4. Constructivity: constructive rewrite proof (induction on b, cbn on
      piu_zz_zprod_seg, nat arithmetic by lia); assumption-free,
      extraction-clean; n is fixed by introduction, not inducted.
   5. Build: coqc -time -native-compiler no -q
      -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
      -Q . "" piu_zz_tau_segaddsplit.v
      (cpu_guard_v3-wrapped; .vos/.vok stubs follow). *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

Lemma piu_zz_zprod_seg_addsplit : forall n x a b : nat,
  piu_zz_zprod_seg n x (a + b)%nat
  = piu_zz_zprod_seg n x a * piu_zz_zprod_seg n (x + a)%nat b.
Proof.
  intros n x a b. induction b as [|c IH].
  - cbn [piu_zz_zprod_seg]. rewrite Nat.add_0_r, Z.mul_1_r. reflexivity.
  - replace (a + S c)%nat with (S (a + c))%nat by lia.
    cbn [piu_zz_zprod_seg].
    replace (S (x + a + c))%nat with (S (x + (a + c)))%nat by lia.
    rewrite IH. rewrite Z.mul_assoc. reflexivity.
Qed.
