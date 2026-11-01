(* piu_zz_tau_enclosure_phi1024.v — consumer 六片链末棒四片机械拆分（KB10 影子链候选案）第 2/4 片·真依赖图波 1。
   使命：承载 zzPhi_1024 单引理巨证体（原 β 区 L811-3133，语句边界不可内切区整块迁移）。
   依赖：piu_zz_tau_enclosure_bank4（直接式 Require Import·伞链 bank3..1/base 传递覆盖 inPn_1024 表与 lcm 面）、
   piu_zz_poincare_engine（zz_in_Pn/zprod_seg）、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   真图证据：对 head 六名 grep 零命中（不依赖 head，与 head 同属波 1 互独立）。
   对标：piu_zz_tau_enclosure 原单件（六片链末棒再拆，语句面逐字节等价）。
   构造性：本片语句零假设、零公理。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_enclosure_phi1024.v *)
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

