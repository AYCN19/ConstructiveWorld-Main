(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 8 *)
(** * planb4_calib_chain_build_n8: poleA/poleB chain tails and the assembled abqA/abqB values for point 8, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n8 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 8, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n8 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n8; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n8.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
Import ListNotations.
Require Import zzm1_gauss.
Require Import zzm2_qpoly.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_laur_extract.
Require Import planb4_g1_rs_channel.
Require Import planb4_g1_ab_def.
Require Import planb4_calib_chain_glue_qred.
Require Import planb4_calib_chain_glue_laur.
Require Import planb4_calib_chain_step_n8.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n8 : list Q :=
  [(2046283012133312604327022962933760#1)%Q; (-6363800697698561499548941643939840#1)%Q; (18494512380903943930656534927769600#1)%Q; (-50172986806077662072864688308224000#1)%Q; (126889871978094446006994374492160000#1)%Q; (-298701524927294022027896160256000000#1)%Q; (653291957630005266384473292800000000#1)%Q; (-1324676358764277504717461913600000000#1)%Q; (2484084651755841477010259968000000000#1)%Q; (-4295591585019756914021498880000000000#1)%Q; (6826830968087243310864793600000000000#1)%Q; (-9932276831277622316184371200000000000#1)%Q; (13167665655405618825003008000000000000#1)%Q; (-15820874870062525102161920000000000000#1)%Q; (17115419708533529955532800000000000000#1)%Q; (-16541228267448534302720000000000000000#1)%Q; (14144597671621888573440000000000000000#1)%Q; (-10573974375597971865600000000000000000#1)%Q; (6805215076652417024000000000000000000#1)%Q; (-3694969964000706560000000000000000000#1)%Q; (1646150369148928000000000000000000000#1)%Q; (-577885702193152000000000000000000000#1)%Q; (149915833466880000000000000000000000#1)%Q; (-25555055411200000000000000000000000#1)%Q; (2147483648000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n8 : list Q :=
  [(2046283012133312604327022962933760#1)%Q; (-6363800697698561499548941643939840#1)%Q; (18494512380903943930656534927769600#1)%Q; (-50172986806077662072864688308224000#1)%Q; (126889871978094446006994374492160000#1)%Q; (-298701524927294022027896160256000000#1)%Q; (653291957630005266384473292800000000#1)%Q; (-1324676358764277504717461913600000000#1)%Q; (2484084651755841477010259968000000000#1)%Q; (-4295591585019756914021498880000000000#1)%Q; (6826830968087243310864793600000000000#1)%Q; (-9932276831277622316184371200000000000#1)%Q; (13167665655405618825003008000000000000#1)%Q; (-15820874870062525102161920000000000000#1)%Q; (17115419708533529955532800000000000000#1)%Q; (-16541228267448534302720000000000000000#1)%Q; (14144597671621888573440000000000000000#1)%Q; (-10573974375597971865600000000000000000#1)%Q; (6805215076652417024000000000000000000#1)%Q; (-3694969964000706560000000000000000000#1)%Q; (1646150369148928000000000000000000000#1)%Q; (-577885702193152000000000000000000000#1)%Q; (149915833466880000000000000000000000#1)%Q; (-25555055411200000000000000000000000#1)%Q; (2147483648000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n8 : Z := (68100481825849942917038479960850196070400)%Z.
Definition pb4cwin_litB_n8 : Z := (-21677056619047600469847519849617811672000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n8_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 8)
              (hd 0%Q (planb4_g1_denw 8)) 8%nat
              (planb4_g1_shp 8))
       pb4cwin_state_n8_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n8_i1.

Example pb4cwin_remcertA_n8_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 8)
              (hd 0%Q (planb4_g1_denw 8)) 8%nat
              pb4cwin_state_n8_i1)
       pb4cwin_state_n8_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n8_i2.

Example pb4cwin_remcertA_n8_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 8)
              (hd 0%Q (planb4_g1_denw 8)) 8%nat
              pb4cwin_state_n8_i2)
       pb4cwin_state_n8_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n8_i3.

(* poleA channel: assemble the chain tail from the 4 block certificates. *)
Lemma pb4cwin_poleAeq_n8 :
  zzId (planb4_g1_poleA 8) pb4cwin_lit_poleA_n8.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 8 + 1)%nat) with ((8 + 17)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 17%nat (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8))) (planb4_g1_shp 8))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n8_i0).
  change 17%nat with ((8 + 9)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 9%nat (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8)))
               (pb4cwin_rem (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8))) 8%nat (planb4_g1_shp 8)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n8_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n8_i1).
  change 9%nat with ((8 + 1)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 1%nat (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8)))
               (pb4cwin_rem (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8))) 8%nat pb4cwin_state_n8_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n8_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n8_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n8_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n8_i3).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n8.
Lemma pb4cwin_build_poleA_n8 :
  zzId (plq_eqb (planb4_g1_poleA 8) pb4cwin_lit_poleA_n8) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n8).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n8.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n8_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 8)
              (hd 0%Q (planb4_g1_denw 8)) 8%nat
              (planb4_g1_shm 8))
       pb4cwin_stateB_n8_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n8_i1.

Example pb4cwin_remcertB_n8_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 8)
              (hd 0%Q (planb4_g1_denw 8)) 8%nat
              pb4cwin_stateB_n8_i1)
       pb4cwin_stateB_n8_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n8_i2.

Example pb4cwin_remcertB_n8_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 8)
              (hd 0%Q (planb4_g1_denw 8)) 8%nat
              pb4cwin_stateB_n8_i2)
       pb4cwin_stateB_n8_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n8_i3.

(* poleB channel: assemble the chain tail from the 4 block certificates. *)
Lemma pb4cwin_poleBeq_n8 :
  zzId (planb4_g1_poleB 8) pb4cwin_lit_poleB_n8.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 8 + 1)%nat) with ((8 + 17)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 17%nat (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8))) (planb4_g1_shm 8))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n8_i0).
  change 17%nat with ((8 + 9)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 9%nat (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8)))
               (pb4cwin_rem (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8))) 8%nat (planb4_g1_shm 8)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n8_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n8_i1).
  change 9%nat with ((8 + 1)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 1%nat (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8)))
               (pb4cwin_rem (planb4_g1_denw 8) ((hd 0%Q (planb4_g1_denw 8))) 8%nat pb4cwin_stateB_n8_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n8_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n8_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n8_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n8_i3).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n8.
Lemma pb4cwin_build_poleB_n8 :
  zzId (plq_eqb (planb4_g1_poleB 8) pb4cwin_lit_poleB_n8) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n8).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n8.

Lemma pb4cwin_abqAeq_n8 :
  zzId (planb4_abqA 8) (inject_Z pb4cwin_litA_n8).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n8).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n8).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n8.
Lemma pb4cwin_build_abqA_n8 :
  zzId (Qeq_bool (planb4_abqA 8) (inject_Z pb4cwin_litA_n8)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n8).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n8.

Lemma pb4cwin_abqBeq_n8 :
  zzId (planb4_abqB 8) (inject_Z pb4cwin_litB_n8).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n8).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n8).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n8.
Lemma pb4cwin_build_abqB_n8 :
  zzId (Qeq_bool (planb4_abqB 8) (inject_Z pb4cwin_litB_n8)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n8).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n8.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n8 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n8 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n8.
Definition pb4cwin_winA_n8_i0 : Q := (-2754342080819947646239090348654592#7)%Q.
Example pb4cwin_foldsegA_n8_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n8 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n8_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n8_i0.
Definition pb4cwin_winA_n8_i1 : Q := (-20971679200767845604676000022528#33)%Q.
Example pb4cwin_foldsegA_n8_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n8 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n8_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n8_i1.
Definition pb4cwin_winA_n8_i2 : Q := (7175137831986515544637876207616#270963)%Q.
Example pb4cwin_foldsegA_n8_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n8 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n8_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n8_i2.
Definition pb4cwin_winA_n8_i3 : Q := (-21655384020221952#1)%Q.
Example pb4cwin_foldsegA_n8_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n8 ((24 + t)%nat))
                   1%nat))
       pb4cwin_winA_n8_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n8_i3.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n8 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n8 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n8.
Definition pb4cwin_winB_n8_i0 : Q := (-4608908629370933886133168450306048#21)%Q.
Example pb4cwin_foldsegB_n8_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n8 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n8_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n8_i0.
Definition pb4cwin_winB_n8_i1 : Q := (1911527343352192478244883136512#33)%Q.
Example pb4cwin_foldsegB_n8_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n8 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n8_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n8_i1.
Definition pb4cwin_winB_n8_i2 : Q := (-10120571672160604089320734720#90321)%Q.
Example pb4cwin_foldsegB_n8_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n8 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n8_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n8_i2.
Definition pb4cwin_winB_n8_i3 : Q := (5286958989312#1)%Q.
Example pb4cwin_foldsegB_n8_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n8 ((24 + t)%nat))
                   1%nat))
       pb4cwin_winB_n8_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n8_i3.