(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 7 *)
(** * planb4_calib_chain_build_n7: poleA/poleB chain tails and the assembled abqA/abqB values for point 7, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n7 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 7, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n7 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n7; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n7.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n7.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n7 : list Q :=
  [(-100076266910126057403290746880#1)%Q; (310732602124807401154670755840#1)%Q; (-892896046246608086610739200000#1)%Q; (2371017570195404849556226048000#1)%Q; (-5807692332787132981953167360000#1)%Q; (13093594175889249266093260800000#1)%Q; (-27099780721585320666071040000000#1)%Q; (51330294854780544488570880000000#1)%Q; (-88649883675004900055449600000000#1)%Q; (138985562233529369100288000000000#1)%Q; (-196773595089792401408000000000000#1)%Q; (249990884712903606272000000000000#1)%Q; (-282816679845291884544000000000000#1)%Q; (282227523158907289600000000000000#1)%Q; (-245502194567924940800000000000000#1)%Q; (183343751870021632000000000000000#1)%Q; (-115212415171297280000000000000000#1)%Q; (59256197454233600000000000000000#1)%Q; (-23957730230272000000000000000000#1)%Q; (7141725306880000000000000000000#1)%Q; (-1395864371200000000000000000000#1)%Q; (134217728000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n7 : list Q :=
  [(-100076266910126057403290746880#1)%Q; (310732602124807401154670755840#1)%Q; (-892896046246608086610739200000#1)%Q; (2371017570195404849556226048000#1)%Q; (-5807692332787132981953167360000#1)%Q; (13093594175889249266093260800000#1)%Q; (-27099780721585320666071040000000#1)%Q; (51330294854780544488570880000000#1)%Q; (-88649883675004900055449600000000#1)%Q; (138985562233529369100288000000000#1)%Q; (-196773595089792401408000000000000#1)%Q; (249990884712903606272000000000000#1)%Q; (-282816679845291884544000000000000#1)%Q; (282227523158907289600000000000000#1)%Q; (-245502194567924940800000000000000#1)%Q; (183343751870021632000000000000000#1)%Q; (-115212415171297280000000000000000#1)%Q; (59256197454233600000000000000000#1)%Q; (-23957730230272000000000000000000#1)%Q; (7141725306880000000000000000000#1)%Q; (-1395864371200000000000000000000#1)%Q; (134217728000000000000000000000#1)%Q].
Definition pb4cwin_litA_n7 : Z := (1347172462953838057496096076267520)%Z.
Definition pb4cwin_litB_n7 : Z := (-428818313352773146987517929596000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n7_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 7)
              (hd 0%Q (planb4_g1_denw 7)) 8%nat
              (planb4_g1_shp 7))
       pb4cwin_state_n7_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n7_i1.

Example pb4cwin_remcertA_n7_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 7)
              (hd 0%Q (planb4_g1_denw 7)) 8%nat
              pb4cwin_state_n7_i1)
       pb4cwin_state_n7_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n7_i2.

(* poleA channel: assemble the chain tail from the 3 block certificates. *)
Lemma pb4cwin_poleAeq_n7 :
  zzId (planb4_g1_poleA 7) pb4cwin_lit_poleA_n7.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 7 + 1)%nat) with ((8 + 14)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 14%nat (planb4_g1_denw 7) ((hd 0%Q (planb4_g1_denw 7))) (planb4_g1_shp 7))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n7_i0).
  change 14%nat with ((8 + 6)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 6%nat (planb4_g1_denw 7) ((hd 0%Q (planb4_g1_denw 7)))
               (pb4cwin_rem (planb4_g1_denw 7) ((hd 0%Q (planb4_g1_denw 7))) 8%nat (planb4_g1_shp 7)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n7_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n7_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n7_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n7_i2).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n7.
Lemma pb4cwin_build_poleA_n7 :
  zzId (plq_eqb (planb4_g1_poleA 7) pb4cwin_lit_poleA_n7) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n7).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n7.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n7_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 7)
              (hd 0%Q (planb4_g1_denw 7)) 8%nat
              (planb4_g1_shm 7))
       pb4cwin_stateB_n7_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n7_i1.

Example pb4cwin_remcertB_n7_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 7)
              (hd 0%Q (planb4_g1_denw 7)) 8%nat
              pb4cwin_stateB_n7_i1)
       pb4cwin_stateB_n7_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n7_i2.

(* poleB channel: assemble the chain tail from the 3 block certificates. *)
Lemma pb4cwin_poleBeq_n7 :
  zzId (planb4_g1_poleB 7) pb4cwin_lit_poleB_n7.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 7 + 1)%nat) with ((8 + 14)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 14%nat (planb4_g1_denw 7) ((hd 0%Q (planb4_g1_denw 7))) (planb4_g1_shm 7))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n7_i0).
  change 14%nat with ((8 + 6)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 6%nat (planb4_g1_denw 7) ((hd 0%Q (planb4_g1_denw 7)))
               (pb4cwin_rem (planb4_g1_denw 7) ((hd 0%Q (planb4_g1_denw 7))) 8%nat (planb4_g1_shm 7)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n7_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n7_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n7_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n7_i2).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n7.
Lemma pb4cwin_build_poleB_n7 :
  zzId (plq_eqb (planb4_g1_poleB 7) pb4cwin_lit_poleB_n7) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n7).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n7.

Lemma pb4cwin_abqAeq_n7 :
  zzId (planb4_abqA 7) (inject_Z pb4cwin_litA_n7).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n7).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n7).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n7.
Lemma pb4cwin_build_abqA_n7 :
  zzId (Qeq_bool (planb4_abqA 7) (inject_Z pb4cwin_litA_n7)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n7).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n7.

Lemma pb4cwin_abqBeq_n7 :
  zzId (planb4_abqB 7) (inject_Z pb4cwin_litB_n7).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n7).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n7).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n7.
Lemma pb4cwin_build_abqB_n7 :
  zzId (Qeq_bool (planb4_abqB 7) (inject_Z pb4cwin_litB_n7)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n7).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n7.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n7 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n7 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n7.
Definition pb4cwin_winA_n7_i0 : Q := (2024203919624845005040523542528#105)%Q.
Example pb4cwin_foldsegA_n7_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n7 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n7_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n7_i0.
Definition pb4cwin_winA_n7_i1 : Q := (354003685354612653222264832#15)%Q.
Example pb4cwin_foldsegA_n7_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n7 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n7_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n7_i1.
Definition pb4cwin_winA_n7_i2 : Q := (-23073230639968701957275648#101745)%Q.
Example pb4cwin_foldsegA_n7_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n7 ((16 + t)%nat))
                   6%nat))
       pb4cwin_winA_n7_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n7_i2.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n7 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n7 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n7.
Definition pb4cwin_winB_n7_i0 : Q := (1128116959946973685230972698624#105)%Q.
Example pb4cwin_foldsegB_n7_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n7 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n7_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n7_i0.
Definition pb4cwin_winB_n7_i1 : Q := (-31361836800429773428883456#15)%Q.
Example pb4cwin_foldsegB_n7_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n7 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n7_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n7_i1.
Definition pb4cwin_winB_n7_i2 : Q := (31791485808826825179136#33915)%Q.
Example pb4cwin_foldsegB_n7_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n7 ((16 + t)%nat))
                   6%nat))
       pb4cwin_winB_n7_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n7_i2.