(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 10 *)
(** * planb4_calib_chain_build_n10: poleA/poleB chain tails and the assembled abqA/abqB values for point 10, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n10 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 10, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n10 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n10; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n10.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n10.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n10 : list Q :=
  [(874347976850586842097029058168227964649472#1)%Q; (-2725259809326305706064281212209934190510080#1)%Q; (8046450147140115500177823955616825291571200#1)%Q; (-22489628999139746183207853895788819120128000#1)%Q; (59456942663911836036247542926595032350720000#1)%Q; (-148550607273574403821433694686557293772800000#1)%Q; (350389723177503804233786074230440329216000000#1)%Q; (-779338202358761723148912970280090992640000000#1)%Q; (1632389578621946648239776995133200793600000000#1)%Q; (-3215111479443741191745526675709886464000000000#1)%Q; (5944432849991074858678725735989903360000000000#1)%Q; (-10297710097825798315627879232385843200000000000#1)%Q; (16678354593227719070044182982688768000000000000#1)%Q; (-25193657991207869960386186124984320000000000000#1)%Q; (35396049449508849779475435277516800000000000000#1)%Q; (-46107975082659603762872154324992000000000000000#1)%Q; (55486583248923010381545713172480000000000000000#1)%Q; (-61430547298139687591970288435200000000000000000#1)%Q; (62268422053131564248358453248000000000000000000#1)%Q; (-57462042024149672710708920320000000000000000000#1)%Q; (47952781314531324284685516800000000000000000000#1)%Q; (-35898366050606924244713472000000000000000000000#1)%Q; (23873066281124375067361280000000000000000000000#1)%Q; (-13932383947783184528179200000000000000000000000#1)%Q; (7025706370849579204608000000000000000000000000#1)%Q; (-2999488454613448785920000000000000000000000000#1)%Q; (1054289731573828812800000000000000000000000000#1)%Q; (-292950579569754112000000000000000000000000000#1)%Q; (60341198132346880000000000000000000000000000#1)%Q; (-8191361626931200000000000000000000000000000#1)%Q; (549755813888000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n10 : list Q :=
  [(874347976850586842097029058168227964649472#1)%Q; (-2725259809326305706064281212209934190510080#1)%Q; (8046450147140115500177823955616825291571200#1)%Q; (-22489628999139746183207853895788819120128000#1)%Q; (59456942663911836036247542926595032350720000#1)%Q; (-148550607273574403821433694686557293772800000#1)%Q; (350389723177503804233786074230440329216000000#1)%Q; (-779338202358761723148912970280090992640000000#1)%Q; (1632389578621946648239776995133200793600000000#1)%Q; (-3215111479443741191745526675709886464000000000#1)%Q; (5944432849991074858678725735989903360000000000#1)%Q; (-10297710097825798315627879232385843200000000000#1)%Q; (16678354593227719070044182982688768000000000000#1)%Q; (-25193657991207869960386186124984320000000000000#1)%Q; (35396049449508849779475435277516800000000000000#1)%Q; (-46107975082659603762872154324992000000000000000#1)%Q; (55486583248923010381545713172480000000000000000#1)%Q; (-61430547298139687591970288435200000000000000000#1)%Q; (62268422053131564248358453248000000000000000000#1)%Q; (-57462042024149672710708920320000000000000000000#1)%Q; (47952781314531324284685516800000000000000000000#1)%Q; (-35898366050606924244713472000000000000000000000#1)%Q; (23873066281124375067361280000000000000000000000#1)%Q; (-13932383947783184528179200000000000000000000000#1)%Q; (7025706370849579204608000000000000000000000000#1)%Q; (-2999488454613448785920000000000000000000000000#1)%Q; (1054289731573828812800000000000000000000000000#1)%Q; (-292950579569754112000000000000000000000000000#1)%Q; (60341198132346880000000000000000000000000000#1)%Q; (-8191361626931200000000000000000000000000000#1)%Q; (549755813888000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n10 : Z := (1354133153103621265219656119343503679599270690816)%Z.
Definition pb4cwin_litB_n10 : Z := (-431033969842111272679713625800004336371600806400)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n10_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 10)
              (hd 0%Q (planb4_g1_denw 10)) 8%nat
              (planb4_g1_shp 10))
       pb4cwin_state_n10_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n10_i1.

Example pb4cwin_remcertA_n10_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 10)
              (hd 0%Q (planb4_g1_denw 10)) 8%nat
              pb4cwin_state_n10_i1)
       pb4cwin_state_n10_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n10_i2.

Example pb4cwin_remcertA_n10_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 10)
              (hd 0%Q (planb4_g1_denw 10)) 8%nat
              pb4cwin_state_n10_i2)
       pb4cwin_state_n10_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n10_i3.

(* poleA channel: assemble the chain tail from the 4 block certificates. *)
Lemma pb4cwin_poleAeq_n10 :
  zzId (planb4_g1_poleA 10) pb4cwin_lit_poleA_n10.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 10 + 1)%nat) with ((8 + 23)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 23%nat (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10))) (planb4_g1_shp 10))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n10_i0).
  change 23%nat with ((8 + 15)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 15%nat (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10)))
               (pb4cwin_rem (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10))) 8%nat (planb4_g1_shp 10)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n10_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n10_i1).
  change 15%nat with ((8 + 7)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 7%nat (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10)))
               (pb4cwin_rem (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10))) 8%nat pb4cwin_state_n10_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n10_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n10_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n10_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n10_i3).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n10.
Lemma pb4cwin_build_poleA_n10 :
  zzId (plq_eqb (planb4_g1_poleA 10) pb4cwin_lit_poleA_n10) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n10).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n10.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n10_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 10)
              (hd 0%Q (planb4_g1_denw 10)) 8%nat
              (planb4_g1_shm 10))
       pb4cwin_stateB_n10_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n10_i1.

Example pb4cwin_remcertB_n10_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 10)
              (hd 0%Q (planb4_g1_denw 10)) 8%nat
              pb4cwin_stateB_n10_i1)
       pb4cwin_stateB_n10_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n10_i2.

Example pb4cwin_remcertB_n10_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 10)
              (hd 0%Q (planb4_g1_denw 10)) 8%nat
              pb4cwin_stateB_n10_i2)
       pb4cwin_stateB_n10_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n10_i3.

(* poleB channel: assemble the chain tail from the 4 block certificates. *)
Lemma pb4cwin_poleBeq_n10 :
  zzId (planb4_g1_poleB 10) pb4cwin_lit_poleB_n10.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 10 + 1)%nat) with ((8 + 23)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 23%nat (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10))) (planb4_g1_shm 10))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n10_i0).
  change 23%nat with ((8 + 15)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 15%nat (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10)))
               (pb4cwin_rem (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10))) 8%nat (planb4_g1_shm 10)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n10_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n10_i1).
  change 15%nat with ((8 + 7)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 7%nat (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10)))
               (pb4cwin_rem (planb4_g1_denw 10) ((hd 0%Q (planb4_g1_denw 10))) 8%nat pb4cwin_stateB_n10_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n10_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n10_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n10_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n10_i3).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n10.
Lemma pb4cwin_build_poleB_n10 :
  zzId (plq_eqb (planb4_g1_poleB 10) pb4cwin_lit_poleB_n10) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n10).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n10.

Lemma pb4cwin_abqAeq_n10 :
  zzId (planb4_abqA 10) (inject_Z pb4cwin_litA_n10).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n10).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n10).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n10.
Lemma pb4cwin_build_abqA_n10 :
  zzId (Qeq_bool (planb4_abqA 10) (inject_Z pb4cwin_litA_n10)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n10).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n10.

Lemma pb4cwin_abqBeq_n10 :
  zzId (planb4_abqB 10) (inject_Z pb4cwin_litB_n10).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n10).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n10).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n10.
Lemma pb4cwin_build_abqB_n10 :
  zzId (Qeq_bool (planb4_abqB 10) (inject_Z pb4cwin_litB_n10)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n10).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n10.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n10 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n10 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n10.
Definition pb4cwin_winA_n10_i0 : Q := (-5868573965250171842079500695599606499639296#35)%Q.
Example pb4cwin_foldsegA_n10_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n10 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n10_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n10_i0.
Definition pb4cwin_winA_n10_i1 : Q := (-2538423787903143054007476065991347293650944#6435)%Q.
Example pb4cwin_foldsegA_n10_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n10 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n10_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n10_i1.
Definition pb4cwin_winA_n10_i2 : Q := (7690619150198240969993313700641014546432#79695)%Q.
Example pb4cwin_foldsegA_n10_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n10 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n10_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n10_i2.
Definition pb4cwin_winA_n10_i3 : Q := (-16710388657737934988863022666088448#254475)%Q.
Example pb4cwin_foldsegA_n10_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n10 ((24 + t)%nat))
                   7%nat))
       pb4cwin_winA_n10_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n10_i3.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n10 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n10 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n10.
Definition pb4cwin_winB_n10_i0 : Q := (-9833592239480269362089427731014779733540864#105)%Q.
Example pb4cwin_foldsegB_n10_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n10 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n10_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n10_i0.
Definition pb4cwin_winB_n10_i1 : Q := (240854906859500093696962527790366434787328#6435)%Q.
Example pb4cwin_foldsegB_n10_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n10 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n10_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n10_i1.
Definition pb4cwin_winB_n10_i2 : Q := (-3739370323966823630710916172048498688#8855)%Q.
Example pb4cwin_foldsegB_n10_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n10 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n10_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n10_i2.
Definition pb4cwin_winB_n10_i3 : Q := (4132009976308644171869958701056#254475)%Q.
Example pb4cwin_foldsegB_n10_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n10 ((24 + t)%nat))
                   7%nat))
       pb4cwin_winB_n10_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n10_i3.