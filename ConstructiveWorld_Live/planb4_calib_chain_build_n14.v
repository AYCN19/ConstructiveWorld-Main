(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 14 *)
(** * planb4_calib_chain_build_n14: poleA/poleB chain tails and the assembled abqA/abqB values for point 14, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n14 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 14, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n14 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n14; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n14.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n14.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n14 : list Q :=
  [(168574852705104139519285748660695105397073547602236308193280#1)%Q; (-526777636594448611262902884653465061214962033966520614256640#1)%Q; (1583674923827418556763851647836349014372680410215065688473600#1)%Q; (-4578966923619977122588091508469980666392943941711030124544000#1)%Q; (12728384889999075234301166894664948851325143774201968066560000#1)%Q; (-34002210952805755183475917711962762377614465459473822515200000#1)%Q; (87251729991867185990032184047439778336012448610713075712000000#1)%Q; (-214960708438723868268096625265492791152789844957782343680000000#1)%Q; (508190230171150431820458590573950227029656916997649203200000000#1)%Q; (-1152171927306879976524021350644872340790531997963386880000000000#1)%Q; (2503511010973526917807228016049060759137953770666721280000000000#1)%Q; (-5209722064020067379904471942236085350346727712043827200000000000#1)%Q; (10374712220126122498515713120353563683196627476021248000000000000#1)%Q; (-19754557177578587304938353237404100317264865426145280000000000000#1)%Q; (35932587618822976067728767041588953895715415156326400000000000000#1)%Q; (-62374011570194460573656885150719454656317699915776000000000000000#1)%Q; (103213641537788394473384548441888553441350951895040000000000000000#1)%Q; (-162618171594123957830750687714506535949624252825600000000000000000#1)%Q; (243630199698094959869848174471479175701992570880000000000000000000#1)%Q; (-346577482409456212153389030930284869514900275200000000000000000000#1)%Q; (467404386916105043670073071443267689711140864000000000000000000000#1)%Q; (-596562040204464282477434422646280282250936320000000000000000000000#1)%Q; (719213498321246921715114213804133694885068800000000000000000000000#1)%Q; (-817295510210213083444683555954609453268992000000000000000000000000#1)%Q; (873366255041114063833401332608079411281920000000000000000000000000#1)%Q; (-875321408680077954120653763670645407744000000000000000000000000000#1)%Q; (820372608638165853654252532376735527731200000000000000000000000000#1)%Q; (-716607859527182540759535936242542706688000000000000000000000000000#1)%Q; (581215774912567421489647597164135710720000000000000000000000000000#1)%Q; (-435814050961305616059284565688896716800000000000000000000000000000#1)%Q; (300612805922919966143835567623766016000000000000000000000000000000#1)%Q; (-189641506051572634928593988915036160000000000000000000000000000000#1)%Q; (108669098128573927920075792606822400000000000000000000000000000000#1)%Q; (-56101411384384290382051536797696000000000000000000000000000000000#1)%Q; (25835872653524081692164017356800000000000000000000000000000000000#1)%Q; (-10483575403916433523015575142400000000000000000000000000000000000#1)%Q; (3690137841145227585861451776000000000000000000000000000000000000#1)%Q; (-1103865604493094351106211840000000000000000000000000000000000000#1)%Q; (272862150469524438541926400000000000000000000000000000000000000#1)%Q; (-53510834023693740408832000000000000000000000000000000000000000#1)%Q; (7805999162128733306880000000000000000000000000000000000000000#1)%Q; (-753001857696346931200000000000000000000000000000000000000000#1)%Q; (36028797018963968000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n14 : list Q :=
  [(168574852705104139519285748660695105397073547602236308193280#1)%Q; (-526777636594448611262902884653465061214962033966520614256640#1)%Q; (1583674923827418556763851647836349014372680410215065688473600#1)%Q; (-4578966923619977122588091508469980666392943941711030124544000#1)%Q; (12728384889999075234301166894664948851325143774201968066560000#1)%Q; (-34002210952805755183475917711962762377614465459473822515200000#1)%Q; (87251729991867185990032184047439778336012448610713075712000000#1)%Q; (-214960708438723868268096625265492791152789844957782343680000000#1)%Q; (508190230171150431820458590573950227029656916997649203200000000#1)%Q; (-1152171927306879976524021350644872340790531997963386880000000000#1)%Q; (2503511010973526917807228016049060759137953770666721280000000000#1)%Q; (-5209722064020067379904471942236085350346727712043827200000000000#1)%Q; (10374712220126122498515713120353563683196627476021248000000000000#1)%Q; (-19754557177578587304938353237404100317264865426145280000000000000#1)%Q; (35932587618822976067728767041588953895715415156326400000000000000#1)%Q; (-62374011570194460573656885150719454656317699915776000000000000000#1)%Q; (103213641537788394473384548441888553441350951895040000000000000000#1)%Q; (-162618171594123957830750687714506535949624252825600000000000000000#1)%Q; (243630199698094959869848174471479175701992570880000000000000000000#1)%Q; (-346577482409456212153389030930284869514900275200000000000000000000#1)%Q; (467404386916105043670073071443267689711140864000000000000000000000#1)%Q; (-596562040204464282477434422646280282250936320000000000000000000000#1)%Q; (719213498321246921715114213804133694885068800000000000000000000000#1)%Q; (-817295510210213083444683555954609453268992000000000000000000000000#1)%Q; (873366255041114063833401332608079411281920000000000000000000000000#1)%Q; (-875321408680077954120653763670645407744000000000000000000000000000#1)%Q; (820372608638165853654252532376735527731200000000000000000000000000#1)%Q; (-716607859527182540759535936242542706688000000000000000000000000000#1)%Q; (581215774912567421489647597164135710720000000000000000000000000000#1)%Q; (-435814050961305616059284565688896716800000000000000000000000000000#1)%Q; (300612805922919966143835567623766016000000000000000000000000000000#1)%Q; (-189641506051572634928593988915036160000000000000000000000000000000#1)%Q; (108669098128573927920075792606822400000000000000000000000000000000#1)%Q; (-56101411384384290382051536797696000000000000000000000000000000000#1)%Q; (25835872653524081692164017356800000000000000000000000000000000000#1)%Q; (-10483575403916433523015575142400000000000000000000000000000000000#1)%Q; (3690137841145227585861451776000000000000000000000000000000000000#1)%Q; (-1103865604493094351106211840000000000000000000000000000000000000#1)%Q; (272862150469524438541926400000000000000000000000000000000000000#1)%Q; (-53510834023693740408832000000000000000000000000000000000000000#1)%Q; (7805999162128733306880000000000000000000000000000000000000000#1)%Q; (-753001857696346931200000000000000000000000000000000000000000#1)%Q; (36028797018963968000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n14 : Z := (110069922310893678941469937990244572398332323518748057182206767713484800)%Z.
Definition pb4cwin_litB_n14 : Z := (-35036344443039248439608946386559898932830127241407563578345605396984000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n14_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              (planb4_g1_shp 14))
       pb4cwin_state_n14_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n14_i1.

Example pb4cwin_remcertA_n14_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_state_n14_i1)
       pb4cwin_state_n14_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n14_i2.

Example pb4cwin_remcertA_n14_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_state_n14_i2)
       pb4cwin_state_n14_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n14_i3.

Example pb4cwin_remcertA_n14_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_state_n14_i3)
       pb4cwin_state_n14_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n14_i4.

Example pb4cwin_remcertA_n14_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_state_n14_i4)
       pb4cwin_state_n14_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n14_i5.

(* poleA channel: assemble the chain tail from the 6 block certificates. *)
Lemma pb4cwin_poleAeq_n14 :
  zzId (planb4_g1_poleA 14) pb4cwin_lit_poleA_n14.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 14 + 1)%nat) with ((8 + 35)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 35%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) (planb4_g1_shp 14))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n14_i0).
  change 35%nat with ((8 + 27)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 27%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat (planb4_g1_shp 14)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n14_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n14_i1).
  change 27%nat with ((8 + 19)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 19%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat pb4cwin_state_n14_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n14_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n14_i2).
  change 19%nat with ((8 + 11)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 11%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat pb4cwin_state_n14_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n14_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n14_i3).
  change (planb4_g1_laur_go (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) 11%nat
             (pb4cwin_rem (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) 8%nat
                pb4cwin_state_n14_i3))
    with (planb4_g1_laur_go (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) (8 + 3)%nat
             (pb4cwin_rem (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) 8%nat
                pb4cwin_state_n14_i3)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 3%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat pb4cwin_state_n14_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n14_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n14_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n14_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n14_i5).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n14.
Lemma pb4cwin_build_poleA_n14 :
  zzId (plq_eqb (planb4_g1_poleA 14) pb4cwin_lit_poleA_n14) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n14).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n14.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n14_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              (planb4_g1_shm 14))
       pb4cwin_stateB_n14_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n14_i1.

Example pb4cwin_remcertB_n14_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_stateB_n14_i1)
       pb4cwin_stateB_n14_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n14_i2.

Example pb4cwin_remcertB_n14_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_stateB_n14_i2)
       pb4cwin_stateB_n14_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n14_i3.

Example pb4cwin_remcertB_n14_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_stateB_n14_i3)
       pb4cwin_stateB_n14_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n14_i4.

Example pb4cwin_remcertB_n14_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 14)
              (hd 0%Q (planb4_g1_denw 14)) 8%nat
              pb4cwin_stateB_n14_i4)
       pb4cwin_stateB_n14_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n14_i5.

(* poleB channel: assemble the chain tail from the 6 block certificates. *)
Lemma pb4cwin_poleBeq_n14 :
  zzId (planb4_g1_poleB 14) pb4cwin_lit_poleB_n14.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 14 + 1)%nat) with ((8 + 35)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 35%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) (planb4_g1_shm 14))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n14_i0).
  change 35%nat with ((8 + 27)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 27%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat (planb4_g1_shm 14)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n14_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n14_i1).
  change 27%nat with ((8 + 19)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 19%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat pb4cwin_stateB_n14_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n14_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n14_i2).
  change 19%nat with ((8 + 11)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 11%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat pb4cwin_stateB_n14_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n14_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n14_i3).
  change (planb4_g1_laur_go (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) 11%nat
             (pb4cwin_rem (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) 8%nat
                pb4cwin_stateB_n14_i3))
    with (planb4_g1_laur_go (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) (8 + 3)%nat
             (pb4cwin_rem (planb4_g1_denw 14) (hd 0%Q (planb4_g1_denw 14)) 8%nat
                pb4cwin_stateB_n14_i3)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 3%nat (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14)))
               (pb4cwin_rem (planb4_g1_denw 14) ((hd 0%Q (planb4_g1_denw 14))) 8%nat pb4cwin_stateB_n14_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n14_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n14_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n14_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n14_i5).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n14.
Lemma pb4cwin_build_poleB_n14 :
  zzId (plq_eqb (planb4_g1_poleB 14) pb4cwin_lit_poleB_n14) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n14).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n14.

Lemma pb4cwin_abqAeq_n14 :
  zzId (planb4_abqA 14) (inject_Z pb4cwin_litA_n14).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n14).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n14).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n14.
Lemma pb4cwin_build_abqA_n14 :
  zzId (Qeq_bool (planb4_abqA 14) (inject_Z pb4cwin_litA_n14)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n14).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n14.

Lemma pb4cwin_abqBeq_n14 :
  zzId (planb4_abqB 14) (inject_Z pb4cwin_litB_n14).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n14).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n14).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n14.
Lemma pb4cwin_build_abqB_n14 :
  zzId (Qeq_bool (planb4_abqB 14) (inject_Z pb4cwin_litB_n14)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n14).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n14.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n14 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n14 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n14.
Definition pb4cwin_winA_n14_i0 : Q := (-1127562091706905410713191403795507603279885486300336041754624#35)%Q.
Example pb4cwin_foldsegA_n14_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n14 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n14_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n14_i0.
Definition pb4cwin_winA_n14_i1 : Q := (-132724473471659737076702163818915589835416956978635667931136#1155)%Q.
Example pb4cwin_foldsegA_n14_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n14 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n14_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n14_i1.
Definition pb4cwin_winA_n14_i2 : Q := (583038221679785872996076870573835701248481177548428935168#3553)%Q.
Example pb4cwin_foldsegA_n14_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n14 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n14_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n14_i2.
Definition pb4cwin_winA_n14_i3 : Q := (-233033111742916071644690301783470312382273119875760128#31465)%Q.
Example pb4cwin_foldsegA_n14_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n14 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n14_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n14_i3.
Definition pb4cwin_winA_n14_i4 : Q := (4685320966395634997496830312158927344353104887808#1254855)%Q.
Example pb4cwin_foldsegA_n14_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n14 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n14_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n14_i4.
Definition pb4cwin_winA_n14_i5 : Q := (-2421478948674381861151233594638729216#4305)%Q.
Example pb4cwin_foldsegA_n14_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n14 ((40 + t)%nat))
                   3%nat))
       pb4cwin_winA_n14_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n14_i5.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n14 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n14 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n14.
Definition pb4cwin_winB_n14_i0 : Q := (-1893191948359389506663859480503517703561962258611288309497856#105)%Q.
Example pb4cwin_foldsegB_n14_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n14 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n14_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n14_i0.
Definition pb4cwin_winB_n14_i1 : Q := (13182811787271873070105327361229256110882161941152826130432#1155)%Q.
Example pb4cwin_foldsegB_n14_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n14 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n14_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n14_i1.
Definition pb4cwin_winB_n14_i2 : Q := (-2654178961221574881171685526759732874509546002237620224#3553)%Q.
Example pb4cwin_foldsegB_n14_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n14 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n14_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n14_i2.
Definition pb4cwin_winB_n14_i3 : Q := (175878350046242374776464128155225127505720986566656#94395)%Q.
Example pb4cwin_foldsegB_n14_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n14 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n14_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n14_i3.
Definition pb4cwin_winB_n14_i4 : Q := (-253502216473807628246222463688136617673883648#4601135)%Q.
Example pb4cwin_foldsegB_n14_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n14 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n14_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n14_i4.
Definition pb4cwin_winB_n14_i5 : Q := (739595312494402692950012198912#1435)%Q.
Example pb4cwin_foldsegB_n14_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n14 ((40 + t)%nat))
                   3%nat))
       pb4cwin_winB_n14_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n14_i5.