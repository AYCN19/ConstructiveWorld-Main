(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 15 *)
(** * planb4_calib_chain_build_n15: poleA/poleB chain tails and the assembled abqA/abqB values for point 15, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n15 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 15, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n15 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n15; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n15.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n15.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n15 : list Q :=
  [(-3559056768267159608312900083939025567619589800099423731098583040#1)%Q; (11126396373952931156705346889459214219754074484654279886100234240#1)%Q; (-33550530868323915841227976435707003677720542161868920001763737600#1)%Q; (97554513399333988932177212944655434172650159959354271569281024000#1)%Q; (-273440292975076746474918903114647268782341098368757611112693760000#1)%Q; (738574852879154002419068469242207395764649258251938777425510400000#1)%Q; (-1921666407075495788638654775210681651558881255008450270724096000000#1)%Q; (4814283993728802574442952892563112297013650221403110155223040000000#1)%Q; (-11608006264725356697800594870072057488423819415146745928089600000000#1)%Q; (26924026802886062251445153326008007196067285030241507999744000000000#1)%Q; (-60040482777147310816311466032924713492946277451042452930560000000000#1)%Q; (128651619442098963788053055150492299639630792386878531174400000000000#1)%Q; (-264713904732953650565415080850464354206747128224186105856000000000000#1)%Q; (522671561393765135796039182578109564168907472210273239040000000000000#1)%Q; (-989570306226740660148897232974318837819323413450824089600000000000000#1)%Q; (1795055497149526548221863853656100475940731085341589504000000000000000#1)%Q; (-3117027474805754291606680165427612327078526888087388160000000000000000#1)%Q; (5176313210097780012520587962259265380249693617284710400000000000000000#1)%Q; (-8212354159215015569635765578916331787925942955933696000000000000000000#1)%Q; (12433483129199952952120716514000050232667059299287040000000000000000000#1)%Q; (-17941690071522990408911208595410692436176561346969600000000000000000000#1)%Q; (24643273130843209709595322915581249096530012405760000000000000000000000#1)%Q; (-32170889415084866889074230687828120458955744870400000000000000000000000#1)%Q; (39853081681570997791581236672351572007852179456000000000000000000000000#1)%Q; (-46766081756551562714534686271891006306480291840000000000000000000000000#1)%Q; (51883418774849891893365956627439564919249305600000000000000000000000000#1)%Q; (-54303031338552314709215878794283126881465139200000000000000000000000000#1)%Q; (53491456810769432675969593930591716463607808000000000000000000000000000#1)%Q; (-49460426183700440797110529736338485196881920000000000000000000000000000#1)%Q; (42800975527609938565585834876407697427660800000000000000000000000000000#1)%Q; (-34547548149660819767128306546207707103232000000000000000000000000000000#1)%Q; (25911851110218904414185712621911833313280000000000000000000000000000000#1)%Q; (-17980901938689774323107650727950103347200000000000000000000000000000000#1)%Q; (11486364156744702884412056899868950528000000000000000000000000000000000#1)%Q; (-6715542752506464857259225353467985920000000000000000000000000000000000#1)%Q; (3568835295246408074385246609263820800000000000000000000000000000000000#1)%Q; (-1709856334310161711635721514647552000000000000000000000000000000000000#1)%Q; (731239804049393461219037785620480000000000000000000000000000000000000#1)%Q; (-275724544608367802668404650803200000000000000000000000000000000000000#1)%Q; (90242178932351624170929389568000000000000000000000000000000000000000#1)%Q; (-25115927332721766504406712320000000000000000000000000000000000000000#1)%Q; (5779642469733917812116684800000000000000000000000000000000000000000#1)%Q; (-1055787291382967814848512000000000000000000000000000000000000000000#1)%Q; (143544491931075482746880000000000000000000000000000000000000000000#1)%Q; (-12912720851596686131200000000000000000000000000000000000000000000#1)%Q; (576460752303423488000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n15 : list Q :=
  [(-3559056768267159608312900083939025567619589800099423731098583040#1)%Q; (11126396373952931156705346889459214219754074484654279886100234240#1)%Q; (-33550530868323915841227976435707003677720542161868920001763737600#1)%Q; (97554513399333988932177212944655434172650159959354271569281024000#1)%Q; (-273440292975076746474918903114647268782341098368757611112693760000#1)%Q; (738574852879154002419068469242207395764649258251938777425510400000#1)%Q; (-1921666407075495788638654775210681651558881255008450270724096000000#1)%Q; (4814283993728802574442952892563112297013650221403110155223040000000#1)%Q; (-11608006264725356697800594870072057488423819415146745928089600000000#1)%Q; (26924026802886062251445153326008007196067285030241507999744000000000#1)%Q; (-60040482777147310816311466032924713492946277451042452930560000000000#1)%Q; (128651619442098963788053055150492299639630792386878531174400000000000#1)%Q; (-264713904732953650565415080850464354206747128224186105856000000000000#1)%Q; (522671561393765135796039182578109564168907472210273239040000000000000#1)%Q; (-989570306226740660148897232974318837819323413450824089600000000000000#1)%Q; (1795055497149526548221863853656100475940731085341589504000000000000000#1)%Q; (-3117027474805754291606680165427612327078526888087388160000000000000000#1)%Q; (5176313210097780012520587962259265380249693617284710400000000000000000#1)%Q; (-8212354159215015569635765578916331787925942955933696000000000000000000#1)%Q; (12433483129199952952120716514000050232667059299287040000000000000000000#1)%Q; (-17941690071522990408911208595410692436176561346969600000000000000000000#1)%Q; (24643273130843209709595322915581249096530012405760000000000000000000000#1)%Q; (-32170889415084866889074230687828120458955744870400000000000000000000000#1)%Q; (39853081681570997791581236672351572007852179456000000000000000000000000#1)%Q; (-46766081756551562714534686271891006306480291840000000000000000000000000#1)%Q; (51883418774849891893365956627439564919249305600000000000000000000000000#1)%Q; (-54303031338552314709215878794283126881465139200000000000000000000000000#1)%Q; (53491456810769432675969593930591716463607808000000000000000000000000000#1)%Q; (-49460426183700440797110529736338485196881920000000000000000000000000000#1)%Q; (42800975527609938565585834876407697427660800000000000000000000000000000#1)%Q; (-34547548149660819767128306546207707103232000000000000000000000000000000#1)%Q; (25911851110218904414185712621911833313280000000000000000000000000000000#1)%Q; (-17980901938689774323107650727950103347200000000000000000000000000000000#1)%Q; (11486364156744702884412056899868950528000000000000000000000000000000000#1)%Q; (-6715542752506464857259225353467985920000000000000000000000000000000000#1)%Q; (3568835295246408074385246609263820800000000000000000000000000000000000#1)%Q; (-1709856334310161711635721514647552000000000000000000000000000000000000#1)%Q; (731239804049393461219037785620480000000000000000000000000000000000000#1)%Q; (-275724544608367802668404650803200000000000000000000000000000000000000#1)%Q; (90242178932351624170929389568000000000000000000000000000000000000000#1)%Q; (-25115927332721766504406712320000000000000000000000000000000000000000#1)%Q; (5779642469733917812116684800000000000000000000000000000000000000000#1)%Q; (-1055787291382967814848512000000000000000000000000000000000000000000#1)%Q; (143544491931075482746880000000000000000000000000000000000000000000#1)%Q; (-12912720851596686131200000000000000000000000000000000000000000000#1)%Q; (576460752303423488000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n15 : Z := (1181965522985218301662536739288976383644751764153222479715687163558656737280)%Z.
Definition pb4cwin_litB_n15 : Z := (-376231311094589454491257550691579082748840388718768054022960059926113688000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n15_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              (planb4_g1_shp 15))
       pb4cwin_state_n15_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n15_i1.

Example pb4cwin_remcertA_n15_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_state_n15_i1)
       pb4cwin_state_n15_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n15_i2.

Example pb4cwin_remcertA_n15_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_state_n15_i2)
       pb4cwin_state_n15_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n15_i3.

Example pb4cwin_remcertA_n15_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_state_n15_i3)
       pb4cwin_state_n15_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n15_i4.

Example pb4cwin_remcertA_n15_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_state_n15_i4)
       pb4cwin_state_n15_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n15_i5.

(* poleA channel: assemble the chain tail from the 6 block certificates. *)
Lemma pb4cwin_poleAeq_n15 :
  zzId (planb4_g1_poleA 15) pb4cwin_lit_poleA_n15.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 15 + 1)%nat) with ((8 + 38)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 38%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) (planb4_g1_shp 15))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n15_i0).
  change 38%nat with ((8 + 30)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 30%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat (planb4_g1_shp 15)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n15_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n15_i1).
  change 30%nat with ((8 + 22)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 22%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat pb4cwin_state_n15_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n15_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n15_i2).
  change 22%nat with ((8 + 14)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 14%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat pb4cwin_state_n15_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n15_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n15_i3).
  change (planb4_g1_laur_go (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) 14%nat
             (pb4cwin_rem (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) 8%nat
                pb4cwin_state_n15_i3))
    with (planb4_g1_laur_go (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) (8 + 6)%nat
             (pb4cwin_rem (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) 8%nat
                pb4cwin_state_n15_i3)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 6%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat pb4cwin_state_n15_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n15_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n15_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n15_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n15_i5).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n15.
Lemma pb4cwin_build_poleA_n15 :
  zzId (plq_eqb (planb4_g1_poleA 15) pb4cwin_lit_poleA_n15) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n15).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n15.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n15_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              (planb4_g1_shm 15))
       pb4cwin_stateB_n15_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n15_i1.

Example pb4cwin_remcertB_n15_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_stateB_n15_i1)
       pb4cwin_stateB_n15_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n15_i2.

Example pb4cwin_remcertB_n15_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_stateB_n15_i2)
       pb4cwin_stateB_n15_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n15_i3.

Example pb4cwin_remcertB_n15_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_stateB_n15_i3)
       pb4cwin_stateB_n15_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n15_i4.

Example pb4cwin_remcertB_n15_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 15)
              (hd 0%Q (planb4_g1_denw 15)) 8%nat
              pb4cwin_stateB_n15_i4)
       pb4cwin_stateB_n15_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n15_i5.

(* poleB channel: assemble the chain tail from the 6 block certificates. *)
Lemma pb4cwin_poleBeq_n15 :
  zzId (planb4_g1_poleB 15) pb4cwin_lit_poleB_n15.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 15 + 1)%nat) with ((8 + 38)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 38%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) (planb4_g1_shm 15))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n15_i0).
  change 38%nat with ((8 + 30)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 30%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat (planb4_g1_shm 15)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n15_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n15_i1).
  change 30%nat with ((8 + 22)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 22%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat pb4cwin_stateB_n15_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n15_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n15_i2).
  change 22%nat with ((8 + 14)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 14%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat pb4cwin_stateB_n15_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n15_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n15_i3).
  change (planb4_g1_laur_go (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) 14%nat
             (pb4cwin_rem (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) 8%nat
                pb4cwin_stateB_n15_i3))
    with (planb4_g1_laur_go (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) (8 + 6)%nat
             (pb4cwin_rem (planb4_g1_denw 15) (hd 0%Q (planb4_g1_denw 15)) 8%nat
                pb4cwin_stateB_n15_i3)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 6%nat (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15)))
               (pb4cwin_rem (planb4_g1_denw 15) ((hd 0%Q (planb4_g1_denw 15))) 8%nat pb4cwin_stateB_n15_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n15_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n15_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n15_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n15_i5).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n15.
Lemma pb4cwin_build_poleB_n15 :
  zzId (plq_eqb (planb4_g1_poleB 15) pb4cwin_lit_poleB_n15) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n15).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n15.

Lemma pb4cwin_abqAeq_n15 :
  zzId (planb4_abqA 15) (inject_Z pb4cwin_litA_n15).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n15).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n15).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n15.
Lemma pb4cwin_build_abqA_n15 :
  zzId (Qeq_bool (planb4_abqA 15) (inject_Z pb4cwin_litA_n15)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n15).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n15.

Lemma pb4cwin_abqBeq_n15 :
  zzId (planb4_abqB 15) (inject_Z pb4cwin_litB_n15).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n15).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n15).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n15.
Lemma pb4cwin_build_abqB_n15 :
  zzId (Qeq_bool (planb4_abqB 15) (inject_Z pb4cwin_litB_n15)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n15).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n15.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n15 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n15 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n15.
Definition pb4cwin_winA_n15_i0 : Q := (23790940433484495293794624934747763742766887899542174242615328768#35)%Q.
Example pb4cwin_foldsegA_n15_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n15 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n15_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n15_i0.
Definition pb4cwin_winA_n15_i1 : Q := (116934741992504658898782060315252838216989960574375274775800971264#45045)%Q.
Example pb4cwin_foldsegA_n15_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n15 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n15_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n15_i1.
Definition pb4cwin_winA_n15_i2 : Q := (-41057722340498296112387485785311713477664780992741281930149888#8415)%Q.
Example pb4cwin_foldsegA_n15_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n15 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n15_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n15_i2.
Definition pb4cwin_winA_n15_i3 : Q := (49472823541216246777298339226219297354120835200263510818816#126945)%Q.
Example pb4cwin_foldsegA_n15_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n15 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n15_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n15_i3.
Definition pb4cwin_winA_n15_i4 : Q := (-522728137037446273870760702629813650277386005524774912#858585)%Q.
Example pb4cwin_foldsegA_n15_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n15 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n15_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n15_i4.
Definition pb4cwin_winA_n15_i5 : Q := (11189372936781100161131471869110461000732114944#6108795)%Q.
Example pb4cwin_foldsegA_n15_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n15 ((40 + t)%nat))
                   6%nat))
       pb4cwin_winA_n15_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n15_i5.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n15 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n15 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n15.
Definition pb4cwin_winB_n15_i0 : Q := (39961033405556355339998748744440096238890561836562801979295793152#105)%Q.
Example pb4cwin_foldsegB_n15_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n15 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n15_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n15_i0.
Definition pb4cwin_winB_n15_i1 : Q := (-11701489323080438899592671823882386438461652196643169258694508544#45045)%Q.
Example pb4cwin_foldsegB_n15_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n15 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n15_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n15_i1.
Definition pb4cwin_winB_n15_i2 : Q := (20906774132287918017735657327841069026194123770710701637632#935)%Q.
Example pb4cwin_foldsegB_n15_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n15 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n15_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n15_i2.
Definition pb4cwin_winB_n15_i3 : Q := (-12485420320874112282304201819546687522301880900599676928#126945)%Q.
Example pb4cwin_foldsegB_n15_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n15 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n15_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n15_i3.
Definition pb4cwin_winB_n15_i4 : Q := (6484187808477076022570315842249722976212019576832#726495)%Q.
Example pb4cwin_foldsegB_n15_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n15 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n15_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n15_i4.
Definition pb4cwin_winB_n15_i5 : Q := (-9733693440022563752417850432564444004352#6108795)%Q.
Example pb4cwin_foldsegB_n15_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n15 ((40 + t)%nat))
                   6%nat))
       pb4cwin_winB_n15_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n15_i5.