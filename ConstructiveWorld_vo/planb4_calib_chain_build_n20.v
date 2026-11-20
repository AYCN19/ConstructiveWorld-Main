(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 20 *)
(** * planb4_calib_chain_build_n20: poleA/poleB chain tails and the assembled abqA/abqB values for point 20, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n20 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 20, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n20 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n20; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n20.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n20.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n20 : list Q :=
  [(15361235589782386004143633158309742714572782354450543176961681032243849904441205456896#1)%Q; (-48094266927400651843316313567976263371181551345086892259046155622049057677429922856960#1)%Q; (146557434919092159819047330392650880562454568351070821804947897032315352450251253350400#1)%Q; (-434613382758562900437672310396067675980608231714912862639142547506537530080201015296000#1)%Q; (1254026202514967791181467111487342045483132207997969127045477828016795637881073827840000#1)%Q; (-3519979058540938531949779982887794573036538501042129966591659399383490771868555673600000#1)%Q; (9609904545629104827386465470789496061469356848311260459393505655426991988097941504000000#1)%Q; (-25512489740505688316938760733663469366502393440284227339865471202510846083161128960000000#1)%Q; (65848225011640143629975684499966893914602969834143131064607250099069542509995622400000000#1)%Q; (-165191850856808463958191333205976395779841441244229503618837566972997856800014336000000000#1)%Q; (402694055924202651837816215524960970225163616902458887046581749158765354696048640000000000#1)%Q; (-953641563605150037336996060697903946675658950746247298414315291756307420912025600000000000#1)%Q; (2193269434680441873899528047807955631796287898555990169761176705752345696272384000000000000#1)%Q; (-4897348456100665689037039281968607475834195145723407859752151040080692704706560000000000000#1)%Q; (10613264368087678822782528938758373571450956330000298140569216618452341909094400000000000000#1)%Q; (-22315345666950605688659160326747582167358804384197433591838299655028925792256000000000000000#1)%Q; (45505413489909397541226088772259419225298710788208830419312932878832946380800000000000000000#1)%Q; (-89961226034166253829216516817733816551343708265650502304730349021314416640000000000000000000#1)%Q; (172344666940719695129309989759672751154299328824943655312345539639089561600000000000000000000#1)%Q; (-319813255187432131258657554692995884586615076353684533750605948125184000000000000000000000000#1)%Q; (574572743261600913314629088658458843050190994604288177138155330996273152000000000000000000000#1)%Q; (-998905524831229928012135096883511266664578352534525187801842605017268224000000000000000000000#1)%Q; (1679583867386737231540416796824897216271144110450495969307156438329589760000000000000000000000#1)%Q; (-2729788962262749380884000881503663935430135731293418050307058053834342400000000000000000000000#1)%Q; (4285907823004090985532665330539403883804568625976349118024379411726336000000000000000000000000#1)%Q; (-6496239924849577118347872718239824132012840221488239255349438437130240000000000000000000000000#1)%Q; (9499206307323065483730670708963500879601817583751393659858896656793600000000000000000000000000#1)%Q; (-13390570891882437973377615950823297257684641768403462500372252196864000000000000000000000000000#1)%Q; (18182602622447830220639357244519079362250287891267954451186198773760000000000000000000000000000#1)%Q; (-23762553817084861134368447941228831322554339900902579543820625510400000000000000000000000000000#1)%Q; (29862027690683074091424118513074170450420181424879182820143005696000000000000000000000000000000#1)%Q; (-36050823275733061731617573790285090675458501663180465482906992640000000000000000000000000000000#1)%Q; (41766700852570606522661944207582315906022475654873730233506201600000000000000000000000000000000#1)%Q; (-46385174468467256759662483368210842212429169016012168656584704000000000000000000000000000000000#1)%Q; (49321818957863145970312582945532647308881028310829169073192960000000000000000000000000000000000#1)%Q; (-50146925627253716790791478719043445261575153034236862555750400000000000000000000000000000000000#1)%Q; (48683531845938508617826280249800878444413262589496156749824000000000000000000000000000000000000#1)%Q; (-45059522981334670300960143515223575711534368304595636060160000000000000000000000000000000000000#1)%Q; (39694686748280210003150384391996594140249162595841762918400000000000000000000000000000000000000#1)%Q; (-33222048356626502268744316785920870215331544497878204416000000000000000000000000000000000000000#1)%Q; (26363235222628893580371594249267279495877844717629603840000000000000000000000000000000000000000#1)%Q; (-19792068835908951919910955588612816119607609319961395200000000000000000000000000000000000000000#1)%Q; (14023104923831401180237770985823734771533699348430848000000000000000000000000000000000000000000#1)%Q; (-9351471902137423774595266656285481247088116781547520000000000000000000000000000000000000000000#1)%Q; (5851708329132582110765837951746975537451840097484800000000000000000000000000000000000000000000#1)%Q; (-3424310432207515765762625168093864912552116355072000000000000000000000000000000000000000000000#1)%Q; (1866712297633189128828541984287238743874684846080000000000000000000000000000000000000000000000#1)%Q; (-943813981707263190898004396499308416922235699200000000000000000000000000000000000000000000000#1)%Q; (440355899482194535642701261867747515782135808000000000000000000000000000000000000000000000000#1)%Q; (-188485066162521851195518482098761661698539520000000000000000000000000000000000000000000000000#1)%Q; (73502774937310414120384108919845798333644800000000000000000000000000000000000000000000000000#1)%Q; (-25900260259633990130985161955661297221632000000000000000000000000000000000000000000000000000#1)%Q; (8164640380715176009337937867038187847680000000000000000000000000000000000000000000000000000#1)%Q; (-2274211880384955023130757444284920627200000000000000000000000000000000000000000000000000000#1)%Q; (551022594126963478646370218203414528000000000000000000000000000000000000000000000000000000#1)%Q; (-113768092985819517807433827976478720000000000000000000000000000000000000000000000000000000#1)%Q; (19461315709896442571622498225356800000000000000000000000000000000000000000000000000000000#1)%Q; (-2648000287675483571232452902912000000000000000000000000000000000000000000000000000000000#1)%Q; (268689808038449407224321146880000000000000000000000000000000000000000000000000000000000#1)%Q; (-18073441003238706161857331200000000000000000000000000000000000000000000000000000000000#1)%Q; (604462909807314587353088000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n20 : list Q :=
  [(15361235589782386004143633158309742714572782354450543176961681032243849904441205456896#1)%Q; (-48094266927400651843316313567976263371181551345086892259046155622049057677429922856960#1)%Q; (146557434919092159819047330392650880562454568351070821804947897032315352450251253350400#1)%Q; (-434613382758562900437672310396067675980608231714912862639142547506537530080201015296000#1)%Q; (1254026202514967791181467111487342045483132207997969127045477828016795637881073827840000#1)%Q; (-3519979058540938531949779982887794573036538501042129966591659399383490771868555673600000#1)%Q; (9609904545629104827386465470789496061469356848311260459393505655426991988097941504000000#1)%Q; (-25512489740505688316938760733663469366502393440284227339865471202510846083161128960000000#1)%Q; (65848225011640143629975684499966893914602969834143131064607250099069542509995622400000000#1)%Q; (-165191850856808463958191333205976395779841441244229503618837566972997856800014336000000000#1)%Q; (402694055924202651837816215524960970225163616902458887046581749158765354696048640000000000#1)%Q; (-953641563605150037336996060697903946675658950746247298414315291756307420912025600000000000#1)%Q; (2193269434680441873899528047807955631796287898555990169761176705752345696272384000000000000#1)%Q; (-4897348456100665689037039281968607475834195145723407859752151040080692704706560000000000000#1)%Q; (10613264368087678822782528938758373571450956330000298140569216618452341909094400000000000000#1)%Q; (-22315345666950605688659160326747582167358804384197433591838299655028925792256000000000000000#1)%Q; (45505413489909397541226088772259419225298710788208830419312932878832946380800000000000000000#1)%Q; (-89961226034166253829216516817733816551343708265650502304730349021314416640000000000000000000#1)%Q; (172344666940719695129309989759672751154299328824943655312345539639089561600000000000000000000#1)%Q; (-319813255187432131258657554692995884586615076353684533750605948125184000000000000000000000000#1)%Q; (574572743261600913314629088658458843050190994604288177138155330996273152000000000000000000000#1)%Q; (-998905524831229928012135096883511266664578352534525187801842605017268224000000000000000000000#1)%Q; (1679583867386737231540416796824897216271144110450495969307156438329589760000000000000000000000#1)%Q; (-2729788962262749380884000881503663935430135731293418050307058053834342400000000000000000000000#1)%Q; (4285907823004090985532665330539403883804568625976349118024379411726336000000000000000000000000#1)%Q; (-6496239924849577118347872718239824132012840221488239255349438437130240000000000000000000000000#1)%Q; (9499206307323065483730670708963500879601817583751393659858896656793600000000000000000000000000#1)%Q; (-13390570891882437973377615950823297257684641768403462500372252196864000000000000000000000000000#1)%Q; (18182602622447830220639357244519079362250287891267954451186198773760000000000000000000000000000#1)%Q; (-23762553817084861134368447941228831322554339900902579543820625510400000000000000000000000000000#1)%Q; (29862027690683074091424118513074170450420181424879182820143005696000000000000000000000000000000#1)%Q; (-36050823275733061731617573790285090675458501663180465482906992640000000000000000000000000000000#1)%Q; (41766700852570606522661944207582315906022475654873730233506201600000000000000000000000000000000#1)%Q; (-46385174468467256759662483368210842212429169016012168656584704000000000000000000000000000000000#1)%Q; (49321818957863145970312582945532647308881028310829169073192960000000000000000000000000000000000#1)%Q; (-50146925627253716790791478719043445261575153034236862555750400000000000000000000000000000000000#1)%Q; (48683531845938508617826280249800878444413262589496156749824000000000000000000000000000000000000#1)%Q; (-45059522981334670300960143515223575711534368304595636060160000000000000000000000000000000000000#1)%Q; (39694686748280210003150384391996594140249162595841762918400000000000000000000000000000000000000#1)%Q; (-33222048356626502268744316785920870215331544497878204416000000000000000000000000000000000000000#1)%Q; (26363235222628893580371594249267279495877844717629603840000000000000000000000000000000000000000#1)%Q; (-19792068835908951919910955588612816119607609319961395200000000000000000000000000000000000000000#1)%Q; (14023104923831401180237770985823734771533699348430848000000000000000000000000000000000000000000#1)%Q; (-9351471902137423774595266656285481247088116781547520000000000000000000000000000000000000000000#1)%Q; (5851708329132582110765837951746975537451840097484800000000000000000000000000000000000000000000#1)%Q; (-3424310432207515765762625168093864912552116355072000000000000000000000000000000000000000000000#1)%Q; (1866712297633189128828541984287238743874684846080000000000000000000000000000000000000000000000#1)%Q; (-943813981707263190898004396499308416922235699200000000000000000000000000000000000000000000000#1)%Q; (440355899482194535642701261867747515782135808000000000000000000000000000000000000000000000000#1)%Q; (-188485066162521851195518482098761661698539520000000000000000000000000000000000000000000000000#1)%Q; (73502774937310414120384108919845798333644800000000000000000000000000000000000000000000000000#1)%Q; (-25900260259633990130985161955661297221632000000000000000000000000000000000000000000000000000#1)%Q; (8164640380715176009337937867038187847680000000000000000000000000000000000000000000000000000#1)%Q; (-2274211880384955023130757444284920627200000000000000000000000000000000000000000000000000000#1)%Q; (551022594126963478646370218203414528000000000000000000000000000000000000000000000000000000#1)%Q; (-113768092985819517807433827976478720000000000000000000000000000000000000000000000000000000#1)%Q; (19461315709896442571622498225356800000000000000000000000000000000000000000000000000000000#1)%Q; (-2648000287675483571232452902912000000000000000000000000000000000000000000000000000000000#1)%Q; (268689808038449407224321146880000000000000000000000000000000000000000000000000000000000#1)%Q; (-18073441003238706161857331200000000000000000000000000000000000000000000000000000000000#1)%Q; (604462909807314587353088000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n20 : Z := (93232664665822790411471596328104499563210171013636577034977993606796446907707569624049009266486411264)%Z.
Definition pb4cwin_litB_n20 : Z := (-29676878878389574560264477825441844590152912980892376452653443318779146931314816868512983024539865600)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n20_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              (planb4_g1_shp 20))
       pb4cwin_state_n20_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i1.

Example pb4cwin_remcertA_n20_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_state_n20_i1)
       pb4cwin_state_n20_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i2.

Example pb4cwin_remcertA_n20_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_state_n20_i2)
       pb4cwin_state_n20_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i3.

Example pb4cwin_remcertA_n20_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_state_n20_i3)
       pb4cwin_state_n20_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i4.

Example pb4cwin_remcertA_n20_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_state_n20_i4)
       pb4cwin_state_n20_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i5.

Example pb4cwin_remcertA_n20_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_state_n20_i5)
       pb4cwin_state_n20_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i6.

Example pb4cwin_remcertA_n20_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_state_n20_i6)
       pb4cwin_state_n20_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n20_i7.

(* poleA channel: assemble the chain tail from the 8 block certificates. *)
Lemma pb4cwin_poleAeq_n20 :
  zzId (planb4_g1_poleA 20) pb4cwin_lit_poleA_n20.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 20 + 1)%nat) with ((8 + 53)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 53%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) (planb4_g1_shp 20))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i0).
  change 53%nat with ((8 + 45)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 45%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat (planb4_g1_shp 20)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i1).
  change 45%nat with ((8 + 37)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 37%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_state_n20_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i2).
  change 37%nat with ((8 + 29)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 29%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_state_n20_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i3).
  change 29%nat with ((8 + 21)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 21%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_state_n20_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i4).
  change 21%nat with ((8 + 13)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 13%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_state_n20_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) 13%nat
             (pb4cwin_rem (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) 8%nat
                pb4cwin_state_n20_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) (8 + 5)%nat
             (pb4cwin_rem (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) 8%nat
                pb4cwin_state_n20_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 5%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_state_n20_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n20_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n20_i7).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n20.
Lemma pb4cwin_build_poleA_n20 :
  zzId (plq_eqb (planb4_g1_poleA 20) pb4cwin_lit_poleA_n20) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n20).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n20.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n20_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              (planb4_g1_shm 20))
       pb4cwin_stateB_n20_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i1.

Example pb4cwin_remcertB_n20_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_stateB_n20_i1)
       pb4cwin_stateB_n20_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i2.

Example pb4cwin_remcertB_n20_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_stateB_n20_i2)
       pb4cwin_stateB_n20_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i3.

Example pb4cwin_remcertB_n20_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_stateB_n20_i3)
       pb4cwin_stateB_n20_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i4.

Example pb4cwin_remcertB_n20_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_stateB_n20_i4)
       pb4cwin_stateB_n20_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i5.

Example pb4cwin_remcertB_n20_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_stateB_n20_i5)
       pb4cwin_stateB_n20_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i6.

Example pb4cwin_remcertB_n20_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 20)
              (hd 0%Q (planb4_g1_denw 20)) 8%nat
              pb4cwin_stateB_n20_i6)
       pb4cwin_stateB_n20_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n20_i7.

(* poleB channel: assemble the chain tail from the 8 block certificates. *)
Lemma pb4cwin_poleBeq_n20 :
  zzId (planb4_g1_poleB 20) pb4cwin_lit_poleB_n20.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 20 + 1)%nat) with ((8 + 53)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 53%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) (planb4_g1_shm 20))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i0).
  change 53%nat with ((8 + 45)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 45%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat (planb4_g1_shm 20)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i1).
  change 45%nat with ((8 + 37)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 37%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_stateB_n20_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i2).
  change 37%nat with ((8 + 29)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 29%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_stateB_n20_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i3).
  change 29%nat with ((8 + 21)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 21%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_stateB_n20_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i4).
  change 21%nat with ((8 + 13)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 13%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_stateB_n20_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) 13%nat
             (pb4cwin_rem (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) 8%nat
                pb4cwin_stateB_n20_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) (8 + 5)%nat
             (pb4cwin_rem (planb4_g1_denw 20) (hd 0%Q (planb4_g1_denw 20)) 8%nat
                pb4cwin_stateB_n20_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 5%nat (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20)))
               (pb4cwin_rem (planb4_g1_denw 20) ((hd 0%Q (planb4_g1_denw 20))) 8%nat pb4cwin_stateB_n20_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n20_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n20_i7).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n20.
Lemma pb4cwin_build_poleB_n20 :
  zzId (plq_eqb (planb4_g1_poleB 20) pb4cwin_lit_poleB_n20) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n20).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n20.

Lemma pb4cwin_abqAeq_n20 :
  zzId (planb4_abqA 20) (inject_Z pb4cwin_litA_n20).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n20).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n20).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n20.
Lemma pb4cwin_build_abqA_n20 :
  zzId (Qeq_bool (planb4_abqA 20) (inject_Z pb4cwin_litA_n20)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n20).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n20.

Lemma pb4cwin_abqBeq_n20 :
  zzId (planb4_abqB 20) (inject_Z pb4cwin_litB_n20).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n20).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n20).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n20.
Lemma pb4cwin_build_abqB_n20 :
  zzId (Qeq_bool (planb4_abqB 20) (inject_Z pb4cwin_litB_n20)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n20).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n20.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n20 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n20 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n20.
Definition pb4cwin_winA_n20_i0 : Q := (-102446430300469375720035500422069686997472957766217914870378622655105179757397212659712#35)%Q.
Example pb4cwin_foldsegA_n20_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i0.
Definition pb4cwin_winA_n20_i1 : Q := (-49123317594594198573314358158355967408767451538073175514823876592071258073995528896512#3465)%Q.
Example pb4cwin_foldsegA_n20_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i1.
Definition pb4cwin_winA_n20_i2 : Q := (346806227705063588136326081117693072808026796765630443194217961458141688922855952089088#5148297)%Q.
Example pb4cwin_foldsegA_n20_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i2.
Definition pb4cwin_winA_n20_i3 : Q := (-655745238292996376348765350579282391590120615589979613543803755553250453709914112#19575)%Q.
Example pb4cwin_foldsegA_n20_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i3.
Definition pb4cwin_winA_n20_i4 : Q := (15106023333029710329950096740733986289541327648989130092091879759967323947008#11305)%Q.
Example pb4cwin_foldsegA_n20_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i4.
Definition pb4cwin_winA_n20_i5 : Q := (-316993132940467407935349847327517324742452825153713977075063638680817106944#161063595)%Q.
Example pb4cwin_foldsegA_n20_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i5.
Definition pb4cwin_winA_n20_i6 : Q := (-36815944485900224912089944654492691957853731917204933176568768888832#327806325)%Q.
Example pb4cwin_foldsegA_n20_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winA_n20_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i6.
Definition pb4cwin_winA_n20_i7 : Q := (44875902387214703841797922449609520326089535779715940352#487635)%Q.
Example pb4cwin_foldsegA_n20_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n20 ((56 + t)%nat))
                   5%nat))
       pb4cwin_winA_n20_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n20_i7.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n20 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n20 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n20.
Definition pb4cwin_winB_n20_i0 : Q := (-172341583942590385139331518289739004257511881276215870775350968509246259016969767354368#105)%Q.
Example pb4cwin_foldsegB_n20_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i0.
Definition pb4cwin_winB_n20_i1 : Q := (5040480021680600225542560379421080429202010971022850160284917439443545676133917786112#3465)%Q.
Example pb4cwin_foldsegB_n20_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i1.
Definition pb4cwin_winB_n20_i2 : Q := (-542323597569472347658467601904421893872367168610704201132560838612939898862048378880#1716099)%Q.
Example pb4cwin_foldsegB_n20_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i2.
Definition pb4cwin_winB_n20_i3 : Q := (167406013957205325943245372167483980509803071894192192474565177735750157860864#19575)%Q.
Example pb4cwin_foldsegB_n20_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i3.
Definition pb4cwin_winB_n20_i4 : Q := (-216746602949815673153361226681818895853526471386740949278387684857872384#11305)%Q.
Example pb4cwin_foldsegB_n20_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i4.
Definition pb4cwin_winB_n20_i5 : Q := (232060369640475179586302342894809089299537228257787714316451232874496#161063595)%Q.
Example pb4cwin_foldsegB_n20_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i5.
Definition pb4cwin_winB_n20_i6 : Q := (312644210236826239330422624621949378976597638553493393375232#36422925)%Q.
Example pb4cwin_foldsegB_n20_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winB_n20_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i6.
Definition pb4cwin_winB_n20_i7 : Q := (-171377174400018803383784583091571738549998845952#487635)%Q.
Example pb4cwin_foldsegB_n20_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n20 ((56 + t)%nat))
                   5%nat))
       pb4cwin_winB_n20_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n20_i7.