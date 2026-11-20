(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 22 *)
(** * planb4_calib_chain_build_n22: poleA/poleB chain tails and the assembled abqA/abqB values for point 22, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n22 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 22, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n22 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n22; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n22.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n22.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n22 : list Q :=
  [(6994180064798439654794481982852510423572704968167305254836042311723607313111111744747613454336#1)%Q; (-21906879315697414933850613135529542880581742278648034844391537451100453876376677452729611714560#1)%Q; (66948499562535267101341400537980392061734352099497130176788423881206490147374392990905663488000#1)%Q; (-199601196845731546867537459539475769149454537004810357620412027436102512226128840991380078592000#1)%Q; (580481581664455081807208572606518870491529206964006809728314438439649766815422128977157816320000#1)%Q; (-1646468409848329513246890715519158739828452552544421380961865246539907002110252874656120832000000#1)%Q; (4553969549609737234422986093700801323489485152575538884689896615632938538331142595681452032000000#1)%Q; (-12280782198177773740672849347484082682195293441554805626983460362254548247541840713718169600000000#1)%Q; (32283730154157725946837484549916894551449860592666625151773661317337063847126333550650982400000000#1)%Q; (-82714325966968563214286111810902837525232176880058403533502214080364561451900850476679168000000000#1)%Q; (206504483255829718899884694052364345849536334389781648349629638733221041768416823360880640000000000#1)%Q; (-502269644748714964360894408200786247857145222152036513760452867905195824791627858182144000000000000#1)%Q; (1189883460485691143802355900395473167518696453265686661884843805373935875945351614562304000000000000#1)%Q; (-2744905899468810302346386889297985951672596121223570912862683430619114153095343038791680000000000000#1)%Q; (6164465036000336162688838472520342050472845573859086944023542426397026090979888096870400000000000000#1)%Q; (-13473833675604883309753388697488462467768777096205695861305345147395298137595497676800000000000000000#1)%Q; (28654383142784617564114336144850965120112595467997938780761276041336923960394708418560000000000000000#1)%Q; (-59273998356866980635382227257660429767905508031508815264664980335257305884583893401600000000000000000#1)%Q; (119226399713154915530671131030358309073663205790757742997905804220190934058670227456000000000000000000#1)%Q; (-233114685096191214536301431166072473114734010457781642236037834378503442283553095680000000000000000000#1)%Q; (442895772251807119999671806468305893434484033319635073594381923402819568770272460800000000000000000000#1)%Q; (-817344441804010059237884461438388553939148566929183252631207168773264886212853760000000000000000000000#1)%Q; (1464563166817165539867354312944852312570443423186254442208322044122368369932369920000000000000000000000#1)%Q; (-2546997084375459162273314901789362155074367751763367157586362170587828093924147200000000000000000000000#1)%Q; (4297081973237408181713277053395149604862446013503323103567950489300225736310784000000000000000000000000#1)%Q; (-7029753173657332845568613703717579813267786305988161332988332194999796016087040000000000000000000000000#1)%Q; (11145827103630892565081400741911283728122602090381408738876948533689480275558400000000000000000000000000#1)%Q; (-17118360754948392704161849927469553648725911596703181966488772938377440788480000000000000000000000000000#1)%Q; (25453526647059877732830339253160382310621272855180990321300258448764525608960000000000000000000000000000#1)%Q; (-36619578436750811264322609091987841274048452947368473594664214707238548275200000000000000000000000000000#1)%Q; (50943205040262552125731026831703730972482687885580710510767723190289432576000000000000000000000000000000#1)%Q; (-68482206117103679989843010887029885224710538131949763594164649461180006400000000000000000000000000000000#1)%Q; (88895636855671930742300461409710281852479098132684444981399163321817497600000000000000000000000000000000#1)%Q; (-111344089446127792221428410953165543521988866029487067990215514644283392000000000000000000000000000000000#1)%Q; (134458758163457956043013457027350778602774764259531051849879852637224960000000000000000000000000000000000#1)%Q; (-156413366304082526603966932069269239369974273983529820096627455557632000000000000000000000000000000000000#1)%Q; (175115003613873084175525011618033740077074078641836090292374043885568000000000000000000000000000000000000#1)%Q; (-188499949875374242067328974708070478137658368816390784209133764608000000000000000000000000000000000000000#1)%Q; (194885764767249159380408909949274207374594405373704631614956162252800000000000000000000000000000000000000#1)%Q; (-193302884207364897297068969709895811885797639752000877558788784128000000000000000000000000000000000000000#1)%Q; (183719929583871285886901891086494426123834057833218790690442444800000000000000000000000000000000000000000#1)%Q; (-167094479404586911112041547170960809905723801204288335271847526400000000000000000000000000000000000000000#1)%Q; (145223493227511785115379462836052172813251180141976070383468544000000000000000000000000000000000000000000#1)%Q; (-120422824238569177684996683424017592338851992526060990360453120000000000000000000000000000000000000000000#1)%Q; (95114460880884490790825122231865935815267925360958525512089600000000000000000000000000000000000000000000#1)%Q; (-71425178027721051003759605333632030159172216013255845347328000000000000000000000000000000000000000000000#1)%Q; (50891772628586607082776531786712018513036600661725948149760000000000000000000000000000000000000000000000#1)%Q; (-34329835784412112734219472883201061155059214301681156096000000000000000000000000000000000000000000000000#1)%Q; (21870500681173014189293292201199375975232552134066044928000000000000000000000000000000000000000000000000#1)%Q; (-13122773304057181128220687444714098662372642695948533760000000000000000000000000000000000000000000000000#1)%Q; (7393522587490696013080061583987252657438889337474252800000000000000000000000000000000000000000000000000#1)%Q; (-3898090202124218175954476310283214350782331952824320000000000000000000000000000000000000000000000000000#1)%Q; (1915791268793269761644823165953061754054204331130880000000000000000000000000000000000000000000000000000#1)%Q; (-873829007917866453163834719426031861456015301017600000000000000000000000000000000000000000000000000000#1)%Q; (368032018889822430916138467878855733099582455808000000000000000000000000000000000000000000000000000000#1)%Q; (-142288016544668279805665427906660190722090598400000000000000000000000000000000000000000000000000000000#1)%Q; (50149664975398053298516495447350924372082688000000000000000000000000000000000000000000000000000000000#1)%Q; (-15980863267058607182370317077206344593833984000000000000000000000000000000000000000000000000000000000#1)%Q; (4558474228049446106578444802561892207820800000000000000000000000000000000000000000000000000000000000#1)%Q; (-1149608482491182341584491682940314242252800000000000000000000000000000000000000000000000000000000000#1)%Q; (252331286037644479492816160363236032512000000000000000000000000000000000000000000000000000000000000#1)%Q; (-47222261822506040968632608498363924480000000000000000000000000000000000000000000000000000000000000#1)%Q; (7325900822187759523994938732288409600000000000000000000000000000000000000000000000000000000000000#1)%Q; (-904489129273489886742433572585472000000000000000000000000000000000000000000000000000000000000000#1)%Q; (83322649194200732852772803706880000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-5091028411561126380522648371200000000000000000000000000000000000000000000000000000000000000000#1)%Q; (154742504910672534362390528000000000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n22 : list Q :=
  [(6994180064798439654794481982852510423572704968167305254836042311723607313111111744747613454336#1)%Q; (-21906879315697414933850613135529542880581742278648034844391537451100453876376677452729611714560#1)%Q; (66948499562535267101341400537980392061734352099497130176788423881206490147374392990905663488000#1)%Q; (-199601196845731546867537459539475769149454537004810357620412027436102512226128840991380078592000#1)%Q; (580481581664455081807208572606518870491529206964006809728314438439649766815422128977157816320000#1)%Q; (-1646468409848329513246890715519158739828452552544421380961865246539907002110252874656120832000000#1)%Q; (4553969549609737234422986093700801323489485152575538884689896615632938538331142595681452032000000#1)%Q; (-12280782198177773740672849347484082682195293441554805626983460362254548247541840713718169600000000#1)%Q; (32283730154157725946837484549916894551449860592666625151773661317337063847126333550650982400000000#1)%Q; (-82714325966968563214286111810902837525232176880058403533502214080364561451900850476679168000000000#1)%Q; (206504483255829718899884694052364345849536334389781648349629638733221041768416823360880640000000000#1)%Q; (-502269644748714964360894408200786247857145222152036513760452867905195824791627858182144000000000000#1)%Q; (1189883460485691143802355900395473167518696453265686661884843805373935875945351614562304000000000000#1)%Q; (-2744905899468810302346386889297985951672596121223570912862683430619114153095343038791680000000000000#1)%Q; (6164465036000336162688838472520342050472845573859086944023542426397026090979888096870400000000000000#1)%Q; (-13473833675604883309753388697488462467768777096205695861305345147395298137595497676800000000000000000#1)%Q; (28654383142784617564114336144850965120112595467997938780761276041336923960394708418560000000000000000#1)%Q; (-59273998356866980635382227257660429767905508031508815264664980335257305884583893401600000000000000000#1)%Q; (119226399713154915530671131030358309073663205790757742997905804220190934058670227456000000000000000000#1)%Q; (-233114685096191214536301431166072473114734010457781642236037834378503442283553095680000000000000000000#1)%Q; (442895772251807119999671806468305893434484033319635073594381923402819568770272460800000000000000000000#1)%Q; (-817344441804010059237884461438388553939148566929183252631207168773264886212853760000000000000000000000#1)%Q; (1464563166817165539867354312944852312570443423186254442208322044122368369932369920000000000000000000000#1)%Q; (-2546997084375459162273314901789362155074367751763367157586362170587828093924147200000000000000000000000#1)%Q; (4297081973237408181713277053395149604862446013503323103567950489300225736310784000000000000000000000000#1)%Q; (-7029753173657332845568613703717579813267786305988161332988332194999796016087040000000000000000000000000#1)%Q; (11145827103630892565081400741911283728122602090381408738876948533689480275558400000000000000000000000000#1)%Q; (-17118360754948392704161849927469553648725911596703181966488772938377440788480000000000000000000000000000#1)%Q; (25453526647059877732830339253160382310621272855180990321300258448764525608960000000000000000000000000000#1)%Q; (-36619578436750811264322609091987841274048452947368473594664214707238548275200000000000000000000000000000#1)%Q; (50943205040262552125731026831703730972482687885580710510767723190289432576000000000000000000000000000000#1)%Q; (-68482206117103679989843010887029885224710538131949763594164649461180006400000000000000000000000000000000#1)%Q; (88895636855671930742300461409710281852479098132684444981399163321817497600000000000000000000000000000000#1)%Q; (-111344089446127792221428410953165543521988866029487067990215514644283392000000000000000000000000000000000#1)%Q; (134458758163457956043013457027350778602774764259531051849879852637224960000000000000000000000000000000000#1)%Q; (-156413366304082526603966932069269239369974273983529820096627455557632000000000000000000000000000000000000#1)%Q; (175115003613873084175525011618033740077074078641836090292374043885568000000000000000000000000000000000000#1)%Q; (-188499949875374242067328974708070478137658368816390784209133764608000000000000000000000000000000000000000#1)%Q; (194885764767249159380408909949274207374594405373704631614956162252800000000000000000000000000000000000000#1)%Q; (-193302884207364897297068969709895811885797639752000877558788784128000000000000000000000000000000000000000#1)%Q; (183719929583871285886901891086494426123834057833218790690442444800000000000000000000000000000000000000000#1)%Q; (-167094479404586911112041547170960809905723801204288335271847526400000000000000000000000000000000000000000#1)%Q; (145223493227511785115379462836052172813251180141976070383468544000000000000000000000000000000000000000000#1)%Q; (-120422824238569177684996683424017592338851992526060990360453120000000000000000000000000000000000000000000#1)%Q; (95114460880884490790825122231865935815267925360958525512089600000000000000000000000000000000000000000000#1)%Q; (-71425178027721051003759605333632030159172216013255845347328000000000000000000000000000000000000000000000#1)%Q; (50891772628586607082776531786712018513036600661725948149760000000000000000000000000000000000000000000000#1)%Q; (-34329835784412112734219472883201061155059214301681156096000000000000000000000000000000000000000000000000#1)%Q; (21870500681173014189293292201199375975232552134066044928000000000000000000000000000000000000000000000000#1)%Q; (-13122773304057181128220687444714098662372642695948533760000000000000000000000000000000000000000000000000#1)%Q; (7393522587490696013080061583987252657438889337474252800000000000000000000000000000000000000000000000000#1)%Q; (-3898090202124218175954476310283214350782331952824320000000000000000000000000000000000000000000000000000#1)%Q; (1915791268793269761644823165953061754054204331130880000000000000000000000000000000000000000000000000000#1)%Q; (-873829007917866453163834719426031861456015301017600000000000000000000000000000000000000000000000000000#1)%Q; (368032018889822430916138467878855733099582455808000000000000000000000000000000000000000000000000000000#1)%Q; (-142288016544668279805665427906660190722090598400000000000000000000000000000000000000000000000000000000#1)%Q; (50149664975398053298516495447350924372082688000000000000000000000000000000000000000000000000000000000#1)%Q; (-15980863267058607182370317077206344593833984000000000000000000000000000000000000000000000000000000000#1)%Q; (4558474228049446106578444802561892207820800000000000000000000000000000000000000000000000000000000000#1)%Q; (-1149608482491182341584491682940314242252800000000000000000000000000000000000000000000000000000000000#1)%Q; (252331286037644479492816160363236032512000000000000000000000000000000000000000000000000000000000000#1)%Q; (-47222261822506040968632608498363924480000000000000000000000000000000000000000000000000000000000000#1)%Q; (7325900822187759523994938732288409600000000000000000000000000000000000000000000000000000000000000#1)%Q; (-904489129273489886742433572585472000000000000000000000000000000000000000000000000000000000000000#1)%Q; (83322649194200732852772803706880000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-5091028411561126380522648371200000000000000000000000000000000000000000000000000000000000000000#1)%Q; (154742504910672534362390528000000000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n22 : Z := (75505894808549900156006593338967784433898887230128370740484357673971125516626757787233315731589076686521499648)%Z.
Definition pb4cwin_litB_n22 : Z := (-24034272782714789655893261933494835214358597794218025592815564697690098454432246113337778161565355168942883200)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n22_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              (planb4_g1_shp 22))
       pb4cwin_state_n22_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i1.

Example pb4cwin_remcertA_n22_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i1)
       pb4cwin_state_n22_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i2.

Example pb4cwin_remcertA_n22_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i2)
       pb4cwin_state_n22_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i3.

Example pb4cwin_remcertA_n22_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i3)
       pb4cwin_state_n22_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i4.

Example pb4cwin_remcertA_n22_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i4)
       pb4cwin_state_n22_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i5.

Example pb4cwin_remcertA_n22_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i5)
       pb4cwin_state_n22_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i6.

Example pb4cwin_remcertA_n22_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i6)
       pb4cwin_state_n22_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i7.

Example pb4cwin_remcertA_n22_i8 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_state_n22_i7)
       pb4cwin_state_n22_i8.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n22_i8.

(* poleA channel: assemble the chain tail from the 9 block certificates. *)
Lemma pb4cwin_poleAeq_n22 :
  zzId (planb4_g1_poleA 22) pb4cwin_lit_poleA_n22.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 22 + 1)%nat) with ((8 + 59)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 59%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) (planb4_g1_shp 22))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i0).
  change 59%nat with ((8 + 51)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 51%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat (planb4_g1_shp 22)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i1).
  change 51%nat with ((8 + 43)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 43%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_state_n22_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i2).
  change 43%nat with ((8 + 35)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 35%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_state_n22_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i3).
  change 35%nat with ((8 + 27)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 27%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_state_n22_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i4).
  change 27%nat with ((8 + 19)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 19%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_state_n22_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 19%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_state_n22_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) (8 + 11)%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_state_n22_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 11%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_state_n22_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i6).
  change (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 11%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_state_n22_i6))
    with (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) (8 + 3)%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_state_n22_i6)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 3%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_state_n22_i6))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n22_i8).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n22_i8).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n22.
Lemma pb4cwin_build_poleA_n22 :
  zzId (plq_eqb (planb4_g1_poleA 22) pb4cwin_lit_poleA_n22) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n22).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n22.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n22_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              (planb4_g1_shm 22))
       pb4cwin_stateB_n22_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i1.

Example pb4cwin_remcertB_n22_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i1)
       pb4cwin_stateB_n22_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i2.

Example pb4cwin_remcertB_n22_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i2)
       pb4cwin_stateB_n22_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i3.

Example pb4cwin_remcertB_n22_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i3)
       pb4cwin_stateB_n22_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i4.

Example pb4cwin_remcertB_n22_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i4)
       pb4cwin_stateB_n22_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i5.

Example pb4cwin_remcertB_n22_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i5)
       pb4cwin_stateB_n22_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i6.

Example pb4cwin_remcertB_n22_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i6)
       pb4cwin_stateB_n22_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i7.

Example pb4cwin_remcertB_n22_i8 :
  zzId (pb4cwin_rem (planb4_g1_denw 22)
              (hd 0%Q (planb4_g1_denw 22)) 8%nat
              pb4cwin_stateB_n22_i7)
       pb4cwin_stateB_n22_i8.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n22_i8.

(* poleB channel: assemble the chain tail from the 9 block certificates. *)
Lemma pb4cwin_poleBeq_n22 :
  zzId (planb4_g1_poleB 22) pb4cwin_lit_poleB_n22.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 22 + 1)%nat) with ((8 + 59)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 59%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) (planb4_g1_shm 22))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i0).
  change 59%nat with ((8 + 51)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 51%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat (planb4_g1_shm 22)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i1).
  change 51%nat with ((8 + 43)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 43%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_stateB_n22_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i2).
  change 43%nat with ((8 + 35)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 35%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_stateB_n22_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i3).
  change 35%nat with ((8 + 27)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 27%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_stateB_n22_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i4).
  change 27%nat with ((8 + 19)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 19%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_stateB_n22_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 19%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_stateB_n22_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) (8 + 11)%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_stateB_n22_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 11%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_stateB_n22_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i6).
  change (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 11%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_stateB_n22_i6))
    with (planb4_g1_laur_go (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) (8 + 3)%nat
             (pb4cwin_rem (planb4_g1_denw 22) (hd 0%Q (planb4_g1_denw 22)) 8%nat
                pb4cwin_stateB_n22_i6)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 3%nat (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22)))
               (pb4cwin_rem (planb4_g1_denw 22) ((hd 0%Q (planb4_g1_denw 22))) 8%nat pb4cwin_stateB_n22_i6))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n22_i8).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n22_i8).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n22.
Lemma pb4cwin_build_poleB_n22 :
  zzId (plq_eqb (planb4_g1_poleB 22) pb4cwin_lit_poleB_n22) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n22).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n22.

Lemma pb4cwin_abqAeq_n22 :
  zzId (planb4_abqA 22) (inject_Z pb4cwin_litA_n22).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n22).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n22).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n22.
Lemma pb4cwin_build_abqA_n22 :
  zzId (Qeq_bool (planb4_abqA 22) (inject_Z pb4cwin_litA_n22)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n22).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n22.

Lemma pb4cwin_abqBeq_n22 :
  zzId (planb4_abqB 22) (inject_Z pb4cwin_litB_n22).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n22).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n22).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n22.
Lemma pb4cwin_build_abqB_n22 :
  zzId (Qeq_bool (planb4_abqB 22) (inject_Z pb4cwin_litB_n22)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n22).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n22.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n22 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n22 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n22.
Definition pb4cwin_winA_n22_i0 : Q := (-27968365460843731512718607892728728266440077774039324053985386576027166411008625001989431885824#21)%Q.
Example pb4cwin_foldsegA_n22_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i0.
Definition pb4cwin_winA_n22_i1 : Q := (-23844677206511117518437492248084211436226183054992036040736633585721433172722526785793452670976#3465)%Q.
Example pb4cwin_foldsegA_n22_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i1.
Definition pb4cwin_winA_n22_i2 : Q := (1075114930096569519103280096597945576777702583477972759328758505118118648212694412481193958178816#25741485)%Q.
Example pb4cwin_foldsegA_n22_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i2.
Definition pb4cwin_winA_n22_i3 : Q := (-1820994891100135732607818078205381521569257347180811852016241953061706060532184896058993672192#55221075)%Q.
Example pb4cwin_foldsegA_n22_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i3.
Definition pb4cwin_winA_n22_i4 : Q := (246547345314556153751375155989703757536450429050310901968361513117541620685866159570944#88179)%Q.
Example pb4cwin_foldsegA_n22_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i4.
Definition pb4cwin_winA_n22_i5 : Q := (-4678195588429925505130891505098668332794763098262307119604998684724078831569207296#340515)%Q.
Example pb4cwin_foldsegA_n22_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i5.
Definition pb4cwin_winA_n22_i6 : Q := (-1029682644613751900856097716952188263977320049983459198176844311057091543433216#202927725)%Q.
Example pb4cwin_foldsegA_n22_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i6.
Definition pb4cwin_winA_n22_i7 : Q := (4365280219697285087076047488829860287107828910871166562632010861597687808#19364473485)%Q.
Example pb4cwin_foldsegA_n22_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((56 + t)%nat))
                   8%nat))
       pb4cwin_winA_n22_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i7.
Definition pb4cwin_winA_n22_i8 : Q := (-574829519980853210072804520114022777917074120980299776#195)%Q.
Example pb4cwin_foldsegA_n22_i8 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n22 ((64 + t)%nat))
                   3%nat))
       pb4cwin_winA_n22_i8) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n22_i8.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n22 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n22 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n22.
Definition pb4cwin_winB_n22_i0 : Q := (-15690702555572547346652512821033364151526561984625740989971313777151832890704210594329821970432#21)%Q.
Example pb4cwin_foldsegB_n22_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i0.
Definition pb4cwin_winB_n22_i1 : Q := (2462321757108315175743524805549068382270467086704740532131065559927588388221127509733994921984#3465)%Q.
Example pb4cwin_foldsegB_n22_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i1.
Definition pb4cwin_winB_n22_i2 : Q := (-1691833755819241325929411472529924305994697566610448638985356699539607596238260255012675387392#8580495)%Q.
Example pb4cwin_foldsegB_n22_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i2.
Definition pb4cwin_winB_n22_i3 : Q := (466399627140741709253636097120568336959185108897119466977520586008027696393826641089921024#55221075)%Q.
Example pb4cwin_foldsegB_n22_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i3.
Definition pb4cwin_winB_n22_i4 : Q := (-2976842462376165951828142405494943098707770200190951400009164257667358741906849792#74613)%Q.
Example pb4cwin_foldsegB_n22_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i4.
Definition pb4cwin_winB_n22_i5 : Q := (3273224219300543846631439831516163541333002747114564811435257588428184748032#340515)%Q.
Example pb4cwin_foldsegB_n22_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i5.
Definition pb4cwin_winB_n22_i6 : Q := (9622305033975586945969421864472057544094296149551061940000805120638976#22547525)%Q.
Example pb4cwin_foldsegB_n22_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i6.
Definition pb4cwin_winB_n22_i7 : Q := (-17212670260131812612981869122113121525690623790314040770321973248#19364473485)%Q.
Example pb4cwin_foldsegB_n22_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((56 + t)%nat))
                   8%nat))
       pb4cwin_winB_n22_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i7.
Definition pb4cwin_winB_n22_i8 : Q := (492995144721860999032574882931498991059206144#715)%Q.
Example pb4cwin_foldsegB_n22_i8 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n22 ((64 + t)%nat))
                   3%nat))
       pb4cwin_winB_n22_i8) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n22_i8.