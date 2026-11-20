(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 21 *)
(** * planb4_calib_chain_build_n21: poleA/poleB chain tails and the assembled abqA/abqB values for point 21, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n21 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 21, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n21 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n21; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n21.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n21.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n21 : list Q :=
  [(-327593955820731333366161426335306994467213706623637025463576617412647605288601905826627584#1)%Q; (1025877536196606463713190023233081297569841696119714479672560781970489507772154500790353920#1)%Q; (-3130852777769817890790701576927248748113999449211164455745879165956002356460529470196940800#1)%Q; (9310586241392610850762079677329645271802931143453004224310560442156017117963103200346112000#1)%Q; (-26975747973064977428344289121516531611067537523899634396821324441419405127868415937085440000#1)%Q; (76134552823238583837712156074933493150623646059017315493529839914793357756682817922662400000#1)%Q; (-209279385476627408048129517704252900048894875152540732461633881713027054814392672583680000000#1)%Q; (560178624024664155370569059054809859644681438671648078424410216209108243731599641804800000000#1)%Q; (-1459807252267527687975830634509164221359638894297672498702529313774123294115764371456000000000#1)%Q; (3702892045513503969237803590339656040185176168957569150095488168644725250326418948096000000000#1)%Q; (-9140389910582879658442749845187447532520287319251927965947780574870205999060940226560000000000#1)%Q; (21951379013809448902431300968793991179780881754751412204005186164653249557738553344000000000000#1)%Q; (-51276809956964908106808369612634287722464116901559256393219843091200529345198161920000000000000#1)%Q; (116472687163827179829207097389632288266637508696487608404749800821900484923306803200000000000000#1)%Q; (-257185027389464375369241513529503178209834997699867522320402205084041870074865254400000000000000#1)%Q; (551890306402571031314709776182068736753756544955929926989040222162628299418763264000000000000000#1)%Q; (-1150547066690461168383821211259116697100610591076432634218015174425314077924392960000000000000000#1)%Q; (2329438223885471233166450091986308645194830951957416579594671689792091740071526400000000000000000#1)%Q; (-4578623917418721270701804937813296281438736819983482575703622862378021249089536000000000000000000#1)%Q; (8733495927369273804549899186003662311269891032511049704051017124026550688153600000000000000000000#1)%Q; (-16159693438288324300980526682791100204767155317385798622464962171878049316864000000000000000000000#1)%Q; (28992247239907473541119253068510803303962950024126104362610171808487544193024000000000000000000000#1)%Q; (-50412136201392726810350609989174912647347051183908515001123985727795924828160000000000000000000000#1)%Q; (84914430902303871534489359833917741467108590717928065600980220472977679974400000000000000000000000#1)%Q; (-138483176485372507590277838827711140336080291145483473288573937435107393536000000000000000000000000#1)%Q; (218546509077569802835559980546639764187528910151642125884068543736011816960000000000000000000000000#1)%Q; (-333556652752700015062844918273399161167143122379388127332549726528602112000000000000000000000000000#1)%Q; (492046262309929588122769324311679999620438992217609329837953227455201280000000000000000000000000000#1)%Q; (-701079932670986085341135547498173685856365611827965650361942970204160000000000000000000000000000000#1)%Q; (964163418906948440404082441202176934126876612440607387852793694283366400000000000000000000000000000#1)%Q; (-1278885186762252944839834626686030688422325310957533370131117227638784000000000000000000000000000000#1)%Q; (1634800803082689597130583616374567653073326213768715809763491630284800000000000000000000000000000000#1)%Q; (-2012247776389322904866942230685431804556989557454883454543047163904000000000000000000000000000000000#1)%Q; (2382794136321673989521554918079196645514954081337897036862885724160000000000000000000000000000000000#1)%Q; (-2711795031818083728583378643697941458063588740260864473283753410560000000000000000000000000000000000#1)%Q; (2963044436369139614497732112085407077655462530711020646671423897600000000000000000000000000000000000#1)%Q; (-3104858319909010532109785951540597631637866358144419409667555328000000000000000000000000000000000000#1)%Q; (3116312874932632456031053134228187466386275699762908065662238720000000000000000000000000000000000000#1)%Q; (-2992037380450584901263445291682702870989056673933288255835340800000000000000000000000000000000000000#1)%Q; (2744122736158383232979882317091560189877390866780755513573376000000000000000000000000000000000000000#1)%Q; (-2400388614781280829606403442111416574004581985987464014069760000000000000000000000000000000000000000#1)%Q; (1999274566608932417232198151627920292125259175920425081241600000000000000000000000000000000000000000#1)%Q; (-1582632334802948704613996168887924825909586205454289076224000000000000000000000000000000000000000000#1)%Q; (1188314334711036537065392856436197270682604801717813903360000000000000000000000000000000000000000000#1)%Q; (-844433194153701143234099210238382539826033658652576972800000000000000000000000000000000000000000000#1)%Q; (566525326274423430076448275239604969685141513650044928000000000000000000000000000000000000000000000#1)%Q; (-357859783518213713398396966157326023832167970871705600000000000000000000000000000000000000000000000#1)%Q; (212191180166370288861242604509842304437432575066112000000000000000000000000000000000000000000000000#1)%Q; (-117701166852187505529826132630880540044905288826880000000000000000000000000000000000000000000000000#1)%Q; (60841036179173720487065583394061599952884119633920000000000000000000000000000000000000000000000000#1)%Q; (-29178515106858654660305172965817551582605292339200000000000000000000000000000000000000000000000000#1)%Q; (12917593528890148391951401481328114096731586560000000000000000000000000000000000000000000000000000#1)%Q; (-5248034903198355921439578945557478173468262400000000000000000000000000000000000000000000000000000#1)%Q; (1943139556832415696095050206591061745205248000000000000000000000000000000000000000000000000000000#1)%Q; (-650310850677311740844185109551900826533888000000000000000000000000000000000000000000000000000000#1)%Q; (194762046600956392115094859113729548615680000000000000000000000000000000000000000000000000000000#1)%Q; (-51556102018145522945926880868240982016000000000000000000000000000000000000000000000000000000000#1)%Q; (11874892078409661812199480002263121920000000000000000000000000000000000000000000000000000000000#1)%Q; (-2331411207581186732048590549339340800000000000000000000000000000000000000000000000000000000000#1)%Q; (379344326303204129316413497357107200000000000000000000000000000000000000000000000000000000000#1)%Q; (-49109458543306755269550766292992000000000000000000000000000000000000000000000000000000000000#1)%Q; (4742470919249836496871363706880000000000000000000000000000000000000000000000000000000000000#1)%Q; (-303682165887194848686191411200000000000000000000000000000000000000000000000000000000000000#1)%Q; (9671406556917033397649408000000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n21 : list Q :=
  [(-327593955820731333366161426335306994467213706623637025463576617412647605288601905826627584#1)%Q; (1025877536196606463713190023233081297569841696119714479672560781970489507772154500790353920#1)%Q; (-3130852777769817890790701576927248748113999449211164455745879165956002356460529470196940800#1)%Q; (9310586241392610850762079677329645271802931143453004224310560442156017117963103200346112000#1)%Q; (-26975747973064977428344289121516531611067537523899634396821324441419405127868415937085440000#1)%Q; (76134552823238583837712156074933493150623646059017315493529839914793357756682817922662400000#1)%Q; (-209279385476627408048129517704252900048894875152540732461633881713027054814392672583680000000#1)%Q; (560178624024664155370569059054809859644681438671648078424410216209108243731599641804800000000#1)%Q; (-1459807252267527687975830634509164221359638894297672498702529313774123294115764371456000000000#1)%Q; (3702892045513503969237803590339656040185176168957569150095488168644725250326418948096000000000#1)%Q; (-9140389910582879658442749845187447532520287319251927965947780574870205999060940226560000000000#1)%Q; (21951379013809448902431300968793991179780881754751412204005186164653249557738553344000000000000#1)%Q; (-51276809956964908106808369612634287722464116901559256393219843091200529345198161920000000000000#1)%Q; (116472687163827179829207097389632288266637508696487608404749800821900484923306803200000000000000#1)%Q; (-257185027389464375369241513529503178209834997699867522320402205084041870074865254400000000000000#1)%Q; (551890306402571031314709776182068736753756544955929926989040222162628299418763264000000000000000#1)%Q; (-1150547066690461168383821211259116697100610591076432634218015174425314077924392960000000000000000#1)%Q; (2329438223885471233166450091986308645194830951957416579594671689792091740071526400000000000000000#1)%Q; (-4578623917418721270701804937813296281438736819983482575703622862378021249089536000000000000000000#1)%Q; (8733495927369273804549899186003662311269891032511049704051017124026550688153600000000000000000000#1)%Q; (-16159693438288324300980526682791100204767155317385798622464962171878049316864000000000000000000000#1)%Q; (28992247239907473541119253068510803303962950024126104362610171808487544193024000000000000000000000#1)%Q; (-50412136201392726810350609989174912647347051183908515001123985727795924828160000000000000000000000#1)%Q; (84914430902303871534489359833917741467108590717928065600980220472977679974400000000000000000000000#1)%Q; (-138483176485372507590277838827711140336080291145483473288573937435107393536000000000000000000000000#1)%Q; (218546509077569802835559980546639764187528910151642125884068543736011816960000000000000000000000000#1)%Q; (-333556652752700015062844918273399161167143122379388127332549726528602112000000000000000000000000000#1)%Q; (492046262309929588122769324311679999620438992217609329837953227455201280000000000000000000000000000#1)%Q; (-701079932670986085341135547498173685856365611827965650361942970204160000000000000000000000000000000#1)%Q; (964163418906948440404082441202176934126876612440607387852793694283366400000000000000000000000000000#1)%Q; (-1278885186762252944839834626686030688422325310957533370131117227638784000000000000000000000000000000#1)%Q; (1634800803082689597130583616374567653073326213768715809763491630284800000000000000000000000000000000#1)%Q; (-2012247776389322904866942230685431804556989557454883454543047163904000000000000000000000000000000000#1)%Q; (2382794136321673989521554918079196645514954081337897036862885724160000000000000000000000000000000000#1)%Q; (-2711795031818083728583378643697941458063588740260864473283753410560000000000000000000000000000000000#1)%Q; (2963044436369139614497732112085407077655462530711020646671423897600000000000000000000000000000000000#1)%Q; (-3104858319909010532109785951540597631637866358144419409667555328000000000000000000000000000000000000#1)%Q; (3116312874932632456031053134228187466386275699762908065662238720000000000000000000000000000000000000#1)%Q; (-2992037380450584901263445291682702870989056673933288255835340800000000000000000000000000000000000000#1)%Q; (2744122736158383232979882317091560189877390866780755513573376000000000000000000000000000000000000000#1)%Q; (-2400388614781280829606403442111416574004581985987464014069760000000000000000000000000000000000000000#1)%Q; (1999274566608932417232198151627920292125259175920425081241600000000000000000000000000000000000000000#1)%Q; (-1582632334802948704613996168887924825909586205454289076224000000000000000000000000000000000000000000#1)%Q; (1188314334711036537065392856436197270682604801717813903360000000000000000000000000000000000000000000#1)%Q; (-844433194153701143234099210238382539826033658652576972800000000000000000000000000000000000000000000#1)%Q; (566525326274423430076448275239604969685141513650044928000000000000000000000000000000000000000000000#1)%Q; (-357859783518213713398396966157326023832167970871705600000000000000000000000000000000000000000000000#1)%Q; (212191180166370288861242604509842304437432575066112000000000000000000000000000000000000000000000000#1)%Q; (-117701166852187505529826132630880540044905288826880000000000000000000000000000000000000000000000000#1)%Q; (60841036179173720487065583394061599952884119633920000000000000000000000000000000000000000000000000#1)%Q; (-29178515106858654660305172965817551582605292339200000000000000000000000000000000000000000000000000#1)%Q; (12917593528890148391951401481328114096731586560000000000000000000000000000000000000000000000000000#1)%Q; (-5248034903198355921439578945557478173468262400000000000000000000000000000000000000000000000000000#1)%Q; (1943139556832415696095050206591061745205248000000000000000000000000000000000000000000000000000000#1)%Q; (-650310850677311740844185109551900826533888000000000000000000000000000000000000000000000000000000#1)%Q; (194762046600956392115094859113729548615680000000000000000000000000000000000000000000000000000000#1)%Q; (-51556102018145522945926880868240982016000000000000000000000000000000000000000000000000000000000#1)%Q; (11874892078409661812199480002263121920000000000000000000000000000000000000000000000000000000000#1)%Q; (-2331411207581186732048590549339340800000000000000000000000000000000000000000000000000000000000#1)%Q; (379344326303204129316413497357107200000000000000000000000000000000000000000000000000000000000#1)%Q; (-49109458543306755269550766292992000000000000000000000000000000000000000000000000000000000000#1)%Q; (4742470919249836496871363706880000000000000000000000000000000000000000000000000000000000000#1)%Q; (-303682165887194848686191411200000000000000000000000000000000000000000000000000000000000000#1)%Q; (9671406556917033397649408000000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n21 : Z := (93582581313212057871980534509144957846781696509716280986806704436404513582388637691942668278298840531992576)%Z.
Definition pb4cwin_litB_n21 : Z := (-29788260806593865898848505114628722652100360501798926115735278223866946730013574153195184117587843080550400)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n21_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              (planb4_g1_shp 21))
       pb4cwin_state_n21_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i1.

Example pb4cwin_remcertA_n21_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_state_n21_i1)
       pb4cwin_state_n21_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i2.

Example pb4cwin_remcertA_n21_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_state_n21_i2)
       pb4cwin_state_n21_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i3.

Example pb4cwin_remcertA_n21_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_state_n21_i3)
       pb4cwin_state_n21_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i4.

Example pb4cwin_remcertA_n21_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_state_n21_i4)
       pb4cwin_state_n21_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i5.

Example pb4cwin_remcertA_n21_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_state_n21_i5)
       pb4cwin_state_n21_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i6.

Example pb4cwin_remcertA_n21_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_state_n21_i6)
       pb4cwin_state_n21_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n21_i7.

(* poleA channel: assemble the chain tail from the 8 block certificates. *)
Lemma pb4cwin_poleAeq_n21 :
  zzId (planb4_g1_poleA 21) pb4cwin_lit_poleA_n21.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 21 + 1)%nat) with ((8 + 56)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 56%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) (planb4_g1_shp 21))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i0).
  change 56%nat with ((8 + 48)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 48%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat (planb4_g1_shp 21)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i1).
  change 48%nat with ((8 + 40)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 40%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_state_n21_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i2).
  change 40%nat with ((8 + 32)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 32%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_state_n21_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i3).
  change 32%nat with ((8 + 24)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 24%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_state_n21_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i4).
  change 24%nat with ((8 + 16)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 16%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_state_n21_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) 16%nat
             (pb4cwin_rem (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) 8%nat
                pb4cwin_state_n21_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) (8 + 8)%nat
             (pb4cwin_rem (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) 8%nat
                pb4cwin_state_n21_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 8%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_state_n21_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n21_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n21_i7).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n21.
Lemma pb4cwin_build_poleA_n21 :
  zzId (plq_eqb (planb4_g1_poleA 21) pb4cwin_lit_poleA_n21) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n21).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n21.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n21_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              (planb4_g1_shm 21))
       pb4cwin_stateB_n21_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i1.

Example pb4cwin_remcertB_n21_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_stateB_n21_i1)
       pb4cwin_stateB_n21_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i2.

Example pb4cwin_remcertB_n21_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_stateB_n21_i2)
       pb4cwin_stateB_n21_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i3.

Example pb4cwin_remcertB_n21_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_stateB_n21_i3)
       pb4cwin_stateB_n21_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i4.

Example pb4cwin_remcertB_n21_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_stateB_n21_i4)
       pb4cwin_stateB_n21_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i5.

Example pb4cwin_remcertB_n21_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_stateB_n21_i5)
       pb4cwin_stateB_n21_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i6.

Example pb4cwin_remcertB_n21_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 21)
              (hd 0%Q (planb4_g1_denw 21)) 8%nat
              pb4cwin_stateB_n21_i6)
       pb4cwin_stateB_n21_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n21_i7.

(* poleB channel: assemble the chain tail from the 8 block certificates. *)
Lemma pb4cwin_poleBeq_n21 :
  zzId (planb4_g1_poleB 21) pb4cwin_lit_poleB_n21.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 21 + 1)%nat) with ((8 + 56)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 56%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) (planb4_g1_shm 21))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i0).
  change 56%nat with ((8 + 48)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 48%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat (planb4_g1_shm 21)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i1).
  change 48%nat with ((8 + 40)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 40%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_stateB_n21_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i2).
  change 40%nat with ((8 + 32)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 32%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_stateB_n21_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i3).
  change 32%nat with ((8 + 24)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 24%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_stateB_n21_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i4).
  change 24%nat with ((8 + 16)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 16%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_stateB_n21_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) 16%nat
             (pb4cwin_rem (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) 8%nat
                pb4cwin_stateB_n21_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) (8 + 8)%nat
             (pb4cwin_rem (planb4_g1_denw 21) (hd 0%Q (planb4_g1_denw 21)) 8%nat
                pb4cwin_stateB_n21_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 8%nat (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21)))
               (pb4cwin_rem (planb4_g1_denw 21) ((hd 0%Q (planb4_g1_denw 21))) 8%nat pb4cwin_stateB_n21_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n21_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n21_i7).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n21.
Lemma pb4cwin_build_poleB_n21 :
  zzId (plq_eqb (planb4_g1_poleB 21) pb4cwin_lit_poleB_n21) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n21).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n21.

Lemma pb4cwin_abqAeq_n21 :
  zzId (planb4_abqA 21) (inject_Z pb4cwin_litA_n21).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n21).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n21).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n21.
Lemma pb4cwin_build_abqA_n21 :
  zzId (Qeq_bool (planb4_abqA 21) (inject_Z pb4cwin_litA_n21)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n21).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n21.

Lemma pb4cwin_abqBeq_n21 :
  zzId (planb4_abqB 21) (inject_Z pb4cwin_litB_n21).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n21).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n21).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n21.
Lemma pb4cwin_build_abqB_n21 :
  zzId (Qeq_bool (planb4_abqB 21) (inject_Z pb4cwin_litB_n21)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n21).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n21.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n21 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n21 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n21.
Definition pb4cwin_winA_n21_i0 : Q := (6552032480226820109772754574620521605685489488255752369847736280945422719876227018988191744#105)%Q.
Example pb4cwin_foldsegA_n21_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i0.
Definition pb4cwin_winA_n21_i1 : Q := (1083315886970356906396544228431370645914941261859091117027583614967884597081117297326686208#3465)%Q.
Example pb4cwin_foldsegA_n21_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i1.
Definition pb4cwin_winA_n21_i2 : Q := (-2899250719391632143043063088693174751146114621963897277659012788614402748299643753701834752#1716099)%Q.
Example pb4cwin_foldsegA_n21_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i2.
Definition pb4cwin_winA_n21_i3 : Q := (506007337242066888067516462494485949550727697898228424766481037827437634244045726285824#471975)%Q.
Example pb4cwin_foldsegA_n21_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i3.
Definition pb4cwin_winA_n21_i4 : Q := (-2164148104100288109499212771567099587299566517327438461281094771380858613479243776#33915)%Q.
Example pb4cwin_foldsegA_n21_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i4.
Definition pb4cwin_winA_n21_i5 : Q := (28894861025407634301546564225682863309797168147217774074459939643204538199965696#161063595)%Q.
Example pb4cwin_foldsegA_n21_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i5.
Definition pb4cwin_winA_n21_i6 : Q := (1338536898971614929554099107974196376060495226561571157079517979742306304#46829475)%Q.
Example pb4cwin_foldsegA_n21_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i6.
Definition pb4cwin_winA_n21_i7 : Q := (-4598176315434177651855803682163693693311698510522395465964677234688#19364473485)%Q.
Example pb4cwin_foldsegA_n21_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n21 ((56 + t)%nat))
                   8%nat))
       pb4cwin_winA_n21_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n21_i7.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n21 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n21 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n21.
Definition pb4cwin_winB_n21_i0 : Q := (3674965884140564986482230765729712550982904281503371133693915292955252636941782080617971712#105)%Q.
Example pb4cwin_foldsegB_n21_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i0.
Definition pb4cwin_winB_n21_i1 : Q := (-111533278114838369175851862977262570981768498868998533390099134947314432536758571560337408#3465)%Q.
Example pb4cwin_foldsegB_n21_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i1.
Definition pb4cwin_winB_n21_i2 : Q := (4548756139425892447900862670803519947521762988374277129666932044531914073090923627020288#572033)%Q.
Example pb4cwin_foldsegB_n21_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i2.
Definition pb4cwin_winB_n21_i3 : Q := (-43133045256609421644727600176818798350427411961077350774952712734085392373253144576#157325)%Q.
Example pb4cwin_foldsegB_n21_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i3.
Definition pb4cwin_winB_n21_i4 : Q := (113526790766083371233681307246021570704969759318556801409811902598706968395776#124355)%Q.
Example pb4cwin_foldsegB_n21_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i4.
Definition pb4cwin_winB_n21_i5 : Q := (-20656016386981446378248076335892647933010426062996534349461194607610036224#161063595)%Q.
Example pb4cwin_foldsegB_n21_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i5.
Definition pb4cwin_winB_n21_i6 : Q := (-11946353426356904080663976186660450536696861679975187929475579904#5203275)%Q.
Example pb4cwin_foldsegB_n21_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i6.
Definition pb4cwin_winB_n21_i7 : Q := (17855794298423879205813227614060545822539184654422741352448#19364473485)%Q.
Example pb4cwin_foldsegB_n21_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n21 ((56 + t)%nat))
                   8%nat))
       pb4cwin_winB_n21_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n21_i7.