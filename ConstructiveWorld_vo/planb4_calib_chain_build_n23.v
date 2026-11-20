(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 23 *)
(** * planb4_calib_chain_build_n23: poleA/poleB chain tails and the assembled abqA/abqB values for point 23, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n23 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 23, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n23 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n23; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n23.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n23.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n23 : list Q :=
  [(-149480769335047536552188789323296165997037290879602396071679284566660752073955476994907226201128960#1)%Q; (468280186817801439164313600504907425570270762376135192472351563493662534902561447423982322938019840#1)%Q; (-1432872997271801503218988360407289431148415146863986453322443788421030947956179936627978852211097600#1)%Q; (4281946486838602504569526785454814299134406965357688573001551627401321224592305805777898364207104000#1)%Q; (-12495476295054596438901156387897862160417619109042224226669185078753606693020545021768676577116160000#1)%Q; (35602870459585418810019296377974437823386489186361134532226583986391997872214686679340756762624000000#1)%Q; (-99032206887505682110108276427741900109275409228180125116960629487810124099451374115399277740032000000#1)%Q; (268881979462732356574758797649996215914799270301451507546118718164049536627195172159163025326080000000#1)%Q; (-712477384613841955208061715077600825339931193682428853106181780159135178255909976274378109747200000000#1)%Q; (1842173908805921345807199442534357747565396483842985930919251280460708225422982818101899296768000000000#1)%Q; (-4646884108363368190425611176989039090093482199299737731597492807113463209342781841085982310400000000000#1)%Q; (11433562802043898087905846608468119697362545083814849324337953729385078250360771217002070016000000000000#1)%Q; (-27434804060643232797654656810622046024541065686119866741117035398847265869011158411855790080000000000000#1)%Q; (64184426845569906112520129587804372546697351234718337406829525440086329269039088479816908800000000000000#1)%Q; (-146374941430249145542864242299749816092015994224171274378368748733586669379458058908860416000000000000000#1)%Q; (325318927403112261795027038573632484901937075645458715020041378419093938080818509004144640000000000000000#1)%Q; (-704446491882797979943970098519801427103167651409976653135609608872899413475345138261688320000000000000000#1)%Q; (1485823894102711455351723636199934609622378310443529655341300788467085718747660424105164800000000000000000#1)%Q; (-3051726490008129073445395373323363541128889634586792819188864994863627527444748998541312000000000000000000#1)%Q; (6101751621219038150676175785053196023515107247501926239360751059035895315254497855406080000000000000000000#1)%Q; (-11872956309866275011381342855783591471292247878841765337462566188557583050883146448896000000000000000000000#1)%Q; (22475849823860042120954121546947644179183220679273892989441654659419853851295569936384000000000000000000000#1)%Q; (-41378625606301117770246382632400048601918721205375771768872168219012939956104420392960000000000000000000000#1)%Q; (74059424221527103518615883422569525675498909401330344998732167716282430139660658278400000000000000000000000#1)%Q; (-128813671057466529479617436711448982620897999700154794100648783546601078304020627456000000000000000000000000#1)%Q; (217643062715805857618496458241412224527676130765991040258074515377871334572189286400000000000000000000000000#1)%Q; (-357061584287332309245206258414360728542668252757757249920604546564810281703387955200000000000000000000000000#1)%Q; (568539581234002824175909110718988167245463410834259593747961880092478251978457088000000000000000000000000000#1)%Q; (-878193863351740583386391450227757839484562108465207645573632580418018728025784320000000000000000000000000000#1)%Q; (1315265035938329574065858801212181582345303799850575435458717145958641801415884800000000000000000000000000000#1)%Q; (-1908964324573636988604007130521333203865248940454546427793883783263492725800960000000000000000000000000000000#1)%Q; (2683483791900566775485750877264831472196205638955753857859716254148087041228800000000000000000000000000000000#1)%Q; (-3651381570824480809477226556941664143305550181737758316397183260588358238208000000000000000000000000000000000#1)%Q; (4806150391103418002601912274561403813093975009295242299827773267919618703360000000000000000000000000000000000#1)%Q; (-6115434597538181703190340066089004740313586823904860124136303863040835584000000000000000000000000000000000000#1)%Q; (7516865928128464832496078828624097119010633571547578142031695019430117376000000000000000000000000000000000000#1)%Q; (-8918578916976470464615259949684337985528442619505502400549354620271460352000000000000000000000000000000000000#1)%Q; (10205921426716464680242511461310078406345406926371930388128385405215047680000000000000000000000000000000000000#1)%Q; (-11254632760014794518519257338576618201637642921820917857241792095925043200000000000000000000000000000000000000#1)%Q; (11949016009785011786819120840671373462985317437500789394789111418585088000000000000000000000000000000000000000#1)%Q; (-12201849282819358066206152698899199151515565860515853535875075512729600000000000000000000000000000000000000000#1)%Q; (11971590971119819092394071664677973766589457946216647907072868247142400000000000000000000000000000000000000000#1)%Q; (-11272404752208309317372621778318542965515628326079046167466424139776000000000000000000000000000000000000000000#1)%Q; (10173904491323180133731860414084091201491006219018662784491627479040000000000000000000000000000000000000000000#1)%Q; (-8790039969718652149999131013709824443823644088495902550230931865600000000000000000000000000000000000000000000#1)%Q; (7259468368153625894728004550598117402998041437824836930308669440000000000000000000000000000000000000000000000#1)%Q; (-5722099761886193588209755004979864508617938658400525760562462720000000000000000000000000000000000000000000000#1)%Q; (4297432319739405952766801643798085325600595237377091679603916800000000000000000000000000000000000000000000000#1)%Q; (-3069478969356640035006507215176817937616571853369342366318592000000000000000000000000000000000000000000000000#1)%Q; (2080867874872326515436824895125112342539344446298407598817280000000000000000000000000000000000000000000000000#1)%Q; (-1335927406632072365925100299070792684661331652081843437568000000000000000000000000000000000000000000000000000#1)%Q; (810237923093830636120676217439781994193828257050258309120000000000000000000000000000000000000000000000000000#1)%Q; (-462965479587837581378577396319389310266537565222443417600000000000000000000000000000000000000000000000000000#1)%Q; (248466554868176611586019585029363206655231193321046016000000000000000000000000000000000000000000000000000000#1)%Q; (-124820061555238986445749659504648157787203018078289920000000000000000000000000000000000000000000000000000000#1)%Q; (58467852881659509313208455491204221736661078035660800000000000000000000000000000000000000000000000000000000#1)%Q; (-25424383144463859828087702277538096616372492776243200000000000000000000000000000000000000000000000000000000#1)%Q; (10211305525881265085636273081407985973149908860928000000000000000000000000000000000000000000000000000000000#1)%Q; (-3765741804379719954348906234334375962876177285120000000000000000000000000000000000000000000000000000000000#1)%Q; (1266338584085319899475767293698954954801990860800000000000000000000000000000000000000000000000000000000000#1)%Q; (-385117183875944847953062824796030782050140160000000000000000000000000000000000000000000000000000000000000#1)%Q; (104865480361337701011657706256845669599805440000000000000000000000000000000000000000000000000000000000000#1)%Q; (-25251734157701594887351345655689330137497600000000000000000000000000000000000000000000000000000000000000#1)%Q; (5293545970752547788160446507605142011904000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-946370506984744123760181552764168437760000000000000000000000000000000000000000000000000000000000000000#1)%Q; (140286905450846639117809899834179584000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-16553979317451883541245519149924352000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (1457822949063249519326706668666880000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-85170274702834162913059746611200000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (2475880078570760549798248448000000000000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n23 : list Q :=
  [(-149480769335047536552188789323296165997037290879602396071679284566660752073955476994907226201128960#1)%Q; (468280186817801439164313600504907425570270762376135192472351563493662534902561447423982322938019840#1)%Q; (-1432872997271801503218988360407289431148415146863986453322443788421030947956179936627978852211097600#1)%Q; (4281946486838602504569526785454814299134406965357688573001551627401321224592305805777898364207104000#1)%Q; (-12495476295054596438901156387897862160417619109042224226669185078753606693020545021768676577116160000#1)%Q; (35602870459585418810019296377974437823386489186361134532226583986391997872214686679340756762624000000#1)%Q; (-99032206887505682110108276427741900109275409228180125116960629487810124099451374115399277740032000000#1)%Q; (268881979462732356574758797649996215914799270301451507546118718164049536627195172159163025326080000000#1)%Q; (-712477384613841955208061715077600825339931193682428853106181780159135178255909976274378109747200000000#1)%Q; (1842173908805921345807199442534357747565396483842985930919251280460708225422982818101899296768000000000#1)%Q; (-4646884108363368190425611176989039090093482199299737731597492807113463209342781841085982310400000000000#1)%Q; (11433562802043898087905846608468119697362545083814849324337953729385078250360771217002070016000000000000#1)%Q; (-27434804060643232797654656810622046024541065686119866741117035398847265869011158411855790080000000000000#1)%Q; (64184426845569906112520129587804372546697351234718337406829525440086329269039088479816908800000000000000#1)%Q; (-146374941430249145542864242299749816092015994224171274378368748733586669379458058908860416000000000000000#1)%Q; (325318927403112261795027038573632484901937075645458715020041378419093938080818509004144640000000000000000#1)%Q; (-704446491882797979943970098519801427103167651409976653135609608872899413475345138261688320000000000000000#1)%Q; (1485823894102711455351723636199934609622378310443529655341300788467085718747660424105164800000000000000000#1)%Q; (-3051726490008129073445395373323363541128889634586792819188864994863627527444748998541312000000000000000000#1)%Q; (6101751621219038150676175785053196023515107247501926239360751059035895315254497855406080000000000000000000#1)%Q; (-11872956309866275011381342855783591471292247878841765337462566188557583050883146448896000000000000000000000#1)%Q; (22475849823860042120954121546947644179183220679273892989441654659419853851295569936384000000000000000000000#1)%Q; (-41378625606301117770246382632400048601918721205375771768872168219012939956104420392960000000000000000000000#1)%Q; (74059424221527103518615883422569525675498909401330344998732167716282430139660658278400000000000000000000000#1)%Q; (-128813671057466529479617436711448982620897999700154794100648783546601078304020627456000000000000000000000000#1)%Q; (217643062715805857618496458241412224527676130765991040258074515377871334572189286400000000000000000000000000#1)%Q; (-357061584287332309245206258414360728542668252757757249920604546564810281703387955200000000000000000000000000#1)%Q; (568539581234002824175909110718988167245463410834259593747961880092478251978457088000000000000000000000000000#1)%Q; (-878193863351740583386391450227757839484562108465207645573632580418018728025784320000000000000000000000000000#1)%Q; (1315265035938329574065858801212181582345303799850575435458717145958641801415884800000000000000000000000000000#1)%Q; (-1908964324573636988604007130521333203865248940454546427793883783263492725800960000000000000000000000000000000#1)%Q; (2683483791900566775485750877264831472196205638955753857859716254148087041228800000000000000000000000000000000#1)%Q; (-3651381570824480809477226556941664143305550181737758316397183260588358238208000000000000000000000000000000000#1)%Q; (4806150391103418002601912274561403813093975009295242299827773267919618703360000000000000000000000000000000000#1)%Q; (-6115434597538181703190340066089004740313586823904860124136303863040835584000000000000000000000000000000000000#1)%Q; (7516865928128464832496078828624097119010633571547578142031695019430117376000000000000000000000000000000000000#1)%Q; (-8918578916976470464615259949684337985528442619505502400549354620271460352000000000000000000000000000000000000#1)%Q; (10205921426716464680242511461310078406345406926371930388128385405215047680000000000000000000000000000000000000#1)%Q; (-11254632760014794518519257338576618201637642921820917857241792095925043200000000000000000000000000000000000000#1)%Q; (11949016009785011786819120840671373462985317437500789394789111418585088000000000000000000000000000000000000000#1)%Q; (-12201849282819358066206152698899199151515565860515853535875075512729600000000000000000000000000000000000000000#1)%Q; (11971590971119819092394071664677973766589457946216647907072868247142400000000000000000000000000000000000000000#1)%Q; (-11272404752208309317372621778318542965515628326079046167466424139776000000000000000000000000000000000000000000#1)%Q; (10173904491323180133731860414084091201491006219018662784491627479040000000000000000000000000000000000000000000#1)%Q; (-8790039969718652149999131013709824443823644088495902550230931865600000000000000000000000000000000000000000000#1)%Q; (7259468368153625894728004550598117402998041437824836930308669440000000000000000000000000000000000000000000000#1)%Q; (-5722099761886193588209755004979864508617938658400525760562462720000000000000000000000000000000000000000000000#1)%Q; (4297432319739405952766801643798085325600595237377091679603916800000000000000000000000000000000000000000000000#1)%Q; (-3069478969356640035006507215176817937616571853369342366318592000000000000000000000000000000000000000000000000#1)%Q; (2080867874872326515436824895125112342539344446298407598817280000000000000000000000000000000000000000000000000#1)%Q; (-1335927406632072365925100299070792684661331652081843437568000000000000000000000000000000000000000000000000000#1)%Q; (810237923093830636120676217439781994193828257050258309120000000000000000000000000000000000000000000000000000#1)%Q; (-462965479587837581378577396319389310266537565222443417600000000000000000000000000000000000000000000000000000#1)%Q; (248466554868176611586019585029363206655231193321046016000000000000000000000000000000000000000000000000000000#1)%Q; (-124820061555238986445749659504648157787203018078289920000000000000000000000000000000000000000000000000000000#1)%Q; (58467852881659509313208455491204221736661078035660800000000000000000000000000000000000000000000000000000000#1)%Q; (-25424383144463859828087702277538096616372492776243200000000000000000000000000000000000000000000000000000000#1)%Q; (10211305525881265085636273081407985973149908860928000000000000000000000000000000000000000000000000000000000#1)%Q; (-3765741804379719954348906234334375962876177285120000000000000000000000000000000000000000000000000000000000#1)%Q; (1266338584085319899475767293698954954801990860800000000000000000000000000000000000000000000000000000000000#1)%Q; (-385117183875944847953062824796030782050140160000000000000000000000000000000000000000000000000000000000000#1)%Q; (104865480361337701011657706256845669599805440000000000000000000000000000000000000000000000000000000000000#1)%Q; (-25251734157701594887351345655689330137497600000000000000000000000000000000000000000000000000000000000000#1)%Q; (5293545970752547788160446507605142011904000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-946370506984744123760181552764168437760000000000000000000000000000000000000000000000000000000000000000#1)%Q; (140286905450846639117809899834179584000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-16553979317451883541245519149924352000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (1457822949063249519326706668666880000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (-85170274702834162913059746611200000000000000000000000000000000000000000000000000000000000000000000#1)%Q; (2475880078570760549798248448000000000000000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n23 : Z := (35905368589542602951864756898128302039723069154326279828968719819022665707433922857726401589204140418352100021370880)%Z.
Definition pb4cwin_litB_n23 : Z := (-11429033789124358542634434098537703815712482078171711397853455522913304179280455352637924979065875962202185750032000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n23_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              (planb4_g1_shp 23))
       pb4cwin_state_n23_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i1.

Example pb4cwin_remcertA_n23_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i1)
       pb4cwin_state_n23_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i2.

Example pb4cwin_remcertA_n23_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i2)
       pb4cwin_state_n23_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i3.

Example pb4cwin_remcertA_n23_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i3)
       pb4cwin_state_n23_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i4.

Example pb4cwin_remcertA_n23_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i4)
       pb4cwin_state_n23_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i5.

Example pb4cwin_remcertA_n23_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i5)
       pb4cwin_state_n23_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i6.

Example pb4cwin_remcertA_n23_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i6)
       pb4cwin_state_n23_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i7.

Example pb4cwin_remcertA_n23_i8 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_state_n23_i7)
       pb4cwin_state_n23_i8.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n23_i8.

(* poleA channel: assemble the chain tail from the 9 block certificates. *)
Lemma pb4cwin_poleAeq_n23 :
  zzId (planb4_g1_poleA 23) pb4cwin_lit_poleA_n23.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 23 + 1)%nat) with ((8 + 62)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 62%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) (planb4_g1_shp 23))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i0).
  change 62%nat with ((8 + 54)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 54%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat (planb4_g1_shp 23)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i1).
  change 54%nat with ((8 + 46)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 46%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_state_n23_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i2).
  change 46%nat with ((8 + 38)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 38%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_state_n23_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i3).
  change 38%nat with ((8 + 30)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 30%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_state_n23_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i4).
  change 30%nat with ((8 + 22)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 22%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_state_n23_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 22%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_state_n23_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) (8 + 14)%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_state_n23_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 14%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_state_n23_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i6).
  change (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 14%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_state_n23_i6))
    with (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) (8 + 6)%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_state_n23_i6)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 6%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_state_n23_i6))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n23_i8).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n23_i8).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n23.
Lemma pb4cwin_build_poleA_n23 :
  zzId (plq_eqb (planb4_g1_poleA 23) pb4cwin_lit_poleA_n23) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n23).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n23.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n23_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              (planb4_g1_shm 23))
       pb4cwin_stateB_n23_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i1.

Example pb4cwin_remcertB_n23_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i1)
       pb4cwin_stateB_n23_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i2.

Example pb4cwin_remcertB_n23_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i2)
       pb4cwin_stateB_n23_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i3.

Example pb4cwin_remcertB_n23_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i3)
       pb4cwin_stateB_n23_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i4.

Example pb4cwin_remcertB_n23_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i4)
       pb4cwin_stateB_n23_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i5.

Example pb4cwin_remcertB_n23_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i5)
       pb4cwin_stateB_n23_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i6.

Example pb4cwin_remcertB_n23_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i6)
       pb4cwin_stateB_n23_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i7.

Example pb4cwin_remcertB_n23_i8 :
  zzId (pb4cwin_rem (planb4_g1_denw 23)
              (hd 0%Q (planb4_g1_denw 23)) 8%nat
              pb4cwin_stateB_n23_i7)
       pb4cwin_stateB_n23_i8.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n23_i8.

(* poleB channel: assemble the chain tail from the 9 block certificates. *)
Lemma pb4cwin_poleBeq_n23 :
  zzId (planb4_g1_poleB 23) pb4cwin_lit_poleB_n23.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 23 + 1)%nat) with ((8 + 62)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 62%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) (planb4_g1_shm 23))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i0).
  change 62%nat with ((8 + 54)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 54%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat (planb4_g1_shm 23)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i1).
  change 54%nat with ((8 + 46)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 46%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_stateB_n23_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i2).
  change 46%nat with ((8 + 38)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 38%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_stateB_n23_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i3).
  change 38%nat with ((8 + 30)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 30%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_stateB_n23_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i4).
  change 30%nat with ((8 + 22)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 22%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_stateB_n23_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 22%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_stateB_n23_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) (8 + 14)%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_stateB_n23_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 14%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_stateB_n23_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i6).
  change (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 14%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_stateB_n23_i6))
    with (planb4_g1_laur_go (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) (8 + 6)%nat
             (pb4cwin_rem (planb4_g1_denw 23) (hd 0%Q (planb4_g1_denw 23)) 8%nat
                pb4cwin_stateB_n23_i6)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 6%nat (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23)))
               (pb4cwin_rem (planb4_g1_denw 23) ((hd 0%Q (planb4_g1_denw 23))) 8%nat pb4cwin_stateB_n23_i6))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n23_i8).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n23_i8).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n23.
Lemma pb4cwin_build_poleB_n23 :
  zzId (plq_eqb (planb4_g1_poleB 23) pb4cwin_lit_poleB_n23) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n23).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n23.

Lemma pb4cwin_abqAeq_n23 :
  zzId (planb4_abqA 23) (inject_Z pb4cwin_litA_n23).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n23).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n23).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n23.
Lemma pb4cwin_build_abqA_n23 :
  zzId (Qeq_bool (planb4_abqA 23) (inject_Z pb4cwin_litA_n23)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n23).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n23.

Lemma pb4cwin_abqBeq_n23 :
  zzId (planb4_abqB 23) (inject_Z pb4cwin_litB_n23).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n23).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n23).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n23.
Lemma pb4cwin_build_abqB_n23 :
  zzId (Qeq_bool (planb4_abqB 23) (inject_Z pb4cwin_litB_n23)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n23).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n23.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n23 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n23 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n23.
Definition pb4cwin_winA_n23_i0 : Q := (199188840493838437752826197978398810887968647523923698314143547784293881790437908942497728488800256#7)%Q.
Example pb4cwin_foldsegA_n23_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i0.
Definition pb4cwin_winA_n23_i1 : Q := (151376866830289945455308693175753080338087875097155780642023091139349784584653252197681029453971456#1001)%Q.
Example pb4cwin_foldsegA_n23_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i1.
Definition pb4cwin_winA_n23_i2 : Q := (-102952651315818830062041826985876498103135029520970101090269890228874163231310196614071599497216000#100947)%Q.
Example pb4cwin_foldsegA_n23_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i2.
Definition pb4cwin_winA_n23_i3 : Q := (3609900632392859172976236646405269320658188294258601041108604763657425130120280493118026026057728#3681405)%Q.
Example pb4cwin_foldsegA_n23_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i3.
Definition pb4cwin_winA_n23_i4 : Q := (-10050019358363492541407685089390936765148418866991450523289472236494187514476893573771952128#88179)%Q.
Example pb4cwin_foldsegA_n23_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i4.
Definition pb4cwin_winA_n23_i5 : Q := (6905481973766631618825546503749301520882679509158135751982283670246821368539929116672#7567)%Q.
Example pb4cwin_foldsegA_n23_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i5.
Definition pb4cwin_winA_n23_i6 : Q := (193871646358245873918017109947451183121299186387883855627430248305409784597104820224#284098815)%Q.
Example pb4cwin_foldsegA_n23_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i6.
Definition pb4cwin_winA_n23_i7 : Q := (-6869210479671858967659999434407759446012597780038617821540159217974449799168#61474519)%Q.
Example pb4cwin_foldsegA_n23_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((56 + t)%nat))
                   8%nat))
       pb4cwin_winA_n23_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i7.
Definition pb4cwin_winA_n23_i8 : Q := (33580239579695021476767557279823927048827143211426696270568226816#1021683)%Q.
Example pb4cwin_foldsegA_n23_i8 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n23 ((64 + t)%nat))
                   6%nat))
       pb4cwin_winA_n23_i8) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n23_i8.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n23 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n23 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n23.
Definition pb4cwin_winB_n23_i0 : Q := (335315062661880211037934496615316121236166747812117035052590510875220094656422086336616386931982336#21)%Q.
Example pb4cwin_foldsegB_n23_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i0.
Definition pb4cwin_winB_n23_i1 : Q := (-47021740593498120020561995407289649844276978098669406652929134596733440841836147670815849280700416#3003)%Q.
Example pb4cwin_foldsegB_n23_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i1.
Definition pb4cwin_winB_n23_i2 : Q := (162447852561391764162635459955393628902017564372011681233455180140509579507433773890857865314304#33649)%Q.
Example pb4cwin_foldsegB_n23_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i2.
Definition pb4cwin_winB_n23_i3 : Q := (-925897335585596525156810702255091217953378042689189359135019555529173507869563089938982895616#3681405)%Q.
Example pb4cwin_foldsegB_n23_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i3.
Definition pb4cwin_winB_n23_i4 : Q := (121059289507658283777891410257156396095981987444454458677526912815189586316758089728000#74613)%Q.
Example pb4cwin_foldsegB_n23_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i4.
Definition pb4cwin_winB_n23_i5 : Q := (-4738233000330801835697387027037893441291984851021545742671598665126283336220672#7567)%Q.
Example pb4cwin_foldsegB_n23_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i5.
Definition pb4cwin_winB_n23_i6 : Q := (-5672212737566924126335359006988448287396297618484165102844545047935039045632#94699605)%Q.
Example pb4cwin_foldsegB_n23_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i6.
Definition pb4cwin_winB_n23_i7 : Q := (82408175035255447542459930096947087972857875159082606449331353419776#184423557)%Q.
Example pb4cwin_foldsegB_n23_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((56 + t)%nat))
                   8%nat))
       pb4cwin_winB_n23_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i7.
Definition pb4cwin_winB_n23_i8 : Q := (-86959218310377553891594446510409593334768570477662175232#11238513)%Q.
Example pb4cwin_foldsegB_n23_i8 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n23 ((64 + t)%nat))
                   6%nat))
       pb4cwin_winB_n23_i8) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n23_i8.