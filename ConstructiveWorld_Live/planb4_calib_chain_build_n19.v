(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 19 *)
(** * planb4_calib_chain_build_n19: poleA/poleB chain tails and the assembled abqA/abqB values for point 19, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n19 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 19, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n19 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n19; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n19.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n19.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n19 : list Q :=
  [(-721203674609825514927541867877236950445518253482500484381078411775716792926732288#1)%Q; (2257474574523410437926062600497646984995459617068451750997583370655119194036633600#1)%Q; (-6867775256882541265873138847587222440603784420035349594704715206076794316783616000#1)%Q; (20303144379809789621372282693479115311745396591250004696604868791009458425692160000#1)%Q; (-58315447116739902227629169520183900271217702086037612890549368898287897443041280000#1)%Q; (162700593121623707500537302471466471971294067937153489887930375983906264239308800000#1)%Q; (-440843923314968620931904807905337029274234580523179890216771378943840667828224000000#1)%Q; (1159760506406469885543121435040669036140191549425040523994632394388146183208960000000#1)%Q; (-2961619780260154555779751296346318445479146219286910593820370261338206555340800000000#1)%Q; (7339213750676805183136051001906441928830610217755851775374553294806047522816000000000#1)%Q; (-17644212952961184115838601256250270558941407198195506810062533816686089338880000000000#1)%Q; (41138834504598066560271715271503278510183007657917332900513297172836594483200000000000#1)%Q; (-92993744000993779787910981645295766254062169091570029025722261883571929088000000000000#1)%Q; (203729004692532604392160491782864809670300311085100575372601499698897879040000000000000#1)%Q; (-432398682876204872466631995834592947524203588109458805056266177696969523200000000000000#1)%Q; (888734997311729200939284981299103185870111551928308301377884105975267328000000000000000#1)%Q; (-1768190616424030810248701450726492234870825392897850769045373479173488640000000000000000#1)%Q; (3403728361133390586070844536835799371305301237294457212663171185744281600000000000000000#1)%Q; (-6336314466415134931778423853389687366453647030190157868725170698452992000000000000000000#1)%Q; (11401120953573895492582914677077905639093481783212876620080595892961280000000000000000000#1)%Q; (-19817339822111787847129930668340000599118416901919753073857006246297600000000000000000000#1)%Q; (33256151910754779543278106932440756087027463063409110625650361761792000000000000000000000#1)%Q; (-53845820145107069228867307138687453273698616996872840550162922209280000000000000000000000#1)%Q; (84060348186045699420396863506642212185342768081697245496003998515200000000000000000000000#1)%Q; (-126437282786046303879416371524200019582042922275204668011214536704000000000000000000000000#1)%Q; (183091233464924225098242831675843184170052973932148853192754462720000000000000000000000000#1)%Q; (-255039906303014058898619445224496694577726193119912940144060006400000000000000000000000000#1)%Q; (341437036623741171006954584630212809622060989248482630556450816000000000000000000000000000#1)%Q; (-438894550733361163294182454125578958872960783968468538092421120000000000000000000000000000#1)%Q; (541141264318176000611898961732255139712962469465190554612531200000000000000000000000000000#1)%Q; (-639265546155106622528471389927247662341233458651144451522560000000000000000000000000000000#1)%Q; (722691884032157161347697705479684538801530739157591968972800000000000000000000000000000000#1)%Q; (-780845065933160897824659776284355132316520504745628008448000000000000000000000000000000000#1)%Q; (805207072972090055183361191562198961391007535515987607552000000000000000000000000000000000#1)%Q; (-791260387259399753005309310512555480703837654267943976960000000000000000000000000000000000#1)%Q; (739739373544293219505439519846632025432929384712791654400000000000000000000000000000000000#1)%Q; (-656744109791319759741546276019550960861067569409294336000000000000000000000000000000000000#1)%Q; (552593067972724104957757630103132841172682391410442240000000000000000000000000000000000000#1)%Q; (-439695403086549915464786399932583995314755038347264000000000000000000000000000000000000000#1)%Q; (330049763724230307211183749636668423146394909409280000000000000000000000000000000000000000#1)%Q; (-233084610174912725961548642989768522687633476812800000000000000000000000000000000000000000#1)%Q; (154398061329230578250885875802339879008127365939200000000000000000000000000000000000000000#1)%Q; (-95606676553395941673597255252200109728363184128000000000000000000000000000000000000000000#1)%Q; (55129228848772756701434833870012598257943838720000000000000000000000000000000000000000000#1)%Q; (-29472498665177425582737572508003317708541132800000000000000000000000000000000000000000000#1)%Q; (14534495968199346370969723197341491880001536000000000000000000000000000000000000000000000#1)%Q; (-6573266361098680874483394853993116241756160000000000000000000000000000000000000000000000#1)%Q; (2707456830652656221354968982696023713382400000000000000000000000000000000000000000000000#1)%Q; (-1007311187690190576994249894260822245376000000000000000000000000000000000000000000000000#1)%Q; (335157751235266141565441769950570086400000000000000000000000000000000000000000000000000#1)%Q; (-98502999803742290263782892551693926400000000000000000000000000000000000000000000000000#1)%Q; (25173902798685666689446074422132736000000000000000000000000000000000000000000000000000#1)%Q; (-5480536870269224150514765387530240000000000000000000000000000000000000000000000000000#1)%Q; (988229258747703664498922907238400000000000000000000000000000000000000000000000000000#1)%Q; (-141693624066275267750744031232000000000000000000000000000000000000000000000000000000#1)%Q; (15145951573178155700982906880000000000000000000000000000000000000000000000000000000#1)%Q; (-1072921664907983392551731200000000000000000000000000000000000000000000000000000000#1)%Q; (37778931862957161709568000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n19 : list Q :=
  [(-721203674609825514927541867877236950445518253482500484381078411775716792926732288#1)%Q; (2257474574523410437926062600497646984995459617068451750997583370655119194036633600#1)%Q; (-6867775256882541265873138847587222440603784420035349594704715206076794316783616000#1)%Q; (20303144379809789621372282693479115311745396591250004696604868791009458425692160000#1)%Q; (-58315447116739902227629169520183900271217702086037612890549368898287897443041280000#1)%Q; (162700593121623707500537302471466471971294067937153489887930375983906264239308800000#1)%Q; (-440843923314968620931904807905337029274234580523179890216771378943840667828224000000#1)%Q; (1159760506406469885543121435040669036140191549425040523994632394388146183208960000000#1)%Q; (-2961619780260154555779751296346318445479146219286910593820370261338206555340800000000#1)%Q; (7339213750676805183136051001906441928830610217755851775374553294806047522816000000000#1)%Q; (-17644212952961184115838601256250270558941407198195506810062533816686089338880000000000#1)%Q; (41138834504598066560271715271503278510183007657917332900513297172836594483200000000000#1)%Q; (-92993744000993779787910981645295766254062169091570029025722261883571929088000000000000#1)%Q; (203729004692532604392160491782864809670300311085100575372601499698897879040000000000000#1)%Q; (-432398682876204872466631995834592947524203588109458805056266177696969523200000000000000#1)%Q; (888734997311729200939284981299103185870111551928308301377884105975267328000000000000000#1)%Q; (-1768190616424030810248701450726492234870825392897850769045373479173488640000000000000000#1)%Q; (3403728361133390586070844536835799371305301237294457212663171185744281600000000000000000#1)%Q; (-6336314466415134931778423853389687366453647030190157868725170698452992000000000000000000#1)%Q; (11401120953573895492582914677077905639093481783212876620080595892961280000000000000000000#1)%Q; (-19817339822111787847129930668340000599118416901919753073857006246297600000000000000000000#1)%Q; (33256151910754779543278106932440756087027463063409110625650361761792000000000000000000000#1)%Q; (-53845820145107069228867307138687453273698616996872840550162922209280000000000000000000000#1)%Q; (84060348186045699420396863506642212185342768081697245496003998515200000000000000000000000#1)%Q; (-126437282786046303879416371524200019582042922275204668011214536704000000000000000000000000#1)%Q; (183091233464924225098242831675843184170052973932148853192754462720000000000000000000000000#1)%Q; (-255039906303014058898619445224496694577726193119912940144060006400000000000000000000000000#1)%Q; (341437036623741171006954584630212809622060989248482630556450816000000000000000000000000000#1)%Q; (-438894550733361163294182454125578958872960783968468538092421120000000000000000000000000000#1)%Q; (541141264318176000611898961732255139712962469465190554612531200000000000000000000000000000#1)%Q; (-639265546155106622528471389927247662341233458651144451522560000000000000000000000000000000#1)%Q; (722691884032157161347697705479684538801530739157591968972800000000000000000000000000000000#1)%Q; (-780845065933160897824659776284355132316520504745628008448000000000000000000000000000000000#1)%Q; (805207072972090055183361191562198961391007535515987607552000000000000000000000000000000000#1)%Q; (-791260387259399753005309310512555480703837654267943976960000000000000000000000000000000000#1)%Q; (739739373544293219505439519846632025432929384712791654400000000000000000000000000000000000#1)%Q; (-656744109791319759741546276019550960861067569409294336000000000000000000000000000000000000#1)%Q; (552593067972724104957757630103132841172682391410442240000000000000000000000000000000000000#1)%Q; (-439695403086549915464786399932583995314755038347264000000000000000000000000000000000000000#1)%Q; (330049763724230307211183749636668423146394909409280000000000000000000000000000000000000000#1)%Q; (-233084610174912725961548642989768522687633476812800000000000000000000000000000000000000000#1)%Q; (154398061329230578250885875802339879008127365939200000000000000000000000000000000000000000#1)%Q; (-95606676553395941673597255252200109728363184128000000000000000000000000000000000000000000#1)%Q; (55129228848772756701434833870012598257943838720000000000000000000000000000000000000000000#1)%Q; (-29472498665177425582737572508003317708541132800000000000000000000000000000000000000000000#1)%Q; (14534495968199346370969723197341491880001536000000000000000000000000000000000000000000000#1)%Q; (-6573266361098680874483394853993116241756160000000000000000000000000000000000000000000000#1)%Q; (2707456830652656221354968982696023713382400000000000000000000000000000000000000000000000#1)%Q; (-1007311187690190576994249894260822245376000000000000000000000000000000000000000000000000#1)%Q; (335157751235266141565441769950570086400000000000000000000000000000000000000000000000000#1)%Q; (-98502999803742290263782892551693926400000000000000000000000000000000000000000000000000#1)%Q; (25173902798685666689446074422132736000000000000000000000000000000000000000000000000000#1)%Q; (-5480536870269224150514765387530240000000000000000000000000000000000000000000000000000#1)%Q; (988229258747703664498922907238400000000000000000000000000000000000000000000000000000#1)%Q; (-141693624066275267750744031232000000000000000000000000000000000000000000000000000000#1)%Q; (15145951573178155700982906880000000000000000000000000000000000000000000000000000000#1)%Q; (-1072921664907983392551731200000000000000000000000000000000000000000000000000000000#1)%Q; (37778931862957161709568000000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n19 : Z := (198704694658268551223364166453171896837668242425695960964203829860947575310886321039336032698368)%Z.
Definition pb4cwin_litB_n19 : Z := (-63249668740858340766244433286737341213332934478106565182980960778739215992866516997486380339200)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n19_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              (planb4_g1_shp 19))
       pb4cwin_state_n19_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i1.

Example pb4cwin_remcertA_n19_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_state_n19_i1)
       pb4cwin_state_n19_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i2.

Example pb4cwin_remcertA_n19_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_state_n19_i2)
       pb4cwin_state_n19_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i3.

Example pb4cwin_remcertA_n19_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_state_n19_i3)
       pb4cwin_state_n19_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i4.

Example pb4cwin_remcertA_n19_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_state_n19_i4)
       pb4cwin_state_n19_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i5.

Example pb4cwin_remcertA_n19_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_state_n19_i5)
       pb4cwin_state_n19_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i6.

Example pb4cwin_remcertA_n19_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_state_n19_i6)
       pb4cwin_state_n19_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n19_i7.

(* poleA channel: assemble the chain tail from the 8 block certificates. *)
Lemma pb4cwin_poleAeq_n19 :
  zzId (planb4_g1_poleA 19) pb4cwin_lit_poleA_n19.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 19 + 1)%nat) with ((8 + 50)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 50%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) (planb4_g1_shp 19))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i0).
  change 50%nat with ((8 + 42)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 42%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat (planb4_g1_shp 19)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i1).
  change 42%nat with ((8 + 34)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 34%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_state_n19_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i2).
  change 34%nat with ((8 + 26)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 26%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_state_n19_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i3).
  change 26%nat with ((8 + 18)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 18%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_state_n19_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 18%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_state_n19_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) (8 + 10)%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_state_n19_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 10%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_state_n19_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 10%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_state_n19_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) (8 + 2)%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_state_n19_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 2%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_state_n19_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n19_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n19_i7).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n19.
Lemma pb4cwin_build_poleA_n19 :
  zzId (plq_eqb (planb4_g1_poleA 19) pb4cwin_lit_poleA_n19) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n19).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n19.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n19_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              (planb4_g1_shm 19))
       pb4cwin_stateB_n19_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i1.

Example pb4cwin_remcertB_n19_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_stateB_n19_i1)
       pb4cwin_stateB_n19_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i2.

Example pb4cwin_remcertB_n19_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_stateB_n19_i2)
       pb4cwin_stateB_n19_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i3.

Example pb4cwin_remcertB_n19_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_stateB_n19_i3)
       pb4cwin_stateB_n19_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i4.

Example pb4cwin_remcertB_n19_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_stateB_n19_i4)
       pb4cwin_stateB_n19_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i5.

Example pb4cwin_remcertB_n19_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_stateB_n19_i5)
       pb4cwin_stateB_n19_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i6.

Example pb4cwin_remcertB_n19_i7 :
  zzId (pb4cwin_rem (planb4_g1_denw 19)
              (hd 0%Q (planb4_g1_denw 19)) 8%nat
              pb4cwin_stateB_n19_i6)
       pb4cwin_stateB_n19_i7.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n19_i7.

(* poleB channel: assemble the chain tail from the 8 block certificates. *)
Lemma pb4cwin_poleBeq_n19 :
  zzId (planb4_g1_poleB 19) pb4cwin_lit_poleB_n19.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 19 + 1)%nat) with ((8 + 50)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 50%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) (planb4_g1_shm 19))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i0).
  change 50%nat with ((8 + 42)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 42%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat (planb4_g1_shm 19)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i1).
  change 42%nat with ((8 + 34)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 34%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_stateB_n19_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i2).
  change 34%nat with ((8 + 26)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 26%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_stateB_n19_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i3).
  change 26%nat with ((8 + 18)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 18%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_stateB_n19_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 18%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_stateB_n19_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) (8 + 10)%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_stateB_n19_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 10%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_stateB_n19_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i5).
  change (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 10%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_stateB_n19_i5))
    with (planb4_g1_laur_go (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) (8 + 2)%nat
             (pb4cwin_rem (planb4_g1_denw 19) (hd 0%Q (planb4_g1_denw 19)) 8%nat
                pb4cwin_stateB_n19_i5)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 2%nat (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19)))
               (pb4cwin_rem (planb4_g1_denw 19) ((hd 0%Q (planb4_g1_denw 19))) 8%nat pb4cwin_stateB_n19_i5))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n19_i7).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n19_i7).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n19.
Lemma pb4cwin_build_poleB_n19 :
  zzId (plq_eqb (planb4_g1_poleB 19) pb4cwin_lit_poleB_n19) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n19).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n19.

Lemma pb4cwin_abqAeq_n19 :
  zzId (planb4_abqA 19) (inject_Z pb4cwin_litA_n19).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n19).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n19).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n19.
Lemma pb4cwin_build_abqA_n19 :
  zzId (Qeq_bool (planb4_abqA 19) (inject_Z pb4cwin_litA_n19)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n19).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n19.

Lemma pb4cwin_abqBeq_n19 :
  zzId (planb4_abqB 19) (inject_Z pb4cwin_litB_n19).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n19).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n19).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n19.
Lemma pb4cwin_build_abqB_n19 :
  zzId (Qeq_bool (planb4_abqB 19) (inject_Z pb4cwin_litB_n19)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n19).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n19.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n19 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n19 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n19.
Definition pb4cwin_winA_n19_i0 : Q := (14434945114710600947218690572277947603179224118891445202357387769342778689022066688#105)%Q.
Example pb4cwin_foldsegA_n19_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i0.
Definition pb4cwin_winA_n19_i1 : Q := (5778285528776539876990735037808215783227630875694994044136480505342045472270843904#9009)%Q.
Example pb4cwin_foldsegA_n19_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i1.
Definition pb4cwin_winA_n19_i2 : Q := (-67983163196828850677354479102852247030038196520591077381654223412905663054198341632#25741485)%Q.
Example pb4cwin_foldsegA_n19_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i2.
Definition pb4cwin_winA_n19_i3 : Q := (61340339420154766098423246347635655718812333674899481329968629457793543307264#61425)%Q.
Example pb4cwin_foldsegA_n19_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i3.
Definition pb4cwin_winA_n19_i4 : Q := (-3706574061412230635627582464447852315287070302170631086367072317408804864#146965)%Q.
Example pb4cwin_foldsegA_n19_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i4.
Definition pb4cwin_winA_n19_i5 : Q := (16384780569124060437968495291897667574294852417306773089956108202672128#943372485)%Q.
Example pb4cwin_foldsegA_n19_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i5.
Definition pb4cwin_winA_n19_i6 : Q := (1154147826829699353227101374533268763240800525212803872512278528#4261482225)%Q.
Example pb4cwin_foldsegA_n19_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winA_n19_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i6.
Definition pb4cwin_winA_n19_i7 : Q := (-297604115462388638762475871002938157027033088#57)%Q.
Example pb4cwin_foldsegA_n19_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n19 ((56 + t)%nat))
                   2%nat))
       pb4cwin_winA_n19_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n19_i7.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n19 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n19 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n19.
Definition pb4cwin_winB_n19_i0 : Q := (2697444701001722418328479118202419197569016453898346554067987313994120660766425088#35)%Q.
Example pb4cwin_foldsegB_n19_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i0.
Definition pb4cwin_winB_n19_i1 : Q := (-2953253997263118776107605906677370979163075770005744109373085351091781957368938496#45045)%Q.
Example pb4cwin_foldsegB_n19_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i1.
Definition pb4cwin_winB_n19_i2 : Q := (105919991178084616531947043399819691676763048432078170362102569721434259612237824#8580495)%Q.
Example pb4cwin_foldsegB_n19_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i2.
Definition pb4cwin_winB_n19_i3 : Q := (-15630449913110825132534328038656832922938969368436725571693943252790018048#61425)%Q.
Example pb4cwin_foldsegB_n19_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i3.
Definition pb4cwin_winB_n19_i4 : Q := (135443952225434773135003021704471646496697010018646269877439736840192#373065)%Q.
Example pb4cwin_foldsegB_n19_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i4.
Definition pb4cwin_winB_n19_i5 : Q := (-12316630026068067054301166230126451546653944016089096843287330816#943372485)%Q.
Example pb4cwin_foldsegB_n19_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i5.
Definition pb4cwin_winB_n19_i6 : Q := (-3095389882876772028117977177217787242994148753807507456#157832675)%Q.
Example pb4cwin_foldsegB_n19_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((48 + t)%nat))
                   8%nat))
       pb4cwin_winB_n19_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i6.
Definition pb4cwin_winB_n19_i7 : Q := (1115897445823322965828127693366886400#57)%Q.
Example pb4cwin_foldsegB_n19_i7 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n19 ((56 + t)%nat))
                   2%nat))
       pb4cwin_winB_n19_i7) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n19_i7.