(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 16 *)
(** * planb4_calib_chain_build_n16: poleA/poleB chain tails and the assembled abqA/abqB values for point 16, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n16 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 16, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n16 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n16; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n16.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n16.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n16 : list Q :=
  [(75307711361479224105870313654755091556883661974823225715949997916160#1)%Q; (-235516304657521352454437237522812044827519655496436334675918627799040#1)%Q; (712046796754695599003501084884336027153598310358804058767779010969600#1)%Q; (-2080633344929885312214159313943982797572539389872179450077012557824000#1)%Q; (5874408626511139163647217703158351877516653911300745580870851624960000#1)%Q; (-16020817997953218979205023936841466182741646721159276271974848921600000#1)%Q; (42190553026089071197422086178007857422037488092123498153236234240000000#1)%Q; (-107250895931788305016277540702557526189199609546667152308699136000000000#1)%Q; (263071291815492683715393104847677769369252133632778664157380608000000000#1)%Q; (-622372157133878669707281969418283681801186356316620336800989184000000000#1)%Q; (1419492995530988642872156554032604326665489337648913228800983040000000000#1)%Q; (-3119671944489013780805794096165664162014101357466726009143296000000000000#1)%Q; (6603075249518142325234755584352965041982080655811520348815360000000000000#1)%Q; (-13452283208199105329024521769651107678691792630905278614732800000000000000#1)%Q; (26362669258149916540708115638827272273520892708768425023897600000000000000#1)%Q; (-49663403966883011182583123544829593206174374727821438222336000000000000000#1)%Q; (89872048583055698177778700084390864011473929635369058304000000000000000000#1)%Q; (-156104897949770285434012287907637232456712402045308502016000000000000000000#1)%Q; (260044706440907162112745913891356027171157840568243978240000000000000000000#1)%Q; (-415074192606549152386374800428637446998130689077768355840000000000000000000#1)%Q; (634197139295475877728487783626493558522605593770223206400000000000000000000#1)%Q; (-926580306181381001418304914741492738018670223929901056000000000000000000000#1)%Q; (1293012277843192199640947362759150993302427889240637440000000000000000000000#1)%Q; (-1721236409995225925548655575973078231670502593239449600000000000000000000000#1)%Q; (2182761291932235115974392466296601510016383283363840000000000000000000000000#1)%Q; (-2633029505237257345711486571663792651633770784358400000000000000000000000000#1)%Q; (3016369846723130649893080765984127559316146434867200000000000000000000000000#1)%Q; (-3275822017020006057348574231829246431275283120128000000000000000000000000000#1)%Q; (3365989913259776938288859551273391863030423224320000000000000000000000000000#1)%Q; (-3265302582735349913058967002850875199755963596800000000000000000000000000000#1)%Q; (2983398982024970826546459621053203376272048128000000000000000000000000000000#1)%Q; (-2560455203166585584489202763640012079418572800000000000000000000000000000000#1)%Q; (2057988539630201075442857522847167035736064000000000000000000000000000000000#1)%Q; (-1543927533148557652420070686395238396723200000000000000000000000000000000000#1)%Q; (1076990994530395932837765452669415189381120000000000000000000000000000000000#1)%Q; (-695514081230337327841381158999972590387200000000000000000000000000000000000#1)%Q; (413740695871652899149037579622248611840000000000000000000000000000000000000#1)%Q; (-225393851379806473959994172875420467200000000000000000000000000000000000000#1)%Q; (111676217427415478158449411023175680000000000000000000000000000000000000000#1)%Q; (-49913619003615454532022500440670208000000000000000000000000000000000000000#1)%Q; (19924650998021007095353597367418880000000000000000000000000000000000000000#1)%Q; (-7016465075766768612096818020352000000000000000000000000000000000000000000#1)%Q; (2145851416361283237343878184960000000000000000000000000000000000000000000#1)%Q; (-558362416957888708955498086400000000000000000000000000000000000000000000#1)%Q; (120190285822123480590791475200000000000000000000000000000000000000000000#1)%Q; (-20547819000333032690286592000000000000000000000000000000000000000000000#1)%Q; (2615840543372382966906880000000000000000000000000000000000000000000000#1)%Q; (-220438591680829141811200000000000000000000000000000000000000000000000#1)%Q; (9223372036854775808000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n16 : list Q :=
  [(75307711361479224105870313654755091556883661974823225715949997916160#1)%Q; (-235516304657521352454437237522812044827519655496436334675918627799040#1)%Q; (712046796754695599003501084884336027153598310358804058767779010969600#1)%Q; (-2080633344929885312214159313943982797572539389872179450077012557824000#1)%Q; (5874408626511139163647217703158351877516653911300745580870851624960000#1)%Q; (-16020817997953218979205023936841466182741646721159276271974848921600000#1)%Q; (42190553026089071197422086178007857422037488092123498153236234240000000#1)%Q; (-107250895931788305016277540702557526189199609546667152308699136000000000#1)%Q; (263071291815492683715393104847677769369252133632778664157380608000000000#1)%Q; (-622372157133878669707281969418283681801186356316620336800989184000000000#1)%Q; (1419492995530988642872156554032604326665489337648913228800983040000000000#1)%Q; (-3119671944489013780805794096165664162014101357466726009143296000000000000#1)%Q; (6603075249518142325234755584352965041982080655811520348815360000000000000#1)%Q; (-13452283208199105329024521769651107678691792630905278614732800000000000000#1)%Q; (26362669258149916540708115638827272273520892708768425023897600000000000000#1)%Q; (-49663403966883011182583123544829593206174374727821438222336000000000000000#1)%Q; (89872048583055698177778700084390864011473929635369058304000000000000000000#1)%Q; (-156104897949770285434012287907637232456712402045308502016000000000000000000#1)%Q; (260044706440907162112745913891356027171157840568243978240000000000000000000#1)%Q; (-415074192606549152386374800428637446998130689077768355840000000000000000000#1)%Q; (634197139295475877728487783626493558522605593770223206400000000000000000000#1)%Q; (-926580306181381001418304914741492738018670223929901056000000000000000000000#1)%Q; (1293012277843192199640947362759150993302427889240637440000000000000000000000#1)%Q; (-1721236409995225925548655575973078231670502593239449600000000000000000000000#1)%Q; (2182761291932235115974392466296601510016383283363840000000000000000000000000#1)%Q; (-2633029505237257345711486571663792651633770784358400000000000000000000000000#1)%Q; (3016369846723130649893080765984127559316146434867200000000000000000000000000#1)%Q; (-3275822017020006057348574231829246431275283120128000000000000000000000000000#1)%Q; (3365989913259776938288859551273391863030423224320000000000000000000000000000#1)%Q; (-3265302582735349913058967002850875199755963596800000000000000000000000000000#1)%Q; (2983398982024970826546459621053203376272048128000000000000000000000000000000#1)%Q; (-2560455203166585584489202763640012079418572800000000000000000000000000000000#1)%Q; (2057988539630201075442857522847167035736064000000000000000000000000000000000#1)%Q; (-1543927533148557652420070686395238396723200000000000000000000000000000000000#1)%Q; (1076990994530395932837765452669415189381120000000000000000000000000000000000#1)%Q; (-695514081230337327841381158999972590387200000000000000000000000000000000000#1)%Q; (413740695871652899149037579622248611840000000000000000000000000000000000000#1)%Q; (-225393851379806473959994172875420467200000000000000000000000000000000000000#1)%Q; (111676217427415478158449411023175680000000000000000000000000000000000000000#1)%Q; (-49913619003615454532022500440670208000000000000000000000000000000000000000#1)%Q; (19924650998021007095353597367418880000000000000000000000000000000000000000#1)%Q; (-7016465075766768612096818020352000000000000000000000000000000000000000000#1)%Q; (2145851416361283237343878184960000000000000000000000000000000000000000000#1)%Q; (-558362416957888708955498086400000000000000000000000000000000000000000000#1)%Q; (120190285822123480590791475200000000000000000000000000000000000000000000#1)%Q; (-20547819000333032690286592000000000000000000000000000000000000000000000#1)%Q; (2615840543372382966906880000000000000000000000000000000000000000000000#1)%Q; (-220438591680829141811200000000000000000000000000000000000000000000000#1)%Q; (9223372036854775808000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n16 : Z := (282973214779696622016215950187841678662610060256252213156259139196540390987530240)%Z.
Definition pb4cwin_litB_n16 : Z := (-90073171789586584040128154439634526292285251198587670851563782113431083126544000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n16_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              (planb4_g1_shp 16))
       pb4cwin_state_n16_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n16_i1.

Example pb4cwin_remcertA_n16_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_state_n16_i1)
       pb4cwin_state_n16_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n16_i2.

Example pb4cwin_remcertA_n16_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_state_n16_i2)
       pb4cwin_state_n16_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n16_i3.

Example pb4cwin_remcertA_n16_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_state_n16_i3)
       pb4cwin_state_n16_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n16_i4.

Example pb4cwin_remcertA_n16_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_state_n16_i4)
       pb4cwin_state_n16_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n16_i5.

Example pb4cwin_remcertA_n16_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_state_n16_i5)
       pb4cwin_state_n16_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n16_i6.

(* poleA channel: assemble the chain tail from the 7 block certificates. *)
Lemma pb4cwin_poleAeq_n16 :
  zzId (planb4_g1_poleA 16) pb4cwin_lit_poleA_n16.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 16 + 1)%nat) with ((8 + 41)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 41%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) (planb4_g1_shp 16))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i0).
  change 41%nat with ((8 + 33)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 33%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat (planb4_g1_shp 16)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n16_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i1).
  change 33%nat with ((8 + 25)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 25%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_state_n16_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n16_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i2).
  change 25%nat with ((8 + 17)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 17%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_state_n16_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n16_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i3).
  change 17%nat with ((8 + 9)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 9%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_state_n16_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n16_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) 9%nat
             (pb4cwin_rem (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) 8%nat
                pb4cwin_state_n16_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) (8 + 1)%nat
             (pb4cwin_rem (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) 8%nat
                pb4cwin_state_n16_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 1%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_state_n16_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n16_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n16_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n16_i6).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n16.
Lemma pb4cwin_build_poleA_n16 :
  zzId (plq_eqb (planb4_g1_poleA 16) pb4cwin_lit_poleA_n16) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n16).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n16.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n16_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              (planb4_g1_shm 16))
       pb4cwin_stateB_n16_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n16_i1.

Example pb4cwin_remcertB_n16_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_stateB_n16_i1)
       pb4cwin_stateB_n16_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n16_i2.

Example pb4cwin_remcertB_n16_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_stateB_n16_i2)
       pb4cwin_stateB_n16_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n16_i3.

Example pb4cwin_remcertB_n16_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_stateB_n16_i3)
       pb4cwin_stateB_n16_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n16_i4.

Example pb4cwin_remcertB_n16_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_stateB_n16_i4)
       pb4cwin_stateB_n16_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n16_i5.

Example pb4cwin_remcertB_n16_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 16)
              (hd 0%Q (planb4_g1_denw 16)) 8%nat
              pb4cwin_stateB_n16_i5)
       pb4cwin_stateB_n16_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n16_i6.

(* poleB channel: assemble the chain tail from the 7 block certificates. *)
Lemma pb4cwin_poleBeq_n16 :
  zzId (planb4_g1_poleB 16) pb4cwin_lit_poleB_n16.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 16 + 1)%nat) with ((8 + 41)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 41%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) (planb4_g1_shm 16))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i0).
  change 41%nat with ((8 + 33)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 33%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat (planb4_g1_shm 16)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n16_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i1).
  change 33%nat with ((8 + 25)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 25%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_stateB_n16_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n16_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i2).
  change 25%nat with ((8 + 17)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 17%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_stateB_n16_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n16_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i3).
  change 17%nat with ((8 + 9)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 9%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_stateB_n16_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n16_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) 9%nat
             (pb4cwin_rem (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) 8%nat
                pb4cwin_stateB_n16_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) (8 + 1)%nat
             (pb4cwin_rem (planb4_g1_denw 16) (hd 0%Q (planb4_g1_denw 16)) 8%nat
                pb4cwin_stateB_n16_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 1%nat (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16)))
               (pb4cwin_rem (planb4_g1_denw 16) ((hd 0%Q (planb4_g1_denw 16))) 8%nat pb4cwin_stateB_n16_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n16_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n16_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n16_i6).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n16.
Lemma pb4cwin_build_poleB_n16 :
  zzId (plq_eqb (planb4_g1_poleB 16) pb4cwin_lit_poleB_n16) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n16).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n16.

Lemma pb4cwin_abqAeq_n16 :
  zzId (planb4_abqA 16) (inject_Z pb4cwin_litA_n16).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n16).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n16).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n16.
Lemma pb4cwin_build_abqA_n16 :
  zzId (Qeq_bool (planb4_abqA 16) (inject_Z pb4cwin_litA_n16)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n16).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n16.

Lemma pb4cwin_abqBeq_n16 :
  zzId (planb4_abqB 16) (inject_Z pb4cwin_litB_n16).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n16).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n16).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n16.
Lemma pb4cwin_build_abqB_n16 :
  zzId (Qeq_bool (planb4_abqB 16) (inject_Z pb4cwin_litB_n16)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n16).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n16.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n16 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n16 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n16.
Definition pb4cwin_winA_n16_i0 : Q := (-503122041068724453359215837673485247892494976356967120455959662559232#35)%Q.
Example pb4cwin_foldsegA_n16_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n16_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i0.
Definition pb4cwin_winA_n16_i1 : Q := (-26511969063018620697345107328557491628662413957035736790709812854784#455)%Q.
Example pb4cwin_foldsegA_n16_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n16_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i1.
Definition pb4cwin_winA_n16_i2 : Q := (396857501654260909326506452510940170694171041764076082769013361344512#2860165)%Q.
Example pb4cwin_foldsegA_n16_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n16_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i2.
Definition pb4cwin_winA_n16_i3 : Q := (-73336304937842838996053540738855847464172050143426140348350464#4095)%Q.
Example pb4cwin_foldsegA_n16_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n16_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i3.
Definition pb4cwin_winA_n16_i4 : Q := (373881842147669863929821317773314507435023821142543799681024#5437705)%Q.
Example pb4cwin_foldsegA_n16_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n16_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i4.
Definition pb4cwin_winA_n16_i5 : Q := (-33719324253336627301614174525048875336339888640360448#23009085)%Q.
Example pb4cwin_foldsegA_n16_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n16_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i5.
Definition pb4cwin_winA_n16_i6 : Q := (-2987956015144520579348272571744256#1)%Q.
Example pb4cwin_foldsegA_n16_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n16 ((48 + t)%nat))
                   1%nat))
       pb4cwin_winA_n16_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n16_i6.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n16 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n16 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n16.
Definition pb4cwin_winB_n16_i0 : Q := (-281795231877521975653247092320306401134049749995132478551429927141376#35)%Q.
Example pb4cwin_foldsegB_n16_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n16_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i0.
Definition pb4cwin_winB_n16_i1 : Q := (8010514296541496327163675104313530284569432498181980830949254889472#1365)%Q.
Example pb4cwin_foldsegB_n16_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n16_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i1.
Definition pb4cwin_winB_n16_i2 : Q := (-5488257780434276224283274007557664521754924622175155073320354840576#8580495)%Q.
Example pb4cwin_foldsegB_n16_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n16_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i2.
Definition pb4cwin_winB_n16_i3 : Q := (18559794587004748496753050244335128008842379273372289728512#4095)%Q.
Example pb4cwin_foldsegB_n16_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n16_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i3.
Definition pb4cwin_winB_n16_i4 : Q := (-4612068228942229235205688895401167377546619405335527424#4601135)%Q.
Example pb4cwin_foldsegB_n16_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n16_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i4.
Definition pb4cwin_winB_n16_i5 : Q := (28060303539348632544877050425141457144799821824#23009085)%Q.
Example pb4cwin_foldsegB_n16_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n16_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i5.
Definition pb4cwin_winB_n16_i6 : Q := (178096056887180839738146816#1)%Q.
Example pb4cwin_foldsegB_n16_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n16 ((48 + t)%nat))
                   1%nat))
       pb4cwin_winB_n16_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n16_i6.