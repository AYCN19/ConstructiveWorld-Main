(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 18 *)
(** * planb4_calib_chain_build_n18: poleA/poleB chain tails and the assembled abqA/abqB values for point 18, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n18 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 18, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n18 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n18; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n18.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n18.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n18 : list Q :=
  [(33907024983824082768125572347613666647246714908012364457976519414226186403840#1)%Q; (-106106266274534228889955274786533860200548623053223640860072495924322437693440#1)%Q; (322205292855253882809628665089200110311755544319454926993580797206466238873600#1)%Q; (-949251811716685874869181207549720076882381120117951004768997042140095709184000#1)%Q; (2712665655755403907631083196887470234861631403448194775234686315026091868160000#1)%Q; (-7517578012704354589432584346707115139615104868446933403766380675710582784000000#1)%Q; (20198482560555974799658764262757377811833318951690615398861244042030612480000000#1)%Q; (-52601983383551871192295562641937897353541171307326887993512453496163532800000000#1)%Q; (132740148974063665035072462502879549115736727554148247011748597557362688000000000#1)%Q; (-324476959725518459252877390377048301670608638334586653954244873834987520000000000#1)%Q; (768070809413330971577013271972111796432607868105237740517419149531545600000000000#1)%Q; (-1759941711024188360231742831932199820509898110698196985037262274376499200000000000#1)%Q; (3902181763585358326256649287031718070980710074083470984273525722841088000000000000#1)%Q; (-8368537500951568206320340942128179729042686807908896928960880752721920000000000000#1)%Q; (17351322224992979868785186551972087170408052863174452747125247495372800000000000000#1)%Q; (-34765718057506355333423518043766355660764403465426337546351358771200000000000000000#1)%Q; (67279981711481508553237811414127176461301063248665403243578177617920000000000000000#1)%Q; (-125690287327683428941351044498442781808552886695755959977823227084800000000000000000#1)%Q; (226541404472422825719104029447144219551150459706018073762596913152000000000000000000#1)%Q; (-393690324694901449971189274112777008130247977729698780740352737280000000000000000000#1)%Q; (659227833010169110836218505708527069970887342407428602209501184000000000000000000000#1)%Q; (-1062874271544188073057756966549200410069911596647248612724572160000000000000000000000#1)%Q; (1648783394234986974453815964879730309335339089547142252357222400000000000000000000000#1)%Q; (-2458818026651098292297684351424119509096387579006660787568640000000000000000000000000#1)%Q; (3522003074539178489119717338821006384028400835825666506096640000000000000000000000000#1)%Q; (-4841104040072727350055409246306466148950734884597451561369600000000000000000000000000#1)%Q; (6378957740622681897881638961026473432470840855456326772326400000000000000000000000000#1)%Q; (-8048783238218409093982961366119518164386942360517613715456000000000000000000000000000#1)%Q; (9713419171013296576296600391681968767870300446334480547840000000000000000000000000000#1)%Q; (-11197446729582648125210338550162459145142978889232521625600000000000000000000000000000#1)%Q; (12313086310729604746679184078653961265506277862733250560000000000000000000000000000000#1)%Q; (-12896110156203300707702990944935734773306268092999925760000000000000000000000000000000#1)%Q; (12843322189523841487659632532281936021596680124524134400000000000000000000000000000000#1)%Q; (-12140540171163523492495391461362551041746510425358336000000000000000000000000000000000#1)%Q; (10871229253125367029818258884781681271260974405386240000000000000000000000000000000000#1)%Q; (-9201296273724676865426113649977998590566742360064000000000000000000000000000000000000#1)%Q; (7343396863018636150069035898942804496397662945280000000000000000000000000000000000000#1)%Q; (-5511277943485457640206076478980780173821581721600000000000000000000000000000000000000#1)%Q; (3877986529333652877442346888422800466336808960000000000000000000000000000000000000000#1)%Q; (-2549686918305067155659858447854638241719255040000000000000000000000000000000000000000#1)%Q; (1560367604754525573786562422896609343202918400000000000000000000000000000000000000000#1)%Q; (-884961122023215388209112017041195877479219200000000000000000000000000000000000000000#1)%Q; (462795222140124281201740270569501740761088000000000000000000000000000000000000000000#1)%Q; (-221857797658444557659580936281054217502720000000000000000000000000000000000000000000#1)%Q; (96824644975972779548137427331925724364800000000000000000000000000000000000000000000#1)%Q; (-38154748931643986611793765936587079680000000000000000000000000000000000000000000000#1)%Q; (13440879988638530387074295283518013440000000000000000000000000000000000000000000000#1)%Q; (-4180781730608084349209755132729753600000000000000000000000000000000000000000000000#1)%Q; (1130387686464505409673774648786944000000000000000000000000000000000000000000000000#1)%Q; (-260262188270954278802135827087360000000000000000000000000000000000000000000000000#1)%Q; (49613749543302247331221471232000000000000000000000000000000000000000000000000000#1)%Q; (-7517946049964197874816253952000000000000000000000000000000000000000000000000000#1)%Q; (848987046290304816518266880000000000000000000000000000000000000000000000000000#1)%Q; (-63515829194596728124211200000000000000000000000000000000000000000000000000000#1)%Q; (2361183241434822606848000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n18 : list Q :=
  [(33907024983824082768125572347613666647246714908012364457976519414226186403840#1)%Q; (-106106266274534228889955274786533860200548623053223640860072495924322437693440#1)%Q; (322205292855253882809628665089200110311755544319454926993580797206466238873600#1)%Q; (-949251811716685874869181207549720076882381120117951004768997042140095709184000#1)%Q; (2712665655755403907631083196887470234861631403448194775234686315026091868160000#1)%Q; (-7517578012704354589432584346707115139615104868446933403766380675710582784000000#1)%Q; (20198482560555974799658764262757377811833318951690615398861244042030612480000000#1)%Q; (-52601983383551871192295562641937897353541171307326887993512453496163532800000000#1)%Q; (132740148974063665035072462502879549115736727554148247011748597557362688000000000#1)%Q; (-324476959725518459252877390377048301670608638334586653954244873834987520000000000#1)%Q; (768070809413330971577013271972111796432607868105237740517419149531545600000000000#1)%Q; (-1759941711024188360231742831932199820509898110698196985037262274376499200000000000#1)%Q; (3902181763585358326256649287031718070980710074083470984273525722841088000000000000#1)%Q; (-8368537500951568206320340942128179729042686807908896928960880752721920000000000000#1)%Q; (17351322224992979868785186551972087170408052863174452747125247495372800000000000000#1)%Q; (-34765718057506355333423518043766355660764403465426337546351358771200000000000000000#1)%Q; (67279981711481508553237811414127176461301063248665403243578177617920000000000000000#1)%Q; (-125690287327683428941351044498442781808552886695755959977823227084800000000000000000#1)%Q; (226541404472422825719104029447144219551150459706018073762596913152000000000000000000#1)%Q; (-393690324694901449971189274112777008130247977729698780740352737280000000000000000000#1)%Q; (659227833010169110836218505708527069970887342407428602209501184000000000000000000000#1)%Q; (-1062874271544188073057756966549200410069911596647248612724572160000000000000000000000#1)%Q; (1648783394234986974453815964879730309335339089547142252357222400000000000000000000000#1)%Q; (-2458818026651098292297684351424119509096387579006660787568640000000000000000000000000#1)%Q; (3522003074539178489119717338821006384028400835825666506096640000000000000000000000000#1)%Q; (-4841104040072727350055409246306466148950734884597451561369600000000000000000000000000#1)%Q; (6378957740622681897881638961026473432470840855456326772326400000000000000000000000000#1)%Q; (-8048783238218409093982961366119518164386942360517613715456000000000000000000000000000#1)%Q; (9713419171013296576296600391681968767870300446334480547840000000000000000000000000000#1)%Q; (-11197446729582648125210338550162459145142978889232521625600000000000000000000000000000#1)%Q; (12313086310729604746679184078653961265506277862733250560000000000000000000000000000000#1)%Q; (-12896110156203300707702990944935734773306268092999925760000000000000000000000000000000#1)%Q; (12843322189523841487659632532281936021596680124524134400000000000000000000000000000000#1)%Q; (-12140540171163523492495391461362551041746510425358336000000000000000000000000000000000#1)%Q; (10871229253125367029818258884781681271260974405386240000000000000000000000000000000000#1)%Q; (-9201296273724676865426113649977998590566742360064000000000000000000000000000000000000#1)%Q; (7343396863018636150069035898942804496397662945280000000000000000000000000000000000000#1)%Q; (-5511277943485457640206076478980780173821581721600000000000000000000000000000000000000#1)%Q; (3877986529333652877442346888422800466336808960000000000000000000000000000000000000000#1)%Q; (-2549686918305067155659858447854638241719255040000000000000000000000000000000000000000#1)%Q; (1560367604754525573786562422896609343202918400000000000000000000000000000000000000000#1)%Q; (-884961122023215388209112017041195877479219200000000000000000000000000000000000000000#1)%Q; (462795222140124281201740270569501740761088000000000000000000000000000000000000000000#1)%Q; (-221857797658444557659580936281054217502720000000000000000000000000000000000000000000#1)%Q; (96824644975972779548137427331925724364800000000000000000000000000000000000000000000#1)%Q; (-38154748931643986611793765936587079680000000000000000000000000000000000000000000000#1)%Q; (13440879988638530387074295283518013440000000000000000000000000000000000000000000000#1)%Q; (-4180781730608084349209755132729753600000000000000000000000000000000000000000000000#1)%Q; (1130387686464505409673774648786944000000000000000000000000000000000000000000000000#1)%Q; (-260262188270954278802135827087360000000000000000000000000000000000000000000000000#1)%Q; (49613749543302247331221471232000000000000000000000000000000000000000000000000000#1)%Q; (-7517946049964197874816253952000000000000000000000000000000000000000000000000000#1)%Q; (848987046290304816518266880000000000000000000000000000000000000000000000000000#1)%Q; (-63515829194596728124211200000000000000000000000000000000000000000000000000000#1)%Q; (2361183241434822606848000000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n18 : Z := (1721813281759225046326104366864833669963917080777214485840375793910051546437923150170685440)%Z.
Definition pb4cwin_litB_n18 : Z := (-548070189746518023261582301593527922531312614122856441062952478601604421453937755271296000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n18_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              (planb4_g1_shp 18))
       pb4cwin_state_n18_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n18_i1.

Example pb4cwin_remcertA_n18_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_state_n18_i1)
       pb4cwin_state_n18_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n18_i2.

Example pb4cwin_remcertA_n18_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_state_n18_i2)
       pb4cwin_state_n18_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n18_i3.

Example pb4cwin_remcertA_n18_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_state_n18_i3)
       pb4cwin_state_n18_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n18_i4.

Example pb4cwin_remcertA_n18_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_state_n18_i4)
       pb4cwin_state_n18_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n18_i5.

Example pb4cwin_remcertA_n18_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_state_n18_i5)
       pb4cwin_state_n18_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n18_i6.

(* poleA channel: assemble the chain tail from the 7 block certificates. *)
Lemma pb4cwin_poleAeq_n18 :
  zzId (planb4_g1_poleA 18) pb4cwin_lit_poleA_n18.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 18 + 1)%nat) with ((8 + 47)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 47%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) (planb4_g1_shp 18))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i0).
  change 47%nat with ((8 + 39)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 39%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat (planb4_g1_shp 18)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n18_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i1).
  change 39%nat with ((8 + 31)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 31%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_state_n18_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n18_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i2).
  change 31%nat with ((8 + 23)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 23%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_state_n18_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n18_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i3).
  change 23%nat with ((8 + 15)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 15%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_state_n18_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n18_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) 15%nat
             (pb4cwin_rem (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) 8%nat
                pb4cwin_state_n18_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) (8 + 7)%nat
             (pb4cwin_rem (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) 8%nat
                pb4cwin_state_n18_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 7%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_state_n18_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n18_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n18_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n18_i6).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n18.
Lemma pb4cwin_build_poleA_n18 :
  zzId (plq_eqb (planb4_g1_poleA 18) pb4cwin_lit_poleA_n18) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n18).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n18.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n18_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              (planb4_g1_shm 18))
       pb4cwin_stateB_n18_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n18_i1.

Example pb4cwin_remcertB_n18_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_stateB_n18_i1)
       pb4cwin_stateB_n18_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n18_i2.

Example pb4cwin_remcertB_n18_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_stateB_n18_i2)
       pb4cwin_stateB_n18_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n18_i3.

Example pb4cwin_remcertB_n18_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_stateB_n18_i3)
       pb4cwin_stateB_n18_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n18_i4.

Example pb4cwin_remcertB_n18_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_stateB_n18_i4)
       pb4cwin_stateB_n18_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n18_i5.

Example pb4cwin_remcertB_n18_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 18)
              (hd 0%Q (planb4_g1_denw 18)) 8%nat
              pb4cwin_stateB_n18_i5)
       pb4cwin_stateB_n18_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n18_i6.

(* poleB channel: assemble the chain tail from the 7 block certificates. *)
Lemma pb4cwin_poleBeq_n18 :
  zzId (planb4_g1_poleB 18) pb4cwin_lit_poleB_n18.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 18 + 1)%nat) with ((8 + 47)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 47%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) (planb4_g1_shm 18))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i0).
  change 47%nat with ((8 + 39)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 39%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat (planb4_g1_shm 18)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n18_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i1).
  change 39%nat with ((8 + 31)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 31%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_stateB_n18_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n18_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i2).
  change 31%nat with ((8 + 23)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 23%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_stateB_n18_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n18_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i3).
  change 23%nat with ((8 + 15)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 15%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_stateB_n18_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n18_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) 15%nat
             (pb4cwin_rem (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) 8%nat
                pb4cwin_stateB_n18_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) (8 + 7)%nat
             (pb4cwin_rem (planb4_g1_denw 18) (hd 0%Q (planb4_g1_denw 18)) 8%nat
                pb4cwin_stateB_n18_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 7%nat (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18)))
               (pb4cwin_rem (planb4_g1_denw 18) ((hd 0%Q (planb4_g1_denw 18))) 8%nat pb4cwin_stateB_n18_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n18_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n18_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n18_i6).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n18.
Lemma pb4cwin_build_poleB_n18 :
  zzId (plq_eqb (planb4_g1_poleB 18) pb4cwin_lit_poleB_n18) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n18).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n18.

Lemma pb4cwin_abqAeq_n18 :
  zzId (planb4_abqA 18) (inject_Z pb4cwin_litA_n18).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n18).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n18).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n18.
Lemma pb4cwin_build_abqA_n18 :
  zzId (Qeq_bool (planb4_abqA 18) (inject_Z pb4cwin_litA_n18)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n18).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n18.

Lemma pb4cwin_abqBeq_n18 :
  zzId (planb4_abqB 18) (inject_Z pb4cwin_litB_n18).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n18).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n18).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n18.
Lemma pb4cwin_build_abqB_n18 :
  zzId (Qeq_bool (planb4_abqB 18) (inject_Z pb4cwin_litB_n18)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n18).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n18.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n18 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n18 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n18.
Definition pb4cwin_winA_n18_i0 : Q := (-6466038294528397629624753884208739877681935316084050966305788042166866542592#1)%Q.
Example pb4cwin_foldsegA_n18_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n18_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i0.
Definition pb4cwin_winA_n18_i1 : Q := (-3385687848477526975649193848781976991200141736691892523604398032581061246976#117)%Q.
Example pb4cwin_foldsegA_n18_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n18_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i1.
Definition pb4cwin_winA_n18_i2 : Q := (357135933921374817812068118466322470487655974075288338974600603582106435584#3519)%Q.
Example pb4cwin_foldsegA_n18_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n18_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i2.
Definition pb4cwin_winA_n18_i3 : Q := (-49382034183575267898877941100444060864163585706341353691068938355474432#1755)%Q.
Example pb4cwin_foldsegA_n18_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n18_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i3.
Definition pb4cwin_winA_n18_i4 : Q := (195357531787044477379802891159191268562336891237993533417948346056704#466089)%Q.
Example pb4cwin_foldsegA_n18_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n18_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i4.
Definition pb4cwin_winA_n18_i5 : Q := (-1988623348219904223346570820866323642907471474588725828091117568#17152227)%Q.
Example pb4cwin_foldsegA_n18_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n18_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i5.
Definition pb4cwin_winA_n18_i6 : Q := (-3561541460929651007808549615776995364260586459469185024#11068785)%Q.
Example pb4cwin_foldsegA_n18_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n18 ((48 + t)%nat))
                   7%nat))
       pb4cwin_winA_n18_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n18_i6.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n18 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n18 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n18.
Definition pb4cwin_winB_n18_i0 : Q := (-10871660526576539671518966695775239156398293662154106624369731213308846931968#3)%Q.
Example pb4cwin_foldsegB_n18_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n18_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i0.
Definition pb4cwin_winB_n18_i1 : Q := (344593744239835251865577455553653557514175708003918054164972181613203947520#117)%Q.
Example pb4cwin_foldsegB_n18_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n18_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i1.
Definition pb4cwin_winB_n18_i2 : Q := (-554154213198255618860957841641691061768761275954192654731461122481717248#1173)%Q.
Example pb4cwin_foldsegB_n18_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n18_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i2.
Definition pb4cwin_winB_n18_i3 : Q := (12557464707363624168021533148624968806602974050511696550605319307264#1755)%Q.
Example pb4cwin_foldsegB_n18_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n18_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i3.
Definition pb4cwin_winB_n18_i4 : Q := (-217119602278557366757862711523014156748435389801449058126004224#35853)%Q.
Example pb4cwin_foldsegB_n18_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n18_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i4.
Definition pb4cwin_winB_n18_i5 : Q := (1539943749861454120506103486474954724828408776063373541376#17152227)%Q.
Example pb4cwin_foldsegB_n18_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n18_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i5.
Definition pb4cwin_winB_n18_i6 : Q := (27017609212189222840868572817045622812158459904#1229865)%Q.
Example pb4cwin_foldsegB_n18_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n18 ((48 + t)%nat))
                   7%nat))
       pb4cwin_winB_n18_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n18_i6.