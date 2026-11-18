(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 17 *)
(** * planb4_calib_chain_build_n17: poleA/poleB chain tails and the assembled abqA/abqB values for point 17, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n17 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 17, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n17 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n17; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n17.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n17.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n17 : list Q :=
  [(-1596577077218656448146768590749601684605629186202304426062419138669707264#1)%Q; (4994755917288396669048586837170681115998800730733050183763649472936017920#1)%Q; (-15135958653438974095883825615171081954161386041607435013794383780013670400#1)%Q; (44420464264748422604980482586770121877857047496842029961429730709209088000#1)%Q; (-126220696402300687544992991656249177394252497026609400439752596494745600000#1)%Q; (347167799127584241347503765883922039469844058898182972288619379267993600000#1)%Q; (-924031123531273008297991246001554829866169467015218014379185677533184000000#1)%Q; (2379240653352600740302498940796175547902082166872377026496220029255680000000#1)%Q; (-5924476180919363644121612312895772101328641522542209928239085780992000000000#1)%Q; (14261489802117114499382523266791100406775102008157644258535041662976000000000#1)%Q; (-33175267590765263322772243580140560633339459797680631385988676976640000000000#1)%Q; (74544711491424776754829738090666957401014762656682971469939998720000000000000#1)%Q; (-161724795998552511646095253522623444213368489183009798416517562368000000000000#1)%Q; (338597416443983912975049250012589840876027919742405363655329710080000000000000#1)%Q; (-683773435290825477829111164540564803058851933270484120568542003200000000000000#1)%Q; (1331128590890132689137591473744882325424619348657172883536084992000000000000000#1)%Q; (-2496587510146475831931255028401593074330909867320926019780608000000000000000000#1)%Q; (4508303692590171009746704354940156605759554589605965478861209600000000000000000#1)%Q; (-7832835582608941801947520945299316867011908921451012490788864000000000000000000#1)%Q; (13084038735556451377177145147627409503023113588475860457881600000000000000000000#1)%Q; (-20995913301221181600356145860208473813235533316468189115187200000000000000000000#1)%Q; (32338849044281083618950419319381892485665442529435877113856000000000000000000000#1)%Q; (-47764909349869755637524338884183829683652096731887005859840000000000000000000000#1)%Q; (67585575650095928821150166827415499745070074564504977408000000000000000000000000#1)%Q; (-91514702662620287379771154447036216280405355374881800192000000000000000000000000#1)%Q; (118443732010933171257696146058814157642627328977833820160000000000000000000000000#1)%Q; (-146341466364244725453821079329034936335892248672390348800000000000000000000000000#1)%Q; (172368892081803643674420823236499418029631582697947136000000000000000000000000000#1)%Q; (-193256989032045699326272705697579660188301019955855360000000000000000000000000000#1)%Q; (205913560298660189939328342204708061737929099391795200000000000000000000000000000#1)%Q; (-208127156414756805693061500699378606491717611814912000000000000000000000000000000#1)%Q; (199163602200921200067498926372288407003632626565120000000000000000000000000000000#1)%Q; (-180046011469318717743687301630481575585979039744000000000000000000000000000000000#1)%Q; (153391854968326358110606622832958783883699027968000000000000000000000000000000000#1)%Q; (-122829014991641219831454337922942658587614248960000000000000000000000000000000000#1)%Q; (92167037928691471909900229142228731616349388800000000000000000000000000000000000#1)%Q; (-64589042154015612306474276321988056774082560000000000000000000000000000000000000#1)%Q; (42110274701907007582462101976965207430266880000000000000000000000000000000000000#1)%Q; (-25431116322178486587624212190242130205081600000000000000000000000000000000000000#1)%Q; (14154854488515726906840506860882695815168000000000000000000000000000000000000000#1)%Q; (-7218816024628376139942717052119783833600000000000000000000000000000000000000000#1)%Q; (3350082029125550802319237973746384896000000000000000000000000000000000000000000#1)%Q; (-1403149329073640390346095972795285504000000000000000000000000000000000000000000#1)%Q; (525146135756189227214064627115622400000000000000000000000000000000000000000000#1)%Q; (-173469195551580149754580947487948800000000000000000000000000000000000000000000#1)%Q; (49787879322997485960447553175552000000000000000000000000000000000000000000000#1)%Q; (-12163574056826857991234996142080000000000000000000000000000000000000000000000#1)%Q; (2459417292890224904684280217600000000000000000000000000000000000000000000000#1)%Q; (-395129110484906005938307072000000000000000000000000000000000000000000000000#1)%Q; (47291548846887703286906880000000000000000000000000000000000000000000000000#1)%Q; (-3748378395777780888371200000000000000000000000000000000000000000000000000#1)%Q; (147573952589676412928000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n17 : list Q :=
  [(-1596577077218656448146768590749601684605629186202304426062419138669707264#1)%Q; (4994755917288396669048586837170681115998800730733050183763649472936017920#1)%Q; (-15135958653438974095883825615171081954161386041607435013794383780013670400#1)%Q; (44420464264748422604980482586770121877857047496842029961429730709209088000#1)%Q; (-126220696402300687544992991656249177394252497026609400439752596494745600000#1)%Q; (347167799127584241347503765883922039469844058898182972288619379267993600000#1)%Q; (-924031123531273008297991246001554829866169467015218014379185677533184000000#1)%Q; (2379240653352600740302498940796175547902082166872377026496220029255680000000#1)%Q; (-5924476180919363644121612312895772101328641522542209928239085780992000000000#1)%Q; (14261489802117114499382523266791100406775102008157644258535041662976000000000#1)%Q; (-33175267590765263322772243580140560633339459797680631385988676976640000000000#1)%Q; (74544711491424776754829738090666957401014762656682971469939998720000000000000#1)%Q; (-161724795998552511646095253522623444213368489183009798416517562368000000000000#1)%Q; (338597416443983912975049250012589840876027919742405363655329710080000000000000#1)%Q; (-683773435290825477829111164540564803058851933270484120568542003200000000000000#1)%Q; (1331128590890132689137591473744882325424619348657172883536084992000000000000000#1)%Q; (-2496587510146475831931255028401593074330909867320926019780608000000000000000000#1)%Q; (4508303692590171009746704354940156605759554589605965478861209600000000000000000#1)%Q; (-7832835582608941801947520945299316867011908921451012490788864000000000000000000#1)%Q; (13084038735556451377177145147627409503023113588475860457881600000000000000000000#1)%Q; (-20995913301221181600356145860208473813235533316468189115187200000000000000000000#1)%Q; (32338849044281083618950419319381892485665442529435877113856000000000000000000000#1)%Q; (-47764909349869755637524338884183829683652096731887005859840000000000000000000000#1)%Q; (67585575650095928821150166827415499745070074564504977408000000000000000000000000#1)%Q; (-91514702662620287379771154447036216280405355374881800192000000000000000000000000#1)%Q; (118443732010933171257696146058814157642627328977833820160000000000000000000000000#1)%Q; (-146341466364244725453821079329034936335892248672390348800000000000000000000000000#1)%Q; (172368892081803643674420823236499418029631582697947136000000000000000000000000000#1)%Q; (-193256989032045699326272705697579660188301019955855360000000000000000000000000000#1)%Q; (205913560298660189939328342204708061737929099391795200000000000000000000000000000#1)%Q; (-208127156414756805693061500699378606491717611814912000000000000000000000000000000#1)%Q; (199163602200921200067498926372288407003632626565120000000000000000000000000000000#1)%Q; (-180046011469318717743687301630481575585979039744000000000000000000000000000000000#1)%Q; (153391854968326358110606622832958783883699027968000000000000000000000000000000000#1)%Q; (-122829014991641219831454337922942658587614248960000000000000000000000000000000000#1)%Q; (92167037928691471909900229142228731616349388800000000000000000000000000000000000#1)%Q; (-64589042154015612306474276321988056774082560000000000000000000000000000000000000#1)%Q; (42110274701907007582462101976965207430266880000000000000000000000000000000000000#1)%Q; (-25431116322178486587624212190242130205081600000000000000000000000000000000000000#1)%Q; (14154854488515726906840506860882695815168000000000000000000000000000000000000000#1)%Q; (-7218816024628376139942717052119783833600000000000000000000000000000000000000000#1)%Q; (3350082029125550802319237973746384896000000000000000000000000000000000000000000#1)%Q; (-1403149329073640390346095972795285504000000000000000000000000000000000000000000#1)%Q; (525146135756189227214064627115622400000000000000000000000000000000000000000000#1)%Q; (-173469195551580149754580947487948800000000000000000000000000000000000000000000#1)%Q; (49787879322997485960447553175552000000000000000000000000000000000000000000000#1)%Q; (-12163574056826857991234996142080000000000000000000000000000000000000000000000#1)%Q; (2459417292890224904684280217600000000000000000000000000000000000000000000000#1)%Q; (-395129110484906005938307072000000000000000000000000000000000000000000000000#1)%Q; (47291548846887703286906880000000000000000000000000000000000000000000000000#1)%Q; (-3748378395777780888371200000000000000000000000000000000000000000000000000#1)%Q; (147573952589676412928000000000000000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n17 : Z := (9135196534172422325782160320248118607228037573693091257161666807246722302248151416832)%Z.
Definition pb4cwin_litB_n17 : Z := (-2907823369058982760508610287834447800205543865791839060542143042454658410305905036800)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n17_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              (planb4_g1_shp 17))
       pb4cwin_state_n17_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n17_i1.

Example pb4cwin_remcertA_n17_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_state_n17_i1)
       pb4cwin_state_n17_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n17_i2.

Example pb4cwin_remcertA_n17_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_state_n17_i2)
       pb4cwin_state_n17_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n17_i3.

Example pb4cwin_remcertA_n17_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_state_n17_i3)
       pb4cwin_state_n17_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n17_i4.

Example pb4cwin_remcertA_n17_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_state_n17_i4)
       pb4cwin_state_n17_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n17_i5.

Example pb4cwin_remcertA_n17_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_state_n17_i5)
       pb4cwin_state_n17_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n17_i6.

(* poleA channel: assemble the chain tail from the 7 block certificates. *)
Lemma pb4cwin_poleAeq_n17 :
  zzId (planb4_g1_poleA 17) pb4cwin_lit_poleA_n17.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 17 + 1)%nat) with ((8 + 44)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 44%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) (planb4_g1_shp 17))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i0).
  change 44%nat with ((8 + 36)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 36%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat (planb4_g1_shp 17)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n17_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i1).
  change 36%nat with ((8 + 28)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 28%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_state_n17_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n17_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i2).
  change 28%nat with ((8 + 20)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 20%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_state_n17_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n17_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i3).
  change 20%nat with ((8 + 12)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 12%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_state_n17_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n17_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) 12%nat
             (pb4cwin_rem (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) 8%nat
                pb4cwin_state_n17_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) (8 + 4)%nat
             (pb4cwin_rem (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) 8%nat
                pb4cwin_state_n17_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 4%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_state_n17_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n17_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n17_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n17_i6).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n17.
Lemma pb4cwin_build_poleA_n17 :
  zzId (plq_eqb (planb4_g1_poleA 17) pb4cwin_lit_poleA_n17) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n17).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n17.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n17_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              (planb4_g1_shm 17))
       pb4cwin_stateB_n17_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n17_i1.

Example pb4cwin_remcertB_n17_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_stateB_n17_i1)
       pb4cwin_stateB_n17_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n17_i2.

Example pb4cwin_remcertB_n17_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_stateB_n17_i2)
       pb4cwin_stateB_n17_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n17_i3.

Example pb4cwin_remcertB_n17_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_stateB_n17_i3)
       pb4cwin_stateB_n17_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n17_i4.

Example pb4cwin_remcertB_n17_i5 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_stateB_n17_i4)
       pb4cwin_stateB_n17_i5.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n17_i5.

Example pb4cwin_remcertB_n17_i6 :
  zzId (pb4cwin_rem (planb4_g1_denw 17)
              (hd 0%Q (planb4_g1_denw 17)) 8%nat
              pb4cwin_stateB_n17_i5)
       pb4cwin_stateB_n17_i6.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n17_i6.

(* poleB channel: assemble the chain tail from the 7 block certificates. *)
Lemma pb4cwin_poleBeq_n17 :
  zzId (planb4_g1_poleB 17) pb4cwin_lit_poleB_n17.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 17 + 1)%nat) with ((8 + 44)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 44%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) (planb4_g1_shm 17))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i0).
  change 44%nat with ((8 + 36)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 36%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat (planb4_g1_shm 17)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n17_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i1).
  change 36%nat with ((8 + 28)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 28%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_stateB_n17_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n17_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i2).
  change 28%nat with ((8 + 20)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 20%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_stateB_n17_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n17_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i3).
  change 20%nat with ((8 + 12)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 12%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_stateB_n17_i3))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n17_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i4).
  change (planb4_g1_laur_go (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) 12%nat
             (pb4cwin_rem (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) 8%nat
                pb4cwin_stateB_n17_i4))
    with (planb4_g1_laur_go (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) (8 + 4)%nat
             (pb4cwin_rem (planb4_g1_denw 17) (hd 0%Q (planb4_g1_denw 17)) 8%nat
                pb4cwin_stateB_n17_i4)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 4%nat (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17)))
               (pb4cwin_rem (planb4_g1_denw 17) ((hd 0%Q (planb4_g1_denw 17))) 8%nat pb4cwin_stateB_n17_i4))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n17_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i5).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n17_i6).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n17_i6).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n17.
Lemma pb4cwin_build_poleB_n17 :
  zzId (plq_eqb (planb4_g1_poleB 17) pb4cwin_lit_poleB_n17) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n17).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n17.

Lemma pb4cwin_abqAeq_n17 :
  zzId (planb4_abqA 17) (inject_Z pb4cwin_litA_n17).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n17).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n17).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n17.
Lemma pb4cwin_build_abqA_n17 :
  zzId (Qeq_bool (planb4_abqA 17) (inject_Z pb4cwin_litA_n17)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n17).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n17.

Lemma pb4cwin_abqBeq_n17 :
  zzId (planb4_abqB 17) (inject_Z pb4cwin_litB_n17).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n17).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n17).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n17.
Lemma pb4cwin_build_abqB_n17 :
  zzId (Qeq_bool (planb4_abqB 17) (inject_Z pb4cwin_litB_n17)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n17).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n17.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n17 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n17 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n17.
Definition pb4cwin_winA_n17_i0 : Q := (10661170881612700260215483593636805421963406414060630609225533528066752512#35)%Q.
Example pb4cwin_foldsegA_n17_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n17_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i0.
Definition pb4cwin_winA_n17_i1 : Q := (1776126376215652172435529121425357545256543875244030055323041046470852608#1365)%Q.
Example pb4cwin_foldsegA_n17_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n17_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i1.
Definition pb4cwin_winA_n17_i2 : Q := (-424290581146544761763446589822907550097520439511728100342645066200776704#111435)%Q.
Example pb4cwin_foldsegA_n17_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n17_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i2.
Definition pb4cwin_winA_n17_i3 : Q := (15160058275130432505692051343603923704728758850788547523560922415104#20475)%Q.
Example pb4cwin_foldsegA_n17_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n17_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i3.
Definition pb4cwin_winA_n17_i4 : Q := (-96935345360456576143611065695397006238948173606332389490077728768#16313115)%Q.
Example pb4cwin_foldsegA_n17_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n17_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i4.
Definition pb4cwin_winA_n17_i5 : Q := (320659573147816404243893710414719653805084653219605750218752#600327945)%Q.
Example pb4cwin_foldsegA_n17_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winA_n17_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i5.
Definition pb4cwin_winA_n17_i6 : Q := (152559638946292309700386875050923657365815296#1275)%Q.
Example pb4cwin_foldsegA_n17_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n17 ((48 + t)%nat))
                   4%nat))
       pb4cwin_winA_n17_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n17_i6.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n17 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n17 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n17.
Definition pb4cwin_winB_n17_i0 : Q := (17919675495776134829469408596476075957308147824720536422104806915663986688#105)%Q.
Example pb4cwin_foldsegB_n17_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n17_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i0.
Definition pb4cwin_winB_n17_i1 : Q := (-11992621824113865876679129106216917292358618769604506631770480836608000#91)%Q.
Example pb4cwin_foldsegB_n17_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n17_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i1.
Definition pb4cwin_winB_n17_i2 : Q := (1966019124569467185975423907703926992722497730234070537930973185572864#111435)%Q.
Example pb4cwin_foldsegB_n17_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n17_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i2.
Definition pb4cwin_winB_n17_i3 : Q := (-3846344363726047004774854856643786642322381065233625799834206208#20475)%Q.
Example pb4cwin_foldsegB_n17_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n17_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i3.
Definition pb4cwin_winB_n17_i4 : Q := (36061621875558516271001136132579544528717111566728331001856#418285)%Q.
Example pb4cwin_foldsegB_n17_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n17_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i4.
Definition pb4cwin_winB_n17_i5 : Q := (-256796835237942740170500674313337834105576141361250304#600327945)%Q.
Example pb4cwin_foldsegB_n17_i5 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((40 + t)%nat))
                   8%nat))
       pb4cwin_winB_n17_i5) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i5.
Definition pb4cwin_winB_n17_i6 : Q := (-9764609939096509836967386305322287104#1275)%Q.
Example pb4cwin_foldsegB_n17_i6 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n17 ((48 + t)%nat))
                   4%nat))
       pb4cwin_winB_n17_i6) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n17_i6.