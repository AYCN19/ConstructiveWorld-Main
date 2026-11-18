(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 12 *)
(** * planb4_calib_chain_build_n12: poleA/poleB chain tails and the assembled abqA/abqB values for point 12, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n12 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 12, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n12 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n12; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n12.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n12.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n12 : list Q :=
  [(381240762467434666034018869920846508018648574066688#1)%Q; (-1190066095830148969727030078947135976227920989388800#1)%Q; (3550939780526549986642299044824575401211540904345600#1)%Q; (-10123238490998135356833248138434769018433428258816000#1)%Q; (27559777719623027309595914673468322753088942243840000#1)%Q; (-71607624609348696104107350924736329508096206438400000#1)%Q; (177454327945417777140285283505091394826701635584000000#1)%Q; (-419122710510620092919983742055547809002768302080000000#1)%Q; (942694687034247037081940852293764421881377587200000000#1)%Q; (-2017370785266000444400186573211608557494992896000000000#1)%Q; (4103484722481429699235376082561399839124357120000000000#1)%Q; (-7924904279931568098214296067542700455572275200000000000#1)%Q; (14513774709390721232963205045091915423285248000000000000#1)%Q; (-25172522398801729052549122322650829003161600000000000000#1)%Q; (41284332094451723987323876867778890484940800000000000000#1)%Q; (-63920137281717228837564970799012402692096000000000000000#1)%Q; (93258012934279404451265614692215139860480000000000000000#1)%Q; (-127950526505504065781256759152226598912000000000000000000#1)%Q; (164707306824406078269582729792620331008000000000000000000#1)%Q; (-198420076777209483220030873296605020160000000000000000000#1)%Q; (223052470165621184909974694123064524800000000000000000000#1)%Q; (-233216096832440716011030914583756800000000000000000000000#1)%Q; (225956413450632646149832243549306880000000000000000000000#1)%Q; (-202000818629639116594256706902425600000000000000000000000#1)%Q; (165806835085723102251392411107328000000000000000000000000#1)%Q; (-124243333835295248967036357836800000000000000000000000000#1)%Q; (84414035160091419321433063424000000000000000000000000000#1)%Q; (-51581873185436335654278529024000000000000000000000000000#1)%Q; (28069065378443174411763712000000000000000000000000000000#1)%Q; (-13436394746118956315888844800000000000000000000000000000#1)%Q; (5570459790382477808238592000000000000000000000000000000#1)%Q; (-1959590621260119990599680000000000000000000000000000000#1)%Q; (568770532243465148825600000000000000000000000000000000#1)%Q; (-130780170316700188672000000000000000000000000000000000#1)%Q; (22336446776874106880000000000000000000000000000000000#1)%Q; (-2519201041560371200000000000000000000000000000000000#1)%Q; (140737488355328000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n12 : list Q :=
  [(381240762467434666034018869920846508018648574066688#1)%Q; (-1190066095830148969727030078947135976227920989388800#1)%Q; (3550939780526549986642299044824575401211540904345600#1)%Q; (-10123238490998135356833248138434769018433428258816000#1)%Q; (27559777719623027309595914673468322753088942243840000#1)%Q; (-71607624609348696104107350924736329508096206438400000#1)%Q; (177454327945417777140285283505091394826701635584000000#1)%Q; (-419122710510620092919983742055547809002768302080000000#1)%Q; (942694687034247037081940852293764421881377587200000000#1)%Q; (-2017370785266000444400186573211608557494992896000000000#1)%Q; (4103484722481429699235376082561399839124357120000000000#1)%Q; (-7924904279931568098214296067542700455572275200000000000#1)%Q; (14513774709390721232963205045091915423285248000000000000#1)%Q; (-25172522398801729052549122322650829003161600000000000000#1)%Q; (41284332094451723987323876867778890484940800000000000000#1)%Q; (-63920137281717228837564970799012402692096000000000000000#1)%Q; (93258012934279404451265614692215139860480000000000000000#1)%Q; (-127950526505504065781256759152226598912000000000000000000#1)%Q; (164707306824406078269582729792620331008000000000000000000#1)%Q; (-198420076777209483220030873296605020160000000000000000000#1)%Q; (223052470165621184909974694123064524800000000000000000000#1)%Q; (-233216096832440716011030914583756800000000000000000000000#1)%Q; (225956413450632646149832243549306880000000000000000000000#1)%Q; (-202000818629639116594256706902425600000000000000000000000#1)%Q; (165806835085723102251392411107328000000000000000000000000#1)%Q; (-124243333835295248967036357836800000000000000000000000000#1)%Q; (84414035160091419321433063424000000000000000000000000000#1)%Q; (-51581873185436335654278529024000000000000000000000000000#1)%Q; (28069065378443174411763712000000000000000000000000000000#1)%Q; (-13436394746118956315888844800000000000000000000000000000#1)%Q; (5570459790382477808238592000000000000000000000000000000#1)%Q; (-1959590621260119990599680000000000000000000000000000000#1)%Q; (568770532243465148825600000000000000000000000000000000#1)%Q; (-130780170316700188672000000000000000000000000000000000#1)%Q; (22336446776874106880000000000000000000000000000000000#1)%Q; (-2519201041560371200000000000000000000000000000000000#1)%Q; (140737488355328000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n12 : Z := (1130050022478355843389594407333460371479208703173241822248960)%Z.
Definition pb4cwin_litB_n12 : Z := (-359706094037075538479341958504245342201097233184198048155200)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n12_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              (planb4_g1_shp 12))
       pb4cwin_state_n12_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n12_i1.

Example pb4cwin_remcertA_n12_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              pb4cwin_state_n12_i1)
       pb4cwin_state_n12_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n12_i2.

Example pb4cwin_remcertA_n12_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              pb4cwin_state_n12_i2)
       pb4cwin_state_n12_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n12_i3.

Example pb4cwin_remcertA_n12_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              pb4cwin_state_n12_i3)
       pb4cwin_state_n12_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n12_i4.

(* poleA channel: assemble the chain tail from the 5 block certificates. *)
Lemma pb4cwin_poleAeq_n12 :
  zzId (planb4_g1_poleA 12) pb4cwin_lit_poleA_n12.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 12 + 1)%nat) with ((8 + 29)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 29%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) (planb4_g1_shp 12))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n12_i0).
  change 29%nat with ((8 + 21)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 21%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12)))
               (pb4cwin_rem (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) 8%nat (planb4_g1_shp 12)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n12_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n12_i1).
  change 21%nat with ((8 + 13)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 13%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12)))
               (pb4cwin_rem (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) 8%nat pb4cwin_state_n12_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n12_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n12_i2).
  change 13%nat with ((8 + 5)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 5%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12)))
               (pb4cwin_rem (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) 8%nat pb4cwin_state_n12_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n12_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n12_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n12_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n12_i4).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n12.
Lemma pb4cwin_build_poleA_n12 :
  zzId (plq_eqb (planb4_g1_poleA 12) pb4cwin_lit_poleA_n12) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n12).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n12.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n12_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              (planb4_g1_shm 12))
       pb4cwin_stateB_n12_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n12_i1.

Example pb4cwin_remcertB_n12_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              pb4cwin_stateB_n12_i1)
       pb4cwin_stateB_n12_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n12_i2.

Example pb4cwin_remcertB_n12_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              pb4cwin_stateB_n12_i2)
       pb4cwin_stateB_n12_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n12_i3.

Example pb4cwin_remcertB_n12_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 12)
              (hd 0%Q (planb4_g1_denw 12)) 8%nat
              pb4cwin_stateB_n12_i3)
       pb4cwin_stateB_n12_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n12_i4.

(* poleB channel: assemble the chain tail from the 5 block certificates. *)
Lemma pb4cwin_poleBeq_n12 :
  zzId (planb4_g1_poleB 12) pb4cwin_lit_poleB_n12.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 12 + 1)%nat) with ((8 + 29)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 29%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) (planb4_g1_shm 12))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n12_i0).
  change 29%nat with ((8 + 21)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 21%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12)))
               (pb4cwin_rem (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) 8%nat (planb4_g1_shm 12)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n12_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n12_i1).
  change 21%nat with ((8 + 13)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 13%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12)))
               (pb4cwin_rem (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) 8%nat pb4cwin_stateB_n12_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n12_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n12_i2).
  change 13%nat with ((8 + 5)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 5%nat (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12)))
               (pb4cwin_rem (planb4_g1_denw 12) ((hd 0%Q (planb4_g1_denw 12))) 8%nat pb4cwin_stateB_n12_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n12_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n12_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n12_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n12_i4).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n12.
Lemma pb4cwin_build_poleB_n12 :
  zzId (plq_eqb (planb4_g1_poleB 12) pb4cwin_lit_poleB_n12) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n12).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n12.

Lemma pb4cwin_abqAeq_n12 :
  zzId (planb4_abqA 12) (inject_Z pb4cwin_litA_n12).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n12).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n12).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n12.
Lemma pb4cwin_build_abqA_n12 :
  zzId (Qeq_bool (planb4_abqA 12) (inject_Z pb4cwin_litA_n12)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n12).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n12.

Lemma pb4cwin_abqBeq_n12 :
  zzId (planb4_abqB 12) (inject_Z pb4cwin_litB_n12).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n12).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n12).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n12.
Lemma pb4cwin_build_abqB_n12 :
  zzId (Qeq_bool (planb4_abqB 12) (inject_Z pb4cwin_litB_n12)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n12).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n12.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n12 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n12 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n12.
Definition pb4cwin_winA_n12_i0 : Q := (-7661571267270149213077571074065844239857728664633344#105)%Q.
Example pb4cwin_foldsegA_n12_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n12 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n12_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n12_i0.
Definition pb4cwin_winA_n12_i1 : Q := (-3290703385885873084508735467058627544373149527179264#15015)%Q.
Example pb4cwin_foldsegA_n12_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n12 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n12_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n12_i1.
Definition pb4cwin_winA_n12_i2 : Q := (9073522880936057532463249778631601562635603017728#58905)%Q.
Example pb4cwin_foldsegA_n12_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n12 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n12_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n12_i2.
Definition pb4cwin_winA_n12_i3 : Q := (-16194890646393722169357119637731896532815314944#11044215)%Q.
Example pb4cwin_foldsegA_n12_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n12 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n12_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n12_i3.
Definition pb4cwin_winA_n12_i4 : Q := (36080006253538352629914894900133888#1785)%Q.
Example pb4cwin_foldsegA_n12_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n12 ((32 + t)%nat))
                   5%nat))
       pb4cwin_winA_n12_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n12_i4.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n12 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n12 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n12.
Definition pb4cwin_winB_n12_i0 : Q := (-4284075775197589474058147872622063509059964839657472#105)%Q.
Example pb4cwin_foldsegB_n12_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n12 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n12_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n12_i0.
Definition pb4cwin_winB_n12_i1 : Q := (21381101186284359912789945445070498910315556634624#1001)%Q.
Example pb4cwin_foldsegB_n12_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n12 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n12_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n12_i1.
Definition pb4cwin_winB_n12_i2 : Q := (-13541940567383585898640656063066857536546144256#19635)%Q.
Example pb4cwin_foldsegB_n12_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n12 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n12_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n12_i2.
Definition pb4cwin_winB_n12_i3 : Q := (808746928932999138642916535150788854415360#2208843)%Q.
Example pb4cwin_foldsegB_n12_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n12 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n12_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n12_i3.
Definition pb4cwin_winB_n12_i4 : Q := (-5958272426596511456271232139264#19635)%Q.
Example pb4cwin_foldsegB_n12_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n12 ((32 + t)%nat))
                   5%nat))
       pb4cwin_winB_n12_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n12_i4.