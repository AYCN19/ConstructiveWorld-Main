(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 13 *)
(** * planb4_calib_chain_build_n13: poleA/poleB chain tails and the assembled abqA/abqB values for point 13, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n13 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 13, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n13 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n13; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n13.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n13.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n13 : list Q :=
  [(-8004891153242289126670353531589624493780403705662668800#1)%Q; (25002094730232644503771911794700594749283037954588016640#1)%Q; (-74904462881242183685426949238888664470688227586054553600#1)%Q; (215170993954055401611653342432723724907524201564340224000#1)%Q; (-592403388896533132809464067618841655134299955040092160000#1)%Q; (1562426790824631632813133403927768881102449541120000000000#1)%Q; (-3945453445473252767720129666272987790315889893572608000000#1)%Q; (9533464255225734352633996051087648894280685815070720000000#1)%Q; (-22028025318902399932550792924255641479676605287628800000000#1)%Q; (48635881101207689351935695188689168234143046172672000000000#1)%Q; (-102529408513222158491282301090870742069821833216000000000000#1)%Q; (206191426737295183781947630234342919643951687270400000000000#1)%Q; (-395190251639043445040860635243207447661433061376000000000000#1)%Q; (721103626205059755661555605748615555039090442240000000000000#1)%Q; (-1251245761252011279669955203902906472007834009600000000000000#1)%Q; (2062002442526760321115203993386405236572160000000000000000000#1)%Q; (-3222777809266108045434709343104540957527244800000000000000000#1)%Q; (4769770692634314247726819029344130225405952000000000000000000#1)%Q; (-6673480688503272902007121684353686312058880000000000000000000#1)%Q; (8810045608632181468420636362283251086131200000000000000000000#1)%Q; (-10951357659376742251301449096798939381760000000000000000000000#1)%Q; (12788269566864348538344056949753868451840000000000000000000000#1)%Q; (-13992005849661209595984150659191118233600000000000000000000000#1)%Q; (14302212389165517231729863425150418944000000000000000000000000#1)%Q; (-13612801148683917238852917931655823360000000000000000000000000#1)%Q; (12019395252405190238717036940230656000000000000000000000000000#1)%Q; (-9802615982025829050069611923583795200000000000000000000000000#1)%Q; (7348022350063187517189653369192448000000000000000000000000000#1)%Q; (-5033329954391060039642313465528320000000000000000000000000000#1)%Q; (3129202166639409537427836816588800000000000000000000000000000#1)%Q; (-1751309396194613688414712627200000000000000000000000000000000#1)%Q; (873652788305033269001783869440000000000000000000000000000000#1)%Q; (-383729999548368833887181209600000000000000000000000000000000#1)%Q; (146097251141061138641321984000000000000000000000000000000000#1)%Q; (-47237795480513276763176960000000000000000000000000000000000#1)%Q; (12612163278839931207680000000000000000000000000000000000000#1)%Q; (-2669731607305416343552000000000000000000000000000000000000#1)%Q; (420095773241119866880000000000000000000000000000000000000#1)%Q; (-43684916385493811200000000000000000000000000000000000000#1)%Q; (2251799813685248000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n13 : list Q :=
  [(-8004891153242289126670353531589624493780403705662668800#1)%Q; (25002094730232644503771911794700594749283037954588016640#1)%Q; (-74904462881242183685426949238888664470688227586054553600#1)%Q; (215170993954055401611653342432723724907524201564340224000#1)%Q; (-592403388896533132809464067618841655134299955040092160000#1)%Q; (1562426790824631632813133403927768881102449541120000000000#1)%Q; (-3945453445473252767720129666272987790315889893572608000000#1)%Q; (9533464255225734352633996051087648894280685815070720000000#1)%Q; (-22028025318902399932550792924255641479676605287628800000000#1)%Q; (48635881101207689351935695188689168234143046172672000000000#1)%Q; (-102529408513222158491282301090870742069821833216000000000000#1)%Q; (206191426737295183781947630234342919643951687270400000000000#1)%Q; (-395190251639043445040860635243207447661433061376000000000000#1)%Q; (721103626205059755661555605748615555039090442240000000000000#1)%Q; (-1251245761252011279669955203902906472007834009600000000000000#1)%Q; (2062002442526760321115203993386405236572160000000000000000000#1)%Q; (-3222777809266108045434709343104540957527244800000000000000000#1)%Q; (4769770692634314247726819029344130225405952000000000000000000#1)%Q; (-6673480688503272902007121684353686312058880000000000000000000#1)%Q; (8810045608632181468420636362283251086131200000000000000000000#1)%Q; (-10951357659376742251301449096798939381760000000000000000000000#1)%Q; (12788269566864348538344056949753868451840000000000000000000000#1)%Q; (-13992005849661209595984150659191118233600000000000000000000000#1)%Q; (14302212389165517231729863425150418944000000000000000000000000#1)%Q; (-13612801148683917238852917931655823360000000000000000000000000#1)%Q; (12019395252405190238717036940230656000000000000000000000000000#1)%Q; (-9802615982025829050069611923583795200000000000000000000000000#1)%Q; (7348022350063187517189653369192448000000000000000000000000000#1)%Q; (-5033329954391060039642313465528320000000000000000000000000000#1)%Q; (3129202166639409537427836816588800000000000000000000000000000#1)%Q; (-1751309396194613688414712627200000000000000000000000000000000#1)%Q; (873652788305033269001783869440000000000000000000000000000000#1)%Q; (-383729999548368833887181209600000000000000000000000000000000#1)%Q; (146097251141061138641321984000000000000000000000000000000000#1)%Q; (-47237795480513276763176960000000000000000000000000000000000#1)%Q; (12612163278839931207680000000000000000000000000000000000000#1)%Q; (-2669731607305416343552000000000000000000000000000000000000#1)%Q; (420095773241119866880000000000000000000000000000000000000#1)%Q; (-43684916385493811200000000000000000000000000000000000000#1)%Q; (2251799813685248000000000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n13 : Z := (788942622564733438898330472232680201581170162461319466868486963200)%Z.
Definition pb4cwin_litB_n13 : Z := (-251128236394121622962055360758345650449968128068472562631791040000)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n13_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              (planb4_g1_shp 13))
       pb4cwin_state_n13_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n13_i1.

Example pb4cwin_remcertA_n13_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              pb4cwin_state_n13_i1)
       pb4cwin_state_n13_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n13_i2.

Example pb4cwin_remcertA_n13_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              pb4cwin_state_n13_i2)
       pb4cwin_state_n13_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n13_i3.

Example pb4cwin_remcertA_n13_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              pb4cwin_state_n13_i3)
       pb4cwin_state_n13_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n13_i4.

(* poleA channel: assemble the chain tail from the 5 block certificates. *)
Lemma pb4cwin_poleAeq_n13 :
  zzId (planb4_g1_poleA 13) pb4cwin_lit_poleA_n13.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 13 + 1)%nat) with ((8 + 32)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 32%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) (planb4_g1_shp 13))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n13_i0).
  change 32%nat with ((8 + 24)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 24%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13)))
               (pb4cwin_rem (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) 8%nat (planb4_g1_shp 13)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n13_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n13_i1).
  change 24%nat with ((8 + 16)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 16%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13)))
               (pb4cwin_rem (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) 8%nat pb4cwin_state_n13_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n13_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n13_i2).
  change 16%nat with ((8 + 8)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 8%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13)))
               (pb4cwin_rem (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) 8%nat pb4cwin_state_n13_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n13_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n13_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n13_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n13_i4).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n13.
Lemma pb4cwin_build_poleA_n13 :
  zzId (plq_eqb (planb4_g1_poleA 13) pb4cwin_lit_poleA_n13) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n13).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n13.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n13_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              (planb4_g1_shm 13))
       pb4cwin_stateB_n13_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n13_i1.

Example pb4cwin_remcertB_n13_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              pb4cwin_stateB_n13_i1)
       pb4cwin_stateB_n13_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n13_i2.

Example pb4cwin_remcertB_n13_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              pb4cwin_stateB_n13_i2)
       pb4cwin_stateB_n13_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n13_i3.

Example pb4cwin_remcertB_n13_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 13)
              (hd 0%Q (planb4_g1_denw 13)) 8%nat
              pb4cwin_stateB_n13_i3)
       pb4cwin_stateB_n13_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n13_i4.

(* poleB channel: assemble the chain tail from the 5 block certificates. *)
Lemma pb4cwin_poleBeq_n13 :
  zzId (planb4_g1_poleB 13) pb4cwin_lit_poleB_n13.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 13 + 1)%nat) with ((8 + 32)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 32%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) (planb4_g1_shm 13))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n13_i0).
  change 32%nat with ((8 + 24)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 24%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13)))
               (pb4cwin_rem (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) 8%nat (planb4_g1_shm 13)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n13_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n13_i1).
  change 24%nat with ((8 + 16)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 16%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13)))
               (pb4cwin_rem (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) 8%nat pb4cwin_stateB_n13_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n13_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n13_i2).
  change 16%nat with ((8 + 8)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 8%nat (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13)))
               (pb4cwin_rem (planb4_g1_denw 13) ((hd 0%Q (planb4_g1_denw 13))) 8%nat pb4cwin_stateB_n13_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n13_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n13_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n13_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n13_i4).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n13.
Lemma pb4cwin_build_poleB_n13 :
  zzId (plq_eqb (planb4_g1_poleB 13) pb4cwin_lit_poleB_n13) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n13).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n13.

Lemma pb4cwin_abqAeq_n13 :
  zzId (planb4_abqA 13) (inject_Z pb4cwin_litA_n13).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n13).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n13).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n13.
Lemma pb4cwin_build_abqA_n13 :
  zzId (Qeq_bool (planb4_abqA 13) (inject_Z pb4cwin_litA_n13)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n13).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n13.

Lemma pb4cwin_abqBeq_n13 :
  zzId (planb4_abqB 13) (inject_Z pb4cwin_litB_n13).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n13).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n13).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n13.
Lemma pb4cwin_build_abqB_n13 :
  zzId (Qeq_bool (planb4_abqB 13) (inject_Z pb4cwin_litB_n13)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n13).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n13.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n13 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n13 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n13.
Definition pb4cwin_winA_n13_i0 : Q := (10716122107303151872449052063724482402387345768349433856#7)%Q.
Example pb4cwin_foldsegA_n13_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n13 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n13_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n13_i0.
Definition pb4cwin_winA_n13_i1 : Q := (4132009114886373987003970043657757170542955462773440512#819)%Q.
Example pb4cwin_foldsegA_n13_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n13 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n13_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n13_i1.
Definition pb4cwin_winA_n13_i2 : Q := (-106132250633904211677954639712725694611370338219458560#20349)%Q.
Example pb4cwin_foldsegA_n13_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n13 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n13_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n13_i2.
Definition pb4cwin_winA_n13_i3 : Q := (86681318922381529910083907112238144900887247585280#736281)%Q.
Example pb4cwin_foldsegA_n13_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n13 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n13_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n13_i3.
Definition pb4cwin_winA_n13_i4 : Q := (-14571055471612912310761898168239064075993088#1087541)%Q.
Example pb4cwin_foldsegA_n13_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n13 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winA_n13_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n13_i4.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n13 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n13 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n13.
Definition pb4cwin_winB_n13_i0 : Q := (5994917205750936931283328996137180073485024755233849344#7)%Q.
Example pb4cwin_foldsegB_n13_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n13 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n13_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n13_i0.
Definition pb4cwin_winB_n13_i1 : Q := (-406854657646969818399182634258580694818715288150736896#819)%Q.
Example pb4cwin_foldsegB_n13_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n13 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n13_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n13_i1.
Definition pb4cwin_winB_n13_i2 : Q := (159817209542313169620280087318509114384634924236800#6783)%Q.
Example pb4cwin_foldsegB_n13_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n13 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n13_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n13_i2.
Definition pb4cwin_winB_n13_i3 : Q := (-21730281449303324505521495731393289821311991808#736281)%Q.
Example pb4cwin_foldsegB_n13_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n13 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n13_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n13_i3.
Definition pb4cwin_winB_n13_i4 : Q := (50006348920418472106638284648704114688#250971)%Q.
Example pb4cwin_foldsegB_n13_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n13 ((32 + t)%nat))
                   8%nat))
       pb4cwin_winB_n13_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n13_i4.