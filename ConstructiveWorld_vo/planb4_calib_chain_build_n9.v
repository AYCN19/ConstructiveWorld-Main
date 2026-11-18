(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 9 *)
(** * planb4_calib_chain_build_n9: poleA/poleB chain tails and the assembled abqA/abqB values for point 9, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n9 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 9, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n9 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n9; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n9.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n9.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n9 : list Q :=
  [(-42168444724147139007577695871389663232#1)%Q; (131304295024613577063820791475213434880#1)%Q; (-384966506241111834107879268692472627200#1)%Q; (1061825607911792278634692767517769728000#1)%Q; (-2752559400089564881773525602863677440000#1)%Q; (6698357318613390824047216273496473600000#1)%Q; (-15281422796758849480940248056725504000000#1)%Q; (32632574131574540027483515110031360000000#1)%Q; (-65112018082663746478912883916800000000000#1)%Q; (121147020330271473832234540072960000000000#1)%Q; (-209700298371903046036191654707200000000000#1)%Q; (336796043894573743636724527923200000000000#1)%Q; (-500371789989507336572552347648000000000000#1)%Q; (685253351167208454110283038720000000000000#1)%Q; (-861539431002833513465302220800000000000000#1)%Q; (989702361508809957856772096000000000000000#1)%Q; (-1033040646021621630537564160000000000000000#1)%Q; (973277858968450160289382400000000000000000#1)%Q; (-821113624301998509654016000000000000000000#1)%Q; (614315361260321059635200000000000000000000#1)%Q; (-402662358438409299558400000000000000000000#1)%Q; (227689648853998370816000000000000000000000#1)%Q; (-108835264303401533440000000000000000000000#1)%Q; (42766928114509414400000000000000000000000#1)%Q; (-13266260624146432000000000000000000000000#1)%Q; (3046334403706880000000000000000000000000#1)%Q; (-460420494131200000000000000000000000000#1)%Q; (34359738368000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n9 : list Q :=
  [(-42168444724147139007577695871389663232#1)%Q; (131304295024613577063820791475213434880#1)%Q; (-384966506241111834107879268692472627200#1)%Q; (1061825607911792278634692767517769728000#1)%Q; (-2752559400089564881773525602863677440000#1)%Q; (6698357318613390824047216273496473600000#1)%Q; (-15281422796758849480940248056725504000000#1)%Q; (32632574131574540027483515110031360000000#1)%Q; (-65112018082663746478912883916800000000000#1)%Q; (121147020330271473832234540072960000000000#1)%Q; (-209700298371903046036191654707200000000000#1)%Q; (336796043894573743636724527923200000000000#1)%Q; (-500371789989507336572552347648000000000000#1)%Q; (685253351167208454110283038720000000000000#1)%Q; (-861539431002833513465302220800000000000000#1)%Q; (989702361508809957856772096000000000000000#1)%Q; (-1033040646021621630537564160000000000000000#1)%Q; (973277858968450160289382400000000000000000#1)%Q; (-821113624301998509654016000000000000000000#1)%Q; (614315361260321059635200000000000000000000#1)%Q; (-402662358438409299558400000000000000000000#1)%Q; (227689648853998370816000000000000000000000#1)%Q; (-108835264303401533440000000000000000000000#1)%Q; (42766928114509414400000000000000000000000#1)%Q; (-13266260624146432000000000000000000000000#1)%Q; (3046334403706880000000000000000000000000#1)%Q; (-460420494131200000000000000000000000000#1)%Q; (34359738368000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n9 : Z := (268291249986503741300139391472573324642484224)%Z.
Definition pb4cwin_litB_n9 : Z := (-85399757247310936434547446993881556250886400)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n9_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 9)
              (hd 0%Q (planb4_g1_denw 9)) 8%nat
              (planb4_g1_shp 9))
       pb4cwin_state_n9_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n9_i1.

Example pb4cwin_remcertA_n9_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 9)
              (hd 0%Q (planb4_g1_denw 9)) 8%nat
              pb4cwin_state_n9_i1)
       pb4cwin_state_n9_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n9_i2.

Example pb4cwin_remcertA_n9_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 9)
              (hd 0%Q (planb4_g1_denw 9)) 8%nat
              pb4cwin_state_n9_i2)
       pb4cwin_state_n9_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n9_i3.

(* poleA channel: assemble the chain tail from the 4 block certificates. *)
Lemma pb4cwin_poleAeq_n9 :
  zzId (planb4_g1_poleA 9) pb4cwin_lit_poleA_n9.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 9 + 1)%nat) with ((8 + 20)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 20%nat (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9))) (planb4_g1_shp 9))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n9_i0).
  change 20%nat with ((8 + 12)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 12%nat (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9)))
               (pb4cwin_rem (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9))) 8%nat (planb4_g1_shp 9)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n9_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n9_i1).
  change 12%nat with ((8 + 4)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 4%nat (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9)))
               (pb4cwin_rem (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9))) 8%nat pb4cwin_state_n9_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n9_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n9_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n9_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n9_i3).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n9.
Lemma pb4cwin_build_poleA_n9 :
  zzId (plq_eqb (planb4_g1_poleA 9) pb4cwin_lit_poleA_n9) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n9).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n9.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n9_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 9)
              (hd 0%Q (planb4_g1_denw 9)) 8%nat
              (planb4_g1_shm 9))
       pb4cwin_stateB_n9_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n9_i1.

Example pb4cwin_remcertB_n9_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 9)
              (hd 0%Q (planb4_g1_denw 9)) 8%nat
              pb4cwin_stateB_n9_i1)
       pb4cwin_stateB_n9_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n9_i2.

Example pb4cwin_remcertB_n9_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 9)
              (hd 0%Q (planb4_g1_denw 9)) 8%nat
              pb4cwin_stateB_n9_i2)
       pb4cwin_stateB_n9_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n9_i3.

(* poleB channel: assemble the chain tail from the 4 block certificates. *)
Lemma pb4cwin_poleBeq_n9 :
  zzId (planb4_g1_poleB 9) pb4cwin_lit_poleB_n9.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 9 + 1)%nat) with ((8 + 20)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 20%nat (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9))) (planb4_g1_shm 9))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n9_i0).
  change 20%nat with ((8 + 12)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 12%nat (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9)))
               (pb4cwin_rem (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9))) 8%nat (planb4_g1_shm 9)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n9_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n9_i1).
  change 12%nat with ((8 + 4)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 4%nat (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9)))
               (pb4cwin_rem (planb4_g1_denw 9) ((hd 0%Q (planb4_g1_denw 9))) 8%nat pb4cwin_stateB_n9_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n9_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n9_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n9_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n9_i3).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n9.
Lemma pb4cwin_build_poleB_n9 :
  zzId (plq_eqb (planb4_g1_poleB 9) pb4cwin_lit_poleB_n9) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n9).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n9.

Lemma pb4cwin_abqAeq_n9 :
  zzId (planb4_abqA 9) (inject_Z pb4cwin_litA_n9).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n9).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n9).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n9.
Lemma pb4cwin_build_abqA_n9 :
  zzId (Qeq_bool (planb4_abqA 9) (inject_Z pb4cwin_litA_n9)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n9).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n9.

Lemma pb4cwin_abqBeq_n9 :
  zzId (planb4_abqB 9) (inject_Z pb4cwin_litB_n9).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n9).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n9).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n9.
Lemma pb4cwin_build_abqB_n9 :
  zzId (Qeq_bool (planb4_abqB 9) (inject_Z pb4cwin_litB_n9)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n9).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n9.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n9 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n9 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n9.
Definition pb4cwin_winA_n9_i0 : Q := (283381231825846211889907818984439283712#35)%Q.
Example pb4cwin_foldsegA_n9_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n9 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n9_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n9_i0.
Definition pb4cwin_winA_n9_i1 : Q := (727077774154153602987079648045787250688#45045)%Q.
Example pb4cwin_foldsegA_n9_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n9 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n9_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n9_i1.
Definition pb4cwin_winA_n9_i2 : Q := (-21146511277909637234762105768378368#11385)%Q.
Example pb4cwin_foldsegA_n9_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n9 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n9_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n9_i2.
Definition pb4cwin_winA_n9_i3 : Q := (1126507534808984675845931008#8775)%Q.
Example pb4cwin_foldsegA_n9_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n9 ((24 + t)%nat))
                   4%nat))
       pb4cwin_winA_n9_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n9_i3.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n9 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n9 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n9.
Definition pb4cwin_winB_n9_i0 : Q := (474535113179554865944373285138997444608#105)%Q.
Example pb4cwin_foldsegB_n9_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n9 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n9_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n9_i0.
Definition pb4cwin_winB_n9_i1 : Q := (-67764767272146151100598314521354829824#45045)%Q.
Example pb4cwin_foldsegB_n9_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n9 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n9_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n9_i1.
Definition pb4cwin_winB_n9_i2 : Q := (30385452973679959013403693940736#3795)%Q.
Example pb4cwin_foldsegB_n9_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n9 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n9_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n9_i2.
Definition pb4cwin_winB_n9_i3 : Q := (-276901048283056052371456#8775)%Q.
Example pb4cwin_foldsegB_n9_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n9 ((24 + t)%nat))
                   4%nat))
       pb4cwin_winB_n9_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n9_i3.