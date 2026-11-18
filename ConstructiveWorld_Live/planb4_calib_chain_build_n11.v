(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: assembling certificates at the window point n = 11 *)
(** * planb4_calib_chain_build_n11: poleA/poleB chain tails and the assembled abqA/abqB values for point 11, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n11 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Mission.  poleA/poleB chain tails and the assembled abqA/abqB values for point 11, rewritten level by level from the block certificates: pb4cwin_poleAeq/poleBeq assemble the full pole literal from the step_n11 block certificates through pb4cwin_laur_go_split: the laur wrapper is unfolded and the block split is rewritten in, each block boundary is bridged by a remainder-state certificate (one 8-step pb4cwin_rem bite), the glue lemma rewrites the readout into segments, each segment collapses to its imported literal, and one small bite closes the map/nth readout.  pb4cwin_abqAeq/abqBeq rewrite the two pole arguments of planb4_rs/planb4_ss to their literals and bite only the residual assembly (witness scale, polynomial part, principal fold, Qred).  Boolean plq_eqb / Qeq_bool faces derive from the eq-face certificates.  Fold-window Examples cover the principal sums per window at Qred face, the deep-window insurance face.

    Dependencies.  zzm1_gauss (zzId, mkz, gz_im_neg_frac); zzm2_qpoly (plq_eqb); zzm1b_linform_bridge (zz_sumf); planb4_g1_laur_extract; planb4_g1_rs_channel (planb4_rs, planb4_ss); planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); planb4_calib_chain_glue_laur (pb4cwin_laur_go_split, pb4cwin_rem); planb4_calib_chain_step_n11; stdlib QArith, ZArith, List.

    References.  piu_zz_tau_segtree_1024_merge.v:36-45 (change, glue rewrite, twin rewrite, small bite template); planb4_g1_ab_def.v:60-67 (the assemblies); planb4_g1_rs_channel.v:46-51 (rs/ss faces); planb3_g1_calib.v (the frozen A/B table rows the point literals transcribe).

    Constructivity.  Every assembling lemma is a real rewrite chain over the glue equations; the only bites are the imported per-block certificates, one remainder-state bridge bite per block boundary, plus one residual assembly bite per channel and per fold window; no axioms, no admits; every statement carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_build_n11.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

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
Require Import planb4_calib_chain_step_n11.

Open Scope Q_scope.

(* Chain-tail literals: the full pole lists, and the frozen A/B table rows the assembled values land on. *)
Definition pb4cwin_lit_poleA_n11 : list Q :=
  [(-18219940835328814967331251803768529438268981248#1)%Q; (56836082557295966473523844293434119806359961600#1)%Q; (-168778394579450844984492342967314468430675968000#1)%Q; (476856959669048934037785742888137701583749120000#1)%Q; (-1281047544405246085369041651114847984177643520000#1)%Q; (3269922507095093634376420388602846865732403200000#1)%Q; (-7924159185019137135860761185640262112641024000000#1)%Q; (18214480462636473974012345996082530756853760000000#1)%Q; (-39672051124273919056525772123511007372902400000000#1)%Q; (81782557765904907432831035014957261389824000000000#1)%Q; (-159364244365422598340457644762881631191040000000000#1)%Q; (293127762024341082687042369807599848652800000000000#1)%Q; (-508122791410124491399440310146519007232000000000000#1)%Q; (828618906045703548607448860371221217280000000000000#1)%Q; (-1268680479675213700947244373823507660800000000000000#1)%Q; (1819669505399137109054982533863702528000000000000000#1)%Q; (-2438853746627371437605140211695616000000000000000000#1)%Q; (3045795193033844348256582836944896000000000000000000#1)%Q; (-3532968287819830748874484817592320000000000000000000#1)%Q; (3792342773077013040988571377336320000000000000000000#1)%Q; (-3751207681699230104811633586995200000000000000000000#1)%Q; (3402571614545717103869579755520000000000000000000000#1)%Q; (-2814065936611942227509248000000000000000000000000000#1)%Q; (2107747459576458510998700032000000000000000000000000#1)%Q; (-1418229308090425608689942528000000000000000000000000#1)%Q; (848869776888166365611950080000000000000000000000000#1)%Q; (-446470777835692006309888000000000000000000000000000#1)%Q; (203163824252967190528000000000000000000000000000000#1)%Q; (-78365983728176463872000000000000000000000000000000#1)%Q; (24916184949538894643200000000000000000000000000000#1)%Q; (-6269846310136840192000000000000000000000000000000#1)%Q; (1170847942186106880000000000000000000000000000000#1)%Q; (-144255925564211200000000000000000000000000000000#1)%Q; (8796093022208000000000000000000000000000000000#1)%Q].
Definition pb4cwin_lit_poleB_n11 : list Q :=
  [(-18219940835328814967331251803768529438268981248#1)%Q; (56836082557295966473523844293434119806359961600#1)%Q; (-168778394579450844984492342967314468430675968000#1)%Q; (476856959669048934037785742888137701583749120000#1)%Q; (-1281047544405246085369041651114847984177643520000#1)%Q; (3269922507095093634376420388602846865732403200000#1)%Q; (-7924159185019137135860761185640262112641024000000#1)%Q; (18214480462636473974012345996082530756853760000000#1)%Q; (-39672051124273919056525772123511007372902400000000#1)%Q; (81782557765904907432831035014957261389824000000000#1)%Q; (-159364244365422598340457644762881631191040000000000#1)%Q; (293127762024341082687042369807599848652800000000000#1)%Q; (-508122791410124491399440310146519007232000000000000#1)%Q; (828618906045703548607448860371221217280000000000000#1)%Q; (-1268680479675213700947244373823507660800000000000000#1)%Q; (1819669505399137109054982533863702528000000000000000#1)%Q; (-2438853746627371437605140211695616000000000000000000#1)%Q; (3045795193033844348256582836944896000000000000000000#1)%Q; (-3532968287819830748874484817592320000000000000000000#1)%Q; (3792342773077013040988571377336320000000000000000000#1)%Q; (-3751207681699230104811633586995200000000000000000000#1)%Q; (3402571614545717103869579755520000000000000000000000#1)%Q; (-2814065936611942227509248000000000000000000000000000#1)%Q; (2107747459576458510998700032000000000000000000000000#1)%Q; (-1418229308090425608689942528000000000000000000000000#1)%Q; (848869776888166365611950080000000000000000000000000#1)%Q; (-446470777835692006309888000000000000000000000000000#1)%Q; (203163824252967190528000000000000000000000000000000#1)%Q; (-78365983728176463872000000000000000000000000000000#1)%Q; (24916184949538894643200000000000000000000000000000#1)%Q; (-6269846310136840192000000000000000000000000000000#1)%Q; (1170847942186106880000000000000000000000000000000#1)%Q; (-144255925564211200000000000000000000000000000000#1)%Q; (8796093022208000000000000000000000000000000000#1)%Q].
Definition pb4cwin_litA_n11 : Z := (1776717192655809973715531712942507171769967540923531264)%Z.
Definition pb4cwin_litB_n11 : Z := (-565546647375054955941962293513669761210560446724169600)%Z.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertA_n11_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              (planb4_g1_shp 11))
       pb4cwin_state_n11_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n11_i1.

Example pb4cwin_remcertA_n11_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              pb4cwin_state_n11_i1)
       pb4cwin_state_n11_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n11_i2.

Example pb4cwin_remcertA_n11_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              pb4cwin_state_n11_i2)
       pb4cwin_state_n11_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n11_i3.

Example pb4cwin_remcertA_n11_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              pb4cwin_state_n11_i3)
       pb4cwin_state_n11_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertA_n11_i4.

(* poleA channel: assemble the chain tail from the 5 block certificates. *)
Lemma pb4cwin_poleAeq_n11 :
  zzId (planb4_g1_poleA 11) pb4cwin_lit_poleA_n11.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleA.
  unfold planb4_g1_laur.
  change ((3 * 11 + 1)%nat) with ((8 + 26)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 26%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) (planb4_g1_shp 11))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n11_i0).
  change 26%nat with ((8 + 18)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 18%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11)))
               (pb4cwin_rem (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) 8%nat (planb4_g1_shp 11)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n11_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n11_i1).
  change 18%nat with ((8 + 10)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 10%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11)))
               (pb4cwin_rem (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) 8%nat pb4cwin_state_n11_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n11_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n11_i2).
  change (planb4_g1_laur_go (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) 10%nat
             (pb4cwin_rem (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) 8%nat
                pb4cwin_state_n11_i2))
    with (planb4_g1_laur_go (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) (8 + 2)%nat
             (pb4cwin_rem (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) 8%nat
                pb4cwin_state_n11_i2)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 2%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11)))
               (pb4cwin_rem (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) 8%nat pb4cwin_state_n11_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n11_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n11_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertA_n11_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segA_n11_i4).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleAeq_n11.
Lemma pb4cwin_build_poleA_n11 :
  zzId (plq_eqb (planb4_g1_poleA 11) pb4cwin_lit_poleA_n11) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n11).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleA_n11.

(* Remainder-state certificates: each bridges one block boundary
   with a single 8-step pb4cwin_rem bite against the next block
   state literal, so no assembly step forces a kernel conversion
   over the chain terms. *)
Example pb4cwin_remcertB_n11_i1 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              (planb4_g1_shm 11))
       pb4cwin_stateB_n11_i1.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n11_i1.

Example pb4cwin_remcertB_n11_i2 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              pb4cwin_stateB_n11_i1)
       pb4cwin_stateB_n11_i2.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n11_i2.

Example pb4cwin_remcertB_n11_i3 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              pb4cwin_stateB_n11_i2)
       pb4cwin_stateB_n11_i3.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n11_i3.

Example pb4cwin_remcertB_n11_i4 :
  zzId (pb4cwin_rem (planb4_g1_denw 11)
              (hd 0%Q (planb4_g1_denw 11)) 8%nat
              pb4cwin_stateB_n11_i3)
       pb4cwin_stateB_n11_i4.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_remcertB_n11_i4.

(* poleB channel: assemble the chain tail from the 5 block certificates. *)
Lemma pb4cwin_poleBeq_n11 :
  zzId (planb4_g1_poleB 11) pb4cwin_lit_poleB_n11.
Proof.
  apply zzId_from_eq.
  unfold planb4_g1_poleB.
  unfold planb4_g1_laur.
  change ((3 * 11 + 1)%nat) with ((8 + 26)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 26%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) (planb4_g1_shm 11))).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n11_i0).
  change 26%nat with ((8 + 18)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 18%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11)))
               (pb4cwin_rem (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) 8%nat (planb4_g1_shm 11)))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n11_i1).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n11_i1).
  change 18%nat with ((8 + 10)%nat).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 10%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11)))
               (pb4cwin_rem (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) 8%nat pb4cwin_stateB_n11_i1))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n11_i2).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n11_i2).
  change (planb4_g1_laur_go (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) 10%nat
             (pb4cwin_rem (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) 8%nat
                pb4cwin_stateB_n11_i2))
    with (planb4_g1_laur_go (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) (8 + 2)%nat
             (pb4cwin_rem (planb4_g1_denw 11) (hd 0%Q (planb4_g1_denw 11)) 8%nat
                pb4cwin_stateB_n11_i2)).
  rewrite (pb4cwin_zzId_eq (pb4cwin_laur_go_split 8%nat 2%nat (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11)))
               (pb4cwin_rem (planb4_g1_denw 11) ((hd 0%Q (planb4_g1_denw 11))) 8%nat pb4cwin_stateB_n11_i2))).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n11_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n11_i3).
  rewrite (pb4cwin_zzId_eq pb4cwin_remcertB_n11_i4).
  rewrite (pb4cwin_zzId_eq pb4cwin_segB_n11_i4).
  vm_compute. reflexivity.

Qed.
Print Assumptions pb4cwin_poleBeq_n11.
Lemma pb4cwin_build_poleB_n11 :
  zzId (plq_eqb (planb4_g1_poleB 11) pb4cwin_lit_poleB_n11) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n11).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_poleB_n11.

Lemma pb4cwin_abqAeq_n11 :
  zzId (planb4_abqA 11) (inject_Z pb4cwin_litA_n11).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqA.
  unfold planb4_rs.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n11).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n11).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqAeq_n11.
Lemma pb4cwin_build_abqA_n11 :
  zzId (Qeq_bool (planb4_abqA 11) (inject_Z pb4cwin_litA_n11)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n11).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqA_n11.

Lemma pb4cwin_abqBeq_n11 :
  zzId (planb4_abqB 11) (inject_Z pb4cwin_litB_n11).
Proof.
  apply zzId_from_eq.
  unfold planb4_abqB.
  unfold planb4_ss.
  rewrite (pb4cwin_zzId_eq pb4cwin_poleAeq_n11).
  rewrite (pb4cwin_zzId_eq pb4cwin_poleBeq_n11).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_abqBeq_n11.
Lemma pb4cwin_build_abqB_n11 :
  zzId (Qeq_bool (planb4_abqB 11) (inject_Z pb4cwin_litB_n11)) true.
Proof.
  apply zzId_from_eq.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n11).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_build_abqB_n11.

(* A channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fA_n11 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleA_n11 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 4 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 4 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fA_n11.
Definition pb4cwin_winA_n11_i0 : Q := (52355467531901934815766141174784769424030171136#15)%Q.
Example pb4cwin_foldsegA_n11_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n11 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winA_n11_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n11_i0.
Definition pb4cwin_winA_n11_i1 : Q := (4646635803402624534071124550848323849679798272#495)%Q.
Example pb4cwin_foldsegA_n11_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n11 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winA_n11_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n11_i1.
Definition pb4cwin_winA_n11_i2 : Q := (-46962707584680095193631069728526035115311104#11385)%Q.
Example pb4cwin_foldsegA_n11_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n11 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winA_n11_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n11_i2.
Definition pb4cwin_winA_n11_i3 : Q := (101512905270660034311877500132840190246912#7888725)%Q.
Example pb4cwin_foldsegA_n11_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n11 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winA_n11_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n11_i3.
Definition pb4cwin_winA_n11_i4 : Q := (-15681006221127733093597184#3)%Q.
Example pb4cwin_foldsegA_n11_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fA_n11 ((32 + t)%nat))
                   2%nat))
       pb4cwin_winA_n11_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegA_n11_i4.

(* B channel principal part: per-window Qred certificates over the pole literal (deep-window insurance face). *)
Definition pb4cwin_fB_n11 : nat -> Q :=
  fun jj => match jj with
           | O => 0%Q
           | S j => (nth (S j) pb4cwin_lit_poleB_n11 0%Q
                     * (((Z.opp (fst (gz_im_neg_frac (mkz 6 2) (S j)))) # 1)
                        / ((snd (gz_im_neg_frac (mkz 6 2) (S j))) # 1))%Q
                     / (Z.of_nat (S j) # 1)%Q)%Q
           end.
Print Assumptions pb4cwin_fB_n11.
Definition pb4cwin_winB_n11_i0 : Q := (29259939407992263570441637964335841762898608128#15)%Q.
Example pb4cwin_foldsegB_n11_i0 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n11 ((0 + t)%nat))
                   8%nat))
       pb4cwin_winB_n11_i0) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n11_i0.
Definition pb4cwin_winB_n11_i1 : Q := (-447391563797117274502127812726914598194642944#495)%Q.
Example pb4cwin_foldsegB_n11_i1 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n11 ((8 + t)%nat))
                   8%nat))
       pb4cwin_winB_n11_i1) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n11_i1.
Definition pb4cwin_winB_n11_i2 : Q := (69360944152558542856671943208755420725248#3795)%Q.
Example pb4cwin_foldsegB_n11_i2 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n11 ((16 + t)%nat))
                   8%nat))
       pb4cwin_winB_n11_i2) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n11_i2.
Definition pb4cwin_winB_n11_i3 : Q := (-25232017175155496264324759780866392064#7888725)%Q.
Example pb4cwin_foldsegB_n11_i3 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n11 ((24 + t)%nat))
                   8%nat))
       pb4cwin_winB_n11_i3) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n11_i3.
Definition pb4cwin_winB_n11_i4 : Q := (2620059790916731273216#33)%Q.
Example pb4cwin_foldsegB_n11_i4 :
  zzId (Qeq_bool (Qred (zz_sumf
                   (fun t => pb4cwin_fB_n11 ((32 + t)%nat))
                   2%nat))
       pb4cwin_winB_n11_i4) true.
Proof. apply zzId_from_eq. vm_compute. reflexivity. Qed.
Print Assumptions pb4cwin_foldsegB_n11_i4.