(* ConstructiveWorld-Main - planB wave-2 G1 closing register: dual-route *)
(* carrier alignment bites (A_j, t_n) and the legacy aq/bq disposal.    *)

(** * planb4_u5_carrier_align: the G1 dual-route closing register.

    Mission.  (1) A_j carrier dual-route alignment: the Laurent pole
      readout [nth j (planb4_g1_poleA n) 0] (laur_extract:101) vs the
      Gaussian pair series [piu_zz_Aj n j] (kernel_sum:632), eleven
      Qeq_bool bites n = 1..2, j = 0..3n, all machine true; n = 2 is
      the deepest certified multi-sum depth.  (2) t_n dual-route bites
      [Qeq_bool (planb4_tn n) (zz_phat (planb4_g1_pq n))] n = 1..3:
      all machine false; the zzm2 pdivmod route is the authoritative
      polynomial part, the witness planb4_pdiv face is registered for
      retirement.  (3) The legacy witness aq/bq faces are superseded
      by planb4_g1_ab_def; the SCALE-NORMALIZATION note is disposed by
      the machine anchors -2392/8000 (piu_zz_Aj already in the reduced
      A_j scale).  Details in the section registers below.
    Dependencies.  planb4_g1_laur_extract (poleA/pq);
      piu_zz_kernel_sum (piu_zz_Aj); zzm1b_linform_bridge (zz_phat);
      planb4_g1_witness (planb4_tn; legacy faces); stdlib QArith,
      ZArith, List.
    References.  ZZ2020 Lemma 3 and Prop 1; planb4_g1_ab_def (A/B
      assembly, exponent -floor(5n/2)+2 pinned by the frozen tables);
      piu_zz_n1_linform:349/:404 (multi-sum term-count bound); the
      path-A survey receipt (out-of-memory registration n = 9/16).
    Constructivity.  Bool-valued Qeq_bool bites over transparent Q
      faces; each anchor one vm_compute step; admission-free,
      postulate-free; no Prop-carried statement face.
    Build.  coqc -native-compiler no -q -Q . "" planb4_u5_carrier_align.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Require Import planb4_g1_laur_extract.
Require Import piu_zz_kernel_sum.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_witness.

(* ================================================================== *)
(* Section 1. Route law and the A_j dual-route carrier bites.          *)
(* ================================================================== *)

(* Route law.  Both faces read the coefficient family A_{n,j} of one
   rational function N/D by disjoint routes:
   - planb4_g1_poleA n (planb4_g1_laur_extract:101) reads
     A_{n,j} = [w^(3n-j)](N(5-w)/(10-w)^(3n+1)) off the Laurent series
     of the zzm2 chain (pdivmod -> pshift -> Laurent); that route is
     table-certified at n = 1..6 (zz3_poleA_1..6, laur_extract
     :144-:189) and feeds the certified r/s assembly
     (planb4_g1_rs_assembly:59-:68, zz_linform_r/s over pq/poleA/poleB).
   - piu_zz_Aj n j = gz_Re (piu_zz_Mj_gz n j) (piu_zz_kernel_sum:632)
     sums the Gaussian pair series zz_Mj over the six-index term face;
     it feeds the witness S_n assembly (planb4_g1_witness:99-:108) and
     carries the in-tree certified samples A_{1,1} = 6880,
     A_{1,2} = -11200, A_{2,0} = 37324672 (piu_zz_n1_linform:410-:416).
   The eleven bites weld the two routes to one coefficient family over
   the whole computable window n <= 2: n = 1 (j = 0..3) and n = 2
   (j = 0..6), the latter being the deepest certified multi-sum depth
   in the tree.  The multi-sum route is the depth bottleneck: the term
   list zz_Mj 8 0 already spans 114795 entries (piu_zz_n1_linform:404,
   zz_len_sample_8_0; the count exceeds the n >= 9 working budget, and
   the path-A survey receipt registers out-of-memory at n = 9/16; the
   sigma_decay coordinates of the run order live outside this tree),
   so no multi-sum bite at n >= 3 is claimed here.  Machine-printed
   bite values (vm_compute; the series side prints unreduced Q, e.g.
   piu_zz_Aj 1 3 = 16000 # 2 = 8000):
   poleA 1 = [-2392; 6880; -11200; 8000];  poleA 2 =
   [37324672; -112234880; 256441600; -431872000; 506880000;
   -371200000; 128000000]. *)

Example planb4_u5_aj_1_0 :
  Qeq_bool (nth 0%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 0%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_1_1 :
  Qeq_bool (nth 1%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 1%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_1_2 :
  Qeq_bool (nth 2%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 2%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_1_3 :
  Qeq_bool (nth 3%nat (planb4_g1_poleA 1%nat) 0%Q) (piu_zz_Aj 1%nat 3%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_0 :
  Qeq_bool (nth 0%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 0%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_1 :
  Qeq_bool (nth 1%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 1%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_2 :
  Qeq_bool (nth 2%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 2%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_3 :
  Qeq_bool (nth 3%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 3%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_4 :
  Qeq_bool (nth 4%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 4%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_5 :
  Qeq_bool (nth 5%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 5%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_aj_2_6 :
  Qeq_bool (nth 6%nat (planb4_g1_poleA 2%nat) 0%Q) (piu_zz_Aj 2%nat 6%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 2. The t_n dual-route bites: machine refutation register.   *)
(* ================================================================== *)

(* The witness t_n face (planb4_g1_witness:336-:337, built on its own
   planb4_pdiv long division, witness:287-:315) against the zzm2
   certified route zz_phat (planb4_g1_pq n) (planb4_g1_pq :=
   fst (pdivmod ..), laur_extract:93-:94; zz_phat = the polynomial-part
   integral readout, zzm1b_linform_bridge:51-:53).  All three bites
   come out machine false, so the = true anchor form is kernel-refuted
   and is registered below in its machine-true refuted form (= false);
   per the run order, the zzm2 route is the authoritative polynomial
   part and the witness independent planb4_pdiv face is registered for
   retirement.

   Root cause (machine-printed).  planb4_shift (witness:279-:280)
   builds the shifted subtractend as repeat c k ++ map (fun x => c * x) b,
   echoing the quotient coeff c in the k low padding slots where the
   long division needs zeros; the low coefficients are corrupted and
   the leading slot cancels (5 - 5 = 0 at n = 1), so every later step
   reads c = 0 until the fuel burns out.  The quotients collapse to
   the leading coeff alone: planb4_P 1 = [5; 0; ..; 0] (11 entries)
   vs the authoritative planb4_g1_pq 1 = [560; 0; 5]; likewise
   [-5; 0; ..; 0] (21) and [5; 0; ..; 0] (31) at n = 2, 3.  Hence
   planb4_tn 1..3 = 40, -40, 40 exactly (each = 2 * leading *
   Re(int_0) = 8 * leading, with leading = 5*(-1)^(3n+1)), while the
   authoritative side reads zz_phat (planb4_g1_pq n) = 6700 # 6
   (= 3350/3), -89832405120 # 5040 (= -374301688/21),
   12829747424385024000 # 39916800 at n = 1..3 (vm_compute, exact).
   The authoritative pq face is table-certified upstream (zz3_pq_1..3,
   laur_extract:148/:157/:166) and zz_phat is exercised by the
   certified born-window chain zz_r_1..6 (zzm1b_linform_bridge
   :143-:224).  This register also explains the honest kernel-refuted
   item on the witness a-composite (witness:378-:383, composite 3602
   vs frozen A(1) = 22544): the same collapsed quotient feeds
   planb4_a_cleared (witness:350-:352). *)

Example planb4_u5_tn_dual_red_1 :
  Qeq_bool (planb4_tn 1%nat) (zz_phat (planb4_g1_pq 1%nat)) = false.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_tn_dual_red_2 :
  Qeq_bool (planb4_tn 2%nat) (zz_phat (planb4_g1_pq 2%nat)) = false.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u5_tn_dual_red_3 :
  Qeq_bool (planb4_tn 3%nat) (zz_phat (planb4_g1_pq 3%nat)) = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 3. Legacy-face disposal register (comment-only).            *)
(* ================================================================== *)

(* (a) Supersession.  The witness aq/bq sub-faces (planb4_aq,
   planb4_g1_witness:131-:132; planb4_bq, :134-:135) are Q-valued
   carriers of the S-only / A_{n,0}-only sub-assemblies: they lack the
   L_n clearing factor, the (-1)^(n+1) sign and the polynomial part
   t_n, and the header formula (witness:11-:12) writes the assembly
   exponent as -floor(5n/2)+1.  That +1 exponent form is refuted by
   the frozen tables at n = 1 and n = 2: it yields 1/2 * 12 * 5636/3 =
   11272 != 22544 = A(1) and 1/2 * 840 * (-1) * (-3078046528/105) =
   1539023264 != 3078046528 = A(2), while the +2 form
   2^(-floor(5n/2)+2) yields both table values (pinned in
   planb4_g1_ab_def:48-:53, whose born-window anchors are green in
   planb4_g1_ab_def.vo).  Both sub-faces are superseded by
   planb4_g1_ab_def (planb4_abqA :60, planb4_abqB :65, projected by
   planb4_g1_A/planb4_g1_B :72/:74, the total nat -> Z assembly with
   36 vm_compute-verified born-window anchors); the witness aq/bq
   Definitions stay in place upstream and are registered here as
   pending retirement, together with the planb4_pdiv face of
   Section 2.

   (b) SCALE-NORMALIZATION TASK disposal.  The note (witness:141-:146)
   asks for a carrier scale factor to be pinned against the oracle
   faces A_{1,0} = -2392 and A_{1,3} = 8000, under the premise that
   piu_zz_Aj lives in a raw M_j-sum scale (the |A| * 2^(4n) erratum
   route).  The machine anchors planb4_A10_anchor and
   planb4_A13_anchor (witness:148-:152) close by kernel conversion --
   Qeq_bool (piu_zz_Aj 1 0) (-2392 # 1) = true and Qeq_bool
   (piu_zz_Aj 1 3) (8000 # 1) = true, green in planb4_g1_witness.vo
   and load-verified by this unit's probe -- so piu_zz_Aj already
   lives in the reduced A_j scale, the raw-scale premise is refuted,
   and no carrier rescale is due.  The Section 1 bites stand on the
   same reduced scale: the poleA readout and the series carrier agree
   at all eleven points with no intervening factor. *)

(* ================================================================== *)
(* Section 4. Assumption audit.                                        *)
(* ================================================================== *)

Print Assumptions planb4_u5_aj_1_0.
Print Assumptions planb4_u5_aj_1_1.
Print Assumptions planb4_u5_aj_1_2.
Print Assumptions planb4_u5_aj_1_3.
Print Assumptions planb4_u5_aj_2_0.
Print Assumptions planb4_u5_aj_2_1.
Print Assumptions planb4_u5_aj_2_2.
Print Assumptions planb4_u5_aj_2_3.
Print Assumptions planb4_u5_aj_2_4.
Print Assumptions planb4_u5_aj_2_5.
Print Assumptions planb4_u5_aj_2_6.
Print Assumptions planb4_u5_tn_dual_red_1.
Print Assumptions planb4_u5_tn_dual_red_2.
Print Assumptions planb4_u5_tn_dual_red_3.
