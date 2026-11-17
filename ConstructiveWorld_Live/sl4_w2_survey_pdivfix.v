(* ========================================================================= *)
(* ConstructiveWorld-Main outbound package - SL4 wave-2 survey pdiv faces.   *)
(* Mission      : SL4-W2-SURVEY-PDIV (survey SL4 sections 4/9; debt row      *)
(*                D-SL4-8, witness pdiv retirement groundwork):              *)
(*                planb4_w2_pdiv_fix mirrors the authoritative divider in    *)
(*                three points: zeros in the pad slots (the registered      *)
(*                root cause), per-step drop of the cancelled leading       *)
(*                slot, and canonical order with trailing-zero trim.        *)
(*                Machine-checked: defect = false register and corrected    *)
(*                = true agreement over n = 1..6; agreement under the       *)
(*                authoritative readout at n = 1..3; the witness            *)
(*                accumulator's factor-4 normalization register.            *)
(* Statements   : planb4_w2_shift_fix / _pdroplast / _pdiv_loop_fix /        *)
(*                _pdiv_fix / _P_fix / _tn_fix / _phat_fix;                  *)
(*                planb4_w2_pdiv_defect_1..6; _pdiv_fix_agree_1..6;          *)
(*                _phat_fix_agree_1..3; _tn_norm_gap_1..3.                   *)
(* Dependencies : planb4_g1_witness; planb4_g1_laur_extract (the             *)
(*                authoritative quotient planb4_g1_pq); zzm2_qpoly          *)
(*                (plq_eqb); zzm1_gauss (zzId); zzm1b_linform_bridge         *)
(*                (zz_phat).  Byte-exact origin/main blobs; source routing  *)
(*                in the seat receipt.                                       *)
(* References   : survey SL4 sections 4/9 (row D-SL4-8); the root-cause and  *)
(*                dual-route registers of the carrier-alignment unit; the   *)
(*                certified Laurent anchors zz3_pq_1..6.                     *)
(* Constructivity: transparent list-Q data (one Fixpoint); decidable         *)
(*                vm_compute comparisons; postulate-free throughout.         *)
(* Build        : coqc -native-compiler no -q -Q <closure root> ""           *)
(*                sl4_w2_survey_pdivfix.v (Rocq 9.3.0, scripted form;        *)
(*                explicit -o products outside the source root).             *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith List.
Import ListNotations.
Require Import planb4_g1_witness.
Require Import planb4_g1_laur_extract.
Require Import zzm2_qpoly.
Require Import zzm1_gauss.
Require Import zzm1b_linform_bridge.

(* ================================================================== *)
(* Section 1. The corrected division.  Three structural repairs over  *)
(*            the witness loop, each mirroring the authoritative      *)
(*            divider's shape (zzm2 pdiv_go): zeros in the pad slots  *)
(*            (the registered root cause), the cancelled leading      *)
(*            slot dropped per step so the division advances (the     *)
(*            length-preserving subtraction alone re-reads zero       *)
(*            forever), and the canonical coefficient order with the  *)
(*            trailing-zero trim (the authoritative quotient shape).  *)
(* ================================================================== *)

Definition planb4_w2_shift_fix (c : Q) (k : nat) (a : list Q) : list Q :=
  repeat 0%Q k ++ map (fun x => c * x)%Q a.

Definition planb4_w2_pdroplast (p : list Q) : list Q := rev (tl (rev p)).

Fixpoint planb4_w2_pdiv_loop_fix (a b : list Q) (fuel : nat) : list Q :=
  match fuel with
  | O => []
  | S f =>
      if Nat.ltb (length a) (length b)
      then []
      else
        let c := (planb4_list_last a / planb4_list_last b)%Q in
        let shifted := planb4_w2_shift_fix c ((length a - length b)%nat) b in
        let a' := planb4_w2_pdroplast (planb4_psub_aligned a shifted) in
        c :: planb4_w2_pdiv_loop_fix a' b f
  end.

(* The corrected quotient in the authoritative canonical shape (the   *)
(* loop emits high-to-low; the authoritative face is low-first with   *)
(* the trailing-zero trim).                                           *)
Definition planb4_w2_pdiv_fix (a b : list Q) : list Q :=
  ptrim (rev (planb4_w2_pdiv_loop_fix a b (length a))).

(* The corrected polynomial part on the witness N and D channels. *)
Definition planb4_w2_P_fix (n : nat) : list Q :=
  planb4_w2_pdiv_fix (planb4_N n) (planb4_D n).

(* The corrected polynomial-part integral (the witness tn shape over  *)
(* the corrected quotient).                                           *)
Definition planb4_w2_tn_fix (n : nat) : Q :=
  fst (planb4_tn_acc (planb4_w2_P_fix n) 0).

(* ================================================================== *)
(* Section 2. The defect register over the certified window n = 1..6: *)
(*            the stock witness quotient disagrees with the           *)
(*            authoritative Laurent-route quotient at every index.    *)
(* ================================================================== *)

Lemma planb4_w2_pdiv_defect_1 :
  zzId (plq_eqb (planb4_P 1%nat) (planb4_g1_pq 1%nat)) false.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_defect_2 :
  zzId (plq_eqb (planb4_P 2%nat) (planb4_g1_pq 2%nat)) false.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_defect_3 :
  zzId (plq_eqb (planb4_P 3%nat) (planb4_g1_pq 3%nat)) false.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_defect_4 :
  zzId (plq_eqb (planb4_P 4%nat) (planb4_g1_pq 4%nat)) false.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_defect_5 :
  zzId (plq_eqb (planb4_P 5%nat) (planb4_g1_pq 5%nat)) false.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_defect_6 :
  zzId (plq_eqb (planb4_P 6%nat) (planb4_g1_pq 6%nat)) false.
Proof. vm_compute. reflexivity. Qed.


(* ================================================================== *)
(* Section 3. The corrected division agrees with the authoritative    *)
(*            quotient pointwise over the certified window n = 1..6.  *)
(* ================================================================== *)

Lemma planb4_w2_pdiv_fix_agree_1 :
  zzId (plq_eqb (planb4_w2_P_fix 1%nat) (planb4_g1_pq 1%nat)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_fix_agree_2 :
  zzId (plq_eqb (planb4_w2_P_fix 2%nat) (planb4_g1_pq 2%nat)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_fix_agree_3 :
  zzId (plq_eqb (planb4_w2_P_fix 3%nat) (planb4_g1_pq 3%nat)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_fix_agree_4 :
  zzId (plq_eqb (planb4_w2_P_fix 4%nat) (planb4_g1_pq 4%nat)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_fix_agree_5 :
  zzId (plq_eqb (planb4_w2_P_fix 5%nat) (planb4_g1_pq 5%nat)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_pdiv_fix_agree_6 :
  zzId (plq_eqb (planb4_w2_P_fix 6%nat) (planb4_g1_pq 6%nat)) true.
Proof. vm_compute. reflexivity. Qed.


(* ================================================================== *)
(* Section 4. The corrected quotient under the authoritative readout  *)
(*            agrees with the authoritative pipeline at n = 1..3,     *)
(*            flipping the machine-false dual-route register to true  *)
(*            at the same indices; the witness accumulator's own      *)
(*            normalization (2 * int_k weighting) is machine-pinned   *)
(*            as the constant factor 4 against the authoritative     *)
(*            readout, a convention gap independent of the division   *)
(*            defect.                                                 *)
(* ================================================================== *)

(* The corrected quotient under the authoritative polynomial-part    *)
(* readout.                                                          *)
Definition planb4_w2_phat_fix (n : nat) : Q :=
  zz_phat (planb4_w2_P_fix n).

Lemma planb4_w2_phat_fix_agree_1 :
  Qeq_bool (planb4_w2_phat_fix 1%nat) (zz_phat (planb4_g1_pq 1%nat)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_phat_fix_agree_2 :
  Qeq_bool (planb4_w2_phat_fix 2%nat) (zz_phat (planb4_g1_pq 2%nat)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_phat_fix_agree_3 :
  Qeq_bool (planb4_w2_phat_fix 3%nat) (zz_phat (planb4_g1_pq 3%nat)) = true.
Proof. vm_compute. reflexivity. Qed.


Lemma planb4_w2_tn_norm_gap_1 :
  Qeq_bool (planb4_w2_tn_fix 1%nat)
            (((4 # 1)%Q * zz_phat (planb4_g1_pq 1%nat))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_tn_norm_gap_2 :
  Qeq_bool (planb4_w2_tn_fix 2%nat)
            (((4 # 1)%Q * zz_phat (planb4_g1_pq 2%nat))%Q) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_w2_tn_norm_gap_3 :
  Qeq_bool (planb4_w2_tn_fix 3%nat)
            (((4 # 1)%Q * zz_phat (planb4_g1_pq 3%nat))%Q) = true.
Proof. vm_compute. reflexivity. Qed.


(* ================================================================== *)
(* Section 5. Assumption audit (kernel verdicts, printed at build).   *)
(* ================================================================== *)

Print Assumptions planb4_w2_pdiv_defect_1.
Print Assumptions planb4_w2_pdiv_fix_agree_1.
Print Assumptions planb4_w2_pdiv_defect_2.
Print Assumptions planb4_w2_pdiv_fix_agree_2.
Print Assumptions planb4_w2_pdiv_defect_3.
Print Assumptions planb4_w2_pdiv_fix_agree_3.
Print Assumptions planb4_w2_pdiv_defect_4.
Print Assumptions planb4_w2_pdiv_fix_agree_4.
Print Assumptions planb4_w2_pdiv_defect_5.
Print Assumptions planb4_w2_pdiv_fix_agree_5.
Print Assumptions planb4_w2_pdiv_defect_6.
Print Assumptions planb4_w2_pdiv_fix_agree_6.
Print Assumptions planb4_w2_phat_fix_agree_1.
Print Assumptions planb4_w2_tn_norm_gap_1.
Print Assumptions planb4_w2_phat_fix_agree_2.
Print Assumptions planb4_w2_tn_norm_gap_2.
Print Assumptions planb4_w2_phat_fix_agree_3.
Print Assumptions planb4_w2_tn_norm_gap_3.


(* =================== end of the wave-2 pdiv faces ================= *)
