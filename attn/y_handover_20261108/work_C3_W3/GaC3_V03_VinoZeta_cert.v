(* ===================================================================== *)
(* GaC3_V03_VinoZeta_cert.v                                               *)
(*                                                                       *)
(* Mission. Certificate face of node C3-V03 (segment C3) - the          *)
(*   literal Q-level certificates for the Vinogradov-type 1-line bound   *)
(*   faces of GaC3_V03_VinoZeta: the exponent bookkeeping of the         *)
(*   squared re-carrier, the constant-fold bookkeeping at sample values, *)
(*   and the regime rational shadow.  The proof face carries no          *)
(*   vm_compute token (R2 separation); this slice closes its single      *)
(*   acceptance theorem with vm_compute under the global context.        *)
(*   Bands: (1) the squared-face exponent sums - the squares of the      *)
(*   draft bound faces (ln tau)^(2/3)(ln ln tau)^(1/3) and               *)
(*   (ln tau)^(4/3)(ln ln tau)^(1/3) are (ln tau)^(4/3)(ln ln tau)^(2/3) *)
(*   and (ln tau)^(8/3)(ln ln tau)^(2/3) (exponent addition 2/3+2/3 =    *)
(*   4/3, 1/3+1/3 = 2/3, 4/3+4/3 = 8/3); (2) the cube reading of the     *)
(*   draft faces (3*(2/3) = 2, 3*(1/3) = 1, 3*(4/3) = 4 - the            *)
(*   equivalent integer-exponent identity behind the squared re-carrier  *)
(*   statement-face); (3) the constant-fold bookkeeping                  *)
(*   2*(cv^2/4) + 2*(cv^2/4) = cv^2 at the sample constants 1, 2, 4, 7   *)
(*   (the explicit CV bookkeeping of the main theorems); (4) the        *)
(*   regime rational shadow 9 < 16 (the anchor of the large-ordinate     *)
(*   slot: 3 < 4 gives e^2 < 9 < 16 with e < 3, so ln 16 > 1 > 0 and     *)
(*   the double log stays in the positive domain) plus the positivity    *)
(*   of the four exponents.  Honest scope: the Real-line bound faces    *)
(*   and the explicit constants CV, CV' live on the proof face with the  *)
(*   GAPASUME slot family L-V03-A..F; these literals certify the         *)
(*   rational bookkeeping of the faces, not the Real-line bounds.        *)
(* Dependencies. Stdlib QArith; S01_BaseRing (the Set-sorted Id carrier  *)
(*   and id_refl); S07_RealSetoidExpLog (the RealSetoid Id_eq bridge     *)
(*   elim, the S01 :88 / S02 :99 pattern).  No proof-face module.        *)
(* References. drafts_C3.md C3-V03 card (certificate band); tree        *)
(*   precedent GaC3_Z01_LogDerivSeries_cert.v (literal Definitions +     *)
(*   one Id-carried acceptance theorem, the S01 NatLe :88 / S02 QleT'    *)
(*   :99 Id-carrier reflection pattern with the bridge elim).            *)
(* Constructivity. All statements Set-sorted Id-carried boolean         *)
(*   identities; no global assumption commands; the single acceptance    *)
(*   theorem closes with vm_compute under the global context.            *)
(* Build. coqc -native-compiler no -q -Q . "" -Q <boot_src> "" (sandbox *)
(*   pair, from the work directory), single compile lane under the       *)
(*   cpu_guard v3 wrapper.                                               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith.
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.

(* ---- Band 1: the squared-face exponent sums ---- *)

Definition v03_exp_sq_ok : bool :=
  andb (Qeq_bool ((2 # 3) + (2 # 3)) (4 # 3))
       (andb (Qeq_bool ((1 # 3) + (1 # 3)) (2 # 3))
             (Qeq_bool ((4 # 3) + (4 # 3)) (8 # 3))).

(* ---- Band 2: the cube reading of the draft faces ---- *)

Definition v03_exp_cube_ok : bool :=
  andb (Qeq_bool (3 * (2 # 3)) 2)
       (andb (Qeq_bool (3 * (1 # 3)) 1) (Qeq_bool (3 * (4 # 3)) 4)).

(* ---- Band 3: the constant-fold bookkeeping at sample constants ---- *)

Definition v03_fold_ok (cv : Q) : bool :=
  Qeq_bool (2 * (cv * cv * (1 # 4)) + 2 * (cv * cv * (1 # 4))) (cv * cv).

Definition v03_balance_ok : bool :=
  andb (v03_fold_ok 1) (andb (v03_fold_ok 2) (andb (v03_fold_ok 4) (v03_fold_ok 7))).

(* ---- Band 4: the regime rational shadow and exponent positivity ---- *)

Definition v03_qlt (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.

Definition v03_regime_ok : bool :=
  andb (v03_qlt (9 # 1) (16 # 1))
       (andb (v03_qlt 0 (2 # 3))
             (andb (v03_qlt 0 (1 # 3))
                   (andb (v03_qlt 0 (4 # 3)) (v03_qlt 0 (8 # 3))))).

(* ---- The single acceptance witness (Id-carried, S01 :88 / S02 :99 shape) ---- *)

Definition v03_cert_all : bool :=
  andb (andb v03_exp_sq_ok v03_exp_cube_ok) (andb v03_balance_ok v03_regime_ok).

Theorem v03_cert_all_true : Id v03_cert_all true.
Proof. vm_compute. exact id_refl. Qed.

(* Bridge elim: the Set bearer to the native boolean identity. *)
Lemma v03_cert_true_eq : Id v03_cert_all true -> v03_cert_all = true.
Proof. intro H. exact (RealSetoid.Id_eq _ _ H). Qed.
