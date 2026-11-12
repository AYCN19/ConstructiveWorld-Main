(* ConstructiveWorld-Main - numeric certificate anchors of the quadratic
   Pade lower-bound slice. *)

(** * UpReqPadeLower_cert: rational cross-checks of the Pade
      polynomial identity.

    Mission.  The three numeric anchors of the lower-bound slice,
      moved verbatim from the main module under the certificate
      separation rule: the polynomial identity
      [exp6 * Q2 - P2] evaluated at [y = 1/2] and at [y = 1] against
      the exact rational values [121/2211840] and [19/8640], and the
      witness value [(1/720) * (1/2)^5 = 1/23040].  Each proof is a
      single vm_compute reduction followed by reflexivity.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp, the
      S04-S15 module chain, UpReqPadeExp, UpReqQExpTail,
      UpReqPadeQLeg; Stdlib QArith, Arith, Lia, Setoid (the same
      require face the anchors had at their original position).
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeLower; companion of UpReqPadeLower.v.
    Constructivity.  Pure Set-level equalities on rationals; no
      axioms; every audited name is Closed under the global context.
    Build.  coqc -q -native-compiler no with the l0_local face plus
      the node build face, Coq 9.3.0, wrapped by the temperature
      guard.
*)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* Numeric cross-checks of the polynomial identity (exact rational
   values at the two anchor points). *)
Lemma cpl_sent_g6_half : exp_partial 6%nat (1#2) * pade_den 2%nat (1#2)
                         - pade_num 2%nat (1#2) == (121#2211840).
Proof. vm_compute. reflexivity. Qed.

Lemma cpl_sent_g6_one : exp_partial 6%nat (1#1) * pade_den 2%nat (1#1)
                        - pade_num 2%nat (1#1) == (19#8640).
Proof. vm_compute. reflexivity. Qed.

(* Witness value: (1/720) * (1/2)^5 = 1/23040. *)
Lemma cpl_sent_witness_half : q_pow (1#2) 5%nat / 720 == (1#23040).
Proof. vm_compute. reflexivity. Qed.
