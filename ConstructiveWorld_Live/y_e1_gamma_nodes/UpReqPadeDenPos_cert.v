(* ConstructiveWorld-Main - UpReqPadeDenPos_cert.v - general-n Pade denominator positivity for path C, statement surface preserved verbatim from UpReqPadeDenPos.v (seat1 bound surgery). *)
(* ==========================================================================
   Mission. R2 certificate file: the three n=2/n=3 numeric instances (vm_compute end-to-end cross-check), moved here
     per the certificate-separation rule (LINT-5).
   Dependencies. S01_BaseRing..S15_TailFEPUp chain, UpReqPadeExp,
     UpReqAltSumPos, UpReqPadeQLeg, UpReqPadeDenPos_b; Stdlib QArith, Arith, Lia, Setoid.
   References. Path C general-n Pade denominator positivity (PC2 engine
     altsum_nonneg_leT); source of record: UpReqPadeDenPos.v
     in the debtscan closure dossier (all-green at surgery time).
   Constructivity. Zero admission literals, no classical logic; statement
     surface fully Set-carried (QltT/QleT/QleT'); explicit assumptions
     declared symmetrically in the source dossier header, none forced.
   Build. coqc -q -native-compiler no -Q l0_local "" -Q build "" (Rocq 9.3.0
     at D:/ComplexAnalysis/attn/opam93), compile gate wrapped by
     50_toolkit/cpu_guard_v3.ps1; accepted by 50_toolkit/accept_node.py
     six-chain gate, node UpReqPadeDenPos.
   ========================================================================== *)
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
Require Import S15_TailFEPUp_dep.
Require Import UpReqPadeExp_dep UpReqAltSumPos_dep.
Require Import UpReqPadeQLeg_dep.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
Require Import UpReqPadeDenPos_b.

(* ===== S3 bonus: n=2/n=3 instance end-to-end cross-check via vm_compute ===== *)
(* den_2(x) = 1 - x/2 + x^2/12; den_3(x) = 1 - x/2 + x^2/10 - x^3/120 *)

Lemma pdp_den2_three_fifths : QltT 0 (pade_den 2 (3#5)).
Proof. vm_compute. reflexivity. Qed.

Lemma pdp_den2_one : QleT' 0 (pade_den 2 1%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdp_den3_one : QleT' 0 (pade_den 3 1%Q).
Proof. vm_compute. reflexivity. Qed.
