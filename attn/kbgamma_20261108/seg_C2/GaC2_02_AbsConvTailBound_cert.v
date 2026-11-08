(* ConstructiveWorld-Main - certificate face of node C2.02: literal Q-level
   certificates for the geometric/block arithmetic. *)
(** * GaC2_02_AbsConvTailBound_cert: certificate face of node C2.02.
    Mission.  The certificate face of node C2.02: the literal Q-level
      certificates and the single vm_compute acceptance witness
      (zzPhi shape: literal Definitions plus one all_true theorem)
      for the geometric/block arithmetic of GaC2_02; the proof face
      carries no vm_compute token, and this file requires no
      proof-face module (the proof face consumes this face by name).
    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith].  Requires no
      proof-face module of this development.
    References.  The proof face [GaC2_02_AbsConvTailBound].  GAPASUME
      obligation account (slots discharged as Section hypotheses on
      the proof face, precedent piu_zz_tau_enclosure_base
      HLn_rate_up): L-C2.02-A [Hlnmono] and L-C2.02-B [Hln2pos] are
      L0 stock (anchors: [real_log_lt_mono] S07:6540, where
      [real_log] := [cw_log] S07:7881; [real_log_one] S07:7894; the
      congruence [real_log_wd] cast from [real_weak_trich] S07:5749 +
      [cauchy_real_exp_mono] + [cw_log_exp_right]); not open supply
      faces.  L-C2.02-C [Hnormtri] (new, stem), the complex n-fold triangle
      inequality in rational-margin form on the blocked Dirichlet tail:
      |c_tail M N s|^2 < (sum_{M<j<=N} j^{-sigma})^2 + d for all Q d > 0
      when cRe s = sigma.  OPEN SUPPLY FACE (honest disclosure): no
      [real_abs] and no n-fold Cauchy-Schwarz face in the tree or the C1
      sandbox; [gaC1_14_norm_sq_pair_lt] is the 2-fold form only and
      loses a factor 2 per term, so it cannot give the uniform-in-N
      bound; supply route: C1.4 convergence-engine extension (pointwise
      Lagrange identity) via [GaC1_Iface_*]; consumer:
      [zeta_part_cauchy_bound], whose own content is the C2.01
      tail-difference identity plus (a).  [Hnpos] is satisfiable by
      leaf-a [nat_real_pos].  Leaf split (precedent
      piu_zz_tau_segtree_1024_leaf_a..h + _merge): stem = three main
      lemmas + slot C; leaves _a/_b/_c = base / sectioned core /
      condensation engine; all seven blueprint names (draft-2) present
      ([q_condensation_block] among them).
    Constructivity.  The single theorem [zz_g2_02_all_true] is a
      vm_compute acceptance over the literal Definitions: (1) the
      ratio constants 2^(1-sigma_0) at the integer samples
      sigma_0 = 2,3 (1/2, 1/4) are positive and below one (the draft
      sample 3/2 is not Q-representable for 2^(1-sigma), so the band
      is {2,3}); (2) the draft constant 1 + q/(1-q) at the samples
      equals 2 and 4/3; (3) the block count identities 2^(k+1) - 2^k
      = 2^k for k = 1..5; [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_02_AbsConvTailBound_cert.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3]. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.Arith.

Definition zz_qlt (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.

Definition zz_g2_02_q_at2 : Q := (1 # 2)%Q.
Definition zz_g2_02_q_at3 : Q := (1 # 4)%Q.
Definition zz_g2_02_c_at2 : Q := (2 # 1)%Q.
Definition zz_g2_02_c_at3 : Q := (4 # 3)%Q.

Definition zz_g2_02_ratio_ok : bool :=
  andb (andb (zz_qlt (0 # 1)%Q zz_g2_02_q_at2) (zz_qlt zz_g2_02_q_at2 (1 # 1)%Q))
       (andb (zz_qlt (0 # 1)%Q zz_g2_02_q_at3) (zz_qlt zz_g2_02_q_at3 (1 # 1)%Q)).

Definition zz_g2_02_const_ok : bool :=
  andb (Qeq_bool zz_g2_02_c_at2
          ((1 # 1)%Q + zz_g2_02_q_at2 / ((1 # 1)%Q - zz_g2_02_q_at2)))
       (Qeq_bool zz_g2_02_c_at3
          ((1 # 1)%Q + zz_g2_02_q_at3 / ((1 # 1)%Q - zz_g2_02_q_at3))).

Fixpoint zz_g2_02_block_ok (k : nat) : bool :=
  match k with
  | O => true
  | S i => andb (Nat.eqb (Nat.pow 2 (S i) - Nat.pow 2 i) (Nat.pow 2 i))
                 (zz_g2_02_block_ok i)
  end.

Definition zz_g2_02_all : bool :=
  andb (andb zz_g2_02_ratio_ok zz_g2_02_const_ok) (zz_g2_02_block_ok 5).

Theorem zz_g2_02_all_true : zz_g2_02_all = true.
Proof. vm_compute. reflexivity. Qed.
