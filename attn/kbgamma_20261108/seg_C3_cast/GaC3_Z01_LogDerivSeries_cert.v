(* ConstructiveWorld-Main - literal Q-level certificates for the C3-Z01 Dirichlet-series face. *)

(** * GaC3_Z01_LogDerivSeries_cert: certificate face of the Z01 node.

    Mission.  Certificate face of node C3-Z01 (segment C3): the
    literal Z/Q-level certificates and the single vm_compute
    acceptance witness for the Lambda-weighted Dirichlet-series
    machinery of [GaC3_Z01_LogDerivSeries]; the proof face carries no
    vm_compute token (R2 separation).  Direction lock (spec 2.4-6):
    no proof-face module.  Bands: (1) the von Mangoldt weight
    structure of the lcm power difference at the integer level - for
    n = 1..32 the ratio zz_lcm_range n / zz_lcm_range (n-1) satisfies
    1 <= ratio <= n, ratio divides n, and ratio is one-or-tree-prime
    ([zz_primeb]): the numeric accounting that the weight carrier
    Lambda(n) = ln lcm(1..n) - ln lcm(1..n-1) is supported exactly on
    the prime divisors (the D1-B3 consumption face); (2) the Z-level
    telescope shadow: the product of the ratios over 1..32 equals
    zz_lcm_range 32 (the integer shadow of sum_{n<=N} Lambda(n) = ln
    lcm(1..N)); (3) the geometric band constants at the integer
    samples sigma = 2, 3 (q = 1/2, 1/4; condensation constant 2, 4/3
    - the draft sample sigma = 3/2 is not Q-representable for
    2^(1-sigma), band {2,3}, mirroring the C2.02 certificate band);
    (4) the dyadic block count identities 2^(k+1) - 2^k = 2^k,
    k = 1..5.  Honest scope: the Real-line convergence statements
    and the explicit constant [z01_bound] live on the proof face with
    the GAPASUME premise family (L-Z01-A/B L0-stock instantiable;
    L-Z01-C the open n-fold-triangle supply face); these literals
    certify the weight structure and the rational shadow of the
    constants, not the Real-line bounds
    [zz_g3_z01_all_true].

    Dependencies.  [piu_zz_padic_clearing] ([zz_lcm_range],
    [zz_primeb] - L0 stock), Stdlib [QArith], [Arith].  No
    proof-face module.

    References.  drafts_C3.md C3-Z01 card (certificate band); ZZ
    theory [fds_mangoldt_eq] :29 / [abs_conv_abscissa_log_deriv]
    :39; tree precedent [GaC2_02_AbsConvTailBound_cert] (literal
    Definitions + one all_true theorem, zzPhi shape).

    Constructivity.  All statements Set-sorted boolean identities;
    zero assumed constants, zero abandoned proofs; the single
    theorem closes with vm_compute under the global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
      GaC3_Z01_LogDerivSeries_cert.v] compiles cleanly (exit 0) from
      the work directory (sandbox pair), single compile lane under
      the cpu_guard v3 wrapper. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Arith.Arith.
Require Import piu_zz_padic_clearing.

(* ---- The lcm power difference at the integer level ---- *)

Definition zz_g3_z01_ratio (n : nat) : Z :=
  Z.div (piu_zz_padic_clearing.zz_lcm_range n)
        (piu_zz_padic_clearing.zz_lcm_range (Nat.pred n)).

(* The weight structure: 1 <= ratio <= n, ratio | n, and ratio is        *)
(* one-or-prime (the von Mangoldt support face). *)
Definition zz_g3_z01_lam_ok (n : nat) : bool :=
  andb (Z.leb 1 (zz_g3_z01_ratio n))
       (andb (Z.leb (zz_g3_z01_ratio n) (Z.of_nat n))
             (andb (Z.eqb (Z.modulo (Z.of_nat n) (zz_g3_z01_ratio n)) 0)
                   (orb (Z.eqb (zz_g3_z01_ratio n) 1)
                        (zz_primeb (Z.to_nat (zz_g3_z01_ratio n)))))).

Fixpoint zz_g3_z01_lam_band (k : nat) : bool :=
  match k with
  | O => zz_g3_z01_lam_ok 1
  | S i => andb (zz_g3_z01_lam_ok (S (S i))) (zz_g3_z01_lam_band i)
  end.

(* The Z-level telescope shadow: the product of the ratios over 1..N     *)
(* equals the lcm fold. *)
Fixpoint zz_g3_z01_ratio_prod (N : nat) : Z :=
  match N with
  | O => 1
  | S m => Z.mul (zz_g3_z01_ratio_prod m) (zz_g3_z01_ratio (S m))
  end.

(* ---- The geometric band constants (integer samples sigma = 2, 3) ---- *)

Definition zz_qlt (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.

Definition zz_g3_z01_q_at2 : Q := (1 # 2)%Q.
Definition zz_g3_z01_q_at3 : Q := (1 # 4)%Q.
Definition zz_g3_z01_c_at2 : Q := (2 # 1)%Q.
Definition zz_g3_z01_c_at3 : Q := (4 # 3)%Q.

Definition zz_g3_z01_ratio_ok : bool :=
  andb (andb (zz_qlt (0 # 1)%Q zz_g3_z01_q_at2) (zz_qlt zz_g3_z01_q_at2 (1 # 1)%Q))
       (andb (zz_qlt (0 # 1)%Q zz_g3_z01_q_at3) (zz_qlt zz_g3_z01_q_at3 (1 # 1)%Q)).

Definition zz_g3_z01_const_ok : bool :=
  andb (Qeq_bool zz_g3_z01_c_at2
          ((1 # 1)%Q + zz_g3_z01_q_at2 / ((1 # 1)%Q - zz_g3_z01_q_at2)))
       (Qeq_bool zz_g3_z01_c_at3
          ((1 # 1)%Q + zz_g3_z01_q_at3 / ((1 # 1)%Q - zz_g3_z01_q_at3))).

(* ---- The dyadic block count bookkeeping ---- *)

Fixpoint zz_g3_z01_block_ok (k : nat) : bool :=
  match k with
  | O => true
  | S i => andb (Nat.eqb (Nat.pow 2 (S i) - Nat.pow 2 i) (Nat.pow 2 i))
                 (zz_g3_z01_block_ok i)
  end.

(* ---- The single acceptance witness ---- *)

Definition zz_g3_z01_all : bool :=
  andb (andb (zz_g3_z01_lam_band 31)
             (Z.eqb (zz_g3_z01_ratio_prod 32)
                    (piu_zz_padic_clearing.zz_lcm_range 32)))
       (andb (andb zz_g3_z01_ratio_ok zz_g3_z01_const_ok) (zz_g3_z01_block_ok 5)).

Theorem zz_g3_z01_all_true : zz_g3_z01_all = true.
Proof. vm_compute. reflexivity. Qed.
