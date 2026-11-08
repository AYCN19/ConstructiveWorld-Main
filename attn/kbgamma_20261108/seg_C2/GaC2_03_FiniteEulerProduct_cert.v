(* ConstructiveWorld-Main - numeric certificate face of the finite Euler
   product stem. *)
(** * GaC2_03_FiniteEulerProduct_cert: numeric certificates for C2.03.
    Mission.  The numeric certificate face of the finite Euler product
      stem (the vm_compute place of the node; the stem carries zero
      vm_compute).  Sample scope: the K_p table spot-check is taken at
      N = 4 because plm_v p k = plm_vmax p k k recurses on the fuel k
      with two unshared calls per level (exponential 2^k), so the
      vm_compute sample fuel is pinned to the tree's own smoke scale
      (k = 12, the abl_Pr_lcmdecomp_04 smoke precedent); the lcm-table
      face carries the larger samples N = 5, 10 where plm_v is not
      evaluated.  hl_lcm_upto 4 = 12 = 2^2 * 3;  pen_primes_upto 4 =
      [2; 3];  K_p = (2, 1) for p = (2, 3);  prodf_pow Ktab [2;3] = 12
      = M_4 (the M2 numeric spot-check), and hl_lcm_upto 5 = 60,
      hl_lcm_upto 10 = 2520 (the M_5 / M_10 tables).
    Dependencies.  Stdlib [List] (+ [ListNotations]).  Requires
      [HansonLcm] ([hl_lcm_upto]), [abl_Pr_lcmdecomp_04] ([plm_v]),
      [abl_Pr_enum_02] ([pen_primes_upto]), and
      [GaC2_03_FiniteEulerProduct] ([prodf_pow]) of this development.
    References.  The proof face [GaC2_03_FiniteEulerProduct] (routes
      M1/M2; the M2 numeric spot-check is [cert_prod_4] here).
    Constructivity.  Numeric lemmas close by vm_compute + reflexivity;
      the literal 2520 for hl_lcm_upto 10 was machine-printed by the
      REPL probe; [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_03_FiniteEulerProduct_cert.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3] (-LoadLimit 60 -TempLimit 98
      -AllowG3 -GearForce 0 -CoreN 2). *)

Require Import HansonLcm.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_enum_02.
Require Import GaC2_03_FiniteEulerProduct.
From Stdlib Require Import List.
Import ListNotations.

(* The lcm tables (no plm_v in the statements; cheap). *)
Lemma cert_hl_4 : hl_lcm_upto 4 = 12.
Proof. vm_compute. reflexivity. Qed.

Lemma cert_hl_5 : hl_lcm_upto 5 = 60.
Proof. vm_compute. reflexivity. Qed.

Lemma cert_hl_10 : hl_lcm_upto 10 = 2520.
Proof. vm_compute. reflexivity. Qed.

(* The prime enumeration at the K-sample point. *)
Lemma cert_pen_4 : pen_primes_upto 4 = (2 :: 3 :: nil)%list.
Proof. vm_compute. reflexivity. Qed.

(* The K_p table at N = 4 (fuel 12, the tree smoke scale): 2^2 | 12,        *)
(* 3^1 | 12, and neither 2^3 nor 3^2 divides 12. *)
Lemma cert_K_4 :
  map (fun p => (p, plm_v p (hl_lcm_upto 4))) (pen_primes_upto 4)
  = (2, 2) :: (3, 1) :: nil.
Proof. vm_compute. reflexivity. Qed.

(* The prime-table product identity at N = 4 (the M2 numeric spot-check): *)
(* 2^2 * 3 = 12 = hl_lcm_upto 4. *)
Lemma cert_prod_4 :
  prodf_pow (fun p => plm_v p (hl_lcm_upto 4)) (pen_primes_upto 4)
  = hl_lcm_upto 4.
Proof. vm_compute. reflexivity. Qed.

(* ==== Supply-face audit tail ==== *)
(* 6 numeric certificate lemmas (cert_hl_4, cert_hl_5, cert_hl_10,          *)
(* cert_pen_4, cert_K_4, cert_prod_4); vm_compute per the certificate       *)
(* discipline with the fuel scale above; zero assumed constants and zero    *)
(* abandoned proofs. *)
