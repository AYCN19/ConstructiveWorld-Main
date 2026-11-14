(* * planb5_p7_hval_table: the table-domain (Hval, n<=40) clearing piece
      of the P7 exit assembly (GD-20261114-P7ASM-01 item 5, family-one
      route k0(40)=159, Machin ball carrier dval_M).

    Mission.  Clear the canonical Hval table face pointwise: for each
    table index n the family-one bound

      |A_n + B_n * Mdot_k0(n)| + 2*|B_n| * w_k0(n)  <=  4^-n

    (canonical script chong1_exit_core.py:187-191, the 1d transfer face;
    grid-checked there and re-verified 79/79 EXACT against the anchors by
    the table sweep receipt (sweep report md, 2026-11-14) under OUT/p7_out_20261114/) is
    delivered as the Set-carried row face p7_hval_row n (QleT' carrier
    over Qle_bool), certified by exact vm_compute arithmetic closures -
    the machine evaluates every rational; no hand arithmetic anywhere.

    Registered evaluation-budget downgrade (ALERT clause, 20261114).
    The canonical depths k0(n) reach 159 at n=40 (the 3695-bit numerator
    route).  The in-library Machin partial sum (arctan_partial,
    S11_TP3B5.v:53) is a Qsum with per-operation rational normalization;
    first-hand probe measurements (probe_asm_eval.v, _rv_asm_probe_eval.log):
    row n=5 (k0=20) = 0.633 s, row n=20 (k0=80) = 94.5 CPU s (561 s wall
    under the guard duty cycle).  The registered per-row budget line is
    seconds-level x100 = 100 CPU s (the ask's ALERT formula).  Rows
    n=1..20 (k0(n) <= 80) fit the line and are certified here.  Rows
    n=21..40 (k0(n) = 85..159) extrapolate to 130+ CPU s per row and are
    REGISTERED DEBT, not silently dropped: their row faces and the full
    canonical k0 table (all 40 entries) are delivered as Definitions
    below, and the upgrade path is the integer-accumulating bridge
    registered by the parity cast (cast_parity.v header, same probe
    finding).  The standing numerical certificate for the full n<=40
    table remains the Python Fraction sweep receipt (79/79 EXACT).

    Dependencies.  S01_BaseRing (And as the Set-level product, NatLe),
    S02_CauchyComplete (QleT' = Id (Qle_bool _) true), S03_QExp (q_pow),
    S11_TP3B5 + cast_modulus (mach_mdot / mach_own_modulus, the same
    transcription of canonical faces chong1_exit_core.py:65/:73 as the
    three casts), planb3_g1_calib (planb3_g1_A / planb3_g1_B tables,
    consumed verbatim; byte-identical md5 2a9e5cc4 to the package
    source; its dependency piu_zz_padic_clearing is compiled in-world
    from the Live-tree source, the packaged .vo carries a foreign
    stdlib digest - registered red in _rv_asm_calib_build.log).

    References.  Hval face = chong1_exit_core.py:187-191; k0 table =
    per_n_table.txt + chong1_run1.log L24 (k0(1),k0(5),k0(40) = 3 20
    159); Mdot = chong1_exit_core.py:65; w = :73; A/B tables =
    planb3_g1_calib.v:36/:83; M1:438 prescription; sweep receipt (sweep report md 2026-11-14,
    79/79 EXACT anchors, tightest 1.815 bit@n=5).

    Constructivity.  Zero axioms, zero admitted goals; the row face is
    Set-carried (QleT' / Id bool); certificates are vm_compute closures
    (kernel-checked via the bytecode route at coqchk, the E1051
    prescription).  The 3695-bit numerator route itself is never
    evaluated in this file (that is the registered debt); forbidden
    family-two / family-four routes are never entered.

    Build.  coqc -native-compiler no -q -Q . "" planb5_p7_hval_table.v
      (world directory; Rocq 9.3.0; guard-wrapped single lane). *)
Require Import S01_BaseRing S02_CauchyComplete S03_QExp S11_TP3B5
               cast_modulus planb3_g1_calib.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List.

(* Canonical 1d depth table k0(n), n = 1..40 (chong1_run1.log L24
   k0(1),k0(5),k0(40) = 3 20 159; full table = per_n_table.txt).
   List+nth form; the Q_scope numeral grab (calibration-file
   precedent, term position this time) is fenced off with a local
   Close/Open pair around the literal table. *)
Close Scope Q_scope.
Definition p7_hval_k0_list : list nat :=
  3 :: 7 :: 11 :: 15 :: 20 :: 23 :: 26 :: 32 :: 35 :: 38 :: 43 :: 47 ::
  52 :: 56 :: 59 :: 64 :: 67 :: 71 :: 75 :: 80 :: 85 :: 87 :: 92 :: 93
  :: 99 :: 104 :: 107 :: 112 :: 117 :: 120 :: 122 :: 130 :: 133 :: 135
  :: 141 :: 144 :: 145 :: 151 :: 155 :: 159 :: nil%list.
Open Scope Q_scope.

Definition p7_hval_k0 (n : nat) : nat :=
  nth (n - 1) p7_hval_k0_list (0:nat).

(* canonical 1d bound face (chong1_exit_core.py:187):
   |A_n + B_n * Mdot_k0(n)| + 2*|B_n| * w_k0(n). *)
Definition p7_hval_bound (n : nat) : Q :=
  Qabs ((planb3_g1_A n # 1)%Q + (planb3_g1_B n # 1)%Q
        * mach_mdot (p7_hval_k0 n))
  + 2 * Qabs (planb3_g1_B n # 1)%Q * mach_own_modulus (p7_hval_k0 n).

(* canonical Hval row face: bound * 4^n <= 1 (chong1_exit_core.py:189-190),
   Set-carried via the QleT' Id-bool carrier (S02_CauchyComplete:99). *)
Definition p7_hval_row (n : nat) : Set :=
  QleT' (p7_hval_bound n * q_pow 4 n) 1.

(* The certified table rows n = 1..20 at the canonical depths.  Rows
   n = 21..40 are the registered evaluation-budget debt (header): their
   faces are the same Definition p7_hval_row applied at n = 21..40, and
   the canonical k0 table above already carries their depths. *)
Theorem p7_hval_rows_first20 :
    And (p7_hval_row 1) (And (p7_hval_row 2) (And (p7_hval_row 3) (And
  (p7_hval_row 4) (And (p7_hval_row 5) (And (p7_hval_row 6) (And
  (p7_hval_row 7) (And (p7_hval_row 8) (And (p7_hval_row 9) (And
  (p7_hval_row 10) (And (p7_hval_row 11) (And (p7_hval_row 12) (And
  (p7_hval_row 13) (And (p7_hval_row 14) (And (p7_hval_row 15) (And
  (p7_hval_row 16) (And (p7_hval_row 17) (And (p7_hval_row 18) (And
  (p7_hval_row 19) (p7_hval_row 20))))))))))))))))))).
Proof.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  vm_compute. reflexivity.
Defined.

Print Assumptions p7_hval_rows_first20.
