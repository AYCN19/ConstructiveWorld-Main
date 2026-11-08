(* ===================================================================== *)
(* GaC3_Z04_ZetaMainPart_cert.v                                           *)
(* Mission. Certificate face of node C3-Z04 (segment C3): the literal     *)
(*   Q-level certificates for the main-part expansion of                  *)
(*   GaC3_Z04_ZetaMainPart.  Bands: (1) the window literals of the pole   *)
(*   carrier at the sample strip point (2, 1): the pole distance          *)
(*   d = (a-1)^2 + b^2 = 2, the kernel coordinates (1/2, -1/2), the       *)
(*   exact norm face |mp|^2 = 1/d = 1/2; (2) the derivative main part at  *)
(*   the same window: ((x^2-y^2), -2xy) / d^2 = (0, -1/2) and the norm    *)
(*   face |mp2|^2 = 1/d^2 = 1/4; (3) the quarter-fold bookkeeping of the  *)
(*   three slot theorems, 2*(K/4) + 2*(K/4) = K, at the squared draft     *)
(*   constants B, B2, B2' sampled as 1, 4, 9, 16, 25, 36 (the squares of  *)
(*   1..6); (4) the strip-window shadow: the rational order faces of the  *)
(*   two window premises at a = 2 and the right-sub-strip cap chain       *)
(*   1/4 <= d, 1 <= 4d, 1/d <= 4 at the second sample a = 3/2, b = 1      *)
(*   (d = 5/4).  Honest scope: the Real-line slot theorems and the        *)
(*   premise slots L-Z04-A..F live on the proof face of the stem with     *)
(*   the continuation carriers and the truncation as section data; these  *)
(*   literals certify the rational bookkeeping of the faces, not the      *)
(*   Real-line bounds.                                                    *)
(* Dependencies. Stdlib [QArith]; [S01_BaseRing] (the Set-sorted Id       *)
(*   carrier and id_refl); [S07_RealSetoidExpLog] (the RealSetoid Id_eq   *)
(*   bridge elim, the S01 NatLe / S02 QleT' pattern).  No proof-face      *)
(*   module (the certificate stands beside the stem, zero Require of it). *)
(* References. drafts_C3.md C3-Z04 card (certificate band); tree          *)
(*   precedent [GaC3_Z01_LogDerivSeries_cert.v] and                       *)
(*   [GaC3_V03_VinoZeta_cert.v] (literal Definitions + one Id-carried     *)
(*   acceptance theorem, the Id-carrier reflection pattern with the       *)
(*   bridge elim).                                                        *)
(* Constructivity. All statements are Set-sorted Id-carried boolean       *)
(*   identities; no global assumption commands; the single acceptance     *)
(*   theorem closes with vm_compute under the global context.             *)
(* Build. coqc -native-compiler no -q -Q . "" -Q ../boot_src "" (sandbox  *)
(*   pair, from the work directory), single compile lane under the        *)
(*   thermal guard wrapper.                                               *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith.
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.

(* ---- Band 1: the pole carrier window literals at (a, b) = (2, 1) ---- *)

Definition z04_win_d : Q := ((2 - 1) * (2 - 1) + 1 * 1)%Q.
Definition z04_win_u : Q := ((2 - 1) * / z04_win_d)%Q.
Definition z04_win_v : Q := (- (1 * / z04_win_d))%Q.
Definition z04_win_norm : Q := (z04_win_u * z04_win_u + z04_win_v * z04_win_v)%Q.

Definition z04_mp_ok : bool :=
  andb (Qeq_bool z04_win_d (2 # 1))
       (andb (Qeq_bool z04_win_u (1 # 2))
             (andb (Qeq_bool z04_win_v (- (1 # 2)))
                   (andb (Qeq_bool z04_win_norm (1 # 2))
                         (Qeq_bool (/ z04_win_d) (1 # 2))))).

(* ---- Band 2: the derivative main-part window literals ---- *)

Definition z04_win_u2 : Q := (((2 - 1) * (2 - 1) - 1 * 1) * / (z04_win_d * z04_win_d))%Q.
Definition z04_win_v2 : Q := (- ((2 * (2 - 1) * 1) * / (z04_win_d * z04_win_d)))%Q.
Definition z04_win_norm2 : Q := (z04_win_u2 * z04_win_u2 + z04_win_v2 * z04_win_v2)%Q.

Definition z04_mp2_ok : bool :=
  andb (Qeq_bool z04_win_u2 0)
       (andb (Qeq_bool z04_win_v2 (- (1 # 2)))
             (andb (Qeq_bool z04_win_norm2 (1 # 4))
                   (Qeq_bool (/ (z04_win_d * z04_win_d)) (1 # 4)))).

(* ---- Band 3: the quarter-fold bookkeeping of the three slot theorems ---- *)

Definition z04_fold_ok (k : Q) : bool :=
  Qeq_bool (2 * (k * (1 # 4)) + 2 * (k * (1 # 4))) k.

(* The squared draft constants: B^2 at 1, 4; B2^2 at 9, 16; B2'^2 at     *)
(* 25, 36 (the squares of 1..6). *)
Definition z04_B_ok : bool := andb (z04_fold_ok 1) (z04_fold_ok 4).
Definition z04_B2_ok : bool := andb (z04_fold_ok 9) (z04_fold_ok 16).
Definition z04_B2p_ok : bool := andb (z04_fold_ok 25) (z04_fold_ok 36).

(* The strict-order reader (the V03 certificate helper shape; the 9.3    *)
(* QArith carries no Qlt_bool, so the comparison reads the Qcompare).   *)
Definition z04_qlt (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.

(* ---- Band 4: the strip-window shadow and the sub-strip cap chain ---- *)

Definition z04_win2_d : Q := ((3 # 2 - 1) * (3 # 2 - 1) + 1 * 1)%Q.

Definition z04_window_ok : bool :=
  andb (Qle_bool (1 # 2) 2)
       (andb (Qle_bool 2 2)
             (andb (z04_qlt 0 z04_win_d)
                   (andb (z04_qlt 0 z04_win2_d)
                         (andb (Qle_bool (/ z04_win2_d) 4)
                               (Qle_bool 1 (4 * z04_win2_d)))))).

(* ---- The single acceptance witness (Id-carried, S01 / S02 shape) ---- *)

Definition z04_cert_all : bool :=
  andb (andb z04_mp_ok z04_mp2_ok)
       (andb (andb z04_B_ok z04_B2_ok) (andb z04_B2p_ok z04_window_ok)).

Theorem z04_cert_all_true : Id z04_cert_all true.
Proof. vm_compute. exact id_refl. Qed.

(* Bridge elim: the Set bearer to the native boolean identity. *)
Lemma z04_cert_true_eq : Id z04_cert_all true -> z04_cert_all = true.
Proof. intro H. exact (RealSetoid.Id_eq _ _ H). Qed.
