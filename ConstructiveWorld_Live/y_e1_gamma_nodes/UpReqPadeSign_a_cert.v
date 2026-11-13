(* ConstructiveWorld-Main - certificate face of the Pade n=1 sign node. *)

(** * UpReqPadeSign_a_cert: certificate face of the boxed Pade-sign edition.

    Mission.  Certificate face for the boxed edition of the Pade n=1
      denominator-sign node: the three closed numerical facts of the
      family, each closing by machine reduction in one step.  Bands:
      [pds_den0_one] - the n = 0 denominator is the unit for every x
      (sum_upto 1 keeps only the k = 0 term and q_pow recurses on the
      nat index without touching x); [pds_c10] - the leading Pade
      coefficient of the n = 1 row equals one (same closed-reduction
      style as the anchor piece; an off-by-one in the truncated
      subtraction or a flipped alternating sign turns this red);
      [pds_den1_half] - the anchor value Q_1(1/2) is positive, the
      numeric cross-check of the main face against Q_1(1/2) == 3/4.
      No statement outside this node consumes these three names.
    Dependencies.  S01_BaseRing through S03 (library face),
      UpReqPadeExp_dep5 (seat-local spine edition for pade_den,
      pade_coeff, q_pow, sum_upto), UpReqPadeQLeg; stdlib QArith,
      Arith, Lia, Setoid.
    References.  Statement-face conservation: each Lemma line below is
      byte-identical to the library edition UpReqPadeSign (same names,
      same order inside the family, same quantifier bodies); only the
      comment faces differ.
    Constructivity.  Set-carried; the two QltT-shaped facts reduce to
      the Id-of-bool face over closed Q data; nothing is left open and
      the assumption audit closes under the global context.
    Build.  coqc -q -native-compiler no over the l0_local plus build
      loadpath roots (opam93 9.3.0, cpu-guard wrapped, 96-band).
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp_dep5.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== S1 base: the n = 0 unit fact ===== *)

(* The n = 0 denominator is the unit: sum_upto (S 0) keeps only the
   k = 0 term, and the index-driven recursion closes end to end by
   machine reduction over the neutral x. *)
Lemma pds_den0_one : forall x : Q, pade_den 0 x == 1%Q.
Proof. intro x. vm_compute. reflexivity. Qed.

(* ===== closed coefficient anchor of the n = 1 row ===== *)

Lemma pds_c10 : pade_coeff 1 0%nat == 1%Q.
Proof. vm_compute. reflexivity. Qed.

(* ===== S3 anchor cross-check ===== *)

(* Q_1(1/2) > 0: numeric cross-check against the anchor value
   Q_1(1/2) == 3/4; the boolean comparison reduces to true. *)
Lemma pds_den1_half : QltT 0 (pade_den 1 (1#2)).
Proof. unfold QltT. vm_compute. reflexivity. Qed.

Print Assumptions pds_den0_one.
Print Assumptions pds_c10.
Print Assumptions pds_den1_half.