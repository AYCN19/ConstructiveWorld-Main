(* sl3_d3_gf_anchors.v - machine check of the GF decomposition identity:    *)
(*   inject_Z (poleZ n k) = (-1)^(3n-k) x A_(n,3n-k) x (10^(3n+1+k) # 1)    *)
(*   at n = 1,2 (all j), where poleZ is the folded pole-numerator table     *)
(*   object and A_j is the tree carrier piu_zz_Aj.                          *)
(* Mission      : point anchors certifying the GF decomposition identity at  *)
(*   the head samples, as the machine-outside gate for the D-SL3-3 carrier  *)
(*   fold (sl3_d3_gf_carrier.v).                                            *)
(* Dependencies : piu_zz_kernel_sum (the A_j carrier); Stdlib ZArith,       *)
(*   Arith, Lia, List, QArith.                                              *)
(* References   : the SL3 slot draft, section 1.3 (GF dominance blueprint); *)
(*   survey volume SL3.                                                     *)
(* Constructivity: decidable Q-equality checks only; no proofs, no claims   *)
(*   beyond the identity instances shown.                                   *)
(* Build        : coqc -q -native-compiler no -Q <dir> sl3_d3_gf_anchors.v  *)
From Stdlib Require Import ZArith Arith Lia List QArith.
Require Import piu_zz_kernel_sum.
Import ListNotations.
Open Scope Q_scope.

Fixpoint binomP (n k : nat) {struct n} : nat :=
  match k with
  | O => 1%nat
  | S k' =>
      match n with
      | O => 0%nat
      | S n' => (binomP n' k' + binomP n' (S k'))%nat
      end
  end.

Definition tbl := list Z.

Fixpoint add_tbl (f g : tbl) : tbl :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | a :: f', b :: g' => (a + b)%Z :: add_tbl f' g'
  end.

Fixpoint conv (f g : tbl) : tbl :=
  match f with
  | [] => []
  | a :: f' => add_tbl (map (Z.mul a) g) (0%Z :: conv f' g)
  end.

Fixpoint gf_pow (f : tbl) (k : nat) : tbl :=
  match k with
  | O => [1]%Z
  | S k' => conv f (gf_pow f k')
  end.

Definition ptable (n : nat) : tbl :=
  map (Z.mul 5)
    (conv (gf_pow [5%Z; 1%Z] (2 * n))
          (conv (gf_pow [40%Z; 12%Z; 1%Z] (2 * n))
                (gf_pow [20%Z; 8%Z; 1%Z] (2 * n)))).

Definition kappaZ (n r : nat) : Z :=
  ((if Nat.odd r then -1 else 1) * Z.of_nat (binomP (3 * n + r) r))%Z.

Fixpoint pole_sumR (n k i : nat) : Z :=
  match i with
  | O => (nth k (ptable n) 0%Z * kappaZ n 0 * 10 ^ Z.of_nat k)%Z
  | S i' =>
      (pole_sumR n k i'
      + nth (k - S i') (ptable n) 0%Z * kappaZ n (S i')
        * 10 ^ Z.of_nat (k - S i'))%Z
  end.

Definition poleZ (n k : nat) : Z := pole_sumR n k k.

Lemma anchor_n1_0 :
  inject_Z (poleZ 1 3) ==
   (((if Nat.odd 3 then (-1)#1 else (1)#1) * piu_zz_Aj 1 0) * ((10 ^ (3 * 1 + 1 + 3))#1)).
Proof. vm_compute. reflexivity. Qed.

Lemma anchor_n1_1 :
  inject_Z (poleZ 1 2) ==
   (((if Nat.odd 2 then (-1)#1 else (1)#1) * piu_zz_Aj 1 1) * ((10 ^ (3 * 1 + 1 + 2))#1)).
Proof. vm_compute. reflexivity. Qed.

Lemma anchor_n1_2 :
  inject_Z (poleZ 1 1) ==
   (((if Nat.odd 1 then (-1)#1 else (1)#1) * piu_zz_Aj 1 2) * ((10 ^ (3 * 1 + 1 + 1))#1)).
Proof. vm_compute. reflexivity. Qed.

Lemma anchor_n1_3 :
  inject_Z (poleZ 1 0) ==
   (((if Nat.odd 0 then (-1)#1 else (1)#1) * piu_zz_Aj 1 3) * ((10 ^ (3 * 1 + 1 + 0))#1)).
Proof. vm_compute. reflexivity. Qed.

Lemma anchor_n2_0 :
  inject_Z (poleZ 2 6) ==
   (((if Nat.odd 6 then (-1)#1 else (1)#1) * piu_zz_Aj 2 0) * ((10 ^ (3 * 2 + 1 + 6))#1)).
Proof. vm_compute. reflexivity. Qed.

Lemma anchor_n2_3 :
  inject_Z (poleZ 2 3) ==
   (((if Nat.odd 3 then (-1)#1 else (1)#1) * piu_zz_Aj 2 3) * ((10 ^ (3 * 2 + 1 + 3))#1)).
Proof. vm_compute. reflexivity. Qed.

Lemma anchor_n2_6 :
  inject_Z (poleZ 2 0) ==
   (((if Nat.odd 0 then (-1)#1 else (1)#1) * piu_zz_Aj 2 6) * ((10 ^ (3 * 2 + 1 + 0))#1)).
Proof. vm_compute. reflexivity. Qed.
