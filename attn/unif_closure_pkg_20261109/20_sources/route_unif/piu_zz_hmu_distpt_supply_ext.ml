
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type empty_set = |

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

(** val gmin : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1 **)

let gmin cmp x y =
  match cmp x y with
  | Gt -> y
  | _ -> x

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q0 u =
    match x with
    | O -> Pair (q0, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q0) y
       | S u' -> divmod x' y q0 u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val log2_iter : nat -> nat -> nat -> nat -> nat **)

  let rec log2_iter k p q0 r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> log2_iter k' (S p) (S q0) q0
       | S r' -> log2_iter k' p (S q0) r')

  (** val log2 : nat -> nat **)

  let log2 n =
    log2_iter (pred n) O (S O) O
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)

  let rec ggcdn n a b =
    match n with
    | O -> Pair (XH, (Pair (a, b)))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n0 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n0 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n0 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ ->
            let Pair (g, p) = ggcdn n0 a0 b in
            let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
 end

(** val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos0 rmul x = function
| XI i0 -> let p = pow_pos0 rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos0 rmul x i0 in rmul p p
| XH -> x

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> sumbool **)

let z_lt_le_dec =
  z_lt_ge_dec

type q = { qnum : z; qden : positive }

(** val inject_Z : z -> q **)

let inject_Z x =
  { qnum = x; qden = XH }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum (Zpos q0.qden)) (Z.mul q0.qnum (Zpos p.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val qlt_le_dec : q -> q -> sumbool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q0 =
  let { qnum = qnum0; qden = _ } = q0 in
  (match qnum0 with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qpower_positive : q -> positive -> q **)

let qpower_positive =
  pow_pos0 qmult

(** val qpower : q -> z -> q **)

let qpower q0 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q0 p
| Zneg p -> qinv (qpower_positive q0 p)

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let Pair (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val qmin : q -> q -> q **)

let qmin =
  gmin qcompare

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

(** val natLe_lift : nat -> nat -> natLe **)

let natLe_lift n m =
  let b = Nat.leb n m in
  (match b with
   | True -> Id_refl
   | False -> assert false (* absurd case *))

type qseq = nat -> q

(** val qlt_bool : q -> q -> bool **)

let qlt_bool x y =
  match qcompare x y with
  | Lt -> True
  | _ -> False

type qltT = bool id

(** val qlt_to_QltT : q -> q -> qltT **)

let qlt_to_QltT x y =
  let c = qcompare x y in
  (match c with
   | Lt -> Id_refl
   | _ -> assert false (* absurd case *))

type qleT' = bool id

(** val qle_to_QleT' : q -> q -> qleT' **)

let qle_to_QleT' x y =
  let c = Z.compare (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))
  in
  (match c with
   | Gt -> assert false (* absurd case *)
   | _ -> Id_refl)

(** val qltT_0_1 : qltT **)

let qltT_0_1 =
  Id_refl

(** val qltT_0_2 : qltT **)

let qltT_0_2 =
  Id_refl

(** val qltT_0_3 : qltT **)

let qltT_0_3 =
  Id_refl

(** val qleT'_refl : q -> qleT' **)

let qleT'_refl x =
  let c = Z.compare (Z.mul x.qnum (Zpos x.qden)) (Z.mul x.qnum (Zpos x.qden))
  in
  (match c with
   | Gt -> assert false (* absurd case *)
   | _ -> Id_refl)

(** val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_trans x _ z0 _ _ =
  qle_to_QleT' x z0

(** val qltT_leT' : q -> q -> qltT -> qleT' **)

let qltT_leT' x y _ =
  qle_to_QleT' x y

(** val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_ltT_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_leT'_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qleT'_plus_compat : q -> q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_plus_compat a b c d _ _ =
  qle_to_QleT' (qplus a c) (qplus b d)

(** val qleT'_plus_nonneg_rT : q -> q -> qleT' -> qleT' **)

let qleT'_plus_nonneg_rT x y hy =
  qleT'_trans x (qplus x { qnum = Z0; qden = XH }) (qplus x y)
    (qle_to_QleT' x (qplus x { qnum = Z0; qden = XH }))
    (qleT'_plus_compat x x { qnum = Z0; qden = XH } y (qleT'_refl x) hy)

(** val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qltT_plus_leT'_ltT : q -> q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_plus_leT'_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_plus_ltT_ltT : q -> q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_plus_ltT_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_mult_compat_l : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_mult_compat_l x y z0 _ _ =
  qle_to_QleT' (qmult z0 x) (qmult z0 y)

(** val qleT'_mult_ltT_compat :
    q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT **)

let qleT'_mult_ltT_compat a b c d _ _ _ _ =
  qlt_to_QltT (qmult a c) (qmult b d)

(** val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT **)

let qmult_ltT_0_compat a b _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qmult a b)

(** val qeq_leT' : q -> q -> qleT' **)

let qeq_leT' =
  qle_to_QleT'

type qeqT = bool id

(** val qeq_imp_qeqT : q -> q -> qeqT **)

let qeq_imp_qeqT a b =
  let c = qcompare a b in
  (match c with
   | Eq -> Id_refl
   | _ -> assert false (* absurd case *))

(** val qabs_nonnegT : q -> qleT' **)

let qabs_nonnegT x =
  qle_to_QleT' { qnum = Z0; qden = XH } (qabs x)

(** val qltT_plus_pos_r : q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_pos_r x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qplus x y)

(** val qltT_div_pos : q -> q -> qltT -> qltT -> qltT **)

let qltT_div_pos x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x y)

(** val qltT_eq_compat_l : q -> q -> q -> qltT -> qltT **)

let qltT_eq_compat_l _ a' b _ =
  qlt_to_QltT a' b

(** val qltT_eq_compat_r : q -> q -> q -> qltT -> qltT **)

let qltT_eq_compat_r a _ b _ =
  qlt_to_QltT b a

(** val qltT_mult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_mult_ltT_compat_r a b c _ _ =
  qlt_to_QltT (qmult a c) (qmult b c)

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

type real_eq = q -> qltT -> (nat, nat -> natLe -> qltT) sigT

(** val real_plus : real -> real -> real **)

let real_plus x y =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  ExistT ((fun n -> qplus (x0 n) (x1 n)), (fun eps _ ->
  let s =
    c (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s in
  let s0 =
    c0 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x3, _) = s0 in
  ExistT ((max x2 x3), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qplus (x0 m) (x1 m)) (qplus (x0 n) (x1 n)))) eps))))

(** val real_opp : real -> real **)

let real_opp = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qopp (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qopp (x0 m)) (qopp (x0 n)))) eps))))

(** val real_zero : real **)

let real_zero =
  ExistT ((fun _ -> { qnum = Z0; qden = XH }), (fun _ heps -> ExistT (O,
    (fun _ _ _ _ -> heps))))

type real_lt = (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

type real_le = (real_lt, real_eq) or0

(** val real_lt_trans :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_trans x _ z0 hxy hyz =
  let ExistT (x0, a) = hxy in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (x2, a0) = hyz in
  let Pair (_, s0) = a0 in
  let ExistT (x3, _) = s0 in
  ExistT ((qplus x0 x2), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qplus x0 x2)), (ExistT ((max x1 x3),
  (fun n _ ->
  qlt_to_QltT (qplus x0 x2) (qminus (projT1 z0 n) (projT1 x n))))))))

(** val sum_abs_prefix : qseq -> nat -> q **)

let rec sum_abs_prefix u = function
| O -> { qnum = Z0; qden = XH }
| S n' -> qplus (sum_abs_prefix u n') (qabs (u n'))

(** val cauchy_bounded : qseq -> cauchy -> q **)

let cauchy_bounded u hu =
  let s = hu { qnum = (Zpos XH); qden = XH } Id_refl in
  let ExistT (x, _) = s in
  qplus (qplus (sum_abs_prefix u x) (qabs (u x))) { qnum = (Zpos XH); qden =
    XH }

(** val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT **)

let real_norm_bounded = function
| ExistT (x0, c) ->
  let s = cauchy_bounded x0 c in
  ExistT ((qplus (qabs s) { qnum = (Zpos XH); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qplus (qabs s) { qnum = (Zpos XH); qden = XH })),
  (fun k ->
  qle_to_QleT' (qabs (projT1 (ExistT (x0, c)) k))
    (qplus (qabs s) { qnum = (Zpos XH); qden = XH })))))

(** val real_mult : real -> real -> real **)

let real_mult x y =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  ExistT ((fun n -> qmult (x0 n) (x1 n)), (fun eps _ ->
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, a) = s in
  let Pair (_, q0) = a in
  let s0 = real_norm_bounded (ExistT (x1, c0)) in
  let ExistT (x3, a0) = s0 in
  let Pair (_, q1) = a0 in
  let mupos = qplus { qnum = (Zpos XH); qden = XH } (qabs x2) in
  let mvpos = qplus { qnum = (Zpos XH); qden = XH } (qabs x3) in
  let s1 =
    c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
  in
  let ExistT (x4, q2) = s1 in
  let s2 =
    c0 (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
  in
  let ExistT (x5, q3) = s2 in
  ExistT ((max x4 x5), (fun m n _ _ ->
  let hN1' = q2 m n in
  let hN2' = q3 m n in
  let htriT =
    qle_to_QleT' (qabs (qminus (qmult (x0 m) (x1 m)) (qmult (x0 n) (x1 n))))
      (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
  in
  let hMu_boundT =
    qleT'_trans (qabs (x0 m)) x2 mupos (q0 m) (qle_to_QleT' x2 mupos)
  in
  let hMv_boundT =
    qleT'_trans (qabs (x1 n)) x3 mvpos (q1 n) (qle_to_QleT' x3 mvpos)
  in
  let ht1T =
    qleT'_mult_ltT_compat (qabs (x0 m)) mupos (qabs (qminus (x1 m) (x1 n)))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
      (qlt_to_QltT { qnum = Z0; qden = XH } mupos)
      (qabs_nonnegT (qminus (x1 m) (x1 n))) hMu_boundT
      (hN2' (natLe_lift x5 m) (natLe_lift x5 n))
  in
  let ht2T =
    qleT'_mult_ltT_compat (qabs (x1 n)) mvpos (qabs (qminus (x0 m) (x0 n)))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
      (qlt_to_QltT { qnum = Z0; qden = XH } mvpos)
      (qabs_nonnegT (qminus (x0 m) (x0 n))) hMv_boundT
      (hN1' (natLe_lift x4 m) (natLe_lift x4 n))
  in
  qleT'_ltT_ltT (qabs (qminus (qmult (x0 m) (x1 m)) (qmult (x0 n) (x1 n))))
    (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
      (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
    eps htriT
    (qltT_leT'_ltT
      (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
      (qplus
        (qmult mupos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
        (qmult mvpos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
      eps
      (qltT_plus_ltT (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult mupos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n))))
        (qmult mvpos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
        ht1T ht2T)
      (qeq_leT'
        (qplus
          (qmult mupos
            (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
          (qmult mvpos
            (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
        eps))))))

(** val real_const : q -> real **)

let real_const c =
  ExistT ((fun _ -> c), (fun _ _ -> ExistT (O, (fun _ _ _ _ -> Id_refl))))

(** val q_arch_inv : q -> (nat, __) sigT **)

let q_arch_inv eps =
  let s = qarchimedean (qdiv { qnum = (Zpos XH); qden = XH } eps) in
  let n = mul (Z.to_nat (Zpos s)) (S (S O)) in ExistT (n, __)

(** val real_eq_refl : real -> real_eq **)

let real_eq_refl _ _ _ =
  ExistT (O, (fun _ _ -> Id_refl))

(** val real_eq_sym : real -> real -> real_eq -> real_eq **)

let real_eq_sym _ _ hxy =
  hxy

(** val real_eq_trans :
    real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_eq_trans x _ z0 hxy hyz eps _ =
  let s =
    hxy (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x0, _) = s in
  let s0 =
    hyz (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x1, _) = s0 in
  ExistT ((max x0 x1), (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 x n) (projT1 z0 n))) eps))

(** val real_one : real **)

let real_one =
  ExistT ((fun _ -> { qnum = (Zpos XH); qden = XH }), (fun _ _ -> ExistT (O,
    (fun _ _ _ _ -> Id_refl))))

(** val real_eq_of_zero_diff : real -> real -> real_eq **)

let real_eq_of_zero_diff _ _ _ _ =
  ExistT (O, (fun _ _ -> Id_refl))

(** val real_plus_comm : real -> real -> real_eq **)

let real_plus_comm x y =
  real_eq_of_zero_diff (real_plus x y) (real_plus y x)

(** val real_plus_assoc : real -> real -> real -> real_eq **)

let real_plus_assoc x y z0 =
  real_eq_of_zero_diff (real_plus x (real_plus y z0))
    (real_plus (real_plus x y) z0)

(** val real_plus_zero : real -> real_eq **)

let real_plus_zero x =
  real_eq_of_zero_diff (real_plus x real_zero) x

(** val real_plus_opp : real -> real_eq **)

let real_plus_opp x =
  real_eq_of_zero_diff (real_plus x (real_opp x)) real_zero

(** val real_mult_comm : real -> real -> real_eq **)

let real_mult_comm x y =
  real_eq_of_zero_diff (real_mult x y) (real_mult y x)

(** val real_mult_assoc : real -> real -> real -> real_eq **)

let real_mult_assoc x y z0 =
  real_eq_of_zero_diff (real_mult x (real_mult y z0))
    (real_mult (real_mult x y) z0)

(** val real_mult_one : real -> real_eq **)

let real_mult_one x =
  real_eq_of_zero_diff (real_mult x real_one) x

(** val real_mult_zero : real -> real_eq **)

let real_mult_zero x =
  real_eq_of_zero_diff (real_mult x real_zero) real_zero

(** val real_distrib : real -> real -> real -> real_eq **)

let real_distrib x y z0 =
  real_eq_of_zero_diff (real_mult x (real_plus y z0))
    (real_plus (real_mult x y) (real_mult x z0))

(** val real_le_refl : real -> real_le **)

let real_le_refl x =
  Inr (real_eq_refl x)

(** val real_lt_eq_lt :
    real -> real -> real -> real_lt -> real_eq -> real_lt **)

let real_lt_eq_lt x _ z0 hlt hyz =
  let ExistT (x0, a) = hlt in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 =
    hyz (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s0 in
  ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((max x1 x2), (fun n _ ->
  qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 z0 n) (projT1 x n))))))))

(** val real_eq_lt_lt :
    real -> real -> real -> real_eq -> real_lt -> real_lt **)

let real_eq_lt_lt x _ z0 hxy = function
| ExistT (x0, a) ->
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 =
    hxy (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s0 in
  ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((max x1 x2), (fun n _ ->
  qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 z0 n) (projT1 x n))))))))

(** val real_le_trans :
    real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_trans x y z0 hxy hyz =
  match hxy with
  | Inl hlt ->
    (match hyz with
     | Inl hlt' -> Inl (real_lt_trans x y z0 hlt hlt')
     | Inr heq' -> Inl (real_lt_eq_lt x y z0 hlt heq'))
  | Inr heq ->
    (match hyz with
     | Inl hlt' -> Inl (real_eq_lt_lt x y z0 heq hlt')
     | Inr heq' -> Inr (real_eq_trans x y z0 heq heq'))

(** val real_lt_le_trans :
    real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_le_trans x y z0 hlt = function
| Inl hlt' -> real_lt_trans x y z0 hlt hlt'
| Inr heq' -> real_lt_eq_lt x y z0 hlt heq'

(** val real_le_lt_trans :
    real -> real -> real -> real_le -> real_lt -> real_lt **)

let real_le_lt_trans x y z0 hle hlt =
  match hle with
  | Inl hlt' -> real_lt_trans x y z0 hlt' hlt
  | Inr heq -> real_eq_lt_lt x y z0 heq hlt

(** val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le **)

let real_lt_le_iff x _ = function
| Inl r -> Inl r
| Inr _ -> Inr (real_eq_refl x)

(** val real_lt_plus_compat :
    real -> real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_plus_compat a b c d hab hcd =
  let ExistT (x, a0) = hab in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hcd in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qplus x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qplus x x1)), (ExistT ((max x0 x2),
  (fun n _ ->
  qlt_to_QltT (qplus x x1)
    (qminus (projT1 (real_plus b d) n) (projT1 (real_plus a c) n))))))))

(** val q_pow : q -> nat -> q **)

let rec q_pow x = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult x (q_pow x m)

(** val q_fact : nat -> q **)

let rec q_fact = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult { qnum = (Z.of_nat (S m)); qden = XH } (q_fact m)

(** val exp_partial : nat -> q -> q **)

let rec exp_partial n x =
  match n with
  | O -> { qnum = (Zpos XH); qden = XH }
  | S m -> qplus (exp_partial m x) (qdiv (q_pow x (S m)) (q_fact (S m)))

(** val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT **)

let q_arch_geom a =
  let s =
    qarchimedean
      (qmult
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH })
        a)
  in
  ExistT ((Coq_Pos.to_nat s), (fun t _ ->
  qle_to_QleT'
    (qmult
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
      a)
    { qnum = (Z.of_nat (add t (S O))); qden = XH }))

(** val arch_decay : q -> q -> qleT' -> qltT -> (nat, qltT) sigT **)

let arch_decay c eps _ _ =
  let s = qarchimedean (qdiv c eps) in
  ExistT ((Coq_Pos.to_nat s),
  (qlt_to_QltT
    (qmult c
      (q_pow
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })
        (S (Coq_Pos.to_nat s))))
    eps))

(** val exp_partial_cauchy :
    q -> q -> (nat, nat -> nat -> __ -> __ -> qltT) sigT **)

let exp_partial_cauchy x eps =
  let a = qabs x in
  let s = q_arch_geom a in
  let ExistT (x0, _) = s in
  let c =
    qmult (qdiv (q_pow a x0) (q_fact x0))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let s0 =
    arch_decay c eps (qle_to_QleT' { qnum = Z0; qden = XH } c)
      (qlt_to_QltT { qnum = Z0; qden = XH } eps)
  in
  let ExistT (x1, _) = s0 in
  ExistT ((add x0 (S x1)), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (exp_partial m x) (exp_partial n x))) eps))

(** val exp_series : nat -> q -> q **)

let rec exp_series n b =
  match n with
  | O -> { qnum = (Zpos XH); qden = XH }
  | S m -> qplus (exp_series m b) (qdiv (q_pow b (S m)) (q_fact (S m)))

(** val exp_partial_cauchy_bounded :
    q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q ->
    qleT' -> qltT) sigT **)

let exp_partial_cauchy_bounded b eps _ hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let c =
    qmult (qdiv (q_pow b x) (q_fact x))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let s0 = arch_decay c eps (qle_to_QleT' { qnum = Z0; qden = XH } c) hep in
  let ExistT (x0, _) = s0 in
  ExistT ((add x (S x0)), (fun m n _ _ y _ ->
  qlt_to_QltT (qabs (qminus (exp_partial m y) (exp_partial n y))) eps))

(** val exp_series_arch :
    q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT **)

let exp_series_arch b _ =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let c =
    qplus (exp_series x b)
      (qmult (qdiv (q_pow b x) (q_fact x))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
  in
  ExistT (c, (Pair ((qle_to_QleT' { qnum = (Zpos XH); qden = XH } c),
  (fun n -> qle_to_QleT' (exp_series n b) c))))

(** val cauchy_real_exp : real -> real **)

let cauchy_real_exp = function
| ExistT (x0, c) ->
  ExistT ((fun n -> exp_partial n (x0 n)), (fun eps heps ->
    let s = real_norm_bounded (ExistT (x0, c)) in
    let ExistT (x1, a) = s in
    let Pair (q0, q1) = a in
    let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
    let ExistT (x2, a0) = s0 in
    let Pair (q2, q3) = a0 in
    let hCposT =
      qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }
        x2 qltT_0_1 q2
    in
    let s1 =
      c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
        (qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2) heps
          (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x2 qltT_0_2
            hCposT))
    in
    let ExistT (x3, q4) = s1 in
    let heps2 =
      qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2
    in
    let s2 =
      exp_partial_cauchy_bounded x1
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
        (qltT_leT' { qnum = Z0; qden = XH } x1 q0) heps2
    in
    let ExistT (x4, q5) = s2 in
    ExistT ((Nat.max x3 x4), (fun m n _ _ ->
    qltT_eq_compat_l
      (qabs
        (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
          (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
      (qabs (qminus (exp_partial m (x0 m)) (exp_partial n (x0 n)))) eps
      (let htriT =
         qle_to_QleT'
           (qabs
             (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
               (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
           (qplus
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
       in
       let ht1T =
         qleT'_trans
           (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
           (qmult (qabs (qminus (x0 m) (x0 n))) (exp_series m x1))
           (qmult (qabs (qminus (x0 m) (x0 n))) x2)
           (qle_to_QleT'
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qmult (qabs (qminus (x0 m) (x0 n))) (exp_series m x1)))
           (qleT'_mult_compat_l (exp_series m x1) x2
             (qabs (qminus (x0 m) (x0 n)))
             (qabs_nonnegT (qminus (x0 m) (x0 n))) (q3 m))
       in
       let ht2T = q5 m n (natLe_lift x4 m) (natLe_lift x4 n) (x0 n) (q1 n) in
       let ht3T =
         qltT_leT'_ltT (qmult (qabs (qminus (x0 m) (x0 n))) x2)
           (qmult (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
             x2)
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
           (qltT_mult_ltT_compat_r (qabs (qminus (x0 m) (x0 n)))
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)) x2
             hCposT (q4 m n (natLe_lift x3 m) (natLe_lift x3 n)))
           (qeq_leT'
             (qmult (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
               x2)
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
       in
       qleT'_ltT_ltT
         (qabs
           (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
             (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
         (qplus (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
           (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
         eps htriT
         (qltT_leT'_ltT
           (qplus
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
           (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
           eps
           (qltT_leT'_ltT
             (qplus
               (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
               (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
             (qplus (qmult (qabs (qminus (x0 m) (x0 n))) x2)
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             (qleT'_plus_ltT_ltT
               (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
               (qmult (qabs (qminus (x0 m) (x0 n))) x2)
               (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n))))
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T ht2T)
             (qltT_leT'
               (qplus (qmult (qabs (qminus (x0 m) (x0 n))) x2)
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               (qltT_plus_leT'_ltT (qmult (qabs (qminus (x0 m) (x0 n))) x2)
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht3T
                 (qleT'_refl (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })))))
           (qeq_leT'
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             eps)))))))

(** val cauchy_real_exp_zero : real_eq **)

let cauchy_real_exp_zero eps _ =
  ExistT (O, (fun n _ ->
    qlt_to_QltT { qnum =
      (Z.abs
        (Z.add (Z.mul (exp_partial n { qnum = Z0; qden = XH }).qnum (Zpos XH))
          (Zneg (exp_partial n { qnum = Z0; qden = XH }).qden)));
      qden = (Coq_Pos.mul (exp_partial n { qnum = Z0; qden = XH }).qden XH) }
      eps))

(** val sum_upto : nat -> (nat -> q) -> q **)

let rec sum_upto n f =
  match n with
  | O -> { qnum = Z0; qden = XH }
  | S n' -> qplus (sum_upto n' f) (f n')

(** val exp_partial_tail_small :
    q -> q -> qleT' -> qleT' -> (nat, __) sigT **)

let exp_partial_tail_small m c _ _ =
  let s = q_arch_geom m in
  let ExistT (x, _) = s in
  let s0 =
    arch_decay
      (qmult (qdiv (q_pow m x) (q_fact x))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qdiv { qnum = (Zpos XH); qden = XH } c)
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qmult (qdiv (q_pow m x) (q_fact x))
          (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
            XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv { qnum = (Zpos XH); qden = XH } c))
  in
  let ExistT (x0, _) = s0 in ExistT ((add x (S x0)), __)

(** val cauchy_real_exp_pos : real -> real_lt **)

let cauchy_real_exp_pos = function
| ExistT (x0, c) ->
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x1, a) = s in
  let Pair (q0, _) = a in
  let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
  let ExistT (x2, a0) = s0 in
  let Pair (q1, _) = a0 in
  let hCposT =
    qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } x2
      qltT_0_1 q1
  in
  let s1 =
    exp_partial_tail_small x1 x2 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) q1
  in
  let ExistT (x3, _) = s1 in
  ExistT
  ((qdiv { qnum = (Zpos XH); qden = XH }
     (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)),
  (Pair
  ((qltT_div_pos { qnum = (Zpos XH); qden = XH }
     (qmult { qnum = (Zpos (XO XH)); qden = XH } x2) qltT_0_1
     (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x2 qltT_0_2
       hCposT)),
  (ExistT ((add (mul (S (S O)) x3) (S O)), (fun n _ ->
  qltT_eq_compat_r (qminus (exp_partial n (x0 n)) { qnum = Z0; qden = XH })
    (exp_partial n (x0 n))
    (qdiv { qnum = (Zpos XH); qden = XH }
      (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
    (qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH }
        (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
      (exp_partial n (x0 n)))))))))

(** val real_abs : real -> real **)

let real_abs = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qabs (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qabs (x0 m)) (qabs (x0 n)))) eps))))

(** val real_metric : real -> real -> real **)

let real_metric x y =
  real_abs (real_plus x (real_opp y))

(** val real_inv_pos : real -> real_lt -> real **)

let real_inv_pos x hx =
  let ExistT (x0, c) = x in
  let ExistT (x1, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x2, _) = s in
  ExistT ((fun n ->
  match Nat.leb x2 n with
  | True -> qinv (x0 n)
  | False -> qinv (x0 x2)), (fun eps _ ->
  let delta = qmult eps (qmult x1 x1) in
  let hdlt = qlt_to_QltT { qnum = Z0; qden = XH } (qmult eps (qmult x1 x1)) in
  let s0 = c delta hdlt in
  let ExistT (x3, _) = s0 in
  ExistT ((Nat.max x2 x3), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qinv (x0 m)) (qinv (x0 n)))) eps))))

(** val real_inv_pos_correct : real -> real_lt -> real_eq **)

let real_inv_pos_correct x hx eps _ =
  let ExistT (x0, _) = x in
  let ExistT (_, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x1, (fun n _ ->
  let b = Nat.leb x1 n in
  (match b with
   | True ->
     qlt_to_QltT
       (qabs
         (qminus (qmult (x0 n) (qinv (x0 n))) { qnum = (Zpos XH); qden = XH }))
       eps
   | False -> assert false (* absurd case *))))

(** val real_inv_pos_pos : real -> real_lt -> real_lt **)

let real_inv_pos_pos x hx =
  let ExistT (x0, c) = x in
  let ExistT (_, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, _) = s0 in
  ExistT ((qinv (qplus x2 { qnum = (Zpos XH); qden = XH })), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qinv (qplus x2 { qnum = (Zpos XH); qden = XH }))),
  (ExistT (x1, (fun n _ ->
  let b = Nat.leb x1 n in
  (match b with
   | True ->
     qlt_to_QltT (qinv (qplus x2 { qnum = (Zpos XH); qden = XH }))
       (qminus (qinv (x0 n)) { qnum = Z0; qden = XH })
   | False -> assert false (* absurd case *))))))))

module RealSetoid =
 struct
  (** val real_eq_le : real -> real -> real_eq -> real_le **)

  let real_eq_le _ _ hab =
    Inr hab

  (** val real_lt_le_iff_req :
      real -> real -> (real_lt, real_eq) or0 -> real_le **)

  let real_lt_le_iff_req a b = function
  | Inl r -> real_lt_le_iff a b (Inl r)
  | Inr r -> real_eq_le a b r

  (** val real_eq_plus_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_plus_compat a b c d hac hbd eps _ =
    let hhalf0 =
      qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
    in
    let s = hac (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
    let ExistT (x, _) = s in
    let s0 = hbd (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
    let ExistT (x0, _) = s0 in
    ExistT ((Nat.max x x0), (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_plus a b) k) (projT1 (real_plus c d) k)))
      eps))

  (** val real_eq_opp_compat : real -> real -> real_eq -> real_eq **)

  let real_eq_opp_compat a b hab eps heps =
    let s = hab eps heps in
    let ExistT (x, _) = s in
    ExistT (x, (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_opp a) k) (projT1 (real_opp b) k))) eps))

  (** val real_eq_mult_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_mult_compat a b c d hac hbd eps heps =
    let s = real_norm_bounded a in
    let ExistT (x, a0) = s in
    let Pair (_, q0) = a0 in
    let s0 = real_norm_bounded d in
    let ExistT (x0, a1) = s0 in
    let Pair (_, q1) = a1 in
    let mupos = qplus { qnum = (Zpos XH); qden = XH } (qabs x) in
    let mvpos = qplus { qnum = (Zpos XH); qden = XH } (qabs x0) in
    let muposT = qlt_to_QltT { qnum = Z0; qden = XH } mupos in
    let mvposT = qlt_to_QltT { qnum = Z0; qden = XH } mvpos in
    let hepsB =
      qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos) heps
        (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } mupos
          qltT_0_2 muposT)
    in
    let hepsA =
      qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos) heps
        (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } mvpos
          qltT_0_2 mvposT)
    in
    let s1 =
      hbd (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)) hepsB
    in
    let ExistT (x1, q2) = s1 in
    let s2 =
      hac (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)) hepsA
    in
    let ExistT (x2, q3) = s2 in
    ExistT ((Nat.max x1 x2), (fun k _ ->
    qltT_eq_compat_l
      (qabs
        (qminus (qmult (projT1 a k) (projT1 b k))
          (qmult (projT1 c k) (projT1 d k))))
      (qabs (qminus (projT1 (real_mult a b) k) (projT1 (real_mult c d) k)))
      eps
      (let hbdT =
         qle_to_QleT'
           (qabs
             (qminus (qmult (projT1 a k) (projT1 b k))
               (qmult (projT1 c k) (projT1 d k))))
           (qplus
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k)))))
       in
       let hMa_boundT =
         qleT'_trans (qabs (projT1 a k)) x mupos (q0 k) (qle_to_QleT' x mupos)
       in
       let hMd_boundT =
         qleT'_trans (qabs (projT1 d k)) x0 mvpos (q1 k)
           (qle_to_QleT' x0 mvpos)
       in
       let ht1T =
         qleT'_mult_ltT_compat (qabs (projT1 a k)) mupos
           (qabs (qminus (projT1 b k) (projT1 d k)))
           (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
           muposT (qabs_nonnegT (qminus (projT1 b k) (projT1 d k))) hMa_boundT
           (q2 k (natLe_lift x1 k))
       in
       let ht2T =
         qleT'_mult_ltT_compat (qabs (projT1 d k)) mvpos
           (qabs (qminus (projT1 a k) (projT1 c k)))
           (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
           mvposT (qabs_nonnegT (qminus (projT1 a k) (projT1 c k))) hMd_boundT
           (q3 k (natLe_lift x2 k))
       in
       let ht1bT =
         qeq_leT'
           (qmult mupos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
       in
       let ht2bT =
         qeq_leT'
           (qmult mvpos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
       in
       let ht1T' =
         qltT_leT'_ltT
           (qmult (qabs (projT1 a k))
             (qabs (qminus (projT1 b k) (projT1 d k))))
           (qmult mupos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T ht1bT
       in
       let ht2T' =
         qltT_leT'_ltT
           (qmult (qabs (projT1 d k))
             (qabs (qminus (projT1 a k) (projT1 c k))))
           (qmult mvpos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht2T ht2bT
       in
       qleT'_ltT_ltT
         (qabs
           (qminus (qmult (projT1 a k) (projT1 b k))
             (qmult (projT1 c k) (projT1 d k))))
         (qplus
           (qmult (qabs (projT1 a k))
             (qabs (qminus (projT1 b k) (projT1 d k))))
           (qmult (qabs (projT1 d k))
             (qabs (qminus (projT1 a k) (projT1 c k)))))
         eps hbdT
         (qltT_leT'_ltT
           (qplus
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k)))))
           (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
           eps
           (qltT_plus_ltT
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k))))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T' ht2T')
           (qeq_leT'
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             eps)))))

  (** val real_eq_abs_compat : real -> real -> real_eq -> real_eq **)

  let real_eq_abs_compat a b hab eps heps =
    let s = hab eps heps in
    let ExistT (x, _) = s in
    ExistT (x, (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_abs a) k) (projT1 (real_abs b) k))) eps))

  (** val real_lt_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_lt -> real_lt **)

  let real_lt_compat x1 x2 y1 y2 hx hy hlt =
    real_lt_eq_lt x2 y1 y2 (real_eq_lt_lt x2 x1 y1 (real_eq_sym x1 x2 hx) hlt)
      hy

  (** val real_le_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_le -> real_le **)

  let real_le_compat x1 x2 y1 y2 hx hy = function
  | Inl r -> Inl (real_lt_compat x1 x2 y1 y2 hx hy r)
  | Inr r ->
    Inr
      (real_eq_trans x2 y1 y2
        (real_eq_trans x2 x1 y1 (real_eq_sym x1 x2 hx) r) hy)

  (** val real_le_id_l :
      real -> real -> real -> real_eq -> real_le -> real_le **)

  let real_le_id_l a b c hab hbc =
    real_le_compat b a c c (real_eq_sym a b hab) (real_eq_refl c) hbc

  (** val real_le_id_r :
      real -> real -> real -> real_eq -> real_le -> real_le **)

  let real_le_id_r a b c hbc hab =
    real_le_compat a a b c (real_eq_refl a) hbc hab
 end

(** val exp_trunc_arch_seq :
    (nat -> q) -> (nat -> q) -> q -> q -> qleT' -> (nat -> qleT') -> (nat ->
    qleT') -> qltT -> (nat, nat -> __ -> qltT) sigT **)

let exp_trunc_arch_seq u v b eps hB _ _ _ =
  let s = exp_series_arch b hB in
  let ExistT (x, _) = s in
  let s0 = q_arch_geom b in
  let ExistT (x0, _) = s0 in
  let s1 =
    arch_decay
      (qmult (qdiv (q_pow b x0) (q_fact x0))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x))
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qmult (qdiv (q_pow b x0) (q_fact x0))
          (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
            XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x)))
  in
  let ExistT (x1, _) = s1 in
  ExistT ((add x0 (S x1)), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (sum_upto (S (mul (S (S O)) n)) (fun j ->
          sum_upto (S (sub (mul (S (S O)) n) j)) (fun i ->
            qmult (qdiv (q_pow (u n) j) (q_fact j))
              (qdiv (q_pow (v n) i) (q_fact i)))))
        (sum_upto (S n) (fun j ->
          sum_upto (S n) (fun i ->
            qmult (qdiv (q_pow (u n) j) (q_fact j))
              (qdiv (q_pow (v n) i) (q_fact i)))))))
    eps))

(** val cauchy_real_exp_plus : real -> real -> real_eq **)

let cauchy_real_exp_plus x y eps heps =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, a) = s in
  let Pair (q0, q1) = a in
  let s0 = real_norm_bounded (ExistT (x1, c0)) in
  let ExistT (x3, a0) = s0 in
  let Pair (q2, q3) = a0 in
  let m = qplus x2 x3 in
  let hMposT = qltT_plus_pos_r x2 x3 q0 q2 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let huMT = fun n ->
    qleT'_trans (qabs (x0 n)) x2 (qplus x2 x3) (q1 n)
      (qleT'_plus_nonneg_rT x2 x3 (qltT_leT' { qnum = Z0; qden = XH } x3 q2))
  in
  let hvMT = fun n ->
    qleT'_trans (qabs (x1 n)) x3 (qplus x2 x3) (q3 n)
      (qleT'_trans x3 (qplus x3 x2) (qplus x2 x3)
        (qleT'_plus_nonneg_rT x3 x2
          (qltT_leT' { qnum = Z0; qden = XH } x2 q0))
        (qle_to_QleT' (qplus x3 x2) (qplus x2 x3)))
  in
  let heps3T =
    qltT_div_pos eps { qnum = (Zpos (XI XH)); qden = XH } heps qltT_0_3
  in
  let s1 =
    exp_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT heps3T
  in
  let ExistT (x4, _) = s1 in
  let s2 =
    exp_trunc_arch_seq x0 x1 m (qdiv eps { qnum = (Zpos (XI XH)); qden = XH })
      hMnonnegT huMT hvMT heps3T
  in
  let ExistT (x5, _) = s2 in
  ExistT ((Nat.max x4 x5), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1
          (cauchy_real_exp (real_plus (ExistT (x0, c)) (ExistT (x1, c0)))) n)
        (projT1
          (real_mult (cauchy_real_exp (ExistT (x0, c)))
            (cauchy_real_exp (ExistT (x1, c0))))
          n)))
    eps))

(** val cauchy_real_exp_gt_one : real -> real_lt -> real_lt **)

let cauchy_real_exp_gt_one t = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT ((Nat.max x0 (S O)), (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (cauchy_real_exp t) n) (projT1 real_one n))))))))

(** val real_lt_opp_plus : real -> real -> real_lt -> real_lt **)

let real_lt_opp_plus x y = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0
    (qminus (projT1 (real_plus y (real_opp x)) n) (projT1 real_zero n))))))))

(** val real_mult_pos_compat :
    real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_pos_compat a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val cauchy_real_exp_minus_one_pos : real -> real_lt -> real_lt **)

let cauchy_real_exp_minus_one_pos t ht =
  let r = cauchy_real_exp_gt_one t ht in
  let ExistT (x, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x
    (qminus (projT1 (real_plus (cauchy_real_exp t) (real_opp real_one)) n)
      (projT1 real_zero n))))))))

(** val real_lt_zero_minus : real -> real -> real_lt -> real_lt **)

let real_lt_zero_minus x y = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0 (qminus (projT1 y n) (projT1 x n))))))))

(** val cauchy_real_exp_wd : real -> real -> real_eq -> real_eq **)

let cauchy_real_exp_wd a b hab eps heps =
  let s = real_norm_bounded a in
  let ExistT (x, a0) = s in
  let Pair (q0, _) = a0 in
  let s0 = real_norm_bounded b in
  let ExistT (x0, a1) = s0 in
  let Pair (q1, _) = a1 in
  let m = qplus x x0 in
  let hMposT = qltT_plus_pos_r x x0 q0 q1 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let s1 = exp_series_arch m hMnonnegT in
  let ExistT (x1, a2) = s1 in
  let Pair (q2, _) = a2 in
  let hCposT =
    qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } x1
      qltT_0_1 q2
  in
  let hepsC =
    qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x1) heps
      (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x1 qltT_0_2
        hCposT)
  in
  let s2 =
    hab (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x1)) hepsC
  in
  let ExistT (x2, _) = s2 in
  let heps2T =
    qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2
  in
  let s3 =
    exp_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hMnonnegT heps2T
  in
  let ExistT (x3, _) = s3 in
  ExistT ((Nat.max x2 x3), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_exp a) n) (projT1 (cauchy_real_exp b) n)))
    eps))

(** val real_mult_minus_factor : real -> real -> real_eq **)

let real_mult_minus_factor a b =
  real_eq_of_zero_diff (real_plus (real_mult a b) (real_opp a))
    (real_mult a (real_plus b (real_opp real_one)))

(** val cauchy_real_exp_mono : real -> real -> real_lt -> real_lt **)

let cauchy_real_exp_mono x y hxy =
  let hdiff = real_lt_opp_plus x y hxy in
  let hminus = cauchy_real_exp_minus_one_pos (real_plus y (real_opp x)) hdiff
  in
  let hprod =
    real_mult_pos_compat (cauchy_real_exp x)
      (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
        (real_opp real_one))
      (cauchy_real_exp_pos x) hminus
  in
  let hxyeq = real_eq_of_zero_diff y (real_plus x (real_plus y (real_opp x)))
  in
  let hewd =
    cauchy_real_exp_wd y (real_plus x (real_plus y (real_opp x))) hxyeq
  in
  let heplus = cauchy_real_exp_plus x (real_plus y (real_opp x)) in
  let hmain =
    real_eq_trans (cauchy_real_exp y)
      (cauchy_real_exp (real_plus x (real_plus y (real_opp x))))
      (real_mult (cauchy_real_exp x)
        (cauchy_real_exp (real_plus y (real_opp x))))
      hewd heplus
  in
  let hdiffeq =
    real_eq_trans
      (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
      (real_plus
        (real_mult (cauchy_real_exp x)
          (cauchy_real_exp (real_plus y (real_opp x))))
        (real_opp (cauchy_real_exp x)))
      (real_mult (cauchy_real_exp x)
        (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
          (real_opp real_one)))
      (RealSetoid.real_eq_plus_compat (cauchy_real_exp y)
        (real_opp (cauchy_real_exp x))
        (real_mult (cauchy_real_exp x)
          (cauchy_real_exp (real_plus y (real_opp x))))
        (real_opp (cauchy_real_exp x)) hmain
        (real_eq_refl (real_opp (cauchy_real_exp x))))
      (real_mult_minus_factor (cauchy_real_exp x)
        (cauchy_real_exp (real_plus y (real_opp x))))
  in
  let hposdiff =
    real_lt_eq_lt real_zero
      (real_mult (cauchy_real_exp x)
        (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
          (real_opp real_one)))
      (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x))) hprod
      (real_eq_sym
        (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
        (real_mult (cauchy_real_exp x)
          (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
            (real_opp real_one)))
        hdiffeq)
  in
  let ExistT (x0, a) = hposdiff in
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0
    (qminus (projT1 (cauchy_real_exp y) n) (projT1 (cauchy_real_exp x) n))))))))

(** val real_arch : real -> (nat, (__, real_lt) and0) sigT **)

let real_arch b =
  let s = real_norm_bounded b in
  let ExistT (x, _) = s in
  let s0 = q_arch_geom x in
  let ExistT (x0, _) = s0 in
  ExistT ((add x0 (S (S O))), (Pair (__, (ExistT
  ((qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
     { qnum = (Zpos (XO XH)); qden = XH }),
  (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
       { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT (O, (fun k _ ->
  qlt_to_QltT
    (qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
      { qnum = (Zpos (XO XH)); qden = XH })
    (qminus
      (projT1 (real_const { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH })
        k)
      (projT1 b k))))))))))))

(** val cauchy_real_exp_gt_const : nat -> real_lt **)

let cauchy_real_exp_gt_const n =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT ((S O), (fun n0 _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus
        (projT1
          (cauchy_real_exp (real_const { qnum = (Z.of_nat n); qden = XH }))
          n0)
        (projT1 (real_const { qnum = (Z.of_nat n); qden = XH }) n0))))))))

(** val real_abs_diff_le_lift : real -> real -> q -> q -> nat -> real_lt **)

let real_abs_diff_le_lift a b m _UU03b3_ _ =
  let hg4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let s =
    projT2 a (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH }) hg4
  in
  let ExistT (x, _) = s in
  let s0 =
    projT2 b (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH }) hg4
  in
  let ExistT (x0, _) = s0 in
  ExistT ((qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((Nat.max x x0), (fun n _ ->
  qlt_to_QltT (qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 (real_const (qplus m _UU03b3_)) n)
      (projT1 (real_abs (real_plus a (real_opp b))) n))))))))

(** val real_inv_unique :
    real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_inv_unique a b c hab hac =
  real_eq_trans b (real_mult b real_one) c
    (real_eq_sym (real_mult b real_one) b (real_mult_one b))
    (real_eq_trans (real_mult b real_one) (real_mult b (real_mult a c)) c
      (RealSetoid.real_eq_mult_compat b real_one b (real_mult a c)
        (real_eq_refl b) (real_eq_sym (real_mult a c) real_one hac))
      (real_eq_trans (real_mult b (real_mult a c))
        (real_mult (real_mult b a) c) c (real_mult_assoc b a c)
        (real_eq_trans (real_mult (real_mult b a) c)
          (real_mult (real_mult a b) c) c
          (RealSetoid.real_eq_mult_compat (real_mult b a) c (real_mult a b) c
            (real_mult_comm b a) (real_eq_refl c))
          (real_eq_trans (real_mult (real_mult a b) c) (real_mult real_one c)
            c
            (RealSetoid.real_eq_mult_compat (real_mult a b) c real_one c hab
              (real_eq_refl c))
            (real_eq_trans (real_mult real_one c) (real_mult c real_one) c
              (real_mult_comm real_one c) (real_mult_one c))))))

(** val exp_neg_recip : real -> real_lt -> real_eq **)

let exp_neg_recip x hx =
  real_inv_unique (cauchy_real_exp x) (cauchy_real_exp (real_opp x))
    (real_inv_pos (cauchy_real_exp x) hx)
    (real_eq_trans
      (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_opp x)))
      (cauchy_real_exp (real_plus x (real_opp x))) real_one
      (real_eq_sym (cauchy_real_exp (real_plus x (real_opp x)))
        (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_opp x)))
        (cauchy_real_exp_plus x (real_opp x)))
      (real_eq_trans (cauchy_real_exp (real_plus x (real_opp x)))
        (cauchy_real_exp real_zero) real_one
        (cauchy_real_exp_wd (real_plus x (real_opp x)) real_zero
          (real_eq_of_zero_diff (real_plus x (real_opp x)) real_zero))
        cauchy_real_exp_zero))
    (real_inv_pos_correct (cauchy_real_exp x) hx)

(** val real_const_pos : q -> qltT -> real_lt **)

let real_const_pos c _ =
  ExistT ((qdiv c { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv c { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv c { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const c) n) (projT1 real_zero n))))))))

(** val real_inv_lt_contra :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_inv_lt_contra a b ha hb hab =
  let ExistT (x, a0) = ha in
  let Pair (q0, s) = a0 in
  let ExistT (x0, q1) = s in
  let ExistT (x1, a1) = hb in
  let Pair (q2, s0) = a1 in
  let ExistT (x2, q3) = s0 in
  let ExistT (x3, a2) = hab in
  let Pair (_, s1) = a2 in
  let ExistT (x4, _) = s1 in
  let s2 = real_norm_bounded a in
  let ExistT (x5, _) = s2 in
  let s3 = real_norm_bounded b in
  let ExistT (x6, _) = s3 in
  ExistT ((qdiv x3 (qmult x5 x6)), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x3 (qmult x5 x6))), (ExistT
  ((Nat.max (Nat.max x0 x2) x4), (fun n _ ->
  qlt_to_QltT (qdiv x3 (qmult x5 x6))
    (qminus
      (projT1 (real_inv_pos a (ExistT (x, (Pair (q0, (ExistT (x0, q1))))))) n)
      (projT1 (real_inv_pos b (ExistT (x1, (Pair (q2, (ExistT (x2, q3)))))))
        n))))))))

(** val q_eps16_posT : q -> qltT **)

let q_eps16_posT eps =
  qlt_to_QltT { qnum = Z0; qden = XH }
    (qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH })

(** val log_testA_eps : real -> q -> q -> q -> bool **)

let log_testA_eps y a b eps =
  let m = qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH } in
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (exp_partial_cauchy m d4) in
  let k2 = projT1 (projT2 y d4 (q_eps16_posT eps)) in
  qlt_bool
    (qplus (exp_partial k1 m) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (projT1 y k2)

(** val log_testB_eps : real -> q -> q -> q -> bool **)

let log_testB_eps y a b eps =
  let m = qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH } in
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (exp_partial_cauchy m d4) in
  let k2 = projT1 (projT2 y d4 (q_eps16_posT eps)) in
  qlt_bool
    (qplus (projT1 y k2) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (exp_partial k1 m)

(** val log_m_eps : q -> q -> q **)

let log_m_eps a b =
  qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH }

(** val log_d4_eps : q -> q **)

let log_d4_eps eps =
  qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH }

(** val log_K1_eps : q -> q -> q -> nat **)

let log_K1_eps a b eps =
  projT1 (exp_partial_cauchy (log_m_eps a b) (log_d4_eps eps))

(** val log_K2_eps : real -> q -> q -> q -> nat **)

let log_K2_eps y _ _ eps =
  projT1 (projT2 y (log_d4_eps eps) (q_eps16_posT eps))

(** val log_q_eps : q -> q -> q -> q **)

let log_q_eps a b eps =
  exp_partial (log_K1_eps a b eps) (log_m_eps a b)

(** val log_r_eps : real -> q -> q -> q -> q **)

let log_r_eps y a b eps =
  projT1 y (log_K2_eps y a b eps)

(** val log_testA_eps_true_lt : real -> q -> q -> q -> real_lt **)

let log_testA_eps_true_lt y a b eps =
  let d4 = log_d4_eps eps in
  let k1 = log_K1_eps a b eps in
  let k2 = log_K2_eps y a b eps in
  let q0 = log_q_eps a b eps in
  let r = log_r_eps y a b eps in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT ((Nat.max k1 k2), (fun n _ ->
  qlt_to_QltT
    (qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 y n)
      (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n))))))))

(** val log_testB_eps_true_gt : real -> q -> q -> q -> real_lt **)

let log_testB_eps_true_gt y a b eps =
  let d4 = log_d4_eps eps in
  let k1 = log_K1_eps a b eps in
  let k2 = log_K2_eps y a b eps in
  let q0 = log_q_eps a b eps in
  let r = log_r_eps y a b eps in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT ((Nat.max k1 k2), (fun n _ ->
  qlt_to_QltT
    (qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n)
      (projT1 y n))))))))

(** val log_scan :
    real -> q -> q -> q -> nat -> (((q, q) prod, qltT) sigT, bool) prod **)

let rec log_scan y a b eps = function
| O -> Pair ((ExistT ((Pair (a, b)), (qlt_to_QltT a b))), True)
| S n' ->
  let m = log_m_eps a b in
  (match log_testA_eps y a b eps with
   | True -> log_scan y m b eps n'
   | False ->
     (match log_testB_eps y a b eps with
      | True -> log_scan y a m eps n'
      | False -> Pair ((ExistT ((Pair (a, b)), (qlt_to_QltT a b))), False)))

(** val log_scan_spec :
    real -> q -> q -> q -> nat -> real_lt -> real_lt -> ((bool id, (real_lt,
    (real_lt, qeqT) and0) and0) and0, (bool id, nat -> __ -> qleT') and0) or0 **)

let rec log_scan_spec y a b eps n hla hrb =
  match n with
  | O ->
    Inl (Pair (Id_refl, (Pair (hla, (Pair (hrb,
      (qeq_imp_qeqT (qminus b a)
        (qmult (qminus b a) { qnum = (Zpos XH); qden = XH }))))))))
  | S n0 ->
    let b0 = log_testA_eps y a b eps in
    (match b0 with
     | True ->
       let hmb = log_testA_eps_true_lt y a b eps in
       let hIH = log_scan_spec y (log_m_eps a b) b eps n0 hmb hrb in
       (match hIH with
        | Inl a0 ->
          Inl
            (let Pair (i, a1) = a0 in
             let Pair (r, a2) = a1 in
             let Pair (r0, _) = a2 in
             Pair (i, (Pair (r, (Pair (r0,
             (qeq_imp_qeqT
               (qminus
                 (snd (projT1 (fst (log_scan y (log_m_eps a b) b eps n0))))
                 (fst (projT1 (fst (log_scan y (log_m_eps a b) b eps n0)))))
               (qmult (qminus b a)
                 (q_pow
                   (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                     XH)); qden = XH })
                   (S n0))))))))))
        | Inr a0 -> Inr a0)
     | False ->
       let b1 = log_testB_eps y a b eps in
       (match b1 with
        | True ->
          let ham = log_testB_eps_true_gt y a b eps in
          let hIH = log_scan_spec y a (log_m_eps a b) eps n0 hla ham in
          (match hIH with
           | Inl a0 ->
             Inl
               (let Pair (i, a1) = a0 in
                let Pair (r, a2) = a1 in
                let Pair (r0, _) = a2 in
                Pair (i, (Pair (r, (Pair (r0,
                (qeq_imp_qeqT
                  (qminus
                    (snd (projT1 (fst (log_scan y a (log_m_eps a b) eps n0))))
                    (fst (projT1 (fst (log_scan y a (log_m_eps a b) eps n0)))))
                  (qmult (qminus b a)
                    (q_pow
                      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                        XH)); qden = XH })
                      (S n0))))))))))
           | Inr a0 -> Inr a0)
        | False ->
          Inr (Pair (Id_refl, (fun k _ ->
            qle_to_QleT'
              (qabs
                (qminus
                  (projT1
                    (cauchy_real_exp
                      (real_const
                        (log_m_eps
                          (fst
                            (projT1
                              (fst (Pair ((ExistT ((Pair (a, b)),
                                (qlt_to_QltT a b))), False)))))
                          (snd
                            (projT1
                              (fst (Pair ((ExistT ((Pair (a, b)),
                                (qlt_to_QltT a b))), False))))))))
                    k)
                  (projT1 y k)))
              (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
                (log_d4_eps eps)))))))

(** val exp_lower_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT **)

let exp_lower_q y = function
| ExistT (x, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  let h2e =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)
  in
  let hcst = real_const_pos (qdiv { qnum = (Zpos (XO XH)); qden = XH } x) h2e
  in
  let s0 =
    real_arch (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
  in
  let ExistT (x1, a0) = s0 in
  let Pair (_, r) = a0 in
  let hexpN =
    real_lt_trans (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
      (real_const { qnum = (Z.of_nat x1); qden = XH })
      (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH })) r
      (cauchy_real_exp_gt_const x1)
  in
  let hexpNpos =
    cauchy_real_exp_pos (real_const { qnum = (Z.of_nat x1); qden = XH })
  in
  ExistT (x1, (Pair (__,
  (real_eq_lt_lt
    (cauchy_real_exp (real_const (qopp { qnum = (Z.of_nat x1); qden = XH })))
    (cauchy_real_exp
      (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
    y
    (cauchy_real_exp_wd
      (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
      (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH }))
      (real_eq_of_zero_diff
        (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
        (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH }))))
    (real_lt_trans
      (cauchy_real_exp
        (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
      (real_inv_pos (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
        hcst)
      y
      (real_eq_lt_lt
        (cauchy_real_exp
          (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
        (real_inv_pos
          (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH }))
          hexpNpos)
        (real_inv_pos
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
        (exp_neg_recip (real_const { qnum = (Z.of_nat x1); qden = XH })
          hexpNpos)
        (real_inv_lt_contra
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
          (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH }))
          hcst hexpNpos hexpN))
      (real_eq_lt_lt
        (real_inv_pos
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
        (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) y
        (real_inv_unique
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
          (real_inv_pos
            (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
          (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH }))
          (real_inv_pos_correct
            (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
          (real_eq_of_zero_diff
            (real_mult
              (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
              (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })))
            real_one))
        (ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
        ((qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
        (ExistT (x0, (fun n _ ->
        qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
          (qminus (projT1 y n)
            (projT1 (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH }))
              n)))))))))))))))

(** val exp_upper_q : real -> real_lt -> (nat, (__, real_lt) and0) sigT **)

let exp_upper_q y _ =
  let s = real_arch y in
  let ExistT (x, a) = s in
  let Pair (_, r) = a in
  ExistT (x, (Pair (__,
  (real_lt_trans y (real_const { qnum = (Z.of_nat x); qden = XH })
    (cauchy_real_exp (real_const { qnum = (Z.of_nat x); qden = XH })) r
    (cauchy_real_exp_gt_const x)))))

(** val log_lower : real -> real_lt -> q **)

let log_lower y hy =
  qopp { qnum = (Z.of_nat (projT1 (exp_lower_q y hy))); qden = XH }

(** val log_upper : real -> real_lt -> q **)

let log_upper y hy =
  { qnum = (Z.of_nat (projT1 (exp_upper_q y hy))); qden = XH }

(** val q_pow_arch : q -> q -> (nat, __) sigT **)

let q_pow_arch d eps =
  let s =
    arch_decay d eps (qle_to_QleT' { qnum = Z0; qden = XH } d)
      (qlt_to_QltT { qnum = Z0; qden = XH } eps)
  in
  let ExistT (x, _) = s in ExistT ((S x), __)

(** val real_const_lt : q -> q -> real_lt **)

let real_const_lt c d =
  ExistT ((qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const d) n) (projT1 (real_const c) n))))))))

(** val real_lt_pt_lt : real -> real -> real_lt -> (nat, __) sigT **)

let real_lt_pt_lt _ _ = function
| ExistT (_, a) ->
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val exp_const_lt : q -> q -> real_lt **)

let exp_const_lt a b =
  cauchy_real_exp_mono (real_const a) (real_const b) (real_const_lt a b)

(** val approx_span_pt :
    real -> q -> q -> q -> q -> real_lt -> real_lt -> (nat -> qleT') -> (nat,
    __) sigT **)

let approx_span_pt y a b _ _ hla hrb _ =
  let m = log_m_eps a b in
  let heam = exp_const_lt a (log_m_eps a b) in
  let hemb = exp_const_lt (log_m_eps a b) b in
  let s = real_lt_pt_lt (cauchy_real_exp (real_const a)) y hla in
  let ExistT (x, _) = s in
  let s0 = real_lt_pt_lt y (cauchy_real_exp (real_const b)) hrb in
  let ExistT (x0, _) = s0 in
  let s1 =
    real_lt_pt_lt (cauchy_real_exp (real_const a))
      (cauchy_real_exp (real_const m)) heam
  in
  let ExistT (x1, _) = s1 in
  let s2 =
    real_lt_pt_lt (cauchy_real_exp (real_const m))
      (cauchy_real_exp (real_const b)) hemb
  in
  let ExistT (x2, _) = s2 in
  ExistT ((Nat.max (Nat.max x x0) (Nat.max x1 x2)), __)

(** val real_abs_lift : q -> real -> q -> q -> nat -> real_lt **)

let real_abs_lift m y m0 _UU03b3_ n0 =
  real_abs_diff_le_lift (cauchy_real_exp (real_const m)) y m0 _UU03b3_ n0

(** val approx_def_test : real -> q -> q -> nat -> real_lt **)

let approx_def_test y mN eps n0 =
  let hlift =
    real_abs_lift mN y
      (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
      (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) n0
  in
  real_lt_trans
    (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
    (real_const
      (qplus
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH })))
    (real_const eps) hlift
    (real_const_lt
      (qplus
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }))
      eps)

(** val approx_root :
    real -> real_lt -> q -> (q, (qltT, (qltT, real_lt) and0) and0) sigT **)

let approx_root y hy eps =
  let s = exp_lower_q y hy in
  let ExistT (x, a) = s in
  let Pair (_, r) = a in
  let s0 = exp_upper_q y hy in
  let ExistT (x0, a0) = s0 in
  let Pair (_, r0) = a0 in
  let a1 = qopp { qnum = (Z.of_nat x); qden = XH } in
  let b0 = { qnum = (Z.of_nat x0); qden = XH } in
  let b = qplus (qabs a1) (qabs b0) in
  let s1 = exp_series_arch b (qle_to_QleT' { qnum = Z0; qden = XH } b) in
  let ExistT (x1, a2) = s1 in
  let Pair (_, q0) = a2 in
  let d = qmult (qminus b0 a1) x1 in
  let s2 = q_pow_arch d eps in
  let ExistT (x2, _) = s2 in
  let o = log_scan_spec y a1 b0 eps x2 r r0 in
  (match o with
   | Inl a3 ->
     let Pair (_, a4) = a3 in
     let Pair (r1, a5) = a4 in
     let Pair (r2, _) = a5 in
     let abN = projT1 (fst (log_scan y a1 b0 eps x2)) in
     let aN = fst abN in
     let bN = snd abN in
     let mN = log_m_eps aN bN in
     let s3 = approx_span_pt y aN bN b x1 r1 r2 q0 in
     let ExistT (x3, _) = s3 in
     ExistT (mN, (Pair
     ((qlt_to_QltT (qopp { qnum = (Z.of_nat x); qden = XH }) mN), (Pair
     ((qlt_to_QltT mN { qnum = (Z.of_nat x0); qden = XH }),
     (let hlift =
        real_abs_lift mN y (qmult (qminus bN aN) x1)
          (qdiv
            (qminus eps
              (qmult d
                (q_pow
                  (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                    XH)); qden = XH })
                  x2)))
            { qnum = (Zpos (XO XH)); qden = XH })
          x3
      in
      real_lt_trans
        (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
        (real_const
          (qplus (qmult (qminus bN aN) x1)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH })))
        (real_const eps) hlift
        (real_const_lt
          (qplus (qmult (qminus bN aN) x1)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH }))
          eps)))))))
   | Inr _ ->
     let abN = projT1 (fst (log_scan y a1 b0 eps x2)) in
     let mN = log_m_eps (fst abN) (snd abN) in
     let n0 =
       Nat.max (log_K1_eps (fst abN) (snd abN) eps)
         (log_K2_eps y (fst abN) (snd abN) eps)
     in
     ExistT (mN, (Pair
     ((qlt_to_QltT (qopp { qnum = (Z.of_nat x); qden = XH }) mN), (Pair
     ((qlt_to_QltT mN { qnum = (Z.of_nat x0); qden = XH }),
     (approx_def_test y mN eps n0)))))))

(** val log_eps : nat -> q **)

let log_eps n =
  q_pow
    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })
    (S n)

(** val log_seq : real -> real_lt -> nat -> q **)

let log_seq y hy n =
  projT1 (approx_root y hy (log_eps n))

(** val approx_root_pt_bound : real -> real_lt -> nat -> (nat, __) sigT **)

let approx_root_pt_bound y hy n =
  let s = approx_root y hy (log_eps n) in
  let ExistT (x, a) = s in
  let Pair (_, a0) = a in
  let Pair (_, r) = a0 in
  let s0 =
    real_lt_pt_lt
      (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y)))
      (real_const (log_eps n)) r
  in
  let ExistT (x0, _) = s0 in ExistT (x0, __)

(** val exp_pos_shape :
    real -> (q, (qltT, (nat, nat -> __ -> qltT) sigT) and0) sigT **)

let exp_pos_shape x =
  let r = cauchy_real_exp_pos x in
  let ExistT (x0, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x1, q1) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ -> q1 n (natLe_lift x1 n)))))))

(** val log_seq_cauchy : real -> real_lt -> cauchy **)

let log_seq_cauchy y hy eps _ =
  let a0 = log_lower y hy in
  let s = exp_pos_shape (real_const a0) in
  let ExistT (x, _) = s in
  let delta =
    qdiv (qmult eps x) { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
  in
  let s0 = q_pow_arch { qnum = (Zpos XH); qden = XH } delta in
  let ExistT (x0, _) = s0 in
  ExistT ((S x0), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (log_seq y hy m) (log_seq y hy n))) eps))

(** val cw_log : real -> real_lt -> real **)

let cw_log y hy =
  ExistT ((log_seq y hy), (log_seq_cauchy y hy))

(** val exp_series_arch_shape :
    q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT **)

let exp_series_arch_shape =
  exp_series_arch

(** val cw_log_exp_right : real -> real_lt -> real_eq **)

let cw_log_exp_right y hy gamma _ =
  let s =
    exp_series_arch_shape
      (qplus (qabs (log_lower y hy)) (qabs (log_upper y hy)))
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qplus (qabs (log_lower y hy)) (qabs (log_upper y hy))))
  in
  let ExistT (x, _) = s in
  let hcau =
    log_seq_cauchy y hy
      (qdiv gamma
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
          (qplus x { qnum = (Zpos XH); qden = XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv gamma
          (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
            (qplus x { qnum = (Zpos XH); qden = XH }))))
  in
  let ExistT (x0, _) = hcau in
  let s0 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv gamma { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let ExistT (x1, _) = s0 in
  let n0 = Nat.max x0 (S x1) in
  let happrox = approx_root_pt_bound y hy n0 in
  let ExistT (x2, _) = happrox in
  ExistT ((Nat.max n0 x2), (fun k _ ->
  qlt_to_QltT
    (qabs (qminus (projT1 (cauchy_real_exp (cw_log y hy)) k) (projT1 y k)))
    gamma))

(** val real_lt_not_eq : real -> real -> real_lt -> real_eq not **)

let real_lt_not_eq _ _ _ _ =
  assert false (* absurd case *)

(** val real_weak_trich :
    real -> real -> real_lt not -> real_lt not -> real_eq **)

let real_weak_trich x y _ _ eps _ =
  let heps3 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH })
  in
  let s = projT2 x (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) heps3 in
  let ExistT (x0, _) = s in
  let s0 = projT2 y (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) heps3 in
  let ExistT (x1, _) = s0 in
  let n = Nat.max x0 x1 in
  let hmain = fun n0 ->
    let s1 = qlt_le_dec (qabs (qminus (projT1 x n0) (projT1 y n0))) eps in
    (match s1 with
     | Left -> qlt_to_QltT (qabs (qminus (projT1 x n0) (projT1 y n0))) eps
     | Right -> assert false (* absurd case *))
  in
  ExistT (n, (fun n0 _ -> hmain n0))

(** val log_inv_one_thm : real_lt -> real_eq **)

let log_inv_one_thm h =
  let u = cw_log real_one h in
  let hright = cw_log_exp_right real_one h in
  real_weak_trich u real_zero (fun hult ->
    real_lt_not_eq (cauchy_real_exp u) (cauchy_real_exp real_zero)
      (cauchy_real_exp_mono u real_zero hult)
      (real_eq_trans (cauchy_real_exp u) real_one (cauchy_real_exp real_zero)
        hright
        (real_eq_sym (cauchy_real_exp real_zero) real_one
          cauchy_real_exp_zero)))
    (fun h0lt ->
    real_lt_not_eq (cauchy_real_exp real_zero) (cauchy_real_exp u)
      (cauchy_real_exp_mono real_zero u h0lt)
      (real_eq_trans (cauchy_real_exp real_zero) real_one (cauchy_real_exp u)
        cauchy_real_exp_zero
        (real_eq_sym (cauchy_real_exp u) real_one hright)))

(** val log_inv_mult_thm :
    real -> real -> real_lt -> real_lt -> real_lt -> real_eq **)

let log_inv_mult_thm a b ha hb hab =
  let l = cw_log (real_mult a b) hab in
  let r = real_plus (cw_log a ha) (cw_log b hb) in
  let hL = cw_log_exp_right (real_mult a b) hab in
  let hplus = cauchy_real_exp_plus (cw_log a ha) (cw_log b hb) in
  let hRa = cw_log_exp_right a ha in
  let hRb = cw_log_exp_right b hb in
  let hR =
    real_eq_trans (cauchy_real_exp r)
      (real_mult (cauchy_real_exp (cw_log a ha))
        (cauchy_real_exp (cw_log b hb)))
      (real_mult a b) hplus
      (RealSetoid.real_eq_mult_compat (cauchy_real_exp (cw_log a ha))
        (cauchy_real_exp (cw_log b hb)) a b hRa hRb)
  in
  real_weak_trich l r (fun hLlt ->
    real_lt_not_eq (cauchy_real_exp l) (cauchy_real_exp r)
      (cauchy_real_exp_mono l r hLlt)
      (real_eq_trans (cauchy_real_exp l) (real_mult a b) (cauchy_real_exp r)
        hL (real_eq_sym (cauchy_real_exp r) (real_mult a b) hR)))
    (fun hRlt ->
    real_lt_not_eq (cauchy_real_exp r) (cauchy_real_exp l)
      (cauchy_real_exp_mono r l hRlt)
      (real_eq_trans (cauchy_real_exp r) (real_mult a b) (cauchy_real_exp l)
        hR (real_eq_sym (cauchy_real_exp l) (real_mult a b) hL)))

(** val real_mult_lt_compat :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_lt_compat a b c hab hc =
  let ExistT (x, a0) = hab in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hc in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult b c) n) (projT1 (real_mult a c) n))))))))

(** val real_mult_lt_compat_l :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_lt_compat_l a b c hab hc =
  real_eq_lt_lt (real_mult c a) (real_mult a c) (real_mult c b)
    (real_mult_comm c a)
    (real_lt_eq_lt (real_mult a c) (real_mult b c) (real_mult c b)
      (real_mult_lt_compat a b c hab hc) (real_mult_comm b c))

(** val real_inv_pos_lt_contra :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_inv_pos_lt_contra a b ha hb hab =
  real_eq_lt_lt (real_inv_pos b hb)
    (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
    (real_inv_pos a ha)
    (real_eq_trans (real_inv_pos b hb)
      (real_mult real_one (real_inv_pos b hb))
      (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
      (real_eq_sym (real_mult real_one (real_inv_pos b hb))
        (real_inv_pos b hb)
        (real_eq_trans (real_mult real_one (real_inv_pos b hb))
          (real_mult (real_inv_pos b hb) real_one) (real_inv_pos b hb)
          (real_mult_comm real_one (real_inv_pos b hb))
          (real_mult_one (real_inv_pos b hb))))
      (RealSetoid.real_eq_mult_compat real_one (real_inv_pos b hb)
        (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb)
        (real_eq_sym (real_mult (real_inv_pos a ha) a) real_one
          (real_eq_trans (real_mult (real_inv_pos a ha) a)
            (real_mult a (real_inv_pos a ha)) real_one
            (real_mult_comm (real_inv_pos a ha) a)
            (real_inv_pos_correct a ha)))
        (real_eq_refl (real_inv_pos b hb))))
    (real_lt_eq_lt
      (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
      (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
      (real_inv_pos a ha)
      (real_mult_lt_compat (real_mult (real_inv_pos a ha) a)
        (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb)
        (real_mult_lt_compat_l a b (real_inv_pos a ha) hab
          (real_inv_pos_pos a ha))
        (real_inv_pos_pos b hb))
      (real_eq_trans
        (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
        (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
        (real_inv_pos a ha)
        (real_eq_sym
          (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
          (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
          (real_mult_assoc (real_inv_pos a ha) b (real_inv_pos b hb)))
        (real_eq_trans
          (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
          (real_mult (real_inv_pos a ha) real_one) (real_inv_pos a ha)
          (RealSetoid.real_eq_mult_compat (real_inv_pos a ha)
            (real_mult b (real_inv_pos b hb)) (real_inv_pos a ha) real_one
            (real_eq_refl (real_inv_pos a ha)) (real_inv_pos_correct b hb))
          (real_mult_one (real_inv_pos a ha)))))

(** val real_lt_plus_translate :
    real -> real -> real -> real_lt -> real_lt **)

let real_lt_plus_translate b c d = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (real_plus b d) n) (projT1 (real_plus b c) n))))))))

(** val real_lt_plus_compat_le_lt :
    real -> real -> real -> real -> real_le -> real_lt -> real_lt **)

let real_lt_plus_compat_le_lt a b c d hab hcd =
  match hab with
  | Inl r -> real_lt_plus_compat a b c d r hcd
  | Inr r ->
    real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)
      (RealSetoid.real_eq_plus_compat a c b c r (real_eq_refl c))
      (real_lt_plus_translate b c d hcd)

(** val real_lt_plus_compat_lt_le :
    real -> real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_plus_compat_lt_le a b c d hab = function
| Inl r -> real_lt_plus_compat a b c d hab r
| Inr r ->
  real_eq_lt_lt (real_plus a c) (real_plus a d) (real_plus b d)
    (RealSetoid.real_eq_plus_compat a c a d (real_eq_refl a) r)
    (real_eq_lt_lt (real_plus a d) (real_plus d a) (real_plus b d)
      (real_plus_comm a d)
      (real_lt_eq_lt (real_plus d a) (real_plus d b) (real_plus b d)
        (real_lt_plus_translate d a b hab) (real_plus_comm d b)))

(** val real_log_lt_mono :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_log_lt_mono a b ha hb = function
| ExistT (x, _) ->
  let b0 =
    qplus
      (qplus (qplus (qabs (log_lower a ha)) (qabs (log_upper a ha)))
        (qabs (log_lower b hb)))
      (qabs (log_upper b hb))
  in
  let s = exp_series_arch_shape b0 (qle_to_QleT' { qnum = Z0; qden = XH } b0)
  in
  let ExistT (x0, _) = s in
  let s0 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv x { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x1, _) = s0 in
  let s1 =
    log_seq_cauchy b hb
      (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0)))
  in
  let ExistT (x2, _) = s1 in
  let s2 =
    log_seq_cauchy a ha
      (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } x0)))
  in
  let ExistT (x3, _) = s2 in
  let n0 = Nat.max (S x1) (Nat.max x2 x3) in
  ExistT ((qdiv x (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } x0)), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } x0))),
  (ExistT ((Nat.max (Nat.max x2 x3) n0), (fun n _ ->
  qlt_to_QltT (qdiv x (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } x0))
    (qminus (projT1 (cw_log b hb) n) (projT1 (cw_log a ha) n))))))))

(** val real_le_plus_compat :
    real -> real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_plus_compat a b c d hab hcd =
  match hab with
  | Inl r ->
    (match hcd with
     | Inl r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_lt_plus_compat a b c d r r0))
     | Inr r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_lt_plus_compat_lt_le a b c d r (RealSetoid.real_eq_le c d r0))))
  | Inr r ->
    (match hcd with
     | Inl r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)
           (RealSetoid.real_eq_plus_compat a c b c r (real_eq_refl c))
           (real_lt_plus_translate b c d r0)))
     | Inr r0 ->
       RealSetoid.real_eq_le (real_plus a c) (real_plus b d)
         (RealSetoid.real_eq_plus_compat a c b d r r0))

(** val real_inv_pos_ext :
    real -> real -> real_lt -> real_lt -> real_eq -> real_eq **)

let real_inv_pos_ext x y hx hy heq =
  real_eq_trans (real_inv_pos x hx)
    (real_mult (real_inv_pos x hx) (real_mult y (real_inv_pos y hy)))
    (real_inv_pos y hy)
    (real_eq_trans (real_inv_pos x hx)
      (real_mult (real_inv_pos x hx) real_one)
      (real_mult (real_inv_pos x hx) (real_mult y (real_inv_pos y hy)))
      (real_eq_sym (real_mult (real_inv_pos x hx) real_one)
        (real_inv_pos x hx) (real_mult_one (real_inv_pos x hx)))
      (RealSetoid.real_eq_mult_compat (real_inv_pos x hx) real_one
        (real_inv_pos x hx) (real_mult y (real_inv_pos y hy))
        (real_eq_refl (real_inv_pos x hx))
        (real_eq_sym (real_mult y (real_inv_pos y hy)) real_one
          (real_inv_pos_correct y hy))))
    (real_eq_trans
      (real_mult (real_inv_pos x hx) (real_mult y (real_inv_pos y hy)))
      (real_mult (real_mult (real_inv_pos x hx) y) (real_inv_pos y hy))
      (real_inv_pos y hy)
      (real_mult_assoc (real_inv_pos x hx) y (real_inv_pos y hy))
      (real_eq_trans
        (real_mult (real_mult (real_inv_pos x hx) y) (real_inv_pos y hy))
        (real_mult (real_mult (real_inv_pos x hx) x) (real_inv_pos y hy))
        (real_inv_pos y hy)
        (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos x hx) y)
          (real_inv_pos y hy) (real_mult (real_inv_pos x hx) x)
          (real_inv_pos y hy)
          (RealSetoid.real_eq_mult_compat (real_inv_pos x hx) y
            (real_inv_pos x hx) x (real_eq_refl (real_inv_pos x hx))
            (real_eq_sym x y heq))
          (real_eq_refl (real_inv_pos y hy)))
        (real_eq_trans
          (real_mult (real_mult (real_inv_pos x hx) x) (real_inv_pos y hy))
          (real_mult real_one (real_inv_pos y hy)) (real_inv_pos y hy)
          (RealSetoid.real_eq_mult_compat (real_mult (real_inv_pos x hx) x)
            (real_inv_pos y hy) real_one (real_inv_pos y hy)
            (real_eq_trans (real_mult (real_inv_pos x hx) x)
              (real_mult x (real_inv_pos x hx)) real_one
              (real_mult_comm (real_inv_pos x hx) x)
              (real_inv_pos_correct x hx))
            (real_eq_refl (real_inv_pos y hy)))
          (real_eq_trans (real_mult real_one (real_inv_pos y hy))
            (real_mult (real_inv_pos y hy) real_one) (real_inv_pos y hy)
            (real_mult_comm real_one (real_inv_pos y hy))
            (real_mult_one (real_inv_pos y hy))))))

(** val real_le_mult_compat :
    real -> real -> real -> real_lt -> real_le -> real_le **)

let real_le_mult_compat a b c hc = function
| Inl r ->
  RealSetoid.real_lt_le_iff_req (real_mult a c) (real_mult b c) (Inl
    (real_mult_lt_compat a b c r hc))
| Inr r ->
  RealSetoid.real_eq_le (real_mult a c) (real_mult b c)
    (RealSetoid.real_eq_mult_compat a c b c r (real_eq_refl c))

(** val real_le_mult_compat_weak :
    real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_mult_compat_weak a b c hc hab =
  match hc with
  | Inl r -> real_le_mult_compat a b c r hab
  | Inr r ->
    RealSetoid.real_eq_le (real_mult a c) (real_mult b c)
      (real_eq_trans (real_mult a c) (real_mult a real_zero) (real_mult b c)
        (RealSetoid.real_eq_mult_compat a c a real_zero (real_eq_refl a)
          (real_eq_sym real_zero c r))
        (real_eq_trans (real_mult a real_zero) real_zero (real_mult b c)
          (real_mult_zero a)
          (real_eq_sym (real_mult b c) real_zero
            (real_eq_trans (real_mult b c) (real_mult b real_zero) real_zero
              (RealSetoid.real_eq_mult_compat b c b real_zero (real_eq_refl b)
                (real_eq_sym real_zero c r))
              (real_mult_zero b)))))

(** val real_lt_mult_compat :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_mult_compat a b c hc hab =
  real_mult_lt_compat_l a b c hab hc

(** val real_lt_zero_one : real_lt **)

let real_lt_zero_one =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus (projT1 real_one n) (projT1 real_zero n))))))))

(** val real_plus_positive : real -> real -> real_lt -> real_lt -> real_lt **)

let real_plus_positive a b ha hb =
  real_eq_lt_lt real_zero (real_plus real_zero real_zero) (real_plus a b)
    (real_eq_sym (real_plus real_zero real_zero) real_zero
      (real_eq_of_zero_diff (real_plus real_zero real_zero) real_zero))
    (real_lt_plus_compat real_zero a real_zero b ha hb)

(** val real_mult_positive : real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_positive a b ha hb =
  real_eq_lt_lt real_zero (real_mult real_zero b) (real_mult a b)
    (real_eq_sym (real_mult real_zero b) real_zero
      (real_eq_trans (real_mult real_zero b) (real_mult b real_zero) real_zero
        (real_mult_comm real_zero b) (real_mult_zero b)))
    (real_mult_lt_compat real_zero a b ha hb)

(** val real_min : real -> real -> real **)

let real_min a b =
  let ExistT (x, c) = a in
  let ExistT (x0, c0) = b in
  ExistT ((fun n -> qmin (x n) (x0 n)), (fun eps _ ->
  let hhalf =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = c (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf in
  let ExistT (x1, _) = s in
  let s0 = c0 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf in
  let ExistT (x2, _) = s0 in
  ExistT ((Nat.max x1 x2), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qmin (x m) (x0 m)) (qmin (x n) (x0 n)))) eps))))

(** val real_abs_zero_req : real_eq **)

let real_abs_zero_req =
  real_eq_of_zero_diff (real_abs real_zero) real_zero

(** val real_abs_mult_req : real -> real -> real_eq **)

let real_abs_mult_req a b =
  real_eq_of_zero_diff (real_abs (real_mult a b))
    (real_mult (real_abs a) (real_abs b))

(** val real_abs_pos_req : real -> real_lt -> real_eq **)

let real_abs_pos_req a ha eps _ =
  let ExistT (_, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x, _) = s in
  ExistT (x, (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 (real_abs a) n) (projT1 a n))) eps))

(** val real_abs_triangle_le_eps :
    real -> real -> real -> real_lt -> real_le **)

let real_abs_triangle_le_eps a b eps = function
| ExistT (x, a0) ->
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  RealSetoid.real_lt_le_iff_req (real_abs (real_plus a b))
    (real_plus (real_plus (real_abs a) (real_abs b)) eps) (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_plus (real_plus (real_abs a) (real_abs b)) eps) n)
        (projT1 (real_abs (real_plus a b)) n))))))))))

(** val real_min_pos : real -> real -> real_lt -> real_lt -> real_lt **)

let real_min_pos a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  let e = qmin x x1 in
  let he = qlt_to_QltT { qnum = Z0; qden = XH } e in
  ExistT (e, (Pair (he, (ExistT ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT e (qminus (projT1 (real_min a b) n) (projT1 real_zero n))))))))

(** val real_opp_plus : real -> real -> real_eq **)

let real_opp_plus a b =
  real_eq_of_zero_diff (real_opp (real_plus a b))
    (real_plus (real_opp a) (real_opp b))

(** val real_log : real -> real_lt -> real **)

let real_log =
  cw_log

(** val real_log_mult : real -> real -> real_lt -> real_lt -> real_eq **)

let real_log_mult a b ha hb =
  log_inv_mult_thm a b ha hb (real_mult_positive a b ha hb)

(** val real_log_one : real_lt -> real_eq **)

let real_log_one =
  log_inv_one_thm

module RealInterfaceEnhancedMod =
 struct
  (** val real_exp_ge_linear_eps : real -> real -> real_lt -> real_le **)

  let real_exp_ge_linear_eps t eps heps =
    Inl
      (let ExistT (x, a) = heps in
       let Pair (_, s) = a in
       let ExistT (x0, _) = s in
       let s0 = real_norm_bounded t in
       let ExistT (x1, a0) = s0 in
       let Pair (q0, _) = a0 in
       let s1 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0)
       in
       let ExistT (x2, a1) = s1 in
       let Pair (q1, _) = a1 in
       let s2 =
         exp_partial_tail_small x1 x2
           (qltT_leT' { qnum = Z0; qden = XH } x1 q0) q1
       in
       let ExistT (x3, _) = s2 in
       ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
       ((qlt_to_QltT { qnum = Z0; qden = XH }
          (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
       (ExistT ((Nat.max x0 (add (mul (S (S O)) x3) (S (S (S O))))),
       (fun n _ ->
       qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
         (qminus (projT1 (real_plus (cauchy_real_exp t) eps) n)
           (projT1 (real_plus real_one t) n)))))))))

  (** val real_log_le_linear_eps :
      real -> real -> real_lt -> real_lt -> real_le **)

  let real_log_le_linear_eps x eps hx hepspos =
    let y = real_log x hx in
    let h_exp_log = cw_log_exp_right x hx in
    let hlin = real_exp_ge_linear_eps y eps hepspos in
    real_le_trans y
      (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
      (real_plus (real_plus x (real_opp real_one)) eps)
      (real_le_trans y (real_plus (real_plus real_one y) (real_opp real_one))
        (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
        (RealSetoid.real_eq_le y
          (real_plus (real_plus real_one y) (real_opp real_one))
          (real_eq_of_zero_diff y
            (real_plus (real_plus real_one y) (real_opp real_one))))
        (real_le_trans (real_plus (real_plus real_one y) (real_opp real_one))
          (real_plus (real_plus (cauchy_real_exp y) eps) (real_opp real_one))
          (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one)) eps)
          (real_le_plus_compat (real_plus real_one y)
            (real_plus (cauchy_real_exp y) eps) (real_opp real_one)
            (real_opp real_one) hlin (real_le_refl (real_opp real_one)))
          (RealSetoid.real_eq_le
            (real_plus (real_plus (cauchy_real_exp y) eps)
              (real_opp real_one))
            (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one))
              eps)
            (real_eq_trans
              (real_plus (real_plus (cauchy_real_exp y) eps)
                (real_opp real_one))
              (real_plus (cauchy_real_exp y)
                (real_plus eps (real_opp real_one)))
              (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one))
                eps)
              (real_eq_sym
                (real_plus (cauchy_real_exp y)
                  (real_plus eps (real_opp real_one)))
                (real_plus (real_plus (cauchy_real_exp y) eps)
                  (real_opp real_one))
                (real_plus_assoc (cauchy_real_exp y) eps (real_opp real_one)))
              (real_eq_trans
                (real_plus (cauchy_real_exp y)
                  (real_plus eps (real_opp real_one)))
                (real_plus (cauchy_real_exp y)
                  (real_plus (real_opp real_one) eps))
                (real_plus (real_plus (cauchy_real_exp y) (real_opp real_one))
                  eps)
                (RealSetoid.real_eq_plus_compat (cauchy_real_exp y)
                  (real_plus eps (real_opp real_one)) (cauchy_real_exp y)
                  (real_plus (real_opp real_one) eps)
                  (real_eq_refl (cauchy_real_exp y))
                  (real_plus_comm eps (real_opp real_one)))
                (real_plus_assoc (cauchy_real_exp y) (real_opp real_one) eps))))))
      (real_le_plus_compat (real_plus (cauchy_real_exp y) (real_opp real_one))
        (real_plus x (real_opp real_one)) eps eps
        (real_le_plus_compat (cauchy_real_exp y) x (real_opp real_one)
          (real_opp real_one)
          (RealSetoid.real_eq_le (cauchy_real_exp y) x h_exp_log)
          (real_le_refl (real_opp real_one)))
        (real_le_refl eps))
 end

(** val real_opp_mult : real -> real -> real_eq **)

let real_opp_mult a b =
  real_eq_of_zero_diff (real_opp (real_mult a b)) (real_mult a (real_opp b))

(** val real_opp_opp : real -> real_eq **)

let real_opp_opp x =
  real_eq_of_zero_diff (real_opp (real_opp x)) x

(** val real_eq_mult_cancel_r :
    real -> real -> real -> real_lt -> real_eq -> real_eq **)

let real_eq_mult_cancel_r a b c hc habc =
  real_eq_trans a (real_mult (real_mult a c) (real_inv_pos c hc)) b
    (real_eq_sym (real_mult (real_mult a c) (real_inv_pos c hc)) a
      (real_eq_trans (real_mult (real_mult a c) (real_inv_pos c hc))
        (real_mult a (real_mult c (real_inv_pos c hc))) a
        (real_eq_sym (real_mult a (real_mult c (real_inv_pos c hc)))
          (real_mult (real_mult a c) (real_inv_pos c hc))
          (real_mult_assoc a c (real_inv_pos c hc)))
        (real_eq_trans (real_mult a (real_mult c (real_inv_pos c hc)))
          (real_mult a real_one) a
          (RealSetoid.real_eq_mult_compat a (real_mult c (real_inv_pos c hc))
            a real_one (real_eq_refl a) (real_inv_pos_correct c hc))
          (real_mult_one a))))
    (real_eq_trans (real_mult (real_mult a c) (real_inv_pos c hc))
      (real_mult (real_mult b c) (real_inv_pos c hc)) b
      (RealSetoid.real_eq_mult_compat (real_mult a c) (real_inv_pos c hc)
        (real_mult b c) (real_inv_pos c hc) habc
        (real_eq_refl (real_inv_pos c hc)))
      (real_eq_sym b (real_mult (real_mult b c) (real_inv_pos c hc))
        (real_eq_trans b (real_mult b (real_mult c (real_inv_pos c hc)))
          (real_mult (real_mult b c) (real_inv_pos c hc))
          (real_eq_trans b (real_mult b real_one)
            (real_mult b (real_mult c (real_inv_pos c hc)))
            (real_eq_sym (real_mult b real_one) b (real_mult_one b))
            (RealSetoid.real_eq_mult_compat b real_one b
              (real_mult c (real_inv_pos c hc)) (real_eq_refl b)
              (real_eq_sym (real_mult c (real_inv_pos c hc)) real_one
                (real_inv_pos_correct c hc))))
          (real_mult_assoc b c (real_inv_pos c hc)))))

(** val real_inv_inv : real -> real_lt -> real_lt -> real_eq **)

let real_inv_inv x hx hx' =
  real_eq_mult_cancel_r (real_inv_pos (real_inv_pos x hx) hx') x
    (real_inv_pos x hx) hx'
    (real_eq_trans
      (real_mult (real_inv_pos (real_inv_pos x hx) hx') (real_inv_pos x hx))
      real_one (real_mult x (real_inv_pos x hx))
      (real_eq_trans
        (real_mult (real_inv_pos (real_inv_pos x hx) hx') (real_inv_pos x hx))
        (real_mult (real_inv_pos x hx) (real_inv_pos (real_inv_pos x hx) hx'))
        real_one
        (real_mult_comm (real_inv_pos (real_inv_pos x hx) hx')
          (real_inv_pos x hx))
        (real_inv_pos_correct (real_inv_pos x hx) hx'))
      (real_eq_sym (real_mult x (real_inv_pos x hx)) real_one
        (real_inv_pos_correct x hx)))

(** val real_exp_neg_opp_log : real -> real_lt -> real_eq **)

let real_exp_neg_opp_log x hx =
  real_eq_mult_cancel_r (cauchy_real_exp (real_opp (real_log x hx)))
    (real_inv_pos x hx) x hx
    (real_eq_trans (real_mult (cauchy_real_exp (real_opp (real_log x hx))) x)
      real_one (real_mult (real_inv_pos x hx) x)
      (real_eq_trans
        (real_mult (cauchy_real_exp (real_opp (real_log x hx))) x)
        (real_mult (cauchy_real_exp (real_opp (real_log x hx)))
          (cauchy_real_exp (real_log x hx)))
        real_one
        (RealSetoid.real_eq_mult_compat
          (cauchy_real_exp (real_opp (real_log x hx))) x
          (cauchy_real_exp (real_opp (real_log x hx)))
          (cauchy_real_exp (real_log x hx))
          (real_eq_refl (cauchy_real_exp (real_opp (real_log x hx))))
          (real_eq_sym (cauchy_real_exp (real_log x hx)) x
            (cw_log_exp_right x hx)))
        (real_eq_trans
          (real_mult (cauchy_real_exp (real_opp (real_log x hx)))
            (cauchy_real_exp (real_log x hx)))
          (cauchy_real_exp
            (real_plus (real_opp (real_log x hx)) (real_log x hx)))
          real_one
          (real_eq_sym
            (cauchy_real_exp
              (real_plus (real_opp (real_log x hx)) (real_log x hx)))
            (real_mult (cauchy_real_exp (real_opp (real_log x hx)))
              (cauchy_real_exp (real_log x hx)))
            (cauchy_real_exp_plus (real_opp (real_log x hx)) (real_log x hx)))
          (real_eq_trans
            (cauchy_real_exp
              (real_plus (real_opp (real_log x hx)) (real_log x hx)))
            (cauchy_real_exp real_zero) real_one
            (cauchy_real_exp_wd
              (real_plus (real_opp (real_log x hx)) (real_log x hx)) real_zero
              (real_eq_trans
                (real_plus (real_opp (real_log x hx)) (real_log x hx))
                (real_plus (real_log x hx) (real_opp (real_log x hx)))
                real_zero
                (real_plus_comm (real_opp (real_log x hx)) (real_log x hx))
                (real_plus_opp (real_log x hx))))
            cauchy_real_exp_zero)))
      (real_eq_trans real_one (real_mult x (real_inv_pos x hx))
        (real_mult (real_inv_pos x hx) x)
        (real_eq_sym (real_mult x (real_inv_pos x hx)) real_one
          (real_inv_pos_correct x hx))
        (real_mult_comm x (real_inv_pos x hx))))

(** val real_log_inv_one_inv : real -> real_lt -> real_lt -> real_eq **)

let real_log_inv_one_inv x hx hinv =
  real_weak_trich (real_log (real_inv_pos x hx) hinv)
    (real_opp (real_log x hx)) (fun hLlt ->
    real_lt_not_eq (cauchy_real_exp (real_log (real_inv_pos x hx) hinv))
      (cauchy_real_exp (real_opp (real_log x hx)))
      (cauchy_real_exp_mono (real_log (real_inv_pos x hx) hinv)
        (real_opp (real_log x hx)) hLlt)
      (real_eq_trans (cauchy_real_exp (real_log (real_inv_pos x hx) hinv))
        (real_inv_pos x hx) (cauchy_real_exp (real_opp (real_log x hx)))
        (cw_log_exp_right (real_inv_pos x hx) hinv)
        (real_eq_sym (cauchy_real_exp (real_opp (real_log x hx)))
          (real_inv_pos x hx) (real_exp_neg_opp_log x hx))))
    (fun hRlt ->
    real_lt_not_eq (cauchy_real_exp (real_opp (real_log x hx)))
      (cauchy_real_exp (real_log (real_inv_pos x hx) hinv))
      (cauchy_real_exp_mono (real_opp (real_log x hx))
        (real_log (real_inv_pos x hx) hinv) hRlt)
      (real_eq_trans (cauchy_real_exp (real_opp (real_log x hx)))
        (real_inv_pos x hx)
        (cauchy_real_exp (real_log (real_inv_pos x hx) hinv))
        (real_exp_neg_opp_log x hx)
        (real_eq_sym (cauchy_real_exp (real_log (real_inv_pos x hx) hinv))
          (real_inv_pos x hx) (cw_log_exp_right (real_inv_pos x hx) hinv))))

(** val real_log_wd :
    real -> real -> real_lt -> real_lt -> real_eq -> real_eq **)

let real_log_wd a b ha hb hab =
  real_weak_trich (real_log a ha) (real_log b hb) (fun hLlt ->
    real_lt_not_eq (cauchy_real_exp (real_log a ha))
      (cauchy_real_exp (real_log b hb))
      (cauchy_real_exp_mono (real_log a ha) (real_log b hb) hLlt)
      (real_eq_trans (cauchy_real_exp (real_log a ha)) a
        (cauchy_real_exp (real_log b hb)) (cw_log_exp_right a ha)
        (real_eq_trans a b (cauchy_real_exp (real_log b hb)) hab
          (real_eq_sym (cauchy_real_exp (real_log b hb)) b
            (cw_log_exp_right b hb)))))
    (fun hRlt ->
    real_lt_not_eq (cauchy_real_exp (real_log b hb))
      (cauchy_real_exp (real_log a ha))
      (cauchy_real_exp_mono (real_log b hb) (real_log a ha) hRlt)
      (real_eq_trans (cauchy_real_exp (real_log b hb)) b
        (cauchy_real_exp (real_log a ha)) (cw_log_exp_right b hb)
        (real_eq_trans b a (cauchy_real_exp (real_log a ha))
          (real_eq_sym a b hab)
          (real_eq_sym (cauchy_real_exp (real_log a ha)) a
            (cw_log_exp_right a ha)))))

(** val real_succ_minus_one : real -> real_eq **)

let real_succ_minus_one t =
  real_eq_of_zero_diff (real_plus (real_plus real_one t) (real_opp real_one))
    t

(** val real_log_one_plus_le_eps :
    real -> real -> real_lt -> real_lt -> real_le **)

let real_log_one_plus_le_eps t eps hs heps =
  real_le_trans (real_log (real_plus real_one t) hs)
    (real_plus (real_plus (real_plus real_one t) (real_opp real_one)) eps)
    (real_plus t eps)
    (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_plus real_one t)
      eps hs heps)
    (RealSetoid.real_eq_le
      (real_plus (real_plus (real_plus real_one t) (real_opp real_one)) eps)
      (real_plus t eps)
      (RealSetoid.real_eq_plus_compat
        (real_plus (real_plus real_one t) (real_opp real_one)) eps t eps
        (real_succ_minus_one t) (real_eq_refl eps)))

(** val real_log_div : real -> real -> real_lt -> real_lt -> real_eq **)

let real_log_div a b ha hb =
  real_eq_trans
    (real_log (real_mult a (real_inv_pos b hb))
      (real_mult_positive a (real_inv_pos b hb) ha (real_inv_pos_pos b hb)))
    (real_plus (real_log a ha)
      (real_log (real_inv_pos b hb) (real_inv_pos_pos b hb)))
    (real_plus (real_log a ha) (real_opp (real_log b hb)))
    (real_log_mult a (real_inv_pos b hb) ha (real_inv_pos_pos b hb))
    (RealSetoid.real_eq_plus_compat (real_log a ha)
      (real_log (real_inv_pos b hb) (real_inv_pos_pos b hb)) (real_log a ha)
      (real_opp (real_log b hb)) (real_eq_refl (real_log a ha))
      (real_log_inv_one_inv b hb (real_inv_pos_pos b hb)))

(** val real_succ_mult_inv : real -> real -> real_lt -> real_eq **)

let real_succ_mult_inv x h hx =
  real_eq_trans (real_mult (real_plus x h) (real_inv_pos x hx))
    (real_plus (real_mult (real_inv_pos x hx) x)
      (real_mult (real_inv_pos x hx) h))
    (real_plus real_one (real_mult h (real_inv_pos x hx)))
    (real_eq_trans (real_mult (real_plus x h) (real_inv_pos x hx))
      (real_mult (real_inv_pos x hx) (real_plus x h))
      (real_plus (real_mult (real_inv_pos x hx) x)
        (real_mult (real_inv_pos x hx) h))
      (real_mult_comm (real_plus x h) (real_inv_pos x hx))
      (real_distrib (real_inv_pos x hx) x h))
    (real_eq_trans
      (real_plus (real_mult (real_inv_pos x hx) x)
        (real_mult (real_inv_pos x hx) h))
      (real_plus (real_mult x (real_inv_pos x hx))
        (real_mult h (real_inv_pos x hx)))
      (real_plus real_one (real_mult h (real_inv_pos x hx)))
      (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos x hx) x)
        (real_mult (real_inv_pos x hx) h) (real_mult x (real_inv_pos x hx))
        (real_mult h (real_inv_pos x hx))
        (real_mult_comm (real_inv_pos x hx) x)
        (real_mult_comm (real_inv_pos x hx) h))
      (RealSetoid.real_eq_plus_compat (real_mult x (real_inv_pos x hx))
        (real_mult h (real_inv_pos x hx)) real_one
        (real_mult h (real_inv_pos x hx)) (real_inv_pos_correct x hx)
        (real_eq_refl (real_mult h (real_inv_pos x hx)))))

(** val real_log_plus_diff :
    real -> real -> real_lt -> real_lt -> real_lt -> real_eq **)

let real_log_plus_diff x h hx hxh ht =
  real_eq_trans
    (real_plus (real_log (real_plus x h) hxh) (real_opp (real_log x hx)))
    (real_log (real_mult (real_plus x h) (real_inv_pos x hx))
      (real_mult_positive (real_plus x h) (real_inv_pos x hx) hxh
        (real_inv_pos_pos x hx)))
    (real_log (real_plus real_one (real_mult h (real_inv_pos x hx))) ht)
    (real_eq_sym
      (real_log (real_mult (real_plus x h) (real_inv_pos x hx))
        (real_mult_positive (real_plus x h) (real_inv_pos x hx) hxh
          (real_inv_pos_pos x hx)))
      (real_plus (real_log (real_plus x h) hxh) (real_opp (real_log x hx)))
      (real_log_div (real_plus x h) x hxh hx))
    (real_log_wd (real_mult (real_plus x h) (real_inv_pos x hx))
      (real_plus real_one (real_mult h (real_inv_pos x hx)))
      (real_mult_positive (real_plus x h) (real_inv_pos x hx) hxh
        (real_inv_pos_pos x hx))
      ht (real_succ_mult_inv x h hx))

(** val real_abs_lt_lower : real -> real -> real_lt -> real_lt **)

let real_abs_lt_lower h e = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 h n) (projT1 (real_opp e) n))))))))

(** val real_two_pos_local : real_lt **)

let real_two_pos_local =
  real_eq_lt_lt real_zero (real_plus real_zero real_zero)
    (real_plus real_one real_one)
    (real_eq_sym (real_plus real_zero real_zero) real_zero
      (real_plus_zero real_zero))
    (real_lt_plus_compat real_zero real_one real_zero real_one
      real_lt_zero_one real_lt_zero_one)

(** val real_inv_minus_one_opp_noHt : real -> real_lt -> real_eq **)

let real_inv_minus_one_opp_noHt t =
  let s = real_plus real_one t in
  (fun hs ->
  real_eq_trans (real_opp (real_mult t (real_inv_pos s hs)))
    (real_opp
      (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s hs)))
    (real_plus (real_inv_pos s hs) (real_opp real_one))
    (RealSetoid.real_eq_opp_compat (real_mult t (real_inv_pos s hs))
      (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s hs))
      (RealSetoid.real_eq_mult_compat t (real_inv_pos s hs)
        (real_plus s (real_opp real_one)) (real_inv_pos s hs)
        (real_eq_sym (real_plus s (real_opp real_one)) t
          (real_succ_minus_one t))
        (real_eq_refl (real_inv_pos s hs))))
    (real_eq_trans
      (real_opp
        (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s hs)))
      (real_opp
        (real_mult (real_inv_pos s hs) (real_plus s (real_opp real_one))))
      (real_plus (real_inv_pos s hs) (real_opp real_one))
      (RealSetoid.real_eq_opp_compat
        (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s hs))
        (real_mult (real_inv_pos s hs) (real_plus s (real_opp real_one)))
        (real_mult_comm (real_plus s (real_opp real_one)) (real_inv_pos s hs)))
      (real_eq_trans
        (real_opp
          (real_mult (real_inv_pos s hs) (real_plus s (real_opp real_one))))
        (real_opp
          (real_plus (real_mult (real_inv_pos s hs) s)
            (real_mult (real_inv_pos s hs) (real_opp real_one))))
        (real_plus (real_inv_pos s hs) (real_opp real_one))
        (RealSetoid.real_eq_opp_compat
          (real_mult (real_inv_pos s hs) (real_plus s (real_opp real_one)))
          (real_plus (real_mult (real_inv_pos s hs) s)
            (real_mult (real_inv_pos s hs) (real_opp real_one)))
          (real_distrib (real_inv_pos s hs) s (real_opp real_one)))
        (real_eq_trans
          (real_opp
            (real_plus (real_mult (real_inv_pos s hs) s)
              (real_mult (real_inv_pos s hs) (real_opp real_one))))
          (real_opp
            (real_plus real_one
              (real_opp (real_mult (real_inv_pos s hs) real_one))))
          (real_plus (real_inv_pos s hs) (real_opp real_one))
          (RealSetoid.real_eq_opp_compat
            (real_plus (real_mult (real_inv_pos s hs) s)
              (real_mult (real_inv_pos s hs) (real_opp real_one)))
            (real_plus real_one
              (real_opp (real_mult (real_inv_pos s hs) real_one)))
            (RealSetoid.real_eq_plus_compat (real_mult (real_inv_pos s hs) s)
              (real_mult (real_inv_pos s hs) (real_opp real_one)) real_one
              (real_opp (real_mult (real_inv_pos s hs) real_one))
              (real_eq_trans (real_mult (real_inv_pos s hs) s)
                (real_mult s (real_inv_pos s hs)) real_one
                (real_mult_comm (real_inv_pos s hs) s)
                (real_inv_pos_correct s hs))
              (real_eq_sym (real_opp (real_mult (real_inv_pos s hs) real_one))
                (real_mult (real_inv_pos s hs) (real_opp real_one))
                (real_opp_mult (real_inv_pos s hs) real_one))))
          (real_eq_trans
            (real_opp
              (real_plus real_one
                (real_opp (real_mult (real_inv_pos s hs) real_one))))
            (real_opp (real_plus real_one (real_opp (real_inv_pos s hs))))
            (real_plus (real_inv_pos s hs) (real_opp real_one))
            (RealSetoid.real_eq_opp_compat
              (real_plus real_one
                (real_opp (real_mult (real_inv_pos s hs) real_one)))
              (real_plus real_one (real_opp (real_inv_pos s hs)))
              (RealSetoid.real_eq_plus_compat real_one
                (real_opp (real_mult (real_inv_pos s hs) real_one)) real_one
                (real_opp (real_inv_pos s hs)) (real_eq_refl real_one)
                (RealSetoid.real_eq_opp_compat
                  (real_mult (real_inv_pos s hs) real_one) (real_inv_pos s hs)
                  (real_mult_one (real_inv_pos s hs)))))
            (real_eq_trans
              (real_opp (real_plus real_one (real_opp (real_inv_pos s hs))))
              (real_plus (real_opp real_one)
                (real_opp (real_opp (real_inv_pos s hs))))
              (real_plus (real_inv_pos s hs) (real_opp real_one))
              (real_opp_plus real_one (real_opp (real_inv_pos s hs)))
              (real_eq_trans
                (real_plus (real_opp real_one)
                  (real_opp (real_opp (real_inv_pos s hs))))
                (real_plus (real_opp real_one) (real_inv_pos s hs))
                (real_plus (real_inv_pos s hs) (real_opp real_one))
                (RealSetoid.real_eq_plus_compat (real_opp real_one)
                  (real_opp (real_opp (real_inv_pos s hs)))
                  (real_opp real_one) (real_inv_pos s hs)
                  (real_eq_refl (real_opp real_one))
                  (real_opp_opp (real_inv_pos s hs)))
                (real_plus_comm (real_opp real_one) (real_inv_pos s hs)))))))))

(** val real_t_plus_inv_minus_one : real -> real_lt -> real_eq **)

let real_t_plus_inv_minus_one t =
  let s = real_plus real_one t in
  (fun hs ->
  real_eq_trans
    (real_plus t (real_plus (real_inv_pos s hs) (real_opp real_one)))
    (real_plus t (real_opp (real_mult t (real_inv_pos s hs))))
    (real_mult (real_mult t t) (real_inv_pos s hs))
    (RealSetoid.real_eq_plus_compat t
      (real_plus (real_inv_pos s hs) (real_opp real_one)) t
      (real_opp (real_mult t (real_inv_pos s hs))) (real_eq_refl t)
      (real_eq_sym (real_opp (real_mult t (real_inv_pos s hs)))
        (real_plus (real_inv_pos s hs) (real_opp real_one))
        (real_inv_minus_one_opp_noHt t hs)))
    (real_eq_trans (real_plus t (real_opp (real_mult t (real_inv_pos s hs))))
      (real_plus (real_mult t real_one)
        (real_mult t (real_opp (real_inv_pos s hs))))
      (real_mult (real_mult t t) (real_inv_pos s hs))
      (RealSetoid.real_eq_plus_compat t
        (real_opp (real_mult t (real_inv_pos s hs))) (real_mult t real_one)
        (real_mult t (real_opp (real_inv_pos s hs)))
        (real_eq_sym (real_mult t real_one) t (real_mult_one t))
        (real_opp_mult t (real_inv_pos s hs)))
      (real_eq_trans
        (real_plus (real_mult t real_one)
          (real_mult t (real_opp (real_inv_pos s hs))))
        (real_mult t (real_plus real_one (real_opp (real_inv_pos s hs))))
        (real_mult (real_mult t t) (real_inv_pos s hs))
        (real_eq_sym
          (real_mult t (real_plus real_one (real_opp (real_inv_pos s hs))))
          (real_plus (real_mult t real_one)
            (real_mult t (real_opp (real_inv_pos s hs))))
          (real_distrib t real_one (real_opp (real_inv_pos s hs))))
        (real_eq_trans
          (real_mult t (real_plus real_one (real_opp (real_inv_pos s hs))))
          (real_mult t
            (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s hs)))
          (real_mult (real_mult t t) (real_inv_pos s hs))
          (RealSetoid.real_eq_mult_compat t
            (real_plus real_one (real_opp (real_inv_pos s hs))) t
            (real_mult (real_plus s (real_opp real_one)) (real_inv_pos s hs))
            (real_eq_refl t)
            (real_eq_trans (real_plus real_one (real_opp (real_inv_pos s hs)))
              (real_plus (real_mult s (real_inv_pos s hs))
                (real_opp (real_mult (real_inv_pos s hs) real_one)))
              (real_mult (real_plus s (real_opp real_one))
                (real_inv_pos s hs))
              (RealSetoid.real_eq_plus_compat real_one
                (real_opp (real_inv_pos s hs))
                (real_mult s (real_inv_pos s hs))
                (real_opp (real_mult (real_inv_pos s hs) real_one))
                (real_eq_sym (real_mult s (real_inv_pos s hs)) real_one
                  (real_inv_pos_correct s hs))
                (RealSetoid.real_eq_opp_compat (real_inv_pos s hs)
                  (real_mult (real_inv_pos s hs) real_one)
                  (real_eq_sym (real_mult (real_inv_pos s hs) real_one)
                    (real_inv_pos s hs) (real_mult_one (real_inv_pos s hs)))))
              (real_eq_trans
                (real_plus (real_mult s (real_inv_pos s hs))
                  (real_opp (real_mult (real_inv_pos s hs) real_one)))
                (real_plus (real_mult (real_inv_pos s hs) s)
                  (real_mult (real_inv_pos s hs) (real_opp real_one)))
                (real_mult (real_plus s (real_opp real_one))
                  (real_inv_pos s hs))
                (RealSetoid.real_eq_plus_compat
                  (real_mult s (real_inv_pos s hs))
                  (real_opp (real_mult (real_inv_pos s hs) real_one))
                  (real_mult (real_inv_pos s hs) s)
                  (real_mult (real_inv_pos s hs) (real_opp real_one))
                  (real_mult_comm s (real_inv_pos s hs))
                  (real_opp_mult (real_inv_pos s hs) real_one))
                (real_eq_trans
                  (real_plus (real_mult (real_inv_pos s hs) s)
                    (real_mult (real_inv_pos s hs) (real_opp real_one)))
                  (real_mult (real_inv_pos s hs)
                    (real_plus s (real_opp real_one)))
                  (real_mult (real_plus s (real_opp real_one))
                    (real_inv_pos s hs))
                  (real_eq_sym
                    (real_mult (real_inv_pos s hs)
                      (real_plus s (real_opp real_one)))
                    (real_plus (real_mult (real_inv_pos s hs) s)
                      (real_mult (real_inv_pos s hs) (real_opp real_one)))
                    (real_distrib (real_inv_pos s hs) s (real_opp real_one)))
                  (real_mult_comm (real_inv_pos s hs)
                    (real_plus s (real_opp real_one)))))))
          (real_eq_trans
            (real_mult t
              (real_mult (real_plus s (real_opp real_one))
                (real_inv_pos s hs)))
            (real_mult t (real_mult t (real_inv_pos s hs)))
            (real_mult (real_mult t t) (real_inv_pos s hs))
            (RealSetoid.real_eq_mult_compat t
              (real_mult (real_plus s (real_opp real_one))
                (real_inv_pos s hs))
              t (real_mult t (real_inv_pos s hs)) (real_eq_refl t)
              (RealSetoid.real_eq_mult_compat
                (real_plus s (real_opp real_one)) (real_inv_pos s hs) t
                (real_inv_pos s hs) (real_succ_minus_one t)
                (real_eq_refl (real_inv_pos s hs))))
            (real_mult_assoc t t (real_inv_pos s hs)))))))

(** val real_t_minus_log_bound :
    real -> real -> real_lt -> real_lt -> real_le **)

let real_t_minus_log_bound t eps hs heps =
  let s = real_plus real_one t in
  real_le_trans (real_plus t (real_opp (real_log s hs)))
    (real_plus t (real_log (real_inv_pos s hs) (real_inv_pos_pos s hs)))
    (real_plus (real_mult (real_mult t t) (real_inv_pos s hs)) eps)
    (RealSetoid.real_eq_le (real_plus t (real_opp (real_log s hs)))
      (real_plus t (real_log (real_inv_pos s hs) (real_inv_pos_pos s hs)))
      (RealSetoid.real_eq_plus_compat t (real_opp (real_log s hs)) t
        (real_log (real_inv_pos s hs) (real_inv_pos_pos s hs))
        (real_eq_refl t)
        (real_eq_sym (real_log (real_inv_pos s hs) (real_inv_pos_pos s hs))
          (real_opp (real_log s hs))
          (real_log_inv_one_inv s hs (real_inv_pos_pos s hs)))))
    (real_le_trans
      (real_plus t (real_log (real_inv_pos s hs) (real_inv_pos_pos s hs)))
      (real_plus t
        (real_plus (real_plus (real_inv_pos s hs) (real_opp real_one)) eps))
      (real_plus (real_mult (real_mult t t) (real_inv_pos s hs)) eps)
      (real_le_plus_compat t t
        (real_log (real_inv_pos s hs) (real_inv_pos_pos s hs))
        (real_plus (real_plus (real_inv_pos s hs) (real_opp real_one)) eps)
        (real_le_refl t)
        (RealInterfaceEnhancedMod.real_log_le_linear_eps (real_inv_pos s hs)
          eps (real_inv_pos_pos s hs) heps))
      (RealSetoid.real_eq_le
        (real_plus t
          (real_plus (real_plus (real_inv_pos s hs) (real_opp real_one)) eps))
        (real_plus (real_mult (real_mult t t) (real_inv_pos s hs)) eps)
        (real_eq_trans
          (real_plus t
            (real_plus (real_plus (real_inv_pos s hs) (real_opp real_one))
              eps))
          (real_plus
            (real_plus t (real_plus (real_inv_pos s hs) (real_opp real_one)))
            eps)
          (real_plus (real_mult (real_mult t t) (real_inv_pos s hs)) eps)
          (real_plus_assoc t
            (real_plus (real_inv_pos s hs) (real_opp real_one)) eps)
          (RealSetoid.real_eq_plus_compat
            (real_plus t (real_plus (real_inv_pos s hs) (real_opp real_one)))
            eps (real_mult (real_mult t t) (real_inv_pos s hs)) eps
            (real_t_plus_inv_minus_one t hs) (real_eq_refl eps)))))

(** val real_quad_div_le_two_eps :
    real -> real -> real -> real_lt -> real_lt -> real_lt -> real_le **)

let real_quad_div_le_two_eps t s eps hs hs12 = function
| ExistT (x, a) ->
  let Pair (q0, s0) = a in
  let ExistT (x0, _) = s0 in
  let hinv2lt =
    real_lt_eq_lt (real_inv_pos s hs)
      (real_inv_pos
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local))
      (real_plus real_one real_one)
      (real_inv_pos_lt_contra
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local) s
        (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local) hs
        hs12)
      (real_inv_inv (real_plus real_one real_one) real_two_pos_local
        (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local))
  in
  let ExistT (_, a0) = hinv2lt in
  let Pair (_, s1) = a0 in
  let ExistT (x1, _) = s1 in
  let ExistT (_, a1) = hs12 in
  let Pair (_, s2) = a1 in
  let ExistT (x2, _) = s2 in
  let ExistT (x3, a2) = hs in
  let Pair (q1, s3) = a2 in
  let ExistT (x4, q2) = s3 in
  RealSetoid.real_lt_le_iff_req
    (real_mult (real_mult t t)
      (real_inv_pos s (ExistT (x3, (Pair (q1, (ExistT (x4, q2))))))))
    (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps)
    (Inl (ExistT (x, (Pair (q0, (ExistT
    ((Nat.max x0 (Nat.max x4 (Nat.max x2 x1))), (fun n _ ->
    let i = real_inv_pos s (ExistT (x3, (Pair (q1, (ExistT (x4, q2)))))) in
    let qn = projT1 (real_mult (real_mult t t) i) n in
    let pn =
      projT1
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          eps)
        n
    in
    qlt_to_QltT x (qminus pn qn)))))))))

(** val real_min_lt_l : real -> real -> real -> real_lt -> real_lt **)

let real_min_lt_l h a _ = function
| ExistT (x, a0) ->
  let Pair (q0, s) = a0 in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 a n) (projT1 (real_abs h) n))))))))

(** val real_min_lt_r : real -> real -> real -> real_lt -> real_lt **)

let real_min_lt_r h _ b = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 b n) (projT1 (real_abs h) n))))))))

(** val real_half_x_mult_inv : real -> real_lt -> real_eq **)

let real_half_x_mult_inv x hx =
  real_eq_trans
    (real_mult
      (real_mult
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local) x)
      (real_inv_pos x hx))
    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
      (real_mult x (real_inv_pos x hx)))
    (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
    (real_eq_sym
      (real_mult
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        (real_mult x (real_inv_pos x hx)))
      (real_mult
        (real_mult
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local) x)
        (real_inv_pos x hx))
      (real_mult_assoc
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local) x
        (real_inv_pos x hx)))
    (real_eq_trans
      (real_mult
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        (real_mult x (real_inv_pos x hx)))
      (real_mult
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        real_one)
      (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
      (RealSetoid.real_eq_mult_compat
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        (real_mult x (real_inv_pos x hx))
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        real_one
        (real_eq_refl
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
        (real_inv_pos_correct x hx))
      (real_mult_one
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))

(** val real_half_lt_one_plus_t : real -> real_lt -> real_lt **)

let real_half_lt_one_plus_t t ht =
  let half = real_inv_pos (real_plus real_one real_one) real_two_pos_local in
  let hhalf_t =
    real_eq_lt_lt real_zero (real_plus (real_opp half) half)
      (real_plus half t)
      (real_eq_sym (real_plus (real_opp half) half) real_zero
        (real_eq_trans (real_plus (real_opp half) half)
          (real_plus half (real_opp half)) real_zero
          (real_plus_comm (real_opp half) half) (real_plus_opp half)))
      (real_lt_eq_lt (real_plus (real_opp half) half) (real_plus t half)
        (real_plus half t)
        (real_lt_plus_compat_lt_le (real_opp half) t half half ht
          (real_le_refl half))
        (real_plus_comm t half))
  in
  let hmid =
    real_eq_lt_lt half (real_plus half real_zero)
      (real_plus half (real_plus half t))
      (real_eq_sym (real_plus half real_zero) half (real_plus_zero half))
      (real_lt_plus_compat_le_lt half half real_zero (real_plus half t)
        (real_le_refl half) hhalf_t)
  in
  real_lt_eq_lt half (real_plus half (real_plus half t))
    (real_plus real_one t) hmid
    (real_eq_trans (real_plus half (real_plus half t))
      (real_plus (real_plus half half) t) (real_plus real_one t)
      (real_plus_assoc half half t)
      (RealSetoid.real_eq_plus_compat (real_plus half half) t real_one t
        (real_eq_trans (real_plus half half)
          (real_plus (real_mult half real_one) (real_mult half real_one))
          real_one
          (RealSetoid.real_eq_plus_compat half half (real_mult half real_one)
            (real_mult half real_one)
            (real_eq_sym (real_mult half real_one) half (real_mult_one half))
            (real_eq_sym (real_mult half real_one) half (real_mult_one half)))
          (real_eq_trans
            (real_plus (real_mult half real_one) (real_mult half real_one))
            (real_mult half (real_plus real_one real_one)) real_one
            (real_eq_sym (real_mult half (real_plus real_one real_one))
              (real_plus (real_mult half real_one) (real_mult half real_one))
              (real_distrib half real_one real_one))
            (real_eq_trans (real_mult half (real_plus real_one real_one))
              (real_mult (real_plus real_one real_one) half) real_one
              (real_mult_comm half (real_plus real_one real_one))
              (real_inv_pos_correct (real_plus real_one real_one)
                real_two_pos_local))))
        (real_eq_refl t)))

(** val real_t_abs_lt_half : real -> real -> real_lt -> real_lt -> real_lt **)

let real_t_abs_lt_half x h hx hhx =
  let half = real_inv_pos (real_plus real_one real_one) real_two_pos_local in
  let habs =
    real_eq_trans (real_abs (real_mult h (real_inv_pos x hx)))
      (real_mult (real_abs h) (real_abs (real_inv_pos x hx)))
      (real_mult (real_abs h) (real_inv_pos x hx))
      (real_abs_mult_req h (real_inv_pos x hx))
      (RealSetoid.real_eq_mult_compat (real_abs h)
        (real_abs (real_inv_pos x hx)) (real_abs h) (real_inv_pos x hx)
        (real_eq_refl (real_abs h))
        (real_abs_pos_req (real_inv_pos x hx) (real_inv_pos_pos x hx)))
  in
  let hmid =
    real_mult_lt_compat (real_abs h)
      (real_mult
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local) x)
      (real_inv_pos x hx) hhx (real_inv_pos_pos x hx)
  in
  let heq = real_half_x_mult_inv x hx in
  real_eq_lt_lt (real_abs (real_mult h (real_inv_pos x hx)))
    (real_mult (real_abs h) (real_inv_pos x hx)) half habs
    (real_lt_eq_lt (real_mult (real_abs h) (real_inv_pos x hx))
      (real_mult (real_mult half x) (real_inv_pos x hx)) half hmid heq)

(** val real_abs_le_quad_ll :
    real -> real -> real -> real -> real -> real_lt -> real_lt -> real_lt ->
    real_lt -> real_lt -> real_le **)

let real_abs_le_quad_ll x t eps1 eps2 eps hXA_lt hXB_lt hA heps2 = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (_, a0) = hA in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (_, a1) = heps2 in
  let Pair (_, s1) = a1 in
  let ExistT (x3, _) = s1 in
  let ExistT (_, a2) = hXA_lt in
  let Pair (_, s2) = a2 in
  let ExistT (x4, _) = s2 in
  let ExistT (_, a3) = hXB_lt in
  let Pair (_, s3) = a3 in
  let ExistT (x5, _) = s3 in
  RealSetoid.real_lt_le_iff_req (real_abs x)
    (real_plus
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus eps1 eps2))
      eps)
    (Inl (ExistT (x0, (Pair (q0, (ExistT
    ((Nat.max x1 (Nat.max x4 (Nat.max x5 (Nat.max x2 x3)))), (fun n _ ->
    let qn = projT1 (real_abs x) n in
    let pn =
      projT1
        (real_plus
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus eps1 eps2))
          eps)
        n
    in
    qlt_to_QltT x0 (qminus pn qn)))))))))

(** val real_abs_le_quad_le :
    real -> real -> real -> real -> real -> real_lt -> real_eq -> real_lt ->
    real_lt -> real_lt -> real_le **)

let real_abs_le_quad_le x t eps1 eps2 eps hXA_lt hXB_eq hA heps2 = function
| ExistT (x0, a) ->
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (_, a0) = hA in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (_, a1) = heps2 in
  let Pair (_, s1) = a1 in
  let ExistT (x3, _) = s1 in
  let ExistT (_, a2) = hXA_lt in
  let Pair (_, s2) = a2 in
  let ExistT (x4, _) = s2 in
  let heps0h =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s3 = hXB_eq (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }) heps0h in
  let ExistT (x5, _) = s3 in
  RealSetoid.real_lt_le_iff_req (real_abs x)
    (real_plus
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus eps1 eps2))
      eps)
    (Inl (ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT ((Nat.max x1 (Nat.max x4 (Nat.max x5 (Nat.max x2 x3)))),
    (fun n _ ->
    let qn = projT1 (real_abs x) n in
    let pn =
      projT1
        (real_plus
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus eps1 eps2))
          eps)
        n
    in
    qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }) (qminus pn qn)))))))))

(** val real_abs_le_quad_ee :
    real -> real -> real -> real -> real -> real_eq -> real_eq -> real_lt ->
    real_lt -> real_lt -> real_le **)

let real_abs_le_quad_ee x t eps1 eps2 eps hXA_eq hXB_eq hA heps2 = function
| ExistT (x0, a) ->
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (_, a0) = hA in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (_, a1) = heps2 in
  let Pair (_, s1) = a1 in
  let ExistT (x3, _) = s1 in
  let heps0q =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv x0 { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let s2 = hXA_eq (qdiv x0 { qnum = (Zpos (XO (XO XH))); qden = XH }) heps0q
  in
  let ExistT (x4, _) = s2 in
  let s3 = hXB_eq (qdiv x0 { qnum = (Zpos (XO (XO XH))); qden = XH }) heps0q
  in
  let ExistT (x5, _) = s3 in
  RealSetoid.real_lt_le_iff_req (real_abs x)
    (real_plus
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus eps1 eps2))
      eps)
    (Inl (ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT ((Nat.max x1 (Nat.max x4 (Nat.max x5 (Nat.max x2 x3)))),
    (fun n _ ->
    let qn = projT1 (real_abs x) n in
    let pn =
      projT1
        (real_plus
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus eps1 eps2))
          eps)
        n
    in
    qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }) (qminus pn qn)))))))))

(** val real_abs_le_quad_el :
    real -> real -> real -> real -> real -> real_eq -> real_lt -> real_lt ->
    real_lt -> real_lt -> real_le **)

let real_abs_le_quad_el x t eps1 eps2 eps hXA_eq hXB_lt hA heps2 = function
| ExistT (x0, a) ->
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (_, a0) = hA in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (_, a1) = heps2 in
  let Pair (_, s1) = a1 in
  let ExistT (x3, _) = s1 in
  let ExistT (_, a2) = hXB_lt in
  let Pair (_, s2) = a2 in
  let ExistT (x4, _) = s2 in
  let heps0h =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s3 = hXA_eq (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }) heps0h in
  let ExistT (x5, _) = s3 in
  RealSetoid.real_lt_le_iff_req (real_abs x)
    (real_plus
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus eps1 eps2))
      eps)
    (Inl (ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT ((Nat.max x1 (Nat.max x5 (Nat.max x4 (Nat.max x2 x3)))),
    (fun n _ ->
    let qn = projT1 (real_abs x) n in
    let pn =
      projT1
        (real_plus
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus eps1 eps2))
          eps)
        n
    in
    qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }) (qminus pn qn)))))))))

(** val real_abs_le_quad_eps :
    real -> real -> real -> real -> real -> real_le -> real_le -> real_lt ->
    real_lt -> real_lt -> real_le **)

let real_abs_le_quad_eps x t eps1 eps2 eps hXA hXB hA heps2 heps =
  match hXA with
  | Inl r ->
    (match hXB with
     | Inl r0 -> real_abs_le_quad_ll x t eps1 eps2 eps r r0 hA heps2 heps
     | Inr r0 -> real_abs_le_quad_le x t eps1 eps2 eps r r0 hA heps2 heps)
  | Inr r ->
    (match hXB with
     | Inl r0 -> real_abs_le_quad_el x t eps1 eps2 eps r r0 hA heps2 heps
     | Inr r0 -> real_abs_le_quad_ee x t eps1 eps2 eps r r0 hA heps2 heps)

(** val real_quad_t_le_h_eps :
    real -> real -> real -> real -> real_lt -> real_lt -> real_lt -> real_lt
    -> real_le **)

let real_quad_t_le_h_eps x h eps eps' hx hh _ = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (_, a0) = hh in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (x3, a1) = hx in
  let Pair (q1, s1) = a1 in
  let ExistT (x4, q2) = s1 in
  RealSetoid.real_lt_le_iff_req
    (real_mult
      (real_mult
        (real_mult h
          (real_inv_pos x (ExistT (x3, (Pair (q1, (ExistT (x4, q2))))))))
        (real_mult h
          (real_inv_pos x (ExistT (x3, (Pair (q1, (ExistT (x4, q2)))))))))
      (real_plus real_one real_one))
    (real_plus
      (real_mult
        (real_mult
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local) eps)
        (real_abs h))
      eps')
    (Inl
    (let ExistT (x5, a2) = real_two_pos_local in
     let Pair (q3, s2) = a2 in
     let ExistT (x6, q4) = s2 in
     let half =
       real_inv_pos (real_plus real_one real_one) (ExistT (x5, (Pair (q3,
         (ExistT (x6, q4))))))
     in
     ExistT (x0, (Pair (q0, (ExistT
     ((Nat.max x1 (Nat.max x2 (Nat.max x4 x6))), (fun n _ ->
     let i = real_inv_pos x (ExistT (x3, (Pair (q1, (ExistT (x4, q2)))))) in
     let qn =
       projT1
         (real_mult (real_mult (real_mult h i) (real_mult h i))
           (real_plus real_one real_one))
         n
     in
     let pn =
       projT1 (real_plus (real_mult (real_mult half eps) (real_abs h)) eps') n
     in
     qlt_to_QltT x0 (qminus pn qn)))))))))

(** val real_abs_eq_compat : real -> real -> real_eq -> real_eq **)

let real_abs_eq_compat x y hxy eps heps =
  let s = hxy eps heps in
  let ExistT (x0, _) = s in
  ExistT (x0, (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 (real_abs x) n) (projT1 (real_abs y) n)))
    eps))

(** val real_inv_proj : real -> real_lt -> (nat, __) sigT **)

let real_inv_proj _ = function
| ExistT (_, a) ->
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val real_exp_le_inv_one_minus : real -> real_lt -> real_lt -> real_le **)

let real_exp_le_inv_one_minus x hx0 hx1 =
  let ExistT (x0, a) = hx0 in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (x2, a0) = hx1 in
  let Pair (q0, s0) = a0 in
  let ExistT (x3, q1) = s0 in
  let hx01 =
    real_lt_opp_plus x real_one (ExistT (x2, (Pair (q0, (ExistT (x3, q1))))))
  in
  let s1 = real_inv_proj (real_plus real_one (real_opp x)) hx01 in
  let ExistT (x4, _) = s1 in
  let eps' = qmult (qmult x0 x0) { qnum = (Zpos XH); qden = (XO XH) } in
  let heps' =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult (qmult x0 x0) { qnum = (Zpos XH); qden = (XO XH) })
  in
  Inl (ExistT (eps', (Pair (heps', (ExistT
  ((Nat.max x1 (Nat.max x3 (Nat.max x4 (S (S O))))), (fun n _ ->
  qlt_to_QltT eps'
    (qminus (projT1 (real_inv_pos (real_plus real_one (real_opp x)) hx01) n)
      (projT1 (cauchy_real_exp x) n)))))))))

(** val sin_term : nat -> q -> q **)

let sin_term j x =
  qmult (q_pow { qnum = (Zneg XH); qden = XH } j)
    (qdiv (q_pow x (S (mul (S (S O)) j))) (q_fact (S (mul (S (S O)) j))))

(** val cos_term : nat -> q -> q **)

let cos_term j x =
  qmult (q_pow { qnum = (Zneg XH); qden = XH } j)
    (qdiv (q_pow x (mul (S (S O)) j)) (q_fact (mul (S (S O)) j)))

(** val sin_partial : nat -> q -> q **)

let rec sin_partial n x =
  match n with
  | O -> sin_term O x
  | S m -> qplus (sin_partial m x) (sin_term (S m) x)

(** val cos_partial : nat -> q -> q **)

let rec cos_partial n x =
  match n with
  | O -> cos_term O x
  | S m -> qplus (cos_partial m x) (cos_term (S m) x)

(** val sc_sin_partial_cauchy_bounded :
    q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q ->
    qleT' -> qltT) sigT **)

let sc_sin_partial_cauchy_bounded b eps _ hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let n0' = S (mul (S (S O)) x) in
  let c =
    qmult (qdiv (q_pow b n0') (q_fact n0'))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let hC =
    qle_to_QleT' { qnum = Z0; qden = XH }
      (qmult (qdiv (q_pow b n0') (q_fact n0'))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
  in
  let s0 = arch_decay c eps hC hep in
  let ExistT (x0, _) = s0 in
  ExistT ((add n0' (S x0)), (fun m n _ _ y _ ->
  qlt_to_QltT (qabs (qminus (sin_partial m y) (sin_partial n y))) eps))

(** val sc_cos_partial_cauchy_bounded :
    q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q ->
    qleT' -> qltT) sigT **)

let sc_cos_partial_cauchy_bounded b eps _ hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let n0' = S (mul (S (S O)) x) in
  let c =
    qmult (qdiv (q_pow b n0') (q_fact n0'))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let hC =
    qle_to_QleT' { qnum = Z0; qden = XH }
      (qmult (qdiv (q_pow b n0') (q_fact n0'))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
  in
  let s0 = arch_decay c eps hC hep in
  let ExistT (x0, _) = s0 in
  ExistT ((add n0' (S x0)), (fun m n _ _ y _ ->
  qlt_to_QltT (qabs (qminus (cos_partial m y) (cos_partial n y))) eps))

(** val cauchy_real_sin : real -> real **)

let cauchy_real_sin = function
| ExistT (x0, c) ->
  ExistT ((fun n -> sin_partial n (x0 n)), (fun eps heps ->
    let s = real_norm_bounded (ExistT (x0, c)) in
    let ExistT (x1, a) = s in
    let Pair (q0, _) = a in
    let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
    let ExistT (x2, _) = s0 in
    let s1 =
      c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
        (qlt_to_QltT { qnum = Z0; qden = XH }
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)))
    in
    let ExistT (x3, _) = s1 in
    let s2 =
      sc_sin_partial_cauchy_bounded x1
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
        (qltT_leT' { qnum = Z0; qden = XH } x1 q0)
        (qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2)
    in
    let ExistT (x4, _) = s2 in
    ExistT ((Nat.max x3 x4), (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (sin_partial m (x0 m)) (sin_partial n (x0 n))))
      eps))))

(** val cauchy_real_cos : real -> real **)

let cauchy_real_cos = function
| ExistT (x0, c) ->
  ExistT ((fun n -> cos_partial n (x0 n)), (fun eps heps ->
    let s = real_norm_bounded (ExistT (x0, c)) in
    let ExistT (x1, a) = s in
    let Pair (q0, _) = a in
    let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
    let ExistT (x2, _) = s0 in
    let s1 =
      c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
        (qlt_to_QltT { qnum = Z0; qden = XH }
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)))
    in
    let ExistT (x3, _) = s1 in
    let s2 =
      sc_cos_partial_cauchy_bounded x1
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
        (qltT_leT' { qnum = Z0; qden = XH } x1 q0)
        (qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2)
    in
    let ExistT (x4, _) = s2 in
    ExistT ((Nat.max x3 x4), (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (cos_partial m (x0 m)) (cos_partial n (x0 n))))
      eps))))

(** val lp_a : nat -> q **)

let lp_a k =
  qdiv { qnum = (Zpos XH); qden = XH } { qnum =
    (Z.of_nat (add (mul (S (S O)) k) (S O))); qden = XH }

(** val lp_pair : nat -> q **)

let lp_pair j =
  qminus (lp_a (mul (S (S O)) j)) (lp_a (add (mul (S (S O)) j) (S O)))

(** val lp_odd : nat -> q **)

let rec lp_odd = function
| O -> lp_pair O
| S p -> qplus (lp_odd p) (lp_pair (S p))

(** val lp_four : q **)

let lp_four =
  qplus
    (qplus
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
      { qnum = (Zpos XH); qden = XH })
    { qnum = (Zpos XH); qden = XH }

(** val cauchy_real_pi_leibniz : real **)

let cauchy_real_pi_leibniz =
  ExistT ((fun n -> qmult lp_four (lp_odd n)), (fun eps _ ->
    let s = q_arch_inv (qdiv eps lp_four) in
    let ExistT (x, _) = s in
    ExistT (x, (fun m n _ _ ->
    qlt_to_QltT
      (qabs (qminus (qmult lp_four (lp_odd m)) (qmult lp_four (lp_odd n))))
      eps))))

(** val real_pi_leibniz_gt_three : real_lt **)

let real_pi_leibniz_gt_three =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO (XO
       (XI XH))))))); qden = XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO
         (XO (XI XH))))))); qden = XH })),
    (ExistT ((S (S (S O))), (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO (XO
        (XI XH))))))); qden = XH })
      (qminus (qmult lp_four (lp_odd n)) { qnum = (Zpos (XI XH)); qden = XH })))))))

(** val real_cos_three_halves_pos : real_lt **)

let real_cos_three_halves_pos =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO
       XH))))); qden = XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO
         XH))))); qden = XH })),
    (ExistT ((S (S (S (S O)))), (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO
        XH))))); qden = XH })
      (qminus
        (cos_partial n
          (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        { qnum = Z0; qden = XH })))))))

(** val real_cos_five_thirds_neg : real_lt **)

let real_cos_five_thirds_neg =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO (XO
       (XI XH))))))); qden = XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO
         (XO (XI XH))))))); qden = XH })),
    (ExistT ((S (S (S (S O)))), (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XO (XO
        (XI XH))))))); qden = XH })
      (qminus { qnum = Z0; qden = XH }
        (cos_partial n
          (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI
            XH)); qden = XH })))))))))

(** val real_sin_eq_compat : real -> real -> real_eq -> real_eq **)

let real_sin_eq_compat x y hxy eps _ =
  let s = real_norm_bounded x in
  let ExistT (x0, a) = s in
  let Pair (q0, _) = a in
  let s0 = real_norm_bounded y in
  let ExistT (x1, a0) = s0 in
  let Pair (q1, _) = a0 in
  let b = qplus x0 x1 in
  let hBT =
    qltT_leT' { qnum = Z0; qden = XH } (qplus x0 x1)
      (qltT_plus_pos_r x0 x1 q0 q1)
  in
  let s1 = exp_series_arch b hBT in
  let ExistT (x2, _) = s1 in
  let s2 =
    hxy (qdiv eps x2) (qlt_to_QltT { qnum = Z0; qden = XH } (qdiv eps x2))
  in
  let ExistT (x3, _) = s2 in
  ExistT (x3, (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_sin x) n) (projT1 (cauchy_real_sin y) n)))
    eps))

(** val real_cos_eq_compat : real -> real -> real_eq -> real_eq **)

let real_cos_eq_compat x y hxy eps _ =
  let s = real_norm_bounded x in
  let ExistT (x0, a) = s in
  let Pair (q0, _) = a in
  let s0 = real_norm_bounded y in
  let ExistT (x1, a0) = s0 in
  let Pair (q1, _) = a0 in
  let b = qplus x0 x1 in
  let hBT =
    qltT_leT' { qnum = Z0; qden = XH } (qplus x0 x1)
      (qltT_plus_pos_r x0 x1 q0 q1)
  in
  let s1 = exp_series_arch b hBT in
  let ExistT (x2, _) = s1 in
  let s2 =
    hxy (qdiv eps x2) (qlt_to_QltT { qnum = Z0; qden = XH } (qdiv eps x2))
  in
  let ExistT (x3, _) = s2 in
  ExistT (x3, (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_cos x) n) (projT1 (cauchy_real_cos y) n)))
    eps))

(** val real_cos_strict_decr :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_cos_strict_decr x y h0 hXY h2 =
  let ExistT (_, a) = h0 in
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  let ExistT (x1, a0) = hXY in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (_, a1) = h2 in
  let Pair (_, s1) = a1 in
  let ExistT (x3, _) = s1 in
  let eps =
    qmult (q_pow x1 (S (S O)))
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XI XH)));
        qden = XH })
  in
  let heps_pos =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult (q_pow x1 (S (S O)))
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XI XH)));
          qden = XH }))
  in
  ExistT (eps, (Pair (heps_pos, (ExistT
  ((Nat.max (S (S O)) (Nat.max x2 (Nat.max x0 x3))), (fun n _ ->
  qlt_to_QltT eps
    (qminus (projT1 (cauchy_real_cos x) n) (projT1 (cauchy_real_cos y) n))))))))

(** val cos_partial_cauchy :
    q -> q -> (nat, nat -> nat -> __ -> __ -> qltT) sigT **)

let cos_partial_cauchy x eps =
  let s =
    sc_cos_partial_cauchy_bounded (qabs x) eps
      (qle_to_QleT' { qnum = Z0; qden = XH } (qabs x))
      (qlt_to_QltT { qnum = Z0; qden = XH } eps)
  in
  let ExistT (x0, q0) = s in
  ExistT (x0, (fun m n _ _ ->
  q0 m n (natLe_lift x0 m) (natLe_lift x0 n) x
    (qle_to_QleT' (qabs x) (qabs x))))

(** val cos_K1_eps : q -> q -> nat **)

let cos_K1_eps m eps =
  projT1
    (cos_partial_cauchy m
      (qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH }))

(** val cos_testA_eps : q -> q -> bool **)

let cos_testA_eps m eps =
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (cos_partial_cauchy m d4) in
  qlt_bool
    (qplus (cos_partial k1 m) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    { qnum = Z0; qden = XH }

(** val cos_testB_eps : q -> q -> bool **)

let cos_testB_eps m eps =
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (cos_partial_cauchy m d4) in
  qlt_bool (qmult { qnum = (Zpos (XO XH)); qden = XH } d4) (cos_partial k1 m)

(** val cos_testA_eps_true_lt : q -> q -> real_lt **)

let cos_testA_eps_true_lt m eps =
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (cos_partial_cauchy m d4) in
  let q0 = cos_partial k1 m in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qopp q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT ((qminus (qopp q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT (k1, (fun n _ ->
  qlt_to_QltT
    (qminus (qopp q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 real_zero n) (projT1 (cauchy_real_cos (real_const m)) n))))))))

(** val cos_testB_eps_true_gt : q -> q -> real_lt **)

let cos_testB_eps_true_gt m eps =
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (cos_partial_cauchy m d4) in
  let q0 = cos_partial k1 m in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus q0 { qnum = Z0; qden = XH })
        (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus q0 { qnum = Z0; qden = XH })
     (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT (k1, (fun n _ ->
  qlt_to_QltT
    (qminus (qminus q0 { qnum = Z0; qden = XH })
      (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 (cauchy_real_cos (real_const m)) n) (projT1 real_zero n))))))))

(** val cos_scan :
    q -> q -> q -> nat -> (((q, q) prod, qltT) sigT, bool) prod **)

let rec cos_scan a b eps = function
| O -> Pair ((ExistT ((Pair (a, b)), (qlt_to_QltT a b))), True)
| S n' ->
  let m = log_m_eps a b in
  (match cos_testA_eps m eps with
   | True -> cos_scan a m eps n'
   | False ->
     (match cos_testB_eps m eps with
      | True -> cos_scan m b eps n'
      | False -> Pair ((ExistT ((Pair (a, b)), (qlt_to_QltT a b))), False)))

(** val cos_scan_spec :
    q -> q -> q -> nat -> real_lt -> real_lt -> ((bool id, (real_lt, (real_lt,
    qeqT) and0) and0) and0, (bool id, nat -> __ -> qleT') and0) or0 **)

let rec cos_scan_spec a b eps n hla hrb =
  match n with
  | O ->
    Inl (Pair (Id_refl, (Pair (hla, (Pair (hrb,
      (qeq_imp_qeqT (qminus b a)
        (qmult (qminus b a) { qnum = (Zpos XH); qden = XH }))))))))
  | S n0 ->
    let b0 = cos_testA_eps (log_m_eps a b) eps in
    (match b0 with
     | True ->
       let hmb = cos_testA_eps_true_lt (log_m_eps a b) eps in
       let hIH = cos_scan_spec a (log_m_eps a b) eps n0 hla hmb in
       (match hIH with
        | Inl a0 ->
          Inl
            (let Pair (i, a1) = a0 in
             let Pair (r, a2) = a1 in
             let Pair (r0, _) = a2 in
             Pair (i, (Pair (r, (Pair (r0,
             (qeq_imp_qeqT
               (qminus
                 (snd (projT1 (fst (cos_scan a (log_m_eps a b) eps n0))))
                 (fst (projT1 (fst (cos_scan a (log_m_eps a b) eps n0)))))
               (qmult (qminus b a)
                 (q_pow
                   (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                     XH)); qden = XH })
                   (S n0))))))))))
        | Inr a0 -> Inr a0)
     | False ->
       let b1 = cos_testB_eps (log_m_eps a b) eps in
       (match b1 with
        | True ->
          let ham = cos_testB_eps_true_gt (log_m_eps a b) eps in
          let hIH = cos_scan_spec (log_m_eps a b) b eps n0 ham hrb in
          (match hIH with
           | Inl a0 ->
             Inl
               (let Pair (i, a1) = a0 in
                let Pair (r, a2) = a1 in
                let Pair (r0, _) = a2 in
                Pair (i, (Pair (r, (Pair (r0,
                (qeq_imp_qeqT
                  (qminus
                    (snd (projT1 (fst (cos_scan (log_m_eps a b) b eps n0))))
                    (fst (projT1 (fst (cos_scan (log_m_eps a b) b eps n0)))))
                  (qmult (qminus b a)
                    (q_pow
                      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                        XH)); qden = XH })
                      (S n0))))))))))
           | Inr a0 -> Inr a0)
        | False ->
          Inr (Pair (Id_refl, (fun k _ ->
            qle_to_QleT'
              (qabs
                (qminus
                  (projT1
                    (cauchy_real_cos
                      (real_const
                        (log_m_eps
                          (fst
                            (projT1
                              (fst (Pair ((ExistT ((Pair (a, b)),
                                (qlt_to_QltT a b))), False)))))
                          (snd
                            (projT1
                              (fst (Pair ((ExistT ((Pair (a, b)),
                                (qlt_to_QltT a b))), False))))))))
                    k)
                  (projT1 real_zero k)))
              (qmult { qnum = (Zpos (XI XH)); qden = XH } (log_d4_eps eps)))))))

(** val approx_span_pt_cos :
    q -> q -> q -> q -> real_lt -> real_lt -> (nat -> qleT') -> real_lt ->
    real_lt -> (nat, __) sigT **)

let approx_span_pt_cos a b _ _ hla hrb _ hpos hlt2 =
  let hm2 =
    real_lt_trans (real_const (log_m_eps a b)) (real_const b)
      (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (real_const_lt (log_m_eps a b) b) hlt2
  in
  let hcm =
    real_cos_strict_decr (real_const a) (real_const (log_m_eps a b)) hpos
      (real_const_lt a (log_m_eps a b)) hm2
  in
  let h0m =
    real_lt_trans real_zero (real_const a) (real_const (log_m_eps a b)) hpos
      (real_const_lt a (log_m_eps a b))
  in
  let hcb =
    real_cos_strict_decr (real_const (log_m_eps a b)) (real_const b) h0m
      (real_const_lt (log_m_eps a b) b) hlt2
  in
  let s = real_lt_pt_lt real_zero (cauchy_real_cos (real_const a)) hla in
  let ExistT (x, _) = s in
  let s0 = real_lt_pt_lt (cauchy_real_cos (real_const b)) real_zero hrb in
  let ExistT (x0, _) = s0 in
  let s1 =
    real_lt_pt_lt (cauchy_real_cos (real_const (log_m_eps a b)))
      (cauchy_real_cos (real_const a)) hcm
  in
  let ExistT (x1, _) = s1 in
  let s2 =
    real_lt_pt_lt (cauchy_real_cos (real_const b))
      (cauchy_real_cos (real_const (log_m_eps a b))) hcb
  in
  let ExistT (x2, _) = s2 in
  ExistT ((Nat.max (Nat.max x x0) (Nat.max x1 x2)), __)

(** val cos_abs_lift : q -> q -> q -> nat -> real_lt **)

let cos_abs_lift m m0 _UU03b3_ n0 =
  real_abs_diff_le_lift (cauchy_real_cos (real_const m)) real_zero m0 _UU03b3_
    n0

(** val approx_def_test_cos : q -> q -> nat -> real_lt **)

let approx_def_test_cos mN eps n0 =
  let hlift =
    cos_abs_lift mN
      (qmult { qnum = (Zpos (XI XH)); qden = XH } (log_d4_eps eps))
      (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) n0
  in
  real_lt_trans
    (real_abs
      (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero)))
    (real_const
      (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH })))
    (real_const eps) hlift
    (real_const_lt
      (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }))
      eps)

(** val approx_root_cos : q -> (q, (qltT, (qltT, real_lt) and0) and0) sigT **)

let approx_root_cos eps =
  let a0 =
    qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH }
  in
  let b0 =
    qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI XH));
      qden = XH }
  in
  let b = qplus (qabs a0) (qabs b0) in
  let s = exp_series_arch b (qle_to_QleT' { qnum = Z0; qden = XH } b) in
  let ExistT (x, a) = s in
  let Pair (_, q0) = a in
  let d = qmult (qminus b0 a0) x in
  let s0 = q_pow_arch d eps in
  let ExistT (x0, _) = s0 in
  let o =
    cos_scan_spec a0 b0 eps x0 real_cos_three_halves_pos
      real_cos_five_thirds_neg
  in
  (match o with
   | Inl a1 ->
     let Pair (_, a2) = a1 in
     let Pair (r, a3) = a2 in
     let Pair (r0, _) = a3 in
     let abN = projT1 (fst (cos_scan a0 b0 eps x0)) in
     let aN = fst abN in
     let bN = snd abN in
     let mN = log_m_eps aN bN in
     let hpos_aN = ExistT ({ qnum = (Zpos XH); qden = XH }, (Pair
       ((qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }),
       (ExistT (O, (fun n _ ->
       qlt_to_QltT { qnum = (Zpos XH); qden = XH }
         (qminus (projT1 (real_const aN) n) (projT1 real_zero n))))))))
     in
     let hlt2_bN = real_const_lt bN { qnum = (Zpos (XO XH)); qden = XH } in
     let s1 = approx_span_pt_cos aN bN b x r r0 q0 hpos_aN hlt2_bN in
     let ExistT (x1, _) = s1 in
     ExistT (mN, (Pair
     ((qlt_to_QltT
        (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
          qden = XH })
        (log_m_eps aN bN)),
     (Pair
     ((qlt_to_QltT (log_m_eps aN bN)
        (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI
          XH)); qden = XH })),
     (let hlift =
        cos_abs_lift mN (qmult (qminus bN aN) x)
          (qdiv
            (qminus eps
              (qmult d
                (q_pow
                  (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                    XH)); qden = XH })
                  x0)))
            { qnum = (Zpos (XO XH)); qden = XH })
          x1
      in
      real_lt_trans
        (real_abs
          (real_plus (cauchy_real_cos (real_const mN)) (real_opp real_zero)))
        (real_const
          (qplus (qmult (qminus bN aN) x)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x0)))
              { qnum = (Zpos (XO XH)); qden = XH })))
        (real_const eps) hlift
        (real_const_lt
          (qplus (qmult (qminus bN aN) x)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x0)))
              { qnum = (Zpos (XO XH)); qden = XH }))
          eps)))))))
   | Inr _ ->
     let abN = projT1 (fst (cos_scan a0 b0 eps x0)) in
     let mN = log_m_eps (fst abN) (snd abN) in
     let n0 = cos_K1_eps (log_m_eps (fst abN) (snd abN)) eps in
     ExistT (mN, (Pair
     ((qlt_to_QltT
        (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
          qden = XH })
        (log_m_eps (fst abN) (snd abN))),
     (Pair
     ((qlt_to_QltT (log_m_eps (fst abN) (snd abN))
        (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI
          XH)); qden = XH })),
     (approx_def_test_cos mN eps n0)))))))

(** val cos_zero_seq : nat -> q **)

let cos_zero_seq n =
  projT1 (approx_root_cos (log_eps n))

(** val cos_root_pt_bound : nat -> (nat, __) sigT **)

let cos_root_pt_bound n =
  let s = approx_root_cos (log_eps n) in
  let ExistT (x, a) = s in
  let Pair (_, a0) = a in
  let Pair (_, r) = a0 in
  let s0 =
    real_lt_pt_lt
      (real_abs
        (real_plus (cauchy_real_cos (real_const x)) (real_opp real_zero)))
      (real_const (log_eps n)) r
  in
  let ExistT (x0, _) = s0 in ExistT (x0, __)

(** val cos_seq_cauchy :
    q -> qltT -> (nat, nat -> nat -> __ -> __ -> qltT) sigT **)

let cos_seq_cauchy eps _ =
  let s =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv eps { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x, _) = s in
  ExistT ((S x), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (cos_zero_seq m) (cos_zero_seq n))) eps))

(** val cos_seq_cauchyT :
    q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT **)

let cos_seq_cauchyT eps hepsT =
  let s = cos_seq_cauchy eps hepsT in
  let ExistT (x, q0) = s in ExistT (x, (fun m n _ _ -> q0 m n __ __))

(** val cos_pi_half : real **)

let cos_pi_half =
  ExistT (cos_zero_seq, cos_seq_cauchyT)

(** val real_cos_pi_half_zero : real_eq **)

let real_cos_pi_half_zero eps _ =
  let s =
    exp_series_arch { qnum = (Zpos (XO XH)); qden = XH }
      (qltT_leT' { qnum = Z0; qden = XH } { qnum = (Zpos (XO XH)); qden = XH }
        qltT_0_2)
  in
  let ExistT (x, _) = s in
  let s0 =
    cos_seq_cauchy (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x)))
  in
  let ExistT (x0, _) = s0 in
  let s1 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
  in
  let ExistT (x1, _) = s1 in
  let n0 = Nat.max x0 (S x1) in
  let s2 = cos_root_pt_bound n0 in
  let ExistT (x2, _) = s2 in
  ExistT ((Nat.max (S (S O)) (Nat.max x0 x2)), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_cos cos_pi_half) n) (projT1 real_zero n)))
    eps))

(** val real_pi_geom : real **)

let real_pi_geom =
  real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) cos_pi_half

(** val cos_eq_zero_diag_bound : real -> real_eq -> q -> (nat, __) sigT **)

let cos_eq_zero_diag_bound _ hw delta =
  let s = hw delta (qlt_to_QltT { qnum = Z0; qden = XH } delta) in
  let ExistT (x, _) = s in ExistT (x, __)

(** val real_lt_lower_pt : q -> real -> real_lt -> (nat, __) sigT **)

let real_lt_lower_pt _ _ = function
| ExistT (_, a) ->
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val real_lt_upper_pt : q -> real -> real_lt -> (nat, __) sigT **)

let real_lt_upper_pt _ _ = function
| ExistT (_, a) ->
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val real_pi_leibniz_lt_ten_thirds : real_lt **)

let real_pi_leibniz_lt_ten_thirds =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XI (XI
       XH)))))); qden = XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XI
         (XI XH)))))); qden = XH })),
    (ExistT ((S (S O)), (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO (XO (XI (XI (XI
        XH)))))); qden = XH })
      (qminus
        (qdiv { qnum = (Zpos (XO (XI (XO XH)))); qden = XH } { qnum = (Zpos
          (XI XH)); qden = XH })
        (qmult lp_four (lp_odd n)))))))))

(** val cos_pi_half_unique_widened :
    real -> real_lt -> real_lt -> real_eq -> real_eq **)

let cos_pi_half_unique_widened w hlow hup hw0 eps _ =
  let s =
    real_lt_lower_pt
      (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
        qden = XH })
      w hlow
  in
  let ExistT (x, _) = s in
  let s0 = real_lt_upper_pt { qnum = (Zpos (XO XH)); qden = XH } w hup in
  let ExistT (x0, _) = s0 in
  let s1 =
    cos_eq_zero_diag_bound w hw0
      (qdiv eps { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x1, _) = s1 in
  let s2 =
    cos_eq_zero_diag_bound cos_pi_half real_cos_pi_half_zero
      (qdiv eps { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x2, _) = s2 in
  let s3 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv eps { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x3, _) = s3 in
  let a = Nat.max x (Nat.max x0 (Nat.max x1 x2)) in
  ExistT ((Nat.max (S (S O)) (Nat.max a (S x3))), (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 w n) (projT1 cos_pi_half n))) eps))

(** val real_half_const_three : real_eq **)

let real_half_const_three =
  real_eq_of_zero_diff
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_const { qnum = (Zpos (XI XH)); qden = XH }))
    (real_const
      (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
        qden = XH }))

(** val real_half_const_ten_thirds : real_eq **)

let real_half_const_ten_thirds =
  real_eq_of_zero_diff
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_const
        (qdiv { qnum = (Zpos (XO (XI (XO XH)))); qden = XH } { qnum = (Zpos
          (XI XH)); qden = XH })))
    (real_const
      (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI XH));
        qden = XH }))

(** val real_half_pos : real_lt **)

let real_half_pos =
  real_const_lt { qnum = Z0; qden = XH }
    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })

(** val real_half_pi_leibniz_comm : real_eq **)

let real_half_pi_leibniz_comm =
  real_mult_comm
    (real_const
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH }))
    cauchy_real_pi_leibniz

(** val real_pi_leibniz_half_lower : real_lt **)

let real_pi_leibniz_half_lower =
  real_eq_lt_lt
    (real_const
      (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
        qden = XH }))
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_const { qnum = (Zpos (XI XH)); qden = XH }))
    (real_mult cauchy_real_pi_leibniz
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    (real_eq_sym
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_const { qnum = (Zpos (XI XH)); qden = XH }))
      (real_const
        (qdiv { qnum = (Zpos (XI XH)); qden = XH } { qnum = (Zpos (XO XH));
          qden = XH }))
      real_half_const_three)
    (real_lt_eq_lt
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_const { qnum = (Zpos (XI XH)); qden = XH }))
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        cauchy_real_pi_leibniz)
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      (real_lt_mult_compat (real_const { qnum = (Zpos (XI XH)); qden = XH })
        cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        real_half_pos real_pi_leibniz_gt_three)
      real_half_pi_leibniz_comm)

(** val real_pi_leibniz_half_upper : real_lt **)

let real_pi_leibniz_half_upper =
  real_eq_lt_lt
    (real_mult cauchy_real_pi_leibniz
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      cauchy_real_pi_leibniz)
    (real_const
      (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI XH));
        qden = XH }))
    (real_eq_sym
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        cauchy_real_pi_leibniz)
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      real_half_pi_leibniz_comm)
    (real_lt_eq_lt
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        cauchy_real_pi_leibniz)
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_const
          (qdiv { qnum = (Zpos (XO (XI (XO XH)))); qden = XH } { qnum = (Zpos
            (XI XH)); qden = XH })))
      (real_const
        (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI
          XH)); qden = XH }))
      (real_lt_mult_compat cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos (XO (XI (XO XH)))); qden = XH } { qnum = (Zpos
            (XI XH)); qden = XH }))
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        real_half_pos real_pi_leibniz_lt_ten_thirds)
      real_half_const_ten_thirds)

(** val real_two_half_one : real_eq **)

let real_two_half_one =
  real_eq_of_zero_diff
    (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    real_one

(** val real_double_half_cancel : real -> real_eq **)

let real_double_half_cancel x =
  real_eq_trans
    (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (real_mult x
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))))
    (real_mult (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    x
    (real_mult_assoc (real_const { qnum = (Zpos (XO XH)); qden = XH }) x
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    (real_eq_trans
      (real_mult
        (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      (real_mult
        (real_mult x (real_const { qnum = (Zpos (XO XH)); qden = XH }))
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      x
      (RealSetoid.real_eq_mult_compat
        (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_mult x (real_const { qnum = (Zpos (XO XH)); qden = XH }))
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_mult_comm (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
        (real_eq_refl
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))))
      (real_eq_trans
        (real_mult
          (real_mult x (real_const { qnum = (Zpos (XO XH)); qden = XH }))
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH })))
        (real_mult x
          (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
            (real_const
              (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                qden = XH }))))
        x
        (real_eq_sym
          (real_mult x
            (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
              (real_const
                (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                  qden = XH }))))
          (real_mult
            (real_mult x (real_const { qnum = (Zpos (XO XH)); qden = XH }))
            (real_const
              (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                qden = XH })))
          (real_mult_assoc x (real_const { qnum = (Zpos (XO XH)); qden = XH })
            (real_const
              (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                qden = XH }))))
        (real_eq_trans
          (real_mult x
            (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
              (real_const
                (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                  qden = XH }))))
          (real_mult x real_one) x
          (RealSetoid.real_eq_mult_compat x
            (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
              (real_const
                (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                  qden = XH })))
            x real_one (real_eq_refl x) real_two_half_one)
          (real_eq_of_zero_diff (real_mult x real_one) x))))

(** val sc_add_sin_err_bound :
    q -> q -> qleT' -> qltT -> (nat, q -> q -> nat -> natLe -> qleT' -> qleT'
    -> qltT) sigT **)

let sc_add_sin_err_bound b eps hB hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let s0 = exp_series_arch b hB in
  let ExistT (x0, _) = s0 in
  let p =
    qmult
      (qmult
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH })
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qmult x0
        (qmult (qdiv (q_pow b x) (q_fact x))
          (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
            XH })))
  in
  let s1 = arch_decay p eps (qle_to_QleT' { qnum = Z0; qden = XH } p) hep in
  let ExistT (x1, _) = s1 in
  ExistT ((add x (S x1)), (fun x2 y n _ _ _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (qminus (sin_partial (mul (S (S O)) n) (qplus x2 y))
          (qmult (sin_partial n x2) (cos_partial n y)))
        (qmult (cos_partial n x2) (sin_partial n y))))
    eps))

(** val rs_add_sin : real -> real -> real_eq **)

let rs_add_sin x y eps heps =
  let s = real_norm_bounded x in
  let ExistT (x0, a) = s in
  let Pair (q0, _) = a in
  let s0 = real_norm_bounded y in
  let ExistT (x1, a0) = s0 in
  let Pair (q1, _) = a0 in
  let m = qplus x0 x1 in
  let hMposT = qltT_plus_pos_r x0 x1 q0 q1 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let heps3T =
    qltT_div_pos eps { qnum = (Zpos (XI XH)); qden = XH } heps qltT_0_3
  in
  let s1 =
    sc_sin_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT heps3T
  in
  let ExistT (x2, _) = s1 in
  let s2 =
    sc_add_sin_err_bound m (qdiv eps { qnum = (Zpos (XI XH)); qden = XH })
      hMnonnegT heps3T
  in
  let ExistT (x3, _) = s2 in
  ExistT ((Nat.max x2 x3), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_sin (real_plus x y)) n)
        (projT1
          (real_plus (real_mult (cauchy_real_sin x) (cauchy_real_cos y))
            (real_mult (cauchy_real_cos x) (cauchy_real_sin y)))
          n)))
    eps))

(** val sc_add_cos_err_bound :
    q -> q -> qleT' -> qltT -> (nat, q -> q -> nat -> natLe -> qleT' -> qleT'
    -> qltT) sigT **)

let sc_add_cos_err_bound b eps hB hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let s0 = exp_series_arch b hB in
  let ExistT (x0, _) = s0 in
  let p =
    qmult
      (qplus
        (qmult
          (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
            XH })
          (qplus
            (qplus
              (qplus
                (qplus
                  (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH);
                    qden = XH })
                  { qnum = (Zpos XH); qden = XH })
                { qnum = (Zpos XH); qden = XH })
              { qnum = (Zpos XH); qden = XH })
            { qnum = (Zpos XH); qden = XH }))
        { qnum = (Zpos XH); qden = XH })
      (qmult x0 (qdiv (q_pow b x) (q_fact x)))
  in
  let s1 = arch_decay p eps (qle_to_QleT' { qnum = Z0; qden = XH } p) hep in
  let ExistT (x1, _) = s1 in
  ExistT ((add x (S x1)), (fun x2 y n _ _ _ ->
  qlt_to_QltT
    (qabs
      (qplus
        (qminus (cos_partial (mul (S (S O)) n) (qplus x2 y))
          (qmult (cos_partial n x2) (cos_partial n y)))
        (qmult (sin_partial n x2) (sin_partial n y))))
    eps))

(** val rs_add_cos : real -> real -> real_eq **)

let rs_add_cos x y eps heps =
  let s = real_norm_bounded x in
  let ExistT (x0, a) = s in
  let Pair (q0, _) = a in
  let s0 = real_norm_bounded y in
  let ExistT (x1, a0) = s0 in
  let Pair (q1, _) = a0 in
  let m = qplus x0 x1 in
  let hMposT = qltT_plus_pos_r x0 x1 q0 q1 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let heps3T =
    qltT_div_pos eps { qnum = (Zpos (XI XH)); qden = XH } heps qltT_0_3
  in
  let s1 =
    sc_cos_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT heps3T
  in
  let ExistT (x2, _) = s1 in
  let s2 =
    sc_add_cos_err_bound m (qdiv eps { qnum = (Zpos (XI XH)); qden = XH })
      hMnonnegT heps3T
  in
  let ExistT (x3, _) = s2 in
  ExistT ((Nat.max x2 x3), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_cos (real_plus x y)) n)
        (projT1
          (real_plus (real_mult (cauchy_real_cos x) (cauchy_real_cos y))
            (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin y))))
          n)))
    eps))

(** val arctan_term : nat -> q -> q **)

let arctan_term k x =
  qmult (q_pow { qnum = (Zneg XH); qden = XH } k)
    (qdiv (q_pow x (add (mul (S (S O)) k) (S O))) { qnum =
      (Z.of_nat (add (mul (S (S O)) k) (S O))); qden = XH })

(** val arctan_partial : nat -> q -> q **)

let rec arctan_partial n x =
  match n with
  | O -> arctan_term O x
  | S m -> qplus (arctan_partial m x) (arctan_term (S m) x)

(** val cauchy_real_arctan : real -> (nat -> qleT') -> real **)

let cauchy_real_arctan x _ =
  let u = projT1 x in
  let hu = projT2 x in
  ExistT ((fun n -> arctan_partial n (u n)), (fun eps heps ->
  let s = q_arch_inv (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) in
  let ExistT (x0, _) = s in
  let l = { qnum = (Z.of_nat (S x0)); qden = XH } in
  let hepsL =
    qltT_div_pos eps (qmult { qnum = (Zpos (XI XH)); qden = XH } l) heps
      (qmult_ltT_0_compat { qnum = (Zpos (XI XH)); qden = XH } l qltT_0_3
        (qlt_to_QltT { qnum = Z0; qden = XH } l))
  in
  let s0 = hu (qdiv eps (qmult { qnum = (Zpos (XI XH)); qden = XH } l)) hepsL
  in
  let ExistT (x1, _) = s0 in
  ExistT ((Nat.max x0 x1), (fun m n _ _ ->
  qlt_to_QltT
    (qabs (qminus (arctan_partial m (u m)) (arctan_partial n (u n)))) eps))))

(** val real_sin_eq_cos_cos_double_zero : real -> real_eq -> real_eq **)

let real_sin_eq_cos_cos_double_zero x hsc =
  let hsq =
    RealSetoid.real_eq_mult_compat (cauchy_real_sin x) (cauchy_real_sin x)
      (cauchy_real_cos x) (cauchy_real_cos x) hsc hsc
  in
  let hdiff =
    real_eq_trans
      (real_plus (real_mult (cauchy_real_cos x) (cauchy_real_cos x))
        (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x))))
      (real_plus (real_mult (cauchy_real_sin x) (cauchy_real_sin x))
        (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x))))
      real_zero
      (RealSetoid.real_eq_plus_compat
        (real_mult (cauchy_real_cos x) (cauchy_real_cos x))
        (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x)))
        (real_mult (cauchy_real_sin x) (cauchy_real_sin x))
        (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x)))
        (real_eq_sym (real_mult (cauchy_real_sin x) (cauchy_real_sin x))
          (real_mult (cauchy_real_cos x) (cauchy_real_cos x)) hsq)
        (real_eq_refl
          (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x)))))
      (real_plus_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x)))
  in
  real_eq_trans (cauchy_real_cos (real_plus x x))
    (real_plus (real_mult (cauchy_real_cos x) (cauchy_real_cos x))
      (real_opp (real_mult (cauchy_real_sin x) (cauchy_real_sin x))))
    real_zero (rs_add_cos x x) hdiff

(** val real_two_mult_plus : real -> real_eq **)

let real_two_mult_plus x =
  real_eq_of_zero_diff
    (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
    (real_plus x x)

(** val real_sin_eq_cos_cos_two_zero : real -> real_eq -> real_eq **)

let real_sin_eq_cos_cos_two_zero x hsc =
  real_eq_trans
    (cauchy_real_cos
      (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x))
    (cauchy_real_cos (real_plus x x)) real_zero
    (real_cos_eq_compat
      (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
      (real_plus x x) (real_two_mult_plus x))
    (real_sin_eq_cos_cos_double_zero x hsc)

(** val atan1_pt_bound : nat -> qleT' **)

let atan1_pt_bound n =
  qle_to_QleT' (qabs (projT1 (real_const { qnum = (Zpos XH); qden = XH }) n))
    { qnum = (Zpos XH); qden = XH }

(** val arctan_one_real : real **)

let arctan_one_real =
  cauchy_real_arctan (real_const { qnum = (Zpos XH); qden = XH })
    atan1_pt_bound

(** val real_const_half_four : real_eq **)

let real_const_half_four =
  real_eq_of_zero_diff
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_const { qnum = (Zpos (XO (XO XH))); qden = XH }))
    (real_const { qnum = (Zpos (XO XH)); qden = XH })

(** val real_half_four_mult : real -> real_eq **)

let real_half_four_mult x =
  real_eq_trans
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_mult (real_const { qnum = (Zpos (XO (XO XH))); qden = XH }) x))
    (real_mult
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_const { qnum = (Zpos (XO (XO XH))); qden = XH }))
      x)
    (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) x)
    (real_mult_assoc
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_const { qnum = (Zpos (XO (XO XH))); qden = XH }) x)
    (RealSetoid.real_eq_mult_compat
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_const { qnum = (Zpos (XO (XO XH))); qden = XH }))
      x (real_const { qnum = (Zpos (XO XH)); qden = XH }) x
      real_const_half_four (real_eq_refl x))

(** val channel_cos_double_zero : real_eq -> real_eq **)

let channel_cos_double_zero hsc =
  real_sin_eq_cos_cos_two_zero arctan_one_real hsc

(** val channel_w_eq_two_theta : real_eq -> real_eq **)

let channel_w_eq_two_theta h4 =
  real_eq_trans
    (let ExistT (x, c) = cauchy_real_pi_leibniz in
     let ExistT (x0, c0) =
       real_const
         (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
           XH })
     in
     ExistT ((fun n -> qmult (x n) (x0 n)), (fun eps _ ->
     let ExistT (x1, a) = real_norm_bounded (ExistT (x, c)) in
     let Pair (_, q0) = a in
     let ExistT (x2, a0) = real_norm_bounded (ExistT (x0, c0)) in
     let Pair (_, q1) = a0 in
     let ExistT (x3, q2) =
       c
         (qdiv eps
           (qmult { qnum = (Zpos (XO XH)); qden = XH }
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
         (qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv eps
             (qmult { qnum = (Zpos (XO XH)); qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))))
     in
     let ExistT (x4, q3) =
       c0
         (qdiv eps
           (qmult { qnum = (Zpos (XO XH)); qden = XH }
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
         (qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv eps
             (qmult { qnum = (Zpos (XO XH)); qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
     in
     ExistT ((max x3 x4), (fun m n _ _ ->
     qleT'_ltT_ltT (qabs (qminus (qmult (x m) (x0 m)) (qmult (x n) (x0 n))))
       (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
         (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n)))))
       eps
       (qle_to_QleT' (qabs (qminus (qmult (x m) (x0 m)) (qmult (x n) (x0 n))))
         (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n))))))
       (qltT_leT'_ltT
         (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n)))))
         (qplus
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))))
         eps
         (qltT_plus_ltT (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n))))
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))))
           (qleT'_mult_ltT_compat (qabs (x m))
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
             (qabs (qminus (x0 m) (x0 n)))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
             (qlt_to_QltT { qnum = Z0; qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))
             (qabs_nonnegT (qminus (x0 m) (x0 n)))
             (qleT'_trans (qabs (x m)) x1
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)) (q0 m)
               (qle_to_QleT' x1
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
             (q3 m n (natLe_lift x4 m) (natLe_lift x4 n)))
           (qleT'_mult_ltT_compat (qabs (x0 n))
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
             (qabs (qminus (x m) (x n)))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
             (qlt_to_QltT { qnum = Z0; qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))
             (qabs_nonnegT (qminus (x m) (x n)))
             (qleT'_trans (qabs (x0 n)) x2
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)) (q1 n)
               (qle_to_QleT' x2
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
             (q2 m n (natLe_lift x3 m) (natLe_lift x3 n))))
         (qeq_leT'
           (qplus
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))))
           eps)))))))
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      cauchy_real_pi_leibniz)
    (let ExistT (x, c) = real_const { qnum = (Zpos (XO XH)); qden = XH } in
     let ExistT (x0, c0) = arctan_one_real in
     ExistT ((fun n -> qmult (x n) (x0 n)), (fun eps _ ->
     let ExistT (x1, a) = real_norm_bounded (ExistT (x, c)) in
     let Pair (_, q0) = a in
     let ExistT (x2, a0) = real_norm_bounded (ExistT (x0, c0)) in
     let Pair (_, q1) = a0 in
     let ExistT (x3, q2) =
       c
         (qdiv eps
           (qmult { qnum = (Zpos (XO XH)); qden = XH }
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
         (qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv eps
             (qmult { qnum = (Zpos (XO XH)); qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))))
     in
     let ExistT (x4, q3) =
       c0
         (qdiv eps
           (qmult { qnum = (Zpos (XO XH)); qden = XH }
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
         (qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv eps
             (qmult { qnum = (Zpos (XO XH)); qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
     in
     ExistT ((max x3 x4), (fun m n _ _ ->
     qleT'_ltT_ltT (qabs (qminus (qmult (x m) (x0 m)) (qmult (x n) (x0 n))))
       (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
         (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n)))))
       eps
       (qle_to_QleT' (qabs (qminus (qmult (x m) (x0 m)) (qmult (x n) (x0 n))))
         (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n))))))
       (qltT_leT'_ltT
         (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n)))))
         (qplus
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))))
         eps
         (qltT_plus_ltT (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n))))
           (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))))
           (qleT'_mult_ltT_compat (qabs (x m))
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
             (qabs (qminus (x0 m) (x0 n)))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
             (qlt_to_QltT { qnum = Z0; qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))
             (qabs_nonnegT (qminus (x0 m) (x0 n)))
             (qleT'_trans (qabs (x m)) x1
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)) (q0 m)
               (qle_to_QleT' x1
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
             (q3 m n (natLe_lift x4 m) (natLe_lift x4 n)))
           (qleT'_mult_ltT_compat (qabs (x0 n))
             (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
             (qabs (qminus (x m) (x n)))
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
             (qlt_to_QltT { qnum = Z0; qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))
             (qabs_nonnegT (qminus (x m) (x n)))
             (qleT'_trans (qabs (x0 n)) x2
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)) (q1 n)
               (qle_to_QleT' x2
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
             (q2 m n (natLe_lift x3 m) (natLe_lift x3 n))))
         (qeq_leT'
           (qplus
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))))
           eps)))))))
    (real_mult_comm cauchy_real_pi_leibniz
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    (real_eq_trans
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        cauchy_real_pi_leibniz)
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_mult (real_const { qnum = (Zpos (XO (XO XH))); qden = XH })
          arctan_one_real))
      (let ExistT (x, c) = real_const { qnum = (Zpos (XO XH)); qden = XH } in
       let ExistT (x0, c0) = arctan_one_real in
       ExistT ((fun n -> qmult (x n) (x0 n)), (fun eps _ ->
       let ExistT (x1, a) = real_norm_bounded (ExistT (x, c)) in
       let Pair (_, q0) = a in
       let ExistT (x2, a0) = real_norm_bounded (ExistT (x0, c0)) in
       let Pair (_, q1) = a0 in
       let ExistT (x3, q2) =
         c
           (qdiv eps
             (qmult { qnum = (Zpos (XO XH)); qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
           (qlt_to_QltT { qnum = Z0; qden = XH }
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))))
       in
       let ExistT (x4, q3) =
         c0
           (qdiv eps
             (qmult { qnum = (Zpos (XO XH)); qden = XH }
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
           (qlt_to_QltT { qnum = Z0; qden = XH }
             (qdiv eps
               (qmult { qnum = (Zpos (XO XH)); qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
       in
       ExistT ((max x3 x4), (fun m n _ _ ->
       qleT'_ltT_ltT (qabs (qminus (qmult (x m) (x0 m)) (qmult (x n) (x0 n))))
         (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
           (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n)))))
         eps
         (qle_to_QleT'
           (qabs (qminus (qmult (x m) (x0 m)) (qmult (x n) (x0 n))))
           (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
             (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n))))))
         (qltT_leT'_ltT
           (qplus (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
             (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n)))))
           (qplus
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))))
           eps
           (qltT_plus_ltT (qmult (qabs (x m)) (qabs (qminus (x0 m) (x0 n))))
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
             (qmult (qabs (x0 n)) (qabs (qminus (x m) (x n))))
             (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))))
             (qleT'_mult_ltT_compat (qabs (x m))
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
               (qabs (qminus (x0 m) (x0 n)))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
               (qlt_to_QltT { qnum = Z0; qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))
               (qabs_nonnegT (qminus (x0 m) (x0 n)))
               (qleT'_trans (qabs (x m)) x1
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)) (q0 m)
                 (qle_to_QleT' x1
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))))
               (q3 m n (natLe_lift x4 m) (natLe_lift x4 n)))
             (qleT'_mult_ltT_compat (qabs (x0 n))
               (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
               (qabs (qminus (x m) (x n)))
               (qdiv eps
                 (qmult { qnum = (Zpos (XO XH)); qden = XH }
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
               (qlt_to_QltT { qnum = Z0; qden = XH }
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)))
               (qabs_nonnegT (qminus (x m) (x n)))
               (qleT'_trans (qabs (x0 n)) x2
                 (qplus { qnum = (Zpos XH); qden = XH } (qabs x2)) (q1 n)
                 (qle_to_QleT' x2
                   (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))
               (q2 m n (natLe_lift x3 m) (natLe_lift x3 n))))
           (qeq_leT'
             (qplus
               (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x1))
                 (qdiv eps
                   (qmult { qnum = (Zpos (XO XH)); qden = XH }
                     (qplus { qnum = (Zpos XH); qden = XH } (qabs x1)))))
               (qmult (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))
                 (qdiv eps
                   (qmult { qnum = (Zpos (XO XH)); qden = XH }
                     (qplus { qnum = (Zpos XH); qden = XH } (qabs x2))))))
             eps)))))))
      (RealSetoid.real_eq_mult_compat
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_mult (real_const { qnum = (Zpos (XO (XO XH))); qden = XH })
          arctan_one_real)
        (real_eq_refl
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH })))
        (real_eq_sym
          (real_mult (real_const { qnum = (Zpos (XO (XO XH))); qden = XH })
            arctan_one_real)
          cauchy_real_pi_leibniz h4))
      (real_half_four_mult arctan_one_real))

(** val channel_n5 : real_eq -> real_eq -> real_eq **)

let channel_n5 h4 hsc =
  real_eq_trans
    (cauchy_real_cos
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))))
    (cauchy_real_cos
      (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
        arctan_one_real))
    real_zero
    (real_cos_eq_compat
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
        arctan_one_real)
      (channel_w_eq_two_theta h4))
    (channel_cos_double_zero hsc)

(** val channel_w_lower : real_lt **)

let channel_w_lower =
  real_pi_leibniz_half_lower

(** val channel_w_upper_two : real_lt **)

let channel_w_upper_two =
  real_lt_trans
    (real_mult cauchy_real_pi_leibniz
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    (real_const
      (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI XH));
        qden = XH }))
    (real_const { qnum = (Zpos (XO XH)); qden = XH })
    real_pi_leibniz_half_upper
    (real_const_lt
      (qdiv { qnum = (Zpos (XI (XO XH))); qden = XH } { qnum = (Zpos (XI XH));
        qden = XH })
      { qnum = (Zpos (XO XH)); qden = XH })

(** val channel_w_eq_cos_pi_half : real_eq -> real_eq -> real_eq **)

let channel_w_eq_cos_pi_half h4 hsc =
  cos_pi_half_unique_widened
    (real_mult cauchy_real_pi_leibniz
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    channel_w_lower channel_w_upper_two (channel_n5 h4 hsc)

(** val channel_two_w_eq_pi : real_eq **)

let channel_two_w_eq_pi =
  real_double_half_cancel cauchy_real_pi_leibniz

(** val channel_f1 : real_eq -> real_eq -> real_eq **)

let channel_f1 h4 hsc =
  real_eq_trans
    (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH }) cos_pi_half)
    (real_mult (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))))
    cauchy_real_pi_leibniz
    (RealSetoid.real_eq_mult_compat
      (real_const { qnum = (Zpos (XO XH)); qden = XH }) cos_pi_half
      (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (real_mult cauchy_real_pi_leibniz
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      (real_eq_refl (real_const { qnum = (Zpos (XO XH)); qden = XH }))
      (real_eq_sym
        (real_mult cauchy_real_pi_leibniz
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH })))
        cos_pi_half (channel_w_eq_cos_pi_half h4 hsc)))
    channel_two_w_eq_pi

(** val a3_h4_value_bridge : real_eq **)

let a3_h4_value_bridge eps _ =
  let s = q_arch_inv (qdiv eps lp_four) in
  let ExistT (x, _) = s in
  ExistT (x, (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1
          (real_mult (real_const { qnum = (Zpos (XO (XO XH))); qden = XH })
            arctan_one_real)
          n)
        (projT1 cauchy_real_pi_leibniz n)))
    eps))

(** val real_const_pos_f1 : q -> real_lt **)

let real_const_pos_f1 c =
  ExistT ((qmult c (qinv { qnum = (Zpos (XO XH)); qden = XH })), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qmult c (qinv { qnum = (Zpos (XO XH)); qden = XH }))),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qmult c (qinv { qnum = (Zpos (XO XH)); qden = XH }))
      (qminus (projT1 (real_const c) n) (projT1 real_zero n))))))))

(** val b3r_one_sq_real_pos : real -> real_lt **)

let b3r_one_sq_real_pos x =
  ExistT ({ qnum = (Zpos XH); qden = (XO XH) }, (Pair (Id_refl, (ExistT (O,
    (fun n _ ->
    qlt_to_QltT { qnum = (Zpos XH); qden = (XO XH) }
      (qminus (projT1 (real_plus real_one (real_mult x x)) n)
        (projT1 real_zero n))))))))

(** val b3rr_qdecay : q -> q -> (nat, __) sigT **)

let b3rr_qdecay q0 e =
  let s =
    qarchimedean (qinv (qmult e (qminus { qnum = (Zpos XH); qden = XH } q0)))
  in
  ExistT ((Coq_Pos.to_nat s), __)

(** val b3rr_dom_lt1 :
    real -> q -> (nat -> qleT') -> qleT' -> nat -> qleT' **)

let b3rr_dom_lt1 x r hxr hr1 n =
  qleT'_trans (qabs (projT1 x n)) r { qnum = (Zpos XH); qden = XH } (hxr n)
    hr1

(** val b3rr_C2 : q -> q **)

let b3rr_C2 m =
  qmult { qnum = (Z.of_nat (S (S O))); qden = XH }
    (qmult m
      (qinv
        (qmult (qminus { qnum = (Zpos XH); qden = XH } (qmult m m))
          (qminus { qnum = (Zpos XH); qden = XH } (qmult m m)))))

(** val b3rr_dom_r1 : real -> q -> (nat -> qleT') -> nat -> qleT' **)

let b3rr_dom_r1 x r hxr n =
  b3rr_dom_lt1 x r hxr (qle_to_QleT' r { qnum = (Zpos XH); qden = XH }) n

type cw_unit = nat -> qleT'

(** val real_E : real -> cw_unit -> real **)

let real_E x hx =
  real_plus (cauchy_real_sin (cauchy_real_arctan x hx))
    (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x hx))))

(** val real_E_one : real **)

let real_E_one =
  real_E (real_const { qnum = (Zpos XH); qden = XH }) atan1_pt_bound

(** val real_E_one_unfold : real_eq **)

let real_E_one_unfold =
  real_eq_refl
    (real_plus
      (cauchy_real_sin
        (cauchy_real_arctan (real_const { qnum = (Zpos XH); qden = XH })
          atan1_pt_bound))
      (real_opp
        (real_mult (real_const { qnum = (Zpos XH); qden = XH })
          (cauchy_real_cos
            (cauchy_real_arctan (real_const { qnum = (Zpos XH); qden = XH })
              atan1_pt_bound)))))

(** val real_eq_minus_zero : real -> real -> real_eq -> real_eq **)

let real_eq_minus_zero a b h eps heps =
  let s = h eps heps in
  let ExistT (x, q0) = s in
  ExistT (x, (fun n hn ->
  let hN = q0 n hn in
  qltT_eq_compat_l
    (qabs (qminus (projT1 (real_plus a (real_opp b)) n) (projT1 real_zero n)))
    (qabs (qminus (projT1 a n) (projT1 b n))) eps hN))

(** val b5b_const_one_mult : real -> real_eq **)

let b5b_const_one_mult x =
  real_eq_of_zero_diff
    (real_mult (real_const { qnum = (Zpos XH); qden = XH }) x) x

(** val b5b_hsc_main : real_eq -> real_eq **)

let b5b_hsc_main hE1 =
  let hsincos1 =
    real_eq_minus_zero (cauchy_real_sin arctan_one_real)
      (real_mult (real_const { qnum = (Zpos XH); qden = XH })
        (cauchy_real_cos arctan_one_real))
      (real_eq_trans
        (real_plus (cauchy_real_sin arctan_one_real)
          (real_opp
            (real_mult (real_const { qnum = (Zpos XH); qden = XH })
              (cauchy_real_cos arctan_one_real))))
        real_E_one real_zero
        (real_eq_sym real_E_one
          (real_plus (cauchy_real_sin arctan_one_real)
            (real_opp
              (real_mult (real_const { qnum = (Zpos XH); qden = XH })
                (cauchy_real_cos arctan_one_real))))
          real_E_one_unfold)
        hE1)
  in
  real_eq_trans (cauchy_real_sin arctan_one_real)
    (real_mult (real_const { qnum = (Zpos XH); qden = XH })
      (cauchy_real_cos arctan_one_real))
    (cauchy_real_cos arctan_one_real) hsincos1
    (b5b_const_one_mult (cauchy_real_cos arctan_one_real))

(** val b5b_arch2 : (q, (qleT', nat -> qleT') and0) sigT **)

let b5b_arch2 =
  exp_series_arch { qnum = (Zpos (XO XH)); qden = XH }
    (qle_to_QleT' { qnum = Z0; qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })

(** val b5b_ap_uniform : q -> (nat, (q, (qltT, __) and0) sigT) sigT **)

let b5b_ap_uniform eps =
  let s = q_arch_inv (qdiv eps { qnum = (Zpos (XO (XO (XO XH)))); qden = XH })
  in
  let ExistT (x, _) = s in
  let d0 =
    qdiv (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) { qnum =
      (Z.of_nat (S x)); qden = XH }
  in
  ExistT (x, (ExistT (d0, (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qmult (qmult eps (qinv { qnum = (Zpos (XO (XO XH))); qden = XH }))
       (qinv { qnum = (Z.of_nat (S x)); qden = XH }))),
  __)))))

(** val b5b_unit_const : q -> cw_unit **)

let b5b_unit_const g n =
  qle_to_QleT'
    (qabs (projT1 (real_const (qminus { qnum = (Zpos XH); qden = XH } g)) n))
    { qnum = (Zpos XH); qden = XH }

(** val b5a_QltT_eq_r : q -> q -> q -> qltT -> qltT **)

let b5a_QltT_eq_r _ _ _ hy =
  hy

(** val b5a_q_half_lt_one_plus_sq_T : q -> qltT **)

let b5a_q_half_lt_one_plus_sq_T u =
  qlt_to_QltT
    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })
    (qplus { qnum = (Zpos XH); qden = XH } (qmult u u))

(** val b5a_one_plus_sq_pos : real -> real_lt **)

let b5a_one_plus_sq_pos x =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT (O, (fun n _ ->
    b5a_QltT_eq_r
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus (projT1 (real_plus real_one (real_mult x x)) n)
        (projT1 real_zero n))
      (qplus { qnum = (Zpos XH); qden = XH }
        (qmult (projT1 x n) (projT1 x n)))
      (b5a_q_half_lt_one_plus_sq_T (projT1 x n))))))))

(** val b5a_E : real -> (nat -> qleT') -> real **)

let b5a_E x hx =
  real_plus (cauchy_real_sin (cauchy_real_arctan x hx))
    (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x hx))))

(** val b5a_S : real -> real **)

let b5a_S x =
  cauchy_real_exp
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)))

(** val b5a_sin_wd_exact : real -> real -> real_eq **)

let b5a_sin_wd_exact u v =
  real_eq_of_zero_diff (cauchy_real_sin u) (cauchy_real_sin v)

(** val b5a_atan_d : real -> real **)

let b5a_atan_d x =
  real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)

(** val b5a_comp_err_sin :
    real -> (nat -> qleT') -> real -> (nat -> qleT') -> real **)

let b5a_comp_err_sin x hx h hxh =
  real_plus (cauchy_real_sin (cauchy_real_arctan (real_plus x h) hxh))
    (real_opp
      (real_plus (cauchy_real_sin (cauchy_real_arctan x hx))
        (real_mult (cauchy_real_cos (cauchy_real_arctan x hx))
          (real_mult (b5a_atan_d x) h))))

(** val b5a_comp_err_cos :
    real -> (nat -> qleT') -> real -> (nat -> qleT') -> real **)

let b5a_comp_err_cos x hx h hxh =
  real_plus (cauchy_real_cos (cauchy_real_arctan (real_plus x h) hxh))
    (real_opp
      (real_plus (cauchy_real_cos (cauchy_real_arctan x hx))
        (real_opp
          (real_mult (cauchy_real_sin (cauchy_real_arctan x hx))
            (real_mult (b5a_atan_d x) h)))))

(** val b5c_const_unit : q -> nat -> qleT' **)

let b5c_const_unit q0 n =
  qle_to_QleT' (qabs (projT1 (real_const q0) n)) { qnum = (Zpos XH); qden =
    XH }

(** val b5c_unit_zero : nat -> qleT' **)

let b5c_unit_zero =
  b5c_const_unit { qnum = Z0; qden = XH }

(** val b5c_S_pos : real -> real_lt **)

let b5c_S_pos x =
  cauchy_real_exp_pos
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)))

(** val b5c_J : real -> (nat -> qleT') -> real **)

let b5c_J x hx =
  real_mult (b5a_E x hx) (real_inv_pos (b5a_S x) (b5c_S_pos x))

(** val b5c_sin_zero : real_eq **)

let b5c_sin_zero =
  real_eq_of_zero_diff (cauchy_real_sin real_zero) real_zero

(** val b5c_E_zero_at_zero : (nat -> qleT') -> real_eq **)

let b5c_E_zero_at_zero h0 =
  let hs0 =
    real_eq_trans
      (cauchy_real_sin
        (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))
      (cauchy_real_sin real_zero) real_zero
      (b5a_sin_wd_exact
        (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)
        real_zero)
      b5c_sin_zero
  in
  let hm0 =
    real_eq_trans
      (real_mult (real_const { qnum = Z0; qden = XH })
        (cauchy_real_cos
          (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)))
      (real_mult real_zero
        (cauchy_real_cos
          (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)))
      real_zero
      (RealSetoid.real_eq_mult_compat (real_const { qnum = Z0; qden = XH })
        (cauchy_real_cos
          (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))
        real_zero
        (cauchy_real_cos
          (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))
        (real_eq_of_zero_diff (real_const { qnum = Z0; qden = XH }) real_zero)
        (real_eq_refl
          (cauchy_real_cos
            (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))))
      (real_eq_trans
        (real_mult real_zero
          (cauchy_real_cos
            (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)))
        real_zero real_zero
        (real_eq_of_zero_diff
          (real_mult real_zero
            (cauchy_real_cos
              (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)))
          real_zero)
        (real_eq_refl real_zero))
  in
  real_eq_trans
    (real_plus
      (cauchy_real_sin
        (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))
      (real_opp
        (real_mult (real_const { qnum = Z0; qden = XH })
          (cauchy_real_cos
            (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)))))
    (real_plus real_zero (real_opp real_zero)) real_zero
    (RealSetoid.real_eq_plus_compat
      (cauchy_real_sin
        (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))
      (real_opp
        (real_mult (real_const { qnum = Z0; qden = XH })
          (cauchy_real_cos
            (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0))))
      real_zero (real_opp real_zero) hs0
      (RealSetoid.real_eq_opp_compat
        (real_mult (real_const { qnum = Z0; qden = XH })
          (cauchy_real_cos
            (cauchy_real_arctan (real_const { qnum = Z0; qden = XH }) h0)))
        real_zero hm0))
    (real_eq_trans (real_plus real_zero (real_opp real_zero)) real_zero
      real_zero (real_plus_opp real_zero) (real_eq_refl real_zero))

(** val b5c_J_zero_at_zero : (nat -> qleT') -> real_eq **)

let b5c_J_zero_at_zero h0 =
  real_eq_trans
    (real_mult (b5a_E (real_const { qnum = Z0; qden = XH }) h0)
      (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
        (b5c_S_pos (real_const { qnum = Z0; qden = XH }))))
    (real_mult real_zero
      (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
        (b5c_S_pos (real_const { qnum = Z0; qden = XH }))))
    real_zero
    (RealSetoid.real_eq_mult_compat
      (b5a_E (real_const { qnum = Z0; qden = XH }) h0)
      (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
        (b5c_S_pos (real_const { qnum = Z0; qden = XH })))
      real_zero
      (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
        (b5c_S_pos (real_const { qnum = Z0; qden = XH })))
      (b5c_E_zero_at_zero h0)
      (real_eq_refl
        (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
          (b5c_S_pos (real_const { qnum = Z0; qden = XH })))))
    (real_eq_trans
      (real_mult real_zero
        (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
          (b5c_S_pos (real_const { qnum = Z0; qden = XH }))))
      real_zero real_zero
      (real_eq_of_zero_diff
        (real_mult real_zero
          (real_inv_pos (b5a_S (real_const { qnum = Z0; qden = XH }))
            (b5c_S_pos (real_const { qnum = Z0; qden = XH }))))
        real_zero)
      (real_eq_refl real_zero))

(** val b5c_d_proj_le_one : real -> (nat, __) sigT **)

let b5c_d_proj_le_one x =
  let s =
    real_inv_proj (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)
  in
  let ExistT (x0, _) = s in ExistT (x0, __)

(** val b5i_An : real -> nat -> q **)

let b5i_An x n =
  arctan_partial n (projT1 x n)

(** val b5i_Ahn : real -> real -> nat -> q **)

let b5i_Ahn x h n =
  arctan_partial n (projT1 (real_plus x h) n)

(** val b5i_vn : real -> real -> nat -> q **)

let b5i_vn x h n =
  qminus (b5i_Ahn x h n) (b5i_An x n)

(** val b5i_addcol_sin : real -> real -> (nat -> qleT') -> nat -> q **)

let b5i_addcol_sin x h _ n =
  qabs
    (qminus (sin_partial n (b5i_Ahn x h n))
      (qplus
        (qmult (sin_partial n (b5i_An x n)) (cos_partial n (b5i_vn x h n)))
        (qmult (cos_partial n (b5i_An x n)) (sin_partial n (b5i_vn x h n)))))

(** val b5i_h_le_enk :
    real -> real -> q -> real_lt -> qltT -> (nat, __) sigT **)

let b5i_h_le_enk _ _ _ hh _ =
  let ExistT (_, a) = hh in
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val b5i_h_le_const : real -> q -> real_lt -> qltT -> (nat, __) sigT **)

let b5i_h_le_const _ _ hh _ =
  let ExistT (_, a) = hh in
  let Pair (_, s) = a in let ExistT (x, _) = s in ExistT (x, __)

(** val b5i_abs_le_pointwise :
    real -> real -> real_le -> real -> real_lt -> (nat, __) sigT **)

let b5i_abs_le_pointwise _ _ hle _ = function
| ExistT (x, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  (match hle with
   | Inl r ->
     let ExistT (_, a0) = r in
     let Pair (_, s0) = a0 in
     let ExistT (x1, _) = s0 in ExistT ((Nat.max x1 x0), __)
   | Inr r ->
     let e = qmult x (qinv { qnum = (Zpos (XO XH)); qden = XH }) in
     let he =
       qlt_to_QltT { qnum = Z0; qden = XH }
         (qmult x (qinv { qnum = (Zpos (XO XH)); qden = XH }))
     in
     let s0 = r e he in
     let ExistT (x1, _) = s0 in ExistT ((Nat.max x1 x0), __))

(** val b5i_one_plus_eps2_pos : real -> q -> real_lt -> qltT -> real_lt **)

let b5i_one_plus_eps2_pos eps k2 heps _ =
  let ExistT (_, a) = heps in
  let Pair (_, s) = a in
  let ExistT (x, _) = s in
  ExistT ({ qnum = (Zpos XH); qden = (XO XH) }, (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }),
  (ExistT (x, (fun n _ ->
  qlt_to_QltT { qnum = (Zpos XH); qden = (XO XH) }
    (qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
      (projT1 real_zero n))))))))

(** val b5i_h_inv_quarter :
    real -> real -> real_lt -> real_lt -> (nat, __) sigT **)

let b5i_h_inv_quarter _ eps2 hp = function
| ExistT (_, a) ->
  let Pair (_, s) = a in
  let ExistT (x, _) = s in
  let s0 = real_inv_proj (real_plus real_one eps2) hp in
  let ExistT (x0, _) = s0 in
  let ExistT (_, a0) = hp in
  let Pair (_, s1) = a0 in
  let ExistT (x1, _) = s1 in ExistT ((Nat.max (Nat.max x x0) x1), __)

(** val b5i_rs_addcol :
    real -> (nat -> qleT') -> real -> (nat -> qleT') -> q -> qltT -> (nat, nat
    -> natLe -> qltT) sigT **)

let b5i_rs_addcol x hx h hxh eps heps =
  let a = cauchy_real_arctan x hx in
  let ah = cauchy_real_arctan (real_plus x h) hxh in
  let v = real_plus ah (real_opp a) in
  let s = rs_add_sin a v eps heps in
  let ExistT (x0, q0) = s in
  ExistT (x0, (fun n hn ->
  qltT_eq_compat_l
    (qabs
      (qminus (projT1 (cauchy_real_sin (real_plus a v)) n)
        (projT1
          (real_plus (real_mult (cauchy_real_sin a) (cauchy_real_cos v))
            (real_mult (cauchy_real_cos a) (cauchy_real_sin v)))
          n)))
    (b5i_addcol_sin x h hxh n) eps (q0 n hn)))

(** val b4_abs_le_forall_eps_eq :
    real -> real -> (real -> real_lt -> real_le) -> real_eq **)

let b4_abs_le_forall_eps_eq x y h eps0 _ =
  let ht =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps0 { qnum = (Zpos (XI XH)); qden = XH })
  in
  let r =
    h (real_const (qdiv eps0 { qnum = (Zpos (XI XH)); qden = XH }))
      (real_const_pos (qdiv eps0 { qnum = (Zpos (XI XH)); qden = XH }) ht)
  in
  (match r with
   | Inl r0 ->
     let ExistT (_, a) = r0 in
     let Pair (_, s) = a in
     let ExistT (x0, _) = s in
     ExistT (x0, (fun n _ ->
     qltT_eq_compat_l (projT1 (real_abs (real_plus x (real_opp y))) n)
       (qabs (qminus (projT1 x n) (projT1 y n))) eps0
       (qlt_to_QltT (projT1 (real_abs (real_plus x (real_opp y))) n) eps0)))
   | Inr r0 ->
     let s = r0 (qdiv eps0 { qnum = (Zpos (XI XH)); qden = XH }) ht in
     let ExistT (x0, _) = s in
     ExistT (x0, (fun n _ ->
     qltT_eq_compat_l (projT1 (real_abs (real_plus x (real_opp y))) n)
       (qabs (qminus (projT1 x n) (projT1 y n))) eps0
       (qlt_to_QltT (projT1 (real_abs (real_plus x (real_opp y))) n) eps0))))

(** val b5b_E_close_q : q -> (nat, (q, (qltT, __) and0) sigT) sigT **)

let b5b_E_close_q eps =
  let ExistT (x, _) = b5b_arch2 in
  let s =
    q_arch_inv
      (qdiv eps (qmult { qnum = (Zpos (XO (XO (XI XH)))); qden = XH } x))
  in
  let ExistT (x0, _) = s in
  let k =
    qplus
      (qmult (qmult { qnum = (Zpos (XO XH)); qden = XH } x) { qnum =
        (Z.of_nat (S x0)); qden = XH })
      (qplus (qmult { qnum = (Zpos (XO XH)); qden = XH } x) { qnum = (Zpos
        XH); qden = XH })
  in
  let x1 =
    qdiv
      (qmult { qnum = (Zpos (XO XH)); qden = XH }
        (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }))
      k
  in
  let g0 = qmin { qnum = (Zpos XH); qden = XH } x1 in
  ExistT (x0, (ExistT (g0, (Pair ((qlt_to_QltT { qnum = Z0; qden = XH } g0),
  __)))))

(** val b5b_ep_xg_pos : q -> real_lt **)

let b5b_ep_xg_pos g =
  real_const_pos_f1 (qminus { qnum = (Zpos XH); qden = XH } g)

(** val b5b_ep_xg_lt_one : q -> real_lt **)

let b5b_ep_xg_lt_one g =
  real_const_lt (qminus { qnum = (Zpos XH); qden = XH } g) { qnum = (Zpos XH);
    qden = XH }

(** val b5b_endpoint :
    (real -> cw_unit -> real_lt -> real_lt -> real_eq) -> real_eq **)

let b5b_endpoint b5a_E_zero_on_unit epsQ _ =
  let hhalfT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv epsQ { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = b5b_E_close_q (qdiv epsQ { qnum = (Zpos (XO XH)); qden = XH }) in
  let ExistT (x, s0) = s in
  let ExistT (x0, _) = s0 in
  let s1 = q_arch_inv x0 in
  let ExistT (x1, _) = s1 in
  let a =
    qdiv { qnum = (Zpos XH); qden = XH } { qnum =
      (Z.of_nat (add x1 (S (S O)))); qden = XH }
  in
  let g =
    qmin
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      a
  in
  let xg = real_const (qminus { qnum = (Zpos XH); qden = XH } g) in
  let hxg = b5b_unit_const g in
  let hxg0 = b5b_ep_xg_pos g in
  let hxg1 = b5b_ep_xg_lt_one g in
  let hz0 = b5a_E_zero_on_unit xg hxg hxg0 hxg1 in
  let s2 = hz0 (qdiv epsQ { qnum = (Zpos (XO XH)); qden = XH }) hhalfT in
  let ExistT (x2, _) = s2 in
  ExistT ((Nat.max x x2), (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 real_E_one n) (projT1 real_zero n))) epsQ))

(** val b5b_hsc_theorem :
    (real -> cw_unit -> real_lt -> real_lt -> real_eq) -> real_eq **)

let b5b_hsc_theorem b5a_E_zero_on_unit =
  b5b_hsc_main (b5b_endpoint b5a_E_zero_on_unit)

(** val b5n_h_pts :
    real -> real -> q -> q -> real_lt -> qltT -> qltT -> real_lt -> real_lt ->
    real_lt -> (nat, nat -> natLe -> (qleT', (qleT', qleT') and0) and0) sigT **)

let b5n_h_pts h eps k_UU03b4_ k2 heps hk_UU03b4_ hk2 hh_UU03b4_ hh12 hhq =
  let s = b5i_h_le_enk h eps k_UU03b4_ hh_UU03b4_ hk_UU03b4_ in
  let ExistT (x, _) = s in
  let hc12 =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let s0 = b5i_h_le_const h { qnum = (Zpos XH); qden = (XO XH) } hh12 hc12 in
  let ExistT (x0, _) = s0 in
  let s1 =
    b5i_h_inv_quarter h (real_mult eps (real_const k2))
      (b5i_one_plus_eps2_pos eps k2 heps hk2) hhq
  in
  let ExistT (x1, _) = s1 in
  ExistT ((Nat.max (Nat.max x x0) x1), (fun n _ -> Pair
  ((qle_to_QleT' (qabs (projT1 h n)) (qmult (projT1 eps n) k_UU03b4_)), (Pair
  ((qle_to_QleT' (qabs (projT1 h n)) { qnum = (Zpos XH); qden = (XO XH) }),
  (qle_to_QleT'
    (qmult (qplus { qnum = (Zpos XH); qden = XH } (qmult (projT1 eps n) k2))
      (qabs (projT1 h n)))
    { qnum = (Zpos XH); qden = (XO (XO XH)) }))))))

(** val b5n_eps_proj_lt :
    real -> real_lt -> (q, (qltT, (nat, __) sigT) and0) sigT **)

let b5n_eps_proj_lt _ = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in ExistT (x, (Pair (q0, (ExistT (x0, __)))))

(** val b5c_inv_pos_cert_eq : real -> real_lt -> real_lt -> real_eq **)

let b5c_inv_pos_cert_eq u h1 h2 =
  let s = real_inv_proj u h1 in
  let ExistT (x, _) = s in
  let s0 = real_inv_proj u h2 in
  (fun _ _ ->
  let ExistT (x0, _) = s0 in ExistT ((Nat.max x x0), (fun _ _ -> Id_refl)))

(** val b5d_addcol_cos : real -> real -> (nat -> qleT') -> nat -> q **)

let b5d_addcol_cos x h _ n =
  qabs
    (qminus (cos_partial n (b5i_Ahn x h n))
      (qplus
        (qmult (cos_partial n (b5i_An x n)) (cos_partial n (b5i_vn x h n)))
        (qopp
          (qmult (sin_partial n (b5i_An x n)) (sin_partial n (b5i_vn x h n))))))

(** val b5d_rs_addcol_cos :
    real -> (nat -> qleT') -> real -> (nat -> qleT') -> q -> qltT -> (nat, nat
    -> natLe -> qltT) sigT **)

let b5d_rs_addcol_cos x hx h hxh eps heps =
  let a = cauchy_real_arctan x hx in
  let ah = cauchy_real_arctan (real_plus x h) hxh in
  let v = real_plus ah (real_opp a) in
  let s = rs_add_cos a v eps heps in
  let ExistT (x0, q0) = s in
  ExistT (x0, (fun n hn ->
  qltT_eq_compat_l
    (qabs
      (qminus (projT1 (cauchy_real_cos (real_plus a v)) n)
        (projT1
          (real_plus (real_mult (cauchy_real_cos a) (cauchy_real_cos v))
            (real_opp (real_mult (cauchy_real_sin a) (cauchy_real_sin v))))
          n)))
    (b5d_addcol_cos x h hxh n) eps (q0 n hn)))

(** val b5e_E_err :
    real -> (nat -> qleT') -> real -> (nat -> qleT') -> real **)

let b5e_E_err x hx h hxh =
  real_plus (b5a_E (real_plus x h) hxh)
    (real_opp
      (real_plus (b5a_E x hx)
        (real_mult (real_mult x (b5a_E x hx)) (real_mult (b5a_atan_d x) h))))

(** val b5e_E_dec_proj :
    real -> (nat -> qleT') -> real -> (nat -> qleT') -> (nat, __) sigT **)

let b5e_E_dec_proj x _ _ _ =
  let s =
    real_inv_proj (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)
  in
  let ExistT (x0, _) = s in ExistT (x0, __)

(** val b5f_g : real -> real **)

let b5f_g x =
  real_mult
    (real_const
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH }))
    (real_log (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x))

(** val b5f_v : real -> real -> real **)

let b5f_v x h =
  real_plus (b5f_g (real_plus x h)) (real_opp (b5f_g x))

(** val b5f_g_S : real -> real_eq **)

let b5f_g_S x =
  real_eq_refl
    (cauchy_real_exp
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log (real_plus real_one (real_mult x x))
          (b5a_one_plus_sq_pos x))))

(** val b5f_S_xh_eq : real -> real -> real_eq **)

let b5f_S_xh_eq x h =
  real_eq_trans (b5a_S (real_plus x h))
    (cauchy_real_exp (real_plus (b5f_g x) (b5f_v x h)))
    (real_mult (b5a_S x) (cauchy_real_exp (b5f_v x h)))
    (real_eq_trans (b5a_S (real_plus x h))
      (cauchy_real_exp (b5f_g (real_plus x h)))
      (cauchy_real_exp (real_plus (b5f_g x) (b5f_v x h)))
      (real_eq_refl
        (cauchy_real_exp
          (real_mult
            (real_const
              (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                qden = XH }))
            (real_log
              (real_plus real_one (real_mult (real_plus x h) (real_plus x h)))
              (b5a_one_plus_sq_pos (real_plus x h))))))
      (cauchy_real_exp_wd (b5f_g (real_plus x h))
        (real_plus (b5f_g x) (b5f_v x h))
        (real_eq_of_zero_diff (b5f_g (real_plus x h))
          (real_plus (b5f_g x)
            (real_plus (b5f_g (real_plus x h)) (real_opp (b5f_g x)))))))
    (real_eq_trans (cauchy_real_exp (real_plus (b5f_g x) (b5f_v x h)))
      (real_mult (cauchy_real_exp (b5f_g x)) (cauchy_real_exp (b5f_v x h)))
      (real_mult (b5a_S x) (cauchy_real_exp (b5f_v x h)))
      (cauchy_real_exp_plus (b5f_g x) (b5f_v x h))
      (RealSetoid.real_eq_mult_compat (cauchy_real_exp (b5f_g x))
        (cauchy_real_exp (b5f_v x h)) (b5a_S x) (cauchy_real_exp (b5f_v x h))
        (real_eq_sym (b5a_S x) (cauchy_real_exp (b5f_g x)) (b5f_g_S x))
        (real_eq_refl (cauchy_real_exp (b5f_v x h)))))

(** val b5f_S_err_decomp : real -> real -> real_eq **)

let b5f_S_err_decomp x h =
  let sx = b5a_S x in
  let sv = cauchy_real_exp (b5f_v x h) in
  let w = real_mult (real_mult x (b5a_atan_d x)) h in
  let t = real_mult (real_mult x sx) (real_mult (b5a_atan_d x) h) in
  let a = real_plus sv (real_opp (real_plus real_one (b5f_v x h))) in
  let b = real_plus (b5f_v x h) (real_opp w) in
  real_eq_trans
    (real_plus (b5a_S (real_plus x h)) (real_opp (real_plus sx t)))
    (real_plus (real_mult sx sv) (real_opp (real_plus sx t)))
    (real_plus (real_mult sx a) (real_mult sx b))
    (RealSetoid.real_eq_plus_compat (b5a_S (real_plus x h))
      (real_opp (real_plus sx t)) (real_mult sx sv)
      (real_opp (real_plus sx t)) (b5f_S_xh_eq x h)
      (real_eq_refl (real_opp (real_plus sx t))))
    (real_eq_of_zero_diff
      (real_plus (real_mult sx sv) (real_opp (real_plus sx t)))
      (real_plus (real_mult sx a) (real_mult sx b)))

(** val b5f_u : real -> real **)

let b5f_u x =
  real_plus real_one (real_mult x x)

(** val b5f_Du : real -> real -> real **)

let b5f_Du x h =
  real_plus (b5f_u (real_plus x h)) (real_opp (b5f_u x))

(** val b5f_LogErr : real -> real -> real **)

let b5f_LogErr x h =
  real_plus
    (real_log (b5f_u (real_plus x h)) (b5a_one_plus_sq_pos (real_plus x h)))
    (real_opp
      (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
        (real_mult (b5a_atan_d x) (b5f_Du x h))))

(** val b5f_u_Du_eq : real -> real -> real_eq **)

let b5f_u_Du_eq x h =
  real_eq_of_zero_diff (real_plus (b5f_u x) (b5f_Du x h))
    (b5f_u (real_plus x h))

(** val b5f_u_plus_Du_pos : real -> real -> real_lt **)

let b5f_u_plus_Du_pos x h =
  ExistT ({ qnum = (Zpos XH); qden = (XO XH) }, (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO
       XH) }),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT { qnum = (Zpos XH); qden = (XO XH) }
      (qminus (projT1 (real_plus (b5f_u x) (b5f_Du x h)) n)
        (projT1 real_zero n))))))))

(** val b5f_Du_act_delta :
    q -> real -> (nat -> qleT') -> real -> real -> real_lt -> real_lt ->
    real_lt -> real_lt **)

let b5f_Du_act_delta _ x _ h _UU03b4_L h_UU03b4_L0 hhL hh12 =
  let ExistT (_, a) = h_UU03b4_L0 in
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  let ExistT (x1, a0) = hhL in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let ExistT (_, a1) = hh12 in
  let Pair (_, s1) = a1 in
  let ExistT (x3, _) = s1 in
  ExistT ((qmult x1 (qinv { qnum = (Zpos (XO XH)); qden = XH })), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qmult x1 (qinv { qnum = (Zpos (XO XH)); qden = XH }))),
  (ExistT ((Nat.max (Nat.max x2 (Nat.max x3 x0)) O), (fun n _ ->
  let dLn = projT1 _UU03b4_L n in
  qlt_to_QltT (qmult x1 (qinv { qnum = (Zpos (XO XH)); qden = XH }))
    (qminus dLn (projT1 (real_abs (b5f_Du x h)) n))))))))

(** val b5j_kL : q **)

let b5j_kL =
  { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }

(** val b5j_kL_posT : qltT **)

let b5j_kL_posT =
  qlt_to_QltT { qnum = Z0; qden = XH } b5j_kL

(** val b5j_Sx_abs_pos : real -> real_lt **)

let b5j_Sx_abs_pos x =
  let r = b5c_S_pos x in
  let ExistT (x0, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0 (qminus (projT1 (real_abs (b5a_S x)) n) (projT1 real_zero n))))))))

(** val b5j_Kvq : q -> q **)

let b5j_Kvq r =
  qplus r
    (qplus { qnum = (Zpos XH); qden = (XO (XO XH)) }
      (qmult { qnum = (Zpos XH); qden = (XO XH) }
        (qmult b5j_kL
          (qplus (qmult { qnum = (Zpos (XO XH)); qden = XH } r) { qnum = (Zpos
            XH); qden = (XO XH) }))))

(** val b5j_real_const_mult_eq : q -> q -> real_eq **)

let b5j_real_const_mult_eq q1 q2 =
  real_eq_of_zero_diff (real_mult (real_const q1) (real_const q2))
    (real_const (qmult q1 q2))

(** val b5j_real_le_m_pts :
    real -> real -> real -> real_le -> real_lt -> (nat, __) sigT **)

let b5j_real_le_m_pts _ _ _ hle = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  (match hle with
   | Inl r ->
     let ExistT (_, a0) = r in
     let Pair (_, s0) = a0 in
     let ExistT (x1, _) = s0 in ExistT ((Nat.max x1 x0), __)
   | Inr r ->
     let s0 = r x q0 in
     let ExistT (x1, _) = s0 in ExistT ((Nat.max x1 x0), __))

(** val b5j_v_abs_bd :
    q -> real -> (nat -> qleT') -> real -> real -> real_lt -> (real -> real_lt
    -> real_le) -> real_lt -> real_le **)

let b5j_v_abs_bd r x _ h shV hshV hlog hh12 =
  let epsL' =
    real_mult shV (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })
  in
  let mm =
    real_mult shV
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) })
  in
  let h18T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XO XH))) }
  in
  let h116T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XO (XO XH)))) }
  in
  let hepsL' =
    real_mult_positive shV
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }) hshV
      (real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } h18T)
  in
  let hmm =
    real_mult_positive shV
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }) hshV
      (real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }
        h116T)
  in
  let ExistT (x0, a) = hshV in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (_, a0) = hh12 in
  let Pair (_, s0) = a0 in
  let ExistT (x2, _) = s0 in
  let s1 = b5c_d_proj_le_one x in
  let ExistT (x3, _) = s1 in
  let s2 =
    b5j_real_le_m_pts (real_abs (b5f_LogErr x h))
      (real_plus (real_mult (real_const b5j_kL) (real_abs (b5f_Du x h)))
        epsL')
      mm (hlog epsL' hepsL') hmm
  in
  let ExistT (x4, _) = s2 in
  RealSetoid.real_lt_le_iff_req (real_abs (b5f_v x h))
    (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) (Inl
    (ExistT ((qmult x0 { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qmult x0 { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })),
    (ExistT ((Nat.max x4 (Nat.max x1 (Nat.max x2 x3))), (fun n _ ->
    let hn = projT1 h n in
    let sn = qabs hn in
    let shn = projT1 shV n in
    let vn = qabs (projT1 (b5f_v x h) n) in
    qltT_eq_compat_r
      (qminus
        (projT1
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) n)
        (projT1 (real_abs (b5f_v x h)) n))
      (qminus (qplus (qmult (b5j_Kvq r) sn) shn) vn)
      (qmult x0 { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })
      (qlt_to_QltT (qmult x0 { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })
        (qminus (qplus (qmult (b5j_Kvq r) sn) shn) vn))))))))))

(** val b5j_lin_shape_eq : real -> real_eq **)

let b5j_lin_shape_eq v =
  real_eq_of_zero_diff
    (real_plus (cauchy_real_exp v) (real_opp (real_plus real_one v)))
    (real_plus (real_plus (cauchy_real_exp v) (real_opp real_one))
      (real_opp v))

(** val b5j_v_act_lt :
    q -> real -> (nat -> qleT') -> real -> real -> real_lt -> (real -> real_lt
    -> real_le) -> real_lt -> real_lt -> real_lt **)

let b5j_v_act_lt r x hxr h _UU03b4_lin h_UU03b4_0 hlog hhact hh12 =
  let ExistT (x0, a) = hhact in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let shV =
    real_mult _UU03b4_lin (real_const { qnum = (Zpos XH); qden = (XO XH) })
  in
  let hhalfT =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let hshV =
    real_mult_positive _UU03b4_lin
      (real_const { qnum = (Zpos XH); qden = (XO XH) }) h_UU03b4_0
      (real_const_pos { qnum = (Zpos XH); qden = (XO XH) } hhalfT)
  in
  let hvb = b5j_v_abs_bd r x hxr h shV hshV hlog hh12 in
  let hslope = ExistT ((qmult { qnum = (Zpos (XO XH)); qden = XH } x0), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qmult { qnum = (Zpos (XO XH)); qden = XH } x0)),
    (ExistT (x1, (fun n _ ->
    let dln = projT1 _UU03b4_lin n in
    let sn = qabs (projT1 h n) in
    qltT_eq_compat_r
      (qminus (projT1 _UU03b4_lin n)
        (projT1
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV) n))
      (qminus dln
        (qplus (qmult (b5j_Kvq r) sn)
          (qmult dln { qnum = (Zpos XH); qden = (XO XH) })))
      (qmult { qnum = (Zpos (XO XH)); qden = XH } x0)
      (qlt_to_QltT (qmult { qnum = (Zpos (XO XH)); qden = XH } x0)
        (qminus dln
          (qplus (qmult (b5j_Kvq r) sn)
            (qmult dln { qnum = (Zpos XH); qden = (XO XH) }))))))))))
  in
  real_le_lt_trans (real_abs (b5f_v x h))
    (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
    _UU03b4_lin hvb hslope

(** val b5j_real_const_req : q -> q -> real_eq **)

let b5j_real_const_req q1 q2 =
  real_eq_of_zero_diff (real_const q1) (real_const q2)

(** val b5j_qinv_kvq_req : q -> real_eq **)

let b5j_qinv_kvq_req r =
  real_eq_trans
    (real_mult (real_const (qinv (b5j_Kvq r))) (real_const (b5j_Kvq r)))
    (real_const (qmult (qinv (b5j_Kvq r)) (b5j_Kvq r))) real_one
    (b5j_real_const_mult_eq (qinv (b5j_Kvq r)) (b5j_Kvq r))
    (b5j_real_const_req (qmult (qinv (b5j_Kvq r)) (b5j_Kvq r)) { qnum = (Zpos
      XH); qden = XH })

(** val b5j_mult_plus_distr_eq : real -> real -> real -> real_eq **)

let b5j_mult_plus_distr_eq a b c =
  real_eq_of_zero_diff (real_mult a (real_plus b c))
    (real_plus (real_mult a b) (real_mult a c))

(** val b5j_fourth_threefourth_sum : real -> real_eq **)

let b5j_fourth_threefourth_sum m =
  real_eq_of_zero_diff
    (real_plus
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) m)
      (real_mult (real_const { qnum = (Zpos (XI XH)); qden = (XO (XO XH)) })
        m))
    m

(** val b5j_eps0_kvq_req : q -> real -> real -> real_eq **)

let b5j_eps0_kvq_req r eps invM =
  let m1 =
    real_mult
      (real_mult eps
        (real_mult (real_const (qinv (b5j_Kvq r))) (real_const (b5j_Kvq r))))
      invM
  in
  real_eq_trans
    (real_mult
      (real_mult (real_mult eps (real_const (qinv (b5j_Kvq r)))) invM)
      (real_const (b5j_Kvq r)))
    m1 (real_mult eps invM)
    (real_eq_of_zero_diff
      (real_mult
        (real_mult (real_mult eps (real_const (qinv (b5j_Kvq r)))) invM)
        (real_const (b5j_Kvq r)))
      (real_mult
        (real_mult eps
          (real_mult (real_const (qinv (b5j_Kvq r))) (real_const (b5j_Kvq r))))
        invM))
    (real_eq_trans m1 (real_mult (real_mult eps real_one) invM)
      (real_mult eps invM)
      (RealSetoid.real_eq_mult_compat
        (real_mult eps
          (real_mult (real_const (qinv (b5j_Kvq r))) (real_const (b5j_Kvq r))))
        invM (real_mult eps real_one) invM
        (RealSetoid.real_eq_mult_compat eps
          (real_mult (real_const (qinv (b5j_Kvq r))) (real_const (b5j_Kvq r)))
          eps real_one (real_eq_refl eps) (b5j_qinv_kvq_req r))
        (real_eq_refl invM))
      (real_eq_of_zero_diff (real_mult (real_mult eps real_one) invM)
        (real_mult eps invM)))

(** val b5j_eps0_shv_req : q -> real -> real -> real -> real_lt -> real_eq **)

let b5j_eps0_shv_req r eps eps' invM heps =
  let m =
    real_mult
      (real_mult (real_mult eps (real_inv_pos eps heps))
        (real_const
          (qmult (qinv (b5j_Kvq r))
            (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r)))))
      (real_mult invM eps')
  in
  real_eq_trans
    (real_mult
      (real_mult (real_mult eps (real_const (qinv (b5j_Kvq r)))) invM)
      (real_mult
        (real_mult (real_inv_pos eps heps)
          (real_const
            (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))))
        eps'))
    m
    (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
      (real_mult eps' invM))
    (real_eq_of_zero_diff
      (real_mult
        (real_mult (real_mult eps (real_const (qinv (b5j_Kvq r)))) invM)
        (real_mult
          (real_mult (real_inv_pos eps heps)
            (real_const
              (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))))
          eps'))
      (real_mult
        (real_mult (real_mult eps (real_inv_pos eps heps))
          (real_const
            (qmult (qinv (b5j_Kvq r))
              (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r)))))
        (real_mult invM eps')))
    (real_eq_trans m
      (real_mult
        (real_mult (real_mult eps (real_inv_pos eps heps))
          (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
        (real_mult invM eps'))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_mult eps' invM))
      (RealSetoid.real_eq_mult_compat
        (real_mult (real_mult eps (real_inv_pos eps heps))
          (real_const
            (qmult (qinv (b5j_Kvq r))
              (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r)))))
        (real_mult invM eps')
        (real_mult (real_mult eps (real_inv_pos eps heps))
          (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
        (real_mult invM eps')
        (RealSetoid.real_eq_mult_compat
          (real_mult eps (real_inv_pos eps heps))
          (real_const
            (qmult (qinv (b5j_Kvq r))
              (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))))
          (real_mult eps (real_inv_pos eps heps))
          (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
          (real_eq_refl (real_mult eps (real_inv_pos eps heps)))
          (b5j_real_const_req
            (qmult (qinv (b5j_Kvq r))
              (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r)))
            { qnum = (Zpos XH); qden = (XO (XO XH)) }))
        (real_eq_refl (real_mult invM eps')))
      (real_eq_trans
        (real_mult
          (real_mult (real_mult eps (real_inv_pos eps heps))
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
          (real_mult invM eps'))
        (real_mult
          (real_mult real_one
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
          (real_mult invM eps'))
        (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
          (real_mult eps' invM))
        (RealSetoid.real_eq_mult_compat
          (real_mult (real_mult eps (real_inv_pos eps heps))
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
          (real_mult invM eps')
          (real_mult real_one
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
          (real_mult invM eps')
          (RealSetoid.real_eq_mult_compat
            (real_mult eps (real_inv_pos eps heps))
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) real_one
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
            (real_inv_pos_correct eps heps)
            (real_eq_refl
              (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })))
          (real_eq_refl (real_mult invM eps')))
        (real_eq_trans
          (real_mult
            (real_mult real_one
              (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
            (real_mult invM eps'))
          (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
            (real_mult invM eps'))
          (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
            (real_mult eps' invM))
          (real_eq_of_zero_diff
            (real_mult
              (real_mult real_one
                (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
              (real_mult invM eps'))
            (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
              (real_mult invM eps')))
          (RealSetoid.real_eq_mult_compat
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
            (real_mult invM eps')
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
            (real_mult eps' invM)
            (real_eq_refl
              (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
            (real_mult_comm invM eps')))))

(** val b5k_S_gt_one_cert : real -> real_lt -> real_lt **)

let b5k_S_gt_one_cert x hsq =
  let hdiff =
    real_eq_of_zero_diff (real_mult x x)
      (real_plus (real_plus real_one (real_mult x x)) (real_opp real_one))
  in
  let hdiff2 =
    real_lt_eq_lt real_zero (real_mult x x)
      (real_plus (real_plus real_one (real_mult x x)) (real_opp real_one)) hsq
      hdiff
  in
  let hu1 =
    real_lt_zero_minus real_one (real_plus real_one (real_mult x x)) hdiff2
  in
  let hlog =
    real_eq_lt_lt real_zero (real_log real_one real_lt_zero_one)
      (cw_log (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x))
      (real_eq_sym (real_log real_one real_lt_zero_one) real_zero
        (real_log_one real_lt_zero_one))
      (real_log_lt_mono real_one (real_plus real_one (real_mult x x))
        real_lt_zero_one (b5a_one_plus_sq_pos x) hu1)
  in
  let hhalf =
    real_const_pos
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
  in
  let hprod =
    real_mult_pos_compat
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x))
      hhalf hlog
  in
  real_eq_lt_lt real_one (cauchy_real_exp real_zero) (b5a_S x)
    (real_eq_sym (cauchy_real_exp real_zero) real_one cauchy_real_exp_zero)
    (cauchy_real_exp_mono real_zero
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log (real_plus real_one (real_mult x x))
          (b5a_one_plus_sq_pos x)))
      hprod)

(** val b5k_S_ge_one_cert : real -> real_lt -> (nat, __) sigT **)

let b5k_S_ge_one_cert x hsq =
  let r = b5k_S_gt_one_cert x hsq in
  let ExistT (_, a) = r in
  let Pair (_, s) = a in let ExistT (x0, _) = s in ExistT (x0, __)

(** val b5k_S_ge_one_pos : real -> real_lt -> (nat, __) sigT **)

let b5k_S_ge_one_pos x hx =
  b5k_S_ge_one_cert x (real_mult_pos_compat x x hx hx)

(** val b5a_S_ge_one : real -> real_lt -> (nat, __) sigT **)

let b5a_S_ge_one =
  b5k_S_ge_one_pos

(** val b5l_k_posT : q -> qltT **)

let b5l_k_posT m =
  qlt_to_QltT { qnum = Z0; qden = XH }
    (qinv
      (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
        (qplus m { qnum = (Zpos XH); qden = XH })))

(** val b5l_eq_abs_tri :
    real -> real -> real -> q -> real_eq -> qltT -> (nat, __) sigT **)

let b5l_eq_abs_tri _ _ _ m0 heq hm0 =
  let s = heq m0 hm0 in let ExistT (x, _) = s in ExistT (x, __)

(** val b5m_rS : real -> real -> real **)

let b5m_rS x h =
  real_plus (b5a_S (real_plus x h))
    (real_opp
      (real_plus (b5a_S x)
        (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))

(** val b5m_S_pos_pt : real -> (q, (qltT, (nat, __) sigT) and0) sigT **)

let b5m_S_pos_pt x =
  let r = b5c_S_pos x in
  let ExistT (x0, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in ExistT (x0, (Pair (q0, (ExistT (x1, __)))))

(** val b5m_J_dec_proj :
    real -> real -> (nat -> qleT') -> (nat -> qleT') -> (nat, __) sigT **)

let b5m_J_dec_proj x h _ _ =
  let s = real_inv_proj (b5a_S x) (b5c_S_pos x) in
  let ExistT (x0, _) = s in
  let s0 = real_inv_proj (b5a_S (real_plus x h)) (b5c_S_pos (real_plus x h))
  in
  let ExistT (x1, _) = s0 in
  let s1 = b5m_S_pos_pt x in
  let ExistT (_, a) = s1 in
  let Pair (_, s2) = a in
  let ExistT (x2, _) = s2 in
  let s3 = b5m_S_pos_pt (real_plus x h) in
  let ExistT (_, a0) = s3 in
  let Pair (_, s4) = a0 in
  let ExistT (x3, _) = s4 in
  ExistT ((Nat.max (Nat.max x0 x1) (Nat.max x2 x3)), __)

(** val b5m_S_wd : real -> real -> real_eq -> real_eq **)

let b5m_S_wd u v huv =
  let hsq = RealSetoid.real_eq_mult_compat u u v v huv huv in
  let h1p =
    RealSetoid.real_eq_plus_compat real_one (real_mult u u) real_one
      (real_mult v v) (real_eq_refl real_one) hsq
  in
  let hlog =
    real_log_wd (real_plus real_one (real_mult u u))
      (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos u)
      (b5a_one_plus_sq_pos v) h1p
  in
  let hml =
    RealSetoid.real_eq_mult_compat
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))
      (real_eq_refl
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      hlog
  in
  cauchy_real_exp_wd
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u)))
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v)))
    hml

(** val b5p2_E_eq_J_S : real -> cw_unit -> real_eq **)

let b5p2_E_eq_J_S x hx =
  real_eq_trans (b5a_E x hx) (real_mult (b5a_E x hx) real_one)
    (real_mult (real_mult (b5a_E x hx) (real_inv_pos (b5a_S x) (b5c_S_pos x)))
      (b5a_S x))
    (real_eq_sym (real_mult (b5a_E x hx) real_one) (b5a_E x hx)
      (real_mult_one (b5a_E x hx)))
    (real_eq_trans (real_mult (b5a_E x hx) real_one)
      (real_mult (b5a_E x hx)
        (real_mult (real_inv_pos (b5a_S x) (b5c_S_pos x)) (b5a_S x)))
      (real_mult
        (real_mult (b5a_E x hx) (real_inv_pos (b5a_S x) (b5c_S_pos x)))
        (b5a_S x))
      (RealSetoid.real_eq_mult_compat (b5a_E x hx) real_one (b5a_E x hx)
        (real_mult (real_inv_pos (b5a_S x) (b5c_S_pos x)) (b5a_S x))
        (real_eq_refl (b5a_E x hx))
        (real_eq_sym
          (real_mult (real_inv_pos (b5a_S x) (b5c_S_pos x)) (b5a_S x))
          real_one
          (real_eq_trans
            (real_mult (real_inv_pos (b5a_S x) (b5c_S_pos x)) (b5a_S x))
            (real_mult (b5a_S x) (real_inv_pos (b5a_S x) (b5c_S_pos x)))
            real_one
            (real_mult_comm (real_inv_pos (b5a_S x) (b5c_S_pos x)) (b5a_S x))
            (real_inv_pos_correct (b5a_S x) (b5c_S_pos x)))))
      (real_mult_assoc (b5a_E x hx) (real_inv_pos (b5a_S x) (b5c_S_pos x))
        (b5a_S x)))

(** val b5p2_E_zero_of_J_zero : real -> cw_unit -> real_eq -> real_eq **)

let b5p2_E_zero_of_J_zero x hx hJ0 =
  real_eq_trans (b5a_E x hx) (real_mult (b5c_J x hx) (b5a_S x)) real_zero
    (b5p2_E_eq_J_S x hx)
    (real_eq_trans (real_mult (b5c_J x hx) (b5a_S x))
      (real_mult real_zero (b5a_S x)) real_zero
      (RealSetoid.real_eq_mult_compat (b5c_J x hx) (b5a_S x) real_zero
        (b5a_S x) hJ0 (real_eq_refl (b5a_S x)))
      (real_eq_trans (real_mult real_zero (b5a_S x))
        (real_mult (b5a_S x) real_zero) real_zero
        (real_mult_comm real_zero (b5a_S x)) (real_mult_zero (b5a_S x))))

(** val b5p2_arctan_wd :
    real -> real -> cw_unit -> cw_unit -> real_eq -> real_eq **)

let b5p2_arctan_wd u v hu hv huv epsQ _ =
  let s = b5b_ap_uniform epsQ in
  let ExistT (x, s0) = s in
  let ExistT (x0, a) = s0 in
  let Pair (q0, _) = a in
  let s1 = huv x0 q0 in
  let ExistT (x1, _) = s1 in
  ExistT ((Nat.max x x1), (fun n _ ->
  qltT_eq_compat_l
    (qabs
      (qminus (arctan_partial n (projT1 u n)) (arctan_partial n (projT1 v n))))
    (qabs
      (qminus (projT1 (cauchy_real_arctan u hu) n)
        (projT1 (cauchy_real_arctan v hv) n)))
    epsQ
    (qlt_to_QltT
      (qabs
        (qminus (arctan_partial n (projT1 u n))
          (arctan_partial n (projT1 v n))))
      epsQ)))

(** val b5p2_E_wd :
    real -> real -> cw_unit -> cw_unit -> real_eq -> real_eq **)

let b5p2_E_wd u v hu hv huv =
  let harct = b5p2_arctan_wd u v hu hv huv in
  let hsin =
    real_sin_eq_compat (cauchy_real_arctan u hu) (cauchy_real_arctan v hv)
      harct
  in
  let hcos =
    real_cos_eq_compat (cauchy_real_arctan u hu) (cauchy_real_arctan v hv)
      harct
  in
  let hm =
    RealSetoid.real_eq_mult_compat u
      (cauchy_real_cos (cauchy_real_arctan u hu)) v
      (cauchy_real_cos (cauchy_real_arctan v hv)) huv hcos
  in
  RealSetoid.real_eq_plus_compat (cauchy_real_sin (cauchy_real_arctan u hu))
    (real_opp (real_mult u (cauchy_real_cos (cauchy_real_arctan u hu))))
    (cauchy_real_sin (cauchy_real_arctan v hv))
    (real_opp (real_mult v (cauchy_real_cos (cauchy_real_arctan v hv)))) hsin
    (RealSetoid.real_eq_opp_compat
      (real_mult u (cauchy_real_cos (cauchy_real_arctan u hu)))
      (real_mult v (cauchy_real_cos (cauchy_real_arctan v hv))) hm)

(** val b5p2_S_wd : real -> real -> real_eq -> real_eq **)

let b5p2_S_wd u v huv =
  let hsq = RealSetoid.real_eq_mult_compat u u v v huv huv in
  let h1p =
    RealSetoid.real_eq_plus_compat real_one (real_mult u u) real_one
      (real_mult v v) (real_eq_refl real_one) hsq
  in
  let hlog =
    real_log_wd (real_plus real_one (real_mult u u))
      (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos u)
      (b5a_one_plus_sq_pos v) h1p
  in
  let hml =
    RealSetoid.real_eq_mult_compat
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u))
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v))
      (real_eq_refl
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      hlog
  in
  cauchy_real_exp_wd
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult u u)) (b5a_one_plus_sq_pos u)))
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log (real_plus real_one (real_mult v v)) (b5a_one_plus_sq_pos v)))
    hml

(** val b5p2_J_wd :
    real -> real -> cw_unit -> cw_unit -> real_eq -> real_eq **)

let b5p2_J_wd u v hu hv huv =
  let hS = b5p2_S_wd u v huv in
  let hinv =
    real_inv_pos_ext (b5a_S u) (b5a_S v) (b5c_S_pos u) (b5c_S_pos v) hS
  in
  RealSetoid.real_eq_mult_compat (b5a_E u hu)
    (real_inv_pos (b5a_S u) (b5c_S_pos u)) (b5a_E v hv)
    (real_inv_pos (b5a_S v) (b5c_S_pos v)) (b5p2_E_wd u v hu hv huv) hinv

(** val b5d1_b3rr_atan_deriv_lin :
    q -> real -> (nat -> qleT') -> real -> real_lt -> (real, (real_lt, real ->
    real_lt -> (nat -> qleT') -> real -> real_lt -> real_le) and0) sigT **)

let b5d1_b3rr_atan_deriv_lin r x hxb eps heps =
  let cr =
    b3rr_C2
      (qmult { qnum = (Zpos XH); qden = (XO XH) }
        (qplus { qnum = (Zpos XH); qden = XH } r))
  in
  let k =
    qinv
      (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
        (qplus cr { qnum = (Zpos XH); qden = XH }))
  in
  let rk = real_const k in
  let hrk_pos = real_const_pos_f1 k in
  let delta =
    real_min
      (real_const
        (qmult { qnum = (Zpos XH); qden = (XO XH) }
          (qminus { qnum = (Zpos XH); qden = XH } r)))
      (real_mult eps rk)
  in
  ExistT (delta, (Pair
  ((real_min_pos
     (real_const
       (qmult { qnum = (Zpos XH); qden = (XO XH) }
         (qminus { qnum = (Zpos XH); qden = XH } r)))
     (real_mult eps (real_const k))
     (real_const_pos_f1
       (qmult { qnum = (Zpos XH); qden = (XO XH) }
         (qminus { qnum = (Zpos XH); qden = XH } r)))
     (real_mult_positive eps (real_const k) heps hrk_pos)),
  (fun h hh hxh eps' heps' -> Inl
  (let ExistT (_, a) = heps in
   let Pair (_, s) = a in
   let ExistT (x0, _) = s in
   let ExistT (x1, a0) = heps' in
   let Pair (_, s0) = a0 in
   let ExistT (x2, _) = s0 in
   let hh_l =
     real_min_lt_l h
       (real_const
         (qmult { qnum = (Zpos XH); qden = (XO XH) }
           (qminus { qnum = (Zpos XH); qden = XH } r)))
       (real_mult eps rk) hh
   in
   let hh_r =
     real_min_lt_r h
       (real_const
         (qmult { qnum = (Zpos XH); qden = (XO XH) }
           (qminus { qnum = (Zpos XH); qden = XH } r)))
       (real_mult eps rk) hh
   in
   let ExistT (_, a1) = hh_l in
   let Pair (_, s1) = a1 in
   let ExistT (x3, _) = s1 in
   let ExistT (_, a2) = hh_r in
   let Pair (_, s2) = a2 in
   let ExistT (x4, _) = s2 in
   let s3 =
     real_inv_proj (real_plus real_one (real_mult x x))
       (b3r_one_sq_real_pos x)
   in
   let ExistT (x5, _) = s3 in
   let s4 =
     b3rr_qdecay r (qmult x1 (qinv { qnum = (Zpos (XO XH)); qden = XH }))
   in
   let ExistT (x6, _) = s4 in
   let eta = qmult x1 (qinv { qnum = (Zpos (XO XH)); qden = XH }) in
   let heta_pos =
     qlt_to_QltT { qnum = Z0; qden = XH }
       (qmult x1 (qinv { qnum = (Zpos (XO XH)); qden = XH }))
   in
   ExistT (eta, (Pair (heta_pos, (ExistT
   ((Nat.max (Nat.max (Nat.max x0 x2) (Nat.max x3 x4)) (Nat.max x5 x6)),
   (fun n _ ->
   let wreal =
     real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)
   in
   qlt_to_QltT eta
     (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
       (projT1
         (real_abs
           (real_plus (cauchy_real_arctan (real_plus x h) hxh)
             (real_opp
               (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxb))
                 (real_mult h wreal)))))
         n)))))))))))))

(** val b5dD_atan_deriv_b5a_r_exp :
    q -> real -> (nat -> qleT') -> real -> real_lt -> (real, (real_lt, real ->
    real_lt -> (nat -> qleT') -> real -> real_lt -> real_le) and0) sigT **)

let b5dD_atan_deriv_b5a_r_exp r x hxr eps heps =
  let s = b5d1_b3rr_atan_deriv_lin r x hxr eps heps in
  let ExistT (x0, a) = s in
  let Pair (r0, r1) = a in
  ExistT (x0, (Pair (r0, (fun h hh hxh eps' heps' ->
  let i3 =
    real_inv_pos (real_plus real_one (real_mult x x)) (b3r_one_sq_real_pos x)
  in
  let i5 =
    real_inv_pos (real_plus real_one (real_mult x x)) (b5a_one_plus_sq_pos x)
  in
  let hinv =
    b5c_inv_pos_cert_eq (real_plus real_one (real_mult x x))
      (b5a_one_plus_sq_pos x) (b3r_one_sq_real_pos x)
  in
  let hsl =
    real_eq_trans (real_mult i5 h) (real_mult h i5) (real_mult h i3)
      (real_mult_comm i5 h)
      (RealSetoid.real_eq_mult_compat h i5 h i3 (real_eq_refl h) hinv)
  in
  RealSetoid.real_le_compat
    (real_abs
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3)))))
    (real_abs
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h)))))
    (real_plus (real_mult eps (real_abs h)) eps')
    (real_plus (real_mult eps (real_abs h)) eps')
    (RealSetoid.real_eq_abs_compat
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3))))
      (real_plus (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h))))
      (RealSetoid.real_eq_plus_compat (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3)))
        (cauchy_real_arctan (real_plus x h) hxh)
        (real_opp
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h)))
        (real_eq_refl (cauchy_real_arctan (real_plus x h) hxh))
        (RealSetoid.real_eq_opp_compat
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult h i3))
          (real_plus (cauchy_real_arctan x (b3rr_dom_r1 x r hxr))
            (real_mult i5 h))
          (RealSetoid.real_eq_plus_compat
            (cauchy_real_arctan x (b3rr_dom_r1 x r hxr)) (real_mult h i3)
            (cauchy_real_arctan x (b3rr_dom_r1 x r hxr)) (real_mult i5 h)
            (real_eq_refl (cauchy_real_arctan x (b3rr_dom_r1 x r hxr)))
            (real_eq_sym (real_mult i5 h) (real_mult h i3) hsl)))))
    (real_eq_refl (real_plus (real_mult eps (real_abs h)) eps'))
    (r1 h hh hxh eps' heps')))))

(** val b5dD_vdh_pts_r_exp :
    q -> real -> (nat -> qleT') -> real -> real_lt -> q -> q -> qltT -> qltT
    -> (real, (real_lt, real -> real_lt -> (nat -> qleT') -> real -> real_lt
    -> (nat, __) sigT) and0) sigT **)

let b5dD_vdh_pts_r_exp r x hxr eps heps k2 k2p hk2 hk2p =
  let hx = b3rr_dom_r1 x r hxr in
  let eps2 = real_mult eps (real_const k2) in
  let heps2 =
    real_mult_positive eps (real_const k2) heps (real_const_pos k2 hk2)
  in
  let s = b5dD_atan_deriv_b5a_r_exp r x hxr eps2 heps2 in
  let ExistT (x0, a) = s in
  let Pair (r0, r1) = a in
  ExistT (x0, (Pair (r0, (fun h hh_UU03b4_ hxh eps' heps' ->
  let eps2' = real_mult eps' (real_const k2p) in
  let heps2' =
    real_mult_positive eps' (real_const k2p) heps' (real_const_pos k2p hk2p)
  in
  let v =
    real_plus (cauchy_real_arctan (real_plus x h) hxh)
      (real_opp
        (real_plus (cauchy_real_arctan x hx)
          (real_mult
            (real_inv_pos (real_plus real_one (real_mult x x))
              (b5a_one_plus_sq_pos x))
            h)))
  in
  let habs = r1 h hh_UU03b4_ hxh (real_mult eps' (real_const k2p)) heps2' in
  let s0 =
    b5i_abs_le_pointwise v (real_plus (real_mult eps2 (real_abs h)) eps2')
      habs eps2' heps2'
  in
  let ExistT (x1, _) = s0 in ExistT (x1, __)))))

(** val b5dM_real_const_pos : q -> qltT -> real_lt **)

let b5dM_real_const_pos c _ =
  ExistT ((qdiv c { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv c { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv c { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const c) n) (projT1 real_zero n))))))))

(** val b5dM_b5i_one_plus_eps2_pos :
    real -> q -> real_lt -> qltT -> real_lt **)

let b5dM_b5i_one_plus_eps2_pos eps k2 heps _ =
  let ExistT (_, a) = heps in
  let Pair (_, s) = a in
  let ExistT (x, _) = s in
  ExistT ({ qnum = (Zpos XH); qden = (XO XH) }, (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }),
  (ExistT (x, (fun n _ ->
  qlt_to_QltT { qnum = (Zpos XH); qden = (XO XH) }
    (qminus (projT1 (real_plus real_one (real_mult eps (real_const k2))) n)
      (projT1 real_zero n))))))))

(** val b5dM_b5n_eps_proj_lt :
    real -> real_lt -> (q, (qltT, (nat, __) sigT) and0) sigT **)

let b5dM_b5n_eps_proj_lt _ = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in ExistT (x, (Pair (q0, (ExistT (x0, __)))))

(** val b5dM_b5c_d_proj_le_one : real -> (nat, __) sigT **)

let b5dM_b5c_d_proj_le_one _ =
  ExistT (O, __)

(** val b5dI_inv_leaf_witness_eq : real -> q -> real_lt -> qltT -> real_eq **)

let b5dI_inv_leaf_witness_eq eps k2 heps hk2 =
  RealSetoid.real_eq_mult_compat
    (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
    (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
      (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2))
    (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
    (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
      (b5i_one_plus_eps2_pos eps k2 heps hk2))
    (real_eq_refl (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
    (real_inv_pos_ext (real_plus real_one (real_mult eps (real_const k2)))
      (real_plus real_one (real_mult eps (real_const k2)))
      (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2)
      (b5i_one_plus_eps2_pos eps k2 heps hk2)
      (real_eq_refl (real_plus real_one (real_mult eps (real_const k2)))))

(** val b5dI_real_mult_positive_exp :
    real -> real -> real_lt -> real_lt -> real_lt **)

let b5dI_real_mult_positive_exp a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val b5dI_sin_atan_diff_closed_r_exp :
    q -> real -> (nat -> qleT') -> q -> q -> q -> qleT' -> (nat -> qleT') ->
    real -> real_lt -> (real, (real_lt, real -> real_lt -> (nat -> qleT') ->
    real -> real_lt -> real_le) and0) sigT **)

let b5dI_sin_atan_diff_closed_r_exp r x hxr ms mc c4 _ _ eps heps =
  let hx = b3rr_dom_r1 x r hxr in
  let s = qplus ms mc in
  let k1e =
    qplus
      (qmult ms
        (qplus (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } c4) { qnum =
          (Zpos (XO XH)); qden = XH }))
      (qmult mc
        (qplus (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } c4) { qnum =
          (Zpos (XO (XO XH))); qden = XH }))
  in
  let k_UU03b4_ =
    qinv
      (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))));
        qden = XH } (qplus s { qnum = (Zpos XH); qden = XH }))
  in
  let k2 =
    qinv
      (qmult
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH)))))))))); qden = XH } (qplus s { qnum = (Zpos XH); qden = XH }))
        (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) mc)
          { qnum = (Zpos XH); qden = XH }))
  in
  let k2p =
    qinv
      (qmult
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH))))))))))); qden = XH }
          (qplus k1e { qnum = (Zpos XH); qden = XH }))
        (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) mc)
          { qnum = (Zpos XH); qden = XH }))
  in
  let hk_UU03b4_T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH)))))))))); qden = XH } (qplus s { qnum = (Zpos XH); qden = XH })))
  in
  let hk2T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult
          (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
            XH)))))))))); qden = XH }
            (qplus s { qnum = (Zpos XH); qden = XH }))
          (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) mc)
            { qnum = (Zpos XH); qden = XH })))
  in
  let hk2pT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult
          (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
            XH))))))))))); qden = XH }
            (qplus k1e { qnum = (Zpos XH); qden = XH }))
          (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) mc)
            { qnum = (Zpos XH); qden = XH })))
  in
  let h12T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let h14T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      XH)) }
  in
  let s0 = b5dD_vdh_pts_r_exp r x hxr eps heps k2 k2p hk2T hk2pT in
  let ExistT (x0, a) = s0 in
  let Pair (r0, s1) = a in
  let hc12r = b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO XH) } h12T in
  let hepsk_UU03b4_ =
    real_mult_positive eps (real_const k_UU03b4_) heps
      (b5dM_real_const_pos k_UU03b4_ hk_UU03b4_T)
  in
  let hqtr =
    real_mult_positive (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
      (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } h14T)
      (real_inv_pos_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
  in
  let delta =
    real_min
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
  in
  let hdpos =
    real_min_pos
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_min_pos
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_))
        (real_min_pos x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }) r0
          hc12r)
        hepsk_UU03b4_)
      hqtr
  in
  ExistT (delta, (Pair (hdpos, (fun h hh hxh eps' heps' ->
  let s2 = b5dM_b5c_d_proj_le_one x in
  let ExistT (x1, _) = s2 in
  let s3 = b5dM_b5n_eps_proj_lt eps heps in
  let ExistT (_, a0) = s3 in
  let Pair (_, s4) = a0 in
  let ExistT (x2, _) = s4 in
  let s5 = b5dM_b5n_eps_proj_lt eps' heps' in
  let ExistT (x3, a1) = s5 in
  let Pair (_, s6) = a1 in
  let ExistT (x4, _) = s6 in
  let eta = qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x3 in
  let hetaT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x3)
  in
  let hhA =
    real_min_lt_l h
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhE =
    real_min_lt_r h
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhAA =
    real_min_lt_l h
      (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhlr =
    real_min_lt_r h
      (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhda =
    real_min_lt_l h x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }) hhAA
  in
  let hh12 =
    real_min_lt_r h x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }) hhAA
  in
  let hhq_r =
    real_lt_le_trans (real_abs h)
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hhE
      (RealSetoid.real_eq_le
        (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (b5dI_inv_leaf_witness_eq eps k2 heps hk2T))
  in
  let s7 = b5n_h_pts h eps k_UU03b4_ k2 heps hk_UU03b4_T hk2T hhlr hh12 hhq_r
  in
  let ExistT (x5, _) = s7 in
  let s8 = s1 h hhda hxh eps' heps' in
  let ExistT (x6, _) = s8 in
  let s9 = b5i_rs_addcol x hx h hxh eta hetaT in
  let ExistT (x7, _) = s9 in
  let nmax = Nat.max (Nat.max x2 x4) (Nat.max (Nat.max x5 x6) (Nat.max x7 x1))
  in
  Inl (ExistT (eta, (Pair (hetaT, (ExistT (nmax, (fun n _ ->
  qlt_to_QltT eta
    (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1 (real_abs (b5a_comp_err_sin x hx h hxh)) n)))))))))))))

(** val b5dI_cos_atan_diff_closed_r_exp :
    q -> real -> (nat -> qleT') -> q -> q -> q -> qleT' -> (nat -> qleT') ->
    real -> real_lt -> (real, (real_lt, real -> real_lt -> (nat -> qleT') ->
    real -> real_lt -> real_le) and0) sigT **)

let b5dI_cos_atan_diff_closed_r_exp r x hxr ms mc c4 _ _ eps heps =
  let hx = b3rr_dom_r1 x r hxr in
  let s = qplus ms mc in
  let k1e =
    qplus
      (qmult mc
        (qplus (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } c4) { qnum =
          (Zpos (XO XH)); qden = XH }))
      (qmult ms
        (qplus (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } c4) { qnum =
          (Zpos (XO (XO XH))); qden = XH }))
  in
  let k_UU03b4_ =
    qinv
      (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))));
        qden = XH } (qplus s { qnum = (Zpos XH); qden = XH }))
  in
  let k2 =
    qinv
      (qmult
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH)))))))))); qden = XH } (qplus s { qnum = (Zpos XH); qden = XH }))
        (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) ms)
          { qnum = (Zpos XH); qden = XH }))
  in
  let k2p =
    qinv
      (qmult
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH))))))))))); qden = XH }
          (qplus k1e { qnum = (Zpos XH); qden = XH }))
        (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) ms)
          { qnum = (Zpos XH); qden = XH }))
  in
  let hk_UU03b4_T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH)))))))))); qden = XH } (qplus s { qnum = (Zpos XH); qden = XH })))
  in
  let hk2T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult
          (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
            XH)))))))))); qden = XH }
            (qplus s { qnum = (Zpos XH); qden = XH }))
          (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) ms)
            { qnum = (Zpos XH); qden = XH })))
  in
  let hk2pT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult
          (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
            XH))))))))))); qden = XH }
            (qplus k1e { qnum = (Zpos XH); qden = XH }))
          (qplus (qplus (qmult { qnum = (Zpos (XI XH)); qden = XH } s) ms)
            { qnum = (Zpos XH); qden = XH })))
  in
  let h12T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let h14T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      XH)) }
  in
  let s0 = b5dD_vdh_pts_r_exp r x hxr eps heps k2 k2p hk2T hk2pT in
  let ExistT (x0, a) = s0 in
  let Pair (r0, s1) = a in
  let hc12r = b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO XH) } h12T in
  let hepsk_UU03b4_ =
    real_mult_positive eps (real_const k_UU03b4_) heps
      (b5dM_real_const_pos k_UU03b4_ hk_UU03b4_T)
  in
  let hqtr =
    real_mult_positive (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
      (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } h14T)
      (real_inv_pos_pos (real_plus real_one (real_mult eps (real_const k2)))
        (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T))
  in
  let delta =
    real_min
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
  in
  let hdpos =
    real_min_pos
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_min_pos
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_))
        (real_min_pos x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }) r0
          hc12r)
        hepsk_UU03b4_)
      hqtr
  in
  ExistT (delta, (Pair (hdpos, (fun h hh hxh eps' heps' ->
  let s2 = b5dM_b5c_d_proj_le_one x in
  let ExistT (x1, _) = s2 in
  let s3 = b5dM_b5n_eps_proj_lt eps heps in
  let ExistT (_, a0) = s3 in
  let Pair (_, s4) = a0 in
  let ExistT (x2, _) = s4 in
  let s5 = b5dM_b5n_eps_proj_lt eps' heps' in
  let ExistT (x3, a1) = s5 in
  let Pair (_, s6) = a1 in
  let ExistT (x4, _) = s6 in
  let eta = qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x3 in
  let hetaT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x3)
  in
  let hhA =
    real_min_lt_l h
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhE =
    real_min_lt_r h
      (real_min
        (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
        (real_mult eps (real_const k_UU03b4_)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hh
  in
  let hhAA =
    real_min_lt_l h
      (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhlr =
    real_min_lt_r h
      (real_min x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }))
      (real_mult eps (real_const k_UU03b4_)) hhA
  in
  let hhda =
    real_min_lt_l h x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }) hhAA
  in
  let hh12 =
    real_min_lt_r h x0 (real_const { qnum = (Zpos XH); qden = (XO XH) }) hhAA
  in
  let hhq_r =
    real_lt_le_trans (real_abs h)
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
          (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
      hhE
      (RealSetoid.real_eq_le
        (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5dM_b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (real_mult (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
          (real_inv_pos (real_plus real_one (real_mult eps (real_const k2)))
            (b5i_one_plus_eps2_pos eps k2 heps hk2T)))
        (b5dI_inv_leaf_witness_eq eps k2 heps hk2T))
  in
  let s7 = b5n_h_pts h eps k_UU03b4_ k2 heps hk_UU03b4_T hk2T hhlr hh12 hhq_r
  in
  let ExistT (x5, _) = s7 in
  let s8 = s1 h hhda hxh eps' heps' in
  let ExistT (x6, _) = s8 in
  let s9 = b5d_rs_addcol_cos x hx h hxh eta hetaT in
  let ExistT (x7, _) = s9 in
  let nmax = Nat.max (Nat.max x2 x4) (Nat.max (Nat.max x5 x6) (Nat.max x7 x1))
  in
  Inl (ExistT (eta, (Pair (hetaT, (ExistT (nmax, (fun n _ ->
  qlt_to_QltT eta
    (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1 (real_abs (b5a_comp_err_cos x hx h hxh)) n)))))))))))))

(** val b5dI_E_diff_closed_r_exp :
    q -> real -> (nat -> qleT') -> q -> q -> q -> qleT' -> (nat -> qleT') ->
    real -> real_lt -> (real, (real_lt, real -> real_lt -> (nat -> qleT') ->
    real -> real_lt -> real_le) and0) sigT **)

let b5dI_E_diff_closed_r_exp r x hxr msr mc c4 hC4ge1 hC4 eps heps =
  let hx = b3rr_dom_r1 x r hxr in
  let k_UU03b4_ =
    qinv
      (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))));
        qden = XH } (qplus msr { qnum = (Zpos XH); qden = XH }))
  in
  let hk_UU03b4_T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qinv
        (qmult { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
          XH)))))))))); qden = XH }
          (qplus msr { qnum = (Zpos XH); qden = XH })))
  in
  let hkT4 =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      XH)) }
  in
  let hkT8 =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XO XH))) }
  in
  let hkT16 =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XO (XO XH)))) }
  in
  let hepsS =
    b5dI_real_mult_positive_exp eps
      (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) heps
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } hkT4)
  in
  let hepsC =
    b5dI_real_mult_positive_exp eps
      (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) heps
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } hkT4)
  in
  let s =
    b5dI_sin_atan_diff_closed_r_exp r x hxr msr mc c4 hC4ge1 hC4
      (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
      hepsS
  in
  let ExistT (x0, a) = s in
  let Pair (r0, r1) = a in
  let s0 =
    b5dI_cos_atan_diff_closed_r_exp r x hxr msr mc c4 hC4ge1 hC4
      (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
      hepsC
  in
  let ExistT (x1, a0) = s0 in
  let Pair (r2, r3) = a0 in
  let hepsk_UU03b4_ =
    b5dI_real_mult_positive_exp eps (real_const k_UU03b4_) heps
      (b5dM_real_const_pos k_UU03b4_ hk_UU03b4_T)
  in
  let delta = real_min (real_min x0 x1) (real_mult eps (real_const k_UU03b4_))
  in
  let hdpos =
    real_min_pos (real_min x0 x1) (real_mult eps (real_const k_UU03b4_))
      (real_min_pos x0 x1 r0 r2) hepsk_UU03b4_
  in
  ExistT (delta, (Pair (hdpos, (fun h hh hxh eps' heps' ->
  let s1 = b5dM_b5c_d_proj_le_one x in
  let ExistT (x2, _) = s1 in
  let s2 = b5dM_b5n_eps_proj_lt eps heps in
  let ExistT (_, a1) = s2 in
  let Pair (_, s3) = a1 in
  let ExistT (x3, _) = s3 in
  let s4 = b5dM_b5n_eps_proj_lt eps' heps' in
  let ExistT (x4, a2) = s4 in
  let Pair (_, s5) = a2 in
  let ExistT (x5, _) = s5 in
  let eta = qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x4 in
  let hetaT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x4)
  in
  let hhA =
    real_min_lt_l h (real_min x0 x1) (real_mult eps (real_const k_UU03b4_)) hh
  in
  let hhlr =
    real_min_lt_r h (real_min x0 x1) (real_mult eps (real_const k_UU03b4_)) hh
  in
  let hh_UU03b4_S = real_min_lt_l h x0 x1 hhA in
  let hh_UU03b4_C = real_min_lt_r h x0 x1 hhA in
  let hepsS'' =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }) heps'
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }
        hkT8)
  in
  let hshS =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }) heps'
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }
        hkT16)
  in
  let s6 =
    b5i_abs_le_pointwise (b5a_comp_err_sin x hx h hxh)
      (real_plus
        (real_mult
          (real_mult eps
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
          (real_abs h))
        (real_mult eps'
          (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })))
      (r1 h hh_UU03b4_S hxh
        (real_mult eps'
          (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }))
        hepsS'')
      (real_mult eps'
        (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }))
      hshS
  in
  let ExistT (x6, _) = s6 in
  let hepsC'' =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }) heps'
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }
        hkT8)
  in
  let hshC =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }) heps'
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }
        hkT16)
  in
  let s7 =
    b5i_abs_le_pointwise (b5a_comp_err_cos x hx h hxh)
      (real_plus
        (real_mult
          (real_mult eps
            (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
          (real_abs h))
        (real_mult eps'
          (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })))
      (r3 h hh_UU03b4_C hxh
        (real_mult eps'
          (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }))
        hepsC'')
      (real_mult eps'
        (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }))
      hshC
  in
  let ExistT (x7, _) = s7 in
  let s8 = b5i_h_le_enk h eps k_UU03b4_ hhlr hk_UU03b4_T in
  let ExistT (x8, _) = s8 in
  let s9 = b5e_E_dec_proj x hx h hxh in
  let ExistT (x9, _) = s9 in
  let nmax =
    Nat.max (Nat.max x3 x5)
      (Nat.max (Nat.max x9 x8) (Nat.max (Nat.max x6 x7) x2))
  in
  Inl (ExistT (eta, (Pair (hetaT, (ExistT (nmax, (fun n _ ->
  qlt_to_QltT eta
    (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1
        (real_abs
          (real_plus (b5a_E (real_plus x h) hxh)
            (real_opp
              (real_plus (b5a_E x hx)
                (real_mult (real_mult x (b5a_E x hx))
                  (real_mult (b5a_atan_d x) h))))))
        n)))))))))))))

(** val b5dJ_two_pos_exp : real_lt **)

let b5dJ_two_pos_exp =
  ExistT ({ qnum = (Zpos XH); qden = (XO XH) }, (Pair (Id_refl, (ExistT (O,
    (fun _ _ -> Id_refl))))))

(** val b5dJ_log_diff_dx_exp :
    real -> real_lt -> real -> real_lt -> (real, (real_lt, real -> real_lt ->
    real_lt -> real -> real_lt -> real_le) and0) sigT **)

let b5dJ_log_diff_dx_exp x0 hx0 eps heps =
  let two_inv = real_inv_pos (real_plus real_one real_one) real_two_pos_local
  in
  let four_inv = real_mult two_inv two_inv in
  let eight_inv = real_mult four_inv two_inv in
  let half_x = real_mult two_inv x0 in
  let eps_x2 = real_mult eps (real_mult x0 x0) in
  let eps4 = real_mult four_inv eps_x2 in
  let two_invJ = real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp
  in
  let four_invJ = real_mult two_invJ two_invJ in
  let half_xJ = real_mult two_invJ x0 in
  let eps4J = real_mult four_invJ eps_x2 in
  let delta = real_min half_xJ eps4J in
  ExistT (delta, (Pair
  ((real_min_pos
     (real_mult (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
       x0)
     (real_mult
       (real_mult
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp))
       (real_mult eps (real_mult x0 x0)))
     (real_mult_positive
       (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) x0
       (real_inv_pos_pos (real_plus real_one real_one) b5dJ_two_pos_exp) hx0)
     (real_mult_positive
       (real_mult
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp))
       (real_mult eps (real_mult x0 x0))
       (real_mult_positive
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos_pos (real_plus real_one real_one) b5dJ_two_pos_exp)
         (real_inv_pos_pos (real_plus real_one real_one) b5dJ_two_pos_exp))
       (real_mult_positive eps (real_mult x0 x0) heps
         (real_mult_positive x0 x0 hx0 hx0)))),
  (fun h hh hxh eps' heps' ->
  let share = real_mult eight_inv eps' in
  let hshare =
    real_mult_positive eight_inv eps'
      (real_mult_positive
        (real_mult
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
        (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
        (real_mult_positive
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local)
          (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local))
        (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local))
      heps'
  in
  let t = real_mult h (real_inv_pos x0 hx0) in
  let htwo_eq = fun eps0 heps0 ->
    let s = real_inv_proj (real_plus real_one real_one) real_two_pos_local in
    let ExistT (x, _) = s in
    ExistT (x, (fun n _ ->
    qltT_eq_compat_l { qnum = Z0; qden = XH }
      (qabs
        (qminus
          (projT1
            (real_inv_pos (real_plus real_one real_one) b5dJ_two_pos_exp) n)
          (projT1
            (real_inv_pos (real_plus real_one real_one) real_two_pos_local) n)))
      eps0 heps0))
  in
  let hfour_eq =
    RealSetoid.real_eq_mult_compat two_invJ two_invJ two_inv two_inv htwo_eq
      htwo_eq
  in
  let hhalf_le =
    RealSetoid.real_eq_le (real_mult two_invJ x0) (real_mult two_inv x0)
      (RealSetoid.real_eq_mult_compat two_invJ x0 two_inv x0 htwo_eq
        (real_eq_refl x0))
  in
  let heps4_le =
    RealSetoid.real_eq_le (real_mult four_invJ eps_x2)
      (real_mult four_inv eps_x2)
      (RealSetoid.real_eq_mult_compat four_invJ eps_x2 four_inv eps_x2
        hfour_eq (real_eq_refl eps_x2))
  in
  let hh_halfJ = real_min_lt_l h half_xJ eps4J hh in
  let hh_half = real_lt_le_trans (real_abs h) half_xJ half_x hh_halfJ hhalf_le
  in
  let ht_half = real_t_abs_lt_half x0 h hx0 hh_half in
  let ht_lower = real_abs_lt_lower t two_inv ht_half in
  let hhalf_t = real_half_lt_one_plus_t t ht_lower in
  let htpos =
    real_lt_trans real_zero two_inv (real_plus real_one t)
      (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local)
      hhalf_t
  in
  let hh_eps4J = real_min_lt_r h half_xJ eps4J hh in
  let hh_eps4 = real_lt_le_trans (real_abs h) eps4J eps4 hh_eps4J heps4_le in
  let x = real_plus (real_log (real_plus real_one t) htpos) (real_opp t) in
  let hDX =
    real_eq_trans
      (real_plus (real_log (real_plus x0 h) hxh)
        (real_opp
          (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h))))
      (real_plus (real_log (real_plus x0 h) hxh)
        (real_plus (real_opp (real_log x0 hx0))
          (real_opp (real_mult (real_inv_pos x0 hx0) h))))
      x
      (RealSetoid.real_eq_plus_compat (real_log (real_plus x0 h) hxh)
        (real_opp
          (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))
        (real_log (real_plus x0 h) hxh)
        (real_plus (real_opp (real_log x0 hx0))
          (real_opp (real_mult (real_inv_pos x0 hx0) h)))
        (real_eq_refl (real_log (real_plus x0 h) hxh))
        (real_opp_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))
      (real_eq_trans
        (real_plus (real_log (real_plus x0 h) hxh)
          (real_plus (real_opp (real_log x0 hx0))
            (real_opp (real_mult (real_inv_pos x0 hx0) h))))
        (real_plus
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp (real_log x0 hx0)))
          (real_opp (real_mult (real_inv_pos x0 hx0) h)))
        x
        (real_plus_assoc (real_log (real_plus x0 h) hxh)
          (real_opp (real_log x0 hx0))
          (real_opp (real_mult (real_inv_pos x0 hx0) h)))
        (RealSetoid.real_eq_plus_compat
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp (real_log x0 hx0)))
          (real_opp (real_mult (real_inv_pos x0 hx0) h))
          (real_log (real_plus real_one t) htpos) (real_opp t)
          (real_log_plus_diff x0 h hx0 hxh htpos)
          (real_eq_trans (real_opp (real_mult (real_inv_pos x0 hx0) h))
            (real_opp (real_mult h (real_inv_pos x0 hx0))) (real_opp t)
            (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos x0 hx0) h)
              (real_mult h (real_inv_pos x0 hx0))
              (real_mult_comm (real_inv_pos x0 hx0) h))
            (real_eq_refl (real_opp t)))))
  in
  let hXup =
    real_le_trans x (real_plus (real_plus t share) (real_opp t)) share
      (real_le_plus_compat (real_log (real_plus real_one t) htpos)
        (real_plus t share) (real_opp t) (real_opp t)
        (real_log_one_plus_le_eps t share htpos hshare)
        (real_le_refl (real_opp t)))
      (RealSetoid.real_eq_le (real_plus (real_plus t share) (real_opp t))
        share
        (real_eq_trans (real_plus (real_plus t share) (real_opp t))
          (real_plus t (real_plus share (real_opp t))) share
          (real_eq_sym (real_plus t (real_plus share (real_opp t)))
            (real_plus (real_plus t share) (real_opp t))
            (real_plus_assoc t share (real_opp t)))
          (real_eq_trans (real_plus t (real_plus share (real_opp t)))
            (real_plus (real_plus t (real_opp t)) share) share
            (real_eq_trans (real_plus t (real_plus share (real_opp t)))
              (real_plus t (real_plus (real_opp t) share))
              (real_plus (real_plus t (real_opp t)) share)
              (RealSetoid.real_eq_plus_compat t (real_plus share (real_opp t))
                t (real_plus (real_opp t) share) (real_eq_refl t)
                (real_plus_comm share (real_opp t)))
              (real_plus_assoc t (real_opp t) share))
            (real_eq_trans (real_plus (real_plus t (real_opp t)) share)
              (real_plus real_zero share) share
              (RealSetoid.real_eq_plus_compat (real_plus t (real_opp t)) share
                real_zero share (real_plus_opp t) (real_eq_refl share))
              (real_eq_trans (real_plus real_zero share)
                (real_plus share real_zero) share
                (real_plus_comm real_zero share) (real_plus_zero share))))))
  in
  let hXdown =
    real_le_trans (real_opp x)
      (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus share share))
      (RealSetoid.real_eq_le
        (real_opp
          (real_plus (real_log (real_plus real_one t) htpos) (real_opp t)))
        (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
        (real_eq_trans
          (real_opp
            (real_plus (real_log (real_plus real_one t) htpos) (real_opp t)))
          (real_plus (real_opp (real_log (real_plus real_one t) htpos))
            (real_opp (real_opp t)))
          (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
          (real_opp_plus (real_log (real_plus real_one t) htpos) (real_opp t))
          (real_eq_trans
            (real_plus (real_opp (real_log (real_plus real_one t) htpos))
              (real_opp (real_opp t)))
            (real_plus (real_opp (real_opp t))
              (real_opp (real_log (real_plus real_one t) htpos)))
            (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
            (real_plus_comm (real_opp (real_log (real_plus real_one t) htpos))
              (real_opp (real_opp t)))
            (RealSetoid.real_eq_plus_compat (real_opp (real_opp t))
              (real_opp (real_log (real_plus real_one t) htpos)) t
              (real_opp (real_log (real_plus real_one t) htpos))
              (real_opp_opp t)
              (real_eq_refl
                (real_opp (real_log (real_plus real_one t) htpos)))))))
      (real_le_trans
        (real_plus t (real_opp (real_log (real_plus real_one t) htpos)))
        (real_plus
          (real_mult (real_mult t t)
            (real_inv_pos (real_plus real_one t) htpos))
          share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share share))
        (real_t_minus_log_bound t share htpos hshare)
        (real_le_trans
          (real_plus
            (real_mult (real_mult t t)
              (real_inv_pos (real_plus real_one t) htpos))
            share)
          (real_plus
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one)) share)
            share)
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus share share))
          (real_le_plus_compat
            (real_mult (real_mult t t)
              (real_inv_pos (real_plus real_one t) htpos))
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one)) share)
            share share
            (real_quad_div_le_two_eps t (real_plus real_one t) share htpos
              hhalf_t hshare)
            (real_le_refl share))
          (RealSetoid.real_eq_le
            (real_plus
              (real_plus
                (real_mult (real_mult t t) (real_plus real_one real_one))
                share)
              share)
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one))
              (real_plus share share))
            (real_eq_sym
              (real_plus
                (real_mult (real_mult t t) (real_plus real_one real_one))
                (real_plus share share))
              (real_plus
                (real_plus
                  (real_mult (real_mult t t) (real_plus real_one real_one))
                  share)
                share)
              (real_plus_assoc
                (real_mult (real_mult t t) (real_plus real_one real_one))
                share share)))))
  in
  let habs =
    real_abs_le_quad_eps x t share (real_plus share share) share hXup hXdown
      hshare (real_plus_positive share share hshare hshare) hshare
  in
  let hquad = real_quad_t_le_h_eps x0 h eps share hx0 hh_eps4 heps hshare in
  let habsD =
    real_le_trans
      (real_abs
        (real_plus (real_log (real_plus x0 h) hxh)
          (real_opp
            (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))))
      (real_abs x)
      (real_plus
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share (real_plus share share)))
        share)
      (RealSetoid.real_eq_le
        (real_abs
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp
              (real_plus (real_log x0 hx0)
                (real_mult (real_inv_pos x0 hx0) h)))))
        (real_abs x)
        (real_abs_eq_compat
          (real_plus (real_log (real_plus x0 h) hxh)
            (real_opp
              (real_plus (real_log x0 hx0)
                (real_mult (real_inv_pos x0 hx0) h))))
          x hDX))
      habs
  in
  let hmid =
    real_le_trans
      (real_plus
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share (real_plus share share)))
        share)
      (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
        (real_plus (real_plus share (real_plus share share)) share))
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
        (real_plus share
          (real_plus (real_plus share (real_plus share share)) share)))
      (RealSetoid.real_eq_le
        (real_plus
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus share (real_plus share share)))
          share)
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus (real_plus share (real_plus share share)) share))
        (real_eq_sym
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus (real_plus share (real_plus share share)) share))
          (real_plus
            (real_plus
              (real_mult (real_mult t t) (real_plus real_one real_one))
              (real_plus share (real_plus share share)))
            share)
          (real_plus_assoc
            (real_mult (real_mult t t) (real_plus real_one real_one))
            (real_plus share (real_plus share share)) share)))
      (real_le_trans
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus (real_plus share (real_plus share share)) share))
        (real_plus
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
          (real_plus (real_plus share (real_plus share share)) share))
        (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
          (real_plus share
            (real_plus (real_plus share (real_plus share share)) share)))
        (real_le_plus_compat
          (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
          (real_plus (real_plus share (real_plus share share)) share)
          (real_plus (real_plus share (real_plus share share)) share) hquad
          (real_le_refl
            (real_plus (real_plus share (real_plus share share)) share)))
        (RealSetoid.real_eq_le
          (real_plus
            (real_plus (real_mult (real_mult two_inv eps) (real_abs h)) share)
            (real_plus (real_plus share (real_plus share share)) share))
          (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
            (real_plus share
              (real_plus (real_plus share (real_plus share share)) share)))
          (real_eq_sym
            (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
              (real_plus share
                (real_plus (real_plus share (real_plus share share)) share)))
            (real_plus
              (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
                share)
              (real_plus (real_plus share (real_plus share share)) share))
            (real_plus_assoc (real_mult (real_mult two_inv eps) (real_abs h))
              share
              (real_plus (real_plus share (real_plus share share)) share)))))
  in
  let hfinal =
    let ExistT (x1, a) = real_two_pos_local in
    let Pair (q0, s) = a in
    let ExistT (x2, q1) = s in
    let two_inv0 =
      real_inv_pos (real_plus real_one real_one) (ExistT (x1, (Pair (q0,
        (ExistT (x2, q1))))))
    in
    let four_inv0 = real_mult two_inv0 two_inv0 in
    let eight_inv0 = real_mult four_inv0 two_inv0 in
    let share0 = real_mult eight_inv0 eps' in
    let ExistT (_, a0) = heps in
    let Pair (_, s0) = a0 in
    let ExistT (x3, _) = s0 in
    let ExistT (x4, a1) = heps' in
    let Pair (_, s1) = a1 in
    let ExistT (x5, _) = s1 in
    let eps0q = qmult { qnum = (Zpos (XI XH)); qden = (XO (XO (XO XH))) } x4
    in
    let heps0q = qlt_to_QltT { qnum = Z0; qden = XH } eps0q in
    RealSetoid.real_lt_le_iff_req
      (real_plus (real_mult (real_mult two_inv0 eps) (real_abs h))
        (real_plus share0
          (real_plus (real_plus share0 (real_plus share0 share0)) share0)))
      (real_plus (real_mult eps (real_abs h)) eps') (Inl (ExistT (eps0q, (Pair
      (heps0q, (ExistT ((Nat.max x5 (Nat.max x2 x3)), (fun n _ ->
      qlt_to_QltT eps0q
        (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
          (projT1
            (real_plus (real_mult (real_mult two_inv0 eps) (real_abs h))
              (real_plus share0
                (real_plus (real_plus share0 (real_plus share0 share0))
                  share0)))
            n))))))))))
  in
  real_le_trans
    (real_abs
      (real_plus (real_log (real_plus x0 h) hxh)
        (real_opp
          (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))))
    (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
      (real_plus share
        (real_plus (real_plus share (real_plus share share)) share)))
    (real_plus (real_mult eps (real_abs h)) eps')
    (real_le_trans
      (real_abs
        (real_plus (real_log (real_plus x0 h) hxh)
          (real_opp
            (real_plus (real_log x0 hx0) (real_mult (real_inv_pos x0 hx0) h)))))
      (real_plus
        (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
          (real_plus share (real_plus share share)))
        share)
      (real_plus (real_mult (real_mult two_inv eps) (real_abs h))
        (real_plus share
          (real_plus (real_plus share (real_plus share share)) share)))
      habsD hmid)
    hfinal))))

(** val b5dJ_LogErr_delta_exp :
    real -> real -> real_lt -> (real, (real_lt, real -> real -> real_lt ->
    real_lt -> real_le) and0) sigT **)

let b5dJ_LogErr_delta_exp x epsL hepsL =
  let s = b5dJ_log_diff_dx_exp (b5f_u x) (b5a_one_plus_sq_pos x) epsL hepsL in
  let ExistT (x0, a) = s in
  let Pair (r, r0) = a in
  ExistT (x0, (Pair (r, (fun h epsL' hepsL' hh_UU0394_ ->
  let logexpr =
    real_plus
      (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
      (real_opp
        (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
          (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
            (b5f_Du x h))))
  in
  let hraw = r0 (b5f_Du x h) hh_UU0394_ (b5f_u_plus_Du_pos x h) epsL' hepsL'
  in
  let heq =
    real_eq_trans
      (real_plus
        (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h)))))
      (real_plus
        (real_log (b5f_u (real_plus x h))
          (b5a_one_plus_sq_pos (real_plus x h)))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h)))))
      (real_plus
        (real_log (b5f_u (real_plus x h))
          (b5a_one_plus_sq_pos (real_plus x h)))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (b5a_atan_d x) (b5f_Du x h)))))
      (RealSetoid.real_eq_plus_compat
        (real_log (real_plus (b5f_u x) (b5f_Du x h)) (b5f_u_plus_Du_pos x h))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h))))
        (real_log (b5f_u (real_plus x h))
          (b5a_one_plus_sq_pos (real_plus x h)))
        (real_opp
          (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
            (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
              (b5f_Du x h))))
        (real_log_wd (real_plus (b5f_u x) (b5f_Du x h))
          (b5f_u (real_plus x h)) (b5f_u_plus_Du_pos x h)
          (b5a_one_plus_sq_pos (real_plus x h)) (b5f_u_Du_eq x h))
        (real_eq_refl
          (real_opp
            (real_plus (real_log (b5f_u x) (b5a_one_plus_sq_pos x))
              (real_mult (real_inv_pos (b5f_u x) (b5a_one_plus_sq_pos x))
                (b5f_Du x h))))))
      (real_eq_refl
        (real_plus
          (real_log
            (real_plus real_one (real_mult (real_plus x h) (real_plus x h)))
            (b5a_one_plus_sq_pos (real_plus x h)))
          (real_opp
            (real_plus
              (real_log (real_plus real_one (real_mult x x))
                (b5a_one_plus_sq_pos x))
              (real_mult
                (real_inv_pos (real_plus real_one (real_mult x x))
                  (b5a_one_plus_sq_pos x))
                (b5f_Du x h))))))
  in
  real_le_trans (real_abs (b5f_LogErr x h)) (real_abs logexpr)
    (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL')
    (RealSetoid.real_eq_le (real_abs (b5f_LogErr x h)) (real_abs logexpr)
      (real_abs_eq_compat (b5f_LogErr x h) logexpr
        (real_eq_sym logexpr (b5f_LogErr x h) heq)))
    hraw))))

(** val b5d3_exp_arch4_C : q **)

let b5d3_exp_arch4_C =
  qplus
    (exp_series (S (S (S (S (S (S (S (S (S (S (S O))))))))))) { qnum = (Zpos
      (XO (XO XH))); qden = XH })
    (qmult
      (qdiv
        (q_pow { qnum = (Zpos (XO (XO XH))); qden = XH } (S (S (S (S (S (S (S
          (S (S (S (S O))))))))))))
        (q_fact (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH }))

(** val b5d3_exp_arch4_C_ge1 : qleT' **)

let b5d3_exp_arch4_C_ge1 =
  qle_to_QleT' { qnum = (Zpos XH); qden = XH } b5d3_exp_arch4_C

(** val b5d3_exp_arch4_C_all : nat -> qleT' **)

let b5d3_exp_arch4_C_all j =
  qle_to_QleT' (exp_series j { qnum = (Zpos (XO (XO XH))); qden = XH })
    b5d3_exp_arch4_C

(** val b5dK_real_mult_positive_exp :
    real -> real -> real_lt -> real_lt -> real_lt **)

let b5dK_real_mult_positive_exp a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val b5dK_real_abs_plus_one_pos_exp : real -> real_lt **)

let b5dK_real_abs_plus_one_pos_exp a =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus (projT1 (real_plus real_one (real_abs a)) n)
        (projT1 real_zero n))))))))

(** val b5dK_real_abs_scaling_le_exp :
    real -> real -> real -> real -> real_lt -> real_lt -> real_le **)

let b5dK_real_abs_scaling_le_exp a eps eps' h heps heps' =
  Inl
    (let ExistT (_, a0) = heps in
     let Pair (_, s) = a0 in
     let ExistT (x, _) = s in
     let ExistT (x0, a1) = heps' in
     let Pair (_, s0) = a1 in
     let ExistT (x1, _) = s0 in
     let s1 = real_norm_bounded a in
     let ExistT (x2, _) = s1 in
     let s2 =
       real_inv_proj (real_plus real_one (real_abs a))
         (b5dK_real_abs_plus_one_pos_exp a)
     in
     let ExistT (x3, _) = s2 in
     let m2 = qplus x2 { qnum = (Zpos (XO XH)); qden = XH } in
     ExistT ((qmult x0 (qinv m2)), (Pair
     ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x0 (qinv m2))), (ExistT
     ((Nat.max (Nat.max x x1) x3), (fun n _ ->
     qlt_to_QltT (qmult x0 (qinv m2))
       (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
         (projT1
           (real_mult (real_abs a)
             (real_plus
               (real_mult
                 (real_mult eps
                   (real_inv_pos (real_plus real_one (real_abs a))
                     (b5dK_real_abs_plus_one_pos_exp a)))
                 (real_abs h))
               (real_mult eps'
                 (real_inv_pos (real_plus real_one (real_abs a))
                   (b5dK_real_abs_plus_one_pos_exp a)))))
           n)))))))))

(** val b5dK_exp_minus_one_linear_closed_exp :
    real -> real_lt -> (real, (real_eq, (real_lt, real -> real_lt -> real ->
    real_lt -> real_le) and0) and0) sigT **)

let b5dK_exp_minus_one_linear_closed_exp eps heps =
  let delta =
    real_min (real_const { qnum = (Zpos XH); qden = (XO XH) })
      (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
  in
  ExistT (delta, (Pair
  ((real_eq_refl
     (real_min (real_const { qnum = (Zpos XH); qden = (XO XH) })
       (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })))),
  (Pair
  ((real_min_pos (real_const { qnum = (Zpos XH); qden = (XO XH) })
     (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
     (real_const_pos_f1 { qnum = (Zpos XH); qden = (XO XH) })
     (b5dK_real_mult_positive_exp eps
       (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) heps
       (real_const_pos_f1 { qnum = (Zpos XH); qden = (XO (XO XH)) }))),
  (fun h hh eps' heps' ->
  let hh_half =
    real_min_lt_l h (real_const { qnum = (Zpos XH); qden = (XO XH) })
      (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
      hh
  in
  let hh_eps4 =
    real_min_lt_r h (real_const { qnum = (Zpos XH); qden = (XO XH) })
      (real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }))
      hh
  in
  Inl
  (let ExistT (_, a) = heps in
   let Pair (_, s) = a in
   let ExistT (x, _) = s in
   let ExistT (x0, a0) = heps' in
   let Pair (q0, s0) = a0 in
   let ExistT (x1, _) = s0 in
   let ExistT (_, a1) = hh_half in
   let Pair (_, s1) = a1 in
   let ExistT (x2, _) = s1 in
   let ExistT (_, a2) = hh_eps4 in
   let Pair (_, s2) = a2 in
   let ExistT (x3, _) = s2 in
   ExistT (x0, (Pair (q0, (ExistT
   ((Nat.max (Nat.max (Nat.max x x1) (Nat.max x2 x3)) (S (S O))), (fun n _ ->
   qlt_to_QltT x0
     (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
       (projT1
         (real_abs
           (real_plus (real_plus (cauchy_real_exp h) (real_opp real_one))
             (real_opp h)))
         n)))))))))))))))

(** val b5dK_gdiff_pts_r_exp :
    q -> real -> (nat -> qleT') -> real -> real_lt -> q -> q -> qltT -> qltT
    -> (real, (real_lt, real -> real_lt -> real -> real_lt -> (nat, __) sigT)
    and0) sigT **)

let b5dK_gdiff_pts_r_exp r x hxr eps heps k2 k2p _ hk2p =
  let kL = qmult k2 { qnum = (Zpos XH); qden = (XO XH) } in
  let hkLT = qlt_to_QltT { qnum = Z0; qden = XH } kL in
  let epsL = real_mult eps (real_const kL) in
  let hepsL =
    b5dK_real_mult_positive_exp eps (real_const kL) heps
      (b5dM_real_const_pos kL hkLT)
  in
  let s = b5dJ_LogErr_delta_exp x epsL hepsL in
  let ExistT (x0, a) = s in
  let Pair (r0, r1) = a in
  let a0 =
    real_mult x0 (real_const { qnum = (Zpos XH); qden = (XO (XO (XI XH))) })
  in
  let b = real_mult eps (real_const kL) in
  let c = real_const { qnum = (Zpos XH); qden = (XO XH) } in
  let _UU03b4_g = real_min (real_min a0 b) c in
  let h12T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let h112T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XI XH))) }
  in
  let hA0 =
    b5dK_real_mult_positive_exp x0
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XI XH))) }) r0
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XI XH))) }
        h112T)
  in
  let hB0 =
    b5dK_real_mult_positive_exp eps (real_const kL) heps
      (b5dM_real_const_pos kL hkLT)
  in
  let hC0 = b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO XH) } h12T in
  let h_UU03b4_g0 =
    real_min_pos (real_min a0 b) c (real_min_pos a0 b hA0 hB0) hC0
  in
  ExistT (_UU03b4_g, (Pair (h_UU03b4_g0, (fun h hh_UU03b4_ eps' heps' ->
  let hhAB = real_min_lt_l h (real_min a0 b) c hh_UU03b4_ in
  let hhA = real_min_lt_l h a0 b hhAB in
  let hhB = real_min_lt_r h a0 b hhAB in
  let hhC = real_min_lt_r h (real_min a0 b) c hh_UU03b4_ in
  let hact = b5f_Du_act_delta r x hxr h x0 r0 hhA hhC in
  let epsL'' = real_mult eps' (real_const k2p) in
  let hepsL'' =
    b5dK_real_mult_positive_exp eps' (real_const k2p) heps'
      (b5dM_real_const_pos k2p hk2p)
  in
  let hlog = r1 h epsL'' hepsL'' hact in
  let s0 =
    b5i_abs_le_pointwise (b5f_LogErr x h)
      (real_plus (real_mult epsL (real_abs (b5f_Du x h))) epsL'') hlog epsL''
      hepsL''
  in
  let ExistT (x1, _) = s0 in
  let ExistT (_, a1) = heps in
  let Pair (_, s1) = a1 in
  let ExistT (x2, _) = s1 in
  let ExistT (_, a2) = heps' in
  let Pair (_, s2) = a2 in
  let ExistT (x3, _) = s2 in
  let ExistT (_, a3) = hhB in
  let Pair (_, s3) = a3 in
  let ExistT (x4, _) = s3 in
  let ExistT (_, a4) = hhC in
  let Pair (_, s4) = a4 in
  let ExistT (x5, _) = s4 in
  let s5 = b5dM_b5c_d_proj_le_one x in
  let ExistT (x6, _) = s5 in
  let n = Nat.max x1 (Nat.max x6 (Nat.max x2 (Nat.max x3 (Nat.max x4 x5)))) in
  ExistT (n, __)))))

(** val b5dK_exp_part_bound_closed_r_exp :
    q -> real -> (nat -> qleT') -> real -> real_lt -> (real, (real_lt, real ->
    real_lt -> real -> real_lt -> real_le) and0) sigT **)

let b5dK_exp_part_bound_closed_r_exp r x hxr eps heps =
  let sx = b5a_S x in
  let invM =
    real_inv_pos (real_plus real_one (real_abs sx))
      (b5dK_real_abs_plus_one_pos_exp sx)
  in
  let eps0 = real_mult (real_mult eps (real_const (qinv (b5j_Kvq r)))) invM in
  let hKqinvT = qlt_to_QltT { qnum = Z0; qden = XH } (qinv (b5j_Kvq r)) in
  let hinvM0 =
    real_inv_pos_pos (real_plus real_one (real_abs sx))
      (b5dK_real_abs_plus_one_pos_exp sx)
  in
  let heps0 =
    b5dK_real_mult_positive_exp
      (real_mult eps (real_const (qinv (b5j_Kvq r)))) invM
      (b5dK_real_mult_positive_exp eps (real_const (qinv (b5j_Kvq r))) heps
        (b5dM_real_const_pos (qinv (b5j_Kvq r)) hKqinvT))
      hinvM0
  in
  let heps0le = RealSetoid.real_lt_le_iff_req real_zero eps0 (Inl heps0) in
  let hkLpos = b5dM_real_const_pos b5j_kL b5j_kL_posT in
  let s = b5dJ_LogErr_delta_exp x (real_const b5j_kL) hkLpos in
  let ExistT (x0, a) = s in
  let Pair (r0, r1) = a in
  let s0 = b5dK_exp_minus_one_linear_closed_exp eps0 heps0 in
  let ExistT (x1, a0) = s0 in
  let Pair (_, a1) = a0 in
  let Pair (r2, r3) = a1 in
  let a2 = real_mult x1 (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
  in
  let b =
    real_mult x0 (real_const { qnum = (Zpos XH); qden = (XO (XO (XI XH))) })
  in
  let c = real_const { qnum = (Zpos XH); qden = (XO XH) } in
  let delta = real_min (real_min a2 b) c in
  let h14T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      XH)) }
  in
  let h112T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XI XH))) }
  in
  let h12T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let hA0 =
    b5dK_real_mult_positive_exp x1
      (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) r2
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } h14T)
  in
  let hB0 =
    b5dK_real_mult_positive_exp x0
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XI XH))) }) r0
      (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XI XH))) }
        h112T)
  in
  let hC0 = b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO XH) } h12T in
  let hdelta0 = real_min_pos (real_min a2 b) c (real_min_pos a2 b hA0 hB0) hC0
  in
  ExistT (delta, (Pair (hdelta0, (fun h hh_UU03b4_ eps' heps' ->
  let hhAB = real_min_lt_l h (real_min a2 b) c hh_UU03b4_ in
  let hhA = real_min_lt_l h a2 b hhAB in
  let hhB = real_min_lt_r h a2 b hhAB in
  let hhC = real_min_lt_r h (real_min a2 b) c hh_UU03b4_ in
  let hactDu = b5f_Du_act_delta r x hxr h x0 r0 hhB hhC in
  let hlogS = fun epsL' hepsL' -> r1 h epsL' hepsL' hactDu in
  let hvlt = b5j_v_act_lt r x hxr h x1 r2 hlogS hhA hhC in
  let eps0' =
    real_mult (real_const { qnum = (Zpos (XI XH)); qden = (XO (XO XH)) })
      (real_mult eps' invM)
  in
  let invE = real_inv_pos eps heps in
  let shV =
    real_mult
      (real_mult invE
        (real_const
          (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))))
      eps'
  in
  let h34T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos (XI XH)); qden = (XO
      (XO XH)) }
  in
  let h14KvT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))
  in
  let hinvE0 = real_inv_pos_pos eps heps in
  let heps0' =
    b5dK_real_mult_positive_exp
      (real_const { qnum = (Zpos (XI XH)); qden = (XO (XO XH)) })
      (real_mult eps' invM)
      (b5dM_real_const_pos { qnum = (Zpos (XI XH)); qden = (XO (XO XH)) }
        h34T)
      (b5dK_real_mult_positive_exp eps' invM heps' hinvM0)
  in
  let hshV =
    b5dK_real_mult_positive_exp
      (real_mult invE
        (real_const
          (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))))
      eps'
      (b5dK_real_mult_positive_exp invE
        (real_const
          (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r)))
        hinvE0
        (b5dM_real_const_pos
          (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } (b5j_Kvq r))
          h14KvT))
      heps'
  in
  let hvslope = b5j_v_abs_bd r x hxr h shV hshV hlogS hhC in
  let hlin =
    real_le_trans
      (real_abs
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h)))))
      (real_abs
        (real_plus
          (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
          (real_opp (b5f_v x h))))
      (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')
      (RealSetoid.real_eq_le
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h)))))
        (real_abs
          (real_plus
            (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
            (real_opp (b5f_v x h))))
        (real_abs_eq_compat
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))
          (real_plus
            (real_plus (cauchy_real_exp (b5f_v x h)) (real_opp real_one))
            (real_opp (b5f_v x h)))
          (b5j_lin_shape_eq (b5f_v x h))))
      (r3 (b5f_v x h) hvlt eps0' heps0')
  in
  let hmulv =
    real_le_trans (real_mult eps0 (real_abs (b5f_v x h)))
      (real_mult (real_abs (b5f_v x h)) eps0)
      (real_mult eps0
        (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
      (RealSetoid.real_eq_le (real_mult eps0 (real_abs (b5f_v x h)))
        (real_mult (real_abs (b5f_v x h)) eps0)
        (real_mult_comm eps0 (real_abs (b5f_v x h))))
      (real_le_trans (real_mult (real_abs (b5f_v x h)) eps0)
        (real_mult
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
          eps0)
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        (real_le_mult_compat_weak (real_abs (b5f_v x h))
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
          eps0 heps0le hvslope)
        (RealSetoid.real_eq_le
          (real_mult
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
            eps0)
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          (real_mult_comm
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
            eps0)))
  in
  let hlin2 =
    real_le_trans
      (real_abs
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h)))))
      (real_plus (real_mult eps0 (real_abs (b5f_v x h))) eps0')
      (real_plus
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        eps0')
      hlin
      (real_le_plus_compat (real_mult eps0 (real_abs (b5f_v x h)))
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        eps0' eps0' hmulv (real_le_refl eps0'))
  in
  let hmid1 =
    real_le_trans
      (real_mult (real_abs sx)
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_mult
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h)))))
        (real_abs sx))
      (real_mult (real_abs sx)
        (real_plus
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0'))
      (RealSetoid.real_eq_le
        (real_mult (real_abs sx)
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h))))))
        (real_mult
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))
          (real_abs sx))
        (real_mult_comm (real_abs sx)
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))))
      (real_le_trans
        (real_mult
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))
          (real_abs sx))
        (real_mult
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0')
          (real_abs sx))
        (real_mult (real_abs sx)
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0'))
        (real_le_mult_compat_weak
          (real_abs
            (real_plus (cauchy_real_exp (b5f_v x h))
              (real_opp (real_plus real_one (b5f_v x h)))))
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0')
          (real_abs sx)
          (RealSetoid.real_lt_le_iff_req real_zero (real_abs sx) (Inl
            (b5j_Sx_abs_pos x)))
          hlin2)
        (RealSetoid.real_eq_le
          (real_mult
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0')
            (real_abs sx))
          (real_mult (real_abs sx)
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0'))
          (real_mult_comm
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0')
            (real_abs sx))))
  in
  let hreshape =
    RealSetoid.real_eq_mult_compat (real_abs sx)
      (real_plus
        (real_mult eps0
          (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
        eps0')
      (real_abs sx)
      (real_plus (real_mult (real_mult eps invM) (real_abs h))
        (real_mult eps' invM))
      (real_eq_refl (real_abs sx))
      (real_eq_trans
        (real_plus
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0')
        (real_plus
          (real_plus
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_mult eps0 shV))
          eps0')
        (real_plus (real_mult (real_mult eps invM) (real_abs h))
          (real_mult eps' invM))
        (RealSetoid.real_eq_plus_compat
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0'
          (real_plus
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_mult eps0 shV))
          eps0'
          (b5j_mult_plus_distr_eq eps0
            (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV)
          (real_eq_refl eps0'))
        (real_eq_trans
          (real_plus
            (real_plus
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_mult eps0 shV))
            eps0')
          (real_plus
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_plus (real_mult eps0 shV) eps0'))
          (real_plus (real_mult (real_mult eps invM) (real_abs h))
            (real_mult eps' invM))
          (real_eq_sym
            (real_plus
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_plus (real_mult eps0 shV) eps0'))
            (real_plus
              (real_plus
                (real_mult eps0
                  (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
                (real_mult eps0 shV))
              eps0')
            (real_plus_assoc
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_mult eps0 shV) eps0'))
          (RealSetoid.real_eq_plus_compat
            (real_mult eps0 (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
            (real_plus (real_mult eps0 shV) eps0')
            (real_mult (real_mult eps invM) (real_abs h))
            (real_mult eps' invM)
            (real_eq_trans
              (real_mult eps0
                (real_mult (real_const (b5j_Kvq r)) (real_abs h)))
              (real_mult (real_mult eps0 (real_const (b5j_Kvq r)))
                (real_abs h))
              (real_mult (real_mult eps invM) (real_abs h))
              (real_mult_assoc eps0 (real_const (b5j_Kvq r)) (real_abs h))
              (RealSetoid.real_eq_mult_compat
                (real_mult eps0 (real_const (b5j_Kvq r))) (real_abs h)
                (real_mult eps invM) (real_abs h)
                (b5j_eps0_kvq_req r eps invM) (real_eq_refl (real_abs h))))
            (real_eq_trans (real_plus (real_mult eps0 shV) eps0')
              (real_plus
                (real_mult
                  (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
                  (real_mult eps' invM))
                (real_mult
                  (real_const { qnum = (Zpos (XI XH)); qden = (XO (XO XH)) })
                  (real_mult eps' invM)))
              (real_mult eps' invM)
              (RealSetoid.real_eq_plus_compat (real_mult eps0 shV) eps0'
                (real_mult
                  (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
                  (real_mult eps' invM))
                (real_mult
                  (real_const { qnum = (Zpos (XI XH)); qden = (XO (XO XH)) })
                  (real_mult eps' invM))
                (b5j_eps0_shv_req r eps eps' invM heps)
                (real_eq_refl
                  (real_mult
                    (real_const { qnum = (Zpos (XI XH)); qden = (XO (XO
                      XH)) })
                    (real_mult eps' invM))))
              (b5j_fourth_threefourth_sum (real_mult eps' invM))))))
  in
  real_le_trans
    (real_abs
      (real_mult (b5a_S x)
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h))))))
    (real_mult (real_abs sx)
      (real_abs
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h))))))
    (real_plus (real_mult eps (real_abs h)) eps')
    (RealSetoid.real_eq_le
      (real_abs
        (real_mult (b5a_S x)
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_mult (real_abs sx)
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_abs_mult_req (b5a_S x)
        (real_plus (cauchy_real_exp (b5f_v x h))
          (real_opp (real_plus real_one (b5f_v x h))))))
    (real_le_trans
      (real_mult (real_abs sx)
        (real_abs
          (real_plus (cauchy_real_exp (b5f_v x h))
            (real_opp (real_plus real_one (b5f_v x h))))))
      (real_mult (real_abs sx)
        (real_plus
          (real_mult eps0
            (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h)) shV))
          eps0'))
      (real_plus (real_mult eps (real_abs h)) eps') hmid1
      (real_le_trans
        (real_mult (real_abs sx)
          (real_plus
            (real_mult eps0
              (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                shV))
            eps0'))
        (real_mult (real_abs sx)
          (real_plus (real_mult (real_mult eps invM) (real_abs h))
            (real_mult eps' invM)))
        (real_plus (real_mult eps (real_abs h)) eps')
        (RealSetoid.real_eq_le
          (real_mult (real_abs sx)
            (real_plus
              (real_mult eps0
                (real_plus (real_mult (real_const (b5j_Kvq r)) (real_abs h))
                  shV))
              eps0'))
          (real_mult (real_abs sx)
            (real_plus (real_mult (real_mult eps invM) (real_abs h))
              (real_mult eps' invM)))
          hreshape)
        (b5dK_real_abs_scaling_le_exp (b5a_S x) eps eps' h heps heps')))))))

(** val b5d4_const0_eq_zero : real_eq **)

let b5d4_const0_eq_zero =
  real_eq_of_zero_diff (real_const { qnum = Z0; qden = XH }) real_zero

(** val b5d4_S_const0_eq_one : real_eq **)

let b5d4_S_const0_eq_one =
  let h00 =
    real_eq_trans
      (real_mult (real_const { qnum = Z0; qden = XH })
        (real_const { qnum = Z0; qden = XH }))
      (real_mult real_zero real_zero) real_zero
      (RealSetoid.real_eq_mult_compat (real_const { qnum = Z0; qden = XH })
        (real_const { qnum = Z0; qden = XH }) real_zero real_zero
        b5d4_const0_eq_zero b5d4_const0_eq_zero)
      (real_mult_zero real_zero)
  in
  let hone =
    real_eq_trans
      (real_plus real_one
        (real_mult (real_const { qnum = Z0; qden = XH })
          (real_const { qnum = Z0; qden = XH })))
      (real_plus real_one real_zero) real_one
      (RealSetoid.real_eq_plus_compat real_one
        (real_mult (real_const { qnum = Z0; qden = XH })
          (real_const { qnum = Z0; qden = XH }))
        real_one real_zero (real_eq_refl real_one) h00)
      (real_plus_zero real_one)
  in
  let hlog1 =
    real_log_wd
      (real_plus real_one
        (real_mult (real_const { qnum = Z0; qden = XH })
          (real_const { qnum = Z0; qden = XH })))
      real_one (b5a_one_plus_sq_pos (real_const { qnum = Z0; qden = XH }))
      real_lt_zero_one hone
  in
  let hlogz =
    real_eq_trans
      (real_log
        (real_plus real_one
          (real_mult (real_const { qnum = Z0; qden = XH })
            (real_const { qnum = Z0; qden = XH })))
        (b5a_one_plus_sq_pos (real_const { qnum = Z0; qden = XH })))
      (real_log real_one real_lt_zero_one) real_zero hlog1
      (real_log_one real_lt_zero_one)
  in
  let hmulz =
    real_eq_trans
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { qnum = Z0; qden = XH })
              (real_const { qnum = Z0; qden = XH })))
          (b5a_one_plus_sq_pos (real_const { qnum = Z0; qden = XH }))))
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        real_zero)
      real_zero
      (RealSetoid.real_eq_mult_compat
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { qnum = Z0; qden = XH })
              (real_const { qnum = Z0; qden = XH })))
          (b5a_one_plus_sq_pos (real_const { qnum = Z0; qden = XH })))
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        real_zero
        (real_eq_refl
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH })))
        hlogz)
      (real_mult_zero
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
  in
  real_eq_trans
    (cauchy_real_exp
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { qnum = Z0; qden = XH })
              (real_const { qnum = Z0; qden = XH })))
          (b5a_one_plus_sq_pos (real_const { qnum = Z0; qden = XH })))))
    (cauchy_real_exp real_zero) real_one
    (cauchy_real_exp_wd
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log
          (real_plus real_one
            (real_mult (real_const { qnum = Z0; qden = XH })
              (real_const { qnum = Z0; qden = XH })))
          (b5a_one_plus_sq_pos (real_const { qnum = Z0; qden = XH }))))
      real_zero hmulz)
    cauchy_real_exp_zero

(** val b5dE_const1_eq_one : real_eq **)

let b5dE_const1_eq_one =
  real_eq_of_zero_diff (real_const { qnum = (Zpos XH); qden = XH }) real_one

(** val b5dE_q_pos : q -> real_lt **)

let b5dE_q_pos q0 =
  real_const_pos q0 (qlt_to_QltT { qnum = Z0; qden = XH } q0)

(** val b5dE_half_pos_real : real_lt **)

let b5dE_half_pos_real =
  real_const_pos
    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })
    (qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH }))

(** val b5dE_log_ub_one : q -> real_lt **)

let b5dE_log_ub_one q0 =
  let t = real_mult (real_const q0) (real_const q0) in
  let e0 =
    qmult (qminus { qnum = (Zpos XH); qden = XH } (qmult q0 q0)) { qnum =
      (Zpos XH); qden = (XO XH) }
  in
  let hteq = real_eq_of_zero_diff t (real_const (qmult q0 q0)) in
  let heps0 = real_const_pos e0 (qlt_to_QltT { qnum = Z0; qden = XH } e0) in
  let hlog1 =
    real_log_one_plus_le_eps t (real_const e0)
      (b5a_one_plus_sq_pos (real_const q0)) heps0
  in
  let hle_t = RealSetoid.real_eq_le t (real_const (qmult q0 q0)) hteq in
  let hle_sum =
    real_le_plus_compat t (real_const (qmult q0 q0)) (real_const e0)
      (real_const e0) hle_t (real_le_refl (real_const e0))
  in
  let hsum_eq =
    real_eq_of_zero_diff
      (real_plus (real_const (qmult q0 q0)) (real_const e0))
      (real_const (qplus (qmult q0 q0) e0))
  in
  let hle_sum2 =
    real_le_trans (real_plus t (real_const e0))
      (real_plus (real_const (qmult q0 q0)) (real_const e0))
      (real_const (qplus (qmult q0 q0) e0)) hle_sum
      (RealSetoid.real_eq_le
        (real_plus (real_const (qmult q0 q0)) (real_const e0))
        (real_const (qplus (qmult q0 q0) e0)) hsum_eq)
  in
  let hlog2 =
    real_le_trans
      (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q0)))
      (real_plus t (real_const e0)) (real_const (qplus (qmult q0 q0) e0))
      hlog1 hle_sum2
  in
  let hc_lt =
    real_const_lt (qplus (qmult q0 q0) e0) { qnum = (Zpos XH); qden = XH }
  in
  real_le_lt_trans
    (real_log (real_plus real_one t) (b5a_one_plus_sq_pos (real_const q0)))
    (real_const (qplus (qmult q0 q0) e0))
    (real_const { qnum = (Zpos XH); qden = XH }) hlog2 hc_lt

(** val b5dE_S_lt_exp_half : q -> real_lt **)

let b5dE_S_lt_exp_half q0 =
  let hlogb = b5dE_log_ub_one q0 in
  let hsmall =
    real_lt_eq_lt
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_log
          (real_plus real_one (real_mult (real_const q0) (real_const q0)))
          (b5a_one_plus_sq_pos (real_const q0))))
      (real_mult
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        (real_const { qnum = (Zpos XH); qden = XH }))
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_lt_mult_compat
        (real_log
          (real_plus real_one (real_mult (real_const q0) (real_const q0)))
          (b5a_one_plus_sq_pos (real_const q0)))
        (real_const { qnum = (Zpos XH); qden = XH })
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        b5dE_half_pos_real hlogb)
      (real_eq_of_zero_diff
        (real_mult
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))
          (real_const { qnum = (Zpos XH); qden = XH }))
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
  in
  cauchy_real_exp_mono
    (real_mult
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_log
        (real_plus real_one (real_mult (real_const q0) (real_const q0)))
        (b5a_one_plus_sq_pos (real_const q0))))
    (real_const
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH }))
    hsmall

(** val b5dE_exp_half_le_two : real_le **)

let b5dE_exp_half_le_two =
  let hhalflt1 =
    real_lt_eq_lt
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_const { qnum = (Zpos XH); qden = XH }) real_one
      (real_const_lt
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })
        { qnum = (Zpos XH); qden = XH })
      b5dE_const1_eq_one
  in
  let he1 =
    real_exp_le_inv_one_minus
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      b5dE_half_pos_real hhalflt1
  in
  let w =
    real_lt_opp_plus
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      real_one hhalflt1
  in
  let hb =
    real_eq_of_zero_diff
      (real_plus real_one
        (real_opp
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))))
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
  in
  let hinvext =
    real_inv_pos_ext
      (real_plus real_one
        (real_opp
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))))
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      w b5dE_half_pos_real hb
  in
  let htwo =
    real_inv_unique
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH }))
      (real_inv_pos
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        b5dE_half_pos_real)
      (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (real_inv_pos_correct
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        b5dE_half_pos_real)
      (real_eq_of_zero_diff
        (real_mult
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))
          (real_const { qnum = (Zpos (XO XH)); qden = XH }))
        real_one)
  in
  real_le_trans
    (cauchy_real_exp
      (real_const
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })))
    (real_inv_pos
      (real_plus real_one
        (real_opp
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))))
      w)
    (real_const { qnum = (Zpos (XO XH)); qden = XH }) he1
    (real_le_trans
      (real_inv_pos
        (real_plus real_one
          (real_opp
            (real_const
              (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                qden = XH }))))
        w)
      (real_inv_pos
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH }))
        b5dE_half_pos_real)
      (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (RealSetoid.real_eq_le
        (real_inv_pos
          (real_plus real_one
            (real_opp
              (real_const
                (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
                  qden = XH }))))
          w)
        (real_inv_pos
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))
          b5dE_half_pos_real)
        hinvext)
      (RealSetoid.real_eq_le
        (real_inv_pos
          (real_const
            (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
              qden = XH }))
          b5dE_half_pos_real)
        (real_const { qnum = (Zpos (XO XH)); qden = XH }) htwo))

(** val b5dE_S_ub_tail_q : q -> (nat, __) sigT **)

let b5dE_S_ub_tail_q q0 =
  let s = b5a_S_ge_one (real_const q0) (b5dE_q_pos q0) in
  let ExistT (x, _) = s in
  let hstrict =
    real_lt_le_trans (b5a_S (real_const q0))
      (cauchy_real_exp
        (real_const
          (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH));
            qden = XH })))
      (real_const { qnum = (Zpos (XO XH)); qden = XH })
      (b5dE_S_lt_exp_half q0) b5dE_exp_half_le_two
  in
  let s0 =
    real_lt_pt_lt (b5a_S (real_const q0))
      (real_const { qnum = (Zpos (XO XH)); qden = XH }) hstrict
  in
  let ExistT (x0, _) = s0 in ExistT ((Nat.max x x0), __)

(** val b5dH_E_eq_b5aE : real -> cw_unit -> real_eq **)

let b5dH_E_eq_b5aE x hx =
  real_eq_refl
    (real_plus (cauchy_real_sin (cauchy_real_arctan x hx))
      (real_opp (real_mult x (cauchy_real_cos (cauchy_real_arctan x hx)))))

(** val b5dH_J_zero0 : real_eq **)

let b5dH_J_zero0 =
  b5c_J_zero_at_zero b5c_unit_zero

(** val b5dH_E_zero_of_J_zero : real -> cw_unit -> real_eq -> real_eq **)

let b5dH_E_zero_of_J_zero x hx hJ0 =
  real_eq_trans (real_E x hx) (b5a_E x hx) real_zero (b5dH_E_eq_b5aE x hx)
    (b5p2_E_zero_of_J_zero x hx hJ0)

(** val b5dH_real_const_qeq : q -> q -> real_eq **)

let b5dH_real_const_qeq a b =
  real_eq_of_zero_diff (real_const a) (real_const b)

(** val b5dH_plus_const_eq : q -> q -> real_eq **)

let b5dH_plus_const_eq a b =
  real_eq_of_zero_diff (real_plus (real_const a) (real_const b))
    (real_const (qplus a b))

(** val b5dL_tkq : q -> nat -> nat -> q **)

let b5dL_tkq q0 m k =
  qdiv (qmult q0 { qnum = (Z.of_nat k); qden = XH }) { qnum = (Z.of_nat m);
    qden = XH }

(** val b5dL_qdiv : q -> nat -> q **)

let b5dL_qdiv q0 m =
  qdiv q0 { qnum = (Z.of_nat m); qden = XH }

(** val b5dL_Qnsum : (nat -> q) -> nat -> q **)

let rec b5dL_Qnsum b = function
| O -> { qnum = Z0; qden = XH }
| S m -> qplus (b5dL_Qnsum b m) (b m)

(** val b5dL_tkC : q -> nat -> nat -> cw_unit **)

let b5dL_tkC q0 m k =
  b5c_const_unit (b5dL_tkq q0 m k)

(** val b5dL_abs_const : q -> real_eq **)

let b5dL_abs_const a =
  real_eq_of_zero_diff (real_abs (real_const a)) (real_const (qabs a))

(** val b5dL_mult_const : q -> q -> real_eq **)

let b5dL_mult_const a b =
  real_eq_of_zero_diff (real_mult (real_const a) (real_const b))
    (real_const (qmult a b))

(** val b5dL_bk : q -> nat -> q -> nat -> q **)

let b5dL_bk q0 m epsQ _ =
  qplus
    (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
      (b5dL_qdiv q0 m))
    (qdiv epsQ
      (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } { qnum = (Z.of_nat m);
        qden = XH }))

(** val b5dL_epsQ1 : nat -> q -> q **)

let b5dL_epsQ1 m epsQ =
  qdiv epsQ
    (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } { qnum = (Z.of_nat m);
      qden = XH })

(** val b5dL_J_grid_premise :
    q -> nat -> (nat -> q) -> (nat -> q) -> (nat -> __ -> cw_unit -> cw_unit
    -> real_le) -> cw_unit -> cw_unit -> real_le **)

let b5dL_J_grid_premise q0 m b e hstep c0 cM =
  let rec f n cn c0' =
    match n with
    | O ->
      let hjw =
        b5p2_J_wd (real_const (b5dL_tkq q0 m O))
          (real_const (b5dL_tkq q0 m O)) cn c0'
          (real_eq_refl (real_const (b5dL_tkq q0 m O)))
      in
      real_le_trans
        (real_abs
          (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
        real_zero (real_const (qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
        (RealSetoid.real_eq_le
          (real_abs
            (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
          real_zero
          (real_eq_trans
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) cn))))
            real_zero
            (real_abs_eq_compat
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) cn)))
              (RealSetoid.real_eq_plus_compat
                (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))
                (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) cn))
                (real_eq_refl (b5c_J (real_const (b5dL_tkq q0 m O)) cn))
                (RealSetoid.real_eq_opp_compat
                  (b5c_J (real_const (b5dL_tkq q0 m O)) c0')
                  (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                  (real_eq_sym (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                    (b5c_J (real_const (b5dL_tkq q0 m O)) c0') hjw))))
            (real_eq_trans
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) cn))))
              (real_abs real_zero) real_zero
              (real_abs_eq_compat
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m O)) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) cn)))
                real_zero
                (real_plus_opp (b5c_J (real_const (b5dL_tkq q0 m O)) cn)))
              real_abs_zero_req)))
        (RealSetoid.real_eq_le real_zero
          (real_const (qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
          (real_eq_sym (real_const (qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
            real_zero
            (real_eq_of_zero_diff
              (real_const (qplus (b5dL_Qnsum b O) (b5dL_Qnsum e O)))
              real_zero)))
    | S n0 ->
      let hmid = b5dL_tkC q0 m n0 in
      let hstep_n = hstep n0 __ hmid cn in
      let hih_n = f n0 hmid c0' in
      let htri =
        real_abs_triangle_le_eps
          (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)))
          (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
            (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))
          (real_const (e n0))
          (real_const_pos (e n0)
            (qlt_to_QltT { qnum = Z0; qden = XH } (e n0)))
      in
      let hring =
        real_eq_of_zero_diff
          (real_plus
            (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)))
            (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
              (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
          (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))
      in
      let hmain =
        RealSetoid.real_le_id_l
          (real_abs
            (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
          (real_abs
            (real_plus
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)))
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))))
          (real_plus
            (real_plus
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid))))
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))))
            (real_const (e n0)))
          (real_abs_eq_compat
            (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))
            (real_plus
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)))
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
            (real_eq_sym
              (real_plus
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)))
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))
              hring))
          htri
      in
      let hrhs =
        real_le_plus_compat
          (real_plus
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid))))
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))))
          (real_plus (real_const (b n0))
            (real_const (qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
          (real_const (e n0)) (real_const (e n0))
          (real_le_plus_compat
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid))))
            (real_const (b n0))
            (real_abs
              (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
            (real_const (qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))) hstep_n
            hih_n)
          (real_le_refl (real_const (e n0)))
      in
      real_le_trans
        (real_abs
          (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
            (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
        (real_plus
          (real_plus (real_const (b n0))
            (real_const (qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
          (real_const (e n0)))
        (real_const (qplus (b5dL_Qnsum b (S n0)) (b5dL_Qnsum e (S n0))))
        (real_le_trans
          (real_abs
            (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
              (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0'))))
          (real_plus
            (real_plus
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S n0))) cn)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid))))
              (real_abs
                (real_plus (b5c_J (real_const (b5dL_tkq q0 m n0)) hmid)
                  (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0')))))
            (real_const (e n0)))
          (real_plus
            (real_plus (real_const (b n0))
              (real_const (qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
            (real_const (e n0)))
          hmain hrhs)
        (RealSetoid.real_eq_le
          (real_plus
            (real_plus (real_const (b n0))
              (real_const (qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
            (real_const (e n0)))
          (real_const (qplus (b5dL_Qnsum b (S n0)) (b5dL_Qnsum e (S n0))))
          (real_eq_of_zero_diff
            (real_plus
              (real_plus (real_const (b n0))
                (real_const (qplus (b5dL_Qnsum b n0) (b5dL_Qnsum e n0))))
              (real_const (e n0)))
            (real_const (qplus (b5dL_Qnsum b (S n0)) (b5dL_Qnsum e (S n0))))))
  in f m cM c0

(** val b5dL_eps_real_lower :
    real -> real_lt -> (q, (qltT, real_le) and0) sigT **)

let b5dL_eps_real_lower e = function
| ExistT (x, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
  (RealSetoid.real_lt_le_iff_req
    (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) e (Inl (ExistT
    ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (x0, (fun n _ ->
    qltT_eq_compat_r
      (qminus (projT1 e n)
        (projT1 (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) n))
      (qminus (projT1 e n) (qdiv x { qnum = (Zpos (XO XH)); qden = XH }))
      (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
        (qminus (projT1 e n) (qdiv x { qnum = (Zpos (XO XH)); qden = XH })))))))))))))))

(** val b5dL_J_zero_on_grid_premise :
    q -> nat -> q -> (nat -> __ -> cw_unit -> cw_unit -> real_le) -> cw_unit
    -> real_le **)

let b5dL_J_zero_on_grid_premise q0 m epsQ hstep hq =
  let c0 = b5dL_tkC q0 m O in
  let cM = b5dL_tkC q0 m m in
  let hgrid =
    b5dL_J_grid_premise q0 m (b5dL_bk q0 m epsQ) (fun _ -> b5dL_epsQ1 m epsQ)
      (fun k _ -> hstep k __) c0 cM
  in
  let hbrM =
    b5p2_J_wd (real_const (b5dL_tkq q0 m m)) (real_const q0) cM hq
      (b5dH_real_const_qeq (b5dL_tkq q0 m m) q0)
  in
  let hbr0 =
    b5p2_J_wd (real_const (b5dL_tkq q0 m O))
      (real_const { qnum = Z0; qden = XH }) c0 b5c_unit_zero
      (b5dH_real_const_qeq (b5dL_tkq q0 m O) { qnum = Z0; qden = XH })
  in
  let habs =
    real_abs_eq_compat
      (real_plus (b5c_J (real_const q0) hq)
        (real_opp (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero)))
      (real_plus (b5c_J (real_const (b5dL_tkq q0 m m)) cM)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0)))
      (RealSetoid.real_eq_plus_compat (b5c_J (real_const q0) hq)
        (real_opp (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero))
        (b5c_J (real_const (b5dL_tkq q0 m m)) cM)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0))
        (real_eq_sym (b5c_J (real_const (b5dL_tkq q0 m m)) cM)
          (b5c_J (real_const q0) hq) hbrM)
        (RealSetoid.real_eq_opp_compat
          (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero)
          (b5c_J (real_const (b5dL_tkq q0 m O)) c0)
          (real_eq_sym (b5c_J (real_const (b5dL_tkq q0 m O)) c0)
            (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero) hbr0)))
  in
  real_le_trans
    (real_abs
      (real_plus (b5c_J (real_const q0) hq)
        (real_opp (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero))))
    (real_abs
      (real_plus (b5c_J (real_const (b5dL_tkq q0 m m)) cM)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0))))
    (real_const epsQ)
    (RealSetoid.real_eq_le
      (real_abs
        (real_plus (b5c_J (real_const q0) hq)
          (real_opp
            (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero))))
      (real_abs
        (real_plus (b5c_J (real_const (b5dL_tkq q0 m m)) cM)
          (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0))))
      habs)
    (RealSetoid.real_le_id_r
      (real_abs
        (real_plus (b5c_J (real_const (b5dL_tkq q0 m m)) cM)
          (real_opp (b5c_J (real_const (b5dL_tkq q0 m O)) c0))))
      (real_const
        (qplus (b5dL_Qnsum (b5dL_bk q0 m epsQ) m)
          (b5dL_Qnsum (fun _ -> b5dL_epsQ1 m epsQ) m)))
      (real_const epsQ)
      (b5dH_real_const_qeq
        (qplus (b5dL_Qnsum (b5dL_bk q0 m epsQ) m)
          (b5dL_Qnsum (fun _ -> b5dL_epsQ1 m epsQ) m))
        epsQ)
      hgrid)

(** val b5dL_E_rational_zero_premise :
    q -> (q -> __ -> (nat, (natLe, nat -> __ -> cw_unit -> cw_unit -> real_le)
    and0) sigT) -> cw_unit -> real_eq **)

let b5dL_E_rational_zero_premise q0 hmod hq =
  b5dH_E_zero_of_J_zero (real_const q0) hq
    (b4_abs_le_forall_eps_eq (b5c_J (real_const q0) hq) real_zero (fun e he ->
      let s = b5dL_eps_real_lower e he in
      let ExistT (x, a) = s in
      let Pair (_, r) = a in
      let s0 = hmod x __ in
      let ExistT (x0, a0) = s0 in
      let Pair (_, r0) = a0 in
      let hle_c = b5dL_J_zero_on_grid_premise q0 x0 x r0 hq in
      let habs0 =
        real_abs_eq_compat
          (real_plus (b5c_J (real_const q0) hq) (real_opp real_zero))
          (real_plus (b5c_J (real_const q0) hq)
            (real_opp
              (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero)))
          (RealSetoid.real_eq_plus_compat (b5c_J (real_const q0) hq)
            (real_opp real_zero) (b5c_J (real_const q0) hq)
            (real_opp
              (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero))
            (real_eq_refl (b5c_J (real_const q0) hq))
            (RealSetoid.real_eq_opp_compat real_zero
              (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero)
              (real_eq_sym
                (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero)
                real_zero b5dH_J_zero0)))
      in
      real_le_trans
        (real_abs (real_plus (b5c_J (real_const q0) hq) (real_opp real_zero)))
        (real_const x) e
        (RealSetoid.real_le_id_l
          (real_abs
            (real_plus (b5c_J (real_const q0) hq) (real_opp real_zero)))
          (real_abs
            (real_plus (b5c_J (real_const q0) hq)
              (real_opp
                (b5c_J (real_const { qnum = Z0; qden = XH }) b5c_unit_zero))))
          (real_const x) habs0 hle_c)
        r))

(** val b5dP_S_diff_closed_r_M_exp_tail :
    q -> real -> (nat -> qleT') -> q -> nat -> real -> real_lt -> (real,
    (real_lt, real -> real_lt -> real -> real_lt -> real_le) and0) sigT **)

let b5dP_S_diff_closed_r_M_exp_tail r x hxr m nM eps heps =
  let k2 =
    qinv
      (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
        (qplus m { qnum = (Zpos XH); qden = XH }))
  in
  let k2p =
    qinv
      (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
        (qplus m { qnum = (Zpos XH); qden = XH }))
  in
  let hk2T = b5l_k_posT m in
  let hk2pT = b5l_k_posT m in
  let h2T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO XH) }
  in
  let h4T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      XH)) }
  in
  let h8T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XO XH))) }
  in
  let h16T =
    qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
      (XO (XO XH)))) }
  in
  let eps1 = real_mult eps (real_const { qnum = (Zpos XH); qden = (XO XH) })
  in
  let heps1 =
    real_mult_positive eps (real_const { qnum = (Zpos XH); qden = (XO XH) })
      heps (real_const_pos { qnum = (Zpos XH); qden = (XO XH) } h2T)
  in
  let eps2 =
    real_mult eps (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
  in
  let heps2 =
    real_mult_positive eps
      (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) heps
      (real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } h4T)
  in
  let s = b5dK_exp_part_bound_closed_r_exp r x hxr eps1 heps1 in
  let ExistT (x0, a) = s in
  let Pair (r0, r1) = a in
  let s0 = b5dK_gdiff_pts_r_exp r x hxr eps2 heps2 k2 k2p hk2T hk2pT in
  let ExistT (x1, a0) = s0 in
  let Pair (r2, s1) = a0 in
  let delta = real_min x0 x1 in
  let hd0 = real_min_pos x0 x1 r0 r2 in
  ExistT (delta, (Pair (hd0, (fun h hh eps' heps' ->
  let s2 = b5n_eps_proj_lt eps heps in
  let ExistT (_, a1) = s2 in
  let Pair (_, s3) = a1 in
  let ExistT (x2, _) = s3 in
  let hhE = real_min_lt_l h x0 x1 hh in
  let hhG = real_min_lt_r h x0 x1 hh in
  let s4 = b5n_eps_proj_lt eps' heps' in
  let ExistT (x3, a2) = s4 in
  let Pair (_, s5) = a2 in
  let ExistT (x4, _) = s5 in
  let eta = qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x3 in
  let hetaT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x3)
  in
  let eps1' =
    real_mult eps' (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) })
  in
  let heps1' =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO XH)) }) heps'
      (real_const_pos { qnum = (Zpos XH); qden = (XO (XO XH)) } h4T)
  in
  let shE =
    real_mult eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) })
  in
  let hshE =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }) heps'
      (real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) }
        h16T)
  in
  let eps2' =
    real_mult eps' (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })
  in
  let heps2' =
    real_mult_positive eps'
      (real_const { qnum = (Zpos XH); qden = (XO (XO (XO XH))) }) heps'
      (real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } h8T)
  in
  let m0 = qmult { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO XH))))) } x3
  in
  let hm0T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO XH))))) } x3)
  in
  let err =
    real_plus (b5a_S (real_plus x h))
      (real_opp
        (real_plus (b5a_S x)
          (real_mult (real_mult x (b5a_S x)) (real_mult (b5a_atan_d x) h))))
  in
  let eobj =
    real_mult (b5a_S x)
      (real_plus (cauchy_real_exp (b5f_v x h))
        (real_opp (real_plus real_one (b5f_v x h))))
  in
  let wS =
    real_plus (b5f_v x h)
      (real_opp (real_mult (real_mult x (b5a_atan_d x)) h))
  in
  let gob = real_mult (b5a_S x) wS in
  let bexp = real_plus (real_mult eps1 (real_abs h)) eps1' in
  let hexp_le = r1 h hhE eps1' heps1' in
  let s6 = b5i_abs_le_pointwise eobj bexp hexp_le shE hshE in
  let ExistT (x5, _) = s6 in
  let s7 = s1 h hhG eps2' heps2' in
  let ExistT (x6, _) = s7 in
  let s8 = b5l_eq_abs_tri err eobj gob m0 (b5f_S_err_decomp x h) hm0T in
  let ExistT (x7, _) = s8 in
  Inl (ExistT (eta, (Pair (hetaT,
  (let nmax =
     Nat.max nM (Nat.max x2 (Nat.max x4 (Nat.max x5 (Nat.max x6 x7))))
   in
   ExistT (nmax, (fun n _ ->
   qlt_to_QltT eta
     (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
       (projT1 (real_abs err) n)))))))))))))

(** val b5dQ_min_lb :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let b5dQ_min_lb lb a b hltA hltB =
  let ExistT (x, a0) = hltA in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hltB in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  let e = qmin x x1 in
  let he = qlt_to_QltT { qnum = Z0; qden = XH } e in
  ExistT (e, (Pair (he, (ExistT ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT e (qminus (projT1 (real_min a b) n) (projT1 lb n))))))))

(** val b5dQ_Hq32T : qltT **)

let b5dQ_Hq32T =
  Id_refl

(** val b5dQ_chain3 : q -> q **)

let b5dQ_chain3 a =
  qmult (qmult a { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO XH))))) })
    { qnum = (Zpos XH); qden = (XO (XO XH)) }

(** val b5dQ_chain4 : q -> q **)

let b5dQ_chain4 a =
  qmult (b5dQ_chain3 a) { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO (XO (XI XH))))))))))))) }

(** val b5dQ_vB : q -> q -> q **)

let b5dQ_vB q0 a =
  qmin
    (qmult { qnum = (Zpos XH); qden = (XO XH) }
      (qminus { qnum = (Zpos XH); qden = XH } q0))
    (qmult (b5dQ_chain4 a)
      (qinv
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
          (qplus
            (b3rr_C2
              (qmult { qnum = (Zpos XH); qden = (XO XH) }
                (qplus { qnum = (Zpos XH); qden = XH } q0)))
            { qnum = (Zpos XH); qden = XH }))))

(** val b5dQ_margin_lemma : q -> qltT **)

let b5dQ_margin_lemma v =
  qlt_to_QltT (qmult v { qnum = (Zpos XH); qden = (XO (XO XH)) })
    (qminus v (qmult v { qnum = (Zpos XH); qden = (XO XH) }))

(** val b5dQ_vSC : q -> q -> q **)

let b5dQ_vSC q0 a =
  qmin
    (qmin (qmin (b5dQ_vB q0 a) { qnum = (Zpos XH); qden = (XO XH) })
      (qmult (b5dQ_chain3 a) { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XI XH)))))))))) }))
    (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) }
      (qinv
        (qplus { qnum = (Zpos XH); qden = XH }
          (qmult (b5dQ_chain3 a) { qnum = (Zpos XH); qden = (XO (XO (XO (XO
            (XO (XO (XO (XO (XO (XO (XO (XO (XI XH))))))))))))) }))))

(** val b5dQ_vE : q -> q -> q **)

let b5dQ_vE q0 a =
  qmin (qmin (b5dQ_vSC q0 a) (b5dQ_vSC q0 a))
    (qmult (qmult a { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO XH))))) })
      { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      XH)))))))))) })

(** val b5dQ_lb_E : q -> real -> (nat -> qleT') -> q -> real_lt **)

let b5dQ_lb_E q0 _ _ a =
  ExistT ((qmult (b5dQ_vE q0 a) { qnum = (Zpos XH); qden = (XO (XO XH)) }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qmult (b5dQ_vE q0 a) { qnum = (Zpos XH); qden = (XO (XO XH)) })),
    (ExistT (O, (fun _ _ -> b5dQ_margin_lemma (b5dQ_vE q0 a)))))))

(** val b5dQ_Hq14T : qltT **)

let b5dQ_Hq14T =
  qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = (XO (XO
    XH)) }

(** val b5dQ_Hq1T : qltT **)

let b5dQ_Hq1T =
  qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }

(** val b5dQ_S_tk0_eq_one : q -> nat -> real_eq **)

let b5dQ_S_tk0_eq_one q0 m =
  real_eq_trans (b5a_S (real_const (b5dL_tkq q0 m O)))
    (b5a_S (real_const { qnum = Z0; qden = XH })) real_one
    (b5m_S_wd (real_const (b5dL_tkq q0 m O))
      (real_const { qnum = Z0; qden = XH })
      (b5dH_real_const_qeq (b5dL_tkq q0 m O) { qnum = Z0; qden = XH }))
    b5d4_S_const0_eq_one

(** val b5dQ_S_lb_tail_k0 : q -> nat -> (nat, __) sigT **)

let b5dQ_S_lb_tail_k0 q0 m =
  let s =
    b5dQ_S_tk0_eq_one q0 m { qnum = (Zpos XH); qden = (XO (XO XH)) }
      b5dQ_Hq14T
  in
  let ExistT (x, _) = s in ExistT (x, __)

(** val b5dQ_S_ub_tail_k0 : q -> nat -> (nat, __) sigT **)

let b5dQ_S_ub_tail_k0 q0 m =
  let s = b5dQ_S_tk0_eq_one q0 m { qnum = (Zpos XH); qden = XH } b5dQ_Hq1T in
  let ExistT (x, _) = s in ExistT (x, __)

(** val b5dQ_S_ub_tail_restate :
    (nat -> q) -> (nat, __) sigT -> (nat, __) sigT **)

let b5dQ_S_ub_tail_restate _ = function
| ExistT (x, _) -> ExistT (x, __)

(** val b5dQ_S_lb_tail_kS : q -> nat -> nat -> (nat, __) sigT **)

let b5dQ_S_lb_tail_kS q0 m k =
  b5dQ_S_ub_tail_restate (fun n ->
    projT1 (b5a_S (real_const (b5dL_tkq q0 m k))) n)
    (b5a_S_ge_one (real_const (b5dL_tkq q0 m k))
      (real_const_pos_f1 (b5dL_tkq q0 m k)))

(** val b5dQ_S_ub_tail_kS : q -> nat -> nat -> (nat, __) sigT **)

let b5dQ_S_ub_tail_kS q0 m k =
  b5dE_S_ub_tail_q (b5dL_tkq q0 m k)

(** val b5dQ_tkq_Hxr : q -> nat -> nat -> nat -> qleT' **)

let b5dQ_tkq_Hxr q0 m k n =
  qle_to_QleT' (qabs (projT1 (real_const (b5dL_tkq q0 m k)) n)) q0

(** val b5dQ_xph_unit : q -> nat -> nat -> cw_unit **)

let b5dQ_xph_unit q0 m k n =
  qle_to_QleT'
    (qabs
      (projT1
        (real_plus (real_const (b5dL_tkq q0 m k))
          (real_const (b5dL_qdiv q0 m)))
        n))
    { qnum = (Zpos XH); qden = XH }

(** val b5dQ_rhs_bk : q -> nat -> nat -> q -> real_eq **)

let b5dQ_rhs_bk q0 m k epsQ =
  let heta =
    real_eq_trans (real_abs (real_const (b5dL_qdiv q0 m)))
      (real_const (qabs (b5dL_qdiv q0 m))) (real_const (b5dL_qdiv q0 m))
      (b5dL_abs_const (b5dL_qdiv q0 m))
      (b5dH_real_const_qeq (qabs (b5dL_qdiv q0 m)) (b5dL_qdiv q0 m))
  in
  let hm =
    real_eq_trans
      (real_mult
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_abs (real_const (b5dL_qdiv q0 m))))
      (real_mult
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_const (b5dL_qdiv q0 m)))
      (real_const
        (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
          (b5dL_qdiv q0 m)))
      (RealSetoid.real_eq_mult_compat
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_abs (real_const (b5dL_qdiv q0 m)))
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_const (b5dL_qdiv q0 m))
        (real_eq_refl
          (real_const
            (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))))
        heta)
      (b5dL_mult_const
        (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
        (b5dL_qdiv q0 m))
  in
  real_eq_trans
    (real_plus
      (real_mult
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_abs (real_const (b5dL_qdiv q0 m))))
      (real_const (b5dL_epsQ1 m epsQ)))
    (real_plus
      (real_const
        (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
          (b5dL_qdiv q0 m)))
      (real_const (b5dL_epsQ1 m epsQ)))
    (real_const (b5dL_bk q0 m epsQ k))
    (RealSetoid.real_eq_plus_compat
      (real_mult
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_abs (real_const (b5dL_qdiv q0 m))))
      (real_const (b5dL_epsQ1 m epsQ))
      (real_const
        (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
          (b5dL_qdiv q0 m)))
      (real_const (b5dL_epsQ1 m epsQ)) hm
      (real_eq_refl (real_const (b5dL_epsQ1 m epsQ))))
    (real_eq_trans
      (real_plus
        (real_const
          (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
            (b5dL_qdiv q0 m)))
        (real_const (b5dL_epsQ1 m epsQ)))
      (real_const
        (qplus
          (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
            (b5dL_qdiv q0 m))
          (b5dL_epsQ1 m epsQ)))
      (real_const (b5dL_bk q0 m epsQ k))
      (b5dH_plus_const_eq
        (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
          (b5dL_qdiv q0 m))
        (b5dL_epsQ1 m epsQ))
      (real_eq_refl (real_const (b5dL_bk q0 m epsQ k))))

(** val b5dQ_J_tk_succ_bridge :
    q -> nat -> nat -> cw_unit -> cw_unit -> real_eq **)

let b5dQ_J_tk_succ_bridge q0 m k hk1 hp =
  b5p2_J_wd (real_const (b5dL_tkq q0 m (S k)))
    (real_plus (real_const (b5dL_tkq q0 m k)) (real_const (b5dL_qdiv q0 m)))
    hk1 hp
    (real_eq_trans (real_const (b5dL_tkq q0 m (S k)))
      (real_const (qplus (b5dL_tkq q0 m k) (b5dL_qdiv q0 m)))
      (real_plus (real_const (b5dL_tkq q0 m k)) (real_const (b5dL_qdiv q0 m)))
      (b5dH_real_const_qeq (b5dL_tkq q0 m (S k))
        (qplus (b5dL_tkq q0 m k) (b5dL_qdiv q0 m)))
      (real_eq_sym
        (real_plus (real_const (b5dL_tkq q0 m k))
          (real_const (b5dL_qdiv q0 m)))
        (real_const (qplus (b5dL_tkq q0 m k) (b5dL_qdiv q0 m)))
        (b5dH_plus_const_eq (b5dL_tkq q0 m k) (b5dL_qdiv q0 m))))

(** val b5dQ_J_cert_wd : q -> cw_unit -> cw_unit -> real_eq **)

let b5dQ_J_cert_wd t hx hx' =
  b5p2_J_wd (real_const t) (real_const t) hx hx' (real_eq_refl (real_const t))

(** val b5dQ_step_inst :
    q -> nat -> nat -> (nat -> qleT') -> cw_unit -> cw_unit -> cw_unit -> real
    -> real_le -> real_le **)

let b5dQ_step_inst q0 m k hxr hk1 hk hxh r hmain =
  RealSetoid.real_le_id_l
    (real_abs
      (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m k)) hk))))
    (real_abs
      (real_plus
        (b5c_J
          (real_plus (real_const (b5dL_tkq q0 m k))
            (real_const (b5dL_qdiv q0 m)))
          hxh)
        (real_opp
          (b5c_J (real_const (b5dL_tkq q0 m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q0 m k)) q0 hxr)))))
    r
    (real_abs_eq_compat
      (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m k)) hk)))
      (real_plus
        (b5c_J
          (real_plus (real_const (b5dL_tkq q0 m k))
            (real_const (b5dL_qdiv q0 m)))
          hxh)
        (real_opp
          (b5c_J (real_const (b5dL_tkq q0 m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q0 m k)) q0 hxr))))
      (RealSetoid.real_eq_plus_compat
        (b5c_J (real_const (b5dL_tkq q0 m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m k)) hk))
        (b5c_J
          (real_plus (real_const (b5dL_tkq q0 m k))
            (real_const (b5dL_qdiv q0 m)))
          hxh)
        (real_opp
          (b5c_J (real_const (b5dL_tkq q0 m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q0 m k)) q0 hxr)))
        (b5dQ_J_tk_succ_bridge q0 m k hk1 hxh)
        (RealSetoid.real_eq_opp_compat
          (b5c_J (real_const (b5dL_tkq q0 m k)) hk)
          (b5c_J (real_const (b5dL_tkq q0 m k))
            (b3rr_dom_r1 (real_const (b5dL_tkq q0 m k)) q0 hxr))
          (b5dQ_J_cert_wd (b5dL_tkq q0 m k) hk
            (b3rr_dom_r1 (real_const (b5dL_tkq q0 m k)) q0 hxr)))))
    hmain

(** val b5dQ_lbSdiff_cE : q -> q -> q **)

let b5dQ_lbSdiff_cE q0 a =
  qmin
    (qmin
      (qmult
        (qmin { qnum = (Zpos XH); qden = (XO XH) }
          (qmult
            (qmult
              (qmult (qmult a { qnum = (Zpos XH); qden = (XO XH) })
                (qinv (b5j_Kvq q0)))
              { qnum = (Zpos XH); qden = (XI XH) })
            { qnum = (Zpos XH); qden = (XO (XO XH)) }))
        { qnum = (Zpos XH); qden = (XO (XO XH)) })
      (qmult
        (qmin { qnum = (Zpos XH); qden = (XO XH) }
          (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } b5j_kL))
        { qnum = (Zpos XH); qden = (XO (XO (XI XH))) }))
    { qnum = (Zpos XH); qden = (XO XH) }

(** val b5dQ_lbSdiff_cG : q -> q -> q **)

let b5dQ_lbSdiff_cG _ a =
  qmin
    (qmin
      (qmult
        (qmin { qnum = (Zpos XH); qden = (XO XH) }
          (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) }
            (qmult (qmult a { qnum = (Zpos XH); qden = (XO (XO XH)) })
              (qmult
                (qinv
                  (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
                    (qplus { qnum = (Zpos (XO XH)); qden = XH } { qnum = (Zpos
                      XH); qden = XH })))
                { qnum = (Zpos XH); qden = (XO XH) }))))
        { qnum = (Zpos XH); qden = (XO (XO (XI XH))) })
      (qmult (qmult a { qnum = (Zpos XH); qden = (XO (XO XH)) })
        (qmult
          (qinv
            (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
              (qplus { qnum = (Zpos (XO XH)); qden = XH } { qnum = (Zpos XH);
                qden = XH })))
          { qnum = (Zpos XH); qden = (XO XH) })))
    { qnum = (Zpos XH); qden = (XO XH) }

(** val b5dQ_lbSdiff_cS : q -> q -> q **)

let b5dQ_lbSdiff_cS q0 a =
  qmin (b5dQ_lbSdiff_cE q0 a) (b5dQ_lbSdiff_cG q0 a)

(** val b5dQ_lbSdiff_val : q -> q -> q **)

let b5dQ_lbSdiff_val q0 a =
  qmult (b5dQ_lbSdiff_cS q0 a) { qnum = (Zpos XH); qden = (XO XH) }

(** val b5dQ_lb_Sdiff : q -> real -> (nat -> qleT') -> q -> nat -> real_lt **)

let b5dQ_lb_Sdiff q0 x hxr a nub =
  let cS = b5dQ_lbSdiff_cS q0 a in
  let lb = qmult cS { qnum = (Zpos XH); qden = (XO XH) } in
  let e = qmult lb { qnum = (Zpos XH); qden = (XO XH) } in
  ExistT (e, (Pair ((qlt_to_QltT { qnum = Z0; qden = XH } e), (ExistT (nub,
  (fun n _ ->
  qlt_to_QltT e
    (qminus
      (projT1
        (projT1
          (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
            qden = XH } nub (real_const a)
            (real_const_pos a (qlt_to_QltT { qnum = Z0; qden = XH } a))))
        n)
      (projT1 (real_const (b5dQ_lbSdiff_val q0 a)) n))))))))

(** val b5dQ_tau : q -> q **)

let b5dQ_tau q0 =
  qmult { qnum = (Zpos XH); qden = (XO XH) }
    (qinv
      (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
        (qplus (qmult q0 { qnum = (Zpos (XO XH)); qden = XH }) { qnum = (Zpos
          XH); qden = XH })))

(** val b5dQ_kS : q -> q **)

let b5dQ_kS q0 =
  qmult
    (qmult
      (qmult { qnum = (Zpos XH); qden = (XO XH) }
        (qmult { qnum = (Zpos XH); qden = (XO XH) } { qnum = (Zpos XH); qden =
          (XO XH) }))
      { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })
    (qinv
      (qplus
        (qplus { qnum = (Zpos XH); qden = XH }
          (qmult q0 { qnum = (Zpos XH); qden = XH }))
        { qnum = (Zpos XH); qden = XH }))

(** val b5dQ_m4 : q -> q -> q **)

let b5dQ_m4 q0 epsQ =
  qmin
    (qmin
      (qmin
        (qmult
          (b5dQ_vE q0
            (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
          { qnum = (Zpos XH); qden = (XO XH) })
        (b5dQ_lbSdiff_val q0
          (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
            (b5dQ_kS q0))))
      (b5dQ_lbSdiff_val q0 { qnum = (Zpos XH); qden = XH }))
    (b5dQ_tau q0)

(** val b5dQ_delta0 : q -> q -> q **)

let b5dQ_delta0 q0 epsQ =
  qmult (b5dQ_m4 q0 epsQ) { qnum = (Zpos XH); qden = (XO XH) }

(** val b5dQ_p4g_leaf_E : q -> real -> (nat -> qleT') -> q -> real_lt **)

let b5dQ_p4g_leaf_E =
  b5dQ_lb_E

(** val b5dQ_p4g_leaf_S :
    q -> real -> (nat -> qleT') -> q -> nat -> real_lt **)

let b5dQ_p4g_leaf_S =
  b5dQ_lb_Sdiff

(** val b5dQ_p4g_J_tail_lb_var :
    q -> q -> nat -> nat -> (nat -> qleT') -> nat -> nat -> (real, (real_lt,
    (real -> real_lt -> (nat -> qleT') -> real -> real_lt -> real_le, real_lt)
    and0) and0) sigT **)

let b5dQ_p4g_J_tail_lb_var q0 epsQ mg k hxr nA nM =
  let x = real_const (b5dL_tkq q0 mg k) in
  let a = qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0) in
  let cA = { qnum = (Zpos XH); qden = (XO XH) } in
  let m = { qnum = (Zpos (XO XH)); qden = XH } in
  let ms = { qnum = (Zpos XH); qden = XH } in
  let mc = { qnum = (Zpos XH); qden = XH } in
  let eps = real_const a in
  let heps = real_const_pos a (qlt_to_QltT { qnum = Z0; qden = XH } a) in
  let hx = b3rr_dom_r1 x q0 hxr in
  let cB = qmult cA { qnum = (Zpos XH); qden = (XO XH) } in
  let mE = qplus ms (qmult q0 mc) in
  let kE = qmult cB { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } in
  let kEp = qmult cB { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) } in
  let kapE = qmult cB { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) } in
  let invM1 = qinv (qplus mE { qnum = (Zpos XH); qden = XH }) in
  let kS =
    qmult (qmult (qmult cA cB) { qnum = (Zpos XH); qden = (XO (XO (XO XH))) })
      invM1
  in
  let kSp =
    qmult
      (qmult (qmult cA cB) { qnum = (Zpos XH); qden = (XO (XO (XO (XO
        XH)))) })
      invM1
  in
  let kapS =
    qmult
      (qmult (qmult cA cB) { qnum = (Zpos XH); qden = (XO (XO (XO (XO
        XH)))) })
      invM1
  in
  let k1 = qplus (qmult q0 m) { qnum = (Zpos XH); qden = XH } in
  let tau =
    qmult cA (qinv (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } k1))
  in
  let mu = qmult cA { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) } in
  let kapS2 = qmult cA { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) } in
  let hkEpT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult cB { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) })
  in
  let hkapET =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult cB { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) })
  in
  let hkSpT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult
        (qmult (qmult cA cB) { qnum = (Zpos XH); qden = (XO (XO (XO (XO
          XH)))) })
        invM1)
  in
  let hkapST =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult
        (qmult (qmult cA cB) { qnum = (Zpos XH); qden = (XO (XO (XO (XO
          XH)))) })
        invM1)
  in
  let htauT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult cA
        (qinv (qmult { qnum = (Zpos (XO (XO (XO XH)))); qden = XH } k1)))
  in
  let hmuT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult cA { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) })
  in
  let hkapS2T =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult cA { qnum = (Zpos XH); qden = (XO (XO (XO (XO XH)))) })
  in
  let epsE = real_mult eps (real_const kE) in
  let epsS = real_const (qmult a kS) in
  let _UU03b4_E =
    projT1
      (b5dI_E_diff_closed_r_exp q0 x hxr { qnum = (Zpos XH); qden = XH }
        { qnum = (Zpos XH); qden = XH } b5d3_exp_arch4_C b5d3_exp_arch4_C_ge1
        b5d3_exp_arch4_C_all epsE
        (b5dI_real_mult_positive_exp (real_const a)
          (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO
            XH))))) })
          (b5dM_real_const_pos a (qlt_to_QltT { qnum = Z0; qden = XH } a))
          (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO
            XH))))) } b5dQ_Hq32T)))
  in
  let h_UU03b4_E0 =
    fst
      (projT2
        (b5dI_E_diff_closed_r_exp q0 x hxr { qnum = (Zpos XH); qden = XH }
          { qnum = (Zpos XH); qden = XH } b5d3_exp_arch4_C
          b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all epsE
          (b5dI_real_mult_positive_exp (real_const a)
            (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO
              XH))))) })
            (b5dM_real_const_pos a (qlt_to_QltT { qnum = Z0; qden = XH } a))
            (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO
              (XO XH))))) } b5dQ_Hq32T))))
  in
  let h_UU03b4_E =
    snd
      (projT2
        (b5dI_E_diff_closed_r_exp q0 x hxr { qnum = (Zpos XH); qden = XH }
          { qnum = (Zpos XH); qden = XH } b5d3_exp_arch4_C
          b5d3_exp_arch4_C_ge1 b5d3_exp_arch4_C_all epsE
          (b5dI_real_mult_positive_exp (real_const a)
            (real_const { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO
              XH))))) })
            (b5dM_real_const_pos a (qlt_to_QltT { qnum = Z0; qden = XH } a))
            (b5dM_real_const_pos { qnum = (Zpos XH); qden = (XO (XO (XO (XO
              (XO XH))))) } b5dQ_Hq32T))))
  in
  let _UU03b4_S1 =
    projT1
      (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
        qden = XH } nM epsS
        (real_const_pos (qmult a kS)
          (qlt_to_QltT { qnum = Z0; qden = XH } (qmult a kS))))
  in
  let h_UU03b4_S10 =
    fst
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
          qden = XH } nM epsS
          (real_const_pos (qmult a kS)
            (qlt_to_QltT { qnum = Z0; qden = XH } (qmult a kS)))))
  in
  let h_UU03b4_S1 =
    snd
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
          qden = XH } nM epsS
          (real_const_pos (qmult a kS)
            (qlt_to_QltT { qnum = Z0; qden = XH } (qmult a kS)))))
  in
  let _UU03b4_S2 =
    projT1
      (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
        qden = XH } nM (real_const { qnum = (Zpos XH); qden = XH })
        (real_const_pos { qnum = (Zpos XH); qden = XH }
          (qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden =
            XH })))
  in
  let h_UU03b4_S20 =
    fst
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
          qden = XH } nM (real_const { qnum = (Zpos XH); qden = XH })
          (real_const_pos { qnum = (Zpos XH); qden = XH }
            (qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden =
              XH }))))
  in
  let h_UU03b4_S2 =
    snd
      (projT2
        (b5dP_S_diff_closed_r_M_exp_tail q0 x hxr { qnum = (Zpos (XO XH));
          qden = XH } nM (real_const { qnum = (Zpos XH); qden = XH })
          (real_const_pos { qnum = (Zpos XH); qden = XH }
            (qlt_to_QltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden =
              XH }))))
  in
  let delta =
    real_min (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau)
  in
  let hdpos =
    real_min_pos (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau)
      (real_min_pos (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2
        (real_min_pos _UU03b4_E _UU03b4_S1 h_UU03b4_E0 h_UU03b4_S10)
        h_UU03b4_S20)
      (real_const_pos tau htauT)
  in
  ExistT (delta, (Pair (hdpos, (Pair ((fun h hh hxh eps' heps' ->
  let s = b5dM_b5n_eps_proj_lt eps heps in
  let ExistT (_, a0) = s in
  let Pair (_, s0) = a0 in
  let ExistT (x0, _) = s0 in
  let hh1 =
    real_min_lt_l h (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau) hh
  in
  let hh_UU03c4_ =
    real_min_lt_r h (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2)
      (real_const tau) hh
  in
  let hh2 = real_min_lt_l h (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2 hh1 in
  let hhS2 = real_min_lt_r h (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2 hh1 in
  let hhE = real_min_lt_l h _UU03b4_E _UU03b4_S1 hh2 in
  let hhS1 = real_min_lt_r h _UU03b4_E _UU03b4_S1 hh2 in
  let s1 = b5dM_b5n_eps_proj_lt eps' heps' in
  let ExistT (x1, a1) = s1 in
  let Pair (_, s2) = a1 in
  let ExistT (x2, _) = s2 in
  let eta = qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x1 in
  let hetaT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO (XO (XO XH))) } x1)
  in
  let epsE' = real_mult eps' (real_const kEp) in
  let hepsE' =
    real_mult_positive eps' (real_const kEp) heps' (real_const_pos kEp hkEpT)
  in
  let shE = real_mult eps' (real_const kapE) in
  let hshE =
    real_mult_positive eps' (real_const kapE) heps'
      (real_const_pos kapE hkapET)
  in
  let epsS' = real_mult eps' (real_const kSp) in
  let hepsS' =
    real_mult_positive eps' (real_const kSp) heps' (real_const_pos kSp hkSpT)
  in
  let shS = real_mult eps' (real_const kapS) in
  let hshS =
    real_mult_positive eps' (real_const kapS) heps'
      (real_const_pos kapS hkapST)
  in
  let hc_UU03bc_ = real_const_pos mu hmuT in
  let hc_UU03ba_S2 = real_const_pos kapS2 hkapS2T in
  let bE = real_plus (real_mult epsE (real_abs h)) epsE' in
  let s3 =
    b5i_abs_le_pointwise (b5e_E_err x hx h hxh) bE
      (h_UU03b4_E h hhE hxh epsE' hepsE') shE hshE
  in
  let ExistT (x3, _) = s3 in
  let bS1 = real_plus (real_mult epsS (real_abs h)) epsS' in
  let s4 =
    b5i_abs_le_pointwise (b5m_rS x h) bS1 (h_UU03b4_S1 h hhS1 epsS' hepsS')
      shS hshS
  in
  let ExistT (x4, _) = s4 in
  let bS2 =
    real_plus
      (real_mult (real_const { qnum = (Zpos XH); qden = XH }) (real_abs h))
      (real_const mu)
  in
  let s5 =
    b5i_abs_le_pointwise (b5m_rS x h) bS2
      (h_UU03b4_S2 h hhS2 (real_const mu) hc_UU03bc_) (real_const kapS2)
      hc_UU03ba_S2
  in
  let ExistT (x5, _) = s5 in
  let s6 = b5i_h_le_const h tau hh_UU03c4_ htauT in
  let ExistT (x6, _) = s6 in
  let s7 = b5dM_b5c_d_proj_le_one x in
  let ExistT (x7, _) = s7 in
  let s8 = b5m_J_dec_proj x h hx hxh in
  let ExistT (x8, _) = s8 in
  let nmax =
    Nat.max nM
      (Nat.max (Nat.max x0 x2)
        (Nat.max (Nat.max x8 x6)
          (Nat.max (Nat.max x3 (Nat.max x4 x5)) (Nat.max nA x7))))
  in
  Inl (ExistT (eta, (Pair (hetaT, (ExistT (nmax, (fun n _ ->
  qlt_to_QltT eta
    (qminus (projT1 (real_plus (real_mult eps (real_abs h)) eps') n)
      (projT1
        (real_abs
          (real_plus (b5c_J (real_plus x h) hxh) (real_opp (b5c_J x hx))))
        n)))))))))),
  (let hqE =
     real_const_lt (b5dQ_delta0 q0 epsQ)
       (qmult
         (b5dQ_vE q0
           (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
         { qnum = (Zpos XH); qden = (XO XH) })
   in
   let hlbE =
     b5dQ_p4g_leaf_E q0 x hxr
       (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
   in
   let hdE =
     real_lt_trans (real_const (b5dQ_delta0 q0 epsQ))
       (real_const
         (qmult
           (b5dQ_vE q0
             (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
           { qnum = (Zpos XH); qden = (XO XH) }))
       _UU03b4_E hqE hlbE
   in
   let hqS1 =
     real_const_lt (b5dQ_delta0 q0 epsQ)
       (b5dQ_lbSdiff_val q0
         (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
           (b5dQ_kS q0)))
   in
   let hlbS1 =
     b5dQ_p4g_leaf_S q0 x hxr
       (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
         (b5dQ_kS q0))
       nM
   in
   let hdS1 =
     real_lt_trans (real_const (b5dQ_delta0 q0 epsQ))
       (real_const
         (b5dQ_lbSdiff_val q0
           (qmult (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0))
             (b5dQ_kS q0))))
       _UU03b4_S1 hqS1 hlbS1
   in
   let hqS2 =
     real_const_lt (b5dQ_delta0 q0 epsQ)
       (b5dQ_lbSdiff_val q0 { qnum = (Zpos XH); qden = XH })
   in
   let hlbS2 = b5dQ_p4g_leaf_S q0 x hxr { qnum = (Zpos XH); qden = XH } nM in
   let hdS2 =
     real_lt_trans (real_const (b5dQ_delta0 q0 epsQ))
       (real_const (b5dQ_lbSdiff_val q0 { qnum = (Zpos XH); qden = XH }))
       _UU03b4_S2 hqS2 hlbS2
   in
   b5dQ_min_lb (real_const (b5dQ_delta0 q0 epsQ))
     (real_min (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2) (real_const tau)
     (b5dQ_min_lb (real_const (b5dQ_delta0 q0 epsQ))
       (real_min _UU03b4_E _UU03b4_S1) _UU03b4_S2
       (b5dQ_min_lb (real_const (b5dQ_delta0 q0 epsQ)) _UU03b4_E _UU03b4_S1
         hdE hdS1)
       hdS2)
     (real_const_lt (b5dQ_delta0 q0 epsQ) tau)))))))

(** val b5dQ_Hstep :
    q -> q -> nat -> nat -> (nat -> qleT') -> nat -> nat -> cw_unit -> cw_unit
    -> real_le **)

let b5dQ_Hstep q0 epsQ m k hxr nA nM hk hk1 =
  let vapp = b5dQ_p4g_J_tail_lb_var q0 epsQ m k hxr nA nM in
  let ExistT (x, a) = vapp in
  let Pair (_, a0) = a in
  let Pair (r, r0) = a0 in
  let h_UU03b7_c = real_const_lt (b5dL_qdiv q0 m) (b5dQ_delta0 q0 epsQ) in
  let h_UU03b7_d =
    real_lt_trans (real_const (b5dL_qdiv q0 m))
      (real_const (b5dQ_delta0 q0 epsQ)) x h_UU03b7_c r0
  in
  let heta =
    real_eq_trans (real_abs (real_const (b5dL_qdiv q0 m)))
      (real_const (qabs (b5dL_qdiv q0 m))) (real_const (b5dL_qdiv q0 m))
      (b5dL_abs_const (b5dL_qdiv q0 m))
      (b5dH_real_const_qeq (qabs (b5dL_qdiv q0 m)) (b5dL_qdiv q0 m))
  in
  let h_UU03b7_abs =
    RealSetoid.real_lt_compat (real_const (b5dL_qdiv q0 m))
      (real_abs (real_const (b5dL_qdiv q0 m))) x x
      (real_eq_sym (real_abs (real_const (b5dL_qdiv q0 m)))
        (real_const (b5dL_qdiv q0 m)) heta)
      (real_eq_refl x) h_UU03b7_d
  in
  let hxh = b5dQ_xph_unit q0 m k in
  let heps1pos =
    real_const_pos (b5dL_epsQ1 m epsQ)
      (qlt_to_QltT { qnum = Z0; qden = XH } (b5dL_epsQ1 m epsQ))
  in
  let hcore =
    r (real_const (b5dL_qdiv q0 m)) h_UU03b7_abs hxh
      (real_const (b5dL_epsQ1 m epsQ)) heps1pos
  in
  let hstepR =
    b5dQ_step_inst q0 m k hxr hk1 hk hxh
      (real_plus
        (real_mult
          (real_const
            (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
          (real_abs (real_const (b5dL_qdiv q0 m))))
        (real_const (b5dL_epsQ1 m epsQ)))
      hcore
  in
  RealSetoid.real_le_id_r
    (real_abs
      (real_plus (b5c_J (real_const (b5dL_tkq q0 m (S k))) hk1)
        (real_opp (b5c_J (real_const (b5dL_tkq q0 m k)) hk))))
    (real_plus
      (real_mult
        (real_const
          (qdiv epsQ (qmult { qnum = (Zpos (XO XH)); qden = XH } q0)))
        (real_abs (real_const (b5dL_qdiv q0 m))))
      (real_const (b5dL_epsQ1 m epsQ)))
    (real_const (b5dL_bk q0 m epsQ k)) (b5dQ_rhs_bk q0 m k epsQ) hstepR

(** val b5dQ_Hmod :
    q -> q -> (nat, (natLe, nat -> __ -> cw_unit -> cw_unit -> real_le) and0)
    sigT **)

let b5dQ_Hmod q0 epsQ =
  let s = q_arch_inv (qdiv (b5dQ_delta0 q0 epsQ) q0) in
  let ExistT (x, _) = s in
  let m = add x (S (S O)) in
  ExistT (m, (Pair ((natLe_lift (S O) m), (fun k _ ->
  match k with
  | O ->
    let s0 = b5dQ_S_lb_tail_k0 q0 m in
    let ExistT (x0, _) = s0 in
    let s1 = b5dQ_S_ub_tail_k0 q0 m in
    (fun hk hk1 ->
    let ExistT (x1, _) = s1 in
    b5dQ_Hstep q0 epsQ m O (b5dQ_tkq_Hxr q0 m O) x0 x1 hk hk1)
  | S n ->
    let s0 = b5dQ_S_lb_tail_kS q0 m (S n) in
    let ExistT (x0, _) = s0 in
    let s1 = b5dQ_S_ub_tail_kS q0 m (S n) in
    (fun hk hk1 ->
    let ExistT (x1, _) = s1 in
    b5dQ_Hstep q0 epsQ m (S n) (b5dQ_tkq_Hxr q0 m (S n)) x0 x1 hk hk1)))))

(** val b5dQ_E_rational_zero : q -> cw_unit -> real_eq **)

let b5dQ_E_rational_zero q0 hq =
  b5dL_E_rational_zero_premise q0 (fun x _ -> b5dQ_Hmod q0 x) hq

(** val b5dS_E_pair_close : q -> (nat, (q, (qltT, __) and0) sigT) sigT **)

let b5dS_E_pair_close eps =
  let ExistT (x, _) = b5b_arch2 in
  let s =
    q_arch_inv
      (qdiv eps (qmult { qnum = (Zpos (XO (XO (XI XH)))); qden = XH } x))
  in
  let ExistT (x0, _) = s in
  let k =
    qplus
      (qmult (qmult { qnum = (Zpos (XO XH)); qden = XH } x) { qnum =
        (Z.of_nat (S x0)); qden = XH })
      (qplus (qmult { qnum = (Zpos (XO XH)); qden = XH } x) { qnum = (Zpos
        XH); qden = XH })
  in
  let x1 =
    qdiv
      (qmult { qnum = (Zpos (XO XH)); qden = XH }
        (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }))
      k
  in
  ExistT (x0, (ExistT (x1, (Pair ((qlt_to_QltT { qnum = Z0; qden = XH } x1),
  __)))))

(** val b5dS_E_zero_on_unit :
    real -> cw_unit -> real_lt -> real_lt -> real_eq **)

let b5dS_E_zero_on_unit x hx hx0 hx1 epsQ _ =
  let hhalfT =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv epsQ { qnum = (Zpos (XO XH)); qden = XH })
  in
  let s = b5dS_E_pair_close (qdiv epsQ { qnum = (Zpos (XO XH)); qden = XH })
  in
  let ExistT (x0, s0) = s in
  let ExistT (x1, a) = s0 in
  let Pair (q0, _) = a in
  let ExistT (_, a0) = hx0 in
  let Pair (_, s1) = a0 in
  let ExistT (x2, _) = s1 in
  let ExistT (_, a1) = hx1 in
  let Pair (_, s2) = a1 in
  let ExistT (x3, _) = s2 in
  let s3 = projT2 x x1 q0 in
  let ExistT (x4, _) = s3 in
  let nq = Nat.max (Nat.max x2 x3) x4 in
  let q1 = projT1 x nq in
  let hq = b5c_const_unit q1 in
  let s4 =
    b5dQ_E_rational_zero q1 hq
      (qdiv epsQ { qnum = (Zpos (XO XH)); qden = XH }) hhalfT
  in
  let ExistT (x5, _) = s4 in
  ExistT ((Nat.max (Nat.max x0 nq) x5), (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 (real_E x hx) n) (projT1 real_zero n)))
    epsQ))

type qltT' = bool id

(** val qlt_to_QltT' : q -> q -> qltT' **)

let qlt_to_QltT' =
  qlt_to_QltT

(** val lw0m_xL : nat -> q **)

let lw0m_xL n =
  qmult lp_four (lp_odd n)

(** val lw0m_metric_congr : real -> real -> real -> real_eq -> real_eq **)

let lw0m_metric_congr x y z0 hxy eps heps =
  let s = hxy eps heps in
  let ExistT (x0, _) = s in
  ExistT (x0, (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (real_metric x z0) n) (projT1 (real_metric y z0) n)))
    eps))

(** val lw2_channel_f1_closed : real_eq **)

let lw2_channel_f1_closed =
  channel_f1 a3_h4_value_bridge (b5b_hsc_theorem b5dS_E_zero_on_unit)

(** val leibsep_metric_pi_transport :
    q -> q -> qltT -> (nat, nat -> natLe -> qltT) sigT **)

let leibsep_metric_pi_transport q0 eps heps =
  lw0m_metric_congr real_pi_geom cauchy_real_pi_leibniz (real_const q0)
    lw2_channel_f1_closed eps heps

(** val lw1m_height : q -> nat **)

let lw1m_height q0 =
  S (Coq_Pos.to_nat (qred q0).qden)

type lw1m_dist_pt = (nat, nat -> natLe -> qltT') sigT

(** val piu1932_ck_alpha : q -> nat -> q -> q **)

let piu1932_ck_alpha c0 alpha q0 =
  qdiv c0 (q_pow { qnum = (Z.of_nat (lw1m_height q0)); qden = XH } alpha)

type piu_mu_QleT =
| Piu_mu_QleT_i

type piu_mu_ZleT =
| Piu_mu_ZleT_i

type ('s1, 's2) piu_mu_and2 =
| Piu_mu_and2_i of 's1 * 's2

type ('s1, 's2, 's3) piu_mu_and3 =
| Piu_mu_and3_i of 's1 * 's2 * 's3

(** val piu_mu_mult_le_r_inv : q -> q -> q -> piu_mu_QleT **)

let piu_mu_mult_le_r_inv _ _ _ =
  Piu_mu_QleT_i

(** val piu_zz_c0_criterion : q **)

let piu_zz_c0_criterion =
  { qnum = (Zpos XH); qden = (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI (XO (XO (XO
    XH)))))))))))))))))))))))))) }

(** val piu_zz_mu_kappa : q **)

let piu_zz_mu_kappa =
  { qnum = (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI
    (XI (XO (XI (XO (XO (XO (XI (XO (XO (XO XH))))))))))))))))))))))))));
    qden = XH }

(** val piu_zz_mu_qpow_inject : nat -> q -> q -> qleT' -> qleT' **)

let piu_zz_mu_qpow_inject t x y _ =
  match t with
  | O -> assert false (* absurd case *)
  | S _ -> qle_to_QleT' x y

(** val piu_zz_realcert_of_distpt :
    q -> q -> q -> qltT -> lw1m_dist_pt -> real_lt **)

let piu_zz_realcert_of_distpt q0 d e he = function
| ExistT (x, _) ->
  let s = leibsep_metric_pi_transport q0 e he in
  let ExistT (x0, _) = s in
  ExistT (e, (Pair (he, (ExistT ((Nat.max x x0), (fun k _ ->
  qlt_to_QltT e
    (qminus (projT1 (real_metric real_pi_geom (real_const q0)) k) d)))))))

(** val piu_zz_Hmu_rateslot_of_distpt :
    q -> (q, (qltT, lw1m_dist_pt) and0) sigT -> real_lt **)

let piu_zz_Hmu_rateslot_of_distpt q0 = function
| ExistT (x, a) ->
  let Pair (q1, l) = a in
  piu_zz_realcert_of_distpt q0
    (piu1932_ck_alpha piu_zz_c0_criterion (S (S (S (S (S (S (S (S O))))))))
      q0)
    x q1 l

(** val piu_zz_ec_mu_cond :
    (nat -> z) -> (nat -> z) -> (z -> z -> q) -> (z -> z -> piu_mu_QleT) -> (z
    -> z -> z -> nat -> __ -> piu_mu_QleT) -> (nat -> (piu_mu_ZleT,
    piu_mu_ZleT) piu_mu_and2) -> (z -> nat -> __ -> (nat, (piu_mu_QleT,
    piu_mu_ZleT, piu_mu_QleT) piu_mu_and3) sigT) -> (nat -> qleT') -> (z -> z
    -> __ -> (nat, nat -> __ -> qleT') sigT) -> q -> real_lt **)

let piu_zz_ec_mu_cond _ _ _ _ _ _ _ _ hexit q0 =
  let q1 = Coq_Pos.to_nat (qred q0).qden in
  let p0 = (qred q0).qnum in
  piu_zz_Hmu_rateslot_of_distpt q0
    (let s = hexit p0 (Z.of_nat q1) __ in
     let ExistT (x, _) = s in
     let bQ = inject_Z (Z.of_nat q1) in
     let b8 = qpower bQ (Z.of_nat (S (S (S (S (S (S (S (S O))))))))) in
     let hQ = { qnum = (Z.of_nat (lw1m_height q0)); qden = XH } in
     let h8 = qpower hQ (Z.of_nat (S (S (S (S (S (S (S (S O))))))))) in
     ExistT
     ((qmult { qnum = (Zpos XH); qden = (XO (XO XH)) }
        (qmult piu_zz_c0_criterion (qminus (qinv b8) (qinv h8)))),
     (Pair
     ((qlt_to_QltT { qnum = Z0; qden = XH }
        (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) }
          (qmult piu_zz_c0_criterion (qminus (qinv b8) (qinv h8))))),
     (ExistT (x, (fun k _ ->
     qlt_to_QltT
       (qplus
         (piu1932_ck_alpha piu_zz_c0_criterion (S (S (S (S (S (S (S (S
           O)))))))) q0)
         (qmult { qnum = (Zpos (XO XH)); qden = XH }
           (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) }
             (qmult piu_zz_c0_criterion (qminus (qinv b8) (qinv h8))))))
       (qabs (qminus (lw0m_xL k) q0)))))))))

type piu_zz_n2b_hcoef17_A = nat -> qleT'

(** val piu_zz_s2_w1 : q **)

let piu_zz_s2_w1 =
  inject_Z (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XO (XI (XI
    (XI (XI (XI (XO (XI (XO (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XO (XO
    XH))))))))))))))))))))))))))))))))))

(** val piu_zz_s2_w2 : q **)

let piu_zz_s2_w2 =
  inject_Z (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XO (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO (XO
    (XO (XI (XI (XO (XI (XO (XI (XO (XO (XO
    XH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val piu_zz_s2_w3 : q **)

let piu_zz_s2_w3 =
  inject_Z (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XI (XO (XI (XI (XI (XI (XO (XO (XI (XO (XO (XO (XI (XO (XO
    (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO
    (XO (XO (XI (XI (XO (XI (XO (XI (XO (XO (XO
    XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val piu_zz_s2_regime_splice :
    (nat -> q) -> (nat -> qleT' -> qleT' -> qleT') -> (nat -> qleT' -> qleT'
    -> qleT') -> (nat -> qleT' -> qleT') -> nat -> qleT' -> qleT' **)

let piu_zz_s2_regime_splice _ hPiece1 hPiece2 hPiece3 n hw1 =
  let s = qlt_le_dec (inject_Z (Z.of_nat n)) piu_zz_s2_w2 in
  (match s with
   | Left -> hPiece1 n hw1 (qle_to_QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2)
   | Right ->
     let s0 = qlt_le_dec (inject_Z (Z.of_nat n)) piu_zz_s2_w3 in
     (match s0 with
      | Left ->
        hPiece2 n (qle_to_QleT' piu_zz_s2_w2 (inject_Z (Z.of_nat n)))
          (qle_to_QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w3)
      | Right -> hPiece3 n (qle_to_QleT' piu_zz_s2_w3 (inject_Z (Z.of_nat n)))))

(** val piu_zz_s2_head_maxform :
    (nat -> q) -> (nat -> qleT' -> qleT' -> qleT') -> (nat -> qleT' -> qleT'
    -> qleT') -> (nat -> qleT' -> qleT') -> (nat -> qleT' -> qleT' -> qleT')
    -> nat -> (qleT', qleT') sum **)

let piu_zz_s2_head_maxform s2face hPiece1 hPiece2 hPiece3 hC1branch n =
  let s = qlt_le_dec (inject_Z (Z.of_nat n)) piu_zz_s2_w1 in
  (match s with
   | Left ->
     Inr
       (hC1branch n
         (qle_to_QleT' (inject_Z (Zpos (XI (XO (XO (XI (XO XH)))))))
           (inject_Z (Z.of_nat n)))
         (qle_to_QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2))
   | Right ->
     Inl
       (piu_zz_s2_regime_splice s2face hPiece1 hPiece2 hPiece3 n
         (qle_to_QleT' piu_zz_s2_w1 (inject_Z (Z.of_nat n)))))

type piu_zz_s2_head_combined_face =
  (piu_zz_n2b_hcoef17_A, (nat -> qleT' -> qleT' -> qleT', nat -> qleT' ->
  qleT' -> qleT', nat -> qleT' -> qleT') piu_mu_and3) piu_mu_and2

(** val piu_zz_ec_nescD : nat -> nat **)

let piu_zz_ec_nescD q0 =
  Nat.div (add (mul (S (S O)) (S (Nat.log2 q0))) (S (S (S (S (S O)))))) (S (S
    (S (S (S O)))))

(** val piu_zz_ec_escwin_limb1_Q : nat -> piu_mu_QleT **)

let piu_zz_ec_escwin_limb1_Q q0 =
  piu_mu_mult_le_r_inv
    (qmult (inject_Z (Z.of_nat q0))
      (qpower { qnum = (Zpos (XI XH)); qden = (XO (XO (XI (XO XH)))) }
        (Z.of_nat (piu_zz_ec_nescD q0))))
    { qnum = (Zpos XH); qden = (XO XH) }
    (qpower (inject_Z (Zpos (XO (XO (XI (XO XH))))))
      (Z.of_nat (piu_zz_ec_nescD q0)))

(** val piu_zz_ec_escwin_limb3_Q : nat -> piu_mu_QleT **)

let piu_zz_ec_escwin_limb3_Q _ =
  Piu_mu_QleT_i

type piu_zz_ec_HescD_face =
  (nat, (piu_mu_QleT, piu_mu_ZleT, piu_mu_QleT) piu_mu_and3) sigT

(** val piu_zz_ec_HescD_of_window :
    (nat -> z) -> (nat -> z) -> z -> nat -> piu_mu_ZleT ->
    piu_zz_ec_HescD_face **)

let piu_zz_ec_HescD_of_window _ _ _ q0 h2 =
  ExistT ((piu_zz_ec_nescD q0), (Piu_mu_and3_i ((piu_zz_ec_escwin_limb1_Q q0),
    h2, (piu_zz_ec_escwin_limb3_Q q0))))

(** val piu_zz_hmu_kappa_c0 : qeqT **)

let piu_zz_hmu_kappa_c0 =
  qeq_imp_qeqT
    (qmult { qnum = (Zpos (XO XH)); qden = XH }
      (qmult piu_zz_mu_kappa piu_zz_c0_criterion))
    { qnum = (Zpos XH); qden = XH }

(** val piu_zz_hmu_c0_inv : qeqT **)

let piu_zz_hmu_c0_inv =
  qeq_imp_qeqT
    (qdiv { qnum = (Zpos XH); qden = XH }
      (qmult { qnum = (Zpos (XO XH)); qden = XH } piu_zz_mu_kappa))
    piu_zz_c0_criterion

(** val piu_zz_hmu_qpow_inject_alpha8 : q -> q -> qleT' -> qleT' **)

let piu_zz_hmu_qpow_inject_alpha8 x y h =
  piu_zz_mu_qpow_inject (S (S (S (S (S (S (S (S O)))))))) x y h

(** val piu_zz_hmu_qpow_inject_tau2 : q -> q -> qleT' -> qleT' **)

let piu_zz_hmu_qpow_inject_tau2 x y h =
  piu_zz_mu_qpow_inject (S (S O)) x y h

(** val piu_zz_hmu_distpt_of_realcert :
    q -> q -> real_lt -> (q, (qltT, lw1m_dist_pt) and0) sigT **)

let piu_zz_hmu_distpt_of_realcert q0 d = function
| ExistT (x, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  let heps2 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qmult { qnum = (Zpos XH); qden = (XO XH) } x)
  in
  let s0 =
    leibsep_metric_pi_transport q0
      (qmult { qnum = (Zpos XH); qden = (XO XH) } x) heps2
  in
  let ExistT (x1, _) = s0 in
  ExistT ((qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } x), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } x)),
  (ExistT ((Nat.max x0 x1), (fun k _ ->
  qlt_to_QltT'
    (qplus d
      (qmult { qnum = (Zpos (XO XH)); qden = XH }
        (qmult { qnum = (Zpos XH); qden = (XO (XO XH)) } x)))
    (qabs (qminus (lw0m_xL k) q0))))))))

(** val piu_zz_hmu_distpt_supply :
    (nat -> z) -> (nat -> z) -> (z -> z -> q) -> (z -> z -> piu_mu_QleT) -> (z
    -> z -> z -> nat -> __ -> piu_mu_QleT) -> (nat -> (piu_mu_ZleT,
    piu_mu_ZleT) piu_mu_and2) -> (z -> nat -> __ -> (nat, (piu_mu_QleT,
    piu_mu_ZleT, piu_mu_QleT) piu_mu_and3) sigT) -> (nat -> qleT') -> (z -> z
    -> __ -> (nat, nat -> __ -> qleT') sigT) -> q -> (q, (qltT, lw1m_dist_pt)
    and0) sigT **)

let piu_zz_hmu_distpt_supply a b dv hp htri hcoef hesc hcage hexit q0 =
  piu_zz_hmu_distpt_of_realcert q0
    (piu1932_ck_alpha piu_zz_c0_criterion (S (S (S (S (S (S (S (S O))))))))
      q0)
    (piu_zz_ec_mu_cond a b dv hp htri hcoef hesc hcage hexit q0)

(** val piu_zz_hmu_realcert_of_chain :
    (nat -> z) -> (nat -> z) -> (z -> z -> q) -> (z -> z -> piu_mu_QleT) -> (z
    -> z -> z -> nat -> __ -> piu_mu_QleT) -> (nat -> (piu_mu_ZleT,
    piu_mu_ZleT) piu_mu_and2) -> (z -> nat -> __ -> (nat, (piu_mu_QleT,
    piu_mu_ZleT, piu_mu_QleT) piu_mu_and3) sigT) -> (nat -> qleT') -> (z -> z
    -> __ -> (nat, nat -> __ -> qleT') sigT) -> q -> real_lt **)

let piu_zz_hmu_realcert_of_chain a b dv hp htri hcoef hesc hcage hexit q0 =
  piu_zz_Hmu_rateslot_of_distpt q0
    (piu_zz_hmu_distpt_supply a b dv hp htri hcoef hesc hcage hexit q0)

(** val piu_zz_hmu_n5_hescd_contract :
    (nat -> z) -> (nat -> z) -> z -> nat -> piu_mu_ZleT ->
    piu_zz_ec_HescD_face **)

let piu_zz_hmu_n5_hescd_contract =
  piu_zz_ec_HescD_of_window

(** val piu_zz_hmu_n4_maxform_of_combined :
    (nat -> z) -> (nat -> z) -> (nat -> q) -> piu_zz_s2_head_combined_face ->
    (nat -> qleT' -> qleT' -> qleT') -> nat -> (qleT', qleT') sum **)

let piu_zz_hmu_n4_maxform_of_combined _ _ s2f h x n =
  let Piu_mu_and2_i (_, p) = h in
  let Piu_mu_and3_i (q0, q1, q2) = p in
  piu_zz_s2_head_maxform s2f q0 q1 q2 x n
