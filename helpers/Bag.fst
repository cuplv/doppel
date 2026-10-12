module Bag

module PM = FStar.PartialMap



/// Bags are represented as partial maps from elements to their multiplicity.
/// Invariant: a key is present (Some n) only when n > 0;
///            absence from the map (None) means multiplicity 0.

let bag (a: eqtype) = PM.t a nat

let empty (#a: eqtype) : bag a = PM.empty a nat

let count (#a: eqtype) (b: bag a) (x: a) : nat =
  match PM.sel b x with
  | Some n -> n
  | None -> 0

let mem (#a: eqtype) (x: a) (b: bag a) : bool = count b x > 0

let subset (#a: eqtype) (b1 b2: bag a) : prop = forall (x: a). count b1 x <= count b2 x

let remove (#a: eqtype) (x: a) (b: bag a) : bag a =
  let n = count b x in
  if n = 0 then b else if n = 1 then PM.remove b x else PM.upd b x (n - 1)

let insert (#a: eqtype) (x: a) (b: bag a) : bag a = PM.upd b x (count b x + 1)

let mem_count #a x b = ()

let subset_refl #a b = ()

let mem_empty #a x = ()

let mem_insert #a x y b = ()

let count_insert #a x y b = ()

let mem_remove #a x y b = ()

let count_remove #a x y b = ()

let remove_preserves_subset #a x b1 b2 = ()

#push-options "--z3rlimit 40"
let remove_remove_commute #a x y b =
  let lhs = remove x (remove y b) in
  let rhs = remove y (remove x b) in
  let aux (z: a) : Lemma (PM.sel lhs z == PM.sel rhs z) = () in
  FStar.Classical.forall_intro aux;
  PM.eq_intro lhs rhs;
  PM.eq_elim lhs rhs

let remove_insert_commute #a x y b =
  let lhs = remove x (insert y b) in
  let rhs = insert y (remove x b) in
  let aux (z: a) : Lemma (PM.sel lhs z == PM.sel rhs z) = () in
  FStar.Classical.forall_intro aux;
  PM.eq_intro lhs rhs;
  PM.eq_elim lhs rhs
#pop-options

let subset_mem #a x b1 b2 = ()
