(** Generic partitioning helpers. *)

module Partition

open FStar.GhostSet



// Helper proposition that the relation is an equivalence relation.

let is_equiv (#a: Type) (r: (a -> a -> prop)) : prop =
  (forall x. r x x) /\ (forall x y. r x y ==> r y x) /\ (forall x y z. r x y /\ r y z ==> r x z)

(**
  Partitioning of all the elements of the type `a`.

  The partitioning is implicitly defined by an equivalence relation on elements
  of the type, such that any two elements related by the relation are in the
  same partition.
*)
class partition (a: Type) = {
  in_same_partition:(a -> a -> prop);
  in_same_partition_equiv: unit -> squash (is_equiv in_same_partition)
}
