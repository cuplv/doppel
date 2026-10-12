(** Additional properties of FStar's ulib Sets *)

module FStar.Set.Properties

open FStar.Set

val remove_add (#a: eqtype) (y: a) (s: set a)
    : Lemma (ensures equal (remove y (add y s)) (remove y s)) [SMTPat (remove y (add y s))]

val union_empty (#a: eqtype) (s: set a)
    : Lemma (ensures equal (union s empty) s) [SMTPat (union s empty)]

val union_empty_left (#a: eqtype) (s: set a)
    : Lemma (ensures equal (union empty s) s) [SMTPat (union empty s)]

val set_subset_transitive
      (#a: eqtype)
      (s1 s2 s3: set a)
    : Lemma
      (requires subset s1 s2 /\ subset s2 s3)
      (ensures subset s1 s3)

val set_subset_union_left
      (#a: eqtype)
      (s1 s2: set a)
    : Lemma
      (ensures subset s1 (union s1 s2))

val set_subset_union_right
      (#a: eqtype)
      (s1 s2: set a)
    : Lemma
      (ensures subset s2 (union s1 s2))

val set_subset_union
      (#a: eqtype)
      (s1 s2 s3: set a)
    : Lemma
      (requires subset s1 s3 /\ subset s2 s3)
      (ensures subset (union s1 s2) s3)

val as_set_append_left_subset
      (#a: eqtype)
      (as1 as2: list a)
    : Lemma
      (ensures subset (as_set as1) (as_set (List.Tot.append as1 as2)))

val as_set_append_right_subset
      (#a: eqtype)
      (as1 as2: list a)
    : Lemma
      (ensures subset (as_set as2) (as_set (List.Tot.append as1 as2)))

val as_set_append_subset
      (#a: eqtype)
      (as1 as2: list a)
      (target: set a)
    : Lemma
      (requires subset (as_set as1) target /\ subset (as_set as2) target)
      (ensures subset (as_set (List.Tot.append as1 as2)) target)

/// Two successive `add`s commute.
val add_commute (#a: eqtype) (x y: a) (s: set a)
    : Lemma (ensures add x (add y s) == add y (add x s))

/// `add` is idempotent.
val add_idem (#a: eqtype) (x: a) (s: set a)
    : Lemma (ensures add x (add x s) == add x s)

/// `add` and `remove` of distinct elements commute.
val add_remove_commute (#a: eqtype) (x y: a) (s: set a)
    : Lemma (requires x <> y)
            (ensures add x (remove y s) == remove y (add x s))

/// `remove` and `add` of distinct elements commute.
val remove_add_commute (#a: eqtype) (x y: a) (s: set a)
    : Lemma (requires x <> y)
            (ensures remove x (add y s) == add y (remove x s))
