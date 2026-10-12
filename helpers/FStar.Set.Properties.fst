(** Additional properties of FStar's ulib Sets *)

module FStar.Set.Properties

open FStar.Set

let remove_add (#a: eqtype) (y: a) (s: set a)
    : Lemma (ensures equal (remove y (add y s)) (remove y s)) = ()

let union_empty (#a: eqtype) (s: set a)
    : Lemma (ensures equal (union s empty) s) = ()

let union_empty_left (#a: eqtype) (s: set a)
    : Lemma (ensures equal (union empty s) s) = ()

let set_subset_transitive
      (#a: eqtype)
      (s1 s2 s3: set a)
    : Lemma
      (requires subset s1 s2 /\ subset s2 s3)
      (ensures subset s1 s3) =
  subset_mem s1 s2;
  subset_mem s2 s3;
  assert (forall x. mem x s1 ==> mem x s3);
  mem_subset s1 s3

let set_subset_union_left
      (#a: eqtype)
      (s1 s2: set a)
    : Lemma
      (ensures subset s1 (union s1 s2)) =
  assert (forall x. mem x s1 ==> mem x (union s1 s2));
  mem_subset s1 (union s1 s2)

let set_subset_union_right
      (#a: eqtype)
      (s1 s2: set a)
    : Lemma
      (ensures subset s2 (union s1 s2)) =
  assert (forall x. mem x s2 ==> mem x (union s1 s2));
  mem_subset s2 (union s1 s2)

let set_subset_union
      (#a: eqtype)
      (s1 s2 s3: set a)
    : Lemma
      (requires subset s1 s3 /\ subset s2 s3)
      (ensures subset (union s1 s2) s3) =
  subset_mem s1 s3;
  subset_mem s2 s3;
  assert (forall x. mem x (union s1 s2) ==> mem x s3);
  mem_subset (union s1 s2) s3

let rec as_set_append_left_subset
      (#a: eqtype)
      (as1 as2: list a)
    : Lemma
      (ensures subset (as_set as1) (as_set (List.Tot.append as1 as2))) =
  match as1 with
  | [] ->
    assert (forall x. mem x (as_set as1) ==> mem x (as_set (List.Tot.append as1 as2)));
    mem_subset (as_set as1) (as_set (List.Tot.append as1 as2))
  | hd::tl ->
    as_set_append_left_subset tl as2;
    assert (forall x. mem x (as_set as1) ==> mem x (as_set (List.Tot.append as1 as2)));
    mem_subset (as_set as1) (as_set (List.Tot.append as1 as2))

let rec as_set_append_right_subset
      (#a: eqtype)
      (as1 as2: list a)
    : Lemma
      (ensures subset (as_set as2) (as_set (List.Tot.append as1 as2))) =
  match as1 with
  | [] ->
    assert (List.Tot.append as1 as2 == as2);
    assert (forall x. mem x (as_set as2) ==> mem x (as_set (List.Tot.append as1 as2)));
    mem_subset (as_set as2) (as_set (List.Tot.append as1 as2))
  | hd::tl ->
    as_set_append_right_subset tl as2;
    assert (forall x. mem x (as_set as2) ==> mem x (as_set (List.Tot.append as1 as2)));
    mem_subset (as_set as2) (as_set (List.Tot.append as1 as2))

let rec as_set_append_subset
      (#a: eqtype)
      (as1 as2: list a)
      (target: set a)
    : Lemma
      (requires subset (as_set as1) target /\ subset (as_set as2) target)
      (ensures subset (as_set (List.Tot.append as1 as2)) target) =
  match as1 with
  | [] ->
    assert (List.Tot.append as1 as2 == as2);
    assert (forall x. mem x (as_set (List.Tot.append as1 as2)) ==> mem x target);
    mem_subset (as_set (List.Tot.append as1 as2)) target
  | hd::tl ->
    as_set_append_subset tl as2 target;
    subset_mem (as_set as1) target;
    assert (forall x. mem x (as_set (List.Tot.append as1 as2)) ==> mem x target);
    mem_subset (as_set (List.Tot.append as1 as2)) target

let add_commute (#a: eqtype) (x y: a) (s: set a)
    : Lemma (ensures add x (add y s) == add y (add x s)) =
  lemma_equal_intro (add x (add y s)) (add y (add x s));
  lemma_equal_elim (add x (add y s)) (add y (add x s))

let add_idem (#a: eqtype) (x: a) (s: set a)
    : Lemma (ensures add x (add x s) == add x s) =
  lemma_equal_intro (add x (add x s)) (add x s);
  lemma_equal_elim (add x (add x s)) (add x s)

let add_remove_commute (#a: eqtype) (x y: a) (s: set a)
    : Lemma (requires x <> y)
            (ensures add x (remove y s) == remove y (add x s)) =
  lemma_equal_intro (add x (remove y s)) (remove y (add x s));
  lemma_equal_elim (add x (remove y s)) (remove y (add x s))

let remove_add_commute (#a: eqtype) (x y: a) (s: set a)
    : Lemma (requires x <> y)
            (ensures remove x (add y s) == add y (remove x s)) =
  lemma_equal_intro (remove x (add y s)) (add y (remove x s));
  lemma_equal_elim (remove x (add y s)) (add y (remove x s))
