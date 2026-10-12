module Bag



/// Abstract bag (multiset) type.  (paper §3.1: Bag(X))
/// The concrete representation is hidden; clients use only the operations below.

val bag: eqtype -> Type0



/// The empty bag.

val empty (#a: eqtype) : bag a



/// The multiplicity of x in b (0 when x is absent).
val count (#a: eqtype) (b: bag a) (x: a) : nat



/// True iff x has positive multiplicity in b.

val mem (#a: eqtype) (x: a) (b: bag a) : bool



/// b1 ⊆ b2: every element has at least as high a multiplicity in b2 as in b1.

val subset (#a: eqtype) (b1 b2: bag a) : prop



/// Remove one copy of x from b (no-op if x is absent).

val remove (#a: eqtype) (x: a) (b: bag a) : bag a



/// Add one copy of x to b.

val insert (#a: eqtype) (x: a) (b: bag a) : bag a


val mem_count (#a: eqtype) (x: a) (b: bag a)
    : Lemma (mem x b == (count b x > 0))
    [SMTPat (mem x b)]


/// b ⊆ b (reflexivity).  Fires as an SMT pattern whenever the solver sees
/// `subset b b` as a goal.

val subset_refl (#a: eqtype) (b: bag a)
    : Lemma (subset b b) [SMTPat (subset b b)]



/// mem is false for the empty bag.

val mem_empty (#a: eqtype) (x: a)
    : Lemma (~(mem x (empty #a))) [SMTPat (mem x (empty #a))]



/// Membership after insert: x is in (insert y b) iff x = y or x was already in b.

val mem_insert (#a: eqtype) (x y: a) (b: bag a)
    : Lemma (mem x (insert y b) == (x = y || mem x b))
      [SMTPat (mem x (insert y b))]

/// Multiplicity after insert: inserting x increments x's count by 1 and
/// leaves all other elements unchanged.

val count_insert (#a: eqtype) (x y: a) (b: bag a)
    : Lemma
        (count (insert x b) y ==
          (if x = y then count b x + 1 else count b y))
      [SMTPat (count (insert x b) y)]

val mem_remove (#a: eqtype) (x y: a) (b: bag a)
    : Lemma (mem x (remove y b) == ((x <> y && mem x b) || ((x = y) && count b y > 1)))
      [SMTPat (mem x (remove y b))]

/// Multiplicity after remove: removing one copy of x decrements x's count
/// (or leaves it at 0); all other elements are unaffected.

val count_remove (#a: eqtype) (x y: a) (b: bag a)
    : Lemma
        (count (remove x b) y ==
          (if x = y && count b x > 0 then count b x - 1 else count b y))
      [SMTPat (count (remove x b) y)]

val remove_preserves_subset (#a: eqtype) (x: a) (b1 b2: bag a)
    : Lemma
        (requires subset b1 b2)
        (ensures subset (remove x b1) b2)
      [SMTPat (subset (remove x b1) b2)]

/// Commutativity: removing two elements in either order gives the same bag.

val remove_remove_commute (#a: eqtype) (x y: a) (b: bag a)
    : Lemma (remove x (remove y b) == remove y (remove x b))
      [SMTPat (remove x (remove y b))]

/// Commutativity of remove and insert (when the removed element exists or
/// differs from the inserted one).

val remove_insert_commute (#a: eqtype) (x y: a) (b: bag a)
    : Lemma (requires x <> y \/ mem x b)
            (ensures remove x (insert y b) == insert y (remove x b))

/// Membership is monotone along `subset`: if `b1 ⊆ b2` and `x ∈ b1` then
/// `x ∈ b2`.  (No SMT pattern: invoke explicitly to stay inert in callers.)

val subset_mem (#a: eqtype) (x: a) (b1 b2: bag a)
    : Lemma (requires subset b1 b2 /\ mem x b1) (ensures mem x b2)
