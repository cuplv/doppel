module FStar.Bijection.Ext

open FStar.Bijection

val bijection_injective (#a #b : Type) (f : cbij a b) (x1 x2 : a)
  : Lemma
    (requires f.cright x1 == f.cright x2)
    (ensures x1 == x2)

val bijection_right_injective (#a #b : Type) (f : cbij a b) (x1 x2 : a)
  : Lemma
    (requires ~(x1 == x2))
    (ensures ~(f.cright x1 == f.cright x2))

val bijection_surjective (#a #b : Type) (f : cbij a b) (y : b)
  : Lemma
    (ensures exists x. f.cright x == y)
