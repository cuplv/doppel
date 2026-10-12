(** Extensions to the `PartialMap` module in FStar's ulib *)

module FStar.PartialMap.Ext



// Re-export the original PartialMap module so just this module can be imported.

include FStar.PartialMap



(**
  Map a function over the values of a `PartialMap`.
*)

val map (#k: eqtype) (f: ('a -> 'b)) (m: PartialMap.t k 'a) : PartialMap.t k 'b

val sel_map (#k: eqtype) (f: ('a -> 'b)) (m: PartialMap.t k 'a) (key: k)
    : Lemma (ensures PartialMap.sel (map f m) key == Option.mapTot f (PartialMap.sel m key))
      [SMTPat (PartialMap.sel (map f m) key)]

(**
  Updates at distinct keys commute.
*)

val upd_commute (#k: eqtype) (#v: Type) (m: PartialMap.t k v)
    (k1: k) (v1: v) (k2: k) (v2: v)
    : Lemma (requires k1 <> k2)
            (ensures PartialMap.upd (PartialMap.upd m k1 v1) k2 v2 ==
                     PartialMap.upd (PartialMap.upd m k2 v2) k1 v1)
