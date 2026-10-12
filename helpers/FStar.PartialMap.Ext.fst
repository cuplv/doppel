(** Extensions to the `PartialMap` module in FStar's ulib *)

module FStar.PartialMap.Ext



(**
  Map a function over the values of a `PartialMap`.
*)

// TODO: Need to extend F*'s PartialMap module directly to define this
// since the implementation (as a total function to options) is hidden behind
// its interface.

let map (#k: eqtype) (f: ('a -> 'b)) (m: PartialMap.t k 'a) : PartialMap.t k 'b = admit ()

let sel_map (#k: eqtype) (f: ('a -> 'b)) (m: PartialMap.t k 'a) (key: k)
    : Lemma (ensures PartialMap.sel (map f m) key == Option.mapTot f (PartialMap.sel m key))
      [SMTPat (PartialMap.sel (map f m) key)] = admit ()

let upd_commute (#k: eqtype) (#v: Type) (m: PartialMap.t k v)
    (k1: k) (v1: v) (k2: k) (v2: v)
    : Lemma (requires k1 <> k2)
            (ensures PartialMap.upd (PartialMap.upd m k1 v1) k2 v2 ==
                     PartialMap.upd (PartialMap.upd m k2 v2) k1 v1) =
  PartialMap.eq_intro (PartialMap.upd (PartialMap.upd m k1 v1) k2 v2)
                      (PartialMap.upd (PartialMap.upd m k2 v2) k1 v1);
  PartialMap.eq_elim  (PartialMap.upd (PartialMap.upd m k1 v1) k2 v2)
                      (PartialMap.upd (PartialMap.upd m k2 v2) k1 v1)
