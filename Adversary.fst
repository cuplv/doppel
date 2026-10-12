(**
  Defines the adversary interface. An adversary is defined by the derivations it
  can use to derive new terms from its knowledge.
  (paper §3.1, Fig. 5; the `Tester`
  class in the Lean development.)
*)

module Adversary

open SymbolicTypes

module Seq = FStar.Seq

class adversary (term: eqtype) = {
  derivation:eqtype;
  derive:derivation -> knowledge term -> option term;
  indistinguishable:term -> term -> prop;
  // Indistinguishability must be an equivalence relation, mirroring the
  // `Setoid` requirement on `Tester.indistinguishable` in the Lean
  // development. The metatheory proven in Lean relies on reflexivity (e.g. to
  // show equal knowledges are statically equivalent) and symmetry (for the
  // reverse direction of bisimulation arguments).
  indistinguishable_equiv:unit
    -> squash ((forall t. indistinguishable t t) /\
        (forall t1 t2. indistinguishable t1 t2 ==> indistinguishable t2 t1) /\
        (forall t1 t2 t3. indistinguishable t1 t2 /\ indistinguishable t2 t3 ==> indistinguishable t1 t3));
  derivable:know: knowledge term -> t: term -> (r: prop{r == (exists d. derive d know = Some t)});
  append_preserves_derive:d: derivation -> know1: knowledge term -> know2: knowledge term
    -> squash (forall t. derive d know1 = Some t ==> derive d (Seq.append know1 know2) = Some t)
}
