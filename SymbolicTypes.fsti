module SymbolicTypes

open FStar.Seq

open SencTerms



/// Type representing a channel identifier

val channel_id:eqtype



/// Type of the adversary's knowledge.
/// Maps indices to terms (represented as partial functions).

let knowledge_index:eqtype = nat

let knowledge (term: eqtype) = seq term



/// Knowledge membership: a term is in knowledge if it appears at some index.

let knowledge_mem (#term: eqtype) (know: knowledge term) (t: term) : prop = mem t know
