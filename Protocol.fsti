(** Protocols as reactive labelled transition systems (RLTS), introduced in the
    paper's "Formal model and definitions" (paper §3.1, Fig. 5). *)

module Protocol

open Bag



/// Protocol transition label: τ (internal) or (o, t) (observable)  (paper §3.1)
///
/// The `id` type parameter carries an arbitrary protocol-specific identifier
/// (e.g. a session id) that can be used to partition transitions without
/// contributing to the observable information `o`.

type label (term: eqtype) (observable: Type) (id: Type) =
  | Internal : lbl_id: id -> label term observable id
  | Observable : o: observable -> t: term -> lbl_id: id -> label term observable id



/// Protocol state as a record with fields `inputs` and `internal`.
/// (formalism: Σ = Bag(Term) × Σ_internal; represented here as named fields)

noeq
type state (term: eqtype) (internal_state: Type) = {
  inputs:bag term;
  internal:internal_state
}



/// Transition constraint: transitions may only remove inputs from the bag.
/// (formalism: (inputs, σ) →ᵅ (inputs', σ') ⟹ inputs' ⊆ inputs)

let valid_transitions'
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (transitions:
          (state term internal_state -> label term obs id -> state term internal_state -> prop))
    : prop =
  forall (s: state term internal_state) (l: label term obs id) (s': state term internal_state).
    transitions s l s' ==> Bag.subset s'.inputs s.inputs



/// Protocol typeclass, parameterized by term/observable/id/internal-state types.
/// (paper §3.1)

class protocol (term: eqtype) (observable: Type) (id: Type) (internal_state: Type) = {
  transition:state term internal_state -> label term observable id -> state term internal_state -> prop;
  init:state term internal_state;
  valid_transitions:
    s: state term internal_state ->
    l: label term observable id ->
    s': state term internal_state ->
    squash (transition s l s' ==> Bag.subset s'.inputs s.inputs)
}
