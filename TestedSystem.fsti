(**
  A tested system is the combination of a protocol and an adversary interacting
  with it. Defined in the paper's "Formal model and definitions", paper §3.1
  (§3.1, "Composing adversaries with protocols",
  Fig. 5b).
*)

module TestedSystem

open Adversary

open Bag

module Protocol = Protocol

open SymbolicTypes



/// Tested system state as a record with fields `know`, `inputs`, and `internal`.
/// (formalism: Σ_{T∥P} = List(Term) × Bag(Term) × Σ_{P_internal}; represented here as named fields)

noeq
type state (term: eqtype) (internal_state: Type) = {
  know:knowledge term;
  inputs:bag term;
  internal:internal_state
}

(**
  Helpers to convert between the tested system state and protocol state.
*)
unfold
let s2p_state
    (#term: eqtype)
    (#internal_state: Type)
    (s: state term internal_state)
    : Protocol.state term internal_state =
  {
    inputs = s.inputs;
    internal = s.internal
  }

unfold
let p2s_state
    (#term: eqtype)
    (#internal_state: Type)
    (s: Protocol.state term internal_state)
    (know: knowledge term)
    : state term internal_state =
  {
    know = know;
    inputs = s.inputs;
    internal = s.internal
  }


/// Labels for the tested system: τ, observable effects o, or tester derivations δ.
/// (paper §3.1, Fig. 5b)
///
/// The `id` type parameter carries a protocol-specific identifier (e.g. session
/// id) that labels Internal and Observable transitions for partitioning purposes.

type label (term: eqtype) (obs: Type) (id: Type) (adv: adversary term) =
  | Internal : lbl_id: id -> label term obs id adv // Internal protocol transition
  | Observable : o: obs -> lbl_id: id -> label term obs id adv // Protocol exhibits observable effect o
  | Input : d: adv.derivation -> label term obs id adv // Tester adds derivation result to protocol inputs



/// Transition relation for the tested system T∥P.
/// (paper §3.1, Fig. 5b — three-case definition)

let transitions'
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (adv: adversary term)
      (p: Protocol.protocol term obs id internal_state)
      (s: state term internal_state)
      (l: label term obs id adv)
      (s': state term internal_state)
    : prop =
  match l with
  | Internal lbl_id ->
    p.transition
      (s2p_state s)
      (Protocol.Internal lbl_id)
      (s2p_state s')
    /\ s'.know == s.know
  | Observable o lbl_id ->
    exists t.
      // Protocol takes an observable step emitting (o, t); t is added to the tester's knowledge.
      p.transition
        (s2p_state s)
        (Protocol.Observable o t lbl_id)
        (s2p_state s')
      /\ s'.know == Seq.snoc s.know t
  | Input d ->
    exists t.
      // Knowledge and internal state don't change when tester adds input to protocol.
      // Tester applies derivation d to current knowledge; if it produces Some t, t is added to P's input bag.
      adv.derive d s.know == Some t
      /\ s'.inputs == Bag.insert t s.inputs
      /\ s'.know == s.know
      /\ s'.internal == s.internal



(**
  Initial tested state is parametric on the initial knowledge and internal
  state. The network is initially empty.
*)

let init'
      (#term: eqtype)
      (#internal_state: Type)
      (know_0: knowledge term)
      (proto_state_0: internal_state)
    : state term internal_state = { know = know_0; inputs = Bag.empty; internal = proto_state_0 }


(** Type of tested system transition relations *)
type transitions_t (term: eqtype) (obs id internal_state: Type) (adv: adversary term) =
  (state term internal_state -> label term obs id adv -> state term internal_state -> prop)



/// Constraint on how a single labeled transition may change the tester's
/// knowledge: internal transitions must preserve it exactly, while all other
/// transitions may only add to it.

let valid_knowledge_change
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (#adv: adversary term)
      (s: state term internal_state)
      (l: label term obs id adv)
      (s': state term internal_state)
    : prop =
  match l with
  | Internal _ -> s'.know == s.know
  | _ -> forall t. knowledge_mem s.know t ==> knowledge_mem s'.know t



/// A valid tested-system transition relation must only add to the tester's
/// knowledge, and internal transitions must not change the knowledge at all.
/// (Mirrors `validObservableTransitionRelation` in the Lean development. The
/// metatheory proven in Lean relies on this invariant; in F* it holds by
/// construction for any system built with `TestedSystem.system` — see
/// `transitions'_valid` below — so the admitted lemmas in
/// `ObservationalBisimulation` discharge it automatically rather than taking it
/// as a hypothesis.)

let valid_observable_transition_relation
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (#adv: adversary term)
      (transitions: transitions_t term obs id internal_state adv)
    : prop =
  forall (s: state term internal_state) (l: label term obs id adv) (s': state term internal_state).
    transitions s l s' ==> valid_knowledge_change s l s'



/// The tested-system transition relation derived from a protocol is always
/// valid: internal steps leave knowledge unchanged, observable steps only
/// append to it, and tester inputs leave it unchanged.

val transitions'_valid
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (adv: adversary term)
      (p: Protocol.protocol term obs id internal_state)
    : Lemma (valid_observable_transition_relation (transitions' adv p))
      [SMTPat (valid_observable_transition_relation (transitions' adv p))]

// Type of a tested system.
//
// The type is parameterized on the adversary and initial knowledge since
// ultimately the system will be used to model the interaction of the specific
// adversary with two protocols. The adversary should have the same capabilities
// and initial knowledge in both cases.
noeq
type system_t
  (#term: eqtype) (#obs: Type) (#id: Type) (#internal_state: Type) (#adv: adversary term)
  (#know0: knowledge term)
  = {
  transitions: transitions_t term obs id internal_state adv;
  init:(s: state term internal_state {s.know == know0})
}

unfold
let system
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (adv: adversary term)
      (p: Protocol.protocol term obs id internal_state)
      (know_0: knowledge term)
    : system_t #term #obs #id #internal_state #adv #know_0 =
  { transitions = transitions' adv p; init = init' know_0 p.init.internal }
