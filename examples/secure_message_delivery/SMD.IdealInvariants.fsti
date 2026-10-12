module SMD.IdealInvariants

open AdversarySenc
open SencTerms
open SymbolicTypes
open TestedSystem

open SMD.Adversary
open SMD.Ideal
open SMD.TestedProtocols

module PartialMap = FStar.PartialMap

module Set = FStar.Set



/// Invariant: The secret key is not derivable from the attacker's knowledge.

let ideal_invariant_secret_key_not_derivable (state: ideal_system_state) : prop =
  forall (d: adv.derivation). not (adv.derive d state.know = Some (Key state.internal.sim_key))



/// Invariant: Any committed messages must be derivable from the attacker's
/// knowledge, since the pair of the session and message must be present in
/// the attacker's knowledge.

let ideal_invariant_committed_messages_derivable_from_knowledge (state: ideal_system_state) : prop =
  forall (session: session_id) (message: term).
    PartialMap.sel state.internal.messages session = Some message ==>
    adv.derivable state.know (Pair (SessionId session) message)



/// Invariant: The private channels are empty after observable transitions.

let ideal_invariant_private_channels_empty (state: ideal_system_state) : prop =
  forall (term: term).
    not (Set.mem term state.internal.ideal_to_sim_channel) /\
    not (Set.mem term state.internal.sim_to_ideal_channel)



(**
  Invariant: The adversary cannot derive a valid response for a session with the
  correct secret key unless the simulator already sent the encrypted message
  out.

  Note: this invariant is defined in terms of being able to derive a term
  _containing_ a valid encrypted response, rather than just being able to derive
  a valid encrypted response, to provide a stronger inductive invariant when
  reasoning about being able to derive the response. This strengthened invariant
  is needed when modeling attacker derivations as an unbounded function rather
  than a single transition.
*)

let ideal_invariant_cannot_derive_valid_response_before_send (state: ideal_system_state) : prop =
  forall (d: adv.derivation) (session: session_id) (derived_term: term).
    let valid_encrypted_response = Senc (SessionId session) state.internal.sim_key in
    in_term derived_term valid_encrypted_response /\
    (adv.derive d state.know = Some derived_term) ==>
    Set.mem session state.internal.sim_sent_sessions



/// Invariant: The simulator cannot have sent a decoy out unless the ideal
/// functionality has committed to a message.

let ideal_invariant_sim_sent_only_after_ideal_commit (state: ideal_system_state) : prop =
  forall (session: session_id).
    Set.mem session state.internal.sim_sent_sessions ==
    PartialMap.contains state.internal.messages session


/// Tested-system invariant for the new bag-input model: every pending protocol
/// input is derivable from current adversary knowledge.

let ideal_invariant_inputs_are_derivable (state: ideal_system_state) : prop =
  forall (t: term). Bag.mem t state.inputs ==> derivable state.know t


/// Combined ideal invariants.

let ideal_invariants (state: ideal_system_state) : prop =
  ideal_invariant_secret_key_not_derivable state /\
  ideal_invariant_committed_messages_derivable_from_knowledge state /\
  ideal_invariant_private_channels_empty state /\
  ideal_invariant_cannot_derive_valid_response_before_send state /\
  ideal_invariant_sim_sent_only_after_ideal_commit state /\
  ideal_invariant_inputs_are_derivable state


val ideal_invariants_preserved_after_send'
      (session: session_id)
      (state new_state: ideal_system_state)
    : Lemma
      (requires (
        let sent_term = Senc (SessionId session) state.internal.sim_key in
        ideal_invariants state /\
        ideal_invariant_inputs_are_derivable state /\
        smd_ideal_protocol_send_transition (s2p_state state)
          session
          sent_term
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know sent_term)
      )
      (ensures ideal_invariants new_state)

val ideal_invariants_preserved_after_receive'
      (session: session_id)
      (message: term)
      (state new_state: ideal_system_state)
    : Lemma
      (requires
        ideal_invariants state /\
        ideal_invariant_inputs_are_derivable state /\
        smd_ideal_protocol_receive_transition (s2p_state state)
          session
          (Pair (SessionId session) message)
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know (Pair (SessionId session) message))
      (ensures ideal_invariants new_state)
