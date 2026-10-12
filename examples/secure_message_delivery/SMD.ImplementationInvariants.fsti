module SMD.ImplementationInvariants

open AdversarySenc
open SencTerms
open SymbolicTypes
open TestedSystem

open SMD.Implementation
open SMD.Adversary
open SMD.TestedProtocols

module Set = FStar.Set



/// Invariants over the tested-system implementation state.

let impl_invariant_secret_key_not_derivable (state: impl_system_state) : prop =
  forall (d: adv.derivation). not (adv.derive d state.know = Some (Key state.internal.key))



(**
  Invariant: The adversary cannot derive any term containing the valid encrypted
  response for a session with the correct secret key unless the sender already
  sent the encrypted message out.

  Note: this invariant is defined in terms of being able to derive a term
  _containing_ a valid encrypted response, rather than just being able to derive
  a valid encrypted response, to provide a stronger inductive invariant when
  reasoning about being able to derive the response. This strengthened invariant
  is needed when modeling attacker derivations as an unbounded function rather
  than a single transition.
*)

let impl_invariant_cannot_derive_response_before_send (state: impl_system_state) : prop =
  forall (d: adv.derivation) (session: session_id) (encrypted_message: term) (derived_term: term).
    is_receive_trigger_for_session session state.internal.key encrypted_message /\
    (adv.derive d state.know = Some derived_term) /\ in_term derived_term encrypted_message ==>
    Set.mem session state.internal.sent_sessions



(**
  Invariant: Any message that will be delivered by the receiver has to already
  be known by the adversary.

  This invariant is needed to ensure that no new information is learned from the
  receiver's message delivery, and therefore static equivalence is preserved
  after this transition.

  Note: this invariant is defined in terms of being able to derive a term
  _containing_ a valid encrypted response, rather than just being able to derive
  a valid encrypted response, to provide a stronger inductive invariant when
  reasoning about being able to derive the response. This strengthened invariant
  is needed when modeling attacker derivations as an unbounded function rather
  than a single transition.
*)

let impl_invariant_to_be_delivered_messages_in_knowledge (state: impl_system_state) : prop =
  forall (session: session_id) (message: term) (derived_term: term).
    let session_message_pair = Pair (SessionId session) message in
    let valid_response = Senc session_message_pair state.internal.key in
    in_term derived_term valid_response /\ derivable state.know derived_term ==>
    derivable state.know session_message_pair



(**
  If the adversary can derive a valid response, it only does so through wrapping
  and unwrapping a valid response emitted by the protocol.

  Intuitively, this invariant holds since the adversary cannot forge valid
  responses since the key it would need is not derivable (by
  `impl_invariant_secret_key_not_derivable`).

  This invariant uses `in_term` to support induction over derivation structure.
*)
let impl_invariant_derived_valid_response_equivalent_to_observed_response (state: impl_system_state)
    : prop =
  forall (session: session_id) (message: term) (d: adv.derivation) (derived_term: term).
    let valid_response = Senc (Pair (SessionId session) message) state.internal.key in
    adv.derive d state.know = Some derived_term /\ in_term derived_term valid_response ==>
    // Note: there may be multiple observations containing the valid response
    // since the adversary may use an observed valid response to induce future
    // protocol transitions. However, any valid response must have originally
    // come from the protocol. This invariant therefore existentially quantifies
    // over the index of the original observation.
    (exists (idx: knowledge_index).
      adv.derive (DeriveObserved idx) state.know = Some valid_response)



(**
  Invariant: The `messages` map tracks exactly the sessions that have been
  sent: a session has an entry in `messages` if and only if it is in
  `sent_sessions`.

  This invariant is needed to transfer `PartialMap.contains ideal.messages s`
  to `PartialMap.contains impl.messages s` via the `sent_sessions` /
  `sim_sent_sessions` membership equivalence in the bisimulation relation.
*)

let impl_invariant_sent_sessions_have_messages (state: impl_system_state) : prop =
  forall (session: session_id).
    Set.mem session state.internal.sent_sessions ==
    PartialMap.contains state.internal.messages session



(**
  Invariant: If the adversary can derive a term containing a valid encrypted
  response `Senc(Pair(SessionId session, message), key)`, then
  `messages[session]` stores exactly that `message`.

  This holds because (a) the adversary cannot forge valid encryptions without
  the key, (b) the only source of such Senc terms in knowledge is the send
  transition which also stores the message, and (c) each session is sent at
  most once.
*)

let impl_invariant_messages_consistent_with_knowledge (state: impl_system_state) : prop =
  forall (session: session_id) (message: term) (d: adv.derivation) (derived_term: term).
    adv.derive d state.know = Some derived_term /\
    in_term derived_term (Senc (Pair (SessionId session) message) state.internal.key)
    ==> PartialMap.sel state.internal.messages session == Some message

/// Tested-system invariant for the new bag-input model: every pending protocol
/// input is derivable from current adversary knowledge.

let impl_invariant_inputs_are_derivable
  (state: impl_system_state)
    : prop =
  forall (t: term). Bag.mem t state.inputs ==> derivable state.know t


/// Combined implementation invariant.

let implementation_invariants (state: impl_system_state) : prop =
  impl_invariant_secret_key_not_derivable state /\
  impl_invariant_cannot_derive_response_before_send state /\
  impl_invariant_to_be_delivered_messages_in_knowledge state /\
  impl_invariant_derived_valid_response_equivalent_to_observed_response state /\
  impl_invariant_sent_sessions_have_messages state /\
  impl_invariant_messages_consistent_with_knowledge state /\
  impl_invariant_inputs_are_derivable state

// Instantiated version of
// `impl_invariant_derived_valid_response_equivalent_to_observed_response` that
// is easier to apply in proofs.
val impl_valid_response_is_observed
      (state: impl_system_state)
      (session: session_id)
      (message: term)
      (d: adv.derivation)
      (derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        adv.derive d state.know = Some derived_term /\
        in_term derived_term (Senc (Pair (SessionId session) message) state.internal.key))
      (ensures
        exists (idx: knowledge_index).
          adv.derive (DeriveObserved idx) state.know =
          Some (Senc (Pair (SessionId session) message) state.internal.key))



(**
  The implementation invariants are preserved by each possible transition from
  states satisfying the invariants.
*)

val implementation_invariants_preserved_after_send'
      (session: session_id)
      (message: term)
      (state new_state: impl_system_state)
    : Lemma
      (requires (
        let sent_term = Senc (Pair (SessionId session) message) state.internal.key in
        implementation_invariants state /\
        impl_invariant_inputs_are_derivable state /\
        smd_impl_protocol_send_transition (s2p_state state)
          session
          sent_term
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know sent_term))
      (ensures implementation_invariants new_state)

val implementation_invariants_preserved_after_receive'
      (session: session_id)
      (message: term)
      (state new_state: impl_system_state)
    : Lemma
      (requires
        implementation_invariants state /\
        impl_invariant_inputs_are_derivable state /\
        smd_impl_protocol_receive_transition (s2p_state state)
          session
          (Pair (SessionId session) message)
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know (Pair (SessionId session) message))
      (ensures implementation_invariants new_state)
