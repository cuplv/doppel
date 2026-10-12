module MA.ObservationalBisimulation.Relation

open SymbolicTypes

open Bag

open AencTerms

open MA.Types

open MA.NSL

open MA.Ideal

open MA.Adversary

open TestedSystem

open MA.TestedProtocols

open MA.IdealInvariants

module PartialMap = FStar.PartialMap

module Set = FStar.Set

// Since mutual authentication doesn't provide any secrecy guarantees, the
// simulator can be chosen to produce the same outputs as the implementation.
// The knowledge then will always be the same.
let ma_same_knowledge
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  s_p.know == s_q.know

// Since there just needs to exist some simulator that, composed with the ideal
// functionality, matches the implementation behavior, then the simulator can
// just be chosen to use the same keys and nonces as the implementation.
let ma_same_key_directory
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  s_p.internal.key_directory == key_directory /\
  s_q.internal.key_directory == key_directory


// Since mutual authentication doesn't provide any secrecy guarantees, the
// simulator can be chosen to produce the same outputs as the implementation.
// The inputs then will also be the same since any particular input transition
// using a particular derivation is deterministic with respect to the current
// knowledge.
let ma_same_inputs
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  s_p.inputs == s_q.inputs

let ma_same_used_nonces
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  s_p.internal.used_nonces == s_q.internal.used_nonces


let ma_impl_stored_nonces_are_used
      (s_p: impl_system_state)
    : prop =
  forall (participant: participant_id) (session: session_id) (n: nonce).
    match ma_get_participant_session_state (s2p_state s_p) participant session with
    | Some pss ->
      nonce_in_participant_session_state pss n ==> Set.mem n s_p.internal.used_nonces
    | None -> True


let ma_impl_used_nonces_invariant
      (s_p: impl_system_state)
    : prop =
  ma_impl_stored_nonces_are_used s_p /\
  ma_inputs_nonces_are_used s_p.internal.used_nonces s_p.inputs /\
  ma_knowledge_nonces_are_used s_p.internal.used_nonces s_p.know


let ma_initiator_session_correspondence
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id) (initiator: participant_id).
    let initiator_entry =
      ma_initiator_session_state (s2p_state s_p) initiator session
    in
    let sim_entry =
      ma_sim_initiator_session_state (s2p_state s_q) initiator session
    in
    (Some? initiator_entry <==> Some? sim_entry) /\
    (Some? initiator_entry ==> (
      let initiator_state = Some?.v initiator_entry in
      let sim_state = Some?.v sim_entry in
      initiator_state.initiator == sim_state.initiator /\
      initiator_state.responder == sim_state.responder /\
      initiator_state.initiator_nonce == sim_state.initiator_nonce /\
      initiator_state.ack_sent == sim_state.ack_sent))

let ma_responder_session_correspondence
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id) (responder: participant_id).
    let responder_entry =
      ma_responder_session_state (s2p_state s_p) responder session
    in
    let sim_entry =
      ma_sim_responder_session_state (s2p_state s_q) responder session
    in
    (Some? responder_entry <==> Some? sim_entry) /\
    (Some? responder_entry ==> (
      let responder_state = Some?.v responder_entry in
      let sim_state = Some?.v sim_entry in
      responder_state.responder == sim_state.responder /\
      responder_state.initiator == sim_state.initiator /\
      responder_state.responder_nonce == sim_state.responder_nonce /\
      responder_state.output_sent == sim_state.output_forwarded))

(**
  Since the ideal functionality only accepts at most one
  authentication request per participant per session, and since the simulator is
  leaked every accepted authentication request, the requests accepted by the
  ideal functionality must exactly match the simulator-side session entries.

  NOTE: unlike the dual `ma_sim_session_matches_ideal_request` (session ==>
  request), this clause (request ==> session) is deliberately NOT part of
  `ma_ideal_system_inv`.  A standalone `ma_ideal_initiate` transition records a
  request before the matching simulator session is created, so the `None ->
  False` case is momentarily violated and the clause is not an inductive
  invariant of the ideal system on its own.  In the bisimulation, the paired
  ideal steps (initiate + send) keep request and session creation atomic, so it
  remains a valid conjunct of `ma_bisim_relation`.
*)
let ma_ideal_request_matches_sim_session
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
         (party peer: participant_id)
         (r: role).
    Set.mem { party = party; peer = peer; role = r }
      (ma_session_requests (s2p_state s_q) session) ==>
    (match ma_get_sim_participant_session_state (s2p_state s_q) party session with
    | Some (SimInitiatorSession initiator_state) ->
      r == Initiator /\
      initiator_state.initiator == party /\
      initiator_state.responder == peer
    | Some (SimResponderSession responder_state) ->
      r == Responder /\
      responder_state.responder == party /\
      responder_state.initiator == peer
    | None -> False)

(**
  For implementation initiator sessions, the ideal-side pending output token is
  the simulator-visible counterpart of the implementation-only `output_sent`
  bit.  Before the acknowledgment is sent, implementation output cannot already
  have been sent; once the acknowledgment has been sent, the output token is
  present exactly while the implementation output is still pending.
*)
let ma_initiator_output_token_matches_impl_pending_output
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id) (initiator: participant_id).
    match ma_initiator_session_state (s2p_state s_p) initiator session with
    | Some initiator_state ->
      (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
      (initiator_state.ack_sent ==>
        (Set.mem (ma_output_term session initiator) s_q.internal.sim_to_ideal_channel <==>
         not initiator_state.output_sent))
    | None -> True

(**
  Responder analog of `ma_initiator_output_token_matches_impl_pending_output`.

  The implementation realizes a responder authentication output as a single
  `ma_nsl_responder_output` step, whereas the ideal+simulator realizes it as a
  pair `ma_sim_receive_message3` (places `Output(session, responder)` on the
  sim-to-ideal channel and sets `output_forwarded`) followed by
  `ma_ideal_deliver(Responder)` (removes the token).  The bisimulation keeps that
  pair atomic, so at any *related* state no responder output token is in flight:
  if `Output(session, responder)` is on the sim-to-ideal channel then the
  implementation responder session has not yet emitted its output
  (`not output_sent`).

  Combined with `ma_output_token_matches_sim_phase` (token in flight ==> the
  simulator responder session has `output_forwarded`) and
  `ma_responder_session_correspondence` (`output_sent == output_forwarded`), this
  conjunct makes a token-in-flight configuration with `output_sent` contradictory,
  which rules out a standalone length-1 `ma_ideal_deliver(Responder)` from a
  related state.
*)
let ma_responder_output_token_matches_impl_pending_output
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id) (responder: participant_id).
    match ma_responder_session_state (s2p_state s_p) responder session with
    | Some responder_state ->
      Set.mem (ma_output_term session responder) s_q.internal.sim_to_ideal_channel ==>
      not responder_state.output_sent
    | None -> True


let ma_inputs_are_derivable
      (s: TestedSystem.state term 'internal)
    : prop =
  forall (input_t: term).
    Bag.mem input_t s.inputs ==> adv.derivable s.know input_t



// The `iff_instance` lemmas are equivalent to the following `iff` lemmas, but
// with the universally quantified variables moved into the parameters. This
// allows the SMT solver to use the `iff_instance` lemmas to solve for the
// quantified versions without having to unfold the propositions to reason about
// the bi-implications.
let ma_initiator_ack_equivalent_transitions_enabled_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : prop =
  ma_nsl_initiator_ack_enabled (s2p_state s_p)
    session initiator responder responder_nonce initiator_key responder_pubkey <==>
  ma_sim_send_message3_enabled (s2p_state s_q)
    session initiator responder responder_nonce initiator_key responder_pubkey

let ma_initiator_ack_equivalent_transitions_enabled_iff
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
    (initiator responder: participant_id)
    (responder_nonce: nonce)
    (initiator_key: priv_key)
    (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder responder_nonce initiator_key responder_pubkey

let ma_responder_reply_equivalent_transitions_enabled_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : prop =
  ma_nsl_responder_reply_enabled (s2p_state s_p)
    session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey <==>
  (ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
   ma_sim_send_message2_enabled
     (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
     session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)

let ma_responder_reply_equivalent_transitions_enabled_iff
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
    (responder initiator: participant_id)
    (initiator_nonce responder_nonce: nonce)
    (responder_key: priv_key)
    (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
      session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey

let ma_initiator_output_equivalent_transitions_enabled_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : prop =
  ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder <==>
  ma_ideal_deliver_enabled (s2p_state s_q) session initiator responder Initiator

let ma_initiator_output_equivalent_transitions_enabled_iff
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
    (initiator responder: participant_id).
    ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder

let ma_initiator_start_equivalent_transitions_enabled_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : prop =
  ma_nsl_initiator_start_enabled (s2p_state s_p)
    session initiator responder initiator_nonce responder_pubkey <==>
  (ma_ideal_initiate_enabled (s2p_state s_q) session initiator responder Initiator /\
   ma_sim_send_message1_enabled
     (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
     session initiator responder initiator_nonce responder_pubkey)

let ma_initiator_start_equivalent_transitions_enabled_iff
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
    (initiator responder: participant_id)
    (initiator_nonce: nonce)
    (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder initiator_nonce responder_pubkey

let ma_responder_output_equivalent_transitions_enabled_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : prop =
  ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key <==>
  (ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
   ma_ideal_deliver_enabled
     (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
     session responder initiator Responder)

let ma_responder_output_equivalent_transitions_enabled_iff
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
    (responder initiator: participant_id)
    (responder_key: priv_key).
    ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q
      session responder initiator responder_key

(**
  Bisimulation relation used to prove observational bisimulation up to
  partitions between the NSL implementation and the Mutual Authentication
  ideal-plus-simulator protocols.
*)
let ma_bisim_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : prop =
  ma_same_knowledge s_p s_q /\
  ma_same_key_directory key_directory s_p s_q /\
  ma_same_inputs s_p s_q /\
  ma_same_used_nonces s_p s_q /\
  ma_impl_used_nonces_invariant s_p /\
  // Inductive invariant for the ideal system. Destructure sites recover those
  // conjuncts with `ma_ideal_system_inv_elim`.
  ma_ideal_system_inv corrupt key_directory s_q /\
  // `ma_ideal_request_matches_sim_session` (request ==> session) is NOT an
  // inductive invariant of the ideal system on its own (see its definition), so
  // it stays an explicit relation conjunct.
  ma_ideal_request_matches_sim_session s_q /\
  ma_initiator_session_correspondence s_p s_q /\
  ma_responder_session_correspondence s_p s_q /\
  ma_initiator_output_token_matches_impl_pending_output s_p s_q /\
  ma_responder_output_token_matches_impl_pending_output s_p s_q /\
  ma_inputs_are_derivable s_p /\
  ma_private_keys_not_derivable corrupt key_directory s_p /\
  ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q /\
  ma_responder_reply_equivalent_transitions_enabled_iff s_p s_q /\
  ma_initiator_output_equivalent_transitions_enabled_iff s_p s_q /\
  ma_initiator_start_equivalent_transitions_enabled_iff s_p s_q /\
  ma_responder_output_equivalent_transitions_enabled_iff s_p s_q
