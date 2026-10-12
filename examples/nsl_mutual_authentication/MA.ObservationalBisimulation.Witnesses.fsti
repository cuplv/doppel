module MA.ObservationalBisimulation.Witnesses

/// Explicit witness states for the NSL MA observational bisimulation proof.
///
/// This module fixes the intended successor-state shapes for the matching
/// implementation and ideal-plus-simulator transitions. The corresponding
/// reachability lemmas are declared here and proven in the matching `.fst`.

open SymbolicTypes

open AencTerms

open MA.NSL

open MA.Ideal

open MA.Adversary

open MA.Types

open TestedSystem

open Bag

module PartialMap = FStar.PartialMap

module Seq = FStar.Seq

open MA.ObservationalBisimulation.Relation
open MA.IdealInvariants

open MA.TestedProtocols

open ObservationalBisimulation

open TestEquivalence



/// =========================================================================
/// Impl -> Ideal witnesses
/// =========================================================================

/// When the implementation takes the `nsl_initiator_start` NetSend step,
/// the ideal system matches it with `ma_ideal_initiate` followed by
/// `ma_sim_send_message1`.

let ma_impl_initiator_start_ideal_witness
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : ideal_system_state =
  let s_q' =
    ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator
  in
  let s_q'' =
    ma_sim_send_message1_state s_q' session initiator responder initiator_nonce
  in
  p2s_state s_q''
    (Seq.snoc s_q.know
      (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey))

val ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures (
        let s_q' = ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey in
        if query_participant = initiator && query_session = session then
          ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
          Some (SimInitiatorSession
            {
              initiator = initiator;
              responder = responder;
              initiator_nonce = initiator_nonce;
              ack_sent = false
            })
        else
          ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
          ma_get_sim_participant_session_state (s2p_state s_q) query_participant query_session
      ))
      [SMTPat (ma_get_sim_participant_session_state
        (s2p_state (ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey))
        query_participant query_session)]

val ma_impl_initiator_start_ideal_witness_get_updated_sim_responder_session_state
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (query_responder: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures (
        let s_q' = ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey in
        match ma_sim_responder_session_state (s2p_state s_q') query_responder query_session with
        | Some responder_state ->
          ma_sim_responder_session_state (s2p_state s_q) query_responder query_session ==
          Some responder_state
        | None -> True))
      [SMTPat (ma_sim_responder_session_state
        (s2p_state (ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey))
        query_responder query_session)]

val ma_impl_initiator_start_ideal_witness_updated_session_requests
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (query_session: session_id)
    : Lemma
      (ensures (
        let s_q' = ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey in
        let request = {party = initiator; peer = responder; role = Initiator} in
        if query_session = session
        then ma_session_requests (s2p_state s_q') session == Set.add request (ma_session_requests (s2p_state s_q) session)
        else ma_session_requests (s2p_state s_q') query_session == ma_session_requests (s2p_state s_q) query_session))
      [SMTPat (ma_session_requests
        (s2p_state (ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey))
        query_session)]

val ma_obs_bisim_observable_step_impl_initiator_start
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires (
        let sent_term =
          ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
        in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_start_enabled (s2p_state s_p)
          session initiator responder initiator_nonce responder_pubkey /\
        ma_nsl_initiator_start_transition (s2p_state s_p)
          session initiator responder
          sent_term
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q
          [TestedSystem.Internal lid; TestedSystem.Observable NetSend lid]
          (ma_impl_initiator_start_ideal_witness
            s_q session initiator responder initiator_nonce responder_pubkey)))


/// When the implementation takes the `nsl_responder_reply` NetSend step,
/// the ideal system matches it with `ma_ideal_initiate` followed by
/// `ma_sim_send_message2`.

let ma_impl_responder_reply_ideal_witness
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : ideal_system_state =
  let s_q_mid =
    ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder
  in
  let s_q' =
    ma_sim_send_message2_state s_q_mid session responder initiator
      initiator_nonce responder_nonce responder_key
  in
  p2s_state s_q'
    (Seq.snoc s_q.know
      (ma_nsl_message2_term session initiator responder initiator_nonce responder_nonce initiator_pubkey))

val ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures (
        let s_q' = ma_impl_responder_reply_ideal_witness
          s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey in
        if query_participant = responder && query_session = session then
          ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
          Some (SimResponderSession
            {
              responder = responder;
              initiator = initiator;
              responder_nonce = responder_nonce;
              output_forwarded = false
            })
        else
          ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
          ma_get_sim_participant_session_state (s2p_state s_q) query_participant query_session
      ))
      [SMTPat (ma_get_sim_participant_session_state
        (s2p_state (ma_impl_responder_reply_ideal_witness
          s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey))
        query_participant query_session)]

val ma_impl_responder_reply_ideal_witness_get_updated_sim_responder_session_state
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (query_responder: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures (
        let s_q' = ma_impl_responder_reply_ideal_witness
          s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey in
        if query_responder = responder && query_session = session then
          ma_sim_responder_session_state (s2p_state s_q') query_responder query_session ==
          Some {
            responder = responder;
            initiator = initiator;
            responder_nonce = responder_nonce;
            output_forwarded = false
          }
        else
          ma_sim_responder_session_state (s2p_state s_q') query_responder query_session ==
          ma_sim_responder_session_state (s2p_state s_q) query_responder query_session))
      [SMTPat (ma_sim_responder_session_state
        (s2p_state (ma_impl_responder_reply_ideal_witness
          s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey))
        query_responder query_session)]

val ma_impl_responder_reply_ideal_witness_updated_session_requests
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (query_session: session_id)
    : Lemma
      (ensures (
        let s_q' = ma_impl_responder_reply_ideal_witness
          s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey in
        let request = {party = responder; peer = initiator; role = Responder} in
        if query_session = session
        then ma_session_requests (s2p_state s_q') session == Set.add request (ma_session_requests (s2p_state s_q) session)
        else ma_session_requests (s2p_state s_q') query_session == ma_session_requests (s2p_state s_q) query_session))
      [SMTPat (ma_session_requests
        (s2p_state (ma_impl_responder_reply_ideal_witness
          s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey))
        query_session)]

val ma_obs_bisim_observable_step_impl_responder_reply
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires (
        let sent_term =
          ma_nsl_message2_term
            session initiator responder initiator_nonce responder_nonce initiator_pubkey
        in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_responder_reply_enabled (s2p_state s_p)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey /\
        ma_nsl_responder_reply_transition (s2p_state s_p)
          session responder initiator
          sent_term
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q
          [TestedSystem.Internal lid; TestedSystem.Observable NetSend lid]
          (ma_impl_responder_reply_ideal_witness
            s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)))


/// When the implementation takes the `nsl_initiator_ack` NetSend step,
/// the ideal system matches it directly with `ma_sim_send_message3`.

let ma_impl_initiator_ack_ideal_witness
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : ideal_system_state =
  let s_q' =
    ma_sim_send_message3_state (s2p_state s_q) session initiator responder responder_nonce initiator_key
  in
  p2s_state s_q'
    (Seq.snoc s_q.know
      (ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey))

val ma_obs_bisim_observable_step_impl_initiator_ack
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires (
        let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
        in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_ack_enabled (s2p_state s_p)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        ma_nsl_initiator_ack_transition (s2p_state s_p)
          session initiator responder
          sent_term
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q
          [TestedSystem.Observable NetSend lid]
          (ma_impl_initiator_ack_ideal_witness
            s_q session initiator responder responder_nonce initiator_key responder_pubkey)))


/// When the implementation takes the `nsl_initiator_output` IoSend step,
/// the ideal system matches it directly with `ma_ideal_deliver`.

let ma_impl_initiator_output_ideal_witness
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : ideal_system_state =
  let s_q' = ma_ideal_deliver_state (s2p_state s_q) session initiator responder in
  p2s_state s_q'
    (Seq.snoc s_q.know (ma_authenticated_term session initiator responder))

val ma_impl_initiator_output_ideal_witness_knowledge
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).know ==
        Seq.snoc s_q.know (ma_authenticated_term session initiator responder))
      [SMTPat (ma_impl_initiator_output_ideal_witness s_q session initiator responder).know]

val ma_impl_initiator_output_ideal_witness_preserves_inputs
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).inputs ==
        s_q.inputs)
      [SMTPat (ma_impl_initiator_output_ideal_witness s_q session initiator responder).inputs]

val ma_impl_initiator_output_ideal_witness_preserves_key_directory
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.key_directory ==
        s_q.internal.key_directory)
      [SMTPat (ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.key_directory]

val ma_impl_initiator_output_ideal_witness_preserves_sim_participant_sessions
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.sim_participant_sessions ==
        s_q.internal.sim_participant_sessions)
      [SMTPat (ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.sim_participant_sessions]

val ma_impl_initiator_output_ideal_witness_session_requests_eq
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures
        ma_session_requests
          (s2p_state (ma_impl_initiator_output_ideal_witness s_q session initiator responder))
          query_session ==
        ma_session_requests (s2p_state s_q) query_session)
      [SMTPat (ma_session_requests
        (s2p_state (ma_impl_initiator_output_ideal_witness s_q session initiator responder))
        query_session)]

val ma_obs_bisim_observable_step_impl_initiator_output
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
    : Lemma
      (requires (
        let output_term = ma_authenticated_term session initiator responder in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
        ma_nsl_initiator_output_transition (s2p_state s_p)
          session initiator responder
          output_term
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q
          [TestedSystem.Observable IoSend lid]
          (ma_impl_initiator_output_ideal_witness s_q session initiator responder)))


/// When the implementation takes the `nsl_responder_output` IoSend step,
/// the ideal system matches it with `ma_sim_receive_message3` followed by
/// `ma_ideal_deliver`.

let ma_impl_responder_output_ideal_witness
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : ideal_system_state =
  let s_q_mid =
    ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key
  in
  let s_q' = ma_ideal_deliver_state s_q_mid session responder initiator in
  p2s_state s_q'
    (Seq.snoc s_q.know (ma_authenticated_term session responder initiator))

val ma_impl_responder_output_ideal_witness_knowledge
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key).know ==
        Seq.snoc s_q.know (ma_authenticated_term session responder initiator))
      [SMTPat (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key).know]

val ma_impl_responder_output_ideal_witness_session_requests_eq
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (query_session: session_id)
    : Lemma
      (ensures
        ma_session_requests
          (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key))
          query_session ==
        ma_session_requests (s2p_state s_q) query_session)
      [SMTPat (ma_session_requests
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key))
        query_session)]

val ma_impl_responder_output_ideal_witness_preserves_key_directory
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.key_directory ==
        (s2p_state s_q).internal.key_directory)
      [SMTPat (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.key_directory]

val ma_impl_responder_output_ideal_witness_preserves_used_nonces
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.used_nonces ==
        (s2p_state s_q).internal.used_nonces)
      [SMTPat (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.used_nonces]

val ma_impl_responder_output_ideal_witness_preserves_ideal_to_sim_channel
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.ideal_to_sim_channel ==
        (s2p_state s_q).internal.ideal_to_sim_channel)
      [SMTPat (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.ideal_to_sim_channel]

val ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (requires Some? (ma_sim_responder_session_state (s2p_state s_q) responder session))
      (ensures (
        let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
        let responder_state = Some?.v (ma_sim_responder_session_state (s2p_state s_q) responder session) in
        if query_participant = responder && query_session = session then
          ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
          Some (SimResponderSession { responder_state with output_forwarded = true })
        else
          ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
          ma_get_sim_participant_session_state (s2p_state s_q) query_participant query_session
      ))
      [SMTPat (ma_get_sim_participant_session_state
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key))
        query_participant query_session)]

val ma_impl_responder_output_ideal_witness_preserves_sim_responder_session_fields
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (query_responder: participant_id)
      (query_session: session_id)
    : Lemma
      (requires Some? (ma_sim_responder_session_state (s2p_state s_q) responder session))
      (ensures (
        let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
        let post_entry = ma_sim_responder_session_state (s2p_state s_q') query_responder query_session in
        let pre_entry = ma_sim_responder_session_state (s2p_state s_q) query_responder query_session in
        Some? post_entry ==>
          Some? pre_entry /\
          (let post_responder_state = Some?.v post_entry in
          let pre_responder_state = Some?.v pre_entry in
          post_responder_state.responder == pre_responder_state.responder /\
          post_responder_state.initiator == pre_responder_state.initiator /\
          post_responder_state.responder_nonce == pre_responder_state.responder_nonce)
      ))
      [SMTPat (ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
        s_q session responder initiator responder_key query_responder query_session)]

val ma_obs_bisim_observable_step_impl_responder_output
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires (
        let output_term = ma_authenticated_term session responder initiator in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
        ma_nsl_responder_output_transition (s2p_state s_p)
          session responder initiator
          output_term
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q
          [TestedSystem.Internal lid; TestedSystem.Observable IoSend lid]
          (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)))



/// =========================================================================
/// Ideal -> Impl witnesses
/// =========================================================================

/// When the ideal system takes the eventual-observable sequence
/// `ma_ideal_initiate; ma_sim_send_message1`, the implementation matches it
/// with the `nsl_initiator_start` NetSend step.

let ma_ideal_send_message1_impl_witness
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : impl_system_state =
  let s_p' =
    ma_nsl_initiator_start_state (s2p_state s_p) session initiator responder initiator_nonce
  in
  p2s_state s_p'
    (Seq.snoc s_p.know
      (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey))

val ma_obs_bisim_observable_step_ideal_send_message1
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires (
        let sent_term =
          ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
        in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_start_enabled (s2p_state s_p)
          session initiator responder initiator_nonce responder_pubkey /\
        (exists (s_q_mid: ideal_system_state).
          ma_ideal_initiate_protocol_transition (s2p_state s_q)
            session initiator responder Initiator
            (s2p_state s_q_mid) /\
          s_q_mid.know == s_q.know /\
          ma_sim_send_message1_protocol_transition (s2p_state s_q_mid)
            session initiator responder
            sent_term
            (s2p_state s_q') /\
          s_q'.know == Seq.snoc s_q_mid.know sent_term)))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p
          [TestedSystem.Observable NetSend lid]
          (ma_ideal_send_message1_impl_witness
            s_p session initiator responder initiator_nonce responder_pubkey)))


/// When the ideal system takes the eventual-observable sequence
/// `ma_ideal_initiate; ma_sim_send_message2`, the implementation matches it
/// with the `nsl_responder_reply` NetSend step.

let ma_ideal_send_message2_impl_witness
      (s_p: impl_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : impl_system_state =
  let s_p' =
    ma_nsl_responder_reply_state (s2p_state s_p) session responder initiator
      initiator_nonce responder_nonce responder_key
  in
  p2s_state s_p'
    (Seq.snoc s_p.know
      (ma_nsl_message2_term session initiator responder initiator_nonce responder_nonce initiator_pubkey))

val ma_obs_bisim_observable_step_ideal_send_message2
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires (
        let sent_term =
          ma_nsl_message2_term
            session initiator responder initiator_nonce responder_nonce initiator_pubkey
        in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey /\
        (exists (s_q_mid: ideal_system_state).
          ma_ideal_initiate_protocol_transition (s2p_state s_q)
            session responder initiator Responder
            (s2p_state s_q_mid) /\
          s_q_mid.know == s_q.know /\
          ma_sim_send_message2_protocol_transition (s2p_state s_q_mid)
            session responder initiator
            sent_term
            (s2p_state s_q') /\
          s_q'.know == Seq.snoc s_q_mid.know sent_term)))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p
          [TestedSystem.Observable NetSend lid]
          (ma_ideal_send_message2_impl_witness
            s_p session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)))


/// When the ideal system emits the third simulated NSL message via
/// `ma_sim_send_message3`, the implementation matches it with the
/// `nsl_initiator_ack` NetSend step.

let ma_ideal_send_message3_impl_witness
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : impl_system_state =
  let s_p' =
    ma_nsl_initiator_ack_state (s2p_state s_p) session initiator responder responder_nonce initiator_key
  in
  p2s_state s_p'
    (Seq.snoc s_p.know
      (ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey))

val ma_ideal_send_message3_impl_witness_preserves_used_nonces
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (ensures
        (ma_ideal_send_message3_impl_witness
          s_p session initiator responder responder_nonce initiator_key responder_pubkey).internal.used_nonces ==
        s_p.internal.used_nonces)
      [SMTPat (ma_ideal_send_message3_impl_witness s_p session initiator responder responder_nonce initiator_key responder_pubkey).internal.used_nonces]

val ma_ideal_send_message3_impl_witness_transition
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_nsl_initiator_ack_enabled (s2p_state s_p)
          session initiator responder responder_nonce initiator_key responder_pubkey)
      (ensures (
        let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
        in
        ma_nsl_initiator_ack_transition (s2p_state s_p) session initiator responder sent_term
          (s2p_state
            (ma_ideal_send_message3_impl_witness
              s_p session initiator responder responder_nonce initiator_key responder_pubkey))))

val ma_obs_bisim_observable_step_ideal_send_message3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires (
        let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
        in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_sim_send_message3_enabled (s2p_state s_q)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        ma_sim_send_message3_protocol_transition (s2p_state s_q)
          session initiator responder
          sent_term
          (s2p_state s_q') /\
        s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p
          [TestedSystem.Observable NetSend lid]
          (ma_ideal_send_message3_impl_witness
            s_p session initiator responder responder_nonce initiator_key responder_pubkey)))


/// When the ideal system takes the initiator-side `ma_ideal_deliver` step,
/// the implementation matches it with the `nsl_initiator_output` IoSend step.

let ma_ideal_deliver_initiator_impl_witness
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : impl_system_state =
  let s_p' = ma_nsl_initiator_output_state (s2p_state s_p) session initiator responder in
  p2s_state s_p'
    (Seq.snoc s_p.know (ma_authenticated_term session initiator responder))

val ma_obs_bisim_observable_step_ideal_deliver_initiator
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_q': ideal_system_state)
    : Lemma
      (requires (
        let output_term = ma_authenticated_term session initiator responder in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
        ma_ideal_deliver_protocol_transition (s2p_state s_q)
          session initiator responder Initiator
          output_term
          (s2p_state s_q') /\
        s_q'.know == Seq.snoc s_q.know output_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p
          [TestedSystem.Observable IoSend lid]
          (ma_ideal_deliver_initiator_impl_witness s_p session initiator responder)))


/// When the ideal system takes the responder-side `ma_ideal_deliver` step,
/// the implementation matches it with the `nsl_responder_output` IoSend step.

let ma_ideal_deliver_responder_impl_witness
      (s_p: impl_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : impl_system_state =
  let s_p' =
    ma_nsl_responder_output_state (s2p_state s_p) session responder initiator responder_key
  in
  p2s_state s_p'
    (Seq.snoc s_p.know (ma_authenticated_term session responder initiator))

val ma_obs_bisim_observable_step_ideal_deliver_responder
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_q': ideal_system_state)
    : Lemma
      (requires (
        let output_term = ma_authenticated_term session responder initiator in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
        ma_ideal_deliver_protocol_transition (s2p_state s_q)
          session responder initiator Responder
          output_term
          (s2p_state s_q') /\
        s_q'.know == Seq.snoc s_q.know output_term))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p
          [TestedSystem.Observable IoSend lid]
          (ma_ideal_deliver_responder_impl_witness s_p session responder initiator responder_key)))
