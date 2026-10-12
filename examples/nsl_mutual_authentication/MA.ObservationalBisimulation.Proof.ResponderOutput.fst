module MA.ObservationalBisimulation.Proof.ResponderOutput

/// Preservation lemmas for the impl_responder_output transition family,
/// extracted from MA.ObservationalBisimulation.Proof to shrink the top-level
/// verification job. Only the top-level relation-preservation lemma
/// [ma_obs_bisim_observable_step_impl_responder_output_preserves_relation] is
/// used outside this module; all other helpers are local.
///
/// This module owns the `--split_queries always --z3rlimit_factor 4 --ifuel 4`
/// solver options scoped around the cluster.
///
/// Verification time: ~3:03 (standalone, clean)

open SymbolicTypes
open AencTerms
open AdversaryAenc
open MA.NSL
open MA.Ideal
open MA.Adversary
open MA.Types
open StaticEquivalence
open TestedSystem
open ObservationalBisimulation
open TestEquivalence
open Partition
open Bag

module PartialMap = FStar.PartialMap
module Set = FStar.Set
module SeqProps = FStar.Seq.Properties
module List = FStar.List.Tot.Base

open MA.ObservationalBisimulation.Relation
open MA.IdealInvariants
open MA.ObservationalBisimulation.Witnesses
open MA.ObservationalBisimulation.Witnesses.IdealInvariants
open MA.TestedProtocols
open MA.ObservationalBisimulation.Proof.Common
open MA.ObservationalBisimulation.Proof.MessageDerivability

#push-options "--z3rlimit_factor 4 --ifuel 4"

private
let ma_impl_responder_output_preserves_responder_output_iff_instance
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        ma_responder_output_equivalent_transitions_enabled_iff_instance s_p'
          (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)
          quant_session quant_responder quant_initiator quant_responder_key) =
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in

  if quant_responder = responder && quant_session = session
  then (
    // The responder output transitions can only be taken at most once per
    // responder per session, so they are both no longer enabled.
    assert ~(ma_nsl_responder_output_enabled (s2p_state s_p') quant_session quant_responder quant_initiator quant_responder_key);
    assert ~(ma_sim_receive_message3_enabled (s2p_state s_q') quant_session quant_responder quant_initiator quant_responder_key)
  )
  else (
    // The quantified instance is for a different session or responder, so the
    // relevant state is unchanged and the invariant will continue to hold.
    ma_ideal_system_inv_elim corrupt key_directory s_q;
    ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s2p_state s_p) session responder initiator responder_key quant_responder quant_session;
    ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
      s_q session responder initiator responder_key quant_responder quant_session;
    // The firing transition only removes the message3 input for the firing
    // session/responder.  Frame the impl input bag so the quantified instance's
    // message3 membership is unchanged by the removal.
    let firing_responder_state = Some?.v (ma_responder_session_state (s2p_state s_p) responder session) in
    let removed_message3 = ma_nsl_message3_network_term
      session initiator responder firing_responder_state.responder_nonce (PubKey responder_key) in
    assert (s_p'.inputs == Bag.remove removed_message3 s_p.inputs) ;
    (match ma_responder_session_state (s2p_state s_p) quant_responder quant_session with
     | Some quant_responder_state ->
       let quant_message3 = ma_nsl_message3_network_term
         quant_session quant_initiator quant_responder quant_responder_state.responder_nonce (PubKey quant_responder_key) in
       Bag.mem_remove quant_message3 removed_message3 s_p.inputs
     | None -> ()) ;
    assert (ma_nsl_responder_output_enabled (s2p_state s_p') quant_session quant_responder quant_initiator quant_responder_key <==> ma_nsl_responder_output_enabled (s2p_state s_p) quant_session quant_responder quant_initiator quant_responder_key);
    assert (
      (ma_sim_receive_message3_enabled (s2p_state s_q') quant_session quant_responder quant_initiator quant_responder_key
        /\ ma_ideal_deliver_enabled
          (ma_sim_receive_message3_state (s2p_state s_q') quant_session quant_responder quant_initiator quant_responder_key)
          quant_session quant_responder quant_initiator Responder)
      <==>
      (ma_sim_receive_message3_enabled (s2p_state s_q) quant_session quant_responder quant_initiator quant_responder_key
        /\ ma_ideal_deliver_enabled
          (ma_sim_receive_message3_state (s2p_state s_q) quant_session quant_responder quant_initiator quant_responder_key)
          quant_session quant_responder quant_initiator Responder)
    );
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q quant_session quant_responder quant_initiator quant_responder_key);
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q' quant_session quant_responder quant_initiator quant_responder_key)
  )


private
let ma_impl_responder_output_preserves_structural_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
          ma_same_knowledge s_p' s_q' /\
          ma_same_key_directory key_directory s_p' s_q' /\
          ma_same_inputs s_p' s_q' /\
          ma_same_used_nonces s_p' s_q' /\
          ma_initiator_session_correspondence s_p' s_q' /\
          ma_responder_session_correspondence s_p' s_q')) =
  let output_term = ma_authenticated_term session responder initiator in
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
  assert (Some? (ma_responder_session_state (s2p_state s_p) responder session)) ;
  assert (s2p_state s_p' == ma_nsl_responder_output_state
      (s2p_state s_p) session responder initiator responder_key) ;
  assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
      s_p s_q session responder initiator responder_key) ;
  assert (ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
     ma_ideal_deliver_enabled
       (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
       session responder initiator Responder) ;
  let initiator_corr_helper (query_session: session_id) (query_initiator: participant_id)
      : Lemma
        (ensures (
          let initiator_entry =
            ma_initiator_session_state (s2p_state s_p') query_initiator query_session
          in
          let sim_entry =
            ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session
          in
          (Some? initiator_entry <==> Some? sim_entry) /\
          (Some? initiator_entry ==> (
            let initiator_state = Some?.v initiator_entry in
            let sim_state = Some?.v sim_entry in
            initiator_state.initiator == sim_state.initiator /\
            initiator_state.responder == sim_state.responder /\
            initiator_state.initiator_nonce == sim_state.initiator_nonce /\
            initiator_state.ack_sent == sim_state.ack_sent)))) =
    assert (let initiator_entry =
        ma_initiator_session_state (s2p_state s_p) query_initiator query_session
      in
      let sim_entry =
        ma_sim_initiator_session_state (s2p_state s_q) query_initiator query_session
      in
      (Some? initiator_entry <==> Some? sim_entry) /\
      (Some? initiator_entry ==> (
        let initiator_state = Some?.v initiator_entry in
        let sim_state = Some?.v sim_entry in
        initiator_state.initiator == sim_state.initiator /\
        initiator_state.responder == sim_state.responder /\
        initiator_state.initiator_nonce == sim_state.initiator_nonce /\
        initiator_state.ack_sent == sim_state.ack_sent))) ;
    ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s2p_state s_p) session responder initiator responder_key query_initiator query_session;
    ma_sim_receive_message3_state_get_updated_sim_participant_session_state
      (s2p_state s_q) session responder initiator responder_key query_initiator query_session;
    ma_ideal_deliver_state_preserves_get_sim_participant_session_state
      (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
      session responder initiator query_initiator query_session;
    assert (let initiator_entry =
        ma_initiator_session_state (s2p_state s_p') query_initiator query_session
      in
      let sim_entry =
        ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session
      in
      (Some? initiator_entry <==> Some? sim_entry) /\
      (Some? initiator_entry ==> (
        let initiator_state = Some?.v initiator_entry in
        let sim_state = Some?.v sim_entry in
        initiator_state.initiator == sim_state.initiator /\
        initiator_state.responder == sim_state.responder /\
        initiator_state.initiator_nonce == sim_state.initiator_nonce /\
        initiator_state.ack_sent == sim_state.ack_sent)))
  in
  let responder_corr_helper (query_session: session_id) (query_responder: participant_id)
      : Lemma
        (ensures (
          let responder_entry =
            ma_responder_session_state (s2p_state s_p') query_responder query_session
          in
          let sim_entry =
            ma_sim_responder_session_state (s2p_state s_q') query_responder query_session
          in
          (Some? responder_entry <==> Some? sim_entry) /\
          (Some? responder_entry ==> (
            let responder_state = Some?.v responder_entry in
            let sim_state = Some?.v sim_entry in
            responder_state.responder == sim_state.responder /\
            responder_state.initiator == sim_state.initiator /\
            responder_state.responder_nonce == sim_state.responder_nonce /\
            responder_state.output_sent == sim_state.output_forwarded)))) =
    assert (let responder_entry =
        ma_responder_session_state (s2p_state s_p) query_responder query_session
      in
      let sim_entry =
        ma_sim_responder_session_state (s2p_state s_q) query_responder query_session
      in
      (Some? responder_entry <==> Some? sim_entry) /\
      (Some? responder_entry ==> (
        let responder_state = Some?.v responder_entry in
        let sim_state = Some?.v sim_entry in
        responder_state.responder == sim_state.responder /\
        responder_state.initiator == sim_state.initiator /\
        responder_state.responder_nonce == sim_state.responder_nonce /\
        responder_state.output_sent == sim_state.output_forwarded))) ;
    ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s2p_state s_p) session responder initiator responder_key query_responder query_session;
    ma_sim_receive_message3_state_get_updated_sim_participant_session_state
      (s2p_state s_q) session responder initiator responder_key query_responder query_session;
    ma_ideal_deliver_state_preserves_get_sim_participant_session_state
      (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
      session responder initiator query_responder query_session;
    assert (let responder_entry =
        ma_responder_session_state (s2p_state s_p') query_responder query_session
      in
      let sim_entry =
        ma_sim_responder_session_state (s2p_state s_q') query_responder query_session
      in
      (Some? responder_entry <==> Some? sim_entry) /\
      (Some? responder_entry ==> (
        let responder_state = Some?.v responder_entry in
        let sim_state = Some?.v sim_entry in
        responder_state.responder == sim_state.responder /\
        responder_state.initiator == sim_state.initiator /\
        responder_state.responder_nonce == sim_state.responder_nonce /\
        responder_state.output_sent == sim_state.output_forwarded)))
  in
  FStar.Classical.forall_intro_2 initiator_corr_helper;
  FStar.Classical.forall_intro_2 responder_corr_helper;
  assert (ma_initiator_session_correspondence s_p' s_q' /\
     ma_responder_session_correspondence s_p' s_q') ;
  assert (ma_same_knowledge s_p' s_q' /\
     ma_same_key_directory key_directory s_p' s_q' /\
     ma_same_inputs s_p' s_q' /\
     ma_same_used_nonces s_p' s_q' /\
     ma_initiator_session_correspondence s_p' s_q' /\
     ma_responder_session_correspondence s_p' s_q')

private
let ma_impl_responder_output_preserves_used_nonce_invariant_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        ma_impl_used_nonces_invariant s_p') =
  let output_term = ma_authenticated_term session responder initiator in
  ma_knowledge_nonces_snoc s_p.know output_term;
  // `output_term` is `Pair (SessionId _) (Pair (ParticipantId _) (ParticipantId _))`,
  // so `ma_term_nonces` unfolds to nested unions of empty sets.  Drive the
  // recursion explicitly so the Set extensional-equality query closes without
  // depending on fuel-sensitive triggers.
  assert (ma_term_nonces output_term ==
    Set.union (ma_term_nonces (SessionId session))
      (Set.union (ma_term_nonces (ParticipantId responder))
                 (ma_term_nonces (ParticipantId initiator)))) ;
  assert (Set.equal (ma_term_nonces output_term) Set.empty);
  assert (ma_impl_used_nonces_invariant s_p);
  assert (Some? (ma_responder_session_state (s2p_state s_p) responder session));
  assert (s2p_state s_p' == ma_nsl_responder_output_state
      (s2p_state s_p) session responder initiator responder_key) ;
  assert (s_p'.internal.used_nonces == s_p.internal.used_nonces) ;
  ma_knowledge_nonces_snoc_empty_preserves_subset s_p.know output_term s_p.internal.used_nonces;
  let impl_stored_helper
        (query_participant: participant_id)
        (query_session: session_id)
        (n: nonce)
      : Lemma
        (ensures
          (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
          | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
          | None -> True)) =
    let responder_state = Some?.v (ma_responder_session_state (s2p_state s_p) responder session) in
    if query_participant = responder then
      if query_session = session then
        (ma_get_participant_session_state_after_update_same (s2p_state s_p)
          responder session (ResponderSession { responder_state with output_sent = true });
         assert (ma_get_participant_session_state (s2p_state s_p') query_participant query_session ==
           Some (ResponderSession { responder_state with output_sent = true })) ;
         assert (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
           | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
           | None -> True))
      else
        (ma_get_participant_session_state_after_update_different (s2p_state s_p)
          responder session (ResponderSession { responder_state with output_sent = true })
          query_participant query_session;
         assert (ma_get_participant_session_state (s2p_state s_p') query_participant query_session ==
           ma_get_participant_session_state (s2p_state s_p) query_participant query_session);
         assert (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
           | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
           | None -> True))
    else
      (ma_get_participant_session_state_after_update_different (s2p_state s_p)
        responder session (ResponderSession { responder_state with output_sent = true })
        query_participant query_session;
       assert (ma_get_participant_session_state (s2p_state s_p') query_participant query_session ==
         ma_get_participant_session_state (s2p_state s_p) query_participant query_session);
       assert (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
         | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
         | None -> True))
  in
  FStar.Classical.forall_intro_3 impl_stored_helper;
  assert (ma_impl_used_nonces_invariant s_p')

private
let ma_impl_responder_output_preserves_ideal_bookkeeping_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
          ma_ideal_request_matches_sim_session s_q' /\
          ma_initiator_output_token_matches_impl_pending_output s_p' s_q')) =
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
  assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
      s_p s_q session responder initiator responder_key) ;
  assert (ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
     ma_ideal_deliver_enabled
       (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
       session responder initiator Responder) ;
  let post_ideal_request_matches_sim_session ()
      : Lemma (ensures ma_ideal_request_matches_sim_session s_q') =
    let helper (query_session: session_id)
               (query_party query_peer: participant_id)
               (query_role: role)
        : Lemma
          (ensures
            Set.mem { party = query_party; peer = query_peer; role = query_role }
              (ma_session_requests (s2p_state s_q') query_session) ==>
            (match ma_get_sim_participant_session_state (s2p_state s_q') query_party query_session with
            | Some (SimInitiatorSession initiator_state) ->
              query_role == Initiator /\
              initiator_state.initiator == query_party /\
              initiator_state.responder == query_peer
            | Some (SimResponderSession responder_state) ->
              query_role == Responder /\
              responder_state.responder == query_party /\
              responder_state.initiator == query_peer
            | None -> False)) =
      ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
        s_q session responder initiator responder_key query_party query_session;
      ma_impl_responder_output_ideal_witness_session_requests_eq
        s_q session responder initiator responder_key query_session;
      assert (Set.mem { party = query_party; peer = query_peer; role = query_role }
          (ma_session_requests (s2p_state s_q') query_session) ==>
        (match ma_get_sim_participant_session_state (s2p_state s_q') query_party query_session with
        | Some (SimInitiatorSession initiator_state) ->
          query_role == Initiator /\
          initiator_state.initiator == query_party /\
          initiator_state.responder == query_peer
        | Some (SimResponderSession responder_state) ->
          query_role == Responder /\
          responder_state.responder == query_party /\
          responder_state.initiator == query_peer
        | None -> False))
    in
    FStar.Classical.forall_intro_4 helper
  in
  post_ideal_request_matches_sim_session ();
  let post_initiator_output_token_matches_impl_pending_output ()
      : Lemma (ensures ma_initiator_output_token_matches_impl_pending_output s_p' s_q') =
    let helper (query_session: session_id) (query_initiator: participant_id)
        : Lemma
          (ensures
            (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
            | Some initiator_state ->
              (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
              (initiator_state.ack_sent ==>
                (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
                 not initiator_state.output_sent))
            | None -> True)) =
      ma_nsl_responder_output_state_preserves_get_participant_session_state
        (s2p_state s_p) session responder initiator responder_key query_initiator query_session;
      if query_session = session && query_initiator = responder then
        assert (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
          | Some initiator_state ->
            (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
            (initiator_state.ack_sent ==>
              (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
               not initiator_state.output_sent))
          | None -> True)
      else
        (assert (ma_output_term query_session query_initiator <> ma_output_term session responder) ;
        assert (ma_initiator_session_state (s2p_state s_p') query_initiator query_session ==
           ma_initiator_session_state (s2p_state s_p) query_initiator query_session) ;
        assert (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
           Set.mem (ma_output_term query_session query_initiator) (s2p_state s_q).internal.sim_to_ideal_channel) ;
        assert (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
          | Some initiator_state ->
            (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
            (initiator_state.ack_sent ==>
              (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
               not initiator_state.output_sent))
          | None -> True))
    in
    FStar.Classical.forall_intro_2 helper;
    assert (ma_initiator_output_token_matches_impl_pending_output s_p' s_q')
  in
  post_initiator_output_token_matches_impl_pending_output ();
  assert (ma_ideal_request_matches_sim_session s_q' /\
     ma_initiator_output_token_matches_impl_pending_output s_p' s_q')

private
let ma_impl_responder_output_preserves_input_derivability_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
          ma_inputs_are_derivable s_p')) =
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
  assert (ma_inputs_are_derivable s_p')

private
let ma_impl_responder_output_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
          ma_private_keys_not_derivable corrupt key_directory s_p')) =
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
  assert (ma_private_keys_not_derivable corrupt key_directory s_p) ;
  let impl_private_helper (participant: participant_id) (k: priv_key) (d: derivation)
      : Lemma
        (ensures
          PartialMap.sel key_directory participant == Some k /\
          not (Set.mem participant corrupt) ==>
          not (derive d s_p'.know = Some (PrivKey k))) =
    if PartialMap.sel key_directory participant = Some k && not (Set.mem participant corrupt) then
      if derive d s_p'.know = Some (PrivKey k) then
        (private_keys_learned_from_public_output_already_derivable
          s_p.know session responder initiator k d;
         assert (False))
  in
  FStar.Classical.forall_intro_3 impl_private_helper;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p')

private
let ma_impl_responder_output_preserves_enabledness_iffs
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
          ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')) =
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
  assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
      s_p s_q session responder initiator responder_key) ;
  assert (ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
     ma_ideal_deliver_enabled
       (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
       session responder initiator Responder) ;
  assert (Some? (ma_sim_responder_session_state (s2p_state s_q) responder session)) ;
  let post_responder_reply_iff_instance
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey})
    : Lemma
      (ensures
        ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey) =
    ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s2p_state s_p) session responder initiator responder_key quant_responder quant_session;
    ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
      s_q session responder initiator responder_key quant_responder quant_session;
    let selected_responder_state = Some?.v (ma_sim_responder_session_state (s2p_state s_q) responder session) in
    let removed_message3 = ma_nsl_message3_network_term
      session initiator responder selected_responder_state.responder_nonce (PubKey responder_key) in
    let responder_auth_input = ma_auth_input_term quant_session quant_responder quant_initiator Responder in
    let responder_message1_input = ma_nsl_message1_network_term
      quant_session quant_initiator quant_responder quant_initiator_nonce (PubKey quant_responder_key) in
    assert (responder_auth_input <> removed_message3) ;
    assert (responder_message1_input <> removed_message3) ;
    Bag.mem_remove responder_auth_input removed_message3 (s2p_state s_p).inputs;
    Bag.mem_remove responder_message1_input removed_message3 (s2p_state s_p).inputs;
    assert (s_p'.inputs == Bag.remove removed_message3 s_p.inputs) ;
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey) ;
    assert (ma_nsl_responder_reply_enabled (s2p_state s_p')
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey <==>
       ma_nsl_responder_reply_enabled (s2p_state s_p)
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey) ;
    assert (responder_message1_input <> responder_auth_input) ;
    assert (s_q'.inputs == Bag.remove removed_message3 s_q.inputs /\
       s_q'.internal.used_nonces == s_q.internal.used_nonces /\
       s_q'.internal.key_directory == s_q.internal.key_directory /\
       s_q'.internal.ideal_to_sim_channel == s_q.internal.ideal_to_sim_channel) ;
    Bag.mem_remove responder_auth_input removed_message3 s_q.inputs;
    Bag.mem_remove responder_message1_input removed_message3 s_q.inputs;
    Bag.mem_remove responder_message1_input responder_auth_input s_q'.inputs;
    Bag.mem_remove responder_message1_input responder_auth_input s_q.inputs;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q') quant_session quant_responder quant_initiator Responder
      quant_responder quant_session;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q) quant_session quant_responder quant_initiator Responder
      quant_responder quant_session;
    ma_ideal_initiate_state_preserves_key_directory
      (s2p_state s_q') quant_session quant_responder quant_initiator Responder;
    ma_ideal_initiate_state_preserves_key_directory
      (s2p_state s_q) quant_session quant_responder quant_initiator Responder;
    ma_ideal_initiate_state_preserves_used_nonces
      (s2p_state s_q') quant_session quant_responder quant_initiator Responder;
    ma_ideal_initiate_state_preserves_used_nonces
      (s2p_state s_q) quant_session quant_responder quant_initiator Responder;
    assert ((ma_ideal_initiate_enabled (s2p_state s_q') quant_session quant_responder quant_initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q') quant_session quant_responder quant_initiator Responder)
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey) <==>
       (ma_ideal_initiate_enabled (s2p_state s_q) quant_session quant_responder quant_initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q) quant_session quant_responder quant_initiator Responder)
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)) ;
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey)
  in
  let post_initiator_output_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
    : Lemma
      (ensures
        ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder) =
    ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s2p_state s_p) session responder initiator responder_key quant_initiator quant_session;
    ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
      s_q session responder initiator responder_key quant_initiator quant_session;
    ma_impl_responder_output_ideal_witness_session_requests_eq
      s_q session responder initiator responder_key quant_session;
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_initiator quant_responder) ;
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_initiator quant_responder)
  in
  let post_initiator_start_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (ensures
        ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) =
    ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s2p_state s_p) session responder initiator responder_key quant_initiator quant_session;
    ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
      s_q session responder initiator responder_key quant_initiator quant_session;
    ma_impl_responder_output_ideal_witness_session_requests_eq
      s_q session responder initiator responder_key quant_session;
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) ;
    assert (ma_nsl_initiator_start_enabled (s2p_state s_p')
        quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey <==>
       ma_nsl_initiator_start_enabled (s2p_state s_p)
        quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) ;
    let selected_responder_state = Some?.v (ma_sim_responder_session_state (s2p_state s_q) responder session) in
    let removed_message3 = ma_nsl_message3_network_term
      session initiator responder selected_responder_state.responder_nonce (PubKey responder_key) in
    let initiator_auth_input = ma_auth_input_term quant_session quant_initiator quant_responder Initiator in
    assert (initiator_auth_input <> removed_message3) ;
    assert (s_q'.inputs == Bag.remove removed_message3 s_q.inputs /\
       s_q'.internal.used_nonces == s_q.internal.used_nonces /\
       s_q'.internal.key_directory == s_q.internal.key_directory /\
       s_q'.internal.ideal_to_sim_channel == s_q.internal.ideal_to_sim_channel) ;
    Bag.mem_remove initiator_auth_input removed_message3 s_q.inputs;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q') quant_session quant_initiator quant_responder Initiator
      quant_initiator quant_session;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q) quant_session quant_initiator quant_responder Initiator
      quant_initiator quant_session;
    ma_ideal_initiate_state_preserves_key_directory
      (s2p_state s_q') quant_session quant_initiator quant_responder Initiator;
    ma_ideal_initiate_state_preserves_key_directory
      (s2p_state s_q) quant_session quant_initiator quant_responder Initiator;
    ma_ideal_initiate_state_preserves_used_nonces
      (s2p_state s_q') quant_session quant_initiator quant_responder Initiator;
    ma_ideal_initiate_state_preserves_used_nonces
      (s2p_state s_q) quant_session quant_initiator quant_responder Initiator;
    assert ((ma_ideal_initiate_enabled (s2p_state s_q') quant_session quant_initiator quant_responder Initiator /\
        ma_sim_send_message1_enabled
          (ma_ideal_initiate_state (s2p_state s_q') quant_session quant_initiator quant_responder Initiator)
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) <==>
       (ma_ideal_initiate_enabled (s2p_state s_q) quant_session quant_initiator quant_responder Initiator /\
        ma_sim_send_message1_enabled
          (ma_ideal_initiate_state (s2p_state s_q) quant_session quant_initiator quant_responder Initiator)
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey)) ;
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey)
  in
  let post_responder_output_iff_instance
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (ensures
        ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_responder_key) =
    ma_impl_responder_output_preserves_responder_output_iff_instance
      corrupt key_directory s_p s_q session responder initiator responder_key s_p'
      quant_session quant_responder quant_initiator quant_responder_key
  in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q') ;
  introduce forall
    (quant_session: session_id)
    (quant_responder quant_initiator: participant_id)
    (quant_initiator_nonce quant_responder_nonce: nonce)
    (quant_responder_key: priv_key)
    (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey}).
    ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
      quant_session quant_responder quant_initiator quant_initiator_nonce
      quant_responder_nonce quant_responder_key quant_initiator_pubkey
  with post_responder_reply_iff_instance quant_session quant_responder quant_initiator
    quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey;
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q') ;
  FStar.Classical.forall_intro_3 post_initiator_output_iff_instance;
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q') ;
  introduce forall
    (quant_session: session_id)
    (quant_initiator quant_responder: participant_id)
    (quant_initiator_nonce: nonce)
    (quant_responder_pubkey: term {PubKey? quant_responder_pubkey}).
    ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
      quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey
  with post_initiator_start_iff_instance quant_session quant_initiator quant_responder
    quant_initiator_nonce quant_responder_pubkey;
  assert (ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q') ;
  FStar.Classical.forall_intro_4 post_responder_output_iff_instance;
  assert (ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q') ;
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')

let ma_obs_bisim_observable_step_impl_responder_output_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session responder initiator in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
          ma_nsl_responder_output_transition (s2p_state s_p) session responder initiator output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          s_p'
          (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)) =
  let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
  ma_impl_responder_output_preserves_structural_clauses
    corrupt key_directory s_p s_q session responder initiator responder_key s_p';
  ma_impl_responder_output_preserves_used_nonce_invariant_clauses
    corrupt key_directory s_p s_q session responder initiator responder_key s_p';
  ma_impl_responder_output_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q session responder initiator responder_key s_p';
  ma_impl_responder_output_preserves_input_derivability_clauses
    corrupt key_directory s_p s_q session responder initiator responder_key s_p';
  ma_impl_responder_output_preserves_secrecy_clauses
    corrupt key_directory s_p s_q session responder initiator responder_key s_p';
  ma_impl_responder_output_preserves_enabledness_iffs
    corrupt key_directory s_p s_q session responder initiator responder_key s_p';
  // The opaque ideal-side invariant `ma_ideal_system_inv` at the post-state is
  // discharged directly by the witness invariant-preservation lemma (rather than
  // by reproving each conjunct via `ma_ideal_system_inv_elim`).  Establish the
  // ideal-side enabledness from the relation's responder-output iff together with
  // the impl-side enabledness, then invoke the preservation lemma.
  assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
      s_p s_q session responder initiator responder_key);
  assert (ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
     ma_ideal_deliver_enabled
       (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
       session responder initiator Responder);
  ma_impl_responder_output_ideal_witness_preserves_inv
    corrupt key_directory s_q session responder initiator responder_key;
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')
#pop-options
