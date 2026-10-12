module MA.ObservationalBisimulation.Proof.InputStep

/// Input-step preservation for the MA mutual-authentication protocol.
///
/// Extracted from `MA.ObservationalBisimulation.Proof.fst` to speed up
/// verification iteration. This cluster contains:
///   - Input-insert preservation helpers for the implementation-side and
///     relational relation clauses.  The ideal-side clauses (nonce freshness,
///     input derivability, Message2/Message3 authentication, secrecy, and
///     simulator-session bookkeeping) are not re-proven here: they are
///     conjuncts of `ma_ideal_system_inv`, which the call sites carry forward
///     across the input step via `ma_ideal_system_inv_preserved` and recover via
///     `ma_ideal_system_inv_elim`.
///   - The per-direction `ma_input_step_impl_preserves_*_clauses` lemmas.
///   - `ma_input_step_impl_preserves_enabledness_iffs` and
///     `ma_input_step_impl_preserves_relation_after_insert`.
///   - `ma_obs_bisim_input_step_impl` and `ma_obs_bisim_input_step_ideal`.
///
/// Verification time: ~3:07 (standalone, clean)

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

open MA.TestedProtocols

open MA.ObservationalBisimulation.Proof.Common

open MA.ObservationalBisimulation.Proof.MessageDerivability

private
let ma_input_insert_preserves_inputs_nonces_are_used
      (used_nonces: Set.set nonce)
      (know: knowledge term)
      (derivation0: derivation)
      (derived_input: term)
      (inputs: bag term)
    : Lemma
      (requires
        derive derivation0 know = Some derived_input /\
        ma_knowledge_nonces_are_used used_nonces know /\
        ma_inputs_nonces_are_used used_nonces inputs)
      (ensures
        ma_inputs_nonces_are_used used_nonces (Bag.insert derived_input inputs)) =
  ma_derive_term_nonces_in_knowledge_nonces know derivation0 derived_input;
  FStar.Set.Properties.set_subset_transitive
    (ma_term_nonces derived_input) (ma_knowledge_nonces know) used_nonces;
  let helper (input_t: term)
      : Lemma
        (ensures
          Bag.mem input_t (Bag.insert derived_input inputs) ==>
          ma_term_nonces_are_used used_nonces input_t) =
    Bag.mem_insert input_t derived_input inputs;
    if input_t = derived_input then ()
    else ()
  in
  FStar.Classical.forall_intro helper

private
let ma_input_insert_preserves_inputs_are_derivable
      (know: knowledge term)
      (derivation0: derivation)
      (derived_input: term)
      (inputs: bag term)
    : Lemma
      (requires
        derive derivation0 know = Some derived_input /\
        (forall (input_t: term). Bag.mem input_t inputs ==> adv.derivable know input_t))
      (ensures
        forall (input_t: term).
          Bag.mem input_t (Bag.insert derived_input inputs) ==> adv.derivable know input_t) =
  let helper (input_t: term)
      : Lemma
        (ensures
          Bag.mem input_t (Bag.insert derived_input inputs) ==> adv.derivable know input_t) =
    Bag.mem_insert input_t derived_input inputs;
    if input_t = derived_input then
      FStar.Classical.exists_intro
        (fun d -> derive d know = Some input_t) derivation0
    else ()
  in
  FStar.Classical.forall_intro helper

private
let ma_input_step_impl_preserves_structural_and_input_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs })
      (ensures
        ma_same_knowledge s_p' s_q' /\
        ma_same_key_directory key_directory s_p' s_q' /\
        ma_key_directory_injective key_directory /\
        ma_same_inputs s_p' s_q' /\
        ma_same_used_nonces s_p' s_q' /\
        ma_impl_used_nonces_invariant s_p' /\
        ma_impl_stored_nonces_are_used s_p' /\
        ma_inputs_are_derivable s_p') =
  // `ma_key_directory_injective` is recovered from the pre-state ideal
  // invariant; the ideal-side nonce/input/provenance clauses are not
  // re-proven here because they are subsumed by `ma_ideal_system_inv s_q'`
  // (established by `ma_ideal_system_inv_preserved` at the call sites).
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  assert (s_q'.know == s_q.know);
  assert (s_q'.internal == s_q.internal);
  assert (s_q'.inputs == Bag.insert derived_input s_q.inputs);
  assert (s_p.know == s_q.know /\
     s_p.inputs == s_q.inputs /\
     s_p.internal.used_nonces == s_q.internal.used_nonces /\
     ma_impl_used_nonces_invariant s_p /\
     ma_impl_stored_nonces_are_used s_p) ;
  ma_input_insert_preserves_inputs_nonces_are_used
    s_p.internal.used_nonces s_p.know derivation0 derived_input s_p.inputs;
  ma_input_insert_preserves_inputs_are_derivable
    s_p.know derivation0 derived_input s_p.inputs;
  let impl_stored_helper (participant: participant_id) (session: session_id) (n: nonce)
      : Lemma
        (ensures (
          match ma_get_participant_session_state (s2p_state s_p') participant session with
          | Some pss ->
            nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
          | None -> True)) =
    assert (ma_get_participant_session_state (s2p_state s_p') participant session ==
       ma_get_participant_session_state (s2p_state s_p) participant session) ;
    let h_stored : squash (ma_impl_stored_nonces_are_used s_p) = () in
    let h_participant = FStar.Classical.Sugar.forall_elim participant h_stored in
    let h_session = FStar.Classical.Sugar.forall_elim session h_participant in
    let _h_instance = FStar.Classical.Sugar.forall_elim n h_session in
    assert (match ma_get_participant_session_state (s2p_state s_p') participant session with
      | Some pss ->
        nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
      | None -> True)
  in
  introduce forall (participant: participant_id) (session: session_id) (n: nonce).
    (match ma_get_participant_session_state (s2p_state s_p') participant session with
    | Some pss ->
      nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
    | None -> True)
  with impl_stored_helper participant session n;
  assert (ma_impl_stored_nonces_are_used s_p') ;
  assert (ma_inputs_nonces_are_used s_p'.internal.used_nonces s_p'.inputs);
  assert (ma_knowledge_nonces_are_used s_p'.internal.used_nonces s_p'.know);
  assert (ma_impl_used_nonces_invariant s_p');
  assert (ma_inputs_are_derivable s_p');
  assert (ma_same_knowledge s_p' s_q' /\
     ma_same_key_directory key_directory s_p' s_q' /\
     ma_key_directory_injective key_directory /\
     ma_same_inputs s_p' s_q' /\
     ma_same_used_nonces s_p' s_q' /\
     ma_impl_used_nonces_invariant s_p' /\
     ma_impl_stored_nonces_are_used s_p' /\
     ma_inputs_are_derivable s_p')

private
let ma_input_step_impl_preserves_session_correspondence_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs })
      (ensures
        ma_initiator_session_correspondence s_p' s_q' /\
        ma_responder_session_correspondence s_p' s_q') =
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
    assert (ma_initiator_session_state (s2p_state s_p') query_initiator query_session ==
       ma_initiator_session_state (s2p_state s_p) query_initiator query_session /\
       ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session ==
       ma_sim_initiator_session_state (s2p_state s_q) query_initiator query_session) ;
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
    assert (ma_responder_session_state (s2p_state s_p') query_responder query_session ==
       ma_responder_session_state (s2p_state s_p) query_responder query_session /\
       ma_sim_responder_session_state (s2p_state s_q') query_responder query_session ==
       ma_sim_responder_session_state (s2p_state s_q) query_responder query_session) ;
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
     ma_responder_session_correspondence s_p' s_q')

private
let ma_input_step_impl_preserves_ideal_bookkeeping_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs })
      (ensures
        ma_ideal_request_matches_sim_session s_q' /\
        ma_initiator_output_token_matches_impl_pending_output s_p' s_q') =
  // `ma_sim_session_matches_ideal_request` and `ma_output_token_matches_sim_phase`
  // are conjuncts of `ma_ideal_system_inv s_q'` (preserved by
  // `ma_ideal_system_inv_preserved`), so only the two non-invariant relational
  // clauses are established here.
  let ideal_request_matches_session_helper
      (query_session: session_id)
      (party peer: participant_id)
      (r: role)
      : Lemma
      (ensures (
        Set.mem { party = party; peer = peer; role = r }
          (ma_session_requests (s2p_state s_q') query_session) ==>
        (match ma_get_sim_participant_session_state (s2p_state s_q') party query_session with
        | Some (SimInitiatorSession initiator_state) ->
          r == Initiator /\
          initiator_state.initiator == party /\
          initiator_state.responder == peer
        | Some (SimResponderSession responder_state) ->
          r == Responder /\
          responder_state.responder == party /\
          responder_state.initiator == peer
        | None -> False))) =
    assert (Set.mem { party = party; peer = peer; role = r }
        (ma_session_requests (s2p_state s_q) query_session) ==>
      (match ma_get_sim_participant_session_state (s2p_state s_q) party query_session with
      | Some (SimInitiatorSession initiator_state) ->
        r == Initiator /\
        initiator_state.initiator == party /\
        initiator_state.responder == peer
      | Some (SimResponderSession responder_state) ->
        r == Responder /\
        responder_state.responder == party /\
        responder_state.initiator == peer
      | None -> False)) ;
    assert (ma_get_sim_participant_session_state (s2p_state s_q') party query_session ==
       ma_get_sim_participant_session_state (s2p_state s_q) party query_session /\
       ma_session_requests (s2p_state s_q') query_session ==
       ma_session_requests (s2p_state s_q) query_session) ;
    assert (Set.mem { party = party; peer = peer; role = r }
        (ma_session_requests (s2p_state s_q') query_session) ==>
      (match ma_get_sim_participant_session_state (s2p_state s_q') party query_session with
      | Some (SimInitiatorSession initiator_state) ->
        r == Initiator /\
        initiator_state.initiator == party /\
        initiator_state.responder == peer
      | Some (SimResponderSession responder_state) ->
        r == Responder /\
        responder_state.responder == party /\
        responder_state.initiator == peer
      | None -> False))
  in
  introduce forall (query_session: session_id) (party peer: participant_id) (r: role).
    Set.mem { party = party; peer = peer; role = r }
      (ma_session_requests (s2p_state s_q') query_session) ==>
    (match ma_get_sim_participant_session_state (s2p_state s_q') party query_session with
    | Some (SimInitiatorSession initiator_state) ->
      r == Initiator /\
      initiator_state.initiator == party /\
      initiator_state.responder == peer
    | Some (SimResponderSession responder_state) ->
      r == Responder /\
      responder_state.responder == party /\
      responder_state.initiator == peer
    | None -> False)
  with ideal_request_matches_session_helper query_session party peer r;
  assert (ma_ideal_request_matches_sim_session s_q') ;
  let initiator_output_token_helper (query_session: session_id) (initiator: participant_id)
      : Lemma
      (ensures (
        match ma_initiator_session_state (s2p_state s_p') initiator query_session with
        | Some initiator_state ->
          (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
          (initiator_state.ack_sent ==>
            (Set.mem (ma_output_term query_session initiator) s_q'.internal.sim_to_ideal_channel <==>
             not initiator_state.output_sent))
        | None -> True)) =
    assert (match ma_initiator_session_state (s2p_state s_p) initiator query_session with
      | Some initiator_state ->
        (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
        (initiator_state.ack_sent ==>
          (Set.mem (ma_output_term query_session initiator) s_q.internal.sim_to_ideal_channel <==>
           not initiator_state.output_sent))
      | None -> True) ;
    assert (ma_initiator_session_state (s2p_state s_p') initiator query_session ==
       ma_initiator_session_state (s2p_state s_p) initiator query_session /\
       s_q'.internal.sim_to_ideal_channel == s_q.internal.sim_to_ideal_channel) ;
    assert (match ma_initiator_session_state (s2p_state s_p') initiator query_session with
      | Some initiator_state ->
        (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
        (initiator_state.ack_sent ==>
          (Set.mem (ma_output_term query_session initiator) s_q'.internal.sim_to_ideal_channel <==>
           not initiator_state.output_sent))
      | None -> True)
  in
  FStar.Classical.forall_intro_2 initiator_output_token_helper;
  assert (ma_initiator_output_token_matches_impl_pending_output s_p' s_q') ;
  assert (ma_ideal_request_matches_sim_session s_q' /\
     ma_initiator_output_token_matches_impl_pending_output s_p' s_q')

private
let ma_input_step_impl_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs })
      (ensures
        ma_private_keys_not_derivable corrupt key_directory s_p') =
  // The ideal-side secrecy clauses (`ma_private_keys_not_derivable s_q'`,
  // `ma_valid_initiator_nonces_not_derivable s_q'`,
  // `ma_valid_responder_nonces_not_derivable s_q'`) are consequences of
  // `ma_ideal_system_inv s_q'` (preserved by `ma_ideal_system_inv_preserved`),
  // so only the implementation-side clause is established here.
  let impl_private_key_helper (participant: participant_id) (k: priv_key) (d: adv.derivation)
      : Lemma
      (ensures
        PartialMap.sel key_directory participant == Some k /\
        not (Set.mem participant corrupt) ==>
        not (adv.derive d s_p'.know = Some (PrivKey k))) =
    assert (PartialMap.sel key_directory participant == Some k /\
       not (Set.mem participant corrupt) ==>
       not (adv.derive d s_p.know = Some (PrivKey k))) ;
    assert (PartialMap.sel key_directory participant == Some k /\
       not (Set.mem participant corrupt) ==>
       not (adv.derive d s_p'.know = Some (PrivKey k)))
  in
  introduce forall (participant: participant_id) (k: priv_key) (d: adv.derivation).
    PartialMap.sel key_directory participant == Some k /\
    not (Set.mem participant corrupt) ==>
    not (adv.derive d s_p'.know = Some (PrivKey k))
  with impl_private_key_helper participant k d;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p')


private
let ma_input_step_impl_preserves_initiator_ack_enabled_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs })
      (ensures ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q') =
  ma_input_step_impl_preserves_structural_and_input_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  let initiator_ack_enabled_helper
      (query_session: session_id)
      (query_initiator query_responder: participant_id)
      (query_responder_nonce: nonce)
      (query_initiator_key: priv_key)
      (query_responder_pubkey: term {PubKey? query_responder_pubkey})
      : Lemma
      (ensures
        ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
          query_session query_initiator query_responder query_responder_nonce
          query_initiator_key query_responder_pubkey) =
    let h_initiator_corr : squash (ma_initiator_session_correspondence s_p' s_q') = () in
    let h_initiator_corr_session = FStar.Classical.Sugar.forall_elim query_session h_initiator_corr in
    let _h_initiator_corr_instance = FStar.Classical.Sugar.forall_elim query_initiator h_initiator_corr_session in
    assert (ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
        query_session query_initiator query_responder query_responder_nonce
        query_initiator_key query_responder_pubkey)
  in
  introduce forall (query_session: session_id)
                    (query_initiator query_responder: participant_id)
                    (query_responder_nonce: nonce)
                    (query_initiator_key: priv_key)
                    (query_responder_pubkey: term {PubKey? query_responder_pubkey}).
    ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
      query_session query_initiator query_responder query_responder_nonce
      query_initiator_key query_responder_pubkey
  with initiator_ack_enabled_helper query_session query_initiator query_responder
    query_responder_nonce query_initiator_key query_responder_pubkey;
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q')


#push-options "--split_queries no --z3rlimit 30"
private
let ma_input_step_impl_preserves_responder_reply_enabled_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs } /\
        ma_ideal_system_inv corrupt key_directory s_q')
      (ensures ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q') =
  ma_input_step_impl_preserves_structural_and_input_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  // `ma_sim_session_matches_ideal_request s_q'` is recovered from the preserved
  // ideal invariant rather than from a dedicated input-step helper.
  ma_ideal_system_inv_elim corrupt key_directory s_q';
  let responder_reply_enabled_helper
      (query_session: session_id)
      (query_responder query_initiator: participant_id)
      (query_initiator_nonce query_responder_nonce: nonce)
      (query_responder_key: priv_key)
      (query_initiator_pubkey: term {PubKey? query_initiator_pubkey})
      : Lemma
      (ensures
        ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          query_session query_responder query_initiator query_initiator_nonce
          query_responder_nonce query_responder_key query_initiator_pubkey) =
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
        query_session query_responder query_initiator query_initiator_nonce
        query_responder_nonce query_responder_key query_initiator_pubkey) ;
    let auth_input =
      ma_auth_input_term query_session query_responder query_initiator Responder in
    let message1_input =
      ma_nsl_message1_network_term query_session query_initiator query_responder
        query_initiator_nonce (PubKey query_responder_key) in
    let ideal_mid =
      ma_ideal_initiate_state (s2p_state s_q') query_session query_responder
        query_initiator Responder in
    assert (auth_input <> message1_input) ;
    Bag.mem_remove message1_input auth_input s_q'.inputs;
    assert (Bag.mem message1_input ideal_mid.inputs == Bag.mem message1_input s_q'.inputs) ;
    ma_ideal_initiate_state_preserves_key_directory
      (s2p_state s_q') query_session query_responder query_initiator Responder;
    ma_ideal_initiate_state_preserves_used_nonces
      (s2p_state s_q') query_session query_responder query_initiator Responder;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q') query_session query_responder query_initiator Responder
      query_responder query_session;
    ma_set_mem_add
      (ma_authenticating_term query_session query_responder query_initiator Responder)
      (ma_authenticating_term query_session query_responder query_initiator Responder)
      (s2p_state s_q').internal.ideal_to_sim_channel;
    assert (Set.mem (ma_authenticating_term query_session query_responder query_initiator Responder)
        ideal_mid.internal.ideal_to_sim_channel) ;
    let h_initiator_corr : squash (ma_initiator_session_correspondence s_p' s_q') = () in
    let h_initiator_corr_session = FStar.Classical.Sugar.forall_elim query_session h_initiator_corr in
    let _h_initiator_corr_instance = FStar.Classical.Sugar.forall_elim query_responder h_initiator_corr_session in
    let h_responder_corr : squash (ma_responder_session_correspondence s_p' s_q') = () in
    let h_responder_corr_session = FStar.Classical.Sugar.forall_elim query_session h_responder_corr in
    let _h_responder_corr_instance = FStar.Classical.Sugar.forall_elim query_responder h_responder_corr_session in
    let h_request_matches : squash (ma_ideal_request_matches_sim_session s_q') = () in
    let h_request_matches_session = FStar.Classical.Sugar.forall_elim query_session h_request_matches in
    let h_request_matches_party = FStar.Classical.Sugar.forall_elim query_responder h_request_matches_session in
    let h_request_matches_peer = FStar.Classical.Sugar.forall_elim query_initiator h_request_matches_party in
    let _h_request_matches_instance = FStar.Classical.Sugar.forall_elim Responder h_request_matches_peer in
    let h_sim_matches : squash (ma_sim_session_matches_ideal_request s_q') = () in
    let h_sim_matches_session = FStar.Classical.Sugar.forall_elim query_session h_sim_matches in
    let _h_sim_matches_instance = FStar.Classical.Sugar.forall_elim query_responder h_sim_matches_session in
    assert (Bag.mem auth_input s_p'.inputs == Bag.mem auth_input s_q'.inputs /\
       Bag.mem message1_input s_p'.inputs == Bag.mem message1_input s_q'.inputs) ;
    assert (PartialMap.sel (s2p_state s_p').internal.key_directory query_responder ==
        PartialMap.sel (s2p_state s_q').internal.key_directory query_responder /\
       PartialMap.sel (s2p_state s_p').internal.key_directory query_initiator ==
        PartialMap.sel (s2p_state s_q').internal.key_directory query_initiator /\
       s_p'.internal.used_nonces == s_q'.internal.used_nonces) ;
    FStar.Tactics.Effect.assert_by_tactic
      ((not (PartialMap.contains
          (ma_participant_sessions (s2p_state s_p') query_responder)
          query_session))
       <==>
       (not (PartialMap.contains
          (ma_sim_participant_sessions (s2p_state s_q') query_responder)
          query_session)))
      (fun _ ->
          (let open FStar.Tactics.V2 in
            norm [delta_only [`%ma_initiator_session_correspondence;
                              `%ma_responder_session_correspondence;
                              `%ma_initiator_session_state;
                              `%ma_responder_session_state;
                              `%ma_sim_initiator_session_state;
                              `%ma_sim_responder_session_state;
                              `%ma_get_participant_session_state;
                              `%ma_get_sim_participant_session_state;
                              `%FStar.PartialMap.contains];
                  zeta; iota];
            smt ())) ;
    FStar.Tactics.Effect.assert_by_tactic
      (((forall (stored_request: auth_request).
          Set.mem stored_request (ma_session_requests (s2p_state s_q') query_session) ==>
          stored_request.party <> query_responder))
       <==>
       (not (PartialMap.contains
          (ma_sim_participant_sessions (s2p_state s_q') query_responder)
          query_session)))
      (fun _ ->
          (let open FStar.Tactics.V2 in
            norm [delta_only [`%ma_sim_session_matches_ideal_request;
                              `%ma_ideal_request_matches_sim_session;
                              `%ma_sim_initiator_session_state;
                              `%ma_sim_responder_session_state;
                              `%ma_get_sim_participant_session_state;
                              `%FStar.PartialMap.contains];
                  zeta; iota];
            smt ())) ;
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
        query_session query_responder query_initiator query_initiator_nonce
        query_responder_nonce query_responder_key query_initiator_pubkey)
  in
  introduce forall (query_session: session_id)
                    (query_responder query_initiator: participant_id)
                    (query_initiator_nonce query_responder_nonce: nonce)
                    (query_responder_key: priv_key)
                    (query_initiator_pubkey: term {PubKey? query_initiator_pubkey}).
    ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
      query_session query_responder query_initiator query_initiator_nonce
      query_responder_nonce query_responder_key query_initiator_pubkey
  with responder_reply_enabled_helper query_session query_responder query_initiator
    query_initiator_nonce query_responder_nonce query_responder_key query_initiator_pubkey;
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q')
#pop-options


private
let ma_input_step_impl_preserves_initiator_output_enabled_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs })
      (ensures ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q') =
  ma_input_step_impl_preserves_structural_and_input_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  let initiator_output_enabled_helper
      (query_session: session_id)
      (query_initiator query_responder: participant_id)
      : Lemma
      (ensures
        ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          query_session query_initiator query_responder) =
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q
        query_session query_initiator query_responder) ;
    assert (ma_initiator_session_state (s2p_state s_p') query_initiator query_session ==
       ma_initiator_session_state (s2p_state s_p) query_initiator query_session /\
       ma_session_requests (s2p_state s_q') query_session ==
       ma_session_requests (s2p_state s_q) query_session /\
       s_q'.internal.sim_to_ideal_channel == s_q.internal.sim_to_ideal_channel) ;
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
        query_session query_initiator query_responder)
  in
  introduce forall (query_session: session_id)
                    (query_initiator query_responder: participant_id).
    ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
      query_session query_initiator query_responder
  with initiator_output_enabled_helper query_session query_initiator query_responder;
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q')


private
let ma_input_step_impl_preserves_initiator_start_enabled_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs } /\
        ma_ideal_system_inv corrupt key_directory s_q')
      (ensures ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q') =
  ma_input_step_impl_preserves_structural_and_input_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  // `ma_sim_session_matches_ideal_request s_q'` is recovered from the preserved
  // ideal invariant rather than from a dedicated input-step helper.
  ma_ideal_system_inv_elim corrupt key_directory s_q';
  let initiator_start_enabled_helper
      (query_session: session_id)
      (query_initiator query_responder: participant_id)
      (query_initiator_nonce: nonce)
      (query_responder_pubkey: term {PubKey? query_responder_pubkey})
      : Lemma
      (ensures
        ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          query_session query_initiator query_responder query_initiator_nonce
          query_responder_pubkey) =
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
        query_session query_initiator query_responder query_initiator_nonce
        query_responder_pubkey) ;
    let auth_input =
      ma_auth_input_term query_session query_initiator query_responder Initiator in
    let ideal_mid =
      ma_ideal_initiate_state (s2p_state s_q') query_session query_initiator
        query_responder Initiator in
    ma_ideal_initiate_state_preserves_key_directory
      (s2p_state s_q') query_session query_initiator query_responder Initiator;
    ma_ideal_initiate_state_preserves_used_nonces
      (s2p_state s_q') query_session query_initiator query_responder Initiator;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q') query_session query_initiator query_responder Initiator
      query_initiator query_session;
    ma_set_mem_add
      (ma_authenticating_term query_session query_initiator query_responder Initiator)
      (ma_authenticating_term query_session query_initiator query_responder Initiator)
      (s2p_state s_q').internal.ideal_to_sim_channel;
    assert (Set.mem (ma_authenticating_term query_session query_initiator query_responder Initiator)
        ideal_mid.internal.ideal_to_sim_channel) ;
    let h_initiator_corr : squash (ma_initiator_session_correspondence s_p' s_q') = () in
    let h_initiator_corr_session = FStar.Classical.Sugar.forall_elim query_session h_initiator_corr in
    let _h_initiator_corr_instance = FStar.Classical.Sugar.forall_elim query_initiator h_initiator_corr_session in
    let h_responder_corr : squash (ma_responder_session_correspondence s_p' s_q') = () in
    let h_responder_corr_session = FStar.Classical.Sugar.forall_elim query_session h_responder_corr in
    let _h_responder_corr_instance = FStar.Classical.Sugar.forall_elim query_initiator h_responder_corr_session in
    let h_request_matches : squash (ma_ideal_request_matches_sim_session s_q') = () in
    let h_request_matches_session = FStar.Classical.Sugar.forall_elim query_session h_request_matches in
    let h_request_matches_party = FStar.Classical.Sugar.forall_elim query_initiator h_request_matches_session in
    let h_request_matches_peer = FStar.Classical.Sugar.forall_elim query_responder h_request_matches_party in
    let _h_request_matches_instance = FStar.Classical.Sugar.forall_elim Initiator h_request_matches_peer in
    let h_sim_matches : squash (ma_sim_session_matches_ideal_request s_q') = () in
    let h_sim_matches_session = FStar.Classical.Sugar.forall_elim query_session h_sim_matches in
    let _h_sim_matches_instance = FStar.Classical.Sugar.forall_elim query_initiator h_sim_matches_session in
    assert (Bag.mem auth_input s_p'.inputs == Bag.mem auth_input s_q'.inputs) ;
    assert (PartialMap.sel (s2p_state s_p').internal.key_directory query_responder ==
        PartialMap.sel (s2p_state s_q').internal.key_directory query_responder /\
       s_p'.internal.used_nonces == s_q'.internal.used_nonces) ;
    FStar.Tactics.Effect.assert_by_tactic
      ((not (PartialMap.contains
          (ma_participant_sessions (s2p_state s_p') query_initiator)
          query_session))
       <==>
       (not (PartialMap.contains
          (ma_sim_participant_sessions (s2p_state s_q') query_initiator)
          query_session)))
      (fun _ ->
          (let open FStar.Tactics.V2 in
            norm [delta_only [`%ma_initiator_session_correspondence;
                              `%ma_responder_session_correspondence;
                              `%ma_initiator_session_state;
                              `%ma_responder_session_state;
                              `%ma_sim_initiator_session_state;
                              `%ma_sim_responder_session_state;
                              `%ma_get_participant_session_state;
                              `%ma_get_sim_participant_session_state;
                              `%FStar.PartialMap.contains];
                  zeta; iota];
            smt ())) ;
    FStar.Tactics.Effect.assert_by_tactic
      (((forall (stored_request: auth_request).
          Set.mem stored_request (ma_session_requests (s2p_state s_q') query_session) ==>
          stored_request.party <> query_initiator))
       <==>
       (not (PartialMap.contains
          (ma_sim_participant_sessions (s2p_state s_q') query_initiator)
          query_session)))
      (fun _ ->
          (let open FStar.Tactics.V2 in
            norm [delta_only [`%ma_sim_session_matches_ideal_request;
                              `%ma_ideal_request_matches_sim_session;
                              `%ma_sim_initiator_session_state;
                              `%ma_sim_responder_session_state;
                              `%ma_get_sim_participant_session_state;
                              `%FStar.PartialMap.contains];
                  zeta; iota];
            smt ())) ;
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
        query_session query_initiator query_responder query_initiator_nonce
        query_responder_pubkey)
  in
  introduce forall (query_session: session_id)
                    (query_initiator query_responder: participant_id)
                    (query_initiator_nonce: nonce)
                    (query_responder_pubkey: term {PubKey? query_responder_pubkey}).
    ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
      query_session query_initiator query_responder query_initiator_nonce
      query_responder_pubkey
  with initiator_start_enabled_helper query_session query_initiator query_responder
    query_initiator_nonce query_responder_pubkey;
  assert (ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q')


private
let ma_input_step_impl_preserves_responder_output_enabled_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs } /\
        ma_ideal_system_inv corrupt key_directory s_q')
      (ensures ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q') =
  ma_input_step_impl_preserves_structural_and_input_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  // The input-derivability, derivable-Message3 authentication, and
  // session-matches-request facts used below are conjuncts of the preserved
  // ideal invariant `ma_ideal_system_inv s_q'`.
  ma_ideal_system_inv_elim corrupt key_directory s_q';
  let responder_output_enabled_helper
      (query_session: session_id)
      (query_responder query_initiator: participant_id)
      (query_responder_key: priv_key)
      : Lemma
      (ensures
        ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          query_session query_responder query_initiator query_responder_key) =
    let impl_enabled =
      ma_nsl_responder_output_enabled (s2p_state s_p')
        query_session query_responder query_initiator query_responder_key in
    let ideal_enabled =
      ma_sim_receive_message3_enabled (s2p_state s_q')
        query_session query_responder query_initiator query_responder_key /\
      ma_ideal_deliver_enabled
        (ma_sim_receive_message3_state (s2p_state s_q')
          query_session query_responder query_initiator query_responder_key)
        query_session query_responder query_initiator Responder in
    let prove_ideal_from_impl ()
        : Lemma (requires impl_enabled) (ensures ideal_enabled) =
      assert (ma_sim_receive_message3_enabled (s2p_state s_q')
          query_session query_responder query_initiator query_responder_key) ;
      assert (Some? (ma_sim_responder_session_state (s2p_state s_q') query_responder query_session));
      let responder_state = Some?.v (ma_sim_responder_session_state (s2p_state s_q') query_responder query_session) in
      let message3_input = ma_nsl_message3_network_term
        query_session query_initiator query_responder responder_state.responder_nonce
        (PubKey query_responder_key) in
      assert (responder_state.responder == query_responder /\
              responder_state.initiator == query_initiator);
      assert (matches_responder_state s_q' query_session query_responder query_initiator responder_state.responder_nonce);
      assert (PartialMap.sel s_q'.internal.key_directory query_responder == Some query_responder_key);
      assert (Bag.mem message3_input s_q'.inputs);
      let h_inputs : squash (ma_ideal_inputs_derivable s_q') = () in
      let _h_input_instance = FStar.Classical.Sugar.forall_elim message3_input h_inputs in
      assert (derivable s_q'.know message3_input);
      assert (adv.derivable s_q'.know message3_input);
      let witness: adv.derivation -> prop =
        (fun d -> adv.derive d s_q'.know = Some message3_input) in
      let message3_derivation =
        FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation witness in
      assert (adv.derive message3_derivation s_q'.know = Some message3_input) ;
      ma_sim_receive_message3_state_session_requests_eq
        (s2p_state s_q') query_session query_responder query_initiator query_responder_key query_session;
      let h_sim_matches : squash (ma_sim_session_matches_ideal_request s_q') = () in
      // The responder's own request follows from the (existing) responder session,
      // independently of corruption.
      let h_sim_matches_responder_session = FStar.Classical.Sugar.forall_elim query_session h_sim_matches in
      let _h_sim_matches_responder = FStar.Classical.Sugar.forall_elim query_responder h_sim_matches_responder_session in
      assert (Set.mem { party = query_responder; peer = query_initiator; role = Responder }
          (ma_session_requests (s2p_state s_q') query_session)) ;
      // The deliver disjunct for (query_responder, query_initiator, Responder) — the
      // `at_least_one_corrupt` clause OR the complementary Initiator request — holds
      // either way: with both parties honest, Message3 provenance recovers the matching
      // initiator session/request; with at least one corrupt, the corruption disjunct
      // applies (and `ma_message3_provenance_matches_initiator` is not available).
      assert (s_q'.internal.corrupt == corrupt) ;
      if not (Set.mem query_initiator corrupt) && not (Set.mem query_responder corrupt) then
        (ma_message3_provenance_matches_initiator corrupt key_directory s_q' query_session
           query_responder query_initiator responder_state.responder_nonce
           query_responder_key message3_derivation;
         assert (matches_initiator_peer_state s_q' query_session query_initiator query_responder) ;
         let h_sim_matches_initiator_session = FStar.Classical.Sugar.forall_elim query_session h_sim_matches in
         let _h_sim_matches_initiator = FStar.Classical.Sugar.forall_elim query_initiator h_sim_matches_initiator_session in
         assert (Set.mem { party = query_initiator; peer = query_responder; role = Initiator }
            (ma_session_requests (s2p_state s_q') query_session)) ;
         assert (Set.mem query_initiator s_q'.internal.corrupt \/ Set.mem query_responder s_q'.internal.corrupt \/
           Set.mem { party = query_initiator; peer = query_responder; role = Initiator }
            (ma_session_requests (s2p_state s_q') query_session)))
      else
        assert (Set.mem query_initiator s_q'.internal.corrupt \/ Set.mem query_responder s_q'.internal.corrupt \/
          Set.mem { party = query_initiator; peer = query_responder; role = Initiator }
           (ma_session_requests (s2p_state s_q') query_session)) ;
      assert (Set.mem (ma_output_term query_session query_responder)
          (ma_sim_receive_message3_state (s2p_state s_q')
            query_session query_responder query_initiator query_responder_key).internal.sim_to_ideal_channel) ;
      assert (ma_ideal_deliver_enabled
          (ma_sim_receive_message3_state (s2p_state s_q')
            query_session query_responder query_initiator query_responder_key)
          query_session query_responder query_initiator Responder) ;
      assert (ideal_enabled)
    in
    let prove_impl_from_ideal ()
        : Lemma (requires ideal_enabled) (ensures impl_enabled) =
      // `ideal_enabled` exposes the ideal sim responder session, its key, and the
      // Message3 input.  Mirror `prove_ideal_from_impl` in reverse: instantiate
      // the impl<->ideal responder-session correspondence pointwise to transport
      // the matching session (its nonce and phase) to the impl side, then surface
      // the input/key facts.
      assert (Some? (ma_sim_responder_session_state (s2p_state s_q') query_responder query_session));
      let sim_state = Some?.v (ma_sim_responder_session_state (s2p_state s_q') query_responder query_session) in
      let h_responder_corr : squash (ma_responder_session_correspondence s_p' s_q') = () in
      let h_responder_corr_session = FStar.Classical.Sugar.forall_elim query_session h_responder_corr in
      let _h_responder_corr_instance = FStar.Classical.Sugar.forall_elim query_responder h_responder_corr_session in
      assert (Some? (ma_responder_session_state (s2p_state s_p') query_responder query_session));
      let responder_state =
        Some?.v (ma_responder_session_state (s2p_state s_p') query_responder query_session) in
      assert (responder_state.responder == query_responder /\
              responder_state.initiator == query_initiator /\
              not responder_state.output_sent /\
              responder_state.responder_nonce == sim_state.responder_nonce);
      let message3_input = ma_nsl_message3_network_term
        query_session query_initiator query_responder sim_state.responder_nonce
        (PubKey query_responder_key) in
      assert (Bag.mem message3_input s_q'.inputs);
      assert (Bag.mem message3_input s_p'.inputs);
      assert (PartialMap.sel (s2p_state s_p').internal.key_directory query_responder
                == Some query_responder_key);
      assert (impl_enabled)
    in
    let _h_impl_to_ideal
      : squash (impl_enabled ==> ideal_enabled)
      = FStar.Classical.Sugar.implies_intro
        impl_enabled
        (fun _ -> ideal_enabled)
        (fun h_impl_enabled ->
          prove_ideal_from_impl ();
          (() <: squash ideal_enabled)) in
    let _h_ideal_to_impl
      : squash (ideal_enabled ==> impl_enabled)
      = FStar.Classical.Sugar.implies_intro
        ideal_enabled
        (fun _ -> impl_enabled)
        (fun h_ideal_enabled ->
          prove_impl_from_ideal ();
          (() <: squash impl_enabled)) in
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
        query_session query_responder query_initiator query_responder_key)
  in
  introduce forall (query_session: session_id)
                    (query_responder query_initiator: participant_id)
                    (query_responder_key: priv_key).
    ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
      query_session query_responder query_initiator query_responder_key
  with responder_output_enabled_helper query_session query_responder query_initiator
    query_responder_key;
  assert (ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')

private
let ma_input_step_impl_preserves_enabledness_iffs
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs } /\
        ma_ideal_system_inv corrupt key_directory s_q')
      (ensures
        ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q') =
  ma_input_step_impl_preserves_initiator_ack_enabled_iff
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_responder_reply_enabled_iff
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_initiator_output_enabled_iff
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_initiator_start_enabled_iff
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_responder_output_enabled_iff
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q'


private
let ma_input_step_impl_preserves_relation_after_insert
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (derivation0: derivation)
      (derived_input: term)
      (s_p': impl_system_state)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        derive derivation0 s_p.know = Some derived_input /\
        s_p'.inputs == Bag.insert derived_input s_p.inputs /\
        s_p'.know == s_p.know /\
        s_p'.internal == s_p.internal /\
        s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs } /\
        // The ideal-side invariant at the post-state; the callers (which carry
        // `know0` and the system transition) discharge it via
        // `ma_ideal_system_inv_preserved`.
        ma_ideal_system_inv corrupt key_directory s_q')
      (ensures
        ma_bisim_relation corrupt key_directory s_p' s_q') =
  ma_input_step_impl_preserves_structural_and_input_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_secrecy_clauses
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  ma_input_step_impl_preserves_enabledness_iffs
    corrupt key_directory s_p s_q derivation0 derived_input s_p' s_q';
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')

let ma_obs_bisim_input_step_impl
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (d: adv.derivation)
      (s_p': impl_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        (ma_impl_system corrupt key_directory know0).transitions s_p (TestedSystem.Input d) s_p')
      (ensures
        exists s_q'.
          (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Input d) s_q' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  assert (Some? (adv.derive d s_p.know));
  let derived_input = Some?.v (adv.derive d s_p.know) in
  assert (adv.derive d s_p.know == Some derived_input);
  assert (s_p'.inputs == Bag.insert derived_input s_p.inputs);
  assert (s_p'.know == s_p.know);
  assert (s_p'.internal == s_p.internal);
  assert (s_p.know == s_q.know)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation; `%ma_same_knowledge]; zeta; iota];
        smt ());
  assert (adv.derive d s_q.know == Some derived_input);
  let s_q': ideal_system_state = {
    know = s_q.know;
    inputs = Bag.insert derived_input s_q.inputs;
    internal = s_q.internal
  } in
  assert ((ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Input d) s_q');
  // `ma_ideal_system_inv_preserved` discharges the post-state ideal invariant
  // `ma_ideal_system_inv corrupt key_directory s_q'`, which is the precondition of
  // `ma_input_step_impl_preserves_relation_after_insert` (and subsumes the
  // ideal-side relation clauses).
  ma_ideal_system_inv_preserved corrupt key_directory know0 s_q s_q' (TestedSystem.Input d);
  ma_input_step_impl_preserves_relation_after_insert
    corrupt key_directory s_p s_q d derived_input s_p' s_q'

let ma_obs_bisim_input_step_ideal
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (d: adv.derivation)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Input d) s_q')
      (ensures
        exists s_p'.
          (ma_impl_system corrupt key_directory know0).transitions s_p (TestedSystem.Input d) s_p' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  assert (Some? (adv.derive d s_q.know));
  let derived_input = Some?.v (adv.derive d s_q.know) in
  assert (adv.derive d s_q.know == Some derived_input);
  assert (s_q'.inputs == Bag.insert derived_input s_q.inputs);
  assert (s_q'.know == s_q.know);
  assert (s_q'.internal == s_q.internal);
  assert (s_q' == { s_q with inputs = Bag.insert derived_input s_q.inputs });
  assert (s_p.know == s_q.know)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation; `%ma_same_knowledge]; zeta; iota];
        smt ());
  assert (adv.derive d s_p.know == Some derived_input);
  let s_p': impl_system_state = {
    know = s_p.know;
    inputs = Bag.insert derived_input s_p.inputs;
    internal = s_p.internal
  } in
  assert ((ma_impl_system corrupt key_directory know0).transitions s_p (TestedSystem.Input d) s_p');
  // `ma_ideal_system_inv_preserved` discharges the post-state ideal invariant
  // `ma_ideal_system_inv corrupt key_directory s_q'`, which is the precondition of
  // `ma_input_step_impl_preserves_relation_after_insert` (and subsumes the
  // ideal-side relation clauses).
  ma_ideal_system_inv_preserved corrupt key_directory know0 s_q s_q' (TestedSystem.Input d);
  ma_input_step_impl_preserves_relation_after_insert
    corrupt key_directory s_p s_q d derived_input s_p' s_q'
