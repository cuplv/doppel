module MA.ObservationalBisimulation.Proof.SendMessage3InitiatorAck

(**
  SendMessage3 + InitiatorAck cluster extracted from
  [MA.ObservationalBisimulation.Proof].
*)

open FStar.List.Tot
open FStar.Set
open FStar.PartialMap
open FStar.Tactics.V2

open SymbolicTypes
open AencTerms
open AdversaryAenc
open StaticEquivalence
open Protocol
open TestedSystem
open TestEquivalence
open ObservationalBisimulation
open Partition
open Bag

open MA.Types
open MA.Adversary
open MA.NSL
open MA.Ideal
open MA.TestedProtocols
open MA.ObservationalBisimulation.Relation
open MA.IdealInvariants
open MA.ObservationalBisimulation.Witnesses
open MA.ObservationalBisimulation.Witnesses.IdealInvariants
open MA.ObservationalBisimulation.Proof.Common
open MA.ObservationalBisimulation.Proof.MessageDerivability

#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

(**
  Implementation private-key secrecy preservation for the ideal send-message3 step
  and its implementation witness.  Message3 is a session ciphertext whose plaintext
  carries no private keys, so observing it exposes no new private key even when the
  responder (the encryption-key owner) is corrupt: the argument is the
  key-secrecy-free `derivable_from_observed_term_without_private_key_subterms`
  (+ `private_key_built_from_subterms_already_derivable`), and the clause is guarded
  by `not (Set.mem participant corrupt)` to match the now-conditional invariant.
*)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
private
let ma_ideal_send_message3_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_sim_send_message3_enabled (s2p_state s_q)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        s2p_state s_q' == ma_sim_send_message3_state (s2p_state s_q)
          session initiator responder responder_nonce initiator_key /\
        ma_sim_send_message3_protocol_transition (s2p_state s_q) session initiator responder sent_term (s2p_state s_q') /\
        s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures
        (let s_p' = ma_ideal_send_message3_impl_witness
          s_p session initiator responder responder_nonce initiator_key responder_pubkey in
        ma_private_keys_not_derivable corrupt key_directory s_p')) =
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
  let s_p' = ma_ideal_send_message3_impl_witness
    s_p session initiator responder responder_nonce initiator_key responder_pubkey in
  // unfold the impl witness so its knowledge is the single-ciphertext extension
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  let impl_private_helper (participant: participant_id) (participant_key: priv_key) (d: derivation)
      : Lemma
        (ensures
          PartialMap.sel key_directory participant == Some participant_key /\
          not (Set.mem participant corrupt) ==>
          not (derive d s_p'.know = Some (PrivKey participant_key))) =
    if PartialMap.sel key_directory participant = Some participant_key &&
       not (Set.mem participant corrupt) then
      if derive d s_p'.know = Some (PrivKey participant_key) then (
        // the impl post-state's knowledge extends `s_p.know` by exactly the sent Message3
        assert (s_p'.know == Seq.snoc s_p.know sent_term);
        derivable_from_observed_term_without_private_key_subterms
          s_p.know sent_term d (PrivKey participant_key);
        derivable_subterms_underapproximate_keys_exact_with_no_privkeys
          s_p.know sent_term;
        private_key_built_from_subterms_already_derivable
          s_p.know
          (derivable_subterms_underapproximate_keys s_p.know sent_term)
          participant_key;
        assert (derivable s_p.know (PrivKey participant_key));
        assert False)
  in
  FStar.Classical.forall_intro_3 impl_private_helper;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p')
#pop-options

(**
  Secrecy preservation for implementation initiator-ack and its ideal witness.
  This is the implementation-side wrapper around Message3.  The observed-term
  derivability facts are covered by the Message3 helper lemmas above; the ideal
  witness state uses the same simulator send-message3 update as the ideal-side
  Message3 proof.
*)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
private
let ma_impl_initiator_ack_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_ack_enabled (s2p_state s_p)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        ma_nsl_initiator_ack_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        ma_private_keys_not_derivable corrupt key_directory s_p') =
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
  let impl_private_helper (participant: participant_id) (participant_key: priv_key) (d: derivation)
      : Lemma
        (ensures
          PartialMap.sel key_directory participant == Some participant_key /\
          not (Set.mem participant corrupt) ==>
          not (derive d s_p'.know = Some (PrivKey participant_key))) =
    if PartialMap.sel key_directory participant = Some participant_key &&
       not (Set.mem participant corrupt) then
      if derive d s_p'.know = Some (PrivKey participant_key) then (
        // the impl post-state's knowledge extends `s_p.know` by exactly the sent Message3
        assert (s_p'.know == Seq.snoc s_p.know sent_term);
        derivable_from_observed_term_without_private_key_subterms
          s_p.know sent_term d (PrivKey participant_key);
        derivable_subterms_underapproximate_keys_exact_with_no_privkeys
          s_p.know sent_term;
        private_key_built_from_subterms_already_derivable
          s_p.know
          (derivable_subterms_underapproximate_keys s_p.know sent_term)
          participant_key;
        assert (derivable s_p.know (PrivKey participant_key));
        assert False)
  in
  FStar.Classical.forall_intro_3 impl_private_helper;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p')
#pop-options

private
let ma_initiator_ack_iff_from_structural_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_same_inputs s_p s_q /\
        ma_same_key_directory key_directory s_p s_q /\
        ma_initiator_session_correspondence s_p s_q)
      (ensures
        ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p s_q
          session initiator responder responder_nonce initiator_key responder_pubkey) =
  let h_corr : squash (ma_initiator_session_correspondence s_p s_q) = () in
  let h_corr_session = FStar.Classical.Sugar.forall_elim session h_corr in
  let _h_corr_instance = FStar.Classical.Sugar.forall_elim initiator h_corr_session in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder responder_nonce initiator_key responder_pubkey)

private
let ma_nsl_initiator_ack_state_preserves_impl_stored_nonces_are_used
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (post_know: knowledge term)
    : Lemma
      (requires
        ma_impl_stored_nonces_are_used s_p /\
        Some? (ma_initiator_session_state (s2p_state s_p) initiator session))
      (ensures
        ma_impl_stored_nonces_are_used
          (p2s_state
            (ma_nsl_initiator_ack_state
              (s2p_state s_p) session initiator responder responder_nonce initiator_key)
            post_know)) =
  let s_p' =
    p2s_state
      (ma_nsl_initiator_ack_state
        (s2p_state s_p) session initiator responder responder_nonce initiator_key)
      post_know
  in
  let stored_helper (query_participant: participant_id) (query_session: session_id) (n: nonce)
      : Lemma
        (ensures (
          match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
          | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
          | None -> True)) =
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key query_participant query_session;
    assert (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
       | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
       | None -> True)
  in
  FStar.Classical.forall_intro_3 stored_helper

private
let ma_sim_send_message3_state_preserves_ideal_request_matches_sim_session
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_ideal_request_matches_sim_session s_q /\
        ma_sim_send_message3_enabled (s2p_state s_q)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        s2p_state s_q' ==
          ma_sim_send_message3_state (s2p_state s_q)
            session initiator responder responder_nonce initiator_key)
      (ensures ma_ideal_request_matches_sim_session s_q') =
  assert (Some? (ma_sim_initiator_session_state (s2p_state s_q) initiator session)) ;
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
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key query_party query_session;
    if query_party = initiator && query_session = session then
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
    else
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

private
let ma_ideal_send_message3_impl_witness_preserves_impl_used_nonces_invariant
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_impl_used_nonces_invariant s_p /\
        ma_nsl_initiator_ack_enabled (s2p_state s_p)
          session initiator responder responder_nonce initiator_key responder_pubkey)
      (ensures
        ma_impl_used_nonces_invariant
          (ma_ideal_send_message3_impl_witness
            s_p session initiator responder responder_nonce initiator_key responder_pubkey))
      [SMTPat (ma_impl_used_nonces_invariant
        (ma_ideal_send_message3_impl_witness
          s_p session initiator responder responder_nonce initiator_key responder_pubkey))] =
  let sent_term = ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
  let s_p' = ma_ideal_send_message3_impl_witness
    s_p session initiator responder responder_nonce initiator_key responder_pubkey in
  let initiator_state = Some?.v (ma_initiator_session_state (s2p_state s_p) initiator session) in
  let removed_message2 = ma_nsl_message2_network_term
    session initiator responder initiator_state.initiator_nonce responder_nonce (PubKey initiator_key)
  in
  assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session));
  ma_nsl_initiator_ack_state_inputs_eq (s2p_state s_p)
    session initiator responder responder_nonce initiator_key;
  ma_ideal_send_message3_impl_witness_preserves_used_nonces
    s_p session initiator responder responder_nonce initiator_key responder_pubkey;
  ma_nsl_initiator_ack_state_preserves_impl_stored_nonces_are_used s_p
    session initiator responder responder_nonce initiator_key (Seq.snoc s_p.know sent_term);
  let input_helper (input_t: term)
      : Lemma
        (ensures
          Bag.mem input_t s_p'.inputs ==>
          ma_term_nonces_are_used s_p'.internal.used_nonces input_t) =
    Bag.mem_remove input_t removed_message2 (s2p_state s_p).inputs;
    assert (Bag.mem input_t s_p'.inputs ==>
       ma_term_nonces_are_used s_p'.internal.used_nonces input_t)
  in
  FStar.Classical.forall_intro input_helper;
  assert (Bag.mem removed_message2 (s2p_state s_p).inputs);
  ma_message3_term_nonces_are_used_from_message2_input
    s_p.internal.used_nonces (s2p_state s_p).inputs session initiator responder
    initiator_state.initiator_nonce responder_nonce initiator_key responder_pubkey;
  ma_knowledge_nonces_snoc_preserves_subset s_p.know sent_term s_p.internal.used_nonces;
  assert (ma_impl_used_nonces_invariant s_p')

private
let ma_initiator_ack_preserves_initiator_output_iff_instance_from_message2_authenticity
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_q': ideal_system_state)
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
    : Lemma
      (requires
        (let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_ack_enabled (s2p_state s_p)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        ma_sim_send_message3_enabled (s2p_state s_q)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        s2p_state s_q' == ma_sim_send_message3_state
          (s2p_state s_q) session initiator responder responder_nonce initiator_key /\
        s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures
        ma_initiator_output_equivalent_transitions_enabled_iff_instance
          (ma_ideal_send_message3_impl_witness s_p
            session initiator responder responder_nonce initiator_key responder_pubkey)
          s_q'
          quant_session quant_initiator quant_responder) =
  let s_p' = ma_ideal_send_message3_impl_witness s_p
    session initiator responder responder_nonce initiator_key responder_pubkey in
  let sent_term = ma_nsl_message3_term
    session initiator responder responder_nonce responder_pubkey in
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  assert (s2p_state s_p' == ma_nsl_initiator_ack_state
      (s2p_state s_p) session initiator responder responder_nonce initiator_key) ;
  assert (s_p'.know == Seq.snoc s_p.know sent_term) ;
  assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session)) ;
  assert (Some? (ma_sim_initiator_session_state (s2p_state s_q) initiator session)) ;
  let initiator_state = Some?.v (ma_initiator_session_state (s2p_state s_p) initiator session) in
  let removed_message2 = ma_nsl_message2_network_term
    session initiator responder initiator_state.initiator_nonce responder_nonce
    (PubKey initiator_key)
  in
  assert (Bag.mem removed_message2 (s2p_state s_q).inputs) ;
  // The consumed Message2 network term is in `s_q.inputs`, hence derivable (C2).
  let sim_initiator_state =
    Some?.v (ma_sim_initiator_session_state (s2p_state s_q) initiator session) in
  assert (matches_initiator_state s_q session initiator responder
            sim_initiator_state.initiator_nonce) ;
  assert (sim_initiator_state.initiator_nonce == initiator_state.initiator_nonce) ;
  assert (PartialMap.sel s_q.internal.key_directory initiator == Some initiator_key) ;
  assert (derivable s_q.know removed_message2) ;
  // The Initiator's own request is recorded because the simulator initiator session
  // exists (`ma_sim_session_matches_ideal_request`, from `ma_ideal_system_inv_elim`);
  // this is independent of corruption.
  assert (Set.mem { party = initiator; peer = responder; role = Initiator }
      (ma_session_requests (s2p_state s_q) session)) ;
  // The disjunct deliver-enabledness needs for (initiator, responder, Initiator) — the
  // `at_least_one_corrupt` clause OR the complementary Responder request — holds either
  // way: when both parties are honest, Message2 provenance recovers the complementary
  // responder session/request; when at least one is corrupt, the corruption disjunct
  // applies directly (and `ma_message2_provenance_matches_responder` is not available).
  assert (s_q.internal.corrupt == corrupt) ;
  if not (Set.mem initiator corrupt) && not (Set.mem responder corrupt) then
    (eliminate exists (d2: adv.derivation). adv.derive d2 s_q.know == Some removed_message2
     returns matches_responder_state s_q session responder initiator responder_nonce
     with _hd2.
       ma_message2_provenance_matches_responder corrupt key_directory s_q session initiator responder
         sim_initiator_state.initiator_nonce responder_nonce initiator_key d2 ;
     assert (match ma_sim_responder_session_state (s2p_state s_q) responder session with
       | Some responder_state ->
         responder_state.responder == responder /\
         responder_state.initiator == initiator /\
         responder_state.responder_nonce == responder_nonce
       | None -> False) ;
     assert (Set.mem { party = responder; peer = initiator; role = Responder }
         (ma_session_requests (s2p_state s_q) session)) ;
     assert (Set.mem initiator s_q.internal.corrupt \/ Set.mem responder s_q.internal.corrupt \/
       Set.mem { party = responder; peer = initiator; role = Responder }
         (ma_session_requests (s2p_state s_q) session)))
  else
    assert (Set.mem initiator s_q.internal.corrupt \/ Set.mem responder s_q.internal.corrupt \/
      Set.mem { party = responder; peer = initiator; role = Responder }
        (ma_session_requests (s2p_state s_q) session)) ;
  ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
    session initiator responder responder_nonce initiator_key quant_initiator quant_session;
  ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
    session initiator responder responder_nonce initiator_key quant_initiator quant_session;
  ma_sim_send_message3_state_session_requests_eq (s2p_state s_q)
    session initiator responder responder_nonce initiator_key quant_session;
  assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q
      quant_session quant_initiator quant_responder) ;
  if quant_session = session && quant_initiator = initiator then
    if quant_responder = responder then
      (assert (ma_nsl_initiator_output_enabled (s2p_state s_p')
          quant_session quant_initiator quant_responder) ;
      assert (ma_ideal_deliver_enabled (s2p_state s_q')
          quant_session quant_initiator quant_responder Initiator) ;
      assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder))
    else
      (assert (~(ma_nsl_initiator_output_enabled (s2p_state s_p')
          quant_session quant_initiator quant_responder)) ;
      assert (~(ma_ideal_deliver_enabled (s2p_state s_q')
          quant_session quant_initiator quant_responder Initiator)) ;
      assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder))
  else
    (assert (ma_nsl_initiator_output_enabled (s2p_state s_p')
        quant_session quant_initiator quant_responder <==>
       ma_nsl_initiator_output_enabled (s2p_state s_p)
        quant_session quant_initiator quant_responder) ;
    assert (ma_ideal_deliver_enabled (s2p_state s_q')
        quant_session quant_initiator quant_responder Initiator <==>
       ma_ideal_deliver_enabled (s2p_state s_q)
        quant_session quant_initiator quant_responder Initiator) ;
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_initiator quant_responder))

(**
  Structural-clause preservation for the ideal `send_message3` step and its
  impl witness.  Bundles the same-knowledge / same-key-directory /
  same-inputs / same-used-nonces / session-correspondence conjuncts of
  `ma_bisim_relation` into a single named helper so that the main
  `_preserves_relation` lemma's VC does not have to re-prove them inline.
*)
#push-options "--split_queries no --ifuel 2 --z3rlimit 30"
private
let ma_ideal_send_message3_preserves_structural_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_sim_send_message3_enabled (s2p_state s_q)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q)
          session initiator responder responder_nonce initiator_key /\
        s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures
        (let s_p' = ma_ideal_send_message3_impl_witness s_p
          session initiator responder responder_nonce initiator_key responder_pubkey in
        ma_same_knowledge s_p' s_q' /\
        ma_same_key_directory key_directory s_p' s_q' /\
        ma_same_inputs s_p' s_q' /\
        ma_initiator_session_correspondence s_p' s_q' /\
        ma_responder_session_correspondence s_p' s_q')) =
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
  let s_p' = ma_ideal_send_message3_impl_witness s_p
    session initiator responder responder_nonce initiator_key responder_pubkey in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q);
  assert (ma_nsl_initiator_ack_enabled (s2p_state s_p)
        session initiator responder responder_nonce initiator_key responder_pubkey);
  ma_ideal_send_message3_impl_witness_transition s_p
    session initiator responder responder_nonce initiator_key responder_pubkey;
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  assert (s2p_state s_p' == ma_nsl_initiator_ack_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key);
  assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session));
  assert (Some? (ma_sim_initiator_session_state (s2p_state s_q) initiator session));
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
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key query_initiator query_session;
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key query_initiator query_session;
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
        initiator_state.ack_sent == sim_state.ack_sent)));
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
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key query_responder query_session;
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key query_responder query_session;
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
        responder_state.output_sent == sim_state.output_forwarded)));
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
  assert (ma_same_knowledge s_p' s_q');
  assert (ma_same_key_directory key_directory s_p' s_q');
  assert (ma_same_inputs s_p' s_q');
  assert (ma_initiator_session_correspondence s_p' s_q');
  assert (ma_responder_session_correspondence s_p' s_q')
#pop-options

(**
  Preserves the `ma_initiator_output_token_matches_impl_pending_output`
  conjunct of `ma_bisim_relation` across the ideal `send_message3` step.
  Extracted from the inline body of
  `ma_obs_bisim_observable_step_ideal_send_message3_preserves_relation`
  to reduce the size of the outer VC.
*)
#push-options "--split_queries no --ifuel 2 --z3rlimit 30"
private
let ma_ideal_send_message3_preserves_initiator_output_token_matches_impl_pending_output
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
          ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_sim_send_message3_enabled (s2p_state s_q)
          session initiator responder responder_nonce initiator_key responder_pubkey /\
        (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q)
          session initiator responder responder_nonce initiator_key /\
        s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures
        ma_initiator_output_token_matches_impl_pending_output
          (ma_ideal_send_message3_impl_witness s_p
            session initiator responder responder_nonce initiator_key responder_pubkey)
          s_q') =
  let s_p' =
    ma_ideal_send_message3_impl_witness s_p
      session initiator responder responder_nonce initiator_key responder_pubkey
  in
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
    assert (ma_initiator_output_token_matches_impl_pending_output s_p s_q /\
       ma_initiator_session_correspondence s_p s_q) ;
    let h_bridge
      : squash (ma_initiator_output_token_matches_impl_pending_output s_p s_q) = () in
    let h_bridge_session = FStar.Classical.Sugar.forall_elim query_session h_bridge in
    let _h_bridge_instance = FStar.Classical.Sugar.forall_elim query_initiator h_bridge_session in
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key query_initiator query_session;
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key query_initiator query_session;
    ma_set_mem_add
      (ma_output_term query_session query_initiator)
      (ma_output_term session initiator)
      (s2p_state s_q).internal.sim_to_ideal_channel;
    if query_initiator = initiator && query_session = session then
      (assert (match ma_initiator_session_state (s2p_state s_p) initiator session with
        | Some old_initiator_state ->
          not old_initiator_state.ack_sent /\ not old_initiator_state.output_sent
        | None -> False) ;
      assert (Set.mem (ma_output_term session initiator) s_q'.internal.sim_to_ideal_channel) ;
      let old_initiator_state = Some?.v (ma_initiator_session_state (s2p_state s_p) initiator session) in
      assert (ma_initiator_session_state (s2p_state s_p') initiator session ==
         Some { old_initiator_state with ack_sent = true }) ;
      assert (match ma_initiator_session_state (s2p_state s_p') initiator session with
        | Some post_initiator_state -> post_initiator_state.ack_sent /\ not post_initiator_state.output_sent
        | None -> False) ;
      assert (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
        | Some initiator_state ->
          (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
          (initiator_state.ack_sent ==>
            (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
             not initiator_state.output_sent))
        | None -> True))
    else
      (assert (ma_output_term query_session query_initiator <> ma_output_term session initiator) ;
      assert (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
         Set.mem (ma_output_term query_session query_initiator) (s2p_state s_q).internal.sim_to_ideal_channel) ;
      assert (ma_initiator_session_state (s2p_state s_p') query_initiator query_session ==
         ma_initiator_session_state (s2p_state s_p) query_initiator query_session) ;
      assert (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
        | Some initiator_state ->
          (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
          (initiator_state.ack_sent ==>
            (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
             not initiator_state.output_sent))
        | None -> True))
  in
  let helper_session (query_session: session_id)
      : Lemma
        (ensures
          (forall (query_initiator: participant_id).
            match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
            | Some initiator_state ->
              (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
              (initiator_state.ack_sent ==>
                (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
                 not initiator_state.output_sent))
            | None -> True)) =
    introduce forall (query_initiator: participant_id).
      (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
      | Some initiator_state ->
        (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
        (initiator_state.ack_sent ==>
          (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
           not initiator_state.output_sent))
      | None -> True)
    with helper query_session query_initiator
  in
  introduce forall (query_session: session_id).
    (forall (query_initiator: participant_id).
      match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
      | Some initiator_state ->
        (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
        (initiator_state.ack_sent ==>
          (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
           not initiator_state.output_sent))
      | None -> True)
  with helper_session query_session;
  assert (ma_initiator_output_token_matches_impl_pending_output s_p' s_q')
#pop-options

#push-options "--split_queries no --ifuel 2 --z3rlimit 30"
private
let ma_ideal_send_message3_preserves_equivalent_transitions_enabled_iffs
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_sim_send_message3_enabled (s2p_state s_q)
            session initiator responder responder_nonce initiator_key responder_pubkey /\
          (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q)
            session initiator responder responder_nonce initiator_key /\
          s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures
        (let s_p' =
            ma_ideal_send_message3_impl_witness s_p
              session initiator responder responder_nonce initiator_key responder_pubkey
          in
          ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')) =
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
  in
  let s_p' =
    ma_ideal_send_message3_impl_witness s_p
      session initiator responder responder_nonce initiator_key responder_pubkey
  in
  ma_ideal_send_message3_preserves_structural_clauses corrupt key_directory s_p s_q
    session initiator responder responder_nonce initiator_key responder_pubkey s_q';
  ma_ideal_send_message3_impl_witness_transition s_p
    session
    initiator
    responder
    responder_nonce
    initiator_key
    responder_pubkey;
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q
    );
  assert (ma_nsl_initiator_ack_enabled (s2p_state s_p)
        session
        initiator
        responder
        responder_nonce
        initiator_key
        responder_pubkey);
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  assert (s2p_state s_p' == ma_nsl_initiator_ack_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key);
  assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session));
  assert (Some? (ma_sim_initiator_session_state (s2p_state s_q) initiator session));
  let post_freshness_equiv (fresh_nonce: nonce)
    : Lemma
      (ensures
        (ma_nsl_nonce_is_fresh (s2p_state s_p') fresh_nonce <==>
         ma_sim_nonce_is_fresh (s2p_state s_q') fresh_nonce))
      [SMTPat (ma_nsl_nonce_is_fresh (s2p_state s_p') fresh_nonce);
       SMTPat (ma_sim_nonce_is_fresh (s2p_state s_q') fresh_nonce)] =
    assert (ma_nsl_nonce_is_fresh (s2p_state s_p') fresh_nonce <==>
       ma_sim_nonce_is_fresh (s2p_state s_q') fresh_nonce)
  in
  let post_ack_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_responder_nonce: nonce)
      (quant_initiator_key: priv_key)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (ensures
        ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_responder_nonce
          quant_initiator_key quant_responder_pubkey)
      [SMTPat (ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_responder_nonce
          quant_initiator_key quant_responder_pubkey)] =
    ma_initiator_ack_iff_from_structural_clauses corrupt key_directory s_p' s_q'
      quant_session quant_initiator quant_responder quant_responder_nonce
      quant_initiator_key quant_responder_pubkey
  in
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
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)
      [SMTPat (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)] =
    post_freshness_equiv quant_responder_nonce;
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey);
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key quant_responder quant_session;
    let ack_initiator_state = Some?.v (ma_initiator_session_state (s2p_state s_p) initiator session) in
    let removed_message2 = ma_nsl_message2_network_term
      session initiator responder ack_initiator_state.initiator_nonce responder_nonce
      (PubKey initiator_key)
    in
    let responder_auth_input = ma_auth_input_term quant_session quant_responder quant_initiator Responder in
    let responder_message1_input = ma_nsl_message1_network_term
      quant_session quant_initiator quant_responder quant_initiator_nonce (PubKey quant_responder_key)
    in
    assert (responder_auth_input <> removed_message2);
    assert (responder_message1_input <> removed_message2);
    Bag.mem_remove responder_auth_input removed_message2 (s2p_state s_p).inputs;
    Bag.mem_remove responder_message1_input removed_message2 (s2p_state s_p).inputs;
    assert (ma_nsl_responder_reply_enabled (s2p_state s_p')
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey <==>
       ma_nsl_responder_reply_enabled (s2p_state s_p)
        quant_session quant_responder quant_initiator quant_initiator_nonce
        quant_responder_nonce quant_responder_key quant_initiator_pubkey);
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key quant_responder quant_session;
    assert ((ma_ideal_initiate_enabled (s2p_state s_q') quant_session quant_responder quant_initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q') quant_session quant_responder quant_initiator Responder)
          quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey) <==>
       (ma_ideal_initiate_enabled (s2p_state s_q) quant_session quant_responder quant_initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q) quant_session quant_responder quant_initiator Responder)
          quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey));
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
          quant_session quant_initiator quant_responder)
      [SMTPat (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder)] =
    ma_initiator_ack_preserves_initiator_output_iff_instance_from_message2_authenticity
      corrupt key_directory s_p s_q session initiator responder responder_nonce initiator_key
      responder_pubkey s_q' quant_session quant_initiator quant_responder
  in
  let post_initiator_start_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (ensures
        ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce
          quant_responder_pubkey)
      [SMTPat (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce
          quant_responder_pubkey)] =
    post_freshness_equiv quant_initiator_nonce;
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_initiator quant_responder quant_initiator_nonce
        quant_responder_pubkey);
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key quant_initiator quant_session;
    let ack_initiator_state = Some?.v (ma_initiator_session_state (s2p_state s_p) initiator session) in
    let removed_message2 = ma_nsl_message2_network_term
      session initiator responder ack_initiator_state.initiator_nonce responder_nonce
      (PubKey initiator_key)
    in
    let initiator_auth_input = ma_auth_input_term quant_session quant_initiator quant_responder Initiator in
    assert (initiator_auth_input <> removed_message2);
    Bag.mem_remove initiator_auth_input removed_message2 (s2p_state s_p).inputs;
    Bag.mem_remove initiator_auth_input removed_message2 (s2p_state s_q).inputs;
    assert (ma_nsl_initiator_start_enabled (s2p_state s_p')
        quant_session quant_initiator quant_responder quant_initiator_nonce
        quant_responder_pubkey <==>
       ma_nsl_initiator_start_enabled (s2p_state s_p)
        quant_session quant_initiator quant_responder quant_initiator_nonce
        quant_responder_pubkey);
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key quant_initiator quant_session;
    assert ((ma_ideal_initiate_enabled (s2p_state s_q') quant_session quant_initiator quant_responder Initiator /\
        ma_sim_send_message1_enabled
          (ma_ideal_initiate_state (s2p_state s_q') quant_session quant_initiator quant_responder Initiator)
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) <==>
       (ma_ideal_initiate_enabled (s2p_state s_q) quant_session quant_initiator quant_responder Initiator /\
        ma_sim_send_message1_enabled
          (ma_ideal_initiate_state (s2p_state s_q) quant_session quant_initiator quant_responder Initiator)
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey));
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_initiator quant_responder quant_initiator_nonce
        quant_responder_pubkey)
  in
  let post_responder_output_iff_instance
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (ensures
        ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_responder_key)
      [SMTPat (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_responder_key)] =
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_responder quant_initiator quant_responder_key);
    assert (ma_nsl_responder_output_enabled (s2p_state s_p)
        quant_session quant_responder quant_initiator quant_responder_key <==>
       (ma_sim_receive_message3_enabled (s2p_state s_q)
          quant_session quant_responder quant_initiator quant_responder_key /\
        ma_ideal_deliver_enabled
          (ma_sim_receive_message3_state (s2p_state s_q)
            quant_session quant_responder quant_initiator quant_responder_key)
          quant_session quant_responder quant_initiator Responder));
    ma_nsl_initiator_ack_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key quant_responder quant_session;
    let ack_initiator_state = Some?.v (ma_initiator_session_state (s2p_state s_p) initiator session) in
    let removed_message2 = ma_nsl_message2_network_term
      session initiator responder ack_initiator_state.initiator_nonce responder_nonce
      (PubKey initiator_key)
    in
    assert ((s2p_state s_p').inputs == Bag.remove removed_message2 (s2p_state s_p).inputs);
    assert ((s2p_state s_p').internal.key_directory == (s2p_state s_p).internal.key_directory);
    assert (ma_responder_session_state (s2p_state s_p') quant_responder quant_session ==
       ma_responder_session_state (s2p_state s_p) quant_responder quant_session);
    let impl_responder_output_preserved ()
        : Lemma
          (ensures
            (ma_nsl_responder_output_enabled (s2p_state s_p')
              quant_session quant_responder quant_initiator quant_responder_key <==>
             ma_nsl_responder_output_enabled (s2p_state s_p)
              quant_session quant_responder quant_initiator quant_responder_key)) =
      match ma_responder_session_state (s2p_state s_p) quant_responder quant_session with
      | Some quant_responder_state ->
        let responder_message3_input = ma_nsl_message3_network_term
          quant_session quant_initiator quant_responder quant_responder_state.responder_nonce
          (PubKey quant_responder_key)
        in
        ma_message3_network_term_not_message2_network_term
          quant_session quant_initiator quant_responder quant_responder_state.responder_nonce
          (PubKey quant_responder_key)
          session initiator responder ack_initiator_state.initiator_nonce responder_nonce
          (PubKey initiator_key);
        Bag.mem_remove responder_message3_input removed_message2 (s2p_state s_p).inputs;
        assert (Bag.mem responder_message3_input (s2p_state s_p').inputs <==>
           Bag.mem responder_message3_input (s2p_state s_p).inputs);
        assert (ma_nsl_responder_output_enabled (s2p_state s_p')
            quant_session quant_responder quant_initiator quant_responder_key <==>
           ma_nsl_responder_output_enabled (s2p_state s_p)
            quant_session quant_responder quant_initiator quant_responder_key)
      | None ->
        assert (ma_nsl_responder_output_enabled (s2p_state s_p')
            quant_session quant_responder quant_initiator quant_responder_key <==>
           ma_nsl_responder_output_enabled (s2p_state s_p)
            quant_session quant_responder quant_initiator quant_responder_key)
    in
    impl_responder_output_preserved ();
    ma_sim_send_message3_state_get_updated_sim_participant_session_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key quant_responder quant_session;
    assert ((s2p_state s_q').inputs == Bag.remove removed_message2 (s2p_state s_q).inputs);
    assert ((s2p_state s_q').internal.key_directory == (s2p_state s_q).internal.key_directory /\
       (s2p_state s_q').internal.requests == (s2p_state s_q).internal.requests);
    let ideal_responder_output_preserved ()
        : Lemma
          (ensures
            (((ma_sim_receive_message3_enabled (s2p_state s_q')
                quant_session quant_responder quant_initiator quant_responder_key /\
              ma_ideal_deliver_enabled
                (ma_sim_receive_message3_state (s2p_state s_q')
                  quant_session quant_responder quant_initiator quant_responder_key)
                quant_session quant_responder quant_initiator Responder) <==>
             (ma_sim_receive_message3_enabled (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key /\
              ma_ideal_deliver_enabled
                (ma_sim_receive_message3_state (s2p_state s_q)
                  quant_session quant_responder quant_initiator quant_responder_key)
                quant_session quant_responder quant_initiator Responder)))) =
      match ma_sim_responder_session_state (s2p_state s_q) quant_responder quant_session with
      | Some quant_responder_state ->
        let responder_message3_input = ma_nsl_message3_network_term
          quant_session quant_initiator quant_responder quant_responder_state.responder_nonce
          (PubKey quant_responder_key)
        in
        ma_message3_network_term_not_message2_network_term
          quant_session quant_initiator quant_responder quant_responder_state.responder_nonce
          (PubKey quant_responder_key)
          session initiator responder ack_initiator_state.initiator_nonce responder_nonce
          (PubKey initiator_key);
        Bag.mem_remove responder_message3_input removed_message2 (s2p_state s_q).inputs;
        assert (Bag.mem responder_message3_input (s2p_state s_q').inputs <==>
           Bag.mem responder_message3_input (s2p_state s_q).inputs);
        assert (ma_sim_receive_message3_enabled (s2p_state s_q')
            quant_session quant_responder quant_initiator quant_responder_key <==>
           ma_sim_receive_message3_enabled (s2p_state s_q)
            quant_session quant_responder quant_initiator quant_responder_key);
        assert (ma_ideal_deliver_enabled
            (ma_sim_receive_message3_state (s2p_state s_q')
              quant_session quant_responder quant_initiator quant_responder_key)
            quant_session quant_responder quant_initiator Responder <==>
           ma_ideal_deliver_enabled
            (ma_sim_receive_message3_state (s2p_state s_q)
              quant_session quant_responder quant_initiator quant_responder_key)
            quant_session quant_responder quant_initiator Responder);
        assert ((ma_sim_receive_message3_enabled (s2p_state s_q')
              quant_session quant_responder quant_initiator quant_responder_key /\
            ma_ideal_deliver_enabled
              (ma_sim_receive_message3_state (s2p_state s_q')
                quant_session quant_responder quant_initiator quant_responder_key)
              quant_session quant_responder quant_initiator Responder) <==>
           (ma_sim_receive_message3_enabled (s2p_state s_q)
              quant_session quant_responder quant_initiator quant_responder_key /\
            ma_ideal_deliver_enabled
              (ma_sim_receive_message3_state (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key)
              quant_session quant_responder quant_initiator Responder))
      | None ->
        assert ((ma_sim_receive_message3_enabled (s2p_state s_q')
              quant_session quant_responder quant_initiator quant_responder_key /\
            ma_ideal_deliver_enabled
              (ma_sim_receive_message3_state (s2p_state s_q')
                quant_session quant_responder quant_initiator quant_responder_key)
              quant_session quant_responder quant_initiator Responder) <==>
           (ma_sim_receive_message3_enabled (s2p_state s_q)
              quant_session quant_responder quant_initiator quant_responder_key /\
            ma_ideal_deliver_enabled
              (ma_sim_receive_message3_state (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key)
              quant_session quant_responder quant_initiator Responder))
    in
    ideal_responder_output_preserved ();
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_responder quant_initiator quant_responder_key)
  in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q');
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q');
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q');
  assert (ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q');
  assert (ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')

#pop-options
#push-options "--split_queries no --ifuel 2 --z3rlimit 30"
let ma_obs_bisim_observable_step_ideal_send_message3_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          // ma_sim_send_message3_protocol_transition is existentially
          // quantified over the initiator, responder, responder_nonce,
          // initiator_key, and responder_pubkey parameters that determine
          // stepped to state for the transition. We therefore explicitly
          // characterize the existentially quantified transition parameters by
          // adding the enabled and stepped to state here. When this proof is
          // used in the main bisimulation proof, these parameters and facts can
          // be pulled from the `ma_sim_send_message3_protocol_transition`
          // assumption.
          ma_sim_send_message3_enabled (s2p_state s_q)
            session
            initiator
            responder
            responder_nonce
            initiator_key
            responder_pubkey /\
          (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q) session initiator responder responder_nonce initiator_key /\
          ma_sim_send_message3_protocol_transition (s2p_state s_q)
            session
            initiator
            responder
            sent_term
            (s2p_state s_q') /\ s_q'.know == Seq.snoc s_q.know sent_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          (ma_ideal_send_message3_impl_witness s_p
              session
              initiator
              responder
              responder_nonce
              initiator_key
              responder_pubkey)
          s_q') =
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
  in
  let s_p' =
    ma_ideal_send_message3_impl_witness s_p
      session
      initiator
      responder
      responder_nonce
      initiator_key
      responder_pubkey
  in
  // Discharge the ideal-side post-state invariant. `s_q'` is characterized by
  // the precondition as the `ma_sim_send_message3` post-state (its
  // `inputs`/`internal` via `s2p_state` and its `know` via the `Seq.snoc`),
  // which are exactly the three record fields of
  // `ma_impl_initiator_ack_ideal_witness s_q ...`, so the two states are equal.
  // The witness preservation lemma then carries `ma_ideal_system_inv` across
  // the step from the pre-state invariant (a transparent conjunct of
  // `ma_bisim_relation corrupt key_directory s_p s_q`).
  ma_impl_initiator_ack_ideal_witness_preserves_inv
    corrupt key_directory s_q session initiator responder responder_nonce initiator_key responder_pubkey;
  assert (s_q' == ma_impl_initiator_ack_ideal_witness
    s_q session initiator responder responder_nonce initiator_key responder_pubkey);
  ma_ideal_send_message3_preserves_structural_clauses corrupt key_directory s_p s_q
    session initiator responder responder_nonce initiator_key responder_pubkey s_q';
  ma_ideal_send_message3_preserves_equivalent_transitions_enabled_iffs
    corrupt key_directory s_p s_q session initiator responder responder_nonce initiator_key
    responder_pubkey s_q';
  assert (ma_same_used_nonces s_p' s_q');
  ma_ideal_send_message3_impl_witness_preserves_impl_used_nonces_invariant
    s_p session initiator responder responder_nonce initiator_key responder_pubkey;
  assert ((s2p_state s_q').internal.requests == (s2p_state s_q).internal.requests) ;
  // `ma_ideal_request_matches_sim_session` is a standalone conjunct of
  // `ma_bisim_relation` (it is NOT part of `ma_ideal_system_inv`), so it must be
  // re-established explicitly across the step.
  let post_ideal_request_matches_sim_session ()
      : Lemma (ensures ma_ideal_request_matches_sim_session s_q') =
    ma_sim_send_message3_state_preserves_ideal_request_matches_sim_session
      s_q session initiator responder responder_nonce initiator_key responder_pubkey s_q'
  in
  post_ideal_request_matches_sim_session ();
  ma_ideal_send_message3_preserves_initiator_output_token_matches_impl_pending_output
    corrupt key_directory s_p s_q session initiator responder responder_nonce initiator_key
    responder_pubkey s_q';
  ma_ideal_send_message3_preserves_secrecy_clauses
    corrupt key_directory s_p s_q session initiator responder responder_nonce initiator_key responder_pubkey s_q';
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')

#pop-options

#push-options "--split_queries no --ifuel 2 --z3rlimit 30"
let ma_obs_bisim_observable_step_impl_initiator_ack_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_ack_enabled (s2p_state s_p)
            session
            initiator
            responder
            responder_nonce
            initiator_key
            responder_pubkey /\
          // Multiple states can be stepped to by the same transition, so this
          // further restriction links the new state to the given parameters.
          s2p_state s_p' == ma_nsl_initiator_ack_state (s2p_state s_p) session initiator responder responder_nonce initiator_key /\
          ma_nsl_initiator_ack_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          s_p'
          (ma_impl_initiator_ack_ideal_witness s_q
              session
              initiator
              responder
              responder_nonce
              initiator_key
              responder_pubkey)) =
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
  in
  let s_q' =
    ma_impl_initiator_ack_ideal_witness
      s_q session initiator responder responder_nonce initiator_key responder_pubkey
  in
  let s_p_w =
    ma_ideal_send_message3_impl_witness
      s_p session initiator responder responder_nonce initiator_key responder_pubkey
  in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q) ;
  assert (ma_sim_send_message3_enabled (s2p_state s_q)
      session initiator responder responder_nonce initiator_key responder_pubkey) ;
  assert (s2p_state s_q' == ma_sim_send_message3_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key) ;
  assert (ma_sim_send_message3_protocol_transition (s2p_state s_q) session initiator responder sent_term (s2p_state s_q')) ;
  assert (s_q'.know == Seq.snoc s_q.know sent_term) ;
  ma_obs_bisim_observable_step_ideal_send_message3_preserves_relation
    corrupt key_directory s_p s_q session initiator responder responder_nonce initiator_key
    responder_pubkey s_q';
  assert (s_p' == s_p_w) ;
  ma_impl_initiator_ack_preserves_secrecy_clauses
    corrupt key_directory s_p s_q session initiator responder responder_nonce initiator_key responder_pubkey s_p';
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')
#pop-options
