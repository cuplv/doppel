module MA.ObservationalBisimulation.Proof.ResponderReplyDeliverMessage2



/// ResponderReply + IdealSendMessage2 preservation cluster: per-family helpers (secrecy, state-preservation, structural clauses, enabledness iffs), the impl_responder_reply _preserves_relation main lemma, and the ideal_send_message2 _preserves_relation lemma.
///
/// Extracted from MA.ObservationalBisimulation.Proof to reduce verification
/// time of the top-level proof module.

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

open MA.ObservationalBisimulation.Proof.ResponderOutput

open MA.ObservationalBisimulation.Proof.InputStep

open MA.ObservationalBisimulation.Proof.SendMessage3InitiatorAck

#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

#push-options "--fuel 6 --ifuel 2 --z3rlimit 150"



(**
  Implementation private-key secrecy preservation for the responder-reply step.
  The ideal-side secrecy clauses (ideal private keys and valid initiator/responder
  nonces) are recovered from `ma_ideal_system_inv` at the witness post-state, so
  this helper only discharges the implementation `ma_private_keys_not_derivable`
  clause.

  Message2 is a session ciphertext `Aenc (... no private keys ...) initiator_key`.
  Even when the initiator (the encryption-key owner) is corrupt — so the key may be
  derivable — observing Message2 exposes no NEW private key, because its plaintext
  has no private-key subterms.  The derivation argument is therefore the
  key-secrecy-free `MA.Adversary.derivable_from_observed_term_without_private_key_subterms`
  (+ `private_key_built_from_subterms_already_derivable`), and the clause is guarded
  by `not (Set.mem participant corrupt)` to match the now-conditional invariant.
*)

let ma_impl_responder_reply_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures ma_private_keys_not_derivable corrupt key_directory s_p') =
  let sent_term =
    ma_nsl_message2_term session initiator responder initiator_nonce responder_nonce initiator_pubkey in
  // Observing Message2 (a session ciphertext whose plaintext carries no private
  // keys) exposes no NEW private keys, even when the initiator (= encryption key
  // owner) is corrupt: `derivable_from_observed_term_without_private_key_subterms`
  // needs no key secrecy.  Only non-corrupt directory keys are constrained; the
  // contradiction closes against the impl private-key secrecy carried in
  // `ma_bisim_relation`.
  let impl_private_helper (participant: participant_id) (participant_key: priv_key) (d: derivation)
      : Lemma
      (ensures
        PartialMap.sel key_directory participant == Some participant_key /\
        not (Set.mem participant corrupt) ==>
        not (derive d s_p'.know = Some (PrivKey participant_key))) =
    if PartialMap.sel key_directory participant = Some participant_key &&
       not (Set.mem participant corrupt)
    then
      if derive d s_p'.know = Some (PrivKey participant_key)
      then
        (assert (s_p'.know == Seq.snoc s_p.know sent_term);
          derivable_from_observed_term_without_private_key_subterms
            s_p.know sent_term d (PrivKey participant_key);
          derivable_subterms_underapproximate_keys_exact_with_no_privkeys s_p.know sent_term;
          private_key_built_from_subterms_already_derivable s_p.know
            (derivable_subterms_underapproximate_keys s_p.know sent_term) participant_key;
          assert (derivable s_p.know (PrivKey participant_key));
          assert (False))
  in
  FStar.Classical.forall_intro_3 impl_private_helper;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p')
#pop-options

let ma_nsl_responder_reply_state_preserves_impl_used_nonces_invariant
      (s_p: impl_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (post_know: knowledge term)
    : Lemma
      (requires
        ma_impl_used_nonces_invariant s_p /\
        ma_nsl_responder_reply_enabled (s2p_state s_p)
          session
          responder
          initiator
          initiator_nonce
          responder_nonce
          responder_key
          initiator_pubkey /\
        post_know ==
        Seq.snoc s_p.know
          (ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey))
      (ensures
        ma_impl_used_nonces_invariant (p2s_state (ma_nsl_responder_reply_state (s2p_state s_p)
                  session
                  responder
                  initiator
                  initiator_nonce
                  responder_nonce
                  responder_key)
              post_know)) =
  let sent_term =
    ma_nsl_message2_term session
      initiator
      responder
      initiator_nonce
      responder_nonce
      initiator_pubkey
  in
  let message1_term =
    ma_nsl_message1_network_term session initiator responder initiator_nonce (PubKey responder_key)
  in
  let auth_term = ma_auth_input_term session responder initiator Responder in
  let s_p' =
    p2s_state (ma_nsl_responder_reply_state (s2p_state s_p)
          session
          responder
          initiator
          initiator_nonce
          responder_nonce
          responder_key)
      post_know
  in
  ma_nsl_responder_reply_state_inputs_eq (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  ma_nsl_responder_reply_state_preserves_used_nonces (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  let stored_helper (query_participant: participant_id) (query_session: session_id) (n: nonce)
      : Lemma
      (ensures
        (match
            ma_get_participant_session_state (s2p_state s_p') query_participant query_session
          with
          | Some pss ->
            nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
          | None -> True)) =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      query_participant
      query_session;
    assert (match
          ma_get_participant_session_state (s2p_state s_p') query_participant query_session
        with
        | Some pss ->
          nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
        | None -> True)
  in
  FStar.Classical.forall_intro_3 stored_helper;
  let input_helper (input_t: term)
      : Lemma
      (ensures
        Bag.mem input_t s_p'.inputs ==> ma_term_nonces_are_used s_p'.internal.used_nonces input_t) =
    Bag.mem_remove input_t auth_term (Bag.remove message1_term (s2p_state s_p).inputs);
    Bag.mem_remove input_t message1_term (s2p_state s_p).inputs;
    assert (Bag.mem input_t s_p'.inputs ==>
        ma_term_nonces_are_used s_p'.internal.used_nonces input_t)
  in
  FStar.Classical.forall_intro input_helper;
  ma_message2_term_nonces_are_used_from_message1_input s_p'.internal.used_nonces
    (s2p_state s_p).inputs
    session
    initiator
    responder
    initiator_nonce
    responder_nonce
    responder_key
    initiator_pubkey;
  ma_knowledge_nonces_snoc_preserves_subset s_p.know sent_term s_p'.internal.used_nonces;
  assert (ma_impl_used_nonces_invariant s_p')

#push-options ""

let ma_impl_responder_reply_preserves_ideal_request_matches_sim_session
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        ma_ideal_request_matches_sim_session (ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey)) =
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  let helper (query_session: session_id) (query_party query_peer: participant_id) (query_role: role)
      : Lemma
      (ensures
        Set.mem ({ party = query_party; peer = query_peer; role = query_role })
          (ma_session_requests (s2p_state s_q') query_session) ==>
        (match ma_get_sim_participant_session_state (s2p_state s_q') query_party query_session with
          | Some (SimInitiatorSession initiator_state) ->
            query_role == Initiator /\ initiator_state.initiator == query_party /\
            initiator_state.responder == query_peer
          | Some (SimResponderSession responder_state) ->
            query_role == Responder /\ responder_state.responder == query_party /\
            responder_state.initiator == query_peer
          | None -> False)) =
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey query_party
      query_session;
    ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
      query_session;
    let new_request = { party = responder; peer = initiator; role = Responder } in
    let query_request = { party = query_party; peer = query_peer; role = query_role } in
    ma_set_mem_add query_request new_request (ma_session_requests (s2p_state s_q) session);
    if query_session = session && query_party = responder then ()
  in
  FStar.Classical.forall_intro_4 helper

#pop-options

let ma_impl_responder_reply_preserves_basic_state_facts
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        (let s_q' =
            ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey
          in
          ma_same_knowledge s_p' s_q' /\ ma_same_key_directory key_directory s_p' s_q' /\
          ma_same_inputs s_p' s_q' /\ ma_same_used_nonces s_p' s_q')) =
  let message1_term =
    ma_nsl_message1_network_term session initiator responder initiator_nonce (PubKey responder_key)
  in
  let auth_term = ma_auth_input_term session responder initiator Responder in
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  let s_q_mid = ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder in
  ma_nsl_responder_reply_state_inputs_eq (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  ma_nsl_responder_reply_state_preserves_key_directory (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  ma_nsl_responder_reply_state_preserves_used_nonces (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  ma_ideal_initiate_state_preserves_key_directory (s2p_state s_q)
    session
    responder
    initiator
    Responder;
  ma_ideal_initiate_state_preserves_used_nonces (s2p_state s_q)
    session
    responder
    initiator
    Responder;
  ma_sim_send_message2_state_inputs_eq s_q_mid
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  ma_sim_send_message2_state_preserves_key_directory s_q_mid
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  ma_sim_send_message2_state_preserves_used_nonces s_q_mid
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key;
  Bag.remove_remove_commute auth_term message1_term (s2p_state s_p).inputs;
  assert (ma_same_knowledge s_p' s_q' /\
      ma_same_key_directory key_directory s_p' s_q' /\ ma_same_inputs s_p' s_q' /\
      ma_same_used_nonces s_p' s_q')

let ma_impl_responder_reply_preserves_used_nonce_invariants
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures ma_impl_used_nonces_invariant s_p') =
  // The ideal used-nonce invariant at the witness post-state is recovered from
  // `ma_ideal_system_inv`.
  ma_nsl_responder_reply_state_preserves_impl_used_nonces_invariant s_p
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    initiator_pubkey
    s_p'.know;
  assert (ma_impl_used_nonces_invariant s_p')

let ma_impl_responder_reply_preserves_session_correspondence
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        (let s_q' =
            ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey
          in
          ma_initiator_session_correspondence s_p' s_q' /\
          ma_responder_session_correspondence s_p' s_q')) =
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  assert (s2p_state s_p' ==
      ma_nsl_responder_reply_state (s2p_state s_p)
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key);
  let initiator_corr_helper (query_session: session_id) (query_initiator: participant_id)
      : Lemma
      (ensures
        (let initiator_entry =
            ma_initiator_session_state (s2p_state s_p') query_initiator query_session
          in
          let sim_entry =
            ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session
          in
          (Some? initiator_entry <==> Some? sim_entry) /\
          (Some? initiator_entry ==>
            (let initiator_state = Some?.v initiator_entry in
              let sim_state = Some?.v sim_entry in
              initiator_state.initiator == sim_state.initiator /\
              initiator_state.responder == sim_state.responder /\
              initiator_state.initiator_nonce == sim_state.initiator_nonce /\
              initiator_state.ack_sent == sim_state.ack_sent)))) =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      query_initiator
      query_session;
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
      query_initiator query_session;
    assert (let initiator_entry =
          ma_initiator_session_state (s2p_state s_p') query_initiator query_session
        in
        let sim_entry =
          ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session
        in
        (Some? initiator_entry <==> Some? sim_entry) /\
        (Some? initiator_entry ==>
          (let initiator_state = Some?.v initiator_entry in
            let sim_state = Some?.v sim_entry in
            initiator_state.initiator == sim_state.initiator /\
            initiator_state.responder == sim_state.responder /\
            initiator_state.initiator_nonce == sim_state.initiator_nonce /\
            initiator_state.ack_sent == sim_state.ack_sent)))
  in
  let responder_corr_helper (query_session: session_id) (query_responder: participant_id)
      : Lemma
      (ensures
        (let responder_entry =
            ma_responder_session_state (s2p_state s_p') query_responder query_session
          in
          let sim_entry =
            ma_sim_responder_session_state (s2p_state s_q') query_responder query_session
          in
          (Some? responder_entry <==> Some? sim_entry) /\
          (Some? responder_entry ==>
            (let responder_state = Some?.v responder_entry in
              let sim_state = Some?.v sim_entry in
              responder_state.responder == sim_state.responder /\
              responder_state.initiator == sim_state.initiator /\
              responder_state.responder_nonce == sim_state.responder_nonce /\
              responder_state.output_sent == sim_state.output_forwarded)))) =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      query_responder
      query_session;
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
      query_responder query_session;
    assert (let responder_entry =
          ma_responder_session_state (s2p_state s_p') query_responder query_session
        in
        let sim_entry =
          ma_sim_responder_session_state (s2p_state s_q') query_responder query_session
        in
        (Some? responder_entry <==> Some? sim_entry) /\
        (Some? responder_entry ==>
          (let responder_state = Some?.v responder_entry in
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

#push-options "--z3rlimit 20"

let ma_impl_responder_reply_preserves_responder_reply_iff_off_updated_pair
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term{PubKey? quant_initiator_pubkey})
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term /\
          (quant_session <> session \/ quant_responder <> responder)))
      (ensures
        (let s_q' =
            ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey
          in
          ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p'
            s_q'
            quant_session
            quant_responder
            quant_initiator
            quant_initiator_nonce
            quant_responder_nonce
            quant_responder_key
            quant_initiator_pubkey)) =
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    quant_responder
    quant_session;
  ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
    responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
    quant_responder quant_session;
  ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    initiator_pubkey
    quant_session;
  assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance
        s_p
        s_q
        quant_session
        quant_responder
        quant_initiator
        quant_initiator_nonce
        quant_responder_nonce
        quant_responder_key
        quant_initiator_pubkey);
  assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance
        s_p'
        s_q'
        quant_session
        quant_responder
        quant_initiator
        quant_initiator_nonce
        quant_responder_nonce
        quant_responder_key
        quant_initiator_pubkey)

let ma_impl_responder_reply_preserves_initiator_start_iff_off_updated_pair
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term{PubKey? quant_responder_pubkey})
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term /\
          (quant_session <> session \/ quant_initiator <> responder)))
      (ensures
        (let s_q' =
            ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey
          in
          ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p'
            s_q'
            quant_session
            quant_initiator
            quant_responder
            quant_initiator_nonce
            quant_responder_pubkey)) =
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    quant_initiator
    quant_session;
  ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
    responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
    quant_initiator quant_session;
  ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    initiator_pubkey
    quant_session;
  assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance
        s_p
        s_q
        quant_session
        quant_initiator
        quant_responder
        quant_initiator_nonce
        quant_responder_pubkey);
  assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance
        s_p'
        s_q'
        quant_session
        quant_initiator
        quant_responder
        quant_initiator_nonce
        quant_responder_pubkey)

#pop-options

let ma_impl_responder_reply_preserves_enabledness_iffs
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term /\
          // Ideal-side invariant at the witness post-state, used to recover the
          // simulator bookkeeping clauses (sim-session/request and
          // output-token/phase) needed for the initiator-ack iff below.
          ma_ideal_system_inv corrupt key_directory
            (ma_impl_responder_reply_ideal_witness s_q
                session responder initiator initiator_nonce responder_nonce
                responder_key initiator_pubkey)))
      (ensures
        (let s_q' =
            ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey
          in
          ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q' /\
          ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')) =
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  ma_impl_responder_reply_preserves_basic_state_facts corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_impl_responder_reply_preserves_session_correspondence corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  // Recover the simulator bookkeeping clauses at the witness post-state from the
  // ideal-system invariant supplied by the precondition; these feed the
  // initiator-ack enabledness iff below.
  ma_ideal_system_inv_elim corrupt key_directory s_q';
  ma_impl_responder_reply_preserves_ideal_request_matches_sim_session corrupt key_directory s_p s_q session
    responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p'
        s_q');
  let responder_reply_helper
        (quant_session: session_id)
        (quant_responder quant_initiator: participant_id)
        (quant_initiator_nonce quant_responder_nonce: nonce)
        (quant_responder_key: priv_key)
        (quant_initiator_pubkey: term{PubKey? quant_initiator_pubkey})
      : Lemma
        (ensures
          ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p'
            s_q'
            quant_session
            quant_responder
            quant_initiator
            quant_initiator_nonce
            quant_responder_nonce
            quant_responder_key
            quant_initiator_pubkey)
        [
          SMTPat
          (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p'
              s_q'
              quant_session
              quant_responder
              quant_initiator
              quant_initiator_nonce
              quant_responder_nonce
              quant_responder_key
              quant_initiator_pubkey)
        ] =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      quant_responder
      quant_session;
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
      quant_responder quant_session;
    ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
      quant_session;
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance
          s_p
          s_q
          quant_session
          quant_responder
          quant_initiator
          quant_initiator_nonce
          quant_responder_nonce
          quant_responder_key
          quant_initiator_pubkey);
    if quant_session = session && quant_responder = responder
    then
      (assert (~(ma_nsl_responder_reply_enabled (s2p_state s_p')
                quant_session
                quant_responder
                quant_initiator
                quant_initiator_nonce
                quant_responder_nonce
                quant_responder_key
                quant_initiator_pubkey));
        assert (~(ma_sim_send_message2_enabled (ma_ideal_initiate_state
                    (s2p_state s_q')
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder)
                quant_session
                quant_responder
                quant_initiator
                quant_initiator_nonce
                quant_responder_nonce
                quant_responder_key
                quant_initiator_pubkey));
        assert (~(ma_ideal_initiate_enabled (s2p_state s_q')
                quant_session
                quant_responder
                quant_initiator
                Responder /\
              ma_sim_send_message2_enabled (ma_ideal_initiate_state (s2p_state s_q')
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder)
                quant_session
                quant_responder
                quant_initiator
                quant_initiator_nonce
                quant_responder_nonce
                quant_responder_key
                quant_initiator_pubkey));
        assert (ma_nsl_responder_reply_enabled (s2p_state s_p')
              quant_session
              quant_responder
              quant_initiator
              quant_initiator_nonce
              quant_responder_nonce
              quant_responder_key
              quant_initiator_pubkey <==>
            (ma_ideal_initiate_enabled (s2p_state s_q')
                quant_session
                quant_responder
                quant_initiator
                Responder /\
              ma_sim_send_message2_enabled (ma_ideal_initiate_state (s2p_state s_q')
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder)
                quant_session
                quant_responder
                quant_initiator
                quant_initiator_nonce
                quant_responder_nonce
                quant_responder_key
                quant_initiator_pubkey));
        assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance
              s_p'
              s_q'
              quant_session
              quant_responder
              quant_initiator
              quant_initiator_nonce
              quant_responder_nonce
              quant_responder_key
              quant_initiator_pubkey))
    else
      (ma_impl_responder_reply_preserves_responder_reply_iff_off_updated_pair corrupt key_directory s_p s_q
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
          s_p' quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)
  in
  let initiator_output_helper
        (quant_session: session_id)
        (quant_initiator quant_responder: participant_id)
      : Lemma
        (ensures
          ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p'
            s_q'
            quant_session
            quant_initiator
            quant_responder)
        [
          SMTPat
          (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p'
              s_q'
              quant_session
              quant_initiator
              quant_responder)
        ] =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      quant_initiator
      quant_session;
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
      quant_initiator quant_session;
    ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
      quant_session;
    let new_request = { party = responder; peer = initiator; role = Responder } in
    let request = { party = quant_initiator; peer = quant_responder; role = Initiator } in
    let complementary_request = complementary_request quant_initiator quant_responder Initiator in
    ma_set_mem_add request new_request (ma_session_requests (s2p_state s_q) session);
    ma_set_mem_add complementary_request new_request (ma_session_requests (s2p_state s_q) session);
    if quant_session = session && quant_initiator = responder then ();
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance
          s_p
          s_q
          quant_session
          quant_initiator
          quant_responder);
    assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance
          s_p'
          s_q'
          quant_session
          quant_initiator
          quant_responder)
  in
  let initiator_start_helper
        (quant_session: session_id)
        (quant_initiator quant_responder: participant_id)
        (quant_initiator_nonce: nonce)
        (quant_responder_pubkey: term{PubKey? quant_responder_pubkey})
      : Lemma
        (ensures
          ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p'
            s_q'
            quant_session
            quant_initiator
            quant_responder
            quant_initiator_nonce
            quant_responder_pubkey)
        [
          SMTPat
          (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p'
              s_q'
              quant_session
              quant_initiator
              quant_responder
              quant_initiator_nonce
              quant_responder_pubkey)
        ] =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      quant_initiator
      quant_session;
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
      quant_initiator quant_session;
    ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
      quant_session;
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance
          s_p
          s_q
          quant_session
          quant_initiator
          quant_responder
          quant_initiator_nonce
          quant_responder_pubkey);
    if quant_session = session && quant_initiator = responder
    then
      (assert (~(ma_nsl_initiator_start_enabled (s2p_state s_p')
                quant_session
                quant_initiator
                quant_responder
                quant_initiator_nonce
                quant_responder_pubkey));
        assert (~(ma_sim_send_message1_enabled (ma_ideal_initiate_state
                    (s2p_state s_q')
                    quant_session
                    quant_initiator
                    quant_responder
                    Initiator)
                quant_session
                quant_initiator
                quant_responder
                quant_initiator_nonce
                quant_responder_pubkey)));
    if quant_session = session && quant_initiator = responder
    then
      assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance
            s_p'
            s_q'
            quant_session
            quant_initiator
            quant_responder
            quant_initiator_nonce
            quant_responder_pubkey)
    else
      ma_impl_responder_reply_preserves_initiator_start_iff_off_updated_pair corrupt key_directory s_p s_q
        session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
        s_p' quant_session quant_initiator quant_responder quant_initiator_nonce
        quant_responder_pubkey
  in
  let responder_output_helper
        (quant_session: session_id)
        (quant_responder quant_initiator: participant_id)
        (quant_responder_key: priv_key)
      : Lemma
        (ensures
          ma_responder_output_equivalent_transitions_enabled_iff_instance s_p'
            s_q'
            quant_session
            quant_responder
            quant_initiator
            quant_responder_key)
        [
          SMTPat
          (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p'
              s_q'
              quant_session
              quant_responder
              quant_initiator
              quant_responder_key)
        ] =
    ma_nsl_responder_reply_state_get_updated_participant_session_state (s2p_state s_p)
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      quant_responder
      quant_session;
    ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state s_q session
      responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
      quant_responder quant_session;
    ma_impl_responder_reply_ideal_witness_updated_session_requests s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
      quant_session;
    let new_request = { party = responder; peer = initiator; role = Responder } in
    let request = { party = quant_responder; peer = quant_initiator; role = Responder } in
    let complementary_request = complementary_request quant_responder quant_initiator Responder in
    ma_set_mem_add request new_request (ma_session_requests (s2p_state s_q) session);
    ma_set_mem_add complementary_request new_request (ma_session_requests (s2p_state s_q) session);
    let message3_input =
      ma_nsl_message3_network_term quant_session
        quant_initiator
        quant_responder
        responder_nonce
        (PubKey quant_responder_key)
    in
    assert (ma_impl_used_nonces_invariant s_p /\
        ma_same_inputs s_p' s_q' /\ ma_same_key_directory key_directory s_p' s_q' /\
        ma_responder_session_correspondence s_p' s_q');
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
          s_p
          s_q
          quant_session
          quant_responder
          quant_initiator
          quant_responder_key);
    if quant_session = session && quant_responder = responder
    then
      (assert (quant_session == session /\ quant_responder == responder);
        let matching_message3_input =
          // In the updated-session case, responder reply creates the exact
          // responder session whose stored nonce is the fresh responder_nonce.
          ma_nsl_message3_network_term session
            quant_initiator
            responder
            responder_nonce
            (PubKey quant_responder_key)
        in
        assert (message3_input == matching_message3_input);
        ma_nsl_responder_reply_state_inputs_eq (s2p_state s_p)
          session
          responder
          initiator
          initiator_nonce
          responder_nonce
          responder_key;
        // The responder-reply step only removes Auth(...) and Message1(...), so a
        // potential enabling Message3 is unaffected by those removals.
        assert (matching_message3_input <>
            ma_auth_input_term session responder initiator Responder);
        assert (matching_message3_input <>
            ma_nsl_message1_network_term session
              initiator
              responder
              initiator_nonce
              (PubKey responder_key));
        Bag.mem_remove matching_message3_input
          (ma_auth_input_term session responder initiator Responder)
          (Bag.remove (ma_nsl_message1_network_term session
                  initiator
                  responder
                  initiator_nonce
                  (PubKey responder_key))
              (s2p_state s_p).inputs);
        Bag.mem_remove matching_message3_input
          (ma_nsl_message1_network_term session
              initiator
              responder
              initiator_nonce
              (PubKey responder_key))
          (s2p_state s_p).inputs;
        assert (ma_inputs_nonces_are_used (s2p_state s_p).internal
                .used_nonces
              (s2p_state s_p).inputs);
        let matching_message3_input_mem_implies_responder_nonce_used ()
            : // Any queued matching Message3 would require responder_nonce be in the
            // pre-state used-nonces set via ma_inputs_nonces_are_used. This would
            // contradict the pre-state freshness requirement for enabling responder
            // reply, so no matching Message3 can be queued in the pre-state.
            Lemma (requires Bag.mem matching_message3_input (s2p_state s_p).inputs)
              (ensures Set.mem responder_nonce (s2p_state s_p).internal.used_nonces) =
          assert (ma_term_nonces_are_used (s2p_state s_p).internal
                  .used_nonces
                matching_message3_input);
          // `matching_message3_input` is definitionally the message3 network
          // term application below.  We restate the goal against that explicit
          // application so that `norm [delta_only ...]` can unfold the
          // `ma_term_nonces` chain (a `let`-bound local is not a `delta_only`
          // target), then SMT closes the residual `Set` membership.
          assert (matching_message3_input ==
            ma_nsl_message3_network_term session
              quant_initiator
              responder
              responder_nonce
              (PubKey quant_responder_key));
          FStar.Tactics.Effect.assert_by_tactic (Set.mem responder_nonce
                (ma_term_nonces (ma_nsl_message3_network_term session
                    quant_initiator
                    responder
                    responder_nonce
                    (PubKey quant_responder_key))))
            (fun _ ->
                (let open FStar.Tactics.V2 in
                  norm [
                      delta_only [
                          `%ma_term_nonces;
                          `%ma_nsl_message3_network_term;
                          `%ma_nsl_message3_term;
                          `%ma_net_input_term
                        ];
                      zeta;
                      iota
                    ];
                  smt ()));
          FStar.Tactics.Effect.assert_by_tactic (Set.mem responder_nonce
                (s2p_state s_p).internal.used_nonces)
            (fun _ ->
                (let open FStar.Tactics.V2 in
                  norm [delta_only [`%ma_term_nonces_are_used]; zeta; iota];
                  smt ()))
        in
        let _h_implies
          : squash (Bag.mem matching_message3_input (s2p_state s_p).inputs ==>
                    Set.mem responder_nonce (s2p_state s_p).internal.used_nonces)
          = FStar.Classical.Sugar.implies_intro (Bag.mem matching_message3_input
                  (s2p_state s_p).inputs)
              (fun _ -> Set.mem responder_nonce (s2p_state s_p).internal.used_nonces)
              (fun h_mem ->
                  matching_message3_input_mem_implies_responder_nonce_used ();
                  (() <: squash (Set.mem responder_nonce
                        (s2p_state s_p).internal.used_nonces))) in
        // But responder reply is only enabled when responder_nonce is fresh in
        // the pre-state, so that matching Message3 cannot already be queued.
        FStar.Tactics.Effect.assert_by_tactic (not (Set.mem responder_nonce
                  (s2p_state s_p).internal.used_nonces))
          (fun _ ->
              (let open FStar.Tactics.V2 in
                norm [
                    delta_only [
                        `%ma_bisim_relation;
                        `%ma_nsl_responder_reply_enabled;
                        `%ma_nsl_nonce_is_fresh
                      ];
                    zeta;
                    iota
                  ];
                smt ()));
        assert (not (Bag.mem matching_message3_input
                  (s2p_state s_p).inputs));
        assert (not (Bag.mem matching_message3_input
                  (s2p_state s_p').inputs));
        // With no matching Message3 available after the reply, both the
        // implementation responder-output transition and the simulator
        // receive-message3 transition are disabled, so the iff is immediate.
        assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
              s_p'
              s_q'
              quant_session
              quant_responder
              quant_initiator
              quant_responder_key))
    else
      (assert (quant_session <> session \/ quant_responder <> responder);
        let post_impl_enabled_eq ()
            : // Away from the updated responder session, responder reply only removes
            // Auth(...) and Message1(...), so responder-output enabledness is carried
            // across by preserving the relevant Message3 membership and session data.
            Lemma
            (ensures
              (ma_nsl_responder_output_enabled (s2p_state s_p')
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key <==>
                ma_nsl_responder_output_enabled (s2p_state s_p)
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key)) =
          match ma_responder_session_state (s2p_state s_p) quant_responder quant_session with
          | Some quant_responder_state ->
            let responder_message3_input =
              ma_nsl_message3_network_term quant_session
                quant_initiator
                quant_responder
                quant_responder_state.responder_nonce
                (PubKey quant_responder_key)
            in
            assert (responder_message3_input <>
                ma_auth_input_term session responder initiator Responder);
            assert (responder_message3_input <>
                ma_nsl_message1_network_term session
                  initiator
                  responder
                  initiator_nonce
                  (PubKey responder_key));
            Bag.mem_remove responder_message3_input
              (ma_auth_input_term session responder initiator Responder)
              (Bag.remove (ma_nsl_message1_network_term session
                      initiator
                      responder
                      initiator_nonce
                      (PubKey responder_key))
                  (s2p_state s_p).inputs);
            Bag.mem_remove responder_message3_input
              (ma_nsl_message1_network_term session
                  initiator
                  responder
                  initiator_nonce
                  (PubKey responder_key))
              (s2p_state s_p).inputs;
            assert (ma_nsl_responder_output_enabled (s2p_state s_p')
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key <==>
                ma_nsl_responder_output_enabled (s2p_state s_p)
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key)
          | None ->
            assert (ma_nsl_responder_output_enabled (s2p_state s_p')
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key <==>
                ma_nsl_responder_output_enabled (s2p_state s_p)
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key)
        in
        let post_ideal_enabled_eq ()
            : // The ideal-side receive/deliver pair is preserved for the same reason:
            // the responder-reply witness does not touch the relevant Message3 input
            // or the requests needed for this off-session/off-responder instance.
            Lemma
            (ensures
              ((ma_sim_receive_message3_enabled (s2p_state s_q')
                    quant_session
                    quant_responder
                    quant_initiator
                    quant_responder_key /\
                  ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q')
                        quant_session
                        quant_responder
                        quant_initiator
                        quant_responder_key)
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder) <==>
                (ma_sim_receive_message3_enabled (s2p_state s_q)
                    quant_session
                    quant_responder
                    quant_initiator
                    quant_responder_key /\
                  ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q)
                        quant_session
                        quant_responder
                        quant_initiator
                        quant_responder_key)
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder))) =
          match ma_sim_responder_session_state (s2p_state s_q) quant_responder quant_session with
          | Some quant_responder_state ->
            let responder_message3_input =
              ma_nsl_message3_network_term quant_session
                quant_initiator
                quant_responder
                quant_responder_state.responder_nonce
                (PubKey quant_responder_key)
            in
            assert (responder_message3_input <>
                ma_auth_input_term session responder initiator Responder);
            assert (responder_message3_input <>
                ma_nsl_message1_network_term session
                  initiator
                  responder
                  initiator_nonce
                  (PubKey responder_key));
            Bag.mem_remove responder_message3_input
              (ma_auth_input_term session responder initiator Responder)
              (Bag.remove (ma_nsl_message1_network_term session
                      initiator
                      responder
                      initiator_nonce
                      (PubKey responder_key))
                  (s2p_state s_q).inputs);
            Bag.mem_remove responder_message3_input
              (ma_nsl_message1_network_term session
                  initiator
                  responder
                  initiator_nonce
                  (PubKey responder_key))
              (s2p_state s_q).inputs;
            assert (ma_sim_receive_message3_enabled (s2p_state s_q')
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key <==>
                ma_sim_receive_message3_enabled (s2p_state s_q)
                  quant_session
                  quant_responder
                  quant_initiator
                  quant_responder_key);
            assert (ma_ideal_deliver_enabled (ma_sim_receive_message3_state
                      (s2p_state s_q')
                      quant_session
                      quant_responder
                      quant_initiator
                      quant_responder_key)
                  quant_session
                  quant_responder
                  quant_initiator
                  Responder <==>
                ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q)
                      quant_session
                      quant_responder
                      quant_initiator
                      quant_responder_key)
                  quant_session
                  quant_responder
                  quant_initiator
                  Responder);
            assert ((ma_sim_receive_message3_enabled (s2p_state s_q')
                    quant_session
                    quant_responder
                    quant_initiator
                    quant_responder_key /\
                  ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q')
                        quant_session
                        quant_responder
                        quant_initiator
                        quant_responder_key)
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder) <==>
                (ma_sim_receive_message3_enabled (s2p_state s_q)
                    quant_session
                    quant_responder
                    quant_initiator
                    quant_responder_key /\
                  ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q)
                        quant_session
                        quant_responder
                        quant_initiator
                        quant_responder_key)
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder))
          | None ->
            assert ((ma_sim_receive_message3_enabled (s2p_state s_q')
                    quant_session
                    quant_responder
                    quant_initiator
                    quant_responder_key /\
                  ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q')
                        quant_session
                        quant_responder
                        quant_initiator
                        quant_responder_key)
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder) <==>
                (ma_sim_receive_message3_enabled (s2p_state s_q)
                    quant_session
                    quant_responder
                    quant_initiator
                    quant_responder_key /\
                  ma_ideal_deliver_enabled (ma_sim_receive_message3_state (s2p_state s_q)
                        quant_session
                        quant_responder
                        quant_initiator
                        quant_responder_key)
                    quant_session
                    quant_responder
                    quant_initiator
                    Responder))
        in
        post_impl_enabled_eq ();
        post_ideal_enabled_eq ();
        assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
              s_p'
              s_q'
              quant_session
              quant_responder
              quant_initiator
              quant_responder_key))
  in
  introduce forall (quant_session: session_id) (quant_responder: participant_id) (quant_initiator:
  participant_id) (quant_initiator_nonce: nonce) (quant_responder_nonce: nonce) (quant_responder_key:
  priv_key) (quant_initiator_pubkey: term{PubKey? quant_initiator_pubkey}) . ma_responder_reply_equivalent_transitions_enabled_iff_instance
    s_p'
    s_q'
    quant_session
    quant_responder
    quant_initiator
    quant_initiator_nonce
    quant_responder_nonce
    quant_responder_key
    quant_initiator_pubkey
  with responder_reply_helper quant_session
    quant_responder
    quant_initiator
    quant_initiator_nonce
    quant_responder_nonce
    quant_responder_key
    quant_initiator_pubkey;
  introduce forall (quant_session: session_id) (quant_initiator: participant_id) (quant_responder:
  participant_id) . ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p'
    s_q'
    quant_session
    quant_initiator
    quant_responder
  with initiator_output_helper quant_session quant_initiator quant_responder;
  introduce forall (quant_session: session_id) (quant_initiator: participant_id) (quant_responder:
  participant_id) (quant_initiator_nonce: nonce) (quant_responder_pubkey:
  term{PubKey? quant_responder_pubkey}) . ma_initiator_start_equivalent_transitions_enabled_iff_instance
    s_p'
    s_q'
    quant_session
    quant_initiator
    quant_responder
    quant_initiator_nonce
    quant_responder_pubkey
  with initiator_start_helper quant_session
    quant_initiator
    quant_responder
    quant_initiator_nonce
    quant_responder_pubkey;
  introduce forall (quant_session: session_id) (quant_responder: participant_id) (quant_initiator:
  participant_id) (quant_responder_key: priv_key) . ma_responder_output_equivalent_transitions_enabled_iff_instance
    s_p'
    s_q'
    quant_session
    quant_responder
    quant_initiator
    quant_responder_key
  with responder_output_helper quant_session quant_responder quant_initiator quant_responder_key;
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p'
        s_q' /\ ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
      ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q' /\
      ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')

#push-options "--z3rlimit 10"

let ma_obs_bisim_observable_step_impl_responder_reply_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          s_p'
          (ma_impl_responder_reply_ideal_witness s_q
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey)) =
  let sent_term =
    ma_nsl_message2_term session
      initiator
      responder
      initiator_nonce
      responder_nonce
      initiator_pubkey
  in
  let message1_term =
    ma_nsl_message1_network_term session initiator responder initiator_nonce (PubKey responder_key)
  in
  let auth_term = ma_auth_input_term session responder initiator Responder in
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  let s_q_mid = ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder in
  // Discharge the ideal-side relation conjunct `ma_ideal_system_inv
  // key_directory s_q'` here for the post-state.  The pre-state invariant is
  // carried by `ma_bisim_relation corrupt key_directory s_p s_q`; the matching ideal
  // enabledness comes from the responder-reply equivalent-transitions bridge
  // applied to the implementation enabledness precondition;
  // `ma_impl_responder_reply_ideal_witness_preserves_inv` then chains
  // `ma_ideal_system_inv_preserved` over the ideal-initiate + send-message2
  // steps to obtain the post-state invariant.
  assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
    session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey);
  ma_impl_responder_reply_ideal_witness_preserves_inv corrupt key_directory s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey;
  ma_impl_responder_reply_preserves_basic_state_facts corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_impl_responder_reply_preserves_used_nonce_invariants corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_impl_responder_reply_preserves_session_correspondence corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_impl_responder_reply_preserves_ideal_request_matches_sim_session corrupt key_directory s_p s_q session
    responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_impl_responder_reply_preserves_enabledness_iffs corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_impl_responder_reply_preserves_secrecy_clauses corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')

#pop-options

let ma_ideal_send_message2_preserves_impl_transition_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
          ma_sim_send_message2_enabled (ma_ideal_initiate_state (s2p_state s_q)
                session
                responder
                initiator
                Responder)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          (exists (s_q_mid: ideal_system_state).
              // ma_ideal_initiate_protocol_transition is existentially
              // quantified over the party, peer, and role parameters that
              // determine stepped to state for the transition. As a result, the
              // `ma_ideal_initiate_protocol_transition (s2p_state s_q) session
              // (s2p_state s_q_mid)` relation could hold here for different
              // parameters. We therefore explicitly characterize the
              // existentially quantified transition parameters by adding the
              // stepped to state here. When this proof is used in the main
              // bisimulation proof, these parameters and facts can be pulled
              // from the `ma_ideal_initiate_protocol_transition` assumption.
              ((s2p_state s_q_mid) ==
                ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder) /\
              ma_ideal_initiate_protocol_transition (s2p_state s_q) session responder initiator Responder (s2p_state s_q_mid) /\
              s_q_mid.know == s_q.know /\
              ma_sim_send_message2_protocol_transition (s2p_state s_q_mid)
                session
                responder
                initiator
                sent_term
                (s2p_state s_q') /\ s_q'.know == Seq.snoc s_q_mid.know sent_term)))
      (ensures
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          let s_p' =
            ma_ideal_send_message2_impl_witness s_p
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey
          in
          ma_nsl_responder_reply_enabled (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          s2p_state s_p' ==
          ma_nsl_responder_reply_state (s2p_state s_p)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key /\ s_p'.know == Seq.snoc s_p.know sent_term /\
          ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p'))) =
  let sent_term =
    ma_nsl_message2_term session
      initiator
      responder
      initiator_nonce
      responder_nonce
      initiator_pubkey
  in
  let s_p' =
    ma_ideal_send_message2_impl_witness s_p
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance
        s_p
        s_q
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key
        initiator_pubkey);
  assert (ma_nsl_responder_reply_enabled (s2p_state s_p)
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key
        initiator_pubkey);
  assert (s2p_state s_p' ==
      ma_nsl_responder_reply_state (s2p_state s_p)
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key);
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  introduce exists responder' initiator' initiator_nonce' responder_nonce' responder_key' initiator_pubkey'.ma_nsl_responder_reply_enabled
    (s2p_state s_p)
    session
    responder'
    initiator'
    initiator_nonce'
    responder_nonce'
    responder_key'
    initiator_pubkey' /\
  sent_term ==
  MA.NSL.ma_nsl_message2_term session
    initiator'
    responder'
    initiator_nonce'
    responder_nonce'
    initiator_pubkey' /\
  s2p_state s_p' ==
  ma_nsl_responder_reply_state (s2p_state s_p)
    session
    responder'
    initiator'
    initiator_nonce'
    responder_nonce'
    responder_key'
  with responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
  and ();
  assert (ma_nsl_responder_reply_transition (s2p_state s_p)
        session
        responder
        initiator
        sent_term
        (s2p_state s_p'));
  assert (ma_nsl_responder_reply_enabled (s2p_state s_p)
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key
        initiator_pubkey /\
      s2p_state s_p' ==
      ma_nsl_responder_reply_state (s2p_state s_p)
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key /\ s_p'.know == Seq.snoc s_p.know sent_term /\
      ma_nsl_responder_reply_transition (s2p_state s_p) session responder initiator sent_term (s2p_state s_p'))

let ma_ideal_send_message2_preserves_ideal_witness_clause
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
          ma_sim_send_message2_enabled (ma_ideal_initiate_state (s2p_state s_q)
                session
                responder
                initiator
                Responder)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          (exists (s_q_mid: ideal_system_state).
              ((s2p_state s_q_mid) ==
                ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder) /\
              ma_ideal_initiate_protocol_transition (s2p_state s_q) session responder initiator Responder (s2p_state s_q_mid) /\
              s_q_mid.know == s_q.know /\
              ma_sim_send_message2_protocol_transition (s2p_state s_q_mid)
                session
                responder
                initiator
                sent_term
                (s2p_state s_q') /\ s_q'.know == Seq.snoc s_q_mid.know sent_term)))
      (ensures
        s_q' ==
        ma_impl_responder_reply_ideal_witness s_q
          session
          responder
          initiator
          initiator_nonce
          responder_nonce
          responder_key
          initiator_pubkey) =
  assert (s_q' ==
      ma_impl_responder_reply_ideal_witness s_q
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key
        initiator_pubkey)

let ma_obs_bisim_observable_step_ideal_send_message2_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term{PubKey? initiator_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message2_term session
              initiator
              responder
              initiator_nonce
              responder_nonce
              initiator_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
          ma_sim_send_message2_enabled (ma_ideal_initiate_state (s2p_state s_q)
                session
                responder
                initiator
                Responder)
            session
            responder
            initiator
            initiator_nonce
            responder_nonce
            responder_key
            initiator_pubkey /\
          (exists (s_q_mid: ideal_system_state).
              // ma_ideal_initiate_protocol_transition is existentially
              // quantified over the party, peer, and role parameters that
              // determine stepped to state for the transition. As a result, the
              // `ma_ideal_initiate_protocol_transition (s2p_state s_q) session
              // (s2p_state s_q_mid)` relation could hold here for different
              // parameters. We therefore explicitly characterize the
              // existentially quantified transition parameters by adding the
              // stepped to state here. When this proof is used in the main
              // bisimulation proof, these parameters and facts can be pulled
              // from the `ma_ideal_initiate_protocol_transition` assumption.
              ((s2p_state s_q_mid) ==
                ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder) /\
              ma_ideal_initiate_protocol_transition (s2p_state s_q) session responder initiator Responder (s2p_state s_q_mid) /\
              s_q_mid.know == s_q.know /\
              ma_sim_send_message2_protocol_transition (s2p_state s_q_mid)
                session
                responder
                initiator
                sent_term
                (s2p_state s_q') /\ s_q'.know == Seq.snoc s_q_mid.know sent_term)))
      (ensures
        ma_bisim_relation corrupt key_directory
          (ma_ideal_send_message2_impl_witness s_p
              session
              responder
              initiator
              initiator_nonce
              responder_nonce
              responder_key
              initiator_pubkey)
          s_q') =
  let s_p' =
    ma_ideal_send_message2_impl_witness s_p
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  let s_q_witness =
    ma_impl_responder_reply_ideal_witness s_q
      session
      responder
      initiator
      initiator_nonce
      responder_nonce
      responder_key
      initiator_pubkey
  in
  ma_ideal_send_message2_preserves_impl_transition_clauses corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_q';
  ma_obs_bisim_observable_step_impl_responder_reply_preserves_relation corrupt key_directory s_p s_q session
    responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  assert (ma_bisim_relation corrupt key_directory s_p' s_q_witness);
  ma_ideal_send_message2_preserves_ideal_witness_clause corrupt key_directory s_p s_q session responder
    initiator initiator_nonce responder_nonce responder_key initiator_pubkey s_q';
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')
