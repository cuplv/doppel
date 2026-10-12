module MA.ObservationalBisimulation.Witnesses

#set-options "--z3rlimit 25"

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

let ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
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
      )) =
  let s_q_mid = ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator in
  let session_state =
    SimInitiatorSession
      {
        initiator = initiator;
        responder = responder;
        initiator_nonce = initiator_nonce;
        ack_sent = false
      }
  in
  if query_participant = initiator && query_session = session then
    ma_get_sim_participant_session_state_after_update_same
      s_q_mid initiator session session_state
  else
    (ma_get_sim_participant_session_state_after_update_different
      s_q_mid initiator session session_state query_participant query_session;
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q) session initiator responder Initiator query_participant query_session)

let ma_impl_initiator_start_ideal_witness_get_updated_sim_responder_session_state
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
        | None -> True)) =
  ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
    s_q session initiator responder initiator_nonce responder_pubkey query_responder query_session;
  assert (let s_q' = ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey in
    match ma_sim_responder_session_state (s2p_state s_q') query_responder query_session with
    | Some responder_state ->
      ma_sim_responder_session_state (s2p_state s_q) query_responder query_session ==
      Some responder_state
    | None -> True)

let ma_impl_initiator_start_ideal_witness_updated_session_requests
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
= if query_session = session
  then ()
  else ()

private
let ma_nsl_responder_reply_transition_witnesses
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (sent_term: term)
      (s': Protocol.state term impl_internal_state)
    : Lemma
      (requires
        ma_nsl_responder_reply_enabled
          s session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey /\
        sent_term == MA.NSL.ma_nsl_message2_term
          session initiator responder initiator_nonce responder_nonce initiator_pubkey /\
        s' == ma_nsl_responder_reply_state
          s session responder initiator initiator_nonce responder_nonce responder_key)
      (ensures
        ma_nsl_responder_reply_transition s session responder initiator sent_term s') =
  introduce exists initiator_nonce' responder_nonce' responder_key' initiator_pubkey'.
    ma_nsl_responder_reply_enabled
      s session responder initiator initiator_nonce' responder_nonce' responder_key' initiator_pubkey' /\
    sent_term == MA.NSL.ma_nsl_message2_term
      session initiator responder initiator_nonce' responder_nonce' initiator_pubkey' /\
    s' == ma_nsl_responder_reply_state
      s session responder initiator initiator_nonce' responder_nonce' responder_key'
  with initiator_nonce responder_nonce responder_key initiator_pubkey
  and ()

private
let ma_nsl_initiator_ack_transition_witnesses
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_term: term)
      (s': Protocol.state term impl_internal_state)
    : Lemma
      (requires
        ma_nsl_initiator_ack_enabled
          s session initiator responder responder_nonce initiator_key responder_pubkey /\
        sent_term == MA.NSL.ma_nsl_message3_term
          session initiator responder responder_nonce responder_pubkey /\
        s' == ma_nsl_initiator_ack_state
          s session initiator responder responder_nonce initiator_key)
      (ensures
        ma_nsl_initiator_ack_transition s session initiator responder sent_term s') =
  introduce exists responder_nonce' initiator_key' responder_pubkey'.
    ma_nsl_initiator_ack_enabled
      s session initiator responder responder_nonce' initiator_key' responder_pubkey' /\
    sent_term == MA.NSL.ma_nsl_message3_term
      session initiator responder responder_nonce' responder_pubkey' /\
    s' == ma_nsl_initiator_ack_state
      s session initiator responder responder_nonce' initiator_key'
  with responder_nonce initiator_key responder_pubkey
  and ()

private
let ma_impl_system_observable_transition_from_protocol
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s: impl_system_state)
      (o: ma_effect)
      (lid: ma_label_id)
      (t: term)
      (s': impl_system_state)
    : Lemma
      (requires
        (ma_nsl_protocol key_directory).transition
          (s2p_state s)
          (Protocol.Observable o t lid)
          (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        (ma_impl_system corrupt key_directory know0).transitions
          s
          (TestedSystem.Observable o lid)
          s') =
  assert ((ma_impl_system corrupt key_directory know0).transitions
    s
    (TestedSystem.Observable o lid)
    s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ())

private
let ma_impl_singleton_eventually_observable
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': impl_system_state)
      (o: ma_effect)
      (lid: ma_label_id)
    : Lemma
      (requires
        (ma_impl_system corrupt key_directory know0).transitions
          s
          (TestedSystem.Observable o lid)
          s')
      (ensures
        eventually_observable_step
          (ma_impl_system corrupt key_directory know0)
          s
          [TestedSystem.Observable o lid]
          s') =
  let lbls : list system_label = [TestedSystem.Observable o lid] in
  assert (multi_transitions
    (ma_impl_system corrupt key_directory know0).transitions
    s
    lbls
    s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step
    (ma_impl_system corrupt key_directory know0)
    s
    lbls
    s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

private
let ma_nsl_initiator_start_transition_witnesses
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_term: term)
      (s': Protocol.state term impl_internal_state)
    : Lemma
      (requires
        ma_nsl_initiator_start_enabled
          s session initiator responder initiator_nonce responder_pubkey /\
        sent_term == MA.NSL.ma_nsl_message1_term
          session initiator responder initiator_nonce responder_pubkey /\
        s' == ma_nsl_initiator_start_state s session initiator responder initiator_nonce)
      (ensures
        ma_nsl_initiator_start_transition s session initiator responder sent_term s') =
  introduce exists initiator_nonce' responder_pubkey'.
    ma_nsl_initiator_start_enabled
      s session initiator responder initiator_nonce' responder_pubkey' /\
    sent_term == MA.NSL.ma_nsl_message1_term
      session initiator responder initiator_nonce' responder_pubkey' /\
    s' == ma_nsl_initiator_start_state s session initiator responder initiator_nonce'
  with initiator_nonce responder_pubkey
  and ()

private
let ma_nsl_protocol_transition_from_initiator_start
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_term: term)
      (s': Protocol.state term impl_internal_state)
    : Lemma
      (requires
        ma_nsl_initiator_start_enabled
          s session initiator responder initiator_nonce responder_pubkey /\
        sent_term == MA.NSL.ma_nsl_message1_term
          session initiator responder initiator_nonce responder_pubkey /\
        s' == ma_nsl_initiator_start_state s session initiator responder initiator_nonce)
      (ensures (
        let lid : ma_label_id =
          { session = session; party = initiator; peer = responder; role = Initiator }
        in
        ma_nsl_protocol_transition
          s
          (Protocol.Observable NetSend sent_term lid)
          s')) =
  ma_nsl_initiator_start_transition_witnesses
    s session initiator responder initiator_nonce responder_pubkey sent_term s';
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  assert (ma_nsl_protocol_transition
    s
    (Protocol.Observable NetSend sent_term lid)
    s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_nsl_protocol_transition]; zeta; iota];
        smt ())

private
let ma_responder_reply_enabled_from_ideal_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : Lemma
      (requires
        ma_responder_reply_equivalent_transitions_enabled_iff s_p s_q /\
        ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)
      (ensures
        ma_nsl_responder_reply_enabled (s2p_state s_p)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey) =
  let h_responder_reply_equiv
    : squash (ma_responder_reply_equivalent_transitions_enabled_iff s_p s_q) = ()
  in
  let h_session = FStar.Classical.Sugar.forall_elim session h_responder_reply_equiv in
  let h_responder = FStar.Classical.Sugar.forall_elim responder h_session in
  let h_initiator = FStar.Classical.Sugar.forall_elim initiator h_responder in
  let h_initiator_nonce = FStar.Classical.Sugar.forall_elim initiator_nonce h_initiator in
  let h_responder_nonce = FStar.Classical.Sugar.forall_elim responder_nonce h_initiator_nonce in
  let h_responder_key = FStar.Classical.Sugar.forall_elim responder_key h_responder_nonce in
  let _h_instance
    : squash (
        ma_nsl_responder_reply_enabled (s2p_state s_p)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey <==>
        (ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
         ma_sim_send_message2_enabled
           (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
           session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey))
    = FStar.Classical.Sugar.forall_elim initiator_pubkey h_responder_key
  in
  assert (ma_nsl_responder_reply_enabled (s2p_state s_p)
    session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)
    by (let open FStar.Tactics.V2 in smt ())

private
let ma_nsl_protocol_transition_from_responder_reply
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (responder initiator: participant_id)
      (sent_term: term)
      (s': Protocol.state term impl_internal_state)
    : Lemma
      (requires
        ma_nsl_responder_reply_transition s session responder initiator sent_term s')
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        ma_nsl_protocol_transition
          s
          (Protocol.Observable NetSend sent_term lid)
          s')) =
  ()

private
let ma_ideal_system_observable_transition_from_protocol
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s: ideal_system_state)
      (o: ma_effect)
      (lid: ma_label_id)
      (t: term)
      (s': ideal_system_state)
    : Lemma
      (requires
        (ma_ideal_protocol key_directory corrupt).transition
          (s2p_state s)
          (Protocol.Observable o t lid)
          (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        (ma_ideal_system corrupt key_directory know0).transitions
          s
          (TestedSystem.Observable o lid)
          s') =
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s
    (TestedSystem.Observable o lid)
    s')

    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ())

private
let ma_sim_send_message1_transition_witnesses
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_term: term)
      (s': Protocol.state term ideal_internal_state)
    : Lemma
      (requires
        ma_sim_send_message1_enabled
          s session initiator responder initiator_nonce responder_pubkey /\
        sent_term == ma_nsl_message1_term
          session initiator responder initiator_nonce responder_pubkey /\
        s' == ma_sim_send_message1_state s session initiator responder initiator_nonce)
      (ensures
        ma_sim_send_message1_protocol_transition s session initiator responder sent_term s') =
  introduce exists initiator_nonce' responder_pubkey'.
    ma_sim_send_message1_enabled
      s session initiator responder initiator_nonce' responder_pubkey' /\
    sent_term == ma_nsl_message1_term
      session initiator responder initiator_nonce' responder_pubkey' /\
    s' == ma_sim_send_message1_state s session initiator responder initiator_nonce'
  with initiator_nonce responder_pubkey
  and ()
private
let ma_sim_send_message2_transition_witnesses
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (sent_term: term)
      (s': Protocol.state term ideal_internal_state)
    : Lemma
      (requires
        ma_sim_send_message2_enabled
          s session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey /\
        sent_term == ma_nsl_message2_term
          session initiator responder initiator_nonce responder_nonce initiator_pubkey /\
        s' == ma_sim_send_message2_state
          s session responder initiator initiator_nonce responder_nonce responder_key)
      (ensures
        ma_sim_send_message2_protocol_transition s session responder initiator sent_term s') =
  introduce exists initiator_nonce' responder_nonce' responder_key' initiator_pubkey'.
    ma_sim_send_message2_enabled
      s session responder initiator initiator_nonce' responder_nonce' responder_key' initiator_pubkey' /\
    sent_term == ma_nsl_message2_term
      session initiator responder initiator_nonce' responder_nonce' initiator_pubkey' /\
    s' == ma_sim_send_message2_state
      s session responder initiator initiator_nonce' responder_nonce' responder_key'
  with initiator_nonce responder_nonce responder_key initiator_pubkey
  and ()

private
let ma_responder_output_transition_witnesses
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (output_term: term)
      (s': Protocol.state term impl_internal_state)
    : Lemma
      (requires
        ma_nsl_responder_output_enabled s session responder initiator responder_key /\
        output_term == ma_authenticated_term session responder initiator /\
        s' == ma_nsl_responder_output_state s session responder initiator responder_key)
      (ensures
        exists (responder_key': priv_key).
          ma_nsl_responder_output_enabled s session responder initiator responder_key' /\
          output_term == ma_authenticated_term session responder initiator /\
          s' == ma_nsl_responder_output_state s session responder initiator responder_key') =
  introduce exists responder_key'.
    ma_nsl_responder_output_enabled s session responder initiator responder_key' /\
    output_term == ma_authenticated_term session responder initiator /\
    s' == ma_nsl_responder_output_state s session responder initiator responder_key'
  with responder_key
  and ()

private
let ma_responder_output_ideal_enabled_from_impl_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (requires
        ma_responder_output_equivalent_transitions_enabled_iff s_p s_q /\
        ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key)
      (ensures
        ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
        ma_ideal_deliver_enabled
          (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
          session responder initiator Responder) =
  let h_responder_output_equiv
    : squash (ma_responder_output_equivalent_transitions_enabled_iff s_p s_q) = ()
  in
  let h_session = FStar.Classical.Sugar.forall_elim session h_responder_output_equiv in
  let h_responder = FStar.Classical.Sugar.forall_elim responder h_session in
  let h_initiator = FStar.Classical.Sugar.forall_elim initiator h_responder in
  let _h_instance
    : squash (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q
        session responder initiator responder_key)
    = FStar.Classical.Sugar.forall_elim responder_key h_initiator
  in
  assert (ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
      ma_ideal_deliver_enabled
        (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
        session responder initiator Responder)

private
let ma_sim_receive_message3_transition_witnesses
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s': Protocol.state term ideal_internal_state)
    : Lemma
      (requires
        ma_sim_receive_message3_enabled s session responder initiator responder_key /\
        s' == ma_sim_receive_message3_state s session responder initiator responder_key)
      (ensures
        ma_sim_receive_message3_protocol_transition s session responder initiator s') =
  introduce exists responder_key'.
    ma_sim_receive_message3_enabled s session responder initiator responder_key' /\
    s' == ma_sim_receive_message3_state s session responder initiator responder_key'
  with responder_key
  and ()

private
let ma_ideal_deliver_transition_witnesses
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (party peer: participant_id)
      (r: role)
      (output_t: term)
      (s': Protocol.state term ideal_internal_state)
    : Lemma
      (requires
        output_t == ma_authenticated_term session party peer /\
        ma_ideal_deliver_enabled s session party peer r /\
        s' == ma_ideal_deliver_state s session party peer)
      (ensures
        ma_ideal_deliver_protocol_transition s session party peer r output_t s') =
  ()

private
let ma_ideal_internal_observable_eventually_observable
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s_mid s': ideal_system_state)
      (o: ma_effect)
      (lid: ma_label_id)
    : Lemma
      (requires
        (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal lid) s_mid /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Observable o lid) s')
      (ensures
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s
          [TestedSystem.Internal lid; TestedSystem.Observable o lid]
          s') =
  let lbls : list system_label = [TestedSystem.Internal lid; TestedSystem.Observable o lid] in
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_mid
    [TestedSystem.Observable o lid] s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s lbls s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_ideal_system corrupt key_directory know0) s lbls s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

private
let ma_impl_responder_output_ideal_internal_step
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q s_q_mid: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (requires
        ma_responder_output_equivalent_transitions_enabled_iff s_p s_q /\
        ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key /\
        s_q_mid ==
          p2s_state
            (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
            s_q.know)
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
        ma_ideal_deliver_enabled (s2p_state s_q_mid) session responder initiator Responder /\
        (ma_ideal_system corrupt key_directory know0).transitions
          s_q
          (TestedSystem.Internal lid)
          s_q_mid)) =
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  ma_responder_output_ideal_enabled_from_impl_instance
    s_p s_q session responder initiator responder_key;
  assert (s2p_state s_q_mid ==
    ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key);
  ma_sim_receive_message3_transition_witnesses
    (s2p_state s_q)
    session
    responder
    initiator
    responder_key
    (s2p_state s_q_mid);
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q)
    (Protocol.Internal lid)
    (s2p_state s_q_mid));
  assert (s_q_mid.know == s_q.know);
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s_q
    (TestedSystem.Internal lid)
    s_q_mid)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ())

private
let ma_impl_responder_output_ideal_deliver_step
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_q s_q_mid s_q': ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (requires
        ma_ideal_deliver_enabled (s2p_state s_q_mid) session responder initiator Responder /\
        s_q_mid ==
          p2s_state
            (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
            s_q.know /\
        s2p_state s_q' == ma_ideal_deliver_state (s2p_state s_q_mid) session responder initiator /\
        s_q'.know == Seq.snoc s_q_mid.know (ma_authenticated_term session responder initiator))
      (ensures (
        let lid : ma_label_id =
          { session = session; party = responder; peer = initiator; role = Responder }
        in
        (ma_ideal_system corrupt key_directory know0).transitions
          s_q_mid
          (TestedSystem.Observable IoSend lid)
          s_q')) =
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let output_term = ma_authenticated_term session responder initiator in
  assert (s2p_state s_q_mid ==
    ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key);
  ma_ideal_deliver_transition_witnesses
    (s2p_state s_q_mid)
    session
    responder
    initiator
    Responder
    output_term
    (s2p_state s_q');
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q_mid)
    (Protocol.Observable IoSend output_term lid)
    (s2p_state s_q'));
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s_q_mid
    (TestedSystem.Observable IoSend lid)
    s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ())

let ma_obs_bisim_observable_step_impl_initiator_start
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
    =
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let sent_term =
    ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
  in
  let s_q_mid =
    p2s_state
      (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
      s_q.know
  in
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  let lbls : list system_label = [TestedSystem.Internal lid; TestedSystem.Observable NetSend lid] in
  assert (s2p_state s_q_mid ==
    ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator);
  assert (ma_initiator_start_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  let h_initiator_start_equiv
    : squash (ma_initiator_start_equivalent_transitions_enabled_iff s_p s_q) = ()
  in
  let h_session = FStar.Classical.Sugar.forall_elim session h_initiator_start_equiv in
  let h_initiator = FStar.Classical.Sugar.forall_elim initiator h_session in
  let h_responder = FStar.Classical.Sugar.forall_elim responder h_initiator in
  let h_initiator_nonce = FStar.Classical.Sugar.forall_elim initiator_nonce h_responder in
  let _h_instance
    : squash (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
        session initiator responder initiator_nonce responder_pubkey)
    = FStar.Classical.Sugar.forall_elim responder_pubkey h_initiator_nonce
  in
  assert (ma_ideal_initiate_enabled (s2p_state s_q) session initiator responder Initiator /\
      ma_sim_send_message1_enabled
        (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
        session
        initiator
        responder
        initiator_nonce
        responder_pubkey);
  assert (ma_ideal_initiate_protocol_transition
    (s2p_state s_q) session initiator responder Initiator (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_initiate_protocol_transition]; zeta; iota];
        smt ());
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q)
    (Protocol.Internal lid)
    (s2p_state s_q_mid));
  assert (s_q_mid.know == s_q.know);
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s_q
    (TestedSystem.Internal lid)
    s_q_mid)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (sent_term ==
    ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey);
  assert (s2p_state s_q' ==
    ma_sim_send_message1_state (s2p_state s_q_mid) session initiator responder initiator_nonce);
  assert (s2p_state s_q' ==
    ma_sim_send_message1_state
      (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
      session initiator responder initiator_nonce)
    by (let open FStar.Tactics.V2 in smt ());
  ma_sim_send_message1_transition_witnesses
    (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
    session
    initiator
    responder
    initiator_nonce
    responder_pubkey
    sent_term
    (s2p_state s_q');
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q_mid)
    (Protocol.Observable NetSend sent_term lid)
    (s2p_state s_q'));
  assert (s_q'.know == Seq.snoc s_q_mid.know sent_term);
  assert (exists t.
    (ma_ideal_protocol key_directory corrupt).transition
      (s2p_state s_q_mid)
      (Protocol.Observable NetSend t lid)
      (s2p_state s_q') /\
    s_q'.know == Seq.snoc s_q_mid.know t)
    by (let open FStar.Tactics.V2 in smt ());
  ma_ideal_system_observable_transition_from_protocol
    corrupt
    key_directory
    know0
    s_q_mid
    NetSend
    lid
    sent_term
    s_q';
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_q_mid
    [TestedSystem.Observable NetSend lid] s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

let ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state
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
      )) =
  let s_q_mid = ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder in
  ma_sim_send_message2_state_get_updated_sim_participant_session_state
    s_q_mid session responder initiator initiator_nonce responder_nonce responder_key
    query_participant query_session;
  if query_participant = responder && query_session = session then
    ()
  else
    ma_ideal_initiate_state_preserves_get_sim_participant_session_state
      (s2p_state s_q) session responder initiator Responder query_participant query_session

let ma_impl_responder_reply_ideal_witness_get_updated_sim_responder_session_state
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
          ma_sim_responder_session_state (s2p_state s_q) query_responder query_session)) =
  ma_impl_responder_reply_ideal_witness_get_updated_sim_participant_session_state
    s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
    query_responder query_session;
  assert (let s_q' = ma_impl_responder_reply_ideal_witness
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
      ma_sim_responder_session_state (s2p_state s_q) query_responder query_session)

let ma_impl_responder_reply_ideal_witness_updated_session_requests
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
= if query_session = session
  then ()
  else ()

let ma_obs_bisim_observable_step_impl_responder_reply
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
    =
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let sent_term =
    ma_nsl_message2_term
      session initiator responder initiator_nonce responder_nonce initiator_pubkey
  in
  let s_q_mid =
    p2s_state
      (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
      s_q.know
  in
  let s_q' =
    ma_impl_responder_reply_ideal_witness
      s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
  in
  let lbls : list system_label = [TestedSystem.Internal lid; TestedSystem.Observable NetSend lid] in
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  let h_responder_reply_equiv
    : squash (ma_responder_reply_equivalent_transitions_enabled_iff s_p s_q) = ()
  in
  let h_session = FStar.Classical.Sugar.forall_elim session h_responder_reply_equiv in
  let h_responder = FStar.Classical.Sugar.forall_elim responder h_session in
  let h_initiator = FStar.Classical.Sugar.forall_elim initiator h_responder in
  let h_initiator_nonce = FStar.Classical.Sugar.forall_elim initiator_nonce h_initiator in
  let h_responder_nonce = FStar.Classical.Sugar.forall_elim responder_nonce h_initiator_nonce in
  let h_responder_key = FStar.Classical.Sugar.forall_elim responder_key h_responder_nonce in
  let _h_instance
    : squash (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
        session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)
    = FStar.Classical.Sugar.forall_elim initiator_pubkey h_responder_key
  in
  assert (ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
      ma_sim_send_message2_enabled
        (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
        session
        responder
        initiator
        initiator_nonce
        responder_nonce
        responder_key
        initiator_pubkey);
  assert (s2p_state s_q_mid ==
    ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder);
  assert (ma_ideal_initiate_protocol_transition
    (s2p_state s_q) session responder initiator Responder (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_initiate_protocol_transition]; zeta; iota];
        smt ());
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q)
    (Protocol.Internal lid)
    (s2p_state s_q_mid));
  assert (s_q_mid.know == s_q.know);
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s_q
    (TestedSystem.Internal lid)
    s_q_mid)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (sent_term ==
    ma_nsl_message2_term
      session initiator responder initiator_nonce responder_nonce initiator_pubkey);
  assert (s2p_state s_q' ==
    ma_sim_send_message2_state (s2p_state s_q_mid) session responder initiator
      initiator_nonce responder_nonce responder_key);
  assert (s2p_state s_q' ==
    ma_sim_send_message2_state
      (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
      session responder initiator initiator_nonce responder_nonce responder_key)
    by (let open FStar.Tactics.V2 in smt ());
  ma_sim_send_message2_transition_witnesses
    (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    initiator_pubkey
    sent_term
    (s2p_state s_q');
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q_mid)
    (Protocol.Observable NetSend sent_term lid)
    (s2p_state s_q'));
  assert (s_q'.know == Seq.snoc s_q_mid.know sent_term);
  ma_ideal_system_observable_transition_from_protocol
    corrupt
    key_directory
    know0
    s_q_mid
    NetSend
    lid
    sent_term
    s_q';
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_q_mid
    [TestedSystem.Observable NetSend lid] s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

let ma_obs_bisim_observable_step_impl_initiator_ack
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
    =
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
  in
  let s_q' =
    ma_impl_initiator_ack_ideal_witness
      s_q session initiator responder responder_nonce initiator_key responder_pubkey
  in
  let lbls : list system_label = [TestedSystem.Observable NetSend lid] in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  assert (ma_sim_send_message3_enabled (s2p_state s_q)
    session initiator responder responder_nonce initiator_key responder_pubkey);
  assert (s2p_state s_q' ==
    ma_sim_send_message3_state (s2p_state s_q)
      session initiator responder responder_nonce initiator_key);
  assert (ma_sim_send_message3_protocol_transition
    (s2p_state s_q) session initiator responder sent_term (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_sim_send_message3_protocol_transition]; zeta; iota];
        smt ());
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q)
    (Protocol.Observable NetSend sent_term lid)
    (s2p_state s_q'));
  assert (s_q'.know == Seq.snoc s_q.know sent_term);
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s_q
    (TestedSystem.Observable NetSend lid)
    s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())


let ma_impl_initiator_output_ideal_witness_knowledge
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).know ==
        Seq.snoc s_q.know (ma_authenticated_term session initiator responder)) =
  ()

let ma_impl_initiator_output_ideal_witness_preserves_inputs
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).inputs ==
        s_q.inputs) =
  ma_ideal_deliver_state_preserves_inputs (s2p_state s_q) session initiator responder;
  assert ((ma_impl_initiator_output_ideal_witness s_q session initiator responder).inputs ==
      s_q.inputs)

let ma_impl_initiator_output_ideal_witness_preserves_key_directory
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.key_directory ==
        s_q.internal.key_directory) =
  ma_ideal_deliver_state_preserves_key_directory (s2p_state s_q) session initiator responder;
  assert ((ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.key_directory ==
      s_q.internal.key_directory)

let ma_impl_initiator_output_ideal_witness_preserves_sim_participant_sessions
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.sim_participant_sessions ==
        s_q.internal.sim_participant_sessions) =
  assert ((ma_impl_initiator_output_ideal_witness s_q session initiator responder).internal.sim_participant_sessions ==
      s_q.internal.sim_participant_sessions)

let ma_impl_initiator_output_ideal_witness_session_requests_eq
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures
        ma_session_requests
          (s2p_state (ma_impl_initiator_output_ideal_witness s_q session initiator responder))
          query_session ==
        ma_session_requests (s2p_state s_q) query_session) =
  ma_ideal_deliver_state_session_requests_eq
    (s2p_state s_q) session initiator responder query_session;
  assert (ma_session_requests
      (s2p_state (ma_impl_initiator_output_ideal_witness s_q session initiator responder))
      query_session ==
     ma_session_requests (s2p_state s_q) query_session)

let ma_obs_bisim_observable_step_impl_initiator_output
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
    =
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let output_term = ma_authenticated_term session initiator responder in
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  let lbls : list system_label = [TestedSystem.Observable IoSend lid] in
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  let h_initiator_output_equiv
    : squash (ma_initiator_output_equivalent_transitions_enabled_iff s_p s_q) = ()
  in
  let h_session = FStar.Classical.Sugar.forall_elim session h_initiator_output_equiv in
  let h_initiator = FStar.Classical.Sugar.forall_elim initiator h_session in
  let _h_instance
    : squash (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q
        session initiator responder)
    = FStar.Classical.Sugar.forall_elim responder h_initiator
  in
  assert (ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder <==>
      ma_ideal_deliver_enabled (s2p_state s_q) session initiator responder Initiator);
  assert (ma_ideal_deliver_enabled (s2p_state s_q) session initiator responder Initiator);
  assert (s2p_state s_q' == ma_ideal_deliver_state (s2p_state s_q) session initiator responder);
  assert (ma_ideal_deliver_protocol_transition
    (s2p_state s_q) session initiator responder Initiator output_term (s2p_state s_q'));
  assert ((ma_ideal_protocol key_directory corrupt).transition
    (s2p_state s_q)
    (Protocol.Observable IoSend output_term lid)
    (s2p_state s_q'));
  assert (s_q'.know == Seq.snoc s_q.know output_term);
  assert ((ma_ideal_system corrupt key_directory know0).transitions
    s_q
    (TestedSystem.Observable IoSend lid)
    s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (multi_transitions (ma_ideal_system corrupt key_directory know0).transitions s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

let ma_impl_responder_output_ideal_witness_knowledge
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key).know ==
        Seq.snoc s_q.know (ma_authenticated_term session responder initiator)) =
  ()

let ma_impl_responder_output_ideal_witness_session_requests_eq
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
        ma_session_requests (s2p_state s_q) query_session) =
  let s_q_mid = ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key in
  ma_sim_receive_message3_state_session_requests_eq
    (s2p_state s_q) session responder initiator responder_key query_session;
  ma_ideal_deliver_state_session_requests_eq s_q_mid session responder initiator query_session;
  assert (ma_session_requests
      (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key))
      query_session ==
     ma_session_requests (s2p_state s_q) query_session)

let ma_impl_responder_output_ideal_witness_preserves_key_directory
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.key_directory ==
        (s2p_state s_q).internal.key_directory) =
  let s_q_mid = ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key in
  ma_sim_receive_message3_state_preserves_key_directory
    (s2p_state s_q) session responder initiator responder_key;
  ma_ideal_deliver_state_preserves_key_directory s_q_mid session responder initiator;
  assert ((s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.key_directory ==
     (s2p_state s_q).internal.key_directory)

let ma_impl_responder_output_ideal_witness_preserves_used_nonces
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.used_nonces ==
        (s2p_state s_q).internal.used_nonces) =
  let s_q_mid = ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key in
  ma_sim_receive_message3_state_preserves_used_nonces
    (s2p_state s_q) session responder initiator responder_key;
  ma_ideal_deliver_state_preserves_used_nonces s_q_mid session responder initiator;
  assert ((s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.used_nonces ==
     (s2p_state s_q).internal.used_nonces)

let ma_impl_responder_output_ideal_witness_preserves_ideal_to_sim_channel
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.ideal_to_sim_channel ==
        (s2p_state s_q).internal.ideal_to_sim_channel) =
  let s_q_mid = ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key in
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel
    (s2p_state s_q) session responder initiator responder_key;
  ma_ideal_deliver_state_preserves_ideal_to_sim_channel s_q_mid session responder initiator;
  assert ((s2p_state (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key)).internal.ideal_to_sim_channel ==
     (s2p_state s_q).internal.ideal_to_sim_channel)

let ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
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
      )) =
  let s_q_mid = ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key in
  ma_sim_receive_message3_state_get_updated_sim_participant_session_state
    (s2p_state s_q) session responder initiator responder_key query_participant query_session;
  ma_ideal_deliver_state_preserves_get_sim_participant_session_state
    s_q_mid session responder initiator query_participant query_session;
  assert (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
    let responder_state = Some?.v (ma_sim_responder_session_state (s2p_state s_q) responder session) in
    if query_participant = responder && query_session = session then
      ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
      Some (SimResponderSession { responder_state with output_forwarded = true })
    else
      ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session ==
      ma_get_sim_participant_session_state (s2p_state s_q) query_participant query_session)

let ma_impl_responder_output_ideal_witness_preserves_sim_responder_session_fields
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
      )) =
  ma_impl_responder_output_ideal_witness_get_updated_sim_participant_session_state
    s_q session responder initiator responder_key query_responder query_session;
  assert (let s_q' = ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key in
    let post_entry = ma_sim_responder_session_state (s2p_state s_q') query_responder query_session in
    let pre_entry = ma_sim_responder_session_state (s2p_state s_q) query_responder query_session in
    Some? post_entry ==>
      Some? pre_entry /\
      (let post_responder_state = Some?.v post_entry in
      let pre_responder_state = Some?.v pre_entry in
      post_responder_state.responder == pre_responder_state.responder /\
      post_responder_state.initiator == pre_responder_state.initiator /\
      post_responder_state.responder_nonce == pre_responder_state.responder_nonce))

let ma_obs_bisim_observable_step_impl_responder_output
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_p': impl_system_state)
    =
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let s_q_mid =
    p2s_state
      (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
      s_q.know
  in
  let s_q' =
    ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key
  in
  assert (ma_responder_output_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  assert (ma_nsl_responder_output_enabled (s2p_state s_p) session responder initiator responder_key);
  ma_impl_responder_output_ideal_internal_step
    corrupt key_directory know0 s_p s_q s_q_mid session responder initiator responder_key;
  assert (s2p_state s_q' == ma_ideal_deliver_state (s2p_state s_q_mid) session responder initiator)
    by (let open FStar.Tactics.V2 in
        norm [
            delta_only [
                `%ma_impl_responder_output_ideal_witness;
                `%TestedSystem.s2p_state;
                `%TestedSystem.p2s_state
              ];
            zeta;
            iota
          ];
        smt ());
  assert (s_q'.know == Seq.snoc s_q_mid.know (ma_authenticated_term session responder initiator))
    by (let open FStar.Tactics.V2 in
        norm [
            delta_only [
                `%ma_impl_responder_output_ideal_witness;
                `%TestedSystem.p2s_state
              ];
            zeta;
            iota
          ];
        smt ());
  ma_impl_responder_output_ideal_deliver_step
    corrupt key_directory know0 s_q s_q_mid s_q' session responder initiator responder_key;
  ma_ideal_internal_observable_eventually_observable
    corrupt key_directory know0 s_q s_q_mid s_q' IoSend lid

let ma_obs_bisim_observable_step_ideal_send_message1
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
    =
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let sent_term =
    ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
  in
  let s_p' =
    ma_ideal_send_message1_impl_witness
      s_p session initiator responder initiator_nonce responder_pubkey
  in
  let lbls : list system_label = [TestedSystem.Observable NetSend lid] in
  assert (exists (s_q_mid: ideal_system_state).
    ma_ideal_initiate_protocol_transition (s2p_state s_q)
      session initiator responder Initiator
      (s2p_state s_q_mid) /\
    s_q_mid.know == s_q.know /\
    ma_sim_send_message1_protocol_transition (s2p_state s_q_mid)
      session initiator responder
      sent_term
      (s2p_state s_q') /\
    s_q'.know == Seq.snoc s_q_mid.know sent_term);
  assert (ma_nsl_initiator_start_enabled (s2p_state s_p)
    session initiator responder initiator_nonce responder_pubkey);
  assert (s2p_state s_p' ==
    ma_nsl_initiator_start_state (s2p_state s_p) session initiator responder initiator_nonce);
  ma_nsl_protocol_transition_from_initiator_start
    (s2p_state s_p)
    session
    initiator
    responder
    initiator_nonce
    responder_pubkey
    sent_term
    (s2p_state s_p');
  assert ((ma_nsl_protocol key_directory).transition
    (s2p_state s_p)
    (Protocol.Observable NetSend sent_term lid)
    (s2p_state s_p'));
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  ma_impl_system_observable_transition_from_protocol
    corrupt
    key_directory
    know0
    s_p
    NetSend
    lid
    sent_term
    s_p';
  assert (multi_transitions (ma_impl_system corrupt key_directory know0).transitions s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

let ma_obs_bisim_observable_step_ideal_send_message2
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
    =
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let sent_term =
    ma_nsl_message2_term
      session initiator responder initiator_nonce responder_nonce initiator_pubkey
  in
  let s_p' =
    ma_ideal_send_message2_impl_witness
      s_p session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
  in
  let lbls : list system_label = [TestedSystem.Observable NetSend lid] in
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  ma_responder_reply_enabled_from_ideal_instance
    s_p s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey;
  assert (exists (s_q_mid: ideal_system_state).
    ma_ideal_initiate_protocol_transition (s2p_state s_q)
      session responder initiator Responder
      (s2p_state s_q_mid) /\
    s_q_mid.know == s_q.know /\
    ma_sim_send_message2_protocol_transition (s2p_state s_q_mid)
      session responder initiator
      sent_term
      (s2p_state s_q') /\
    s_q'.know == Seq.snoc s_q_mid.know sent_term);
  assert (sent_term ==
    ma_nsl_message2_term
      session initiator responder initiator_nonce responder_nonce initiator_pubkey);
  assert (sent_term ==
    MA.NSL.ma_nsl_message2_term
      session initiator responder initiator_nonce responder_nonce initiator_pubkey)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%MA.Ideal.ma_nsl_message2_term; `%MA.NSL.ma_nsl_message2_term]; zeta; iota];
        smt ());
  assert (s2p_state s_p' ==
    ma_nsl_responder_reply_state (s2p_state s_p) session responder initiator
      initiator_nonce responder_nonce responder_key);
  ma_nsl_responder_reply_transition_witnesses
    (s2p_state s_p)
    session
    responder
    initiator
    initiator_nonce
    responder_nonce
    responder_key
    initiator_pubkey
    sent_term
    (s2p_state s_p');
  ma_nsl_protocol_transition_from_responder_reply
    (s2p_state s_p)
    session
    responder
    initiator
    sent_term
    (s2p_state s_p');
  assert ((ma_nsl_protocol key_directory).transition
    (s2p_state s_p)
    (Protocol.Observable NetSend sent_term lid)
    (s2p_state s_p'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_nsl_protocol]; zeta; iota];
        smt ());
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  ma_impl_system_observable_transition_from_protocol
    corrupt
    key_directory
    know0
    s_p
    NetSend
    lid
    sent_term
    s_p';
  ma_impl_singleton_eventually_observable
    corrupt
    key_directory
    know0
    s_p
    s_p'
    NetSend
    lid;
  assert (eventually_observable_step
    (ma_impl_system corrupt key_directory know0)
    s_p
    [TestedSystem.Observable NetSend lid]
    (ma_ideal_send_message2_impl_witness
      s_p session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_send_message2_impl_witness]; zeta; iota];
        smt ())

let ma_ideal_send_message3_impl_witness_preserves_used_nonces
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
        s_p.internal.used_nonces) =
        ()

let ma_ideal_send_message3_impl_witness_transition
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
              s_p session initiator responder responder_nonce initiator_key responder_pubkey)))) =
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
  in
  let s_p' =
    ma_ideal_send_message3_impl_witness
      s_p session initiator responder responder_nonce initiator_key responder_pubkey
  in
  assert (s2p_state s_p' ==
    ma_nsl_initiator_ack_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key)
    by (let open FStar.Tactics.V2 in
        norm [
            delta_only [
                `%ma_ideal_send_message3_impl_witness;
                `%TestedSystem.s2p_state;
                `%TestedSystem.p2s_state
              ];
            zeta;
            iota
          ];
        smt ());
  ma_nsl_initiator_ack_transition_witnesses
    (s2p_state s_p)
    session
    initiator
    responder
    responder_nonce
    initiator_key
    responder_pubkey
    sent_term
    (s2p_state s_p')

let ma_obs_bisim_observable_step_ideal_send_message3
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
    =
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let sent_term =
    ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey
  in
  let s_p' =
    ma_ideal_send_message3_impl_witness
      s_p session initiator responder responder_nonce initiator_key responder_pubkey
  in
  let lbls : list system_label = [TestedSystem.Observable NetSend lid] in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_bisim_relation]; zeta; iota];
        smt ());
  assert (ma_nsl_initiator_ack_enabled (s2p_state s_p)
    session initiator responder responder_nonce initiator_key responder_pubkey);
  assert (s2p_state s_p' ==
    ma_nsl_initiator_ack_state (s2p_state s_p)
      session initiator responder responder_nonce initiator_key);
  ma_nsl_initiator_ack_transition_witnesses
    (s2p_state s_p)
    session
    initiator
    responder
    responder_nonce
    initiator_key
    responder_pubkey
    sent_term
    (s2p_state s_p');
  assert (ma_nsl_initiator_ack_transition
    (s2p_state s_p) session initiator responder sent_term (s2p_state s_p'));
  assert ((ma_nsl_protocol key_directory).transition
    (s2p_state s_p)
    (Protocol.Observable NetSend sent_term lid)
    (s2p_state s_p'));
  assert (s_p'.know == Seq.snoc s_p.know sent_term);
  assert ((ma_impl_system corrupt key_directory know0).transitions
    s_p
    (TestedSystem.Observable NetSend lid)
    s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (multi_transitions (ma_impl_system corrupt key_directory know0).transitions s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

let ma_obs_bisim_observable_step_ideal_deliver_initiator
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_q': ideal_system_state)
    =
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let output_term = ma_authenticated_term session initiator responder in
  let s_p' = ma_ideal_deliver_initiator_impl_witness s_p session initiator responder in
  let lbls : list system_label = [TestedSystem.Observable IoSend lid] in
  assert (s2p_state s_p' == ma_nsl_initiator_output_state (s2p_state s_p) session initiator responder);
  assert (ma_nsl_initiator_output_transition
    (s2p_state s_p) session initiator responder output_term (s2p_state s_p'));
  assert ((ma_nsl_protocol key_directory).transition
    (s2p_state s_p)
    (Protocol.Observable IoSend output_term lid)
    (s2p_state s_p'));
  assert (s_p'.know == Seq.snoc s_p.know output_term);
  assert ((ma_impl_system corrupt key_directory know0).transitions
    s_p
    (TestedSystem.Observable IoSend lid)
    s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (multi_transitions (ma_impl_system corrupt key_directory know0).transitions s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())

let ma_obs_bisim_observable_step_ideal_deliver_responder
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (s_q': ideal_system_state)
    =
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let output_term = ma_authenticated_term session responder initiator in
  let s_p' = ma_ideal_deliver_responder_impl_witness s_p session responder initiator responder_key in
  let lbls : list system_label = [TestedSystem.Observable IoSend lid] in
  assert (ma_ideal_deliver_protocol_transition
    (s2p_state s_q)
    session responder initiator Responder
    output_term
    (s2p_state s_q'));
  assert (output_term == ma_authenticated_term session responder initiator);
  assert (s2p_state s_p' ==
    ma_nsl_responder_output_state (s2p_state s_p) session responder initiator responder_key);
  ma_responder_output_transition_witnesses
    (s2p_state s_p)
    session responder initiator responder_key
    output_term
    (s2p_state s_p');
  norm_spec [delta_only [`%ma_nsl_responder_output_transition]]
    (ma_nsl_responder_output_transition
      (s2p_state s_p) session responder initiator output_term (s2p_state s_p'));
  assert ((ma_nsl_protocol key_directory).transition
    (s2p_state s_p)
    (Protocol.Observable IoSend output_term lid)
    (s2p_state s_p'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_nsl_protocol_transition; `%ma_nsl_protocol]; zeta; iota];
        smt ());
  assert (s_p'.know == Seq.snoc s_p.know output_term);
  assert ((ma_impl_system corrupt key_directory know0).transitions
    s_p
    (TestedSystem.Observable IoSend lid)
    s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ());
  assert (multi_transitions (ma_impl_system corrupt key_directory know0).transitions s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%multi_transitions]; zeta; iota];
        smt ());
  assert (is_eventually_observable lbls)
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%is_eventually_observable; `%is_internal; `%lbl_to_effect]; zeta; iota];
        smt ());
  assert (eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step]; zeta; iota];
        smt ())
