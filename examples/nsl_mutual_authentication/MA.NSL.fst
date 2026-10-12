module MA.NSL

open SymbolicTypes

open AencTerms

open MA.Types

open Bag

module Protocol = Protocol

module Set = FStar.Set

let ma_get_participant_session_state_after_update_same
      (s: impl_proto_state)
      (participant: participant_id)
      (session: session_id)
      (session_state: participant_session_state)
    : Lemma
      (ensures (
        let s' = ma_update_participant_session_state s participant session session_state
        in
        ma_get_participant_session_state s' participant session == Some session_state
      )) =
      ()

let ma_get_participant_session_state_after_update_different
      (s: impl_proto_state)
      (participant: participant_id)
      (session: session_id)
      (session_state: participant_session_state)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (requires (query_participant <> participant \/ query_session <> session))
      (ensures (
        let s' = ma_update_participant_session_state s participant session session_state
        in
        ma_get_participant_session_state s' query_participant query_session ==
        ma_get_participant_session_state s query_participant query_session
      )) =
  ()

let ma_nsl_initiator_start_state_inputs_eq
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
    : Lemma
      (ensures
        (ma_nsl_initiator_start_state s session initiator responder initiator_nonce).inputs ==
        Bag.remove (ma_auth_input_term session initiator responder Initiator) s.inputs) =
  ()

let ma_nsl_initiator_start_state_preserves_key_directory
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
    : Lemma
      (ensures
        (ma_nsl_initiator_start_state s session initiator responder initiator_nonce).internal.key_directory ==
        s.internal.key_directory) =
  ()

let ma_nsl_initiator_start_state_preserves_used_nonces
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
    : Lemma
      (ensures
        (ma_nsl_initiator_start_state s session initiator responder initiator_nonce).internal.used_nonces ==
        Set.add initiator_nonce s.internal.used_nonces) =
  ()

let ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures (
        let s' = ma_nsl_initiator_start_state s session initiator responder initiator_nonce in
        if query_participant = initiator && query_session = session then
          ma_get_participant_session_state s' query_participant query_session ==
          Some (InitiatorSession
            {
              initiator = initiator;
              responder = responder;
              initiator_nonce = initiator_nonce;
              ack_sent = false;
              output_sent = false
            })
        else
          ma_get_participant_session_state s' query_participant query_session ==
          ma_get_participant_session_state s query_participant query_session
      )) =
  let session_state =
    InitiatorSession
      {
        initiator = initiator;
        responder = responder;
        initiator_nonce = initiator_nonce;
        ack_sent = false;
        output_sent = false
      }
  in
  if query_participant = initiator && query_session = session then
    ma_get_participant_session_state_after_update_same
      s initiator session session_state
  else
    ma_get_participant_session_state_after_update_different
      s initiator session session_state query_participant query_session

let ma_nsl_responder_reply_state_inputs_eq
      (s: impl_proto_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (ma_nsl_responder_reply_state s session responder initiator initiator_nonce responder_nonce responder_key).inputs ==
        Bag.remove (ma_auth_input_term session responder initiator Responder)
          (Bag.remove (ma_nsl_message1_network_term
            session initiator responder initiator_nonce (PubKey responder_key))
            s.inputs)) =
  ()

let ma_nsl_responder_reply_state_preserves_key_directory
      (s: impl_proto_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (ma_nsl_responder_reply_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.key_directory ==
        s.internal.key_directory) =
  ()

let ma_nsl_responder_reply_state_preserves_used_nonces
      (s: impl_proto_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
    : Lemma
      (ensures
        (ma_nsl_responder_reply_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.used_nonces ==
        Set.add responder_nonce s.internal.used_nonces) =
  ()

let ma_nsl_responder_reply_state_get_updated_participant_session_state
      (s: impl_proto_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (ensures (
        let s' = ma_nsl_responder_reply_state s session responder initiator initiator_nonce responder_nonce responder_key in
        if query_participant = responder && query_session = session then
          ma_get_participant_session_state s' query_participant query_session ==
          Some (ResponderSession
            {
              responder = responder;
              initiator = initiator;
              responder_nonce = responder_nonce;
              output_sent = false
            })
        else
          ma_get_participant_session_state s' query_participant query_session ==
          ma_get_participant_session_state s query_participant query_session
      )) =
  let session_state =
    ResponderSession
      {
        responder = responder;
        initiator = initiator;
        responder_nonce = responder_nonce;
        output_sent = false
      }
  in
  if query_participant = responder && query_session = session then
    ma_get_participant_session_state_after_update_same
      s responder session session_state
  else
    ma_get_participant_session_state_after_update_different
      s responder session session_state query_participant query_session

let ma_nsl_initiator_ack_state_inputs_eq
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
    : Lemma
      (requires Some? (ma_initiator_session_state s initiator session))
      (ensures (
        let initiator_state = Some?.v (ma_initiator_session_state s initiator session) in
        (ma_nsl_initiator_ack_state s session initiator responder responder_nonce initiator_key).inputs ==
          Bag.remove (ma_nsl_message2_network_term
            session initiator responder initiator_state.initiator_nonce responder_nonce
            (PubKey initiator_key)) s.inputs
      )) =
  ()

let ma_nsl_initiator_ack_state_preserves_key_directory
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
    : Lemma
      (ensures
        (ma_nsl_initiator_ack_state s session initiator responder responder_nonce initiator_key).internal.key_directory ==
        s.internal.key_directory) =
  ()

      let ma_nsl_initiator_ack_state_preserves_used_nonces
        (s: impl_proto_state)
        (session: session_id)
        (initiator responder: participant_id)
        (responder_nonce: nonce)
        (initiator_key: priv_key)
          : Lemma
        (ensures
          (ma_nsl_initiator_ack_state s session initiator responder responder_nonce initiator_key).internal.used_nonces ==
          s.internal.used_nonces) =
        ()

let ma_nsl_initiator_ack_state_get_updated_participant_session_state
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (requires Some? (ma_initiator_session_state s initiator session))
      (ensures (
        let s' = ma_nsl_initiator_ack_state s session initiator responder responder_nonce initiator_key in
        let initiator_state = Some?.v (ma_initiator_session_state s initiator session) in
        if query_participant = initiator && query_session = session then
          ma_get_participant_session_state s' query_participant query_session ==
          Some (InitiatorSession { initiator_state with ack_sent = true })
        else
          ma_get_participant_session_state s' query_participant query_session ==
          ma_get_participant_session_state s query_participant query_session
      )) =
  ()

let ma_nsl_initiator_output_state_preserves_inputs
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures (ma_nsl_initiator_output_state s session initiator responder).inputs == s.inputs) =
  ()

let ma_nsl_initiator_output_state_preserves_key_directory
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (ensures
        (ma_nsl_initiator_output_state s session initiator responder).internal.key_directory ==
        s.internal.key_directory) =
  ()

let ma_nsl_initiator_output_state_preserves_get_participant_session_state
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (requires Some? (ma_initiator_session_state s initiator session))
      (ensures (
        let s' = ma_nsl_initiator_output_state s session initiator responder in
        let initiator_state = Some?.v (ma_initiator_session_state s initiator session) in
        if query_participant = initiator && query_session = session then
            ma_get_participant_session_state s' query_participant query_session ==
              Some (InitiatorSession { initiator_state with output_sent = true })
        else
          ma_get_participant_session_state s' query_participant query_session ==
          ma_get_participant_session_state s query_participant query_session
      )) =
  ()

let ma_nsl_initiator_output_state_preserves_freshness
      (s: impl_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (fresh_nonce: nonce)
  : Lemma
    (requires Some? (ma_initiator_session_state s initiator session))
    (ensures (
      let s' = ma_nsl_initiator_output_state s session initiator responder in
      ma_nsl_nonce_is_fresh s' fresh_nonce <==> ma_nsl_nonce_is_fresh s fresh_nonce
    )) =
  let s' = ma_nsl_initiator_output_state s session initiator responder in
  assert (s'.inputs == s.inputs);
  assert (forall participant sid. participant <> initiator ==> ma_get_participant_session_state s' participant sid == ma_get_participant_session_state s participant sid);
  assert (forall participant sid. sid <> session ==> ma_get_participant_session_state s' participant sid == ma_get_participant_session_state s participant sid);
  ()

let ma_nsl_responder_output_state_preserves_get_participant_session_state
      (s: impl_proto_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
      (query_participant: participant_id)
      (query_session: session_id)
    : Lemma
      (requires Some? (ma_responder_session_state s responder session))
      (ensures (
        let s' = ma_nsl_responder_output_state s session responder initiator responder_key in
        let responder_state = Some?.v (ma_responder_session_state s responder session) in
        if query_participant = responder && query_session = session then
          ma_get_participant_session_state s' query_participant query_session ==
          Some (ResponderSession { responder_state with output_sent = true })
        else
          ma_get_participant_session_state s' query_participant query_session ==
          ma_get_participant_session_state s query_participant query_session
      )) =
  ()

let ma_nsl_valid_transitions_lemma
      (s: Protocol.state term impl_internal_state)
      (l: Protocol.label term ma_effect ma_label_id)
      (s': Protocol.state term impl_internal_state)
    : Lemma (ma_nsl_protocol_transition s l s' ==> Bag.subset s'.inputs s.inputs) =
  match l with
  | Protocol.Observable _ _ _ -> ()
  | Protocol.Internal _ -> ()

let ma_nsl_valid_transitions s l s' =
  ma_nsl_valid_transitions_lemma s l s';
  ()
