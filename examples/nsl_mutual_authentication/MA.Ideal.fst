module MA.Ideal

open SymbolicTypes

open AencTerms

open AdversaryAenc

open MA.Adversary

open MA.Types

open Bag

module Protocol = Protocol

module Set = FStar.Set

open FStar.Set.Properties

module PartialMap = FStar.PartialMap

let ma_get_sim_participant_session_state_after_update_same
			(s: ideal_proto_state)
			(participant: participant_id)
			(session: session_id)
			(session_state: sim_participant_session_state)
		: Lemma
			(ensures (
				let s' = ma_update_sim_participant_session_state s participant session session_state
				in
				ma_get_sim_participant_session_state s' participant session == Some session_state
			)) =
	()

let ma_get_sim_participant_session_state_after_update_different
			(s: ideal_proto_state)
			(participant: participant_id)
			(session: session_id)
			(session_state: sim_participant_session_state)
			(query_participant: participant_id)
			(query_session: session_id)
		: Lemma
			(requires (query_participant <> participant \/ query_session <> session))
			(ensures (
				let s' = ma_update_sim_participant_session_state s participant session session_state
				in
				ma_get_sim_participant_session_state s' query_participant query_session ==
				ma_get_sim_participant_session_state s query_participant query_session
			)) =
	()

let ma_ideal_initiate_state_preserves_key_directory
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
		: Lemma
			(ensures
				(ma_ideal_initiate_state s session party peer r).internal.key_directory ==
				s.internal.key_directory) =
	()

let ma_ideal_initiate_state_preserves_corrupt
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
		: Lemma
			(ensures
				(ma_ideal_initiate_state s session party peer r).internal.corrupt ==
				s.internal.corrupt) =
	()

let ma_ideal_initiate_state_preserves_used_nonces
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
		: Lemma
			(ensures
				(ma_ideal_initiate_state s session party peer r).internal.used_nonces ==
				s.internal.used_nonces) =
	()

let ma_ideal_initiate_state_session_requests_eq
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
			(query_session: session_id)
		: Lemma
			(ensures
				ma_session_requests (ma_ideal_initiate_state s session party peer r) query_session ==
				(if query_session = session then
					Set.add { party = party; peer = peer; role = r } (ma_session_requests s session)
				else
					ma_session_requests s query_session)) =
	()

let ma_ideal_initiate_state_preserves_get_sim_participant_session_state
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
			(query_participant: participant_id)
			(query_session: session_id)
		: Lemma
			(ensures
				ma_get_sim_participant_session_state
					(ma_ideal_initiate_state s session party peer r)
					query_participant query_session ==
				ma_get_sim_participant_session_state s query_participant query_session) =
	()

let ma_ideal_initiate_state_inputs_eq
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
		: Lemma
			(ensures
				(ma_ideal_initiate_state s session party peer r).inputs ==
				Bag.remove (ma_auth_input_term session party peer r) s.inputs) =
	()

let ma_ideal_initiate_state_ideal_to_sim_channel_eq
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
		: Lemma
			(ensures
				(ma_ideal_initiate_state s session party peer r).internal.ideal_to_sim_channel ==
				Set.add (ma_authenticating_term session party peer r) s.internal.ideal_to_sim_channel) =
	()

let ma_ideal_initiate_state_preserves_sim_to_ideal_channel
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(r: role)
		: Lemma
			(ensures
				(ma_ideal_initiate_state s session party peer r).internal.sim_to_ideal_channel ==
				s.internal.sim_to_ideal_channel) =
	()

let ma_sim_send_message1_state_preserves_inputs
			(s: ideal_proto_state)
			(session: session_id)
			(initiator responder: participant_id)
			(initiator_nonce: nonce)
		: Lemma
			(ensures
				(ma_sim_send_message1_state s session initiator responder initiator_nonce).inputs ==
				s.inputs) =
	()

let ma_sim_send_message1_state_preserves_key_directory
			(s: ideal_proto_state)
			(session: session_id)
			(initiator responder: participant_id)
			(initiator_nonce: nonce)
		: Lemma
			(ensures
				(ma_sim_send_message1_state s session initiator responder initiator_nonce).internal.key_directory ==
				s.internal.key_directory) =
	()

let ma_sim_send_message1_state_preserves_corrupt
			(s: ideal_proto_state)
			(session: session_id)
			(initiator responder: participant_id)
			(initiator_nonce: nonce)
		: Lemma
			(ensures
				(ma_sim_send_message1_state s session initiator responder initiator_nonce).internal.corrupt ==
				s.internal.corrupt) =
	()

let ma_sim_send_message1_state_preserves_used_nonces
			(s: ideal_proto_state)
			(session: session_id)
			(initiator responder: participant_id)
			(initiator_nonce: nonce)
		: Lemma
			(ensures
				(ma_sim_send_message1_state s session initiator responder initiator_nonce).internal.used_nonces ==
				Set.add initiator_nonce s.internal.used_nonces) =
	()

let ma_sim_send_message2_state_inputs_eq
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key).inputs ==
				Bag.remove (ma_nsl_message1_network_term
					session initiator responder initiator_nonce (PubKey responder_key)) s.inputs) =
	()

let ma_sim_send_message2_state_preserves_key_directory
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.key_directory ==
				s.internal.key_directory) =
	()

let ma_sim_send_message2_state_preserves_corrupt
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.corrupt ==
				s.internal.corrupt) =
	()

let ma_sim_send_message2_state_preserves_used_nonces
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.used_nonces ==
				Set.add responder_nonce s.internal.used_nonces) =
	()

let ma_sim_send_message2_state_preserves_requests
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.requests ==
				s.internal.requests) =
	()

let ma_sim_send_message2_state_preserves_sim_to_ideal_channel
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key).internal.sim_to_ideal_channel ==
				s.internal.sim_to_ideal_channel) =
	()

let ma_sim_send_message2_state_get_updated_sim_participant_session_state
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(initiator_nonce responder_nonce: nonce)
			(responder_key: priv_key)
			(query_participant: participant_id)
			(query_session: session_id)
		: Lemma
			(ensures (
				let s' = ma_sim_send_message2_state s session responder initiator initiator_nonce responder_nonce responder_key in
				if query_participant = responder && query_session = session then
					ma_get_sim_participant_session_state s' query_participant query_session ==
					Some (SimResponderSession
						{
							responder = responder;
							initiator = initiator;
							responder_nonce = responder_nonce;
							output_forwarded = false
						})
				else
					ma_get_sim_participant_session_state s' query_participant query_session ==
					ma_get_sim_participant_session_state s query_participant query_session
			)) =
	let session_state =
		SimResponderSession
			{
				responder = responder;
				initiator = initiator;
				responder_nonce = responder_nonce;
				output_forwarded = false
			}
	in
	if query_participant = responder && query_session = session then
		ma_get_sim_participant_session_state_after_update_same
			s responder session session_state
	else
		ma_get_sim_participant_session_state_after_update_different
			s responder session session_state query_participant query_session

	let ma_sim_send_message3_state_inputs_eq
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
			: Lemma
				(requires Some? (ma_sim_initiator_session_state s initiator session))
				(ensures (
					let initiator_state = Some?.v (ma_sim_initiator_session_state s initiator session) in
					(ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key).inputs ==
						Bag.remove (ma_nsl_message2_network_term
							session initiator responder initiator_state.initiator_nonce responder_nonce
							(PubKey initiator_key)) s.inputs
				)) =
		()

	let ma_sim_send_message3_state_preserves_key_directory
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
			: Lemma
				(ensures
					(ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key).internal.key_directory ==
					s.internal.key_directory) =
		()

	let ma_sim_send_message3_state_preserves_corrupt
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
			: Lemma
				(ensures
					(ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key).internal.corrupt ==
					s.internal.corrupt) =
		()

	let ma_sim_send_message3_state_preserves_used_nonces
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
			: Lemma
				(ensures
					(ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key).internal.used_nonces ==
					s.internal.used_nonces) =
		()

	let ma_sim_send_message3_state_session_requests_eq
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
				(query_session: session_id)
			: Lemma
				(ensures
					ma_session_requests
						(ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key)
						query_session ==
					ma_session_requests s query_session) =
		()

	let ma_sim_send_message3_state_get_updated_sim_participant_session_state
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
				(query_participant: participant_id)
				(query_session: session_id)
			: Lemma
				(requires Some? (ma_sim_initiator_session_state s initiator session))
				(ensures (
					let s' = ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key in
					let initiator_state = Some?.v (ma_sim_initiator_session_state s initiator session) in
					if query_participant = initiator && query_session = session then
						ma_get_sim_participant_session_state s' query_participant query_session ==
						Some (SimInitiatorSession { initiator_state with ack_sent = true })
					else
						ma_get_sim_participant_session_state s' query_participant query_session ==
						ma_get_sim_participant_session_state s query_participant query_session
				)) =
		()

	let ma_sim_send_message3_state_get_updated_sim_responder_session_state
				(s: Protocol.state term ideal_internal_state)
				(session: session_id)
				(initiator responder: participant_id)
				(responder_nonce: nonce)
				(initiator_key: priv_key)
				(query_responder: participant_id)
				(query_session: session_id)
			: Lemma
				(requires Some? (ma_sim_initiator_session_state s initiator session))
				(ensures (
					let s' = ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key in
					match ma_sim_responder_session_state s' query_responder query_session with
					| Some responder_state ->
						ma_sim_responder_session_state s query_responder query_session == Some responder_state
					| None -> True)) =
		ma_sim_send_message3_state_get_updated_sim_participant_session_state
			s session initiator responder responder_nonce initiator_key query_responder query_session;
		FStar.Tactics.Effect.assert_by_tactic
			(let s' = ma_sim_send_message3_state s session initiator responder responder_nonce initiator_key in
			match ma_sim_responder_session_state s' query_responder query_session with
			| Some responder_state ->
				ma_sim_responder_session_state s query_responder query_session == Some responder_state
			| None -> True)
			(fun _ ->
				(let open FStar.Tactics.V2 in
					norm [delta_only [`%ma_sim_responder_session_state;
											`%ma_get_sim_participant_session_state;
											`%ma_sim_send_message3_state];
							zeta; iota];
					smt ()))

		let ma_sim_receive_message3_state_session_requests_eq
					(s: Protocol.state term ideal_internal_state)
					(session: session_id)
					(responder initiator: participant_id)
					(responder_key: priv_key)
					(query_session: session_id)
				: Lemma
					(ensures
						ma_session_requests
							(ma_sim_receive_message3_state s session responder initiator responder_key)
							query_session ==
						ma_session_requests s query_session) =
			()

			let ma_sim_receive_message3_state_get_updated_sim_participant_session_state
						(s: Protocol.state term ideal_internal_state)
						(session: session_id)
						(responder initiator: participant_id)
						(responder_key: priv_key)
						(query_participant: participant_id)
						(query_session: session_id)
					: Lemma
						(requires Some? (ma_sim_responder_session_state s responder session))
						(ensures (
							let s' = ma_sim_receive_message3_state s session responder initiator responder_key in
							let responder_state = Some?.v (ma_sim_responder_session_state s responder session) in
							if query_participant = responder && query_session = session then
								ma_get_sim_participant_session_state s' query_participant query_session ==
								Some (SimResponderSession { responder_state with output_forwarded = true })
							else
								ma_get_sim_participant_session_state s' query_participant query_session ==
								ma_get_sim_participant_session_state s query_participant query_session
						)) =
				()

let ma_sim_receive_message3_state_preserves_key_directory
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_receive_message3_state s session responder initiator responder_key).internal.key_directory ==
				s.internal.key_directory) =
	()

let ma_sim_receive_message3_state_preserves_corrupt
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_receive_message3_state s session responder initiator responder_key).internal.corrupt ==
				s.internal.corrupt) =
	()

let ma_sim_receive_message3_state_preserves_used_nonces
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_receive_message3_state s session responder initiator responder_key).internal.used_nonces ==
				s.internal.used_nonces) =
	()

let ma_sim_receive_message3_state_preserves_ideal_to_sim_channel
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_receive_message3_state s session responder initiator responder_key).internal.ideal_to_sim_channel ==
				s.internal.ideal_to_sim_channel) =
	()

let ma_sim_receive_message3_state_preserves_requests
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(ensures
				(ma_sim_receive_message3_state s session responder initiator responder_key).internal.requests ==
				s.internal.requests) =
	()

let ma_sim_receive_message3_state_sim_to_ideal_channel_eq
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(requires Some? (ma_sim_responder_session_state s responder session))
			(ensures
				(ma_sim_receive_message3_state s session responder initiator responder_key).internal.sim_to_ideal_channel ==
				Set.add (ma_output_term session responder) s.internal.sim_to_ideal_channel) =
	()

let ma_sim_receive_message3_state_inputs_eq
			(s: Protocol.state term ideal_internal_state)
			(session: session_id)
			(responder initiator: participant_id)
			(responder_key: priv_key)
		: Lemma
			(requires (
				match ma_sim_responder_session_state s responder session with
				| Some rstate ->
					Bag.mem (ma_nsl_message3_network_term
						session initiator responder rstate.responder_nonce
						(PubKey responder_key)) s.inputs
				| None -> False))
			(ensures (
				let rstate = Some?.v (ma_sim_responder_session_state s responder session) in
				(ma_sim_receive_message3_state s session responder initiator responder_key).inputs ==
				Bag.remove (ma_nsl_message3_network_term
					session initiator responder rstate.responder_nonce (PubKey responder_key))
					s.inputs)) =
	()

let ma_ideal_deliver_state_preserves_inputs
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
		: Lemma
			(ensures (ma_ideal_deliver_state s session party peer).inputs == s.inputs) =
	()

let ma_ideal_deliver_state_preserves_key_directory
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
		: Lemma
			(ensures
				(ma_ideal_deliver_state s session party peer).internal.key_directory ==
				s.internal.key_directory) =
	()

let ma_ideal_deliver_state_preserves_corrupt
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
		: Lemma
			(ensures
				(ma_ideal_deliver_state s session party peer).internal.corrupt ==
				s.internal.corrupt) =
	()

let ma_ideal_deliver_state_session_requests_eq
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(query_session: session_id)
		: Lemma
			(ensures
				ma_session_requests (ma_ideal_deliver_state s session party peer) query_session ==
				ma_session_requests s query_session) =
	()

let ma_ideal_deliver_state_preserves_get_sim_participant_session_state
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
			(query_participant: participant_id)
			(query_session: session_id)
		: Lemma
			(ensures (
				let s' = ma_ideal_deliver_state s session party peer in
				ma_get_sim_participant_session_state s' query_participant query_session ==
				ma_get_sim_participant_session_state s query_participant query_session
			)) =
	()

let ma_ideal_deliver_state_preserves_used_nonces
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
		: Lemma
			(ensures
				(ma_ideal_deliver_state s session party peer).internal.used_nonces ==
				s.internal.used_nonces) =
	()

let ma_ideal_deliver_state_preserves_ideal_to_sim_channel
			(s: ideal_proto_state)
			(session: session_id)
			(party peer: participant_id)
		: Lemma
			(ensures
				(ma_ideal_deliver_state s session party peer).internal.ideal_to_sim_channel ==
				s.internal.ideal_to_sim_channel) =
	()

let ma_ideal_valid_transitions_lemma
			(s: Protocol.state term ideal_internal_state)
			(l: Protocol.label term ma_effect ma_label_id)
			(s': Protocol.state term ideal_internal_state)
		: Lemma (ma_ideal_protocol_transition s l s' ==> Bag.subset s'.inputs s.inputs) =
	match l with
	| Protocol.Observable _ _ _ -> ()
	| Protocol.Internal _ -> ()

let ma_ideal_valid_transitions s l s' =
	ma_ideal_valid_transitions_lemma s l s';
	()
