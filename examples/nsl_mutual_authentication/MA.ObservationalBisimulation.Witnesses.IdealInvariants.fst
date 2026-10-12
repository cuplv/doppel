module MA.ObservationalBisimulation.Witnesses.IdealInvariants

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

open MA.IdealInvariants

open MA.TestedProtocols

open MA.ObservationalBisimulation.Witnesses


/// Lift a protocol-level internal transition to a tested-system internal
/// transition.
private
let lift_internal_transition
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (lid: ma_label_id)
    : Lemma
      (requires
        ma_ideal_protocol_transition (s2p_state s) (Protocol.Internal lid) (s2p_state s') /\
        s'.know == s.know)
      (ensures
        (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal lid) s') =
  assert ((ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal lid) s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ())


/// Lift a protocol-level observable transition to a tested-system observable
/// transition.
private
let lift_observable_transition
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (o: ma_effect)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_ideal_protocol_transition (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Observable o lid) s') =
  assert ((ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Observable o lid) s')
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%TestedSystem.transitions']; zeta; iota];
        smt ())


/// One internal step that preserves the invariant.
private
let step_internal_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (lid: ma_label_id)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s /\
        ma_ideal_protocol_transition (s2p_state s) (Protocol.Internal lid) (s2p_state s') /\
        s'.know == s.know)
      (ensures ma_ideal_system_inv corrupt key_directory s') =
  lift_internal_transition corrupt key_directory know0 s s' lid;
  ma_ideal_system_inv_preserved corrupt key_directory know0 s s' (TestedSystem.Internal lid)


/// One observable step that preserves the invariant.
private
let step_observable_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (o: ma_effect)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s /\
        ma_ideal_protocol_transition (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_ideal_system_inv corrupt key_directory s') =
  lift_observable_transition corrupt key_directory know0 s s' o lid t;
  ma_ideal_system_inv_preserved corrupt key_directory know0 s s' (TestedSystem.Observable o lid)


let ma_impl_initiator_start_ideal_witness_preserves_inv
      corrupt key_directory s_q session initiator responder initiator_nonce responder_pubkey =
  let know0 = s_q.know in
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let s_mid_p = ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator in
  let s_q_mid = p2s_state s_mid_p s_q.know in
  let sent_term =
    ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
  in
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  let s_final_p = ma_sim_send_message1_state s_mid_p session initiator responder initiator_nonce in
  // Step 1: internal `ma_ideal_initiate` transition s_q -> s_q_mid
  assert (s2p_state s_q_mid == s_mid_p);
  assert (ma_ideal_initiate_protocol_transition
    (s2p_state s_q) session initiator responder Initiator (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_initiate_protocol_transition]; zeta; iota];
        smt ());
  assert (ma_ideal_protocol_transition
    (s2p_state s_q) (Protocol.Internal lid) (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q_mid.know == s_q.know);
  step_internal_inv corrupt key_directory know0 s_q s_q_mid lid;
  // Step 2: observable `ma_sim_send_message1` transition s_q_mid -> s_q'
  assert (s2p_state s_q' == s_final_p);
  introduce exists (in': nonce) (rp': term {PubKey? rp'}).
      ma_sim_send_message1_enabled s_mid_p session initiator responder in' rp' /\
      sent_term == ma_nsl_message1_term session initiator responder in' rp' /\
      s_final_p == ma_sim_send_message1_state s_mid_p session initiator responder in'
    with initiator_nonce responder_pubkey
    and ();
  assert (ma_sim_send_message1_protocol_transition
    s_mid_p session initiator responder sent_term s_final_p);
  assert (ma_ideal_protocol_transition
    (s2p_state s_q_mid) (Protocol.Observable NetSend sent_term lid) (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q'.know == Seq.snoc s_q_mid.know sent_term);
  step_observable_inv corrupt key_directory know0 s_q_mid s_q' NetSend lid sent_term


let ma_impl_responder_reply_ideal_witness_preserves_inv
      corrupt key_directory s_q session responder initiator
      initiator_nonce responder_nonce responder_key initiator_pubkey =
  let know0 = s_q.know in
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let s_mid_p = ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder in
  let s_q_mid = p2s_state s_mid_p s_q.know in
  let sent_term =
    ma_nsl_message2_term session initiator responder initiator_nonce responder_nonce initiator_pubkey
  in
  let s_q' =
    ma_impl_responder_reply_ideal_witness
      s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey
  in
  let s_final_p =
    ma_sim_send_message2_state s_mid_p session responder initiator
      initiator_nonce responder_nonce responder_key
  in
  // Step 1: internal `ma_ideal_initiate` transition s_q -> s_q_mid
  assert (s2p_state s_q_mid == s_mid_p);
  assert (ma_ideal_initiate_protocol_transition
    (s2p_state s_q) session responder initiator Responder (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_initiate_protocol_transition]; zeta; iota];
        smt ());
  assert (ma_ideal_protocol_transition
    (s2p_state s_q) (Protocol.Internal lid) (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q_mid.know == s_q.know);
  step_internal_inv corrupt key_directory know0 s_q s_q_mid lid;
  // Step 2: observable `ma_sim_send_message2` transition s_q_mid -> s_q'
  assert (s2p_state s_q' == s_final_p);
  introduce exists (in': nonce) (rn': nonce) (rk': priv_key) (ip': term {PubKey? ip'}).
      ma_sim_send_message2_enabled s_mid_p session responder initiator in' rn' rk' ip' /\
      sent_term == ma_nsl_message2_term session initiator responder in' rn' ip' /\
      s_final_p == ma_sim_send_message2_state s_mid_p session responder initiator in' rn' rk'
    with initiator_nonce responder_nonce responder_key initiator_pubkey
    and ();
  assert (ma_sim_send_message2_protocol_transition
    s_mid_p session responder initiator sent_term s_final_p);
  assert (ma_ideal_protocol_transition
    (s2p_state s_q_mid) (Protocol.Observable NetSend sent_term lid) (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q'.know == Seq.snoc s_q_mid.know sent_term);
  step_observable_inv corrupt key_directory know0 s_q_mid s_q' NetSend lid sent_term


let ma_impl_initiator_ack_ideal_witness_preserves_inv
      corrupt key_directory s_q session initiator responder responder_nonce initiator_key responder_pubkey =
  let know0 = s_q.know in
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
  let s_final_p =
    ma_sim_send_message3_state (s2p_state s_q) session initiator responder responder_nonce initiator_key
  in
  // Single observable `ma_sim_send_message3` transition s_q -> s_q'
  assert (s2p_state s_q' == s_final_p);
  introduce exists (rn': nonce) (ik': priv_key) (rp': term {PubKey? rp'}).
      ma_sim_send_message3_enabled (s2p_state s_q) session initiator responder rn' ik' rp' /\
      sent_term == ma_nsl_message3_term session initiator responder rn' rp' /\
      s_final_p == ma_sim_send_message3_state (s2p_state s_q) session initiator responder rn' ik'
    with responder_nonce initiator_key responder_pubkey
    and ();
  assert (ma_sim_send_message3_protocol_transition
    (s2p_state s_q) session initiator responder sent_term s_final_p);
  assert (ma_ideal_protocol_transition
    (s2p_state s_q) (Protocol.Observable NetSend sent_term lid) (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q'.know == Seq.snoc s_q.know sent_term);
  step_observable_inv corrupt key_directory know0 s_q s_q' NetSend lid sent_term


let ma_impl_initiator_output_ideal_witness_preserves_inv
      corrupt key_directory s_q session initiator responder =
  let know0 = s_q.know in
  let lid : ma_label_id =
    { session = session; party = initiator; peer = responder; role = Initiator }
  in
  let output_term = ma_authenticated_term session initiator responder in
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  let s_final_p = ma_ideal_deliver_state (s2p_state s_q) session initiator responder in
  // Single observable `ma_ideal_deliver` transition s_q -> s_q'
  assert (s2p_state s_q' == s_final_p);
  assert (ma_ideal_deliver_protocol_transition
    (s2p_state s_q) session initiator responder Initiator output_term (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_deliver_protocol_transition]; zeta; iota];
        smt ());
  assert (ma_ideal_protocol_transition
    (s2p_state s_q) (Protocol.Observable IoSend output_term lid) (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q'.know == Seq.snoc s_q.know output_term);
  step_observable_inv corrupt key_directory know0 s_q s_q' IoSend lid output_term


let ma_impl_responder_output_ideal_witness_preserves_inv
      corrupt key_directory s_q session responder initiator responder_key =
  let know0 = s_q.know in
  let lid : ma_label_id =
    { session = session; party = responder; peer = initiator; role = Responder }
  in
  let s_mid_p =
    ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key
  in
  let s_q_mid = p2s_state s_mid_p s_q.know in
  let output_term = ma_authenticated_term session responder initiator in
  let s_q' =
    ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key
  in
  let s_final_p = ma_ideal_deliver_state s_mid_p session responder initiator in
  // Step 1: internal `ma_sim_receive_message3` transition s_q -> s_q_mid
  assert (s2p_state s_q_mid == s_mid_p);
  introduce exists (rk': priv_key).
      ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator rk' /\
      s_mid_p == ma_sim_receive_message3_state (s2p_state s_q) session responder initiator rk'
    with responder_key
    and ();
  assert (ma_sim_receive_message3_protocol_transition
    (s2p_state s_q) session responder initiator (s2p_state s_q_mid));
  assert (ma_ideal_protocol_transition
    (s2p_state s_q) (Protocol.Internal lid) (s2p_state s_q_mid))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q_mid.know == s_q.know);
  step_internal_inv corrupt key_directory know0 s_q s_q_mid lid;
  // Step 2: observable `ma_ideal_deliver` transition s_q_mid -> s_q'
  assert (s2p_state s_q' == s_final_p);
  assert (ma_ideal_deliver_protocol_transition
    (s2p_state s_q_mid) session responder initiator Responder output_term (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_deliver_protocol_transition]; zeta; iota];
        smt ());
  assert (ma_ideal_protocol_transition
    (s2p_state s_q_mid) (Protocol.Observable IoSend output_term lid) (s2p_state s_q'))
    by (let open FStar.Tactics.V2 in
        norm [delta_only [`%ma_ideal_protocol_transition]; zeta; iota];
        smt ());
  assert (s_q'.know == Seq.snoc s_q_mid.know output_term);
  step_observable_inv corrupt key_directory know0 s_q_mid s_q' IoSend lid output_term
