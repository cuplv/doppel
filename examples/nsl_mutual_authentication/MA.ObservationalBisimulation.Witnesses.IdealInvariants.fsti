module MA.ObservationalBisimulation.Witnesses.IdealInvariants

/// Invariant-preservation lemmas for the ideal witness state functions.
///
/// For each of the five `ma_impl_*_ideal_witness` state functions declared in
/// `MA.ObservationalBisimulation.Witnesses`, this module proves that, given the
/// enabledness preconditions of the underlying ideal+simulator transition(s),
/// the witness state preserves the `ma_ideal_system_inv` invariant owned by
/// `MA.IdealInvariants`.
///
/// Each witness corresponds to one or two ideal protocol steps; the proofs
/// chain `ma_ideal_system_inv_preserved` once per step.

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


/// `ma_impl_initiator_start_ideal_witness` corresponds to
/// `ma_ideal_initiate` (Initiator) followed by `ma_sim_send_message1`.
val ma_impl_initiator_start_ideal_witness_preserves_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s_q /\
        ma_ideal_initiate_enabled (s2p_state s_q) session initiator responder Initiator /\
        ma_sim_send_message1_enabled
          (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
          session initiator responder initiator_nonce responder_pubkey)
      (ensures
        ma_ideal_system_inv corrupt key_directory
          (ma_impl_initiator_start_ideal_witness
            s_q session initiator responder initiator_nonce responder_pubkey))


/// `ma_impl_responder_reply_ideal_witness` corresponds to
/// `ma_ideal_initiate` (Responder) followed by `ma_sim_send_message2`.
val ma_impl_responder_reply_ideal_witness_preserves_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s_q /\
        ma_ideal_initiate_enabled (s2p_state s_q) session responder initiator Responder /\
        ma_sim_send_message2_enabled
          (ma_ideal_initiate_state (s2p_state s_q) session responder initiator Responder)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)
      (ensures
        ma_ideal_system_inv corrupt key_directory
          (ma_impl_responder_reply_ideal_witness
            s_q session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey))


/// `ma_impl_initiator_ack_ideal_witness` corresponds to a single
/// `ma_sim_send_message3` step.
val ma_impl_initiator_ack_ideal_witness_preserves_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s_q /\
        ma_sim_send_message3_enabled
          (s2p_state s_q) session initiator responder responder_nonce initiator_key responder_pubkey)
      (ensures
        ma_ideal_system_inv corrupt key_directory
          (ma_impl_initiator_ack_ideal_witness
            s_q session initiator responder responder_nonce initiator_key responder_pubkey))


/// `ma_impl_initiator_output_ideal_witness` corresponds to a single
/// `ma_ideal_deliver` step (Initiator).
val ma_impl_initiator_output_ideal_witness_preserves_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s_q /\
        ma_ideal_deliver_enabled (s2p_state s_q) session initiator responder Initiator)
      (ensures
        ma_ideal_system_inv corrupt key_directory
          (ma_impl_initiator_output_ideal_witness s_q session initiator responder))


/// `ma_impl_responder_output_ideal_witness` corresponds to
/// `ma_sim_receive_message3` followed by `ma_ideal_deliver` (Responder).
val ma_impl_responder_output_ideal_witness_preserves_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_key: priv_key)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s_q /\
        ma_sim_receive_message3_enabled (s2p_state s_q) session responder initiator responder_key /\
        ma_ideal_deliver_enabled
          (ma_sim_receive_message3_state (s2p_state s_q) session responder initiator responder_key)
          session responder initiator Responder)
      (ensures
        ma_ideal_system_inv corrupt key_directory
          (ma_impl_responder_output_ideal_witness s_q session responder initiator responder_key))
