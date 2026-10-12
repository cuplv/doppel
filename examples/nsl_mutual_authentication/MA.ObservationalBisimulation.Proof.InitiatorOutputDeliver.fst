module MA.ObservationalBisimulation.Proof.InitiatorOutputDeliver

/// InitiatorOutput + IdealDeliver preservation cluster: per-family helpers (enabled/witness/iff and secrecy/inputs-match), pragma-scoped structural_clauses + output_enabled_iff, the impl_initiator_output _preserves_relation main lemma, and the two ideal_deliver_{initiator,responder} _preserves_relation lemmas.
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

let ma_impl_initiator_output_preserves_responder_reply_enabled
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      // Quantified parameters
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        ma_nsl_responder_reply_enabled (s2p_state s_p')
          quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey
        <==>
        ma_nsl_responder_reply_enabled (s2p_state s_p)
          quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey)) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  ma_nsl_initiator_output_state_preserves_freshness (s2p_state s_p) session initiator responder quant_responder_nonce;
  if quant_responder <> initiator
  then ()
  else if quant_session <> session
  then ()
  else ()

let ma_impl_initiator_output_witness_preserves_responder_reply_enabled
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      // Quantified parameters
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        ma_ideal_initiate_enabled (s2p_state s_q') quant_session quant_responder quant_initiator Responder /\
          ma_sim_send_message2_enabled
            (ma_ideal_initiate_state (s2p_state s_q') quant_session quant_responder quant_initiator Responder)
            quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey
        <==>
        ma_ideal_initiate_enabled (s2p_state s_q) quant_session quant_responder quant_initiator Responder /\
          ma_sim_send_message2_enabled
            (ma_ideal_initiate_state (s2p_state s_q) quant_session quant_responder quant_initiator Responder)
            quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey)) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  if quant_responder <> initiator
  then ()
  else if quant_session <> session
  then ()
  else ()

let ma_impl_initiator_output_preserves_responder_reply_iff
  (corrupt: Set.set participant_id)
  (key_directory: PartialMap.t participant_id priv_key)
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
      ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
      s_p'.know == Seq.snoc s_p.know output_term
    ))
    (ensures (
      let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
      ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q'
    ))
=
// The relevant state for these transitions is unchanged by the initiator output
// transitions, so the iff enabled condition is preserved.
let ma_impl_initiator_output_preserves_responder_reply_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      // Quantified parameters
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q' quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey) <==> (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey)))
    = let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
      ma_impl_initiator_output_preserves_responder_reply_enabled corrupt key_directory s_p s_q session initiator responder s_p' quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey;
      ma_impl_initiator_output_witness_preserves_responder_reply_enabled corrupt key_directory s_p s_q session initiator responder s_p' quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey
  in
  // This is the same condition as
  // `ma_impl_initiator_output_preserves_responder_reply_iff`, just with the
  // quantified variables moved into the parameters. The SMT patterns ensure it
  // is used to solve the quantified version of the lemma.
  let ma_impl_initiator_output_preserves_responder_reply_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      // Quantified parameters
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q' quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey
      ))
      // Note: the SMT pattern is much more reliable here when the
      // bi-implication is abstracted into
      // `ma_responder_reply_equivalent_transitions_enabled_iff_instance`.
      [
        SMTPat (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' (ma_impl_initiator_output_ideal_witness s_q session initiator responder) quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey);
        SMTPat (ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder (ma_authenticated_term session initiator responder) (s2p_state s_p'))
      ]
    =
      // The reply enabled iff condition holds for the pre-states (s_p, s_q) by the bisimulation relation.
      assert(ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey);
      // Since the condition holds for the pre-states, then it must also hold for the post-states.
      ma_impl_initiator_output_preserves_responder_reply_iff corrupt key_directory s_p s_q session initiator responder s_p' quant_session quant_responder quant_initiator quant_initiator_nonce quant_responder_nonce quant_responder_key quant_initiator_pubkey
  in
  ()

let ma_impl_initiator_output_preserves_initiator_start_enabled
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        ma_nsl_initiator_start_enabled (s2p_state s_p')
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey
        <==>
        ma_nsl_initiator_start_enabled (s2p_state s_p)
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) =
  ma_nsl_initiator_output_state_preserves_freshness
    (s2p_state s_p) session initiator responder quant_initiator_nonce;
  if quant_initiator <> initiator
  then ()
  else if quant_session <> session
  then ()
  else ()

let ma_impl_initiator_output_witness_preserves_initiator_start_enabled
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        ma_ideal_initiate_enabled (s2p_state s_q') quant_session quant_initiator quant_responder Initiator /\
          ma_sim_send_message1_enabled
            (ma_ideal_initiate_state (s2p_state s_q') quant_session quant_initiator quant_responder Initiator)
            quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey
        <==>
        ma_ideal_initiate_enabled (s2p_state s_q) quant_session quant_initiator quant_responder Initiator /\
          ma_sim_send_message1_enabled
            (ma_ideal_initiate_state (s2p_state s_q) quant_session quant_initiator quant_responder Initiator)
            quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey)) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  if quant_initiator <> initiator
  then ()
  else if quant_session <> session
  then ()
  else ()

let ma_impl_initiator_output_preserves_initiator_start_iff
  (corrupt: Set.set participant_id)
  (key_directory: PartialMap.t participant_id priv_key)
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
      ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
      s_p'.know == Seq.snoc s_p.know output_term
    ))
    (ensures (
      let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
      ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q'
    ))
=
  let ma_impl_initiator_output_preserves_initiator_start_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q' quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey) <==>
        (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey)))
    =
      ma_impl_initiator_output_preserves_initiator_start_enabled corrupt key_directory s_p s_q
        session initiator responder s_p' quant_session quant_initiator quant_responder
        quant_initiator_nonce quant_responder_pubkey;
      ma_impl_initiator_output_witness_preserves_initiator_start_enabled corrupt key_directory s_p s_q
        session initiator responder s_p' quant_session quant_initiator quant_responder
        quant_initiator_nonce quant_responder_pubkey
  in
  let ma_impl_initiator_output_preserves_initiator_start_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey
      ))
      [
        SMTPat (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' (ma_impl_initiator_output_ideal_witness s_q session initiator responder) quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey);
        SMTPat (ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder (ma_authenticated_term session initiator responder) (s2p_state s_p'))
      ]
    =
      assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_initiator quant_responder quant_initiator_nonce quant_responder_pubkey);
      ma_impl_initiator_output_preserves_initiator_start_iff corrupt key_directory s_p s_q
        session initiator responder s_p' quant_session quant_initiator quant_responder
        quant_initiator_nonce quant_responder_pubkey
  in
  ()

let ma_impl_initiator_output_preserves_responder_output_enabled
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        ma_nsl_responder_output_enabled (s2p_state s_p')
          quant_session quant_responder quant_initiator quant_responder_key
        <==>
        ma_nsl_responder_output_enabled (s2p_state s_p)
          quant_session quant_responder quant_initiator quant_responder_key) =
  if quant_responder <> initiator
  then ()
  else if quant_session <> session
  then ()
  else ()

let ma_impl_initiator_output_witness_preserves_responder_output_enabled
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        ma_sim_receive_message3_enabled (s2p_state s_q') quant_session quant_responder quant_initiator quant_responder_key /\
          ma_ideal_deliver_enabled
            (ma_sim_receive_message3_state (s2p_state s_q') quant_session quant_responder quant_initiator quant_responder_key)
            quant_session quant_responder quant_initiator Responder
        <==>
        ma_sim_receive_message3_enabled (s2p_state s_q) quant_session quant_responder quant_initiator quant_responder_key /\
          ma_ideal_deliver_enabled
            (ma_sim_receive_message3_state (s2p_state s_q) quant_session quant_responder quant_initiator quant_responder_key)
            quant_session quant_responder quant_initiator Responder)) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  if quant_responder <> initiator
  then ()
  else if quant_session <> session
  then ()
  else ()

let ma_impl_initiator_output_preserves_responder_output_iff
  (corrupt: Set.set participant_id)
  (key_directory: PartialMap.t participant_id priv_key)
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
      ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
      s_p'.know == Seq.snoc s_p.know output_term
    ))
    (ensures (
      let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
      ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q'
    ))
=
  let ma_impl_initiator_output_preserves_responder_output_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q' quant_session quant_responder quant_initiator quant_responder_key) <==>
        (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q quant_session quant_responder quant_initiator quant_responder_key)))
    =
      ma_impl_initiator_output_preserves_responder_output_enabled corrupt key_directory s_p s_q
        session initiator responder s_p' quant_session quant_responder quant_initiator
        quant_responder_key;
      ma_impl_initiator_output_witness_preserves_responder_output_enabled corrupt key_directory s_p s_q
        session initiator responder s_p' quant_session quant_responder quant_initiator
        quant_responder_key
  in
  let ma_impl_initiator_output_preserves_responder_output_iff_instance
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures (
        let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
        ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_responder_key
      ))
      [
        SMTPat (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' (ma_impl_initiator_output_ideal_witness s_q session initiator responder) quant_session quant_responder quant_initiator quant_responder_key);
        SMTPat (ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder (ma_authenticated_term session initiator responder) (s2p_state s_p'))
      ]
    =
      assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q
        quant_session quant_responder quant_initiator quant_responder_key);
      ma_impl_initiator_output_preserves_responder_output_iff corrupt key_directory s_p s_q
        session initiator responder s_p' quant_session quant_responder quant_initiator
        quant_responder_key
  in
  ()



(**
  Secrecy preservation for implementation initiator-output and its ideal
  witness.  The observed authenticated output is public and contains only the
  session id and participant ids, so the public-output derivability corollaries
  reduce any private-key or nonce derivation from the post-knowledge back to the
  corresponding pre-knowledge.
*)
let ma_impl_initiator_output_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
        ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know output_term))
      (ensures ma_private_keys_not_derivable corrupt key_directory s_p') =
  let impl_private_helper (participant: participant_id) (k: priv_key) (d: derivation)
      : Lemma
        (ensures
          PartialMap.sel key_directory participant == Some k /\
          not (Set.mem participant corrupt) ==>
          not (derive d s_p'.know = Some (PrivKey k))) =
    if PartialMap.sel key_directory participant = Some k && not (Set.mem participant corrupt) then
      if derive d s_p'.know = Some (PrivKey k) then
        (private_keys_learned_from_public_output_already_derivable
          s_p.know session initiator responder k d;
         FStar.Tactics.Effect.assert_by_tactic False
          (fun _ ->
              (let open FStar.Tactics.V2 in
                norm [delta_only [`%ma_bisim_relation;
                                  `%ma_private_keys_not_derivable;
                                  `%derivable];
                      zeta; iota];
                smt ())))
  in
  FStar.Classical.forall_intro_3 impl_private_helper;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p')


#push-options ""
let ma_impl_initiator_output_preserves_structural_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        (let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
          ma_same_knowledge s_p' s_q' /\ ma_same_key_directory key_directory s_p' s_q' /\
          ma_same_inputs s_p' s_q' /\ ma_same_used_nonces s_p' s_q' /\
          ma_initiator_session_correspondence s_p' s_q' /\
          ma_responder_session_correspondence s_p' s_q')) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  assert (ma_same_knowledge s_p s_q /\
      ma_same_key_directory key_directory s_p s_q /\ ma_same_inputs s_p s_q /\
      ma_initiator_session_correspondence s_p s_q /\ ma_responder_session_correspondence s_p s_q
    );
  assert (s2p_state s_p' == ma_nsl_initiator_output_state (s2p_state s_p) session initiator responder);
  assert (ma_same_knowledge s_p' s_q');
  assert (ma_same_key_directory key_directory s_p' s_q');
  assert (ma_same_inputs s_p' s_q');
  assert (ma_same_used_nonces s_p' s_q');
  ma_impl_initiator_output_ideal_witness_preserves_sim_participant_sessions
    s_q session initiator responder;
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
        initiator_state.ack_sent == sim_state.ack_sent)));
      assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session)) ;
      ma_nsl_initiator_output_state_preserves_get_participant_session_state
        (s2p_state s_p) session initiator responder query_initiator query_session;
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
        responder_state.output_sent == sim_state.output_forwarded)));
      assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session)) ;
      ma_nsl_initiator_output_state_preserves_get_participant_session_state
        (s2p_state s_p) session initiator responder query_responder query_session;
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
  assert (ma_same_knowledge s_p' s_q' /\
      ma_same_key_directory key_directory s_p' s_q' /\ ma_same_inputs s_p' s_q' /\
      ma_initiator_session_correspondence s_p' s_q' /\ ma_responder_session_correspondence s_p' s_q'
    )

#pop-options

let ma_impl_initiator_output_preserves_output_enabled_iff
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term /\
          ma_same_knowledge s_p'
            (ma_impl_initiator_output_ideal_witness s_q session initiator responder) /\
          ma_same_key_directory key_directory
            s_p'
            (ma_impl_initiator_output_ideal_witness s_q session initiator responder) /\
          ma_same_inputs s_p'
            (ma_impl_initiator_output_ideal_witness s_q session initiator responder) /\
          ma_initiator_session_correspondence s_p'
            (ma_impl_initiator_output_ideal_witness s_q session initiator responder) /\
          ma_responder_session_correspondence s_p'
            (ma_impl_initiator_output_ideal_witness s_q session initiator responder)))
      (ensures
        ma_initiator_output_equivalent_transitions_enabled_iff s_p'
          (ma_impl_initiator_output_ideal_witness s_q session initiator responder)) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  // Extract the iff at (s_p, s_q) from the bisimulation relation so that the
  // SMT solver has it as a usable fact (rather than buried inside the
  // unfolded ma_bisim_relation).
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p
        s_q);
  let initiator_output_equiv (session': session_id) (initiator' responder': participant_id)
      : Lemma
      (ma_nsl_initiator_output_enabled (s2p_state s_p') session' initiator' responder' <==>
        ma_ideal_deliver_enabled (s2p_state s_q') session' initiator' responder' Initiator) =
    // Use the iff at (s_p, s_q) for this specific (session', initiator',
    // responder'); the iff at (s_p', s_q') then follows from observing that
    // both sides only change for (sess'=session, init'=initiator), where they
    // both become False after the step.
    let h_initiator_output_equiv
      : squash (ma_initiator_output_equivalent_transitions_enabled_iff s_p s_q) = ()
    in
    let h_session = FStar.Classical.Sugar.forall_elim session' h_initiator_output_equiv in
    let h_initiator = FStar.Classical.Sugar.forall_elim initiator' h_session in
    let _h_instance
      : squash (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q session' initiator' responder')
      = FStar.Classical.Sugar.forall_elim responder' h_initiator
    in
    assert (ma_nsl_initiator_output_enabled (s2p_state s_p)
          session'
          initiator'
          responder' <==>
        ma_ideal_deliver_enabled (s2p_state s_q) session' initiator' responder' Initiator);
    assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session));
    if session' = session && initiator' = initiator
    then
      (assert (~(ma_nsl_initiator_output_enabled (s2p_state s_p')
                session'
                initiator'
                responder'));
        assert (~(ma_ideal_deliver_enabled (s2p_state s_q')
                session'
                initiator'
                responder'
                Initiator)))
    else
      // Outside (session, initiator), neither participant_sessions[init'][sess']
      // nor sim_to_ideal_channel's Output(sess', init') membership changes.
      (ma_nsl_initiator_output_state_preserves_get_participant_session_state
          (s2p_state s_p) session initiator responder initiator' session';
      assert (ma_nsl_initiator_output_enabled (s2p_state s_p')
              session'
              initiator'
              responder' <==>
            ma_nsl_initiator_output_enabled (s2p_state s_p) session' initiator' responder');
        assert (ma_ideal_deliver_enabled (s2p_state s_q')
              session'
              initiator'
              responder'
              Initiator <==>
            ma_ideal_deliver_enabled (s2p_state s_q) session' initiator' responder' Initiator))
  in
  let initiator_output_equiv_all (session': session_id)
      : Lemma
      (forall (initiator': participant_id) (responder': participant_id).
          ma_nsl_initiator_output_enabled (s2p_state s_p') session' initiator' responder' <==>
          ma_ideal_deliver_enabled (s2p_state s_q') session' initiator' responder' Initiator) =
    FStar.Classical.forall_intro_2 (initiator_output_equiv session')
  in
  FStar.Classical.forall_intro initiator_output_equiv_all;
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p'
        s_q')


let ma_obs_bisim_observable_step_impl_initiator_output_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_nsl_initiator_output_transition (s2p_state s_p) session initiator responder output_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know output_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          s_p'
          (ma_impl_initiator_output_ideal_witness s_q session initiator responder)) =
  let s_q' = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  ma_impl_initiator_output_preserves_structural_clauses corrupt key_directory
    s_p
    s_q
    session
    initiator
    responder
    s_p';
  ma_impl_initiator_output_preserves_output_enabled_iff corrupt key_directory
    s_p
    s_q
    session
    initiator
    responder
    s_p';
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p s_q
    );
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p'
        s_q');
  // -----------------------------------------------------------------------
  ma_impl_initiator_output_preserves_responder_reply_iff corrupt key_directory
    s_p
    s_q
    session
    initiator
    responder
    s_p';
  ma_impl_initiator_output_preserves_initiator_start_iff corrupt key_directory
    s_p
    s_q
    session
    initiator
    responder
    s_p';
  ma_impl_initiator_output_preserves_responder_output_iff corrupt key_directory
    s_p
    s_q
    session
    initiator
    responder
    s_p';
  let output_term = ma_authenticated_term session initiator responder in
  ma_knowledge_nonces_snoc s_p.know output_term;
  ma_knowledge_nonces_snoc s_q.know output_term;
  FStar.Tactics.Effect.assert_by_tactic (Set.equal (ma_term_nonces output_term) Set.empty)
    (fun _ ->
        (let open FStar.Tactics.V2 in
          norm [delta_only [`%ma_authenticated_term; `%ma_term_nonces]; zeta; iota];
          smt ()));
  assert (ma_impl_used_nonces_invariant s_p /\ ma_ideal_used_nonces_invariant s_q);
  assert (Some? (ma_initiator_session_state (s2p_state s_p) initiator session));
  ma_knowledge_nonces_snoc_empty_preserves_subset s_p.know output_term s_p.internal.used_nonces;
  ma_knowledge_nonces_snoc_empty_preserves_subset s_q.know output_term s_q.internal.used_nonces;
  let impl_stored_helper
        (query_participant: participant_id)
        (query_session: session_id)
        (n: nonce)
      : Lemma
        (ensures
          (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
          | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
          | None -> True)) =
    assert (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
       | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
       | None -> True)
  in
  FStar.Classical.forall_intro_3 impl_stored_helper;
  let ideal_stored_helper
        (query_participant: participant_id)
        (query_session: session_id)
        (n: nonce)
      : Lemma
        (ensures
          (match PartialMap.sel (ma_sim_participant_sessions (s2p_state s_q') query_participant) query_session with
          | Some (SimInitiatorSession initiator_state) ->
            initiator_state.initiator_nonce == n ==> Set.mem n s_q'.internal.used_nonces
          | Some (SimResponderSession responder_state) ->
            responder_state.responder_nonce == n ==> Set.mem n s_q'.internal.used_nonces
          | None -> True)) =
    assert (match PartialMap.sel (ma_sim_participant_sessions (s2p_state s_q') query_participant) query_session with
       | Some (SimInitiatorSession initiator_state) ->
         initiator_state.initiator_nonce == n ==> Set.mem n s_q'.internal.used_nonces
       | Some (SimResponderSession responder_state) ->
         responder_state.responder_nonce == n ==> Set.mem n s_q'.internal.used_nonces
       | None -> True)
  in
  FStar.Classical.forall_intro_3 ideal_stored_helper;
  assert (ma_impl_used_nonces_invariant s_p');
  assert (ma_ideal_used_nonces_invariant s_q');
  ma_impl_initiator_output_preserves_secrecy_clauses
    corrupt key_directory s_p s_q session initiator responder s_p';
  // Discharge the ideal-side post-state invariant via the single-step
  // preservation lemma (which chains `ma_ideal_system_inv_preserved`).
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p s_q);
  assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance
    s_p s_q session initiator responder);
  assert (ma_ideal_deliver_enabled (s2p_state s_q) session initiator responder Initiator);
  ma_impl_initiator_output_ideal_witness_preserves_inv
    corrupt key_directory s_q session initiator responder;
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')


let ma_obs_bisim_observable_step_ideal_deliver_initiator_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let output_term = ma_authenticated_term session initiator responder in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_output_enabled (s2p_state s_p) session initiator responder /\
          ma_ideal_deliver_protocol_transition (s2p_state s_q) session initiator responder Initiator output_term (s2p_state s_q') /\
          s_q'.know == Seq.snoc s_q.know output_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          (ma_ideal_deliver_initiator_impl_witness s_p session initiator responder)
          s_q') =
  let output_term = ma_authenticated_term session initiator responder in
  let s_p' = ma_ideal_deliver_initiator_impl_witness s_p session initiator responder in
  let s_q_w = ma_impl_initiator_output_ideal_witness s_q session initiator responder in
  assert (ma_nsl_initiator_output_transition (s2p_state s_p)
        session
        initiator
        responder
        output_term
        (s2p_state s_p'));
  assert (s_p'.know == Seq.snoc s_p.know output_term);
  ma_obs_bisim_observable_step_impl_initiator_output_preserves_relation corrupt key_directory
    s_p
    s_q
    session
    initiator
    responder
    s_p';
  assert (s_q' == s_q_w);
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')




/// =========================================================================
/// Input-step preservation and up-to-partitions proof skeleton
/// =========================================================================
