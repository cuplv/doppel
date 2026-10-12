module MA.ObservationalBisimulation.Proof.MessageDerivability

/// Leaf lemmas about derivability of NSL message terms and the nonces
/// they use. Pure derivability/nonce facts with no dependence on other
/// preservation lemmas. Reused across multiple `_preserves_*` families.
///
/// Verification time: ~5s

open SymbolicTypes
open AencTerms
open AdversaryAenc
open MA.NSL
open MA.Ideal
open MA.Adversary
open MA.Types
open StaticEquivalence
open TestedSystem
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

let ma_message1_term_nonces_are_used_from_nonce
      (used_nonces: Set.set nonce)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires Set.mem initiator_nonce used_nonces)
      (ensures
        ma_term_nonces_are_used used_nonces
          (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey)) =
  assert (ma_term_nonces_are_used used_nonces
      (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey))


let ma_message2_term_nonces_are_used_from_message1_input
      (used_nonces: Set.set nonce)
      (inputs: bag term)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : Lemma
      (requires
        ma_inputs_nonces_are_used used_nonces inputs /\
        Bag.mem (ma_nsl_message1_network_term
          session initiator responder initiator_nonce (PubKey responder_key)) inputs /\
        Set.mem responder_nonce used_nonces)
      (ensures
        ma_term_nonces_are_used used_nonces
          (ma_nsl_message2_term
            session initiator responder initiator_nonce responder_nonce initiator_pubkey)) =
  assert (ma_term_nonces_are_used used_nonces
      (ma_nsl_message2_term
        session initiator responder initiator_nonce responder_nonce initiator_pubkey))


let ma_message3_network_term_not_message2_network_term
      (message3_session: session_id)
      (message3_initiator message3_responder: participant_id)
      (message3_responder_nonce: nonce)
      (message3_responder_pubkey: term {PubKey? message3_responder_pubkey})
      (message2_session: session_id)
      (message2_initiator message2_responder: participant_id)
      (message2_initiator_nonce message2_responder_nonce: nonce)
      (message2_initiator_pubkey: term {PubKey? message2_initiator_pubkey})
    : Lemma
      (ensures
        ma_nsl_message3_network_term
          message3_session message3_initiator message3_responder
          message3_responder_nonce message3_responder_pubkey <>
        ma_nsl_message2_network_term
          message2_session message2_initiator message2_responder
          message2_initiator_nonce message2_responder_nonce message2_initiator_pubkey) =
  assert (ma_nsl_message3_network_term
      message3_session message3_initiator message3_responder
      message3_responder_nonce message3_responder_pubkey <>
     ma_nsl_message2_network_term
      message2_session message2_initiator message2_responder
      message2_initiator_nonce message2_responder_nonce message2_initiator_pubkey)


let ma_message3_term_nonces_are_used_from_message2_input
      (used_nonces: Set.set nonce)
      (inputs: bag term)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_inputs_nonces_are_used used_nonces inputs /\
        Bag.mem
          (ma_nsl_message2_network_term
            session initiator responder initiator_nonce responder_nonce
            (PubKey initiator_key))
          inputs)
      (ensures
        ma_term_nonces_are_used used_nonces
          (ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey)) =
  assert (ma_term_nonces_are_used used_nonces
      (ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey))


