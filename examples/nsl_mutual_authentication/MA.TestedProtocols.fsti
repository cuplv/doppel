module MA.TestedProtocols



/// Definitions of the tested systems for the NSL mutual authentication protocol

open AdversaryAenc
open AencTerms
open SymbolicTypes

open MA.Adversary
open MA.Ideal
open MA.NSL
open MA.Types

module PartialMap = FStar.PartialMap

/// MA tested systems: implementation and ideal protocol paired with the
/// asymmetric encryption adversary.

let ma_impl_system
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : TestedSystem.system_t #term
      #ma_effect
      #ma_label_id
      #impl_internal_state
      #adversary_aenc
      #know0 =
  TestedSystem.system adversary_aenc
    (ma_nsl_protocol_with_used_nonces key_directory (ma_knowledge_nonces know0))
    know0

let ma_ideal_system
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : TestedSystem.system_t #term
      #ma_effect
      #ma_label_id
      #ideal_internal_state
      #adversary_aenc
      #know0 =
  TestedSystem.system adversary_aenc
    (ma_ideal_protocol_with_knowledge key_directory corrupt know0)
    know0

(** Type aliases to simplify tested system types *)
type impl_system_state = TestedSystem.state term impl_internal_state
type ideal_system_state = TestedSystem.state term ideal_internal_state
type impl_system_transition = TestedSystem.transitions_t term ma_effect ma_label_id impl_internal_state adversary_aenc
type ideal_system_transition = TestedSystem.transitions_t term ma_effect ma_label_id ideal_internal_state adversary_aenc
type system_label = TestedSystem.label term ma_effect ma_label_id adversary_aenc
