module SMD.TestedProtocols



/// Definitions of the tested systems for the SMD protocol

open AdversarySenc
open SencTerms
open SymbolicTypes

open SMD.Adversary
open SMD.Ideal
open SMD.Implementation
open SMD.Types

/// SMD tested systems: impl and ideal paired with the senc adversary

let smd_impl_system (k: key) (know0: knowledge term)
    : TestedSystem.system_t #term
      #smd_effect
      #session_id
      #impl_internal_state
      #adversary_senc
      #know0 = TestedSystem.system adversary_senc (smd_impl_protocol k) know0

let smd_ideal_system (k: key) (know0: knowledge term)
    : TestedSystem.system_t #term
      #smd_effect
      #session_id
      #ideal_internal_state
      #adversary_senc
      #know0 = TestedSystem.system adversary_senc (smd_ideal_protocol k) know0

(** Type aliases to simplify tested system types *)
type impl_system_state = TestedSystem.state term impl_internal_state
type ideal_system_state = TestedSystem.state term ideal_internal_state
type impl_system_transition = TestedSystem.transitions_t term smd_effect session_id impl_internal_state adversary_senc
type ideal_system_transition = TestedSystem.transitions_t term smd_effect session_id ideal_internal_state adversary_senc
type system_label = TestedSystem.label term smd_effect session_id adversary_senc

