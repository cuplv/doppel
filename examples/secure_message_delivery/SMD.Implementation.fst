module SMD.Implementation

open SymbolicTypes

open SencTerms

open SMD.Adversary

open Bag

module Protocol = Protocol

module Set = FStar.Set

let smd_impl_valid_transitions_lemma
      (s: Protocol.state term impl_internal_state)
      (l: Protocol.label term smd_effect session_id)
      (s': Protocol.state term impl_internal_state)
    : Lemma (smd_impl_protocol_transition s l s' ==> Bag.subset s'.inputs s.inputs) =
  match l with
  | Protocol.Observable _ _ _ -> ()
  | Protocol.Internal _ -> ()

let smd_impl_valid_transitions s l s' =
  smd_impl_valid_transitions_lemma s l s';
  ()
