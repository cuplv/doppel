module SMD.Ideal

open SymbolicTypes

open SencTerms

open SMD.Adversary

open Bag

module Protocol = Protocol

module Set = FStar.Set



/// Helper lemma: both combined transitions remove one triggering input term,
/// so `Bag.subset s'.inputs s.inputs` holds.

let smd_ideal_valid_transitions_lemma
      (s: Protocol.state term ideal_internal_state)
      (l: Protocol.label term smd_effect session_id)
      (s': Protocol.state term ideal_internal_state)
    : Lemma (smd_ideal_protocol_transition s l s' ==> Bag.subset s'.inputs s.inputs) =
  match l with
  | Protocol.Observable _ _ _ -> ()
  | Protocol.Internal _ -> ()

let smd_ideal_valid_transitions s l s' =
  smd_ideal_valid_transitions_lemma s l s';
  ()
