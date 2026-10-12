module TestedSystem

open Adversary

open SymbolicTypes

module Protocol = Protocol

module SeqProps = FStar.Seq.Properties

(**
  Helper for `transitions'_valid`: a single transition step satisfies the
  knowledge constraints of `valid_observable_transition_relation`.
*)
private
let transitions'_valid_aux
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (adv: adversary term)
      (p: Protocol.protocol term obs id internal_state)
      (s: state term internal_state)
      (l: label term obs id adv)
      (s': state term internal_state)
    : Lemma
      (requires transitions' adv p s l s')
      (ensures valid_knowledge_change s l s') =
  match l with
  | Observable o lbl_id ->
    eliminate exists t.
        p.transition (s2p_state s) (Protocol.Observable o t lbl_id) (s2p_state s') /\
        s'.know == Seq.snoc s.know t
    returns (forall t'. knowledge_mem s.know t' ==> knowledge_mem s'.know t')
    with _. SeqProps.lemma_mem_snoc s.know t
  | _ -> ()

let transitions'_valid
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (adv: adversary term)
      (p: Protocol.protocol term obs id internal_state)
    : Lemma (valid_observable_transition_relation (transitions' adv p)) =
  FStar.Classical.forall_intro_3
    (FStar.Classical.move_requires_3 (transitions'_valid_aux adv p))
