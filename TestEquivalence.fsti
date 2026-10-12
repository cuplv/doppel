module TestEquivalence

open Adversary

module Protocol = Protocol

open StaticEquivalence

open SymbolicTypes

module TestedSystem = TestedSystem

let rec multi_transitions
      (#state #label: Type)
      (transitions: (state -> label -> state -> prop))
      (s: state)
      (ls: list label)
      (s': state)
    : Tot prop (decreases ls) =
  match ls with
  | [] -> s == s'
  | l :: ls' -> exists s''. transitions s l s'' /\ multi_transitions transitions s'' ls' s'



(**
  The observable effects and adversary interaction characterize the observable
  behavior of a tested system.
*)

type tested_effect (term: eqtype) (obs: Type) (adv: adversary term) =
  | Observable : obs -> tested_effect term obs adv // Protocol exhibits observable effect o
  // Tester adds derivation result to protocol inputs
  | Input : adv.derivation -> tested_effect term obs adv

let lbl_to_effect
      (#term: eqtype)
      (#obs #id: Type)
      (#adv: adversary term)
      (l: TestedSystem.label term obs id adv)
    : option (tested_effect term obs adv) =
  match l with
  | TestedSystem.Observable o _ -> Some (Observable o)
  | TestedSystem.Input d -> Some (Input d)
  | TestedSystem.Internal _ -> None

(**
  Returns a list of the non-internal effects in the given list of labels. Order
  is preserved. Mirrors `effects` in the Lean development: internal transitions
  produce no effects, while observable effects and tester derivations are both
  kept.
*)
let rec label_effects
      (#term: eqtype)
      (#obs #id: Type)
      (#adv: adversary term)
      (lbls: list (TestedSystem.label term obs id adv))
      : list (tested_effect term obs adv) =
  match lbls with
  | [] -> []
  | l :: ls ->
    (match lbl_to_effect l with
      | Some eff -> eff :: label_effects ls
      | None -> label_effects ls)



/// T-preorder (paper Def. 3.2; `weak_test_preorder` in the Lean
/// development): q refines p — every reachable behavior of p from initial
/// states is matched by q up to static equivalence. The matching trace of q
/// must exhibit the same observable effects, but may differ from p's trace in
/// its internal transitions (the paper's weak multi-step arrow, which absorbs
/// extra τ steps).

let t_preorder
      (#term: eqtype)
      (#obs #id #sigma_p #sigma_q: Type)
      (#adv: adversary term)
      (#know_0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #sigma_p #adv #know_0)
      (q: TestedSystem.system_t #term #obs #id #sigma_q #adv #know_0)
    : prop =
  forall lbls_p (s_p': TestedSystem.state term sigma_p).
    // If p can reach s_p' from its initial state via lbls_p, then q can reach
    // some s_q' from its initial state via some lbls_q with the same
    // observable effects, such that s_p' and s_q' are statically equivalent.
    multi_transitions p.transitions p.init lbls_p s_p' ==>
    (exists (lbls_q: list (TestedSystem.label term obs id adv))
        (s_q': TestedSystem.state term sigma_q).
        label_effects lbls_q == label_effects lbls_p /\
        multi_transitions q.transitions q.init lbls_q s_q' /\
        statically_equivalent adv s_p'.know s_q'.know)



/// T-equivalence (paper Def. 3.3; `weak_test_equivalence` in the
/// Lean development): Mutual t_preorder.

let t_equivalence
      (#term: eqtype)
      (#obs #id #sigma_p #sigma_q: Type)
      (#adv: adversary term)
      (#know_0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #sigma_p #adv #know_0)
      (q: TestedSystem.system_t #term #obs #id #sigma_q #adv #know_0)
    : prop = t_preorder p q /\ t_preorder q p
