module StaticEquivalence

open Adversary

open SymbolicTypes

module PartialMap = FStar.PartialMap
open FStar.Bijection



(** Indistinguishability lifted to optional terms. *)

let indistinguishable'
      (#term: eqtype)
      (indistinguishable: (term -> term -> prop))
      (term1 term2: option term)
    : prop =
  match term1, term2 with
  | Some t1, Some t2 -> indistinguishable t1 t2
  | None, None -> True
  | _, _ -> False



(** Two knowledges are statically equivalent with respect to an adversary when:
    - Every derivation produces indistinguishable terms.
    - Two derivations produce equal terms in one knowledge iff they produce
      equal terms in the other knowledge.
    (paper Def. 3.1; `statically_equivalent` in the
    Lean development.)
*)

let statically_equivalent
      (#term: eqtype)
      (adv: adversary term)
      (knowledge1 knowledge2: knowledge term)
    : prop =
  // Every derivation produces indistinguishable terms
  (forall d.
      indistinguishable' adv.indistinguishable (adv.derive d knowledge1) (adv.derive d knowledge2)) /\
  // Two derivations produce equal terms in one knowledge iff they produce equal terms in the other knowledge
  (forall d1 d2.
      (adv.derive d1 knowledge1 = adv.derive d2 knowledge1) <==>
      (adv.derive d1 knowledge2 = adv.derive d2 knowledge2))


(**
  Predicate capturing that two functions f and f_inv form a bijective
  correspondence on the terms derivable from impl and ideal knowledges:
    t_l correspond[f] t_r  means  t_r = f(t_l)  and  t_l = f_inv(t_r).
*)

let bijective_correspondence_on_derivations
      (#term: eqtype)
      (adv: adversary term)
      (impl_knowledge ideal_knowledge: knowledge term)
      (f : cbij term term)
    : prop =
  forall (d: adv.derivation).
    derive d ideal_knowledge = Option.mapTot f.cright (derive d impl_knowledge)

let derive_bijection_implies_inverse
      (#term: eqtype)
      (adv: adversary term)
      (impl_knowledge ideal_knowledge: knowledge term)
      (f : cbij term term)
      (d : adv.derivation)
    : Lemma
      (requires derive d ideal_knowledge == Option.mapTot f.cright (derive d impl_knowledge))
      (ensures derive d impl_knowledge == Option.mapTot f.cleft (derive d ideal_knowledge))
= match derive d impl_knowledge with
  | None -> ()
  | Some t -> f.bij.left_right t

(**
  Predicate capturing that a bijection f maps every term to an
  indistinguishable term.
*)

let bijection_maps_to_indistinguishable_terms (#term: eqtype) (adv: adversary term) (f: cbij term term) : prop =
  forall (t: term). adv.indistinguishable t (f.cright t)

(**
  The bijective correspondence between derivable terms in both worlds, combined
  with the fact that the bijection maps each term to an indistinguishable one,
  is the key insight needed to prove that static equivalence is preserved
  across transitions.

  When bijective_correspondence_on_derivations holds with f and f_inv, and
  bijection_maps_to_indistinguishable_terms holds for f, then the two
  knowledges are statically equivalent.
*)

let bijective_correspondence_implies_static_equivalence
      (#term: eqtype)
      (adv: adversary term)
      (left_knowledge right_knowledge: knowledge term)
      (f : cbij term term)
    : Lemma
      (requires
        bijective_correspondence_on_derivations adv left_knowledge right_knowledge f /\
        bijection_maps_to_indistinguishable_terms adv f)
      (ensures statically_equivalent adv left_knowledge right_knowledge) =
  assert (forall d. indistinguishable' adv.indistinguishable (adv.derive d left_knowledge) (adv.derive d right_knowledge));
  // Part 2: equality biconditional.
  // ==> direction is trivial (congruence).
  // <== direction needs injectivity of f.cright: if f.cright t1 = f.cright t2
  //     then applying f.cleft and using left_right gives t1 = t2.
  let aux_eq (d1 d2: adv.derivation)
    : Lemma (
        (adv.derive d1 left_knowledge = adv.derive d2 left_knowledge) <==>
        (adv.derive d1 right_knowledge = adv.derive d2 right_knowledge)) =
    match adv.derive d1 left_knowledge, adv.derive d2 left_knowledge with
    | Some t1, Some t2 -> f.bij.left_right t1; f.bij.left_right t2
    | _, _   -> ()
  in
  FStar.Classical.forall_intro_2 aux_eq
