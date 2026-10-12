module ObservationalBisimulation

open Adversary

open Protocol

open StaticEquivalence

open SymbolicTypes

open TestedSystem

open TestEquivalence

open Partition

let obs_bisim_up_to_partitions_implies_t_equivalence
      (#term: eqtype)
      (#obs #id #sigma_p #sigma_q: Type)
      (#adv: adversary term)
      (know0: knowledge term)
      (proto_p: Protocol.protocol term obs id sigma_p)
      (proto_q: Protocol.protocol term obs id sigma_q)
      (part_p part_q: partition (TestedSystem.label term obs id adv))
      (rel: (TestedSystem.state term sigma_p -> TestedSystem.state term sigma_q -> prop))
    : Lemma
      (requires
        (let p = TestedSystem.system adv proto_p know0 in
         let q = TestedSystem.system adv proto_q know0 in
         rel p.init q.init
         /\ (forall (s_p: TestedSystem.state term sigma_p) (s_q: TestedSystem.state term sigma_q).
              rel s_p s_q ==> statically_equivalent adv s_p.know s_q.know)
         /\ obs_bisim_up_to_partitions p q part_p part_q rel
         /\ right_movable p part_p
         /\ right_movable q part_q))
      (ensures
        t_equivalence (TestedSystem.system adv proto_p know0)
          (TestedSystem.system adv proto_q know0)) =
  admit () // Admitted here, proven in Lean

let obs_bisim_up_to_partitions_implies_t_equivalence'
      (#term: eqtype)
      (#obs #id #sigma_p #sigma_q: Type)
      (#adv: adversary term)
      (know0: knowledge term)
      (proto_p: Protocol.protocol term obs id sigma_p)
      (proto_q: Protocol.protocol term obs id sigma_q)
      (part_p part_q: partition (TestedSystem.label term obs id adv))
      (rel: (TestedSystem.state term sigma_p -> TestedSystem.state term sigma_q -> prop))
      (inv_p: TestedSystem.state term sigma_p -> prop)
      (inv_q: TestedSystem.state term sigma_q -> prop)
    : Lemma
      (requires
        (let p = TestedSystem.system adv proto_p know0 in
         let q = TestedSystem.system adv proto_q know0 in
         rel p.init q.init
         /\ (forall (s_p: TestedSystem.state term sigma_p) (s_q: TestedSystem.state term sigma_q).
              rel s_p s_q ==> statically_equivalent adv s_p.know s_q.know)
         /\ obs_bisim_up_to_partitions p q part_p part_q rel
         /\ inv_p p.init /\ inv_q q.init
         /\ (forall s_p lbl s_p'. inv_p s_p ==> p.transitions s_p lbl s_p' ==> inv_p s_p')
         /\ (forall s_q lbl s_q'. inv_q s_q ==> q.transitions s_q lbl s_q' ==> inv_q s_q')
         /\ right_movable_mod_inv p part_p inv_p
         /\ right_movable_mod_inv q part_q inv_q))
      (ensures
        t_equivalence (TestedSystem.system adv proto_p know0)
          (TestedSystem.system adv proto_q know0)) =
  admit () // Admitted here, proven in Lean
