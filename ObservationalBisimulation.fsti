module ObservationalBisimulation

open Adversary

open Protocol

open StaticEquivalence

open SymbolicTypes

open TestedSystem

open TestEquivalence

open Partition

/// -------------------------------------------------------------------------
/// Naming note
/// -------------------------------------------------------------------------
///
/// This module mechanizes the proof technique the paper ("Real Ideals:
/// Symbolic Verification of Simulation-Based Security", the Doppel framework)
/// calls *barrier bisimulation* and its partitioned, right-moving relaxation
/// (paper §4, "Proving testing equivalence"). The F* and
/// Lean identifiers retain the earlier name *observational* (bi)simulation;
/// they denote the same notion. Definitions and theorems are cited below by
/// their number in the paper (e.g. Def. 4.6).



/// -------------------------------------------------------------------------
/// Helper predicates on labels and label sequences
/// -------------------------------------------------------------------------

/// True iff a TestedSystem.label is internal (τ).

let is_internal
      (#term: eqtype)
      (#obs #id: Type)
      (#adv: adversary term)
      (l: TestedSystem.label term obs id adv)
    : bool = None? (lbl_to_effect l)


/// True iff a sequence has the shape  τ* · α  where α is non-internal.

let rec is_eventually_observable
      (#term: eqtype)
      (#obs #id: Type)
      (#adv: adversary term)
      (ls: list (TestedSystem.label term obs id adv))
    : bool =
  match ls with
  | [] -> false
  | [l] -> not (is_internal l)
  | l :: ls' -> is_internal l && is_eventually_observable ls'

let eventually_observable_step
      (#term: eqtype)
      (#obs #id #internal_state: Type)
      (#adv: adversary term)
      (#know0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #internal_state #adv #know0)
      (s: TestedSystem.state term internal_state)
      (lbls: list (TestedSystem.label term obs id adv))
      (s': TestedSystem.state term internal_state)
    : prop = is_eventually_observable lbls /\ multi_transitions p.transitions s lbls s'



/// -------------------------------------------------------------------------
/// Partitions  (paper §4.1)
/// -------------------------------------------------------------------------

/// Right-movable partition  (paper's "Right-Movable Partitioning" definition,
/// §4.1; `rightMovablePartition` in the Lean development):
/// For distinct groups ρ ≠ ρ', any internal τ ∈ ρ commutes past any α ∈ ρ'.

let right_movable
      (#term: eqtype)
      (#obs #id #sigma: Type)
      (#adv: adversary term)
      (#know0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #sigma #adv #know0)
      (part: partition (TestedSystem.label term obs id adv))
    : prop =
  // For all distinct parts (represented by labels in different parts)
  forall (rho: TestedSystem.label term obs id adv) (rho': TestedSystem.label term obs id adv).
    ~(part.in_same_partition rho rho') ==>
    (forall (tau: TestedSystem.label term obs id adv)
        (alpha: TestedSystem.label term obs id adv)
        (s: TestedSystem.state term sigma)
        (s_mid: TestedSystem.state term sigma)
        (s': TestedSystem.state term sigma).
        part.in_same_partition tau rho /\ is_internal tau /\ part.in_same_partition alpha rho' /\
        p.transitions s tau s_mid /\ p.transitions s_mid alpha s' ==>
        (exists (s_mid': TestedSystem.state term sigma).
            p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s'))

(**
  Right-movable partition, conditioned on an inductive state invariant `inv`.
  (paper Def. 4.12;
  `rightMovablePartitionModInvariant` in the Lean development.)
  Same shape as `right_movable` but the inner commute implication is only
  required to hold at states `s` satisfying `inv s`. This is a strictly weaker obligation than
  `right_movable`, sufficient for the bisimulation argument since only
  reachable (hence `inv`-satisfying) states are explored.
*)
let right_movable_mod_inv
      (#term: eqtype)
      (#obs #id #sigma: Type)
      (#adv: adversary term)
      (#know0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #sigma #adv #know0)
      (part: partition (TestedSystem.label term obs id adv))
      (inv: TestedSystem.state term sigma -> prop)
    : prop =
  (forall (rho: TestedSystem.label term obs id adv) (rho': TestedSystem.label term obs id adv).
    ~(part.in_same_partition rho rho') ==>
    (forall (tau: TestedSystem.label term obs id adv)
        (alpha: TestedSystem.label term obs id adv)
        (s: TestedSystem.state term sigma)
        (s_mid: TestedSystem.state term sigma)
        (s': TestedSystem.state term sigma).
        part.in_same_partition tau rho /\ is_internal tau /\ part.in_same_partition alpha rho' /\
        inv s /\ p.transitions s tau s_mid /\ p.transitions s_mid alpha s' ==>
        (exists (s_mid': TestedSystem.state term sigma).
            p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s')))



(** Proposition that holds if all the labels are in the same partition as `l0` *)

let lbls_in_partition
      (#term: eqtype)
      (#obs #id: Type)
      (#adv: adversary term)
      (lbls: list (TestedSystem.label term obs id adv))
      (part: partition (TestedSystem.label term obs id adv))
      (l0: TestedSystem.label term obs id adv)
    : prop =
  // Every eventually-observable transition is in the observable partition
  forall l. List.memP l lbls ==> part.in_same_partition l l0



/// Observational Simulation up to right-movable partitions.

let obs_sim_up_to_partitions
      (#term: eqtype)
      (#obs #id #sigma_p #sigma_q: Type)
      (#adv: adversary term)
      (#know0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #sigma_p #adv #know0)
      (q: TestedSystem.system_t #term #obs #id #sigma_q #adv #know0)
      (part_p: partition (TestedSystem.label term obs id adv))
      (rel:
          (TestedSystem.state term sigma_p -> TestedSystem.state term sigma_q -> prop)
        )
    : prop =
  forall (s_p: TestedSystem.state term sigma_p)
    (s_q: TestedSystem.state term sigma_q)
    (part_l:
    // Indicates the partition the transitions must be in (since the paper definition quantifies over partitions)
    TestedSystem.label term obs id adv)
    (lbls: list (TestedSystem.label term obs id adv))
    (s_p': TestedSystem.state term sigma_p).
    rel s_p s_q /\ lbls_in_partition lbls part_p part_l /\
    eventually_observable_step p s_p lbls s_p' ==>
    (exists
      (lbls': list (TestedSystem.label term obs id adv))
      (s_q': TestedSystem.state term sigma_q).
        label_effects lbls' == label_effects lbls
        /\ eventually_observable_step q s_q lbls' s_q'
        /\ rel s_p' s_q')



/// Observational bisimulation up to right-movable partitions. The paper calls
/// this a *partitioned barrier bisimulation*.
/// (paper Def. 4.6;
/// `observationalBisimulationUpToPartitions` in the Lean development)

let obs_bisim_up_to_partitions
      (#term: eqtype)
      (#obs #id #sigma_p #sigma_q: Type)
      (#adv: adversary term)
      (#know0: knowledge term)
      (p: TestedSystem.system_t #term #obs #id #sigma_p #adv #know0)
      (q: TestedSystem.system_t #term #obs #id #sigma_q #adv #know0)
      (part_p part_q: partition (TestedSystem.label term obs id adv))
      (rel:
          (TestedSystem.state term sigma_p -> TestedSystem.state term sigma_q -> prop)
        )
    : prop =
  obs_sim_up_to_partitions p q part_p rel /\
  obs_sim_up_to_partitions q p part_q (fun s_q s_p -> rel s_p s_q)



/// -------------------------------------------------------------------------
/// Main theorem  (paper Thm. 4.7)
/// -------------------------------------------------------------------------

/// Obs. bisimulation up to right-movable partitions implies T-equivalence.
/// [admitted here, proven in Lean]
///
/// Like the Lean and paper theorems, this gives sufficient conditions for a
/// *protocol composed with an adversary*: the two tested systems are obtained
/// from protocols `proto_p`/`proto_q` and the tester `adv` via
/// `TestedSystem.system`, rather than being arbitrary tested systems. The Lean
/// theorem is proven for the `combined_transitions` construction specifically
/// (its proof inspects that relation's structure), so stating this axiom over
/// arbitrary transition relations would claim more than is proven.
///
/// Because the systems are built by `TestedSystem.system`, their transition
/// relations are valid by construction (`TestedSystem.transitions'_valid`), so
/// the knowledge-validity hypotheses the Lean proof relies on hold automatically
/// and need not be assumed here.

val obs_bisim_up_to_partitions_implies_t_equivalence
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
          (TestedSystem.system adv proto_q know0))

(**
  Strengthened version of `obs_bisim_up_to_partitions_implies_t_equivalence`
  that allows conditioning the right-movability requirement on inductive
  invariants `inv_p` and `inv_q`.
  (paper Thm. 4.13;
  `..._mod_inv` in the Lean development.)

  This is useful when the right-movability property does not hold universally
  but holds for transitions from reachable states, which are over-approximated
  by the invariants.

  As above, the two systems are protocol-adversary compositions built with
  `TestedSystem.system`. The proof is admitted here, and proven in Lean.
*)
val obs_bisim_up_to_partitions_implies_t_equivalence'
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
          (TestedSystem.system adv proto_q know0))
