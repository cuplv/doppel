module SMD.ObservationalBisimulation.Proof



/// Protocol-level T-equivalence for Secure Message Delivery.
///
/// This module assembles the observational bisimulation for SMD — the relation
/// from `SMD.ObservationalBisimulation.Relation` together with the
/// step-simulation lemmas from the `SMD.ObservationalBisimulation.Proof.*`
/// submodules — into the TestedSystem / ObservationalBisimulation typeclass
/// framework, yielding the T-equivalence theorem for the SMD protocol
/// (`smd_t_equivalence`).
///
/// The step-simulation lemmas (observable transitions) and the structural
/// lemmas (partition equivalence, right-movability, etc.) are all proved in
/// F*. The only admitted results this theorem depends on are the two
/// metatheorems in `ObservationalBisimulation`, which are mechanized in the
/// companion Lean development.

open SymbolicTypes

open SencTerms

open AdversarySenc

open SMD.Implementation

open SMD.ImplementationInvariants

open SMD.Ideal

open SMD.IdealInvariants

open SMD.Adversary

open SMD.Types

open StaticEquivalence

open TestedSystem

open ObservationalBisimulation

open TestEquivalence

open Partition

open AdversarySenc

open Bag

module Option = FStar.Option

module PartialMap = FStar.PartialMap.Ext

module Set = FStar.Set

open SMD.ObservationalBisimulation.Relation
open SMD.TestedProtocols

/// Session-based partition on TestedSystem labels.
///
/// Labels for the same session_id are in the same partition class; all Input
/// derivations form their own single class; labels for different sessions or
/// from different kinds are in distinct classes.

let smd_label_in_same_partition
      (l1 l2: TestedSystem.label term smd_effect session_id adversary_senc)
    : prop =
  match l1, l2 with
  | TestedSystem.Input _, TestedSystem.Input _ -> True
  | TestedSystem.Internal s1, TestedSystem.Internal s2 -> s1 == s2
  | TestedSystem.Internal s1, TestedSystem.Observable _ s2 -> s1 == s2
  | TestedSystem.Observable _ s1, TestedSystem.Internal s2 -> s1 == s2
  | TestedSystem.Observable _ s1, TestedSystem.Observable _ s2 -> s1 == s2
  | _, _ -> False

val smd_label_in_same_partition_equiv: unit
  -> squash (Partition.is_equiv smd_label_in_same_partition)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let smd_partition:Partition.partition (TestedSystem.label term smd_effect session_id adversary_senc) =
  {
    in_same_partition = smd_label_in_same_partition;
    in_same_partition_equiv = smd_label_in_same_partition_equiv
  }

/// SMD implementation and ideal are T-equivalent for any shared key.

val smd_t_equivalence (k: key) (know0: knowledge term) : Lemma
  (requires
    ~(derivable know0 (Key k))
    /\ (forall (d: derivation) (t: term) (i: session_id) (m: term).
        derive d know0 = Some t ==>
        ~(in_term t (Senc (Pair (SessionId i) m) k)))
    /\ (forall (d: derivation) (t: term) (i: session_id).
        derive d know0 = Some t ==>
        ~(in_term t (Senc (SessionId i) k))))
  (ensures t_equivalence (smd_impl_system k know0) (smd_ideal_system k know0))
