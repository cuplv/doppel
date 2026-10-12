module MA.ObservationalBisimulation.Proof.IdealImpl

/// Ideal -> Impl observable step simulation for the role-sensitive partition.
///
/// This module discharges the ideal-side half of the up-to-partitions
/// observational bisimulation: given a related pair `(s_p, s_q)` and a single
/// eventually-observable step `lbls` of the *ideal* system from `s_q` that lies
/// wholly within one role-sensitive partition, it exhibits a matching
/// eventually-observable step of the implementation from `s_p` with the same
/// observable effects and a related post-state.
///
/// Unlike the implementation (which has no internal transitions), the ideal
/// system has internal `ma_ideal_initiate` and `ma_sim_receive_message3`
/// transitions, so eventually-observable sequences on the ideal side can have
/// length 2 (`tau ; alpha`).  Because all labels of a single-partition sequence
/// share one `ma_label_id` (role-sensitive), at most one internal `tau` can fire
/// before the observable, so the only feasible shapes are length 1 and length 2.

open SymbolicTypes
open AencTerms
open AdversaryAenc
open MA.NSL
open MA.Ideal
open MA.Adversary
open MA.Types
open TestedSystem
open ObservationalBisimulation
open Partition

module PartialMap = FStar.PartialMap
module Set = FStar.Set

open MA.ObservationalBisimulation.Relation
open MA.IdealInvariants
open MA.TestedProtocols
open MA.PartitioningRole

/// A single eventually-observable step `lbls` of the ideal system from a related
/// `s_q`, lying wholly within one role-sensitive partition `part_l`, is matched
/// by the implementation from `s_p`.
val ma_obs_sim_ideal_impl_instance
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_q: ideal_system_state)
      (s_p: impl_system_state)
      (part_l: system_label)
      (lbls: list system_label)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        lbls_in_partition lbls ma_partition_role part_l /\
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q')
      (ensures
        exists (lbls': list system_label) (s_p': impl_system_state).
          TestEquivalence.label_effects lbls' == TestEquivalence.label_effects lbls /\
          eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls' s_p' /\
          ma_bisim_relation corrupt key_directory s_p' s_q')
