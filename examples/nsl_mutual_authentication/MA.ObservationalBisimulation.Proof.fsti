module MA.ObservationalBisimulation.Proof



/// Protocol-level T-equivalence for NSL mutual authentication.
///
/// This module lifts the intended observational bisimulation for the MA
/// implementation and ideal-plus-simulator protocol into the TestedSystem /
/// ObservationalBisimulation framework. As in the SMD example, labels are
/// partitioned by session_id, and all adversary Input derivations share a
/// single partition class.

open SymbolicTypes

open AencTerms

open AdversaryAenc

open TestEquivalence

module PartialMap = FStar.PartialMap

open MA.NSL

open MA.Adversary

open MA.ObservationalBisimulation.Relation

open MA.IdealInvariants

open MA.TestedProtocols



(**
  NSL mutual authentication implementation and ideal-plus-simulator protocol
  are T-equivalent for any shared initial key directory and knowledge.

  The right-movability of the ideal+simulator side is established only for
  reachable states (those satisfying `MA.IdealInvariants.ma_ideal_system_inv`),
  so the proof routes through
  `obs_bisim_up_to_partitions_implies_t_equivalence'`. The `requires` clause
  therefore carries the honest-start hypotheses needed to establish that
  invariant at the initial state (see
  `MA.IdealInvariants.ma_ideal_system_inv_init`): no directory private key is
  derivable from the adversary's initial knowledge `know0`. No initial nonce
  restrictions required: the protocols only use fresh nonces, so the adversary's
  initial knowledge may contain unrelated nonces.
*)

val ma_t_equivalence
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
      (requires
        ma_key_directory_injective key_directory /\
        (forall (participant: participant_id) (k: priv_key) (d: adv.derivation).
          PartialMap.sel key_directory participant == Some k /\
          not (Set.mem participant corrupt) ==>
          not (adv.derive d (ma_impl_system corrupt key_directory know0).init.know = Some (PrivKey k))))
      (ensures
        t_equivalence
          (ma_impl_system corrupt key_directory know0)
          (ma_ideal_system corrupt key_directory know0))
