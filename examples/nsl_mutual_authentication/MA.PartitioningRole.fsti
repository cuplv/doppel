module MA.PartitioningRole


(**
  Role-sensitive partitioning on TestedSystem labels for the NSL mutual
  authentication example.

  This module distinguishes labels by the *full* `(session, party, peer, role)`
  identifier — i.e. two Internal/Observable labels are in the same class iff
  their `ma_label_id`s are equal. Adversary `Input` derivations form a single
  class of their own, as before.

  Motivation (vs. a role-insensitive partitioning):
    * Finer classes mean fewer eventually-observable transition sequences stay
      inside a single partition, which is what the top-level
      observational-bisimulation-up-to-partitions proof has to consider. In
      particular, a sequence such as `initiate(i, A, B, Initiator) ; initiate(i,
      B, A, Responder) ; sim_message1(i, A, B, Initiator)` mixes the two role
      directions of the exchange; under the unordered partition all three labels
      share a class, so the whole sequence is in-partition, whereas under this
      role-sensitive partition the second label `(i, B, A, Responder)` belongs
      to a *different* class and the sequence is no longer wholly in-partition.

  The role-sensitive partitioning is right-movable for the *reachable* states of
  the ideal+simulator system, conditioned on state invariants such as: (I1) no
  `Output(i, p)` delivery command can be in flight in `sim_to_ideal_channel`
  unless `requests[i]` already contains both `{p, p', r}` and its complementary
  `{p', p, complementary r}` (the invariant suggested by the user), and (I2) at
  most one request per party per session.
*)

open SymbolicTypes

open AencTerms

open AdversaryAenc

open MA.NSL

open MA.Ideal

open MA.Adversary

open MA.Types

open TestedSystem

open ObservationalBisimulation

module PartialMap = FStar.PartialMap

module Set = FStar.Set

open MA.TestedProtocols

/// Two label identifiers are in the same class iff *all four* fields agree.
/// (Equivalently, `id1 == id2`.)
let ma_label_id_in_same_partition_role (id1 id2: ma_label_id) : prop =
  id1.session == id2.session /\
  id1.party == id2.party /\
  id1.peer == id2.peer /\
  id1.role == id2.role

let ma_label_in_same_partition_role
      (l1 l2: TestedSystem.label term ma_effect ma_label_id adversary_aenc)
    : prop =
  match l1, l2 with
  | TestedSystem.Input _, TestedSystem.Input _ -> True
  | TestedSystem.Internal id1, TestedSystem.Internal id2 ->
      ma_label_id_in_same_partition_role id1 id2
  | TestedSystem.Internal id1, TestedSystem.Observable _ id2 ->
      ma_label_id_in_same_partition_role id1 id2
  | TestedSystem.Observable _ id1, TestedSystem.Internal id2 ->
      ma_label_id_in_same_partition_role id1 id2
  | TestedSystem.Observable _ id1, TestedSystem.Observable _ id2 ->
      ma_label_id_in_same_partition_role id1 id2
  | _, _ -> False

(** `ma_label_in_same_partition_role` is an equivalence relation. *)
val ma_label_in_same_partition_role_equiv: unit
  -> squash (Partition.is_equiv ma_label_in_same_partition_role)

(**
  Role-sensitive partitioning of transition labels by session, initiator, and
  responder.
*)
[@@ FStar.Tactics.Typeclasses.tcinstance]
let ma_partition_role: Partition.partition (TestedSystem.label term ma_effect ma_label_id adversary_aenc) =
  {
    in_same_partition = ma_label_in_same_partition_role;
    in_same_partition_equiv = ma_label_in_same_partition_role_equiv
  }

/// Right-movability of internal transitions in the implementation system
/// under the role-sensitive partition.
///
/// Vacuous: `ma_nsl_protocol_transition` defines `Protocol.Internal _ ->
/// False`, so no internal transition exists and the premise is unsatisfiable.
val ma_right_movable_impl_role
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma (right_movable (ma_impl_system corrupt key_directory know0) ma_partition_role)

/// Right-movability of internal transitions in the ideal+simulator system
/// under the role-sensitive partition.
///
/// Conditioned on the ideal system invariant `ma_ideal_system_inv` which
/// over-approximates the set of reachable states.
val ma_right_movable_ideal_role
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma (right_movable_mod_inv (ma_ideal_system corrupt key_directory know0)
              ma_partition_role (MA.IdealInvariants.ma_ideal_system_inv corrupt key_directory))
