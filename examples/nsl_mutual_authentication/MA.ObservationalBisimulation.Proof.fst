module MA.ObservationalBisimulation.Proof

open SymbolicTypes

open AencTerms

open AdversaryAenc

open MA.NSL

open MA.Ideal

open MA.Adversary

open MA.Types

open StaticEquivalence

open TestedSystem

open ObservationalBisimulation

open TestEquivalence

open Partition

open Bag

module PartialMap = FStar.PartialMap

module Set = FStar.Set
module SeqProps = FStar.Seq.Properties
module List = FStar.List.Tot.Base

open MA.ObservationalBisimulation.Relation
open MA.IdealInvariants

open MA.ObservationalBisimulation.Witnesses

open MA.TestedProtocols

open MA.ObservationalBisimulation.Proof.Common

open MA.ObservationalBisimulation.Proof.MessageDerivability

open MA.ObservationalBisimulation.Proof.ResponderOutput

open MA.ObservationalBisimulation.Proof.InputStep

open MA.ObservationalBisimulation.Proof.SendMessage3InitiatorAck

open MA.ObservationalBisimulation.Proof.InitiatorStartSendMessage1

open MA.ObservationalBisimulation.Proof.ResponderReplyDeliverMessage2

open MA.ObservationalBisimulation.Proof.InitiatorOutputDeliver

open MA.PartitioningRole

open MA.ObservationalBisimulation.Proof.IdealImpl




/// Implementation-side observable step simulation.
///
/// The implementation protocol has no internal transitions, so an
/// eventually-observable step from `s_p` is a single `Observable eff lid`
/// label.  This lemma dispatches on `(eff, lid.role)` (and, for the
/// NetSend/Initiator case, on whether the firing transition is the
/// initiator-start or the initiator-ack disjunct), extracts the existential
/// witnesses of the firing impl transition, and combines the corresponding
/// `..._step_impl_*` witness lemma (which exhibits the matching ideal
/// eventually-observable step) with the corresponding
/// `..._step_impl_*_preserves_relation` lemma (which re-establishes the
/// relation at the post-states).

/// Responder-reply observable step.  Factored into its own lemma so the
/// transition appears in `requires` as a clean hypothesis, which lets
/// `eliminate exists` unfold its 4-way existential (cf. the analogous
/// `MA.IdealInvariants` `_preserved_send2` helper).
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60 --split_queries no"
private
let ma_obs_bisim_observable_step_impl_responder_reply_case
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (lid: ma_label_id)
      (t: term)
      (s_p': impl_system_state)
    : Lemma
      (requires
        lid.role == Responder /\
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_responder_reply_transition (s2p_state s_p) lid.session lid.party lid.peer t (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know t)
      (ensures
        exists (lbls': list system_label) (s_q': ideal_system_state).
          label_effects lbls' == [ma_observable_effect NetSend] /\
          eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls' s_q' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  let session = lid.session in
  let party = lid.party in
  let peer = lid.peer in
  // Peel the transition's existential one binder at a time (same idiom as the
  // initiator-ack case).
  let p_inonce (inonce: nonce) : prop =
    exists (rnonce: nonce) (rkey: priv_key) (ipub: term {PubKey? ipub}).
      ma_nsl_responder_reply_enabled (s2p_state s_p) session party peer inonce rnonce rkey ipub /\
      t == MA.NSL.ma_nsl_message2_term session peer party inonce rnonce ipub /\
      (s2p_state s_p') == ma_nsl_responder_reply_state (s2p_state s_p) session party peer inonce rnonce rkey
  in
  assert (exists inonce. p_inonce inonce);
  let initiator_nonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_inonce in
  assert (p_inonce initiator_nonce);
  let p_rnonce (rnonce: nonce) : prop =
    exists (rkey: priv_key) (ipub: term {PubKey? ipub}).
      ma_nsl_responder_reply_enabled (s2p_state s_p) session party peer initiator_nonce rnonce rkey ipub /\
      t == MA.NSL.ma_nsl_message2_term session peer party initiator_nonce rnonce ipub /\
      (s2p_state s_p') == ma_nsl_responder_reply_state (s2p_state s_p) session party peer initiator_nonce rnonce rkey
  in
  assert (exists rnonce. p_rnonce rnonce);
  let responder_nonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_rnonce in
  assert (p_rnonce responder_nonce);
  let p_rkey (rkey: priv_key) : prop =
    exists (ipub: term {PubKey? ipub}).
      ma_nsl_responder_reply_enabled (s2p_state s_p) session party peer initiator_nonce responder_nonce rkey ipub /\
      t == MA.NSL.ma_nsl_message2_term session peer party initiator_nonce responder_nonce ipub /\
      (s2p_state s_p') == ma_nsl_responder_reply_state (s2p_state s_p) session party peer initiator_nonce responder_nonce rkey
  in
  assert (exists rkey. p_rkey rkey);
  let responder_key = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_rkey in
  assert (p_rkey responder_key);
  let p_ipub (ipub: term {PubKey? ipub}) : prop =
    ma_nsl_responder_reply_enabled (s2p_state s_p) session party peer initiator_nonce responder_nonce responder_key ipub /\
    t == MA.NSL.ma_nsl_message2_term session peer party initiator_nonce responder_nonce ipub /\
    (s2p_state s_p') == ma_nsl_responder_reply_state (s2p_state s_p) session party peer initiator_nonce responder_nonce responder_key
  in
  assert (exists (ipub: term {PubKey? ipub}). p_ipub ipub);
  let initiator_pubkey =
    FStar.IndefiniteDescription.indefinite_description_ghost (ipub: term {PubKey? ipub}) p_ipub in
  assert (p_ipub initiator_pubkey);
  let s_q' =
    ma_impl_responder_reply_ideal_witness s_q session party peer
      initiator_nonce responder_nonce responder_key initiator_pubkey in
  ma_obs_bisim_observable_step_impl_responder_reply
    corrupt key_directory know0 s_p s_q session party peer
    initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  ma_obs_bisim_observable_step_impl_responder_reply_preserves_relation
    corrupt key_directory s_p s_q session party peer
    initiator_nonce responder_nonce responder_key initiator_pubkey s_p';
  assert_norm (label_effects
    ([TestedSystem.Internal lid; TestedSystem.Observable NetSend lid] <: list system_label)
    == [ma_observable_effect NetSend])
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"
private
let ma_obs_bisim_observable_step_impl
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (eff: ma_effect)
      (lid: ma_label_id)
      (s_p': impl_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        (ma_impl_system corrupt key_directory know0).transitions s_p (TestedSystem.Observable eff lid) s_p')
      (ensures
        exists (lbls': list system_label) (s_q': ideal_system_state).
          label_effects lbls' == [ma_observable_effect eff] /\
          eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls' s_q' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  let session = lid.session in
  let party = lid.party in
  let peer = lid.peer in
  // Extract the emitted term `t` and the underlying protocol transition.
  let p_t (t: term) : prop =
    ma_nsl_protocol_transition (s2p_state s_p) (Protocol.Observable eff t lid) (s2p_state s_p') /\
    s_p'.know == Seq.snoc s_p.know t
  in
  assert (exists t. p_t t);
  let t = FStar.IndefiniteDescription.indefinite_description_ghost term p_t in
  assert (p_t t);
  match eff with
  | NetSend ->
    (match lid.role with
     | Initiator ->
       // Initiator NetSend: either the initiator-start or the initiator-ack
       // disjunct of `ma_nsl_protocol_transition` fired.
       assert (ma_nsl_initiator_start_transition (s2p_state s_p) session party peer t (s2p_state s_p') \/
               ma_nsl_initiator_ack_transition (s2p_state s_p) session party peer t (s2p_state s_p'));
       if FStar.IndefiniteDescription.strong_excluded_middle
            (ma_nsl_initiator_start_transition (s2p_state s_p) session party peer t (s2p_state s_p'))
       then (
         // Initiator start: extract `(initiator_nonce, responder_pubkey)`.
         let p_start (inonce: nonce) : prop =
           exists (rpub: term {PubKey? rpub}).
             ma_nsl_initiator_start_enabled (s2p_state s_p) session party peer inonce rpub /\
             t == MA.NSL.ma_nsl_message1_term session party peer inonce rpub /\
             (s2p_state s_p') == ma_nsl_initiator_start_state (s2p_state s_p) session party peer inonce
         in
         assert (exists inonce. p_start inonce);
         let initiator_nonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_start in
         assert (p_start initiator_nonce);
         let p_pub (rpub: term {PubKey? rpub}) : prop =
           ma_nsl_initiator_start_enabled (s2p_state s_p) session party peer initiator_nonce rpub /\
           t == MA.NSL.ma_nsl_message1_term session party peer initiator_nonce rpub /\
           (s2p_state s_p') == ma_nsl_initiator_start_state (s2p_state s_p) session party peer initiator_nonce
         in
         assert (exists (rpub: term {PubKey? rpub}). p_pub rpub);
         let responder_pubkey =
           FStar.IndefiniteDescription.indefinite_description_ghost (rpub: term {PubKey? rpub}) p_pub in
         assert (p_pub responder_pubkey);
         let lbls' : list system_label =
           [TestedSystem.Internal lid; TestedSystem.Observable NetSend lid] in
         let s_q' =
           ma_impl_initiator_start_ideal_witness s_q session party peer initiator_nonce responder_pubkey in
         ma_obs_bisim_observable_step_impl_initiator_start
           corrupt key_directory know0 s_p s_q session party peer initiator_nonce responder_pubkey s_p';
         ma_obs_bisim_observable_step_impl_initiator_start_preserves_relation
           corrupt key_directory s_p s_q session party peer initiator_nonce responder_pubkey s_p';
         assert_norm (label_effects
           ([TestedSystem.Internal lid; TestedSystem.Observable NetSend lid] <: list system_label)
           == [ma_observable_effect NetSend])
       ) else (
         // Initiator ack: extract `(responder_nonce, initiator_key, responder_pubkey)`.
         assert (ma_nsl_initiator_ack_transition (s2p_state s_p) session party peer t (s2p_state s_p'));
         let p_rnonce (rnonce: nonce) : prop =
           exists (ikey: priv_key) (rpub: term {PubKey? rpub}).
             ma_nsl_initiator_ack_enabled (s2p_state s_p) session party peer rnonce ikey rpub /\
             t == MA.NSL.ma_nsl_message3_term session party peer rnonce rpub /\
             (s2p_state s_p') == ma_nsl_initiator_ack_state (s2p_state s_p) session party peer rnonce ikey
         in
         assert (exists rnonce. p_rnonce rnonce);
         let responder_nonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_rnonce in
         assert (p_rnonce responder_nonce);
         let p_ikey (ikey: priv_key) : prop =
           exists (rpub: term {PubKey? rpub}).
             ma_nsl_initiator_ack_enabled (s2p_state s_p) session party peer responder_nonce ikey rpub /\
             t == MA.NSL.ma_nsl_message3_term session party peer responder_nonce rpub /\
             (s2p_state s_p') == ma_nsl_initiator_ack_state (s2p_state s_p) session party peer responder_nonce ikey
         in
         assert (exists ikey. p_ikey ikey);
         let initiator_key = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_ikey in
         assert (p_ikey initiator_key);
         let p_rpub (rpub: term {PubKey? rpub}) : prop =
           ma_nsl_initiator_ack_enabled (s2p_state s_p) session party peer responder_nonce initiator_key rpub /\
           t == MA.NSL.ma_nsl_message3_term session party peer responder_nonce rpub /\
           (s2p_state s_p') == ma_nsl_initiator_ack_state (s2p_state s_p) session party peer responder_nonce initiator_key
         in
         assert (exists (rpub: term {PubKey? rpub}). p_rpub rpub);
         let responder_pubkey =
           FStar.IndefiniteDescription.indefinite_description_ghost (rpub: term {PubKey? rpub}) p_rpub in
         assert (p_rpub responder_pubkey);
         let s_q' =
           ma_impl_initiator_ack_ideal_witness s_q session party peer responder_nonce initiator_key responder_pubkey in
         ma_obs_bisim_observable_step_impl_initiator_ack
           corrupt key_directory know0 s_p s_q session party peer responder_nonce initiator_key responder_pubkey s_p';
         ma_obs_bisim_observable_step_impl_initiator_ack_preserves_relation
           corrupt key_directory s_p s_q session party peer responder_nonce initiator_key responder_pubkey s_p';
         assert_norm (label_effects
           ([TestedSystem.Observable NetSend lid] <: list system_label)
           == [ma_observable_effect NetSend])
       )
     | Responder ->
       // Responder reply: delegate to the helper lemma (transition in `requires`).
       assert (ma_nsl_responder_reply_transition (s2p_state s_p) session party peer t (s2p_state s_p'));
       ma_obs_bisim_observable_step_impl_responder_reply_case
         corrupt key_directory know0 s_p s_q lid t s_p')
  | IoSend ->
    (match lid.role with
     | Initiator ->
       // Initiator output: no extra existentials.
       assert (ma_nsl_initiator_output_transition (s2p_state s_p) session party peer t (s2p_state s_p'));
       let s_q' = ma_impl_initiator_output_ideal_witness s_q session party peer in
       ma_obs_bisim_observable_step_impl_initiator_output
         corrupt key_directory know0 s_p s_q session party peer s_p';
       ma_obs_bisim_observable_step_impl_initiator_output_preserves_relation
         corrupt key_directory s_p s_q session party peer s_p';
       assert_norm (label_effects
         ([TestedSystem.Observable IoSend lid] <: list system_label)
         == [ma_observable_effect IoSend])
     | Responder ->
       // Responder output: extract `responder_key`.
       assert (ma_nsl_responder_output_transition (s2p_state s_p) session party peer t (s2p_state s_p'));
       let p_rkey (rkey: priv_key) : prop =
         ma_nsl_responder_output_enabled (s2p_state s_p) session party peer rkey /\
         t == ma_authenticated_term session party peer /\
         (s2p_state s_p') == ma_nsl_responder_output_state (s2p_state s_p) session party peer rkey
       in
       assert (exists rkey. p_rkey rkey);
       let responder_key = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_rkey in
       assert (p_rkey responder_key);
       let s_q' = ma_impl_responder_output_ideal_witness s_q session party peer responder_key in
       ma_obs_bisim_observable_step_impl_responder_output
         corrupt key_directory know0 s_p s_q session party peer responder_key s_p';
       ma_obs_bisim_observable_step_impl_responder_output_preserves_relation
         corrupt key_directory s_p s_q session party peer responder_key s_p';
       assert_norm (label_effects
         ([TestedSystem.Internal lid; TestedSystem.Observable IoSend lid] <: list system_label)
         == [ma_observable_effect IoSend]))
#pop-options

/// Per-instance simulation: a single eventually-observable step `lbls` of the
/// implementation from a related state `s_p` is matched by the ideal side.
/// Since the implementation has no internal transitions, the only feasible
/// `lbls` are `[Observable eff lid]` and `[Input d]`; any other shape makes the
/// `eventually_observable_step` premise unsatisfiable (vacuous).
private
let ma_obs_sim_impl_ideal_instance
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (part_l: system_label)
      (lbls: list system_label)
      (s_p': impl_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        lbls_in_partition lbls ma_partition_role part_l /\
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p')
      (ensures
        exists (lbls': list system_label) (s_q': ideal_system_state).
          label_effects lbls' == label_effects lbls /\
          eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls' s_q' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  match lbls with
  | [TestedSystem.Observable eff lid] ->
    ma_obs_bisim_observable_step_impl corrupt key_directory know0 s_p s_q eff lid s_p';
    assert_norm (label_effects ([TestedSystem.Observable eff lid] <: list system_label)
                 == [ma_observable_effect eff])
  | [TestedSystem.Input d] ->
    ma_obs_bisim_input_step_impl corrupt key_directory know0 s_p s_q d s_p';
    assert (exists s_q'.
      (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Input d) s_q' /\
      ma_bisim_relation corrupt key_directory s_p' s_q');
    // Pick the matching ideal witness explicitly (mirrors the ideal-side
    // `ma_obs_sim_ideal_impl_instance`) rather than leaving it to SMT.
    introduce exists (lbls': list system_label) (s_q': ideal_system_state).
        label_effects lbls' == label_effects lbls /\
        eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls' s_q' /\
        ma_bisim_relation corrupt key_directory s_p' s_q'
    with ([TestedSystem.Input d])
      (FStar.IndefiniteDescription.indefinite_description_ghost ideal_system_state
        (fun s_q' ->
          (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Input d) s_q' /\
          ma_bisim_relation corrupt key_directory s_p' s_q'))
    and ()
  // `is_eventually_observable []` is `false`, so the premise is unsatisfiable.
  | [] -> ()
  // Any remaining `lbls` has 2+ elements, so `is_eventually_observable` forces
  // the first label to be `Internal`. The implementation protocol has no
  // internal transition, so `multi_transitions` (and hence
  // `eventually_observable_step`) is unsatisfiable: the premise is vacuous.
  | _ -> ()

private
let ma_obs_sim_impl_ideal_move_requires
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (part_l: system_label)
      (lbls: list system_label)
      (s_p': impl_system_state)
    : Lemma
      (ma_bisim_relation corrupt key_directory s_p s_q /\
       lbls_in_partition lbls ma_partition_role part_l /\
       eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p' ==>
       (exists (lbls': list system_label) (s_q': ideal_system_state).
          label_effects lbls' == label_effects lbls /\
          eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls' s_q' /\
          ma_bisim_relation corrupt key_directory s_p' s_q')) =
  FStar.Classical.move_requires
    (ma_obs_sim_impl_ideal_instance corrupt key_directory know0 s_p s_q part_l lbls) s_p'

private
let ma_obs_sim_impl_ideal
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
    (obs_sim_up_to_partitions (ma_impl_system corrupt key_directory know0)
        (ma_ideal_system corrupt key_directory know0)
        ma_partition_role
        (ma_bisim_relation corrupt key_directory)) =
  introduce forall
    (s_p: impl_system_state)
    (s_q: ideal_system_state)
    (part_l: system_label)
    (lbls: list system_label)
    (s_p': impl_system_state).
    ma_bisim_relation corrupt key_directory s_p s_q /\
    lbls_in_partition lbls ma_partition_role part_l /\
    eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls s_p' ==>
    (exists (lbls': list system_label) (s_q': ideal_system_state).
       label_effects lbls' == label_effects lbls /\
       eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls' s_q' /\
       ma_bisim_relation corrupt key_directory s_p' s_q')
  with ma_obs_sim_impl_ideal_move_requires corrupt key_directory know0 s_p s_q part_l lbls s_p'

private
let ma_obs_sim_ideal_impl_move_requires
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_q: ideal_system_state)
      (s_p: impl_system_state)
      (part_l: system_label)
      (lbls: list system_label)
      (s_q': ideal_system_state)
    : Lemma
      ((fun s_q s_p -> ma_bisim_relation corrupt key_directory s_p s_q) s_q s_p /\
       lbls_in_partition lbls ma_partition_role part_l /\
       eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q' ==>
       (exists (lbls': list system_label) (s_p': impl_system_state).
          label_effects lbls' == label_effects lbls /\
          eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls' s_p' /\
          (fun s_q s_p -> ma_bisim_relation corrupt key_directory s_p s_q) s_q' s_p')) =
  FStar.Classical.move_requires
    (ma_obs_sim_ideal_impl_instance
      corrupt key_directory know0 s_q s_p part_l lbls) s_q'

private
let ma_obs_sim_ideal_impl
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
    (obs_sim_up_to_partitions (ma_ideal_system corrupt key_directory know0)
        (ma_impl_system corrupt key_directory know0)
        ma_partition_role
        (fun s_q s_p -> ma_bisim_relation corrupt key_directory s_p s_q)) =
  // The ideal-side eventually-observable steps are dispatched per
  // single-partition shape by `ma_obs_sim_ideal_impl_instance`:
  // feasible length-1 / length-2 sequences are matched by the implementation via
  // their per-step witness + `_preserves_relation` lemmas, and the remaining
  // shapes are infeasible from a related state.
  introduce forall
    (s_q: ideal_system_state)
    (s_p: impl_system_state)
    (part_l: system_label)
    (lbls: list system_label)
    (s_q': ideal_system_state).
    (fun s_q s_p -> ma_bisim_relation corrupt key_directory s_p s_q) s_q s_p /\
    lbls_in_partition lbls ma_partition_role part_l /\
    eventually_observable_step (ma_ideal_system corrupt key_directory know0) s_q lbls s_q' ==>
    (exists (lbls': list system_label) (s_p': impl_system_state).
       label_effects lbls' == label_effects lbls /\
       eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls' s_p' /\
       (fun s_q s_p -> ma_bisim_relation corrupt key_directory s_p s_q) s_q' s_p')
  with ma_obs_sim_ideal_impl_move_requires corrupt key_directory know0 s_q s_p part_l lbls s_q'

private
let ma_obs_bisim
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
    (obs_bisim_up_to_partitions (ma_impl_system corrupt key_directory know0)
        (ma_ideal_system corrupt key_directory know0)
        ma_partition_role
        ma_partition_role
        (ma_bisim_relation corrupt key_directory)) =
  ma_obs_sim_impl_ideal corrupt key_directory know0;
  ma_obs_sim_ideal_impl corrupt key_directory know0;
  norm_spec [delta_only [`%obs_bisim_up_to_partitions]]
    (obs_bisim_up_to_partitions (ma_impl_system corrupt key_directory know0)
        (ma_ideal_system corrupt key_directory know0)
        ma_partition_role
        ma_partition_role
        (ma_bisim_relation corrupt key_directory))

/// Trivial invariant for the implementation side: the implementation has no
/// internal transitions, so `ma_right_movable_impl_role` already establishes
/// the full (unconditioned) `right_movable`. We pass the always-true invariant
/// to `obs_bisim_up_to_partitions_implies_t_equivalence'`.
private
let ma_impl_trivial_inv (s: impl_system_state) : prop = True

/// `right_movable` implies `right_movable_mod_inv` for any invariant, since the
/// latter merely adds the hypothesis `inv s` to the same commute obligation.
private
let ma_right_movable_impl_role_mod_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
      (right_movable_mod_inv (ma_impl_system corrupt key_directory know0)
        ma_partition_role ma_impl_trivial_inv) =
  ma_right_movable_impl_role corrupt key_directory know0

let ma_t_equivalence
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term) =
  let p = ma_impl_system corrupt key_directory know0 in
  let q = ma_ideal_system corrupt key_directory know0 in
  // The two systems share the initial knowledge `know0`.
  assert (p.init.know == know0);
  assert (q.init.know == know0);
  ma_init_related corrupt key_directory know0;
  ma_static_equiv_from_rel corrupt key_directory;
  ma_obs_bisim corrupt key_directory know0;
  // Right-movability: implementation side is unconditioned (no internal
  // transitions); ideal side is conditioned on `ma_ideal_system_inv`.
  ma_right_movable_impl_role_mod_inv corrupt key_directory know0;
  ma_right_movable_ideal_role corrupt key_directory know0;
  // The ideal invariant holds at the initial state and is preserved.
  ma_ideal_system_inv_init corrupt key_directory know0;
  introduce forall (s: ideal_system_state) (l: system_label) (s': ideal_system_state).
    ma_ideal_system_inv corrupt key_directory s ==> q.transitions s l s' ==>
    ma_ideal_system_inv corrupt key_directory s'
  with (
    introduce _ ==> _ with _h1. (
      introduce _ ==> _ with _h2.
        ma_ideal_system_inv_preserved corrupt key_directory know0 s s' l
    )
  );
  // The implementation invariant is trivially true everywhere.
  assert (forall (s: impl_system_state). ma_impl_trivial_inv s);
  // The lemma composes the protocols with the adversary via `TestedSystem.system`
  // (matching the local `p` / `q` above), so transition validity holds by
  // construction and need not be supplied here.
  obs_bisim_up_to_partitions_implies_t_equivalence'
    know0
    (ma_nsl_protocol_with_used_nonces key_directory (ma_knowledge_nonces know0))
    (ma_ideal_protocol_with_knowledge key_directory corrupt know0)
    ma_partition_role
    ma_partition_role
    (ma_bisim_relation corrupt key_directory)
    ma_impl_trivial_inv
    (ma_ideal_system_inv corrupt key_directory)
