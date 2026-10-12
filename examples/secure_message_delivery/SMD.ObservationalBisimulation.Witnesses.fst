module SMD.ObservationalBisimulation.Witnesses

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

open Bag

module Option = FStar.Option

module PartialMap = FStar.PartialMap.Ext

module Set = FStar.Set

open SMD.Bijection

open SMD.TestedProtocols

open ObservationalBisimulation

open TestEquivalence

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
let smd_obs_bisim_observable_step_impl_send k know0 s_p s_q session message s_p' =
  assert
    (smd_impl_protocol_send_enabled
      ({ inputs = s_p.inputs; internal = s_p.internal })
      session
      message
      k);
  // Step 1: session not yet sim_sent in ideal (from completed_iff + not sent in impl)
  assert (not (Set.mem session s_p.internal.sent_sessions));
  assert
    (send_equivalent_transitions_completed_iff (s2p_state s_p) (s2p_state s_q));
  assert
    (Set.mem session s_p.internal.sent_sessions <==>
      Set.mem session s_q.internal.sim_sent_sessions);
  assert (not (Set.mem session s_q.internal.sim_sent_sessions));
  // Step 2: ideal has not yet committed a message for this session
  //         (ideal_invariant_sim_sent_only_after_ideal_commit: sim_sent iff messages contains)
  assert (ideal_invariants s_q);
  assert
    (forall sid.
        Set.mem sid s_q.internal.sim_sent_sessions <==>
        PartialMap.contains s_q.internal.messages sid);
  assert (not (PartialMap.contains s_q.internal.messages session));
  // Step 3: corresponding ideal message is in the ideal inputs bag.
  //         Bag correspondence: `Bag.count s_p.inputs t == Bag.count s_q.inputs (bij.cright t)`
  //         with `bij.cright = smd_bi_subst`.  On `Pair (SessionId session) message`,
  //         `smd_bi_subst` recurses to `Pair (SessionId session) (smd_bi_subst message ...)`.
  assert (Bag.mem (Pair (SessionId session) message) s_p.inputs);
  let ideal_message = smd_bi_subst message s_p.internal.messages k k in
  assert (Bag.mem (Pair (SessionId session) ideal_message) s_q.inputs);
  // Step 4: construct the intermediate state after ideal commit (Internal step)
  let t_ideal = Senc (SessionId session) k in
  let s_q' = smd_impl_send_ideal_witness k s_p.internal.messages s_q session message in
  let ideal_trigger_input = Pair (SessionId session) ideal_message in
  // Intermediate state after commit: messages updated, ideal_to_sim_channel populated
  let s_q_mid: TestedSystem.state term ideal_internal_state = {
    know = s_q.know;
    inputs = Bag.remove ideal_trigger_input s_q.inputs;
    internal = {
      s_q.internal with
      messages = PartialMap.upd s_q.internal.messages session ideal_message;
      ideal_to_sim_channel = Set.add (SessionId session) s_q.internal.ideal_to_sim_channel
    }
  } in
  // Show the commit transition (Internal step) is valid
  assert (smd_ideal_commit_enabled (s2p_state s_q) session ideal_message);
  assert (s2p_state s_q_mid == smd_ideal_commit_state (s2p_state s_q) session ideal_message);
  assert (smd_ideal_commit_protocol_transition (s2p_state s_q) session (s2p_state s_q_mid));
  assert ((smd_ideal_protocol k).transition (s2p_state s_q) (Protocol.Internal session) (s2p_state s_q_mid));
  assert (s_q_mid.know == s_q.know);
  assert ((smd_ideal_system k know0).transitions s_q (TestedSystem.Internal session) s_q_mid);
  // Step 5: show the sim_send transition (Observable step) is valid from s_q_mid
  assert (smd_sim_send_enabled (s2p_state s_q_mid) session);
  assert (smd_sim_send_protocol_transition (s2p_state s_q_mid) session t_ideal (s2p_state s_q'));
  assert ((smd_ideal_protocol k).transition (s2p_state s_q_mid) (Protocol.Observable NetSend t_ideal session) (s2p_state s_q'));
  assert (s_q'.know == Seq.snoc s_q_mid.know t_ideal);
  assert ((smd_ideal_system k know0).transitions s_q_mid (TestedSystem.Observable NetSend session) s_q');
  // Step 6: combine into eventually_observable_step [Internal session; Observable NetSend session]
  let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable NetSend session] in
  // multi_transitions for [Observable NetSend session] is: exists s''. transitions s_q_mid (Observable NetSend session) s'' /\ s'' == s_q'
  assert (multi_transitions (smd_ideal_system k know0).transitions s_q_mid
    [TestedSystem.Observable NetSend session] s_q');
  // multi_transitions for [Internal; Observable] is: exists s''. transitions s_q (Internal session) s'' /\ multi_transitions s'' [Observable] s_q'
  assert (multi_transitions (smd_ideal_system k know0).transitions s_q lbls s_q');
  assert (is_eventually_observable lbls);
  assert (eventually_observable_step (smd_ideal_system k know0) s_q lbls s_q')

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let smd_obs_bisim_observable_step_impl_receive k know0 s_p s_q session message s_p' =
  let ideal_message = smd_bi_subst message s_p.internal.messages k k in
  let s_q' = smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message in
  assert (smd_impl_protocol_receive_enabled ({inputs=s_p.inputs;internal=s_p.internal}) session message);
  assert (not (Set.mem session s_p.internal.received_sessions));
  assert (Bag.mem (Senc (Pair (SessionId session) message) k) s_p.inputs);
  assert (derivable s_p.know (Senc (Pair (SessionId session) message) k));
  assert (implementation_invariants s_p);
  assert (impl_invariant_cannot_derive_response_before_send s_p);
  assert_norm (is_receive_trigger_for_session session k (Senc (Pair (SessionId session) message) k));
  assert_norm (in_term (Senc (Pair (SessionId session) message) k) (Senc (Pair (SessionId session) message) k));
  let p_trigger: derivation -> prop =
    fun d -> adv.derive d s_p.know = Some (Senc (Pair (SessionId session) message) k)
  in
  assert (exists d. p_trigger d);
  let d_trigger = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_trigger in
  assert (p_trigger d_trigger);
  assert (adv.derive d_trigger s_p.know = Some (Senc (Pair (SessionId session) message) k));
  assert (Set.mem session s_p.internal.sent_sessions);
  assert (send_equivalent_transitions_completed_iff (s2p_state s_p) (s2p_state s_q));
  assert (Set.mem session s_q.internal.sim_sent_sessions);
  assert (ideal_invariants s_q);
  assert (PartialMap.contains s_q.internal.messages session);
  let stored_ideal_msg = Some?.v (PartialMap.sel s_q.internal.messages session) in
  assert (PartialMap.sel s_q.internal.messages session = Some stored_ideal_msg);
  assert (smd_bisim_relation k s_p s_q);
  assert (StaticEquivalence.bijective_correspondence_on_derivations
    adv
    s_p.know
    s_q.know
    (smd_subst_bijection k k s_p.internal.messages));
  // With the self-inverse bijection, `bij.cright = smd_bi_subst`.  Connect it
  // to the collapsed ideal form: map[session] = Some message (from impl
  // invariant applied to the derivable impl Senc), and then smd_bi_subst
  // collapses `Senc (Pair (SessionId session) message) k` to
  // `Senc (SessionId session) k`.
  assert (impl_invariant_messages_consistent_with_knowledge s_p);
  assert (in_term (Senc (Pair (SessionId session) message) k) (Senc (Pair (SessionId session) message) k));
  assert (PartialMap.sel s_p.internal.messages session = Some message);
  assert (smd_bi_subst (Senc (Pair (SessionId session) message) k) s_p.internal.messages k k
          = Senc (SessionId session) k);
  assert (exists d.
    adv.derive d s_p.know = Some (Senc (Pair (SessionId session) message) k) /\
    adv.derive d s_q.know = Some (Senc (SessionId session) k));
  assert_norm (in_term (Senc (SessionId session) k) (Senc (SessionId session) k));
  assert (to_be_delivered_messages_already_derivable_by_same_derivation s_p s_q);
  assert (exists trigger_d.
    adv.derive trigger_d s_p.know = Some (Pair (SessionId session) message) /\
    adv.derive trigger_d s_q.know = Some (Pair (SessionId session) stored_ideal_msg));
  // smd_bi_subst recurses on Pair; SessionId is identity.  Hence
  // bij.cright (Pair (SessionId session) message) = Pair (SessionId session) ideal_message.
  let bij = smd_subst_bijection k k s_p.internal.messages in
  smd_subst_bijection_right k k s_p.internal.messages (Pair (SessionId session) message);
  assert (bij.cright (Pair (SessionId session) message)
          == Pair (SessionId session) ideal_message);
  // bijective_correspondence: for every d, derive d s_q.know == mapTot bij.cright (derive d s_p.know).
  // With derive d s_p.know = Some (Pair (SessionId session) message), we get
  // derive d s_q.know = Some (Pair (SessionId session) ideal_message), so by functionality of
  // adv.derive, stored_ideal_msg == ideal_message.
  assert (forall trigger_d'.
    adv.derive trigger_d' s_p.know = Some (Pair (SessionId session) message) /\
    adv.derive trigger_d' s_q.know = Some (Pair (SessionId session) stored_ideal_msg) ==>
    stored_ideal_msg == ideal_message);
  assert (stored_ideal_msg == ideal_message);
  assert (receive_equivalent_transitions_completed_iff (s2p_state s_p) (s2p_state s_q));
  assert (not (Set.mem session s_q.internal.sim_received_sessions));
  assert (Bag.mem (Senc (SessionId session) k) s_q.inputs);
  // Construct intermediate state after sim_receive (Internal step)
  let ideal_trigger_input = Senc (SessionId session) k in
  let s_q_mid: TestedSystem.state term ideal_internal_state = {
    know = s_q.know;
    inputs = Bag.remove ideal_trigger_input s_q.inputs;
    internal = {
      s_q.internal with
      sim_received_sessions = Set.add session s_q.internal.sim_received_sessions;
      sim_to_ideal_channel = Set.add (SessionId session) s_q.internal.sim_to_ideal_channel
    }
  } in
  // Show sim_receive transition (Internal step) is valid
  assert (smd_sim_receive_enabled (s2p_state s_q) session);
  assert (s2p_state s_q_mid == smd_sim_receive_state (s2p_state s_q) session);
  assert (smd_sim_receive_protocol_transition (s2p_state s_q) session (s2p_state s_q_mid));
  assert ((smd_ideal_protocol k).transition (s2p_state s_q) (Protocol.Internal session) (s2p_state s_q_mid));
  assert (s_q_mid.know == s_q.know);
  assert ((smd_ideal_system k know0).transitions s_q (TestedSystem.Internal session) s_q_mid);
  // Show ideal_deliver transition (Observable step) is valid from s_q_mid
  let deliver_term = Pair (SessionId session) ideal_message in
  assert (smd_ideal_deliver_enabled (s2p_state s_q_mid) session ideal_message);
  assert (smd_ideal_deliver_protocol_transition (s2p_state s_q_mid) session deliver_term (s2p_state s_q'));
  assert ((smd_ideal_protocol k).transition (s2p_state s_q_mid) (Protocol.Observable IoSend deliver_term session) (s2p_state s_q'));
  assert (s_q'.know == Seq.snoc s_q_mid.know deliver_term);
  // Help split queries: the system transition needs exists t. ..., provide the witness explicitly
  assert ((smd_ideal_protocol k).transition (s2p_state s_q_mid) (Protocol.Observable IoSend deliver_term session) (s2p_state s_q') /\
          s_q'.know == Seq.snoc s_q_mid.know deliver_term);
  assert ((smd_ideal_system k know0).transitions s_q_mid (TestedSystem.Observable IoSend session) s_q');
  // Combine into eventually_observable_step [Internal session; Observable IoSend session]
  let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable IoSend session] in
  assert (multi_transitions (smd_ideal_system k know0).transitions s_q_mid
    [TestedSystem.Observable IoSend session] s_q');
  assert (multi_transitions (smd_ideal_system k know0).transitions s_q lbls s_q');
  assert (is_eventually_observable lbls);
  assert (eventually_observable_step #_ #_ #_ #_ #_ #know0 (smd_ideal_system k know0) s_q lbls s_q')

#pop-options

let smd_obs_bisim_observable_step_ideal_send k know0 s_p s_q session message s_q' =
  let impl_message = smd_bi_subst message s_p.internal.messages k k in
  let s_p' = smd_ideal_send_impl_witness k s_p session message in
  assert (smd_ideal_protocol_send_enabled ({inputs=s_q.inputs;internal=s_q.internal}) session message);
  assert (not (Set.mem session s_q.internal.sim_sent_sessions));
  assert (send_equivalent_transitions_completed_iff (s2p_state s_p) (s2p_state s_q));
  assert (not (Set.mem session s_p.internal.sent_sessions));
  assert (Bag.mem (Pair (SessionId session) message) s_q.inputs);
  // smd_bi_subst on Pair recurses into components; SessionId is identity.
  let bij = smd_subst_bijection k k s_p.internal.messages in
  smd_subst_bijection_left k k s_p.internal.messages (Pair (SessionId session) message);
  smd_subst_bijection_right k k s_p.internal.messages (Pair (SessionId session) impl_message);
  assert (bij.cleft (Pair (SessionId session) message)
          == Pair (SessionId session) impl_message);
  // Self-inverse: applying smd_bi_subst twice returns the original term.  The
  // bag correspondence directly gives us that the impl-side counterpart of
  // `Pair (SessionId session) message` is `bij.cleft` of it, which is
  // `Pair (SessionId session) impl_message`.
  bij.bij.right_left (Pair (SessionId session) impl_message);
  assert (smd_bi_subst (smd_bi_subst (Pair (SessionId session) impl_message) s_p.internal.messages k k) s_p.internal.messages k k
          == Pair (SessionId session) impl_message);
  assert (Bag.mem (Pair (SessionId session) impl_message) s_p.inputs);
  assert (smd_impl_protocol_send_enabled ({inputs=s_p.inputs;internal=s_p.internal}) session impl_message k);
  assert (smd_impl_protocol_send_transition ({inputs=s_p.inputs;internal=s_p.internal}) session (Senc (Pair (SessionId session) impl_message) k) ({inputs=s_p'.inputs;internal=s_p'.internal}));
  assert (s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) impl_message) k));
  assert_norm ((smd_impl_system k know0).transitions s_p (TestedSystem.Observable NetSend session) s_p' <==>
    (exists t. (smd_impl_protocol k).transition (s2p_state s_p) (Protocol.Observable NetSend t session) (s2p_state s_p') /\ s_p'.know == Seq.snoc s_p.know t));
  assert (exists t. (smd_impl_protocol k).transition (s2p_state s_p) (Protocol.Observable NetSend t session) (s2p_state s_p') /\ s_p'.know == Seq.snoc s_p.know t)

let smd_obs_bisim_observable_step_ideal_receive k know0 s_p s_q session message s_q' =
  let stored_ideal_msg = message in
  let impl_message = smd_bi_subst stored_ideal_msg s_p.internal.messages k k in
  let s_p' = smd_ideal_receive_impl_witness k s_p session message in
  assert (smd_ideal_protocol_receive_enabled ({inputs=s_q.inputs;internal=s_q.internal}) session stored_ideal_msg);
  assert (not (Set.mem session s_q.internal.sim_received_sessions));
  assert (PartialMap.sel s_q.internal.messages session == Some stored_ideal_msg);
  assert (receive_equivalent_transitions_completed_iff (s2p_state s_p) (s2p_state s_q));
  assert (not (Set.mem session s_p.internal.received_sessions));
  assert (ideal_invariants s_q);
  assert (ideal_invariant_sim_sent_only_after_ideal_commit s_q);
  assert (Set.mem session s_q.internal.sim_sent_sessions);
  assert (send_equivalent_transitions_completed_iff (s2p_state s_p) (s2p_state s_q));
  assert (Set.mem session s_p.internal.sent_sessions);
  assert (implementation_invariants s_p);
  assert (impl_invariant_sent_sessions_have_messages s_p);
  assert (PartialMap.contains s_p.internal.messages session);
  let stored_impl_msg = Some?.v (PartialMap.sel s_p.internal.messages session) in
  assert (PartialMap.sel s_p.internal.messages session = Some stored_impl_msg);
  assert (smd_bisim_relation k s_p s_q);
  assert (StaticEquivalence.bijective_correspondence_on_derivations
    adv
    s_p.know
    s_q.know
    (smd_subst_bijection k k s_p.internal.messages));
  assert (to_be_delivered_messages_already_derivable_by_same_derivation s_p s_q);
  assert (Bag.mem (Senc (SessionId session) k) s_q.inputs);
  assert (derivable s_q.know (Senc (SessionId session) k));
  let bij = smd_subst_bijection k k s_p.internal.messages in
  // Use the inverse direction of the bijective correspondence to get impl derivability
  let d_enc: derivation =
    FStar.IndefiniteDescription.indefinite_description_ghost derivation
      (fun d -> adv.derive d s_q.know = Some (Senc (SessionId session) k))
  in
  derive_bijection_implies_inverse adv s_p.know s_q.know bij d_enc;
  smd_subst_bijection_left k k s_p.internal.messages (Senc (SessionId session) k);
  // smd_bi_subst on `Senc (SessionId session) k` expands through the map since
  // `sel map session = Some stored_impl_msg`.
  assert (smd_bi_subst (Senc (SessionId session) k) s_p.internal.messages k k
          == Senc (Pair (SessionId session) stored_impl_msg) k);
  assert (derivable s_p.know (Senc (Pair (SessionId session) stored_impl_msg) k));
  assert_norm (in_term (Senc (Pair (SessionId session) stored_impl_msg) k) (Senc (Pair (SessionId session) stored_impl_msg) k));
  assert_norm (in_term (Senc (SessionId session) k) (Senc (SessionId session) k));
  smd_subst_bijection_right k k s_p.internal.messages (Senc (Pair (SessionId session) stored_impl_msg) k);
  // smd_bi_subst collapses `Senc (Pair (SessionId session) stored_impl_msg) k` back
  // to `Senc (SessionId session) k` (map-consistent).
  assert (smd_bi_subst (Senc (Pair (SessionId session) stored_impl_msg) k) s_p.internal.messages k k
          == Senc (SessionId session) k);
  assert (exists d.
    adv.derive d s_p.know = Some (Senc (Pair (SessionId session) stored_impl_msg) k) /\
    adv.derive d s_q.know = Some (Senc (SessionId session) k));
  assert (exists trigger_d.
    adv.derive trigger_d s_p.know = Some (Pair (SessionId session) stored_impl_msg) /\
    adv.derive trigger_d s_q.know = Some (Pair (SessionId session) stored_ideal_msg));
  // Prove stored_impl_msg == impl_message via bijection injectivity
  smd_subst_bijection_right k k s_p.internal.messages (Pair (SessionId session) stored_impl_msg);
  smd_subst_bijection_right k k s_p.internal.messages (Pair (SessionId session) impl_message);
  bij.bij.right_left (Pair (SessionId session) stored_ideal_msg);
  smd_subst_bijection_left k k s_p.internal.messages (Pair (SessionId session) stored_ideal_msg);
  // smd_bi_subst on Pair recurses into components; SessionId is identity.
  assert (smd_bi_subst (Pair (SessionId session) stored_ideal_msg) s_p.internal.messages k k
          == Pair (SessionId session) impl_message);
  assert (bij.cleft (Pair (SessionId session) stored_ideal_msg) == Pair (SessionId session) impl_message);
  // From the bijective correspondence: for all d, derive d ideal = mapTot bij.cright (derive d impl).
  // If derive d impl = Some (Pair (SessionId session) stored_impl_msg), then
  // derive d ideal = Some (bij.cright (Pair (SessionId session) stored_impl_msg)).
  // If that also equals Some (Pair (SessionId session) stored_ideal_msg), then
  // bij.cright (Pair (SessionId session) stored_impl_msg) = Pair (SessionId session) stored_ideal_msg,
  // so Pair (SessionId session) stored_impl_msg = bij.cleft (Pair (SessionId session) stored_ideal_msg)
  //                                              = Pair (SessionId session) impl_message
  assert (forall trigger_d'.
    adv.derive trigger_d' s_p.know = Some (Pair (SessionId session) stored_impl_msg) /\
    adv.derive trigger_d' s_q.know = Some (Pair (SessionId session) stored_ideal_msg) ==>
    stored_impl_msg == impl_message);
  assert (stored_impl_msg == impl_message);
  assert (s_p.internal.key == k);
  assert (Bag.mem (Senc (Pair (SessionId session) impl_message) k) s_p.inputs);
  assert (smd_impl_protocol_receive_enabled ({inputs=s_p.inputs;internal=s_p.internal}) session impl_message);
  assert (smd_impl_protocol_receive_transition ({inputs=s_p.inputs;internal=s_p.internal}) session (Pair (SessionId session) impl_message) ({inputs=s_p'.inputs;internal=s_p'.internal}));
  assert (s_p'.know == Seq.snoc s_p.know (Pair (SessionId session) impl_message));
  assert ((smd_impl_protocol k).transition (s2p_state s_p) (Protocol.Observable IoSend (Pair (SessionId session) impl_message) session) (s2p_state s_p'));
  assert_norm ((smd_impl_system k know0).transitions s_p (TestedSystem.Observable IoSend session) s_p' <==>
    (exists t. (smd_impl_protocol k).transition (s2p_state s_p) (Protocol.Observable IoSend t session) (s2p_state s_p') /\ s_p'.know == Seq.snoc s_p.know t));
  assert (exists t. (smd_impl_protocol k).transition (s2p_state s_p) (Protocol.Observable IoSend t session) (s2p_state s_p') /\ s_p'.know == Seq.snoc s_p.know t)

#pop-options
