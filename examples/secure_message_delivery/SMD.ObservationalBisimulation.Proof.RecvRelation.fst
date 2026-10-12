module SMD.ObservationalBisimulation.Proof.RecvRelation

open SymbolicTypes

open SencTerms

open AdversarySenc

open SMD.Implementation

open SMD.ImplementationInvariants

open SMD.Ideal

open SMD.IdealInvariants

open SMD.Adversary

open SMD.Types

open TestedSystem

open ObservationalBisimulation

open TestEquivalence

open Partition

open AdversarySenc

open Bag

module Option = FStar.Option

module PartialMap = FStar.PartialMap.Ext

module Set = FStar.Set

module Bijection = FStar.Bijection
module BijectionExt = FStar.Bijection.Ext

open SMD.ObservationalBisimulation.Witnesses
open SMD.TestedProtocols

open SMD.Bijection
open StaticEquivalence
open SMD.ObservationalBisimulation.Relation

#push-options "--z3rlimit_factor 8"

private
let mem_remove_neq_forall (#a: eqtype) (y: a) (b: Bag.bag a)
  : Lemma (forall x. x <> y ==> (Bag.mem x (Bag.remove y b) == Bag.mem x b)) =
  let preserve_for_x (x: a)
    : Lemma (x <> y ==> (Bag.mem x (Bag.remove y b) == Bag.mem x b)) =
    Bag.mem_remove x y b
  in
  FStar.Classical.forall_intro preserve_for_x

/// When the implementation takes an IoSend step delivering
/// `Pair(SessionId session, message)` AND the ideal witness state
/// `smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message` is reachable from
/// `s_q`, the `bijective_correspondence_on_derivations` property holds on the new
/// knowledge bases.

private
let smd_obs_bisim_observable_step_impl_recv_preserves_bijective_correspondence
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_p': TestedSystem.state term impl_internal_state)
    : Lemma
      (requires (
        let ideal_message = smd_bi_subst message s_p.internal.messages k k in
        let s_q' = smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message in
        smd_bisim_relation k s_p s_q /\
        smd_impl_protocol_receive_transition (s2p_state s_p)
          session
          (Pair (SessionId session) message)
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know (Pair (SessionId session) message) /\
        (smd_ideal_protocol_receive_transition (s2p_state s_q)
          session
          (Pair (SessionId session) ideal_message)
          (s2p_state s_q'))
      ))
      (ensures
        bijective_correspondence_on_derivations adv
          s_p'.know
          (smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message).know
          (smd_subst_bijection k k s_p'.internal.messages)) =
  let impl_valid_response = Senc (Pair (SessionId session) message) k in
  let impl_pair = Pair (SessionId session) message in
  smd_subst_bijection_right k k s_p.internal.messages impl_valid_response;
  assert_norm (in_term impl_valid_response impl_valid_response);
  assert_norm (in_term (Senc (SessionId session) k) (Senc (SessionId session) k));
  let stored_ideal_msg = Some?.v (PartialMap.sel s_q.internal.messages session) in
  let d_pair = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d ->
      adv.derive d s_p.know = Some impl_pair /\
      adv.derive d s_q.know = Some (Pair (SessionId session) stored_ideal_msg)) in
  smd_subst_bijection_right k k s_p.internal.messages impl_pair;
  bijective_correspondence_preserved_by_derivable_messages
    s_p.know s_q.know s_p.internal.messages s_p.internal.key s_q.internal.sim_key d_pair

private
let smd_obs_bisim_observable_step_ideal_recv_preserves_bijective_correspondence
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires (
        let impl_message = smd_bi_subst message s_p.internal.messages k k in
        let s_p' = smd_ideal_receive_impl_witness k s_p session message in
        smd_bisim_relation k s_p s_q /\
        (smd_ideal_protocol_receive_transition (s2p_state s_q)
          session
          (Pair (SessionId session) message)
          (s2p_state s_q')) /\
        smd_impl_protocol_receive_transition (s2p_state s_p)
          session
          (Pair (SessionId session) impl_message)
          (s2p_state s_p') /\
        s_q'.know == Seq.snoc s_q.know (Pair (SessionId session) message)
      ))
      (ensures (
        let s_p' = smd_ideal_receive_impl_witness k s_p session message in
        bijective_correspondence_on_derivations adv
          s_p'.know
          s_q'.know
          (smd_subst_bijection k k s_p'.internal.messages))) =
  let impl_message = smd_bi_subst message s_p.internal.messages k k in
  let impl_valid_response = Senc (Pair (SessionId session) impl_message) k in
  let impl_pair = Pair (SessionId session) impl_message in
  smd_subst_bijection_right k k s_p.internal.messages impl_valid_response;
  assert_norm (in_term impl_valid_response impl_valid_response);
  assert_norm (in_term (Senc (SessionId session) k) (Senc (SessionId session) k));
  let stored_ideal_msg = Some?.v (PartialMap.sel s_q.internal.messages session) in
  // Establish that s_p.internal.messages[session] = Some impl_message.
  // Follows from the messages correspondence clause of smd_bisim_relation and
  // self-inversion of smd_bi_subst (via the bijection's right∘left = id).
  assert (PartialMap.sel s_q.internal.messages session == Some message);
  assert (PartialMap.sel s_q.internal.messages session ==
          Option.mapTot (fun m -> smd_bi_subst m s_p.internal.messages k k)
                        (PartialMap.sel s_p.internal.messages session));
  let bij = smd_subst_bijection k k s_p.internal.messages in
  smd_subst_bijection_right k k s_p.internal.messages message;
  smd_subst_bijection_left k k s_p.internal.messages message;
  assert (bij.cleft (bij.cright message) == message);
  assert (PartialMap.sel s_p.internal.messages session == Some impl_message);
  // Establish that Senc (Pair (SessionId session) impl_message) k is derivable
  // from impl.know (it is in inputs, and inputs are derivable).
  assert (Bag.mem impl_valid_response s_p.inputs);
  assert (derivable s_p.know impl_valid_response);
  let d_pair = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d ->
      adv.derive d s_p.know = Some impl_pair /\
      adv.derive d s_q.know = Some (Pair (SessionId session) stored_ideal_msg)) in
  smd_subst_bijection_right k k s_p.internal.messages impl_pair;
  bijective_correspondence_preserved_by_derivable_messages
    s_p.know s_q.know s_p.internal.messages s_p.internal.key s_q.internal.sim_key d_pair

/// When the implementation takes an IoSend step delivering
/// `Pair(SessionId session, message)` AND the ideal witness state
/// `smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message` is reachable from
/// `s_q`, the bisimulation relation is preserved between `s_p'` and that
/// witness state.

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
private
let _recv_valid_encrypted_responses_preserved
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_p': TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (s_q': TestedSystem.state term ideal_internal_state)
      (impl_pair: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        derivable s_p.know impl_pair /\
        s_p'.know == Seq.snoc s_p.know impl_pair /\
        s_p'.internal.key == s_p.internal.key /\
        s_q'.internal.messages == s_q.internal.messages)
      (ensures
        valid_encrypted_responses_indistinguishable_from_stored_ideal_messages s_p' s_q') =
  let _valid_resp_preserved
        (qs: session_id) (qim qidm: term) (qd: derivation) (qdt: term)
    : Lemma
      (requires
        adv.derive qd s_p'.know = Some qdt /\
        in_term qdt (Senc (Pair (SessionId qs) qim) s_p'.internal.key) /\
        PartialMap.sel s_q'.internal.messages qs = Some qidm)
      (ensures indistinguishable qim qidm) =
    observe_derivable_no_new_derivations s_p.know impl_pair qdt
  in
  let _valid_resp_quad (qs: session_id) (qim qidm: term)
    : Lemma (forall (qd: derivation) (qdt: term).
      adv.derive qd s_p'.know = Some qdt /\
      in_term qdt (Senc (Pair (SessionId qs) qim) s_p'.internal.key) /\
      PartialMap.sel s_q'.internal.messages qs = Some qidm ==>
      indistinguishable qim qidm) =
    let helper (qd: derivation) (qdt: term)
      : Lemma (
        adv.derive qd s_p'.know = Some qdt /\
        in_term qdt (Senc (Pair (SessionId qs) qim) s_p'.internal.key) /\
        PartialMap.sel s_q'.internal.messages qs = Some qidm ==>
        indistinguishable qim qidm) =
      let imp ()
        : Lemma (requires
          adv.derive qd s_p'.know = Some qdt /\
          in_term qdt (Senc (Pair (SessionId qs) qim) s_p'.internal.key) /\
          PartialMap.sel s_q'.internal.messages qs = Some qidm)
          (ensures indistinguishable qim qidm) =
        _valid_resp_preserved qs qim qidm qd qdt
      in
      Classical.move_requires imp ()
    in
    Classical.forall_intro_2 helper
  in
  Classical.forall_intro_3 _valid_resp_quad;
  assert (valid_encrypted_responses_indistinguishable_from_stored_ideal_messages s_p' s_q')

private
let _recv_to_be_delivered_preserved
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_p': TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (s_q': TestedSystem.state term ideal_internal_state)
      (impl_pair: term)
      (ideal_pair: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        derivable s_p.know impl_pair /\
        derivable s_q.know ideal_pair /\
        s_p'.know == Seq.snoc s_p.know impl_pair /\
        s_q'.know == Seq.snoc s_q.know ideal_pair /\
        s_p'.internal.key == s_p.internal.key /\
        s_p'.internal.messages == s_p.internal.messages /\
        s_q'.internal.messages == s_q.internal.messages /\
        s_q'.internal.sim_key == s_q.internal.sim_key /\
        bijective_correspondence_on_derivations adv s_p'.know s_q'.know
          (smd_subst_bijection k k s_p.internal.messages))
      (ensures
        to_be_delivered_messages_already_derivable_by_same_derivation s_p' s_q') =
  let _to_be_delivered_pre
        (qs: session_id) (qim: term)
        (qd: derivation) (qdi qdia: term)
    : Lemma
      (requires
        adv.derive qd s_p'.know = Some qdi /\
        adv.derive qd s_q'.know = Some qdia /\
        in_term qdi (Senc (Pair (SessionId qs) qim) s_p'.internal.key) /\
        in_term qdia (Senc (SessionId qs) s_q'.internal.sim_key) /\
        Some? (PartialMap.sel s_q'.internal.messages qs))
      (ensures (
        let qidm = Some?.v (PartialMap.sel s_q'.internal.messages qs) in
        exists trigger_d.
          adv.derive trigger_d s_p'.know = Some (Pair (SessionId qs) qim) /\
          adv.derive trigger_d s_q'.know = Some (Pair (SessionId qs) qidm)))
      [SMTPat (adv.derive qd s_p'.know);
       SMTPat (in_term qdi (Senc (Pair (SessionId qs) qim) s_p'.internal.key));
       SMTPat (in_term qdia (Senc (SessionId qs) s_q'.internal.sim_key))] =
    let qidm = Some?.v (PartialMap.sel s_q'.internal.messages qs) in
    let bij = smd_subst_bijection k k s_p.internal.messages in
    // Establish qdia = bij.cright qdi via post-state bijective correspondence
    assert (adv.derive qd s_q'.know = Option.mapTot bij.cright (adv.derive qd s_p'.know));
    assert_norm (Option.mapTot bij.cright (Some qdi) = Some (bij.cright qdi));
    assert (adv.derive qd s_q'.know = Some (bij.cright qdi));
    assert (bij.cright qdi = qdia);
    // Get derivability of qdi from pre-state s_p.know
    observe_derivable_no_new_derivations s_p.know impl_pair qdi;
    observe_derivable_no_new_derivations s_q.know ideal_pair qdia;
    // Get a concrete derivation for qdi from s_p.know
    let d_pre = FStar.IndefiniteDescription.indefinite_description_ghost derivation
      (fun d -> adv.derive d s_p.know = Some qdi) in
    // By pre-state bijective correspondence, d_pre also derives qdia from s_q.know
    assert (adv.derive d_pre s_q.know = Option.mapTot bij.cright (adv.derive d_pre s_p.know));
    assert (adv.derive d_pre s_q.know = Some (bij.cright qdi));
    assert (adv.derive d_pre s_q.know = Some qdia);
    // Bridge key/sim_key/messages equalities for to_be_delivered conditions
    assert (in_term qdi (Senc (Pair (SessionId qs) qim) s_p.internal.key));
    assert (in_term qdia (Senc (SessionId qs) s_q.internal.sim_key));
    assert (PartialMap.sel s_q.internal.messages qs = Some qidm);
    // Apply to_be_delivered s_p s_q using d_pre as the shared derivation
    assert (exists trigger_d.
      adv.derive trigger_d s_p.know = Some (Pair (SessionId qs) qim) /\
      adv.derive trigger_d s_q.know = Some (Pair (SessionId qs) qidm));
    // Get concrete trigger and extend to post-states
    let td_old = FStar.IndefiniteDescription.indefinite_description_ghost derivation
      (fun td ->
        adv.derive td s_p.know = Some (Pair (SessionId qs) qim) /\
        adv.derive td s_q.know = Some (Pair (SessionId qs) qidm)) in
    append_preserves_derive td_old s_p.know (Seq.create 1 impl_pair);
    append_preserves_derive td_old s_q.know (Seq.create 1 ideal_pair)
  in
  assert (to_be_delivered_messages_already_derivable_by_same_derivation s_p' s_q')
#pop-options

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let smd_obs_bisim_observable_step_impl_recv_preserves_relation
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_p': TestedSystem.state term impl_internal_state)
    : Lemma
      (requires (
        let ideal_message = smd_bi_subst message s_p.internal.messages k k in
        let s_q' = smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message in
        smd_bisim_relation k s_p s_q /\
        smd_impl_protocol_receive_transition (s2p_state s_p)
          session
          (Pair (SessionId session) message)
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know (Pair (SessionId session) message) /\
        (smd_ideal_protocol_receive_transition (s2p_state s_q)
          session
          (Pair (SessionId session) ideal_message)
          (s2p_state s_q'))
      ))
      (ensures
        smd_bisim_relation k s_p' (smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message)) =
  let ideal_message = smd_bi_subst message s_p.internal.messages k k in
  let s_q' = smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message in
  let bij = smd_subst_bijection k k s_p'.internal.messages in
  let bij_old = smd_subst_bijection k k s_p.internal.messages in
  let impl_trigger_input = Senc (Pair (SessionId session) message) k in
  let ideal_trigger_input = Senc (SessionId session) k in
  let impl_pair = Pair (SessionId session) message in
  let ideal_pair = Pair (SessionId session) ideal_message in

  // The messages map is unchanged by a receive transition, so bij = bij_old.
  assert (s_p'.internal.messages == s_p.internal.messages);
  assert (s_q'.internal.messages == s_q.internal.messages);

  // === Bijective correspondence and static equivalence ===
  smd_obs_bisim_observable_step_impl_recv_preserves_bijective_correspondence
    k know0 s_p s_q session message s_p';
  smd_subst_bijection_maps_to_indistinguishable_terms k k s_p'.internal.messages;
  bijective_correspondence_implies_static_equivalence adv s_p'.know s_q'.know bij;

  // === Implementation and ideal invariants ===
  implementation_invariants_preserved_after_receive' session message s_p s_p';
  ideal_invariants_preserved_after_receive' session ideal_message s_q s_q';

  // === New knowledge term derivable from old knowledge ===
  // impl_trigger_input is in s_p.inputs (by recv_enabled), hence
  // derivable from s_p.know via bisim's inputs-derivability clause.
  assert (Bag.mem impl_trigger_input s_p.inputs);
  assert (derivable s_p.know impl_trigger_input);
  let d_trig = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_p.know = Some impl_trigger_input) in
  assert (adv.derive d_trig s_p.know = Some impl_trigger_input);
  // First, from impl_invariant_messages_consistent_with_knowledge:
  // impl.messages[session] = Some message.
  assert_norm (in_term impl_trigger_input
                       (Senc (Pair (SessionId session) message) k));
  assert (PartialMap.sel s_p.internal.messages session == Some message);
  // With messages[session] = Some message established, smd_bi_subst unfolds:
  // smd_bi_subst (Senc (Pair (SessionId session) message) k) messages k k
  //   = Senc (SessionId session) k = ideal_trigger_input.
  assert (smd_bi_subst impl_trigger_input s_p.internal.messages k k ==
          Senc (SessionId session) k);
  // From bijective correspondence, the same derivation on s_q.know yields
  // bij.cright impl_trigger_input = ideal_trigger_input.
  smd_subst_bijection_right k k s_p.internal.messages impl_trigger_input;
  assert (bij_old.cright impl_trigger_input == ideal_trigger_input);
  assert (adv.derive d_trig s_q.know == Some ideal_trigger_input);
  // From messages map correspondence:
  // ideal.messages[session] = Some (smd_bi_subst message ...) = Some ideal_message.
  assert (PartialMap.sel s_q.internal.messages session ==
    Option.mapTot (fun m -> smd_bi_subst m s_p.internal.messages k k)
      (PartialMap.sel s_p.internal.messages session));
  assert (PartialMap.sel s_q.internal.messages session == Some ideal_message);
  // Apply to_be_delivered with d=d_trig, derived_impl=impl_trigger_input,
  // derived_ideal=ideal_trigger_input to obtain a SHARED trigger derivation
  // that yields impl_pair from s_p.know and ideal_pair from s_q.know.
  assert_norm (in_term ideal_trigger_input ideal_trigger_input);
  assert (exists trigger_d.
    adv.derive trigger_d s_p.know = Some impl_pair /\
    adv.derive trigger_d s_q.know = Some ideal_pair);
  let d_pair = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d ->
       adv.derive d s_p.know = Some impl_pair /\
       adv.derive d s_q.know = Some ideal_pair) in
  assert (derivable s_p.know impl_pair);
  assert (derivable s_q.know ideal_pair);

  // === canonical_ideal preservation: derivations from s_q'.know reduce to s_q.know ===
  let _canonical_ideal_preserved (d: adv.derivation) (t: term)
    : Lemma
      (ensures adv.derive d s_q'.know = Some t ==> canonical_ideal t k) =
    if Some? (adv.derive d s_q'.know) && Some?.v (adv.derive d s_q'.know) = t
    then begin
      assert (derivable s_q'.know t);
      observe_derivable_no_new_derivations s_q.know ideal_pair t;
      assert (derivable s_q.know t)
    end
  in
  FStar.Classical.forall_intro_2 _canonical_ideal_preserved;

  // === no-ideal-form-senc preservation: derivations from s_p'.know reduce to s_p.know ===
  let _no_ideal_senc_preserved (d: adv.derivation) (t: term) (i: session_id)
    : Lemma
      (ensures adv.derive d s_p'.know = Some t ==>
               in_term t (Senc (SessionId i) k) == false) =
    if Some? (adv.derive d s_p'.know) && Some?.v (adv.derive d s_p'.know) = t
    then begin
      assert (derivable s_p'.know t);
      observe_derivable_no_new_derivations s_p.know impl_pair t;
      assert (derivable s_p.know t)
    end
  in
  FStar.Classical.forall_intro_3 _no_ideal_senc_preserved;

  // === Send transitions enabled iff: messages, key, sent_sessions unchanged ===
  // The recv transition removes a Senc-shaped input; send_enabled looks for a
  // Pair-shaped trigger.  Bag.mem on a Pair-shaped query is unaffected by
  // removing a Senc-shaped element.
  mem_remove_neq_forall impl_trigger_input s_p.inputs;
  mem_remove_neq_forall ideal_trigger_input s_q.inputs;
  let _send_enabled_post (sid: session_id) (m: term)
    : Lemma (ensures
        smd_impl_protocol_send_enabled (s2p_state s_p') sid m k <==>
        smd_ideal_protocol_send_enabled (s2p_state s_q') sid
          (smd_bi_subst m s_p'.internal.messages k k)) =
    let impl_query = Pair (SessionId sid) m in
    let ideal_query = Pair (SessionId sid) (smd_bi_subst m s_p'.internal.messages k k) in
    Bag.mem_remove impl_query impl_trigger_input s_p.inputs;
    Bag.mem_remove ideal_query ideal_trigger_input s_q.inputs;
    assert (Bag.mem impl_query s_p'.inputs == Bag.mem impl_query s_p.inputs);
    assert (Bag.mem ideal_query s_q'.inputs == Bag.mem ideal_query s_q.inputs);
    assert (Set.mem sid s_p'.internal.sent_sessions == Set.mem sid s_p.internal.sent_sessions);
    assert (Set.mem sid s_q'.internal.sim_sent_sessions == Set.mem sid s_q.internal.sim_sent_sessions);
    assert (smd_impl_protocol_send_enabled (s2p_state s_p) sid m k <==>
            smd_ideal_protocol_send_enabled (s2p_state s_q) sid
              (smd_bi_subst m s_p.internal.messages k k))
  in
  FStar.Classical.forall_intro_2 _send_enabled_post;

  // === Receive transitions enabled iff ===
  // For sid != session: Bag.mem on Senc(Pair(SessionId sid) m) k unaffected by
  // removing Senc(Pair(SessionId session) message) k.  received_sessions and
  // sim_received_sessions for sid unchanged.
  // For sid = session: both LHS and RHS are false (already in received sets).
  let _recv_enabled_post (sid: session_id) (m: term)
    : Lemma (ensures
        smd_impl_protocol_receive_enabled (s2p_state s_p') sid m <==>
        smd_ideal_protocol_receive_enabled (s2p_state s_q') sid
          (smd_bi_subst m s_p'.internal.messages k k)) =
    let impl_query = Senc (Pair (SessionId sid) m) k in
    let ideal_query = Senc (SessionId sid) k in
    if sid = session then begin
      assert (Set.mem sid s_p'.internal.received_sessions);
      assert (Set.mem sid s_q'.internal.sim_received_sessions);
      assert (~(smd_impl_protocol_receive_enabled (s2p_state s_p') sid m));
      assert (~(smd_ideal_protocol_receive_enabled (s2p_state s_q') sid
                  (smd_bi_subst m s_p'.internal.messages k k)))
    end else begin
      // sid != session: received_sessions unchanged for sid on both sides.
      assert (Set.mem sid s_p'.internal.received_sessions ==
              Set.mem sid s_p.internal.received_sessions);
      assert (Set.mem sid s_q'.internal.sim_received_sessions ==
              Set.mem sid s_q.internal.sim_received_sessions);
      // Bag.mem of the recv-shaped query is unaffected by removing the
      // recv trigger of a different session.
      Bag.mem_remove impl_query impl_trigger_input s_p.inputs;
      Bag.mem_remove ideal_query ideal_trigger_input s_q.inputs;
      assert (Bag.mem impl_query s_p'.inputs == Bag.mem impl_query s_p.inputs);
      assert (Bag.mem ideal_query s_q'.inputs == Bag.mem ideal_query s_q.inputs);
      // Use old bisim's recv_enabled_iff with messages map unchanged.
      assert (smd_impl_protocol_receive_enabled (s2p_state s_p) sid m <==>
              smd_ideal_protocol_receive_enabled (s2p_state s_q) sid
                (smd_bi_subst m s_p.internal.messages k k))
    end
  in
  FStar.Classical.forall_intro_2 _recv_enabled_post;

  // === Bag-count correspondence ===
  // The removed elements correspond under bij: bij.cright impl_trigger_input =
  // ideal_trigger_input.
  smd_subst_bijection_right k k s_p'.internal.messages impl_trigger_input;
  // Establish messages[session] = Some message via
  // impl_invariant_messages_consistent_with_knowledge.
  assert (Bag.mem impl_trigger_input s_p.inputs);
  assert (derivable s_p.know impl_trigger_input);
  let d_msg = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_p.know = Some impl_trigger_input) in
  assert_norm (in_term impl_trigger_input
                       (Senc (Pair (SessionId session) message) k));
  assert (PartialMap.sel s_p.internal.messages session ==
          Some message);
  assert_norm (smd_bi_subst impl_trigger_input s_p.internal.messages k k ==
               Senc (SessionId session) k);
  assert (bij.cright impl_trigger_input == ideal_trigger_input);

  // === valid_encrypted_responses & to_be_delivered preserved ===
  _recv_valid_encrypted_responses_preserved k s_p s_p' s_q s_q' impl_pair;
  _recv_to_be_delivered_preserved k s_p s_p' s_q s_q' impl_pair ideal_pair;

  // === Inputs derivability ===
  // s_p'.inputs is a sub-bag of s_p.inputs, and s_p'.know extends s_p.know.
  let _inputs_p_derivable (t: term)
    : Lemma (Bag.mem t s_p'.inputs ==> derivable s_p'.know t) =
    if Bag.mem t s_p'.inputs then begin
      Bag.mem_remove t impl_trigger_input s_p.inputs;
      assert (Bag.mem t s_p.inputs);
      assert (derivable s_p.know t);
      append_preserves_derivable s_p.know (Seq.create 1 impl_pair) t
    end
  in
  FStar.Classical.forall_intro _inputs_p_derivable;

  let _inputs_q_derivable (t: term)
    : Lemma (Bag.mem t s_q'.inputs ==> derivable s_q'.know t) =
    if Bag.mem t s_q'.inputs then begin
      Bag.mem_remove t ideal_trigger_input s_q.inputs;
      assert (Bag.mem t s_q.inputs);
      assert (derivable s_q.know t);
      append_preserves_derivable s_q.know (Seq.create 1 ideal_pair) t
    end
  in
  FStar.Classical.forall_intro _inputs_q_derivable;

  // === Per-conjunct checkpoint asserts to help F* split the final synthesis ===
  assert (statically_equivalent adv s_p'.know s_q'.know);
  assert (implementation_invariants s_p');
  assert (ideal_invariants s_q');
  assert (s_p'.internal.key == k);
  assert (s_q'.internal.sim_key == k);
  assert (send_equivalent_transitions_enabled_iff (s2p_state s_p') (s2p_state s_q'));
  assert (send_equivalent_transitions_completed_iff (s2p_state s_p') (s2p_state s_q'));
  assert (receive_equivalent_transitions_enabled_iff (s2p_state s_p') (s2p_state s_q'));
  assert (receive_equivalent_transitions_completed_iff (s2p_state s_p') (s2p_state s_q'));
  assert (valid_encrypted_responses_indistinguishable_from_stored_ideal_messages
            s_p'
            s_q');
  assert (to_be_delivered_messages_already_derivable_by_same_derivation
            s_p'
            s_q');
  assert (bijective_correspondence_on_derivations adv s_p'.know s_q'.know bij);
  assert (forall t.
    Bag.count s_p'.inputs t == Bag.count s_q'.inputs (bij.cright t));
  assert (forall (s: session_id).
    PartialMap.sel s_q'.internal.messages s ==
    Option.mapTot (fun m -> smd_bi_subst m s_p'.internal.messages k k)
      (PartialMap.sel s_p'.internal.messages s));
  assert (forall (d: adv.derivation) (t: term).
    adv.derive d s_q'.know = Some t ==> canonical_ideal t k);
  assert (forall (d: adv.derivation) (t: term) (i: session_id).
    adv.derive d s_p'.know = Some t ==> in_term t (Senc (SessionId i) k) == false);
  ()
#pop-options


#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let smd_obs_bisim_observable_step_ideal_recv_preserves_relation
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires (
        let impl_message = smd_bi_subst message s_p.internal.messages k k in
        let s_p' = smd_ideal_receive_impl_witness k s_p session message in
        smd_bisim_relation k s_p s_q /\
        (smd_ideal_protocol_receive_transition (s2p_state s_q)
          session
          (Pair (SessionId session) message)
          (s2p_state s_q')) /\
        smd_impl_protocol_receive_transition (s2p_state s_p)
          session
          (Pair (SessionId session) impl_message)
          (s2p_state s_p') /\
        s_q'.know == Seq.snoc s_q.know (Pair (SessionId session) message)
      ))
      (ensures (
        let s_p' = smd_ideal_receive_impl_witness k s_p session message in
        smd_bisim_relation k s_p' s_q')) =
  let impl_message = smd_bi_subst message s_p.internal.messages k k in
  let s_p' = smd_ideal_receive_impl_witness k s_p session message in
  let bij = smd_subst_bijection k k s_p'.internal.messages in
  let bij_old = smd_subst_bijection k k s_p.internal.messages in
  let impl_trigger_input = Senc (Pair (SessionId session) impl_message) k in
  let ideal_trigger_input = Senc (SessionId session) k in
  let impl_pair = Pair (SessionId session) impl_message in
  let ideal_pair = Pair (SessionId session) message in

  // The messages map is unchanged by a receive transition, so bij = bij_old.
  assert (s_p'.internal.messages == s_p.internal.messages);
  assert (s_q'.internal.messages == s_q.internal.messages);

  // === Bijective correspondence and static equivalence ===
  smd_obs_bisim_observable_step_ideal_recv_preserves_bijective_correspondence
    k know0 s_p s_q session message s_q';
  smd_subst_bijection_maps_to_indistinguishable_terms k k s_p'.internal.messages;
  bijective_correspondence_implies_static_equivalence adv s_p'.know s_q'.know bij;

  // === Implementation and ideal invariants ===
  implementation_invariants_preserved_after_receive' session impl_message s_p s_p';
  ideal_invariants_preserved_after_receive' session message s_q s_q';

  // === New knowledge term derivable from old knowledge ===
  // From ideal_recv_enabled precondition: s_q.messages[session] = Some message.
  assert (PartialMap.sel s_q.internal.messages session == Some message);
  // From messages-map correspondence: s_p.messages[session] = Some impl_message.
  assert (PartialMap.sel s_q.internal.messages session ==
    Option.mapTot (fun m -> smd_bi_subst m s_p.internal.messages k k)
      (PartialMap.sel s_p.internal.messages session));
  smd_subst_bijection_right k k s_p.internal.messages message;
  smd_subst_bijection_left k k s_p.internal.messages message;
  assert (bij_old.cleft (bij_old.cright message) == message);
  assert (PartialMap.sel s_p.internal.messages session == Some impl_message);
  // Bag.mem impl_trigger_input s_p.inputs from impl recv_enabled precondition.
  assert (Bag.mem impl_trigger_input s_p.inputs);
  assert (derivable s_p.know impl_trigger_input);
  let d_trig = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_p.know = Some impl_trigger_input) in
  assert (adv.derive d_trig s_p.know = Some impl_trigger_input);
  // With messages[session] = Some impl_message established, smd_bi_subst unfolds:
  // smd_bi_subst (Senc (Pair (SessionId session) impl_message) k) messages k k
  //   = Senc (SessionId session) k = ideal_trigger_input.
  assert (smd_bi_subst impl_trigger_input s_p.internal.messages k k ==
          Senc (SessionId session) k);
  smd_subst_bijection_right k k s_p.internal.messages impl_trigger_input;
  assert (bij_old.cright impl_trigger_input == ideal_trigger_input);
  assert (adv.derive d_trig s_q.know == Some ideal_trigger_input);
  // Also Bag.mem ideal_trigger_input s_q.inputs from ideal recv_enabled precondition.
  assert (Bag.mem ideal_trigger_input s_q.inputs);
  // Apply to_be_delivered with d=d_trig, derived_impl=impl_trigger_input,
  // derived_ideal=ideal_trigger_input to obtain a SHARED trigger derivation
  // that yields impl_pair from s_p.know and ideal_pair from s_q.know.
  assert_norm (in_term impl_trigger_input
                       (Senc (Pair (SessionId session) impl_message) k));
  assert_norm (in_term ideal_trigger_input ideal_trigger_input);
  assert (exists trigger_d.
    adv.derive trigger_d s_p.know = Some impl_pair /\
    adv.derive trigger_d s_q.know = Some ideal_pair);
  let d_pair = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d ->
       adv.derive d s_p.know = Some impl_pair /\
       adv.derive d s_q.know = Some ideal_pair) in
  assert (derivable s_p.know impl_pair);
  assert (derivable s_q.know ideal_pair);

  // === canonical_ideal preservation: derivations from s_q'.know reduce to s_q.know ===
  let _canonical_ideal_preserved (d: adv.derivation) (t: term)
    : Lemma
      (ensures adv.derive d s_q'.know = Some t ==> canonical_ideal t k) =
    if Some? (adv.derive d s_q'.know) && Some?.v (adv.derive d s_q'.know) = t
    then begin
      assert (derivable s_q'.know t);
      observe_derivable_no_new_derivations s_q.know ideal_pair t;
      assert (derivable s_q.know t)
    end
  in
  FStar.Classical.forall_intro_2 _canonical_ideal_preserved;

  // === no-ideal-form-senc preservation: derivations from s_p'.know reduce to s_p.know ===
  let _no_ideal_senc_preserved (d: adv.derivation) (t: term) (i: session_id)
    : Lemma
      (ensures adv.derive d s_p'.know = Some t ==>
               in_term t (Senc (SessionId i) k) == false) =
    if Some? (adv.derive d s_p'.know) && Some?.v (adv.derive d s_p'.know) = t
    then begin
      assert (derivable s_p'.know t);
      observe_derivable_no_new_derivations s_p.know impl_pair t;
      assert (derivable s_p.know t)
    end
  in
  FStar.Classical.forall_intro_3 _no_ideal_senc_preserved;

  // === Send transitions enabled iff: messages, key, sent_sessions unchanged ===
  mem_remove_neq_forall impl_trigger_input s_p.inputs;
  mem_remove_neq_forall ideal_trigger_input s_q.inputs;
  let _send_enabled_post (sid: session_id) (m: term)
    : Lemma (ensures
        smd_impl_protocol_send_enabled (s2p_state s_p') sid m k <==>
        smd_ideal_protocol_send_enabled (s2p_state s_q') sid
          (smd_bi_subst m s_p'.internal.messages k k)) =
    let impl_query = Pair (SessionId sid) m in
    let ideal_query = Pair (SessionId sid) (smd_bi_subst m s_p'.internal.messages k k) in
    Bag.mem_remove impl_query impl_trigger_input s_p.inputs;
    Bag.mem_remove ideal_query ideal_trigger_input s_q.inputs;
    assert (Bag.mem impl_query s_p'.inputs == Bag.mem impl_query s_p.inputs);
    assert (Bag.mem ideal_query s_q'.inputs == Bag.mem ideal_query s_q.inputs);
    assert (Set.mem sid s_p'.internal.sent_sessions == Set.mem sid s_p.internal.sent_sessions);
    assert (Set.mem sid s_q'.internal.sim_sent_sessions == Set.mem sid s_q.internal.sim_sent_sessions);
    assert (smd_impl_protocol_send_enabled (s2p_state s_p) sid m k <==>
            smd_ideal_protocol_send_enabled (s2p_state s_q) sid
              (smd_bi_subst m s_p.internal.messages k k))
  in
  FStar.Classical.forall_intro_2 _send_enabled_post;

  // === Receive transitions enabled iff ===
  let _recv_enabled_post (sid: session_id) (m: term)
    : Lemma (ensures
        smd_impl_protocol_receive_enabled (s2p_state s_p') sid m <==>
        smd_ideal_protocol_receive_enabled (s2p_state s_q') sid
          (smd_bi_subst m s_p'.internal.messages k k)) =
    let impl_query = Senc (Pair (SessionId sid) m) k in
    let ideal_query = Senc (SessionId sid) k in
    if sid = session then begin
      assert (Set.mem sid s_p'.internal.received_sessions);
      assert (Set.mem sid s_q'.internal.sim_received_sessions);
      assert (~(smd_impl_protocol_receive_enabled (s2p_state s_p') sid m));
      assert (~(smd_ideal_protocol_receive_enabled (s2p_state s_q') sid
                  (smd_bi_subst m s_p'.internal.messages k k)))
    end else begin
      assert (Set.mem sid s_p'.internal.received_sessions ==
              Set.mem sid s_p.internal.received_sessions);
      assert (Set.mem sid s_q'.internal.sim_received_sessions ==
              Set.mem sid s_q.internal.sim_received_sessions);
      Bag.mem_remove impl_query impl_trigger_input s_p.inputs;
      Bag.mem_remove ideal_query ideal_trigger_input s_q.inputs;
      assert (Bag.mem impl_query s_p'.inputs == Bag.mem impl_query s_p.inputs);
      assert (Bag.mem ideal_query s_q'.inputs == Bag.mem ideal_query s_q.inputs);
      assert (smd_impl_protocol_receive_enabled (s2p_state s_p) sid m <==>
              smd_ideal_protocol_receive_enabled (s2p_state s_q) sid
                (smd_bi_subst m s_p.internal.messages k k))
    end
  in
  FStar.Classical.forall_intro_2 _recv_enabled_post;

  // === Bag-count correspondence ===
  smd_subst_bijection_right k k s_p'.internal.messages impl_trigger_input;
  assert (bij.cright impl_trigger_input == ideal_trigger_input);

  // === valid_encrypted_responses & to_be_delivered preserved ===
  _recv_valid_encrypted_responses_preserved k s_p s_p' s_q s_q' impl_pair;
  _recv_to_be_delivered_preserved k s_p s_p' s_q s_q' impl_pair ideal_pair;

  // === Inputs derivability ===
  let _inputs_p_derivable (t: term)
    : Lemma (Bag.mem t s_p'.inputs ==> derivable s_p'.know t) =
    if Bag.mem t s_p'.inputs then begin
      Bag.mem_remove t impl_trigger_input s_p.inputs;
      assert (Bag.mem t s_p.inputs);
      assert (derivable s_p.know t);
      append_preserves_derivable s_p.know (Seq.create 1 impl_pair) t
    end
  in
  FStar.Classical.forall_intro _inputs_p_derivable;

  let _inputs_q_derivable (t: term)
    : Lemma (Bag.mem t s_q'.inputs ==> derivable s_q'.know t) =
    if Bag.mem t s_q'.inputs then begin
      Bag.mem_remove t ideal_trigger_input s_q.inputs;
      assert (Bag.mem t s_q.inputs);
      assert (derivable s_q.know t);
      append_preserves_derivable s_q.know (Seq.create 1 ideal_pair) t
    end
  in
  FStar.Classical.forall_intro _inputs_q_derivable;

  // === Per-conjunct checkpoint asserts ===
  assert (statically_equivalent adv s_p'.know s_q'.know);
  assert (implementation_invariants s_p');
  assert (ideal_invariants s_q');
  assert (s_p'.internal.key == k);
  assert (s_q'.internal.sim_key == k);
  assert (send_equivalent_transitions_enabled_iff (s2p_state s_p') (s2p_state s_q'));
  assert (send_equivalent_transitions_completed_iff (s2p_state s_p') (s2p_state s_q'));
  assert (receive_equivalent_transitions_enabled_iff (s2p_state s_p') (s2p_state s_q'));
  assert (receive_equivalent_transitions_completed_iff (s2p_state s_p') (s2p_state s_q'));
  assert (valid_encrypted_responses_indistinguishable_from_stored_ideal_messages
            s_p'
            s_q');
  assert (to_be_delivered_messages_already_derivable_by_same_derivation
            s_p'
            s_q');
  assert (bijective_correspondence_on_derivations adv s_p'.know s_q'.know bij);
  assert (forall t.
    Bag.count s_p'.inputs t == Bag.count s_q'.inputs (bij.cright t));
  assert (forall (s: session_id).
    PartialMap.sel s_q'.internal.messages s ==
    Option.mapTot (fun m -> smd_bi_subst m s_p'.internal.messages k k)
      (PartialMap.sel s_p'.internal.messages s));
  assert (forall (d: adv.derivation) (t: term).
    adv.derive d s_q'.know = Some t ==> canonical_ideal t k);
  assert (forall (d: adv.derivation) (t: term) (i: session_id).
    adv.derive d s_p'.know = Some t ==> in_term t (Senc (SessionId i) k) == false);
  ()
#pop-options

#pop-options
