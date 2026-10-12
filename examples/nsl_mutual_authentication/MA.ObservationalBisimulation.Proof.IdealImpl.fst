module MA.ObservationalBisimulation.Proof.IdealImpl

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
open MA.ObservationalBisimulation.Witnesses.IdealInvariants
open MA.TestedProtocols
open MA.PartitioningRole

open MA.ObservationalBisimulation.Proof.Common

open MA.ObservationalBisimulation.Proof.InitiatorStartSendMessage1
open MA.ObservationalBisimulation.Proof.ResponderReplyDeliverMessage2
open MA.ObservationalBisimulation.Proof.SendMessage3InitiatorAck
open MA.ObservationalBisimulation.Proof.InitiatorOutputDeliver
open MA.ObservationalBisimulation.Proof.ResponderOutput
open MA.ObservationalBisimulation.Proof.InputStep

/// ---------------------------------------------------------------------------
/// Infeasibility of two consecutive same-id internal transitions.
///
/// The ideal protocol's internal transitions for a fixed `lid` are
/// `ma_ideal_initiate(lid)` and (only when `lid.role == Responder`)
/// `ma_sim_receive_message3(lid)`.  In every combination, the second transition
/// is disabled at the post-state of the first; this is what bounds a
/// single-partition eventually-observable sequence to at most one internal step
/// and therefore length <= 2.
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries no"
private
let two_same_lid_internals_infeasible
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_q: ideal_system_state)
      (lid: ma_label_id)
      (s_mid s_mid2: ideal_system_state)
    : Lemma
      (requires
        ma_ideal_request_matches_sim_session s_q /\
        ma_ideal_state_inv (s2p_state s_q) /\
        // Formerly the `ma_ideal_inv_{initiator,responder}_session_has_request`
        // conjuncts of `ma_ideal_state_inv`; these were factored out of the
        // proto-state invariant into the system-level `ma_ideal_system_inv` (as
        // `ma_sim_session_matches_ideal_request`), which the call site exposes
        // via `ma_ideal_system_inv_elim`.
        ma_sim_session_matches_ideal_request s_q /\
        (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Internal lid) s_mid /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Internal lid) s_mid2)
      (ensures False) =
  let i = lid.session in
  let pP = lid.party in
  let qQ = lid.peer in
  let r = lid.role in
  let s_qp = s2p_state s_q in
  let s_midp = s2p_state s_mid in
  // The first internal: initiate or (Responder) recv3.
  // After initiate(lid), `requests[i]` contains a party-pP request, so a second
  // initiate(lid) is disabled, and recv3(lid) would need a responder session for
  // pP (created only by send_message2, not by initiate), which under
  // `request_matches_sim_session` would in turn require a Responder request.
  // After recv3(lid), `output_forwarded` is set, so a second recv3(lid) is
  // disabled, and initiate(lid) is disabled because recv3's responder session
  // implies a party-pP request already exists (H_resp).
  ()
#pop-options


/// ---------------------------------------------------------------------------
/// Length-1 observable: `[Observable eff lid]` (no internal prefix).
///
/// Feasible canonical shapes:
///   * NetSend / Initiator with `ma_sim_send_message3`  -> impl `nsl_initiator_ack`
///   * IoSend  / Initiator with `ma_ideal_deliver`      -> impl `nsl_initiator_output`
/// Infeasible-from-a-related-state shapes (discharged to `False`):
///   * NetSend / Initiator with `ma_sim_send_message1` alone
///   * NetSend / Responder with `ma_sim_send_message2` alone
///   * IoSend  / Responder with `ma_ideal_deliver` alone
/// ---------------------------------------------------------------------------

/// `ma_sim_send_message1` alone (no preceding `ma_ideal_initiate`) is infeasible
/// from a related state: enabledness puts `Authenticating(initiator, .., Initiator)`
/// on the ideal->sim channel, which (H_auth_init) forces an `Initiator` request,
/// which (`ma_ideal_request_matches_sim_session`) forces a `SimInitiatorSession`
/// for `initiator` — contradicting send_message1's "no sim session" precondition.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries no"
private
let send_message1_alone_infeasible
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_sim_send_message1_enabled (s2p_state s_q)
          session initiator responder initiator_nonce responder_pubkey)
      (ensures False) =
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  // Authenticating in channel ==> Initiator request recorded (H_auth_init).
  assert (Set.mem ({ party = initiator; peer = responder; role = Initiator })
            (ma_session_requests (s2p_state s_q) session));
  // request ==> SimInitiatorSession for initiator (relation conjunct).
  assert (ma_ideal_request_matches_sim_session s_q);
  assert (Some? (ma_get_sim_participant_session_state (s2p_state s_q) initiator session));
  ()
#pop-options

/// `ma_sim_send_message2` alone (no preceding `ma_ideal_initiate`) is infeasible
/// from a related state, dual to `send_message1_alone_infeasible` via H_auth_resp.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries no"
private
let send_message2_alone_infeasible
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_sim_send_message2_enabled (s2p_state s_q)
          session responder initiator initiator_nonce responder_nonce responder_key initiator_pubkey)
      (ensures False) =
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  assert (Set.mem ({ party = responder; peer = initiator; role = Responder })
            (ma_session_requests (s2p_state s_q) session));
  assert (ma_ideal_request_matches_sim_session s_q);
  assert (Some? (ma_get_sim_participant_session_state (s2p_state s_q) responder session));
  ()
#pop-options

/// Length-1 observable step of the ideal system, matched by the implementation.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries always"
private
let ma_obs_bisim_observable_step_ideal_len1
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (eff: ma_effect)
      (lid: ma_label_id)
      (s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Observable eff lid) s_q')
      (ensures
        exists (lbls': list system_label) (s_p': impl_system_state).
          label_effects lbls' == [ma_observable_effect eff] /\
          eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls' s_p' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  let session = lid.session in
  let party = lid.party in
  let peer = lid.peer in
  // Extract the emitted term `t` and the underlying ideal protocol transition.
  let p_t (t: term) : prop =
    ma_ideal_protocol_transition (s2p_state s_q) (Protocol.Observable eff t lid) (s2p_state s_q') /\
    s_q'.know == Seq.snoc s_q.know t
  in
  assert (exists t. p_t t);
  let t = FStar.IndefiniteDescription.indefinite_description_ghost term p_t in
  assert (p_t t);
  match eff with
  | NetSend ->
    (match lid.role with
     | Initiator ->
       // `ma_sim_send_message1` (infeasible alone) or `ma_sim_send_message3`.
       assert (ma_sim_send_message1_protocol_transition (s2p_state s_q) session party peer t (s2p_state s_q') \/
               ma_sim_send_message3_protocol_transition (s2p_state s_q) session party peer t (s2p_state s_q'));
       if FStar.IndefiniteDescription.strong_excluded_middle
            (ma_sim_send_message3_protocol_transition (s2p_state s_q) session party peer t (s2p_state s_q'))
       then (
         // initiator-ack case (canonical, feasible).
         let p_rnonce (rnonce: nonce) : prop =
           exists (ikey: priv_key) (rpub: term {PubKey? rpub}).
             ma_sim_send_message3_enabled (s2p_state s_q) session party peer rnonce ikey rpub /\
             t == ma_nsl_message3_term session party peer rnonce rpub /\
             (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q) session party peer rnonce ikey
         in
         assert (exists rnonce. p_rnonce rnonce);
         let responder_nonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_rnonce in
         assert (p_rnonce responder_nonce);
         let p_ikey (ikey: priv_key) : prop =
           exists (rpub: term {PubKey? rpub}).
             ma_sim_send_message3_enabled (s2p_state s_q) session party peer responder_nonce ikey rpub /\
             t == ma_nsl_message3_term session party peer responder_nonce rpub /\
             (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q) session party peer responder_nonce ikey
         in
         assert (exists ikey. p_ikey ikey);
         let initiator_key = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_ikey in
         assert (p_ikey initiator_key);
         let p_rpub (rpub: term {PubKey? rpub}) : prop =
           ma_sim_send_message3_enabled (s2p_state s_q) session party peer responder_nonce initiator_key rpub /\
           t == ma_nsl_message3_term session party peer responder_nonce rpub /\
           (s2p_state s_q') == ma_sim_send_message3_state (s2p_state s_q) session party peer responder_nonce initiator_key
         in
         assert (exists (rpub: term {PubKey? rpub}). p_rpub rpub);
         let responder_pubkey =
           FStar.IndefiniteDescription.indefinite_description_ghost (rpub: term {PubKey? rpub}) p_rpub in
         assert (p_rpub responder_pubkey);
         let s_p' = ma_ideal_send_message3_impl_witness
           s_p session party peer responder_nonce initiator_key responder_pubkey in
         ma_obs_bisim_observable_step_ideal_send_message3
           corrupt key_directory know0 s_p s_q session party peer
           responder_nonce initiator_key responder_pubkey s_q';
         ma_obs_bisim_observable_step_ideal_send_message3_preserves_relation
           corrupt key_directory s_p s_q session party peer
           responder_nonce initiator_key responder_pubkey s_q';
         assert_norm (label_effects ([TestedSystem.Observable NetSend lid] <: list system_label)
                      == [ma_observable_effect NetSend])
       ) else (
         // send_message1 alone: infeasible.
         assert (ma_sim_send_message1_protocol_transition (s2p_state s_q) session party peer t (s2p_state s_q'));
         let p_in (inonce: nonce) : prop =
           exists (rpub: term {PubKey? rpub}).
             ma_sim_send_message1_enabled (s2p_state s_q) session party peer inonce rpub /\
             t == ma_nsl_message1_term session party peer inonce rpub /\
             (s2p_state s_q') == ma_sim_send_message1_state (s2p_state s_q) session party peer inonce
         in
         assert (exists inonce. p_in inonce);
         let inonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_in in
         assert (p_in inonce);
         let p_pub (rpub: term {PubKey? rpub}) : prop =
           ma_sim_send_message1_enabled (s2p_state s_q) session party peer inonce rpub /\
           t == ma_nsl_message1_term session party peer inonce rpub /\
           (s2p_state s_q') == ma_sim_send_message1_state (s2p_state s_q) session party peer inonce
         in
         assert (exists (rpub: term {PubKey? rpub}). p_pub rpub);
         let rpub = FStar.IndefiniteDescription.indefinite_description_ghost (rpub: term {PubKey? rpub}) p_pub in
         assert (p_pub rpub);
         send_message1_alone_infeasible corrupt key_directory s_p s_q session party peer inonce rpub)
     | Responder ->
       // `ma_sim_send_message2` alone: infeasible.
       assert (ma_sim_send_message2_protocol_transition (s2p_state s_q) session party peer t (s2p_state s_q'));
       let p_in (inonce: nonce) : prop =
         exists (rnonce: nonce) (rkey: priv_key) (ipub: term {PubKey? ipub}).
           ma_sim_send_message2_enabled (s2p_state s_q) session party peer inonce rnonce rkey ipub /\
           t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
           (s2p_state s_q') == ma_sim_send_message2_state (s2p_state s_q) session party peer inonce rnonce rkey
       in
       assert (exists inonce. p_in inonce);
       let inonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_in in
       assert (p_in inonce);
       let p_rn (rnonce: nonce) : prop =
         exists (rkey: priv_key) (ipub: term {PubKey? ipub}).
           ma_sim_send_message2_enabled (s2p_state s_q) session party peer inonce rnonce rkey ipub /\
           t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
           (s2p_state s_q') == ma_sim_send_message2_state (s2p_state s_q) session party peer inonce rnonce rkey
       in
       assert (exists rnonce. p_rn rnonce);
       let rnonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_rn in
       assert (p_rn rnonce);
       let p_rk (rkey: priv_key) : prop =
         exists (ipub: term {PubKey? ipub}).
           ma_sim_send_message2_enabled (s2p_state s_q) session party peer inonce rnonce rkey ipub /\
           t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
           (s2p_state s_q') == ma_sim_send_message2_state (s2p_state s_q) session party peer inonce rnonce rkey
       in
       assert (exists rkey. p_rk rkey);
       let rkey = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_rk in
       assert (p_rk rkey);
       let p_ip (ipub: term {PubKey? ipub}) : prop =
         ma_sim_send_message2_enabled (s2p_state s_q) session party peer inonce rnonce rkey ipub /\
         t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
         (s2p_state s_q') == ma_sim_send_message2_state (s2p_state s_q) session party peer inonce rnonce rkey
       in
       assert (exists (ipub: term {PubKey? ipub}). p_ip ipub);
       let ipub = FStar.IndefiniteDescription.indefinite_description_ghost (ipub: term {PubKey? ipub}) p_ip in
       assert (p_ip ipub);
       send_message2_alone_infeasible corrupt key_directory s_p s_q session party peer inonce rnonce rkey ipub)
  | IoSend ->
    // `ma_ideal_deliver` at (session, party, peer, role).
    assert (ma_ideal_deliver_protocol_transition (s2p_state s_q) session party peer lid.role t (s2p_state s_q'));
    (match lid.role with
     | Initiator ->
       // deliver-initiator (canonical, feasible).  Establish the impl-side
       // enabledness from the initiator-output iff (deliver enabled at s_q is
       // exactly the iff's right-hand side).
       assert (ma_ideal_deliver_enabled (s2p_state s_q) session party peer Initiator);
       assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance
                 s_p s_q session party peer);
       assert (ma_nsl_initiator_output_enabled (s2p_state s_p) session party peer);
       let s_p' = ma_ideal_deliver_initiator_impl_witness s_p session party peer in
       ma_obs_bisim_observable_step_ideal_deliver_initiator
         corrupt key_directory know0 s_p s_q session party peer s_q';
       ma_obs_bisim_observable_step_ideal_deliver_initiator_preserves_relation
         corrupt key_directory s_p s_q session party peer s_q';
       assert_norm (label_effects ([TestedSystem.Observable IoSend lid] <: list system_label)
                    == [ma_observable_effect IoSend])
     | Responder ->
       // A STANDALONE length-1 `ma_ideal_deliver(Responder)` (no preceding
       // `ma_sim_receive_message3`) is INFEASIBLE from a related state:
       //   * deliver enabled puts `Output(session, party)` (responder direction)
       //     in flight in `sim_to_ideal_channel`;
       //   * by `ma_output_token_matches_sim_phase`, `party`'s simulator session
       //     is therefore a `SimResponderSession` with `output_forwarded = true`;
       //   * by `ma_responder_session_correspondence`, the impl responder session
       //     for `party` exists and has `output_sent == output_forwarded == true`;
       //   * but `ma_responder_output_token_matches_impl_pending_output` (relation
       //     conjunct) forces that same impl responder session to have
       //     `not output_sent` while the token is in flight.  Contradiction.
       assert (ma_ideal_deliver_enabled (s2p_state s_q) session party peer Responder);
       // token in flight on the sim-to-ideal channel.
       assert (Set.mem (ma_output_term session party) s_q.internal.sim_to_ideal_channel);
       // phase invariant: the token pins `party`'s sim session to a
       // `SimResponderSession` with `output_forwarded` set.
       ma_ideal_system_inv_elim corrupt key_directory s_q;
       assert (ma_output_token_matches_sim_phase s_q);
       assert (Some? (ma_sim_responder_session_state (s2p_state s_q) party session));
       assert ((Some?.v (ma_sim_responder_session_state (s2p_state s_q) party session)).output_forwarded);
       // responder correspondence: impl responder session exists, output_sent ==
       // output_forwarded == true.
       assert (ma_responder_session_correspondence s_p s_q);
       assert (Some? (ma_responder_session_state (s2p_state s_p) party session));
       assert ((Some?.v (ma_responder_session_state (s2p_state s_p) party session)).output_sent);
       // new relation conjunct: token in flight ==> impl responder not output_sent.
       assert (ma_responder_output_token_matches_impl_pending_output s_p s_q);
       assert (not (Some?.v (ma_responder_session_state (s2p_state s_p) party session)).output_sent);
       ())
#pop-options

/// ---------------------------------------------------------------------------
/// Length-2 observable: `[Internal lid; Observable eff lid]`.
///
/// Because both labels share one `ma_label_id` (role-sensitive partition), the
/// internal step and the observable step carry the same `lid`.  The feasible
/// canonical shapes are:
///   * `ma_ideal_initiate(Initiator); ma_sim_send_message1`  -> impl `nsl_initiator_start`
///   * `ma_ideal_initiate(Responder); ma_sim_send_message2`  -> impl `nsl_responder_reply`
///   * `ma_sim_receive_message3(Responder); ma_ideal_deliver(Responder)`
///                                                           -> impl `nsl_responder_output`
/// All other same-`lid` internal/observable combinations are infeasible from a
/// related state.
/// ---------------------------------------------------------------------------

#push-options "--fuel 4 --ifuel 4 --z3rlimit 120 --split_queries always"
private
let ma_obs_bisim_observable_step_ideal_len2
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (lid: ma_label_id)
      (eff: ma_effect)
      (s_mid s_q': ideal_system_state)
    : Lemma
      (requires
        ma_bisim_relation corrupt key_directory s_p s_q /\
        (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Internal lid) s_mid /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Observable eff lid) s_q')
      (ensures
        exists (lbls': list system_label) (s_p': impl_system_state).
          label_effects lbls' == [ma_observable_effect eff] /\
          eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls' s_p' /\
          ma_bisim_relation corrupt key_directory s_p' s_q') =
  let session = lid.session in
  let party = lid.party in
  let peer = lid.peer in
  let s_qp = s2p_state s_q in
  let s_midp = s2p_state s_mid in
  // The internal step is `ma_ideal_initiate(lid)` or (Responder) `recv3(lid)`,
  // with `s_mid.know == s_q.know`.
  assert (s_mid.know == s_q.know);
  // Extract the observable term `t` and the underlying ideal protocol transition
  // from `s_mid`.
  let p_t (t: term) : prop =
    ma_ideal_protocol_transition s_midp (Protocol.Observable eff t lid) (s2p_state s_q') /\
    s_q'.know == Seq.snoc s_mid.know t
  in
  assert (exists t. p_t t);
  let t = FStar.IndefiniteDescription.indefinite_description_ghost term p_t in
  assert (p_t t);
  // Case on whether the internal step is `ma_ideal_initiate`.
  if FStar.IndefiniteDescription.strong_excluded_middle
       (ma_ideal_initiate_protocol_transition s_qp session party peer lid.role s_midp)
  then (
    // tau = initiate(lid). s_mid = initiate_state.
    assert (ma_ideal_initiate_enabled s_qp session party peer lid.role);
    assert (s_midp == ma_ideal_initiate_state s_qp session party peer lid.role);
    match eff with
    | NetSend ->
      (match lid.role with
       | Initiator ->
         // alpha must be send_message1 (send_message3 needs a sim session that
         // initiate does not create -> infeasible).
         assert (ma_sim_send_message1_protocol_transition s_midp session party peer t (s2p_state s_q') \/
                 ma_sim_send_message3_protocol_transition s_midp session party peer t (s2p_state s_q'));
         if FStar.IndefiniteDescription.strong_excluded_middle
              (ma_sim_send_message1_protocol_transition s_midp session party peer t (s2p_state s_q'))
         then (
           // canonical: initiate(Initiator); send_message1.
           let p_in (inonce: nonce) : prop =
             exists (rpub: term {PubKey? rpub}).
               ma_sim_send_message1_enabled s_midp session party peer inonce rpub /\
               t == ma_nsl_message1_term session party peer inonce rpub /\
               (s2p_state s_q') == ma_sim_send_message1_state s_midp session party peer inonce
           in
           assert (exists inonce. p_in inonce);
           let inonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_in in
           assert (p_in inonce);
           let p_pub (rpub: term {PubKey? rpub}) : prop =
             ma_sim_send_message1_enabled s_midp session party peer inonce rpub /\
             t == ma_nsl_message1_term session party peer inonce rpub /\
             (s2p_state s_q') == ma_sim_send_message1_state s_midp session party peer inonce
           in
           assert (exists (rpub: term {PubKey? rpub}). p_pub rpub);
           let rpub = FStar.IndefiniteDescription.indefinite_description_ghost (rpub: term {PubKey? rpub}) p_pub in
           assert (p_pub rpub);
           // Establish the impl-side enabledness via the initiator-start iff.
           assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance
                     s_p s_q session party peer inonce rpub);
           assert (ma_nsl_initiator_start_enabled (s2p_state s_p) session party peer inonce rpub);
           let s_p' = ma_ideal_send_message1_impl_witness s_p session party peer inonce rpub in
           ma_obs_bisim_observable_step_ideal_send_message1
             corrupt key_directory know0 s_p s_q session party peer inonce rpub s_q';
           ma_obs_bisim_observable_step_ideal_send_message1_preserves_relation
             corrupt key_directory s_p s_q session party peer inonce rpub s_q';
           assert_norm (label_effects ([TestedSystem.Observable NetSend lid] <: list system_label)
                        == [ma_observable_effect NetSend])
         ) else (
           // initiate(Initiator); send_message3: infeasible. send_message3 needs a
           // SimInitiatorSession for party at s_mid; initiate preserves sessions, so
           // it exists at s_q; H_init then forces an Initiator party-request at s_q,
           // contradicting initiate's "no party request" precondition.
           assert (ma_sim_send_message3_protocol_transition s_midp session party peer t (s2p_state s_q'));
           ma_ideal_system_inv_elim corrupt key_directory s_q;
           assert (Some? (ma_sim_initiator_session_state s_midp party session));
           assert (ma_get_sim_participant_session_state s_midp party session ==
                   ma_get_sim_participant_session_state s_qp party session);
           assert (Some? (ma_sim_initiator_session_state s_qp party session));
           ())
       | Responder ->
         // canonical: initiate(Responder); send_message2.
         assert (ma_sim_send_message2_protocol_transition s_midp session party peer t (s2p_state s_q'));
         let p_in (inonce: nonce) : prop =
           exists (rnonce: nonce) (rkey: priv_key) (ipub: term {PubKey? ipub}).
             ma_sim_send_message2_enabled s_midp session party peer inonce rnonce rkey ipub /\
             t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
             (s2p_state s_q') == ma_sim_send_message2_state s_midp session party peer inonce rnonce rkey
         in
         assert (exists inonce. p_in inonce);
         let inonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_in in
         assert (p_in inonce);
         let p_rn (rnonce: nonce) : prop =
           exists (rkey: priv_key) (ipub: term {PubKey? ipub}).
             ma_sim_send_message2_enabled s_midp session party peer inonce rnonce rkey ipub /\
             t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
             (s2p_state s_q') == ma_sim_send_message2_state s_midp session party peer inonce rnonce rkey
         in
         assert (exists rnonce. p_rn rnonce);
         let rnonce = FStar.IndefiniteDescription.indefinite_description_ghost nonce p_rn in
         assert (p_rn rnonce);
         let p_rk (rkey: priv_key) : prop =
           exists (ipub: term {PubKey? ipub}).
             ma_sim_send_message2_enabled s_midp session party peer inonce rnonce rkey ipub /\
             t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
             (s2p_state s_q') == ma_sim_send_message2_state s_midp session party peer inonce rnonce rkey
         in
         assert (exists rkey. p_rk rkey);
         let rkey = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_rk in
         assert (p_rk rkey);
         let p_ip (ipub: term {PubKey? ipub}) : prop =
           ma_sim_send_message2_enabled s_midp session party peer inonce rnonce rkey ipub /\
           t == ma_nsl_message2_term session peer party inonce rnonce ipub /\
           (s2p_state s_q') == ma_sim_send_message2_state s_midp session party peer inonce rnonce rkey
         in
         assert (exists (ipub: term {PubKey? ipub}). p_ip ipub);
         let ipub = FStar.IndefiniteDescription.indefinite_description_ghost (ipub: term {PubKey? ipub}) p_ip in
         assert (p_ip ipub);
         // Establish impl-side enabledness via the responder-reply iff.
         assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance
                   s_p s_q session party peer inonce rnonce rkey ipub);
         assert (ma_nsl_responder_reply_enabled (s2p_state s_p) session party peer inonce rnonce rkey ipub);
         let s_p' = ma_ideal_send_message2_impl_witness s_p session party peer inonce rnonce rkey ipub in
         ma_obs_bisim_observable_step_ideal_send_message2
           corrupt key_directory know0 s_p s_q session party peer inonce rnonce rkey ipub s_q';
         ma_obs_bisim_observable_step_ideal_send_message2_preserves_relation
           corrupt key_directory s_p s_q session party peer inonce rnonce rkey ipub s_q';
         assert_norm (label_effects ([TestedSystem.Observable NetSend lid] <: list system_label)
                      == [ma_observable_effect NetSend]))
    | IoSend ->
      // tau = initiate(lid); alpha = deliver(lid). Infeasible: deliver reads
      // Output(session, party) (initiate preserves it), so I1a forces a party
      // request at s_q, contradicting initiate's "no party request" precondition.
      assert (ma_ideal_deliver_protocol_transition s_midp session party peer lid.role t (s2p_state s_q'));
      ma_ideal_system_inv_elim corrupt key_directory s_q;
      ma_ideal_initiate_state_preserves_sim_to_ideal_channel s_qp session party peer lid.role;
      assert (Set.mem (ma_output_term session party) s_qp.internal.sim_to_ideal_channel);
      ()
  ) else (
    // tau = recv3(lid), role Responder.
    assert (lid.role == Responder);
    assert (ma_sim_receive_message3_protocol_transition s_qp session party peer s_midp);
    let p_rk (rkey: priv_key) : prop =
      ma_sim_receive_message3_enabled s_qp session party peer rkey /\
      s_midp == ma_sim_receive_message3_state s_qp session party peer rkey
    in
    assert (exists rkey. p_rk rkey);
    let recv_key = FStar.IndefiniteDescription.indefinite_description_ghost priv_key p_rk in
    assert (p_rk recv_key);
    match eff with
    | IoSend ->
      // canonical: recv3(Responder); deliver(Responder) -> impl nsl_responder_output.
      assert (ma_ideal_deliver_protocol_transition s_midp session party peer Responder t (s2p_state s_q'));
      // The impl-side responder-output is enabled (responder-output iff RHS holds
      // at s_q: recv3 enabled and deliver enabled after recv3).
      ma_ideal_system_inv_elim corrupt key_directory s_q;
      assert (ma_responder_output_equivalent_transitions_enabled_iff_instance
                s_p s_q session party peer recv_key);
      assert (ma_sim_receive_message3_enabled s_qp session party peer recv_key /\
              ma_ideal_deliver_enabled
                (ma_sim_receive_message3_state s_qp session party peer recv_key)
                session party peer Responder);
      assert (ma_nsl_responder_output_enabled (s2p_state s_p) session party peer recv_key);
      let output_term = ma_authenticated_term session party peer in
      let s_p' = ma_ideal_deliver_responder_impl_witness s_p session party peer recv_key in
      // s_q' is the post-state of recv3; deliver, which equals the impl->ideal
      // responder-output witness.
      assert (s_q'.know == Seq.snoc s_q.know output_term);
      assert (s2p_state s_q' == ma_ideal_deliver_state s_midp session party peer);
      assert (s_q' == ma_impl_responder_output_ideal_witness s_q session party peer recv_key);
      // The impl matches with nsl_responder_output; relation preserved by the
      // impl-side responder-output preservation lemma (post-state s_q' equals the
      // responder-output ideal witness).
      assert (ma_nsl_responder_output_transition (s2p_state s_p) session party peer
                output_term (s2p_state s_p'));
      assert (s_p'.know == Seq.snoc s_p.know output_term);
      ma_obs_bisim_observable_step_impl_responder_output_preserves_relation
        corrupt key_directory s_p s_q session party peer recv_key s_p';
      assert (ma_bisim_relation corrupt key_directory s_p' s_q');
      let lid_lbls : list system_label = [TestedSystem.Observable IoSend lid] in
      assert (eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lid_lbls s_p');
      assert_norm (label_effects ([TestedSystem.Observable IoSend lid] <: list system_label)
                   == [ma_observable_effect IoSend])
    | NetSend ->
      // tau = recv3(lid).  Role exclusion first: lid.role == Responder forces a
      // Responder observable, so the Initiator-role observables
      // send_message1/send_message3 cannot fire; the only role-consistent NetSend
      // alpha is send_message2.  But send_message2 after recv3 is itself
      // infeasible: recv3 created a SimResponderSession for party, whereas
      // send_message2 requires NO sim session for party.  We derive that
      // contradiction below.
      assert (ma_sim_send_message2_protocol_transition s_midp session party peer t (s2p_state s_q'));
      ma_ideal_system_inv_elim corrupt key_directory s_q;
      // recv3 created/updated a SimResponderSession for party at s_mid, but
      // send_message2 requires NO sim session for party at s_mid. Contradiction.
      assert (Some? (ma_sim_responder_session_state s_midp party session));
      ()
  )
#pop-options

/// Helper: the partition membership of two labels of `lbls` forces equal ids.
private
let lbls_in_partition_same_id
      (part_l: system_label)
      (lbls: list system_label)
      (l1 l2: system_label)
    : Lemma
      (requires
        lbls_in_partition lbls ma_partition_role part_l /\
        List.memP l1 lbls /\ List.memP l2 lbls /\
        TestedSystem.Internal? l1 /\
        (TestedSystem.Internal? l2 \/ TestedSystem.Observable? l2))
      (ensures
        ma_label_in_same_partition_role l1 l2) =
  ma_label_in_same_partition_role_equiv ()

#push-options "--fuel 4 --ifuel 4 --z3rlimit 80 --split_queries no"
let ma_obs_sim_ideal_impl_instance
      corrupt key_directory know0 s_q s_p part_l lbls s_q' =
  match lbls with
  // `is_eventually_observable []` is `false`, so the premise is unsatisfiable.
  | [] -> ()
  | [TestedSystem.Input d] ->
    ma_obs_bisim_input_step_ideal corrupt key_directory know0 s_p s_q d s_q';
    assert (exists s_p'.
      (ma_impl_system corrupt key_directory know0).transitions s_p (TestedSystem.Input d) s_p' /\
      ma_bisim_relation corrupt key_directory s_p' s_q');
    introduce exists (lbls': list system_label) (s_p': impl_system_state).
        label_effects lbls' == label_effects lbls /\
        eventually_observable_step (ma_impl_system corrupt key_directory know0) s_p lbls' s_p' /\
        ma_bisim_relation corrupt key_directory s_p' s_q'
    with ([TestedSystem.Input d])
      (FStar.IndefiniteDescription.indefinite_description_ghost impl_system_state
        (fun s_p' ->
          (ma_impl_system corrupt key_directory know0).transitions s_p (TestedSystem.Input d) s_p' /\
          ma_bisim_relation corrupt key_directory s_p' s_q'))
    and ()
  | [TestedSystem.Observable eff lid] ->
    ma_obs_bisim_observable_step_ideal_len1 corrupt key_directory know0 s_p s_q eff lid s_q';
    assert_norm (label_effects ([TestedSystem.Observable eff lid] <: list system_label)
                 == [ma_observable_effect eff])
  | [TestedSystem.Internal lid1; TestedSystem.Observable eff lid2] ->
    // `lbls_in_partition` forces lid1 == lid2 (role-sensitive); the
    // `multi_transitions` premise gives the intermediate state.
    lbls_in_partition_same_id part_l lbls
      (TestedSystem.Internal lid1) (TestedSystem.Observable eff lid2);
    assert (ma_label_id_in_same_partition_role lid1 lid2);
    assert (lid1 == lid2);
    let p_mid (s_mid: ideal_system_state) : prop =
      (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Internal lid1) s_mid /\
      (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Observable eff lid2) s_q'
    in
    assert (exists s_mid. p_mid s_mid);
    let s_mid = FStar.IndefiniteDescription.indefinite_description_ghost ideal_system_state p_mid in
    assert (p_mid s_mid);
    ma_obs_bisim_observable_step_ideal_len2
      corrupt key_directory know0 s_p s_q lid1 eff s_mid s_q';
    assert_norm (label_effects
      ([TestedSystem.Internal lid1; TestedSystem.Observable eff lid2] <: list system_label)
      == [ma_observable_effect eff])
  // Remaining shapes: `[Internal ...]` of length 1 (not eventually-observable),
  // `[Input d; ...]` of length >= 2 (Input is not internal, so not eventually
  // observable past the first), `[Observable ...; ...]` of length >= 2 (first
  // label not internal), or `[Internal; Internal; ...]` (two same-id internals,
  // infeasible). Handle the genuinely problematic last family explicitly; the
  // rest are ruled out by `is_eventually_observable`.
  | TestedSystem.Internal lid1 :: TestedSystem.Internal lid2 :: rest ->
    // Both internal labels lie in `part_l`'s partition, hence carry the same id.
    lbls_in_partition_same_id part_l lbls
      (TestedSystem.Internal lid1) (TestedSystem.Internal lid2);
    assert (lid1 == lid2);
    // Extract the first two transitions from `multi_transitions`.
    let p_mid (s_mid: ideal_system_state) : prop =
      (ma_ideal_system corrupt key_directory know0).transitions s_q (TestedSystem.Internal lid1) s_mid /\
      (exists s_mid2.
        (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Internal lid2) s_mid2)
    in
    assert (exists s_mid. p_mid s_mid);
    let s_mid = FStar.IndefiniteDescription.indefinite_description_ghost ideal_system_state p_mid in
    assert (p_mid s_mid);
    let p_mid2 (s_mid2: ideal_system_state) : prop =
      (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Internal lid2) s_mid2
    in
    assert (exists s_mid2. p_mid2 s_mid2);
    let s_mid2 = FStar.IndefiniteDescription.indefinite_description_ghost ideal_system_state p_mid2 in
    assert (p_mid2 s_mid2);
    ma_ideal_system_inv_elim corrupt key_directory s_q;
    two_same_lid_internals_infeasible corrupt key_directory know0 s_q lid1 s_mid s_mid2
  | _ -> ()
#pop-options
