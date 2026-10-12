module SMD.ObservationalBisimulation.Proof.ImplSendRelation

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
open SMD.ObservationalBisimulation.Proof.SendHelpers

#push-options "--z3rlimit_factor 8"

#push-options "--split_queries always"
private
let smd_obs_bisim_observable_step_impl_send_preserves_bijective_correspondence
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (session: session_id)
    (message: term)
    (s_p': TestedSystem.state term impl_internal_state)
  : Lemma
    (requires
      smd_bisim_relation k s_p s_q /\
      smd_impl_protocol_send_transition (s2p_state s_p)
        session
        (Senc (Pair (SessionId session) message) k)
        (s2p_state s_p') /\
      s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) message) k) /\
      smd_ideal_protocol_send_transition (s2p_state s_q)
        session
        (Senc (SessionId session) k)
        (s2p_state (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message)))
    (ensures
      bijective_correspondence_on_derivations adv
        s_p'.know
        (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message).know
        (smd_subst_bijection k k s_p'.internal.messages)) =
  // Condition 5 of `bijective_correspondence_preserved_by_additional_message_in_map`:
  // no impl derivable term contains `Senc (SessionId session) k` as subterm.
  // Follows directly from the no-ideal-form-senc clause of `smd_bisim_relation`
  // (instantiate i := session).
  assert (forall (d: adv.derivation) (t: term).
            adv.derive d s_p.know == Some t ==>
            in_term t (Senc (SessionId session) k) == false);
  assert (forall d.
            match adv.derive d s_p.know with
            | None -> True
            | Some t -> in_term t (Senc (SessionId session) k) == false);
  bijective_correspondence_preserved_by_additional_message_in_map
    s_p.know
    s_q.know
    s_p.internal.messages
    k
    k
    session
    message;
  bijective_correspondence_preserved_learning_secret_encrypted_response s_p.know s_q.know s_p'.internal.messages k k session message;
  ()
#pop-options

(**
  Helper: the `valid_encrypted_responses` clause is preserved after an impl
  NetSend step.  Extracted from `..._preserves_relation` so it verifies in a
  small SMT context (one query) instead of being one of hundreds of split
  sub-queries inside the giant lemma.
*)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _send_valid_encrypted_responses_preserved
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_p': TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (ideal_message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        implementation_invariants s_p' /\
        s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) message) k) /\
        s_p'.internal.key == k /\
        PartialMap.sel s_p.internal.messages session == None /\
        // Session-case facts (qs = session, the newly-sent message): supplied by
        // the caller since they are established in the surrounding lemma.
        PartialMap.sel s_q'.internal.messages session == Some ideal_message /\
        indistinguishable message ideal_message /\
        (forall (qs: session_id). qs <> session ==>
          PartialMap.sel s_q'.internal.messages qs == PartialMap.sel s_q.internal.messages qs))
      (ensures
        valid_encrypted_responses_indistinguishable_from_stored_ideal_messages s_p' s_q') =
  let n = Seq.length s_p.know in
  let impl_observed = Senc (Pair (SessionId session) message) k in
  let _valid_encrypted_responses_instance
    (qs: session_id) (qim qidm: term)
    (qd: derivation) (qdt: term)
    : Lemma
      (requires
        adv.derive qd s_p'.know = Some qdt /\
        in_term qdt (Senc (Pair (SessionId qs) qim) s_p'.internal.key) /\
        PartialMap.sel s_q'.internal.messages qs = Some qidm)
      (ensures indistinguishable qim qidm)
      [SMTPat (adv.derive qd s_p'.know);
       SMTPat (in_term qdt (Senc (Pair (SessionId qs) qim) s_p'.internal.key));
       SMTPat (PartialMap.sel s_q'.internal.messages qs);
       SMTPat (indistinguishable qim qidm)] =
    impl_valid_response_is_observed s_p' qs qim qd qdt;
    let idx = FStar.IndefiniteDescription.indefinite_description_ghost knowledge_index
      (fun idx -> adv.derive (DeriveObserved idx) s_p'.know =
                  Some (Senc (Pair (SessionId qs) qim) k)) in
    if idx < n then begin
      obs_from_old_knowledge s_p.know impl_observed k qs qim n idx;
      assert_norm (is_receive_trigger_for_session qs k (Senc (Pair (SessionId qs) qim) k));
      assert_norm (in_term (Senc (Pair (SessionId qs) qim) k) (Senc (Pair (SessionId qs) qim) k));
      assert (Set.mem qs s_p.internal.sent_sessions);
      assert (qs <> session);
      assert (indistinguishable qim qidm)
    end else begin
      _derive_observed_inversion idx s_p'.know (Senc (Pair (SessionId qs) qim) k);
      _snoc_index_eq_last s_p.know s_p'.know impl_observed n idx
    end
  in
  assert (valid_encrypted_responses_indistinguishable_from_stored_ideal_messages s_p' s_q')
#pop-options

(**
  Helper: the `to_be_delivered` clause is preserved after an impl NetSend step.
  Extracted from `..._preserves_relation` for the same performance reason as
  `_send_valid_encrypted_responses_preserved` above.
*)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _send_to_be_delivered_preserved
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_p': TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (ideal_message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        implementation_invariants s_p' /\
        s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) message) k) /\
        s_q'.know == Seq.snoc s_q.know (Senc (SessionId session) k) /\
        s_p'.internal.key == k /\
        s_q'.internal.sim_key == k /\
        PartialMap.sel s_p.internal.messages session == None /\
        // Session-case facts (qs = session, the newly-sent message): supplied by
        // the caller since they are established in the surrounding lemma.
        PartialMap.sel s_q'.internal.messages session == Some ideal_message /\
        (exists trigger_d.
          adv.derive trigger_d s_p'.know = Some (Pair (SessionId session) message) /\
          adv.derive trigger_d s_q'.know = Some (Pair (SessionId session) ideal_message)) /\
        (forall (qs: session_id). qs <> session ==>
          PartialMap.sel s_q'.internal.messages qs == PartialMap.sel s_q.internal.messages qs))
      (ensures
        to_be_delivered_messages_already_derivable_by_same_derivation s_p' s_q') =
  let n = Seq.length s_p.know in
  let impl_observed = Senc (Pair (SessionId session) message) k in
  let ideal_observed = Senc (SessionId session) k in
  let _to_be_delivered_preserved_instance
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
    assert (exists (idx: knowledge_index).
      adv.derive (DeriveObserved idx) s_p'.know =
      Some (Senc (Pair (SessionId qs) qim) k));
    let idx = FStar.IndefiniteDescription.indefinite_description_ghost knowledge_index
      (fun idx -> adv.derive (DeriveObserved idx) s_p'.know =
                  Some (Senc (Pair (SessionId qs) qim) k)) in
    if idx < n then begin
      obs_from_old_knowledge s_p.know impl_observed k qs qim n idx;
      assert_norm (is_receive_trigger_for_session qs k (Senc (Pair (SessionId qs) qim) k));
      assert_norm (in_term (Senc (Pair (SessionId qs) qim) k) (Senc (Pair (SessionId qs) qim) k));
      assert (Set.mem qs s_p.internal.sent_sessions);
      assert (qs <> session);
      assert_norm (in_term (Senc (Pair (SessionId qs) qim) k) (Senc (Pair (SessionId qs) qim) k));
      assert_norm (in_term (Senc (SessionId qs) k) (Senc (SessionId qs) k));
      smd_subst_bijection_right k k s_p.internal.messages
        (Senc (Pair (SessionId qs) qim) k);
      assert (PartialMap.sel s_p.internal.messages qs == Some qim);
      assert (smd_bi_subst (Senc (Pair (SessionId qs) qim) k) s_p.internal.messages k k
              == Senc (SessionId qs) k);
      assert (adv.derive (DeriveObserved idx) s_q.know
              == Some (Senc (SessionId qs) k));
      assert (PartialMap.sel s_q.internal.messages qs == Some qidm);
      assert (exists trigger_d.
        adv.derive trigger_d s_p.know = Some (Pair (SessionId qs) qim) /\
        adv.derive trigger_d s_q.know = Some (Pair (SessionId qs) qidm));
      let td = FStar.IndefiniteDescription.indefinite_description_ghost derivation
        (fun td -> adv.derive td s_p.know = Some (Pair (SessionId qs) qim) /\
                   adv.derive td s_q.know = Some (Pair (SessionId qs) qidm)) in
      append_preserves_derive td s_p.know (Seq.create 1 impl_observed);
      append_preserves_derive td s_q.know (Seq.create 1 ideal_observed)
    end else begin
      _derive_observed_inversion idx s_p'.know (Senc (Pair (SessionId qs) qim) k);
      _snoc_index_eq_last s_p.know s_p'.know impl_observed n idx
    end
  in
  assert (to_be_delivered_messages_already_derivable_by_same_derivation s_p' s_q')
#pop-options

(** Helper: canonical_ideal preserved (ideal derivable terms stay canonical). *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _send_canonical_ideal_preserved
      (k: key)
      (s_q s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
    : Lemma
      (requires
        ~(derivable s_q.know (Key k)) /\
        (forall (d: adv.derivation) (t: term).
          adv.derive d s_q.know = Some t ==> canonical_ideal t k) /\
        s_q'.know == Seq.snoc s_q.know (Senc (SessionId session) k))
      (ensures
        (forall (d: adv.derivation) (t: term).
          adv.derive d s_q'.know = Some t ==> canonical_ideal t k)) =
  assert_norm (canonical_ideal (Senc (SessionId session) k) k);
  let _canonical_ideal_post (d: adv.derivation) (t: term)
    : Lemma (adv.derive d s_q'.know = Some t ==> canonical_ideal t k) =
    if Some? (adv.derive d s_q'.know) && Some?.v (adv.derive d s_q'.know) = t
    then begin
      derivable_from_encrypted_term_without_key
        s_q.know (SessionId session) k d t;
      canonical_ideal_built_from s_q.know k (SessionId session) t
    end
  in
  FStar.Classical.forall_intro_2 _canonical_ideal_post
#pop-options

(** Helper: no-ideal-form-senc preserved (impl derivable terms have no
    `Senc(SessionId _) k` subterm). *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _send_no_ideal_senc_preserved
      (k: key)
      (s_p s_p': TestedSystem.state term impl_internal_state)
      (session: session_id)
      (message: term)
    : Lemma
      (requires
        ~(derivable s_p.know (Key k)) /\
        derivable s_p.know (Pair (SessionId session) message) /\
        (forall (d: adv.derivation) (t: term) (i: session_id).
          adv.derive d s_p.know = Some t ==> in_term t (Senc (SessionId i) k) == false) /\
        s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) message) k))
      (ensures
        (forall (d: adv.derivation) (t: term) (i: session_id).
          adv.derive d s_p'.know = Some t ==> in_term t (Senc (SessionId i) k) == false)) =
  let impl_observed = Senc (Pair (SessionId session) message) k in
  let impl_trigger = Pair (SessionId session) message in
  let d_impl_trig = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_p.know = Some impl_trigger) in
  let _no_ideal_senc_post (d: adv.derivation) (t: term) (i: session_id)
    : Lemma (adv.derive d s_p'.know = Some t ==> in_term t (Senc (SessionId i) k) == false) =
    if Some? (adv.derive d s_p'.know) && Some?.v (adv.derive d s_p'.know) = t
    then begin
      assert (adv.derive d_impl_trig s_p.know = Some impl_trigger);
      assert (in_term impl_trigger (Senc (SessionId i) k) == false);
      assert_norm (in_term impl_trigger (Senc (SessionId i) k) ==
                   (impl_trigger = Senc (SessionId i) k ||
                    in_term (SessionId session) (Senc (SessionId i) k) ||
                    in_term message (Senc (SessionId i) k)));
      assert (in_term message (Senc (SessionId i) k) == false);
      assert_norm (in_term impl_observed (Senc (SessionId i) k) ==
                   (impl_observed = Senc (SessionId i) k ||
                    in_term (Pair (SessionId session) message) (Senc (SessionId i) k)));
      assert_norm (in_term (Pair (SessionId session) message) (Senc (SessionId i) k) ==
                   (in_term (SessionId session) (Senc (SessionId i) k) ||
                    in_term message (Senc (SessionId i) k)));
      derivable_from_encrypted_term_without_key
        s_p.know (Pair (SessionId session) message) k d t;
      no_ideal_senc_built_from s_p.know k (Pair (SessionId session) message) i t
    end
  in
  FStar.Classical.forall_intro_3 _no_ideal_senc_post
#pop-options

(** Helper: messages-map correspondence preserved. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _send_messages_corr_preserved
      (k: key)
      (s_p s_p': TestedSystem.state term impl_internal_state)
      (s_q s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message ideal_message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        PartialMap.sel s_p.internal.messages session == None /\
        smd_bi_subst message s_p'.internal.messages k k == ideal_message /\
        s_p'.internal.messages == PartialMap.upd s_p.internal.messages session message /\
        s_q'.internal.messages == PartialMap.upd s_q.internal.messages session ideal_message)
      (ensures
        (forall (s: session_id).
          PartialMap.sel s_q'.internal.messages s ==
          Option.mapTot (fun m -> smd_bi_subst m s_p'.internal.messages k k)
            (PartialMap.sel s_p'.internal.messages s))) =
  let _messages_corr (s: session_id)
    : Lemma
      (PartialMap.sel s_q'.internal.messages s ==
       Option.mapTot (fun m -> smd_bi_subst m s_p'.internal.messages k k)
         (PartialMap.sel s_p'.internal.messages s)) =
    if s = session then ()
    else begin
      assert (PartialMap.sel s_p'.internal.messages s == PartialMap.sel s_p.internal.messages s);
      assert (PartialMap.sel s_q'.internal.messages s == PartialMap.sel s_q.internal.messages s);
      assert (PartialMap.sel s_q.internal.messages s ==
              Option.mapTot (fun m -> smd_bi_subst m s_p.internal.messages k k)
                (PartialMap.sel s_p.internal.messages s));
      match PartialMap.sel s_p.internal.messages s with
      | None -> ()
      | Some w ->
        _messages_p_stored_value_derivable k s_p s_q s w;
        _impl_irrelevant_update_on_derivable k session message s_p s_q w;
        assert (smd_bi_subst w s_p.internal.messages k k ==
                smd_bi_subst w s_p'.internal.messages k k)
    end
  in
  FStar.Classical.forall_intro _messages_corr
#pop-options

(** Helper: inputs-bag count correspondence preserved under the new bijection. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _send_bag_count_preserved
      (k: key)
      (s_p s_p': TestedSystem.state term impl_internal_state)
      (s_q s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message ideal_message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        PartialMap.sel s_p.internal.messages session == None /\
        s_p'.internal.messages == PartialMap.upd s_p.internal.messages session message /\
        s_p'.inputs == Bag.remove (Pair (SessionId session) message) s_p.inputs /\
        s_q'.inputs == Bag.remove (Pair (SessionId session) ideal_message) s_q.inputs /\
        (smd_subst_bijection k k s_p'.internal.messages).cright (Pair (SessionId session) message)
          == Pair (SessionId session) ideal_message)
      (ensures
        (forall t.
          Bag.count s_p'.inputs t ==
          Bag.count s_q'.inputs ((smd_subst_bijection k k s_p'.internal.messages).cright t))) =
  let bij = smd_subst_bijection k k s_p'.internal.messages in
  let bij_old = smd_subst_bijection k k s_p.internal.messages in
  let impl_trigger = Pair (SessionId session) message in
  let _bag_count_pre (t: term)
    : Lemma (Bag.count s_p.inputs t == Bag.count s_q.inputs (bij.cright t)) =
    smd_subst_bijection_right k k s_p.internal.messages t;
    smd_subst_bijection_right k k s_p'.internal.messages t;
    if Bag.mem t s_p.inputs then begin
      _impl_irrelevant_update_on_derivable k session message s_p s_q t;
      assert (bij_old.cright t == bij.cright t)
    end else begin
      let t' = bij_old.cleft (bij.cright t) in
      let _contra () : Lemma
        (requires Bag.count s_q.inputs (bij.cright t) > 0)
        (ensures False) =
        bij_old.bij.right_left (bij.cright t);
        smd_subst_bijection_right k k s_p.internal.messages t';
        assert (Bag.count s_p.inputs t' > 0);
        assert (Bag.mem t' s_p.inputs);
        _impl_irrelevant_update_on_derivable k session message s_p s_q t';
        smd_subst_bijection_right k k s_p'.internal.messages t';
        assert (bij.cright t' == bij.cright t);
        BijectionExt.bijection_injective bij t' t;
        assert (t' == t)
      in
      Classical.move_requires _contra ()
    end
  in
  FStar.Classical.forall_intro _bag_count_pre;
  smd_subst_bijection_right k k s_p'.internal.messages impl_trigger;
  let _bag_count_post (t: term)
    : Lemma (Bag.count s_p'.inputs t == Bag.count s_q'.inputs (bij.cright t)) =
    count_remove_bijective t impl_trigger s_p.inputs s_q.inputs bij
  in
  FStar.Classical.forall_intro _bag_count_post
#pop-options

(** Helper: send-enabled correspondence preserved (uses the bag-count
    correspondence as a hypothesis). *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 4 --split_queries always"
private
let _send_send_iff_preserved
      (k: key)
      (s_p s_p': TestedSystem.state term impl_internal_state)
      (s_q s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message ideal_message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        PartialMap.sel s_p.internal.messages session == None /\
        s_p'.internal.key == k /\
        s_q'.internal.sim_key == k /\
        s_p'.internal.messages == PartialMap.upd s_p.internal.messages session message /\
        s_q'.internal.messages == PartialMap.upd s_q.internal.messages session ideal_message /\
        s_p'.internal.sent_sessions == Set.add session s_p.internal.sent_sessions /\
        s_q'.internal.sim_sent_sessions == Set.add session s_q.internal.sim_sent_sessions /\
        s_p'.inputs == Bag.remove (Pair (SessionId session) message) s_p.inputs /\
        s_q'.inputs == Bag.remove (Pair (SessionId session) ideal_message) s_q.inputs /\
        (forall t.
          Bag.count s_p'.inputs t ==
          Bag.count s_q'.inputs ((smd_subst_bijection k k s_p'.internal.messages).cright t)))
      (ensures
        send_equivalent_transitions_enabled_iff (s2p_state s_p') (s2p_state s_q')) =
  let bij = smd_subst_bijection k k s_p'.internal.messages in
  let impl_trigger = Pair (SessionId session) message in
  let ideal_trigger = Pair (SessionId session) ideal_message in
  // For sid <> session both impl- and ideal-side send-enabledness are unchanged
  // by the transition (the removed trigger is for `session`).
  let _send_enabled_preserved (sid: session_id) (m: term)
    : Lemma
      (ensures sid <> session ==>
        (smd_impl_protocol_send_enabled (s2p_state s_p') sid m k <==>
         smd_impl_protocol_send_enabled (s2p_state s_p) sid m k) /\
        (smd_ideal_protocol_send_enabled (s2p_state s_q') sid
           (smd_bi_subst m s_p'.internal.messages k k) <==>
         smd_ideal_protocol_send_enabled (s2p_state s_q) sid
           (smd_bi_subst m s_p'.internal.messages k k))) =
    if sid <> session then begin
      Bag.mem_remove (Pair (SessionId sid) m) impl_trigger s_p.inputs;
      Bag.mem_remove (Pair (SessionId sid) (smd_bi_subst m s_p'.internal.messages k k))
                     ideal_trigger s_q.inputs
    end
  in
  FStar.Classical.forall_intro_2 _send_enabled_preserved;
  let _send_iff_pointwise (sid: session_id) (m: term)
    : Lemma
      (ensures
        smd_impl_protocol_send_enabled (s2p_state s_p') sid m k <==>
        smd_ideal_protocol_send_enabled (s2p_state s_q') sid
          (smd_bi_subst m s_p'.internal.messages k k)) =
    if sid = session then begin
      assert (Set.mem session s_p'.internal.sent_sessions);
      assert (Set.mem session s_q'.internal.sim_sent_sessions)
    end else begin
      let p = Pair (SessionId sid) m in
      Bag.mem_remove p impl_trigger s_p.inputs;
      let bm_new = smd_bi_subst m s_p'.internal.messages k k in
      let q = Pair (SessionId sid) bm_new in
      Bag.mem_remove q ideal_trigger s_q.inputs;
      smd_subst_bijection_right k k s_p'.internal.messages p;
      assert_norm (smd_bi_subst p s_p'.internal.messages k k =
                   Pair (SessionId sid) (smd_bi_subst m s_p'.internal.messages k k));
      assert (bij.cright p == q);
      if Bag.mem p s_p.inputs then begin
        _impl_irrelevant_update_on_derivable k session message s_p s_q p;
        assert_norm (smd_bi_subst p s_p.internal.messages k k =
                     Pair (SessionId sid) (smd_bi_subst m s_p.internal.messages k k));
        assert (smd_bi_subst m s_p.internal.messages k k ==
                smd_bi_subst m s_p'.internal.messages k k)
      end
    end
  in
  FStar.Classical.forall_intro_2 _send_iff_pointwise
#pop-options

(** Helper: receive-enabled correspondence preserved. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries always"
private
let _send_recv_iff_preserved
      (k: key)
      (s_p s_p': TestedSystem.state term impl_internal_state)
      (s_q s_q': TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message ideal_message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        PartialMap.sel s_p.internal.messages session == None /\
        PartialMap.sel s_q.internal.messages session == None /\
        s_p'.internal.key == k /\
        s_q'.internal.sim_key == k /\
        s_p'.internal.received_sessions == s_p.internal.received_sessions /\
        s_q'.internal.sim_received_sessions == s_q.internal.sim_received_sessions /\
        s_p'.internal.messages == PartialMap.upd s_p.internal.messages session message /\
        s_q'.internal.messages == PartialMap.upd s_q.internal.messages session ideal_message /\
        s_p'.inputs == Bag.remove (Pair (SessionId session) message) s_p.inputs /\
        s_q'.inputs == Bag.remove (Pair (SessionId session) ideal_message) s_q.inputs)
      (ensures
        receive_equivalent_transitions_enabled_iff (s2p_state s_p') (s2p_state s_q')) =
  let impl_trigger = Pair (SessionId session) message in
  let ideal_trigger = Pair (SessionId session) ideal_message in
  mem_remove_neq_forall impl_trigger s_p.inputs;
  mem_remove_neq_forall ideal_trigger s_q.inputs;
  // For sid = session: the ideal receive trigger Senc(SessionId session) k is not
  // in the ideal inputs (no valid response before send), and removal of the
  // Pair-shaped send trigger preserves that.
  assert_norm (in_term (Senc (SessionId session) k) (Senc (SessionId session) k));
  assert (not (Bag.mem (Senc (SessionId session) k) s_q.inputs));
  assert (not (Bag.mem (Senc (SessionId session) k) s_q'.inputs));
  let _recv_post_bicond (sid: session_id) (m: term)
    : Lemma (ensures
        smd_impl_protocol_receive_enabled (s2p_state s_p') sid m <==>
        smd_ideal_protocol_receive_enabled (s2p_state s_q') sid
          (smd_bi_subst m s_p'.internal.messages k k)) =
    assert (smd_impl_protocol_receive_enabled (s2p_state s_p') sid m ==
            smd_impl_protocol_receive_enabled (s2p_state s_p) sid m);
    if sid = session then begin
      assert (PartialMap.sel s_q.internal.messages session == None);
      assert (~(smd_ideal_protocol_receive_enabled (s2p_state s_q) sid
                  (smd_bi_subst m s_p'.internal.messages k k)));
      assert (~(smd_impl_protocol_receive_enabled (s2p_state s_p) sid m))
    end else begin
      assert (PartialMap.sel s_q'.internal.messages sid ==
              PartialMap.sel s_q.internal.messages sid);
      assert (s_q'.internal.sim_received_sessions ==
              s_q.internal.sim_received_sessions);
      Bag.mem_remove (Senc (SessionId sid) k) ideal_trigger s_q.inputs;
      assert (Bag.mem (Senc (SessionId sid) k) s_q'.inputs ==
              Bag.mem (Senc (SessionId sid) k) s_q.inputs);
      match PartialMap.sel s_q.internal.messages sid with
      | None -> ()
      | Some v ->
        let w = Some?.v (PartialMap.sel s_p.internal.messages sid) in
        assert (PartialMap.sel s_p.internal.messages sid == Some w);
        assert (PartialMap.sel s_q.internal.messages sid ==
                Option.mapTot
                  (fun mm -> smd_bi_subst mm s_p.internal.messages k k)
                  (PartialMap.sel s_p.internal.messages sid));
        assert (v == smd_bi_subst w s_p.internal.messages k k);
        _messages_p_stored_value_derivable k s_p s_q sid w;
        _impl_irrelevant_update_on_derivable k session message s_p s_q w;
        assert (smd_bi_subst w s_p.internal.messages k k ==
                smd_bi_subst w s_p'.internal.messages k k);
        assert (v == smd_bi_subst w s_p'.internal.messages k k);
        let bij_old = smd_subst_bijection k k s_p.internal.messages in
        let bij_new = smd_subst_bijection k k s_p'.internal.messages in
        smd_subst_bijection_right k k s_p.internal.messages w;
        smd_subst_bijection_right k k s_p'.internal.messages w;
        smd_subst_bijection_right k k s_p.internal.messages m;
        smd_subst_bijection_right k k s_p'.internal.messages m;
        let _inj_old () : Lemma
          (requires v == smd_bi_subst m s_p.internal.messages k k)
          (ensures m == w) =
          BijectionExt.bijection_injective bij_old m w
        in
        let _inj_new () : Lemma
          (requires v == smd_bi_subst m s_p'.internal.messages k k)
          (ensures m == w) =
          BijectionExt.bijection_injective bij_new m w
        in
        Classical.move_requires _inj_old ();
        Classical.move_requires _inj_new ()
    end
  in
  FStar.Classical.forall_intro_2 _recv_post_bicond
#pop-options

(**
  When the implementation takes a NetSend step delivering `Senc(Pair(SessionId
  session, message), k)`, AND the ideal witness state
  `smd_impl_send_ideal_witness k s_p.internal.messages s_q session message` is reachable from `s_q`,
  the bijective correspondence is preserved between `s_p'` and that witness
  state.
*)
// Thin driver: each conjunct of `smd_bisim_relation` is discharged by a small,
// independently-verified helper above, keeping this lemma's whole-VC tractable.
// `--split_queries always` is retained (as in the monolithic version, which
// required it to avoid a failed whole-VC).
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries always"
let smd_obs_bisim_observable_step_impl_send_preserves_relation
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
        let s_q' = smd_impl_send_ideal_witness k s_p.internal.messages s_q session message in
        smd_bisim_relation k s_p s_q /\
        smd_impl_protocol_send_transition (s2p_state s_p)
          session
          (Senc (Pair (SessionId session) message) k)
          (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) message) k) /\
        (smd_ideal_protocol_send_transition (s2p_state s_q)
          session
          (Senc (SessionId session) k)
          (s2p_state s_q'))
      ))
      (ensures
        smd_bisim_relation k s_p' (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message)) =
  // === Bijective correspondence, static equivalence, invariants ===
  smd_obs_bisim_observable_step_impl_send_preserves_bijective_correspondence
    k know0 s_p s_q session message s_p';
  smd_subst_bijection_maps_to_indistinguishable_terms k k s_p'.internal.messages;
  bijective_correspondence_implies_static_equivalence adv s_p'.know
    (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message).know
    (smd_subst_bijection k k s_p'.internal.messages);
  implementation_invariants_preserved_after_send' session message s_p s_p';
  ideal_invariants_preserved_after_send' session s_q
    (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message);

  let s_q' = smd_impl_send_ideal_witness k s_p.internal.messages s_q session message in
  let bij = smd_subst_bijection k k s_p'.internal.messages in
  let ideal_message = smd_bi_subst message s_p.internal.messages k k in
  let impl_observed = Senc (Pair (SessionId session) message) k in
  let ideal_observed = Senc (SessionId session) k in
  let impl_trigger = Pair (SessionId session) message in
  let ideal_trigger = Pair (SessionId session) ideal_message in

  // === Field relationships from the transition (s_p') and witness (s_q') ===
  assert (PartialMap.sel s_p.internal.messages session == None);
  assert (s_p'.internal.key == k);
  assert (s_q'.internal.sim_key == k);
  assert (s_p'.internal.messages == PartialMap.upd s_p.internal.messages session message);
  assert (s_q'.internal.messages == PartialMap.upd s_q.internal.messages session ideal_message);
  assert (s_p'.internal.sent_sessions == Set.add session s_p.internal.sent_sessions);
  assert (s_q'.internal.sim_sent_sessions == Set.add session s_q.internal.sim_sent_sessions);
  assert (s_p'.internal.received_sessions == s_p.internal.received_sessions);
  assert (s_q'.internal.sim_received_sessions == s_q.internal.sim_received_sessions);
  assert (s_p'.inputs == Bag.remove impl_trigger s_p.inputs);
  assert (s_q'.inputs == Bag.remove ideal_trigger s_q.inputs);
  assert (s_q'.know == Seq.snoc s_q.know ideal_observed);
  assert (PartialMap.sel s_q.internal.messages session == None);

  // === Trigger derivation + image under the new bijection ===
  let d_trig = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_p.know = Some impl_trigger) in
  assert (Bag.mem impl_trigger s_p.inputs);
  assert (derivable s_p.know impl_trigger);
  assert_norm (smd_bi_subst impl_trigger s_p.internal.messages k k = ideal_trigger);
  smd_subst_bijection_right k k s_p.internal.messages impl_trigger;
  append_preserves_derive d_trig s_p.know (Seq.create 1 impl_observed);
  append_preserves_derive d_trig s_q.know (Seq.create 1 ideal_observed);
  assert (in_term impl_trigger (Senc (SessionId session) k) == false);
  assert (in_term message (Senc (SessionId session) k) == false);
  assert (~(in_term impl_trigger (Senc (Pair (SessionId session) message) k)));
  assert (in_term message (Senc (Pair (SessionId session) message) k) == false);
  smd_bi_subst_preserved_by_irrelevant_update message s_p.internal.messages k k session message;
  assert (smd_bi_subst message s_p'.internal.messages k k == ideal_message);
  assert_norm (smd_bi_subst impl_trigger s_p'.internal.messages k k =
               Pair (SessionId session) (smd_bi_subst message s_p'.internal.messages k k));
  smd_subst_bijection_right k k s_p'.internal.messages impl_trigger;
  assert (bij.cright impl_trigger == ideal_trigger);

  // === Session-case facts for the response/trigger helpers ===
  assert (indistinguishable message ideal_message);
  assert (PartialMap.sel s_q'.internal.messages session == Some ideal_message);
  assert (adv.derive d_trig s_p'.know = Some impl_trigger);
  assert (adv.derive d_trig s_q'.know = Some ideal_trigger);
  assert (exists trigger_d.
    adv.derive trigger_d s_p'.know = Some (Pair (SessionId session) message) /\
    adv.derive trigger_d s_q'.know = Some (Pair (SessionId session) ideal_message));

  // === Key non-derivability (for canonical / no-ideal-senc helpers) ===
  assert (~(derivable s_q.know (Key k)));
  assert (~(derivable s_p.know (Key k)));

  // === Discharge each conjunct via its helper ===
  _send_bag_count_preserved k s_p s_p' s_q s_q' session message ideal_message;
  _send_send_iff_preserved k s_p s_p' s_q s_q' session message ideal_message;
  _send_recv_iff_preserved k s_p s_p' s_q s_q' session message ideal_message;
  _send_messages_corr_preserved k s_p s_p' s_q s_q' session message ideal_message;
  _send_canonical_ideal_preserved k s_q s_q' session;
  _send_no_ideal_senc_preserved k s_p s_p' session message;
  _send_valid_encrypted_responses_preserved k s_p s_p' s_q s_q' session message ideal_message;
  _send_to_be_delivered_preserved k s_p s_p' s_q s_q' session message ideal_message;

  // === Completed-iff conjuncts (set membership; session added on both sides) ===
  assert (send_equivalent_transitions_completed_iff (s2p_state s_p') (s2p_state s_q'));
  assert (receive_equivalent_transitions_completed_iff (s2p_state s_p') (s2p_state s_q'));
  ()
#pop-options

#pop-options
