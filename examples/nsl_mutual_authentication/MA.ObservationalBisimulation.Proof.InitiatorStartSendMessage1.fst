module MA.ObservationalBisimulation.Proof.InitiatorStartSendMessage1

/// InitiatorStart + IdealSendMessage1 preservation cluster: per-family helpers (secrecy, state-preservation, structural clauses, enabledness iffs, ma_initiator_ack_iff_from_structural_clauses_pre), the impl_initiator_start _preserves_relation main lemma, and the ideal_send_message1 _preserves_relation lemma.
///
/// Extracted from MA.ObservationalBisimulation.Proof to reduce verification
/// time of the top-level proof module.

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

open MA.ObservationalBisimulation.Proof.Common

open MA.ObservationalBisimulation.Proof.MessageDerivability

open MA.ObservationalBisimulation.Proof.ResponderOutput

open MA.ObservationalBisimulation.Proof.InputStep

open MA.ObservationalBisimulation.Proof.SendMessage3InitiatorAck

#set-options "--fuel 2 --ifuel 2 --z3rlimit 100"

(**
  Secrecy preservation for implementation initiator-start and its ideal
  witness, in the static-corruption setting.  Observing Message1 — a session
  ciphertext `Aenc (Pair (SessionId i) (Pair (Nonce ni) (ParticipantId a))) rk`
  whose plaintext carries no private keys and whose only nonce is the *fresh*
  `initiator_nonce` — exposes no new secret of an honest session, even when the
  responder (= the Message1 encryption-key owner) is corrupt.  The derivation
  argument is therefore the key-secrecy-free
  `MA.Adversary.derivable_from_observed_term_without_private_key_subterms`
  (rather than `derivable_from_session_encrypted_term_without_key`, which would
  require the responder key to be secret): a private key or nonce derivable from
  `snoc s.know Message1` is `built_with_subterms` from the (key-free) observable
  subterms, hence either already derivable from `s.know` or one of those subterms
  (which for a nonce can only be `initiator_nonce`).

  Each clause is guarded to match the now-conditional invariants:
  `ma_private_keys_not_derivable` only constrains *non-corrupt* directory keys,
  and `ma_valid_{initiator,responder}_nonces_not_derivable` only constrain
  sessions whose initiator and responder are both non-corrupt.  The single sub-case
  that needs the responder honest — the freshly created initiator session, whose
  nonce *is* `initiator_nonce` — gets it from the guard (its responder is the
  Message1 responder), so there `no_old_responder_key_ideal` pins the Message1 key
  as non-derivable and `old_ideal_derivable_nonce_used` rules out a fresh nonce
  being already derivable.
*)
#push-options "--z3rlimit 150 --fuel 6 --ifuel 2"
let ma_impl_initiator_start_preserves_secrecy_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
          ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey in
        ma_bisim_relation corrupt key_directory s_p s_q /\
        ma_nsl_initiator_start_enabled (s2p_state s_p)
          session initiator responder initiator_nonce responder_pubkey /\
        ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
        s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        (let s_q' = ma_impl_initiator_start_ideal_witness
          s_q session initiator responder initiator_nonce responder_pubkey in
        ma_private_keys_not_derivable corrupt key_directory s_p' /\
        ma_private_keys_not_derivable corrupt key_directory s_q' /\
        ma_valid_initiator_nonces_not_derivable corrupt s_q' /\
        ma_valid_responder_nonces_not_derivable corrupt s_q')) =
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  let sent_term = ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey in
  let s_q' = ma_impl_initiator_start_ideal_witness
    s_q session initiator responder initiator_nonce responder_pubkey in
  let responder_key = PubKey?.priv responder_pubkey in
  assert (PartialMap.sel key_directory responder == Some responder_key /\
     ma_private_keys_not_derivable corrupt key_directory s_p /\
     ma_private_keys_not_derivable corrupt key_directory s_q /\
    ma_valid_initiator_nonces_not_derivable corrupt s_q /\
    ma_ideal_used_nonces_invariant s_q /\
     ma_valid_responder_nonces_not_derivable corrupt s_q) ;
  // The responder's private key is non-derivable only when the responder is HONEST
  // (a corrupt responder's key may be in the adversary's initial knowledge).  Guarded
  // accordingly; used only on branches where the non-corruption hypothesis is in scope.
  let no_old_responder_key_ideal (_pf: squash (not (Set.mem responder corrupt)))
      : Lemma (ensures ~(derivable s_q.know (PrivKey responder_key))) =
    if FStar.IndefiniteDescription.strong_excluded_middle
      (derivable s_q.know (PrivKey responder_key))
    then
      (let p: derivation -> prop =
        (fun d0 -> derive d0 s_q.know = Some (PrivKey responder_key)) in
       let d0 = FStar.IndefiniteDescription.indefinite_description_ghost derivation p in
       assert (False))
  in
  let old_ideal_derivable_nonce_used (n: nonce)
      : Lemma (ensures derivable s_q.know (Nonce n) ==> Set.mem n s_q.internal.used_nonces) =
    if FStar.IndefiniteDescription.strong_excluded_middle
      (derivable s_q.know (Nonce n))
    then
      (let p: derivation -> prop =
        (fun d0 -> derive d0 s_q.know = Some (Nonce n)) in
       let d0 = FStar.IndefiniteDescription.indefinite_description_ghost derivation p in
       assert (derive d0 s_q.know = Some (Nonce n)) ;
       ma_derive_nonce_in_knowledge_nonces s_q.know d0 n;
       assert (Set.mem n s_q.internal.used_nonces))
  in
  // Observing Message1 (a session ciphertext whose plaintext carries no private
  // keys) exposes no NEW private keys, regardless of whether the responder is
  // corrupt: `derivable_from_observed_term_without_private_key_subterms` does not
  // require the encryption key to be secret.  Only non-corrupt directory keys are
  // constrained (the clause is now guarded by `not (Set.mem participant corrupt)`).
  let impl_private_helper (participant: participant_id) (k: priv_key) (d: derivation)
      : Lemma
        (ensures
          PartialMap.sel key_directory participant == Some k /\ not (Set.mem participant corrupt) ==>
          not (derive d s_p'.know = Some (PrivKey k))) =
    if PartialMap.sel key_directory participant = Some k && not (Set.mem participant corrupt) then
      if derive d s_p'.know = Some (PrivKey k) then
        (assert (s_p'.know == Seq.snoc s_p.know sent_term);
         derivable_from_observed_term_without_private_key_subterms
           s_p.know sent_term d (PrivKey k);
         derivable_subterms_underapproximate_keys_exact_with_no_privkeys s_p.know sent_term;
         private_key_built_from_subterms_already_derivable s_p.know
           (derivable_subterms_underapproximate_keys s_p.know sent_term) k;
         assert (derivable s_p.know (PrivKey k));
         assert (False))
  in
  let ideal_private_helper (participant: participant_id) (k: priv_key) (d: derivation)
      : Lemma
        (ensures
          PartialMap.sel key_directory participant == Some k /\ not (Set.mem participant corrupt) ==>
          not (derive d s_q'.know = Some (PrivKey k))) =
    if PartialMap.sel key_directory participant = Some k && not (Set.mem participant corrupt) then
      if derive d s_q'.know = Some (PrivKey k) then
        (assert (s_q'.know == Seq.snoc s_q.know sent_term);
         derivable_from_observed_term_without_private_key_subterms
           s_q.know sent_term d (PrivKey k);
         derivable_subterms_underapproximate_keys_exact_with_no_privkeys s_q.know sent_term;
         private_key_built_from_subterms_already_derivable s_q.know
           (derivable_subterms_underapproximate_keys s_q.know sent_term) k;
         assert (derivable s_q.know (PrivKey k));
         assert (False))
  in
  let valid_nonce_helper (query_session: session_id)
      (query_responder query_initiator: participant_id)
      (query_nonce: nonce)
      (d: derivation)
      : Lemma
        (ensures
          (match ma_sim_responder_session_state (s2p_state s_q') query_responder query_session with
          | Some responder_state ->
            responder_state.responder == query_responder /\
            responder_state.initiator == query_initiator /\
            responder_state.responder_nonce == query_nonce /\
            not (Set.mem query_responder corrupt) /\ not (Set.mem query_initiator corrupt) ==>
            not (derive d s_q'.know = Some (Nonce query_nonce))
          | None -> True)) =
    ma_impl_initiator_start_ideal_witness_get_updated_sim_responder_session_state
      s_q session initiator responder initiator_nonce responder_pubkey query_responder query_session;
    match ma_sim_responder_session_state (s2p_state s_q') query_responder query_session with
    | None -> ()
    | Some responder_state ->
      if responder_state.responder = query_responder &&
         responder_state.initiator = query_initiator &&
         responder_state.responder_nonce = query_nonce &&
         not (Set.mem query_responder corrupt) && not (Set.mem query_initiator corrupt) then
            if derive d s_q'.know = Some (Nonce query_nonce) then
              // No key-secrecy needed: a responder session nonce is *used*, whereas the
              // Message1 plaintext only carries the *fresh* `initiator_nonce`; so
              // `query_nonce <> initiator_nonce` and `query_nonce` is not among Message1's
              // observable subterms, hence its post-observation derivability reduces to an
              // old derivation that the (honest) responder-nonce secrecy invariant forbids.
              (assert (s_q'.know == Seq.snoc s_q.know sent_term) ;
               // responder sessions are unchanged by initiator-start
               assert (matches_responder_state s_q query_session query_responder query_initiator query_nonce) ;
               assert (Set.mem query_nonce s_q.internal.used_nonces) ;
               assert (~(Set.mem initiator_nonce s_q.internal.used_nonces)) ;
               assert (query_nonce <> initiator_nonce) ;
               derivable_from_observed_term_without_private_key_subterms
                 s_q.know sent_term d (Nonce query_nonce) ;
               derivable_subterms_underapproximate_keys_exact_with_no_privkeys s_q.know sent_term ;
               assert (~(Set.mem (Nonce query_nonce)
                 (derivable_subterms_underapproximate_keys s_q.know sent_term))) ;
               built_from_subterms_nonce_derivable s_q.know
                 (derivable_subterms_underapproximate_keys s_q.know sent_term) query_nonce ;
               assert (derivable s_q.know (Nonce query_nonce)) ;
               let p: derivation -> prop =
                (fun d0 -> derive d0 s_q.know = Some (Nonce query_nonce)) in
               let d0 = FStar.IndefiniteDescription.indefinite_description_ghost derivation p in
               assert (derive d0 s_q.know = Some (Nonce query_nonce)) ;
               assert (ma_valid_responder_nonces_not_derivable corrupt s_q);
               assert (False))
  in
  let valid_initiator_nonce_helper (query_session: session_id)
      (query_initiator query_responder: participant_id)
      (query_nonce: nonce)
      (d: derivation)
      : Lemma
        (ensures
          (match ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session with
          | Some initiator_state ->
            initiator_state.initiator == query_initiator /\
            initiator_state.responder == query_responder /\
            initiator_state.initiator_nonce == query_nonce /\
            not (Set.mem query_initiator corrupt) /\ not (Set.mem query_responder corrupt) ==>
            not (derive d s_q'.know = Some (Nonce query_nonce))
          | None -> True)) =
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey query_initiator query_session;
    match ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session with
    | None -> ()
    | Some initiator_state ->
      if initiator_state.initiator = query_initiator &&
         initiator_state.responder = query_responder &&
         initiator_state.initiator_nonce = query_nonce &&
         not (Set.mem query_initiator corrupt) && not (Set.mem query_responder corrupt) then
            if derive d s_q'.know = Some (Nonce query_nonce) then
              (assert (s_q'.know == Seq.snoc s_q.know sent_term) ;
               let subterms = derivable_subterms_underapproximate_keys s_q.know sent_term in
               if query_initiator = initiator && query_session = session then
                 // The freshly created initiator session: `query_nonce == initiator_nonce` and
                 // `query_responder == responder` (honest, by the guard), so the Message1 key is
                 // non-derivable, the only observable subterm is the ciphertext itself, and the
                 // fresh nonce's old derivability is impossible.
                 (assert (query_nonce == initiator_nonce) ;
                  assert (query_responder == responder) ;
                  no_old_responder_key_ideal () ;
                  derivable_from_observed_term_without_private_key_subterms
                    s_q.know sent_term d (Nonce query_nonce) ;
                  derivable_subterms_underapproximate_keys_exact_with_no_privkeys s_q.know sent_term ;
                  assert (~(Set.mem (Nonce query_nonce) subterms)) ;
                  built_from_subterms_nonce_derivable s_q.know subterms query_nonce ;
                  assert (derivable s_q.know (Nonce query_nonce)) ;
                  old_ideal_derivable_nonce_used query_nonce ;
                  assert (False))
               else
                 // A pre-existing initiator session (unchanged by initiator-start): its nonce is
                 // *used*, distinct from the fresh `initiator_nonce`, so it is not an observable
                 // subterm of Message1 and its old derivability is forbidden by secrecy at `s_q`.
                 (assert (matches_initiator_state s_q query_session query_initiator query_responder query_nonce) ;
                  assert (Set.mem query_nonce s_q.internal.used_nonces) ;
                  assert (~(Set.mem initiator_nonce s_q.internal.used_nonces)) ;
                  assert (query_nonce <> initiator_nonce) ;
                  derivable_from_observed_term_without_private_key_subterms
                    s_q.know sent_term d (Nonce query_nonce) ;
                  derivable_subterms_underapproximate_keys_exact_with_no_privkeys s_q.know sent_term ;
                  assert (~(Set.mem (Nonce query_nonce) subterms)) ;
                  built_from_subterms_nonce_derivable s_q.know subterms query_nonce ;
                  assert (derivable s_q.know (Nonce query_nonce)) ;
                  let p: derivation -> prop =
                   (fun d0 -> derive d0 s_q.know = Some (Nonce query_nonce)) in
                  let d0 = FStar.IndefiniteDescription.indefinite_description_ghost derivation p in
                  assert (ma_valid_initiator_nonces_not_derivable corrupt s_q) ;
                  assert (False)))
  in
  FStar.Classical.forall_intro_3 impl_private_helper;
  FStar.Classical.forall_intro_3 ideal_private_helper;
  introduce forall
    (query_session: session_id)
    (query_initiator query_responder: participant_id)
    (query_nonce: nonce)
    (d: derivation).
    (match ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session with
    | Some initiator_state ->
      initiator_state.initiator == query_initiator /\
      initiator_state.responder == query_responder /\
      initiator_state.initiator_nonce == query_nonce /\
      not (Set.mem query_initiator corrupt) /\ not (Set.mem query_responder corrupt) ==>
      not (derive d s_q'.know = Some (Nonce query_nonce))
    | None -> True)
  with valid_initiator_nonce_helper query_session query_initiator query_responder query_nonce d;
  introduce forall
    (query_session: session_id)
    (query_responder query_initiator: participant_id)
    (query_nonce: nonce)
    (d: derivation).
    (match ma_sim_responder_session_state (s2p_state s_q') query_responder query_session with
    | Some responder_state ->
      responder_state.responder == query_responder /\
      responder_state.initiator == query_initiator /\
      responder_state.responder_nonce == query_nonce /\
      not (Set.mem query_responder corrupt) /\ not (Set.mem query_initiator corrupt) ==>
      not (derive d s_q'.know = Some (Nonce query_nonce))
    | None -> True)
  with valid_nonce_helper query_session query_responder query_initiator query_nonce d;
  assert (ma_private_keys_not_derivable corrupt key_directory s_p' /\
     ma_private_keys_not_derivable corrupt key_directory s_q' /\
      ma_valid_initiator_nonces_not_derivable corrupt s_q' /\
     ma_valid_responder_nonces_not_derivable corrupt s_q')
#pop-options


let ma_nsl_initiator_start_state_preserves_impl_stored_nonces_are_used
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (post_know: knowledge term)
    : Lemma
      (requires ma_impl_stored_nonces_are_used s_p)
      (ensures
        ma_impl_stored_nonces_are_used
          (p2s_state
            (ma_nsl_initiator_start_state
              (s2p_state s_p) session initiator responder initiator_nonce)
            post_know)) =
  let s_p' =
    p2s_state
      (ma_nsl_initiator_start_state
        (s2p_state s_p) session initiator responder initiator_nonce)
      post_know
  in
  let stored_helper (query_participant: participant_id) (query_session: session_id) (n: nonce)
      : Lemma
        (ensures (
          match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
          | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
          | None -> True)) =
    ma_nsl_initiator_start_state_get_updated_participant_session_state (s2p_state s_p)
      session initiator responder initiator_nonce query_participant query_session;
    ma_nsl_initiator_start_state_preserves_used_nonces (s2p_state s_p)
      session initiator responder initiator_nonce;
    assert (match ma_get_participant_session_state (s2p_state s_p') query_participant query_session with
       | Some pss -> nonce_in_participant_session_state pss n ==> Set.mem n s_p'.internal.used_nonces
       | None -> True)
  in
  FStar.Classical.forall_intro_3 stored_helper

let ma_nsl_initiator_start_state_preserves_impl_used_nonces_invariant
      (s_p: impl_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires ma_impl_used_nonces_invariant s_p)
      (ensures
        ma_impl_used_nonces_invariant
          (p2s_state
            (ma_nsl_initiator_start_state
              (s2p_state s_p) session initiator responder initiator_nonce)
            (Seq.snoc s_p.know
              (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey)))) =
  let sent_term = ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey in
  let s_p' =
    p2s_state
      (ma_nsl_initiator_start_state (s2p_state s_p) session initiator responder initiator_nonce)
      (Seq.snoc s_p.know sent_term)
  in
  ma_nsl_initiator_start_state_inputs_eq (s2p_state s_p)
    session initiator responder initiator_nonce;
  ma_nsl_initiator_start_state_preserves_used_nonces (s2p_state s_p)
    session initiator responder initiator_nonce;
  ma_nsl_initiator_start_state_preserves_impl_stored_nonces_are_used s_p
    session initiator responder initiator_nonce (Seq.snoc s_p.know sent_term);
  let input_helper (input_t: term)
      : Lemma
        (ensures
          Bag.mem input_t s_p'.inputs ==>
          ma_term_nonces_are_used s_p'.internal.used_nonces input_t) =
    Bag.mem_remove input_t (ma_auth_input_term session initiator responder Initiator) (s2p_state s_p).inputs;
    assert (Bag.mem input_t s_p'.inputs ==>
       ma_term_nonces_are_used s_p'.internal.used_nonces input_t)
  in
  FStar.Classical.forall_intro input_helper;
  ma_message1_term_nonces_are_used_from_nonce
    s_p'.internal.used_nonces session initiator responder initiator_nonce responder_pubkey;
  ma_knowledge_nonces_snoc_preserves_subset s_p.know sent_term s_p'.internal.used_nonces;
  assert (ma_impl_used_nonces_invariant s_p')


/// =========================================================================
/// Relation preservation for the witness-matched observable steps
/// =========================================================================

#push-options ""

let ma_obs_bisim_observable_step_impl_initiator_start_preserves_basic_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
         in let s_q' =
            ma_impl_initiator_start_ideal_witness
              s_q session initiator responder initiator_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session initiator responder initiator_nonce responder_pubkey /\
          ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        (let s_q' =
          ma_impl_initiator_start_ideal_witness
            s_q session initiator responder initiator_nonce responder_pubkey in
        ma_same_knowledge s_p' s_q' /\
        ma_same_key_directory key_directory s_p' s_q' /\
        ma_same_inputs s_p' s_q' /\
        ma_same_used_nonces s_p' s_q')) =
  let sent_term =
    ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
  in
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  assert (s2p_state s_p' ==
      ma_nsl_initiator_start_state
        (s2p_state s_p) session initiator responder initiator_nonce) ;
  assert (s2p_state s_q' ==
      ma_sim_send_message1_state
        (ma_ideal_initiate_state
          (s2p_state s_q) session initiator responder Initiator)
        session initiator responder initiator_nonce) ;
  assert (ma_same_knowledge s_p' s_q') ;
  assert (ma_same_key_directory key_directory s_p' s_q') ;
  assert (ma_same_inputs s_p' s_q') ;
  assert (ma_same_used_nonces s_p' s_q') ;
  assert (ma_same_knowledge s_p' s_q' /\
     ma_same_key_directory key_directory s_p' s_q' /\
     ma_same_inputs s_p' s_q' /\
     ma_same_used_nonces s_p' s_q')

let ma_obs_bisim_observable_step_impl_initiator_start_preserves_session_correspondence_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
         in let s_q' =
            ma_impl_initiator_start_ideal_witness
              s_q session initiator responder initiator_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session initiator responder initiator_nonce responder_pubkey /\
          ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        (let s_q' =
          ma_impl_initiator_start_ideal_witness
            s_q session initiator responder initiator_nonce responder_pubkey in
        ma_initiator_session_correspondence s_p' s_q' /\
        ma_responder_session_correspondence s_p' s_q')) =
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  let initiator_corr_helper (query_session: session_id) (query_initiator: participant_id)
      : Lemma
      (ensures (
        let initiator_entry =
          ma_initiator_session_state (s2p_state s_p') query_initiator query_session
        in
        let sim_entry =
          ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session
        in
        (Some? initiator_entry <==> Some? sim_entry) /\
        (Some? initiator_entry ==> (
          let initiator_state = Some?.v initiator_entry in
          let sim_state = Some?.v sim_entry in
          initiator_state.initiator == sim_state.initiator /\
          initiator_state.responder == sim_state.responder /\
          initiator_state.initiator_nonce == sim_state.initiator_nonce /\
          initiator_state.ack_sent == sim_state.ack_sent)))) =
    ma_get_participant_session_state_after_update_same
      (s2p_state s_p) initiator session
      (InitiatorSession
        {
          initiator = initiator;
          responder = responder;
          initiator_nonce = initiator_nonce;
          ack_sent = false;
          output_sent = false
        });
    ma_get_sim_participant_session_state_after_update_same
      (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
      initiator session
      (SimInitiatorSession
        {
          initiator = initiator;
          responder = responder;
          initiator_nonce = initiator_nonce;
          ack_sent = false
        });
    ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s2p_state s_p) session initiator responder initiator_nonce
      query_initiator query_session;
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey
      query_initiator query_session;
    assert (let initiator_entry =
        ma_initiator_session_state (s2p_state s_p') query_initiator query_session
      in
      let sim_entry =
        ma_sim_initiator_session_state (s2p_state s_q') query_initiator query_session
      in
      (Some? initiator_entry <==> Some? sim_entry) /\
      (Some? initiator_entry ==> (
        let initiator_state = Some?.v initiator_entry in
        let sim_state = Some?.v sim_entry in
        initiator_state.initiator == sim_state.initiator /\
        initiator_state.responder == sim_state.responder /\
        initiator_state.initiator_nonce == sim_state.initiator_nonce /\
        initiator_state.ack_sent == sim_state.ack_sent)))
  in
  let responder_corr_helper (query_session: session_id) (query_responder: participant_id)
      : Lemma
      (ensures (
        let responder_entry =
          ma_responder_session_state (s2p_state s_p') query_responder query_session
        in
        let sim_entry =
          ma_sim_responder_session_state (s2p_state s_q') query_responder query_session
        in
        (Some? responder_entry <==> Some? sim_entry) /\
        (Some? responder_entry ==> (
          let responder_state = Some?.v responder_entry in
          let sim_state = Some?.v sim_entry in
          responder_state.responder == sim_state.responder /\
          responder_state.initiator == sim_state.initiator /\
          responder_state.responder_nonce == sim_state.responder_nonce /\
          responder_state.output_sent == sim_state.output_forwarded)))) =
    ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s2p_state s_p) session initiator responder initiator_nonce
      query_responder query_session;
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey
      query_responder query_session;
    assert (let responder_entry =
        ma_responder_session_state (s2p_state s_p') query_responder query_session
      in
      let sim_entry =
        ma_sim_responder_session_state (s2p_state s_q') query_responder query_session
      in
      (Some? responder_entry <==> Some? sim_entry) /\
      (Some? responder_entry ==> (
        let responder_state = Some?.v responder_entry in
        let sim_state = Some?.v sim_entry in
        responder_state.responder == sim_state.responder /\
        responder_state.initiator == sim_state.initiator /\
        responder_state.responder_nonce == sim_state.responder_nonce /\
        responder_state.output_sent == sim_state.output_forwarded)))
  in
  FStar.Classical.forall_intro_2 initiator_corr_helper;
  FStar.Classical.forall_intro_2 responder_corr_helper;
  assert (ma_initiator_session_correspondence s_p' s_q') ;
  assert (ma_responder_session_correspondence s_p' s_q') ;
  assert (ma_initiator_session_correspondence s_p' s_q' /\
     ma_responder_session_correspondence s_p' s_q')

let ma_initiator_ack_iff_from_structural_clauses_pre
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_same_inputs s_p s_q /\
        ma_same_key_directory key_directory s_p s_q /\
        ma_initiator_session_correspondence s_p s_q)
      (ensures
        ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p s_q
          session initiator responder responder_nonce initiator_key responder_pubkey) =
  let h_corr : squash (ma_initiator_session_correspondence s_p s_q) = () in
  let h_corr_session = FStar.Classical.Sugar.forall_elim session h_corr in
  let _h_corr_instance = FStar.Classical.Sugar.forall_elim initiator h_corr_session in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder responder_nonce initiator_key responder_pubkey)

let ma_obs_bisim_observable_step_impl_initiator_start_preserves_transition_equivalence_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey in
         let s_q' =
           ma_impl_initiator_start_ideal_witness
             s_q session initiator responder initiator_nonce responder_pubkey in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session initiator responder initiator_nonce responder_pubkey /\
          ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term /\
          ma_same_inputs s_p' s_q' /\
          ma_same_key_directory key_directory s_p' s_q' /\
          ma_same_used_nonces s_p' s_q' /\
          ma_initiator_session_correspondence s_p' s_q' /\
          ma_responder_session_correspondence s_p' s_q'))
      (ensures
        (let s_q' =
          ma_impl_initiator_start_ideal_witness
            s_q session initiator responder initiator_nonce responder_pubkey in
        ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
        ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q')) =
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  assert (ma_same_inputs s_p' s_q');
  assert (ma_same_key_directory key_directory s_p' s_q');
  assert (ma_same_used_nonces s_p' s_q');
  assert (ma_initiator_session_correspondence s_p' s_q');
  assert (ma_responder_session_correspondence s_p' s_q');
  let post_freshness_equiv (fresh_nonce: nonce)
    : Lemma
      (ensures
        (ma_nsl_nonce_is_fresh (s2p_state s_p') fresh_nonce <==>
         ma_sim_nonce_is_fresh (s2p_state s_q') fresh_nonce)) =
    assert (ma_nsl_nonce_is_fresh (s2p_state s_p') fresh_nonce <==>
       ma_sim_nonce_is_fresh (s2p_state s_q') fresh_nonce)
  in
  let post_ack_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_responder_nonce: nonce)
      (quant_initiator_key: priv_key)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (ensures
        ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_responder_nonce
          quant_initiator_key quant_responder_pubkey)
      [SMTPat (ma_initiator_ack_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_responder_nonce
          quant_initiator_key quant_responder_pubkey)] =
    ma_initiator_ack_iff_from_structural_clauses_pre corrupt key_directory s_p' s_q'
      quant_session quant_initiator quant_responder quant_responder_nonce
      quant_initiator_key quant_responder_pubkey
  in
  let post_responder_reply_iff_instance
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_initiator_nonce quant_responder_nonce: nonce)
      (quant_responder_key: priv_key)
      (quant_initiator_pubkey: term {PubKey? quant_initiator_pubkey})
    : Lemma
      (ensures
        ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)
      [SMTPat (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)] =
    post_freshness_equiv quant_responder_nonce;
    ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s2p_state s_p) session initiator responder initiator_nonce
      quant_responder quant_session;
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey
      quant_responder quant_session;
    assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p s_q
      quant_session quant_responder quant_initiator quant_initiator_nonce
      quant_responder_nonce quant_responder_key quant_initiator_pubkey);
    if quant_responder = initiator && quant_session = session then
      assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)
    else
      assert (ma_responder_reply_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_initiator_nonce
          quant_responder_nonce quant_responder_key quant_initiator_pubkey)
  in
  let post_initiator_output_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
    : Lemma
      (ensures
        ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder)
      [SMTPat (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder)] =
    ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s2p_state s_p) session initiator responder initiator_nonce
      quant_initiator quant_session;
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey
      quant_initiator quant_session;
    if quant_initiator = initiator && quant_session = session then
      assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder)
    else (
      assert (ma_nsl_initiator_output_enabled (s2p_state s_p')
          quant_session quant_initiator quant_responder <==>
         ma_nsl_initiator_output_enabled (s2p_state s_p)
          quant_session quant_initiator quant_responder) ;
      assert (ma_ideal_deliver_enabled (s2p_state s_q')
          quant_session quant_initiator quant_responder Initiator <==>
         ma_ideal_deliver_enabled (s2p_state s_q)
          quant_session quant_initiator quant_responder Initiator) ;
      assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p s_q
          quant_session quant_initiator quant_responder) ;
      assert (ma_initiator_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder))
  in
  let post_initiator_start_iff_instance
      (quant_session: session_id)
      (quant_initiator quant_responder: participant_id)
      (quant_initiator_nonce: nonce)
      (quant_responder_pubkey: term {PubKey? quant_responder_pubkey})
    : Lemma
      (ensures
        ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce
          quant_responder_pubkey)
      [SMTPat (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce
          quant_responder_pubkey)] =
    post_freshness_equiv quant_initiator_nonce;
    ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s2p_state s_p) session initiator responder initiator_nonce
      quant_initiator quant_session;
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey
      quant_initiator quant_session;
    assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
      quant_session quant_initiator quant_responder quant_initiator_nonce
      quant_responder_pubkey);
    if quant_initiator = initiator && quant_session = session then
      assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce
          quant_responder_pubkey)
    else
      assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_initiator quant_responder quant_initiator_nonce
          quant_responder_pubkey)
  in
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q') ;
  assert (ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q') ;
  assert (ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q') ;
  assert (ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q') ;
  assert (ma_initiator_ack_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_responder_reply_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_initiator_output_equivalent_transitions_enabled_iff s_p' s_q' /\
     ma_initiator_start_equivalent_transitions_enabled_iff s_p' s_q')

let ma_obs_bisim_observable_step_impl_initiator_start_preserves_used_nonces_invariant_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session initiator responder initiator_nonce responder_pubkey /\
          ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      // The ideal-side used-nonces invariant is re-established centrally by
      // `ma_impl_initiator_start_ideal_witness_preserves_inv`; this lemma only
      // discharges the implementation-side obligation.
      (ensures ma_impl_used_nonces_invariant s_p') =
  ma_nsl_initiator_start_state_preserves_impl_used_nonces_invariant
    s_p session initiator responder initiator_nonce responder_pubkey;
  assert (ma_impl_used_nonces_invariant s_p')

let ma_obs_bisim_observable_step_impl_initiator_start_preserves_ideal_bookkeeping_clauses
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
         in let s_q' =
            ma_impl_initiator_start_ideal_witness
              s_q session initiator responder initiator_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session initiator responder initiator_nonce responder_pubkey /\
          ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term /\
          ma_same_key_directory key_directory s_p' s_q' /\
          ma_initiator_session_correspondence s_p' s_q' /\
          ma_responder_session_correspondence s_p' s_q'))
      (ensures
        (let s_q' =
          ma_impl_initiator_start_ideal_witness
            s_q session initiator responder initiator_nonce responder_pubkey in
        ma_sim_session_matches_ideal_request s_q' /\
        ma_ideal_request_matches_sim_session s_q' /\
        ma_output_token_matches_sim_phase s_q' /\
        ma_initiator_output_token_matches_impl_pending_output s_p' s_q' /\
        ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')) =
  ma_ideal_system_inv_elim corrupt key_directory s_q;
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  assert (ma_same_key_directory key_directory s_p' s_q');
  assert (ma_initiator_session_correspondence s_p' s_q');
  assert (ma_responder_session_correspondence s_p' s_q');
  assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder initiator_nonce responder_pubkey) ;
  assert (ma_ideal_initiate_enabled (s2p_state s_q) session initiator responder Initiator) ;
  let post_sim_session_matches_ideal_request ()
      : Lemma (ensures ma_sim_session_matches_ideal_request s_q') =
    let helper (query_session: session_id) (query_participant: participant_id)
        : Lemma
          (ensures (
            match ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session with
            | Some (SimInitiatorSession initiator_state) ->
              initiator_state.initiator == query_participant /\
              Set.mem
                { party = query_participant; peer = initiator_state.responder; role = Initiator }
                (ma_session_requests (s2p_state s_q') query_session)
            | Some (SimResponderSession responder_state) ->
              responder_state.responder == query_participant /\
              Set.mem
                { party = query_participant; peer = responder_state.initiator; role = Responder }
                (ma_session_requests (s2p_state s_q') query_session)
            | None -> True)) =
      ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
        s_q session initiator responder initiator_nonce responder_pubkey
        query_participant query_session;
      assert (match ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session with
         | Some (SimInitiatorSession initiator_state) ->
           initiator_state.initiator == query_participant /\
           Set.mem
             { party = query_participant; peer = initiator_state.responder; role = Initiator }
             (ma_session_requests (s2p_state s_q') query_session)
         | Some (SimResponderSession responder_state) ->
           responder_state.responder == query_participant /\
           Set.mem
             { party = query_participant; peer = responder_state.initiator; role = Responder }
             (ma_session_requests (s2p_state s_q') query_session)
         | None -> True)
    in
    FStar.Classical.forall_intro_2 helper
  in
  let post_ideal_request_matches_sim_session ()
      : Lemma (ensures ma_ideal_request_matches_sim_session s_q') =
    let helper (query_session: session_id)
               (query_party query_peer: participant_id)
               (query_role: role)
        : Lemma
          (ensures
            Set.mem { party = query_party; peer = query_peer; role = query_role }
              (ma_session_requests (s2p_state s_q') query_session) ==>
            (match ma_get_sim_participant_session_state (s2p_state s_q') query_party query_session with
            | Some (SimInitiatorSession initiator_state) ->
              query_role == Initiator /\
              initiator_state.initiator == query_party /\
              initiator_state.responder == query_peer
            | Some (SimResponderSession responder_state) ->
              query_role == Responder /\
              responder_state.responder == query_party /\
              responder_state.initiator == query_peer
            | None -> False)) =
      ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
        s_q session initiator responder initiator_nonce responder_pubkey
        query_party query_session;
      ma_impl_initiator_start_ideal_witness_updated_session_requests
        s_q session initiator responder initiator_nonce responder_pubkey
        query_session;
      if query_session = session
      then ()
      else ()
    in
    FStar.Classical.forall_intro_4 helper
  in
  let post_output_token_matches_sim_phase ()
      : Lemma (ensures ma_output_token_matches_sim_phase s_q') =
    let helper (query_session: session_id) (query_participant: participant_id)
        : Lemma
          (ensures
            Set.mem (ma_output_term query_session query_participant)
              s_q'.internal.sim_to_ideal_channel ==>
            (match ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session with
            | Some (SimInitiatorSession initiator_state) ->
              initiator_state.initiator == query_participant /\ initiator_state.ack_sent
            | Some (SimResponderSession responder_state) ->
              responder_state.responder == query_participant /\ responder_state.output_forwarded
            | None -> False)) =
      ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
        s_q session initiator responder initiator_nonce responder_pubkey
        query_participant query_session;
      ma_nsl_initiator_start_state_get_updated_participant_session_state
        (s2p_state s_p) session initiator responder initiator_nonce
        query_participant query_session;
      assert (Set.mem (ma_output_term query_session query_participant)
          s_q'.internal.sim_to_ideal_channel ==>
        (match ma_get_sim_participant_session_state (s2p_state s_q') query_participant query_session with
        | Some (SimInitiatorSession initiator_state) ->
          initiator_state.initiator == query_participant /\ initiator_state.ack_sent
        | Some (SimResponderSession responder_state) ->
          responder_state.responder == query_participant /\ responder_state.output_forwarded
        | None -> False))
    in
    FStar.Classical.forall_intro_2 helper
  in
  let post_initiator_output_token_matches_impl_pending_output ()
      : Lemma (ensures ma_initiator_output_token_matches_impl_pending_output s_p' s_q') =
    let helper (query_session: session_id) (query_initiator: participant_id)
        : Lemma
          (ensures
            (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
            | Some initiator_state ->
              (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
              (initiator_state.ack_sent ==>
                (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
                 not initiator_state.output_sent))
            | None -> True)) =
      ma_nsl_initiator_start_state_get_updated_participant_session_state
        (s2p_state s_p) session initiator responder initiator_nonce
        query_initiator query_session;
      ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
        s_q session initiator responder initiator_nonce responder_pubkey
        query_initiator query_session;
      assert (ma_initiator_output_token_matches_impl_pending_output s_p s_q) ;
      let h_bridge
        : squash (ma_initiator_output_token_matches_impl_pending_output s_p s_q) = () in
      let h_bridge_session = FStar.Classical.Sugar.forall_elim query_session h_bridge in
      let _h_bridge_instance = FStar.Classical.Sugar.forall_elim query_initiator h_bridge_session in
      if query_initiator = initiator && query_session = session then
        assert (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
          | Some initiator_state ->
            (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
            (initiator_state.ack_sent ==>
              (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
               not initiator_state.output_sent))
          | None -> True)
      else
        assert (match ma_initiator_session_state (s2p_state s_p') query_initiator query_session with
          | Some initiator_state ->
            (not initiator_state.ack_sent ==> not initiator_state.output_sent) /\
            (initiator_state.ack_sent ==>
              (Set.mem (ma_output_term query_session query_initiator) s_q'.internal.sim_to_ideal_channel <==>
               not initiator_state.output_sent))
          | None -> True)
    in
    FStar.Classical.forall_intro_2 helper;
    assert (ma_initiator_output_token_matches_impl_pending_output s_p' s_q')
  in
  post_sim_session_matches_ideal_request ();
  post_ideal_request_matches_sim_session ();
  post_output_token_matches_sim_phase ();
  post_initiator_output_token_matches_impl_pending_output ();
  let post_responder_output_iff_instance
      (quant_session: session_id)
      (quant_responder quant_initiator: participant_id)
      (quant_responder_key: priv_key)
    : Lemma
      (ensures
        ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_responder_key)
      [SMTPat (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
          quant_session quant_responder quant_initiator quant_responder_key)] =
    ma_nsl_initiator_start_state_get_updated_participant_session_state
      (s2p_state s_p) session initiator responder initiator_nonce
      quant_responder quant_session;
    ma_impl_initiator_start_ideal_witness_get_updated_sim_participant_session_state
      s_q session initiator responder initiator_nonce responder_pubkey
      quant_responder quant_session;
    let post_impl_enabled_eq ()
        : Lemma
          (ensures
            (ma_nsl_responder_output_enabled (s2p_state s_p')
              quant_session quant_responder quant_initiator quant_responder_key <==>
             ma_nsl_responder_output_enabled (s2p_state s_p)
              quant_session quant_responder quant_initiator quant_responder_key)) =
      (match ma_responder_session_state (s2p_state s_p) quant_responder quant_session with
       | Some responder_state ->
         let message3_input = ma_nsl_message3_network_term
           quant_session quant_initiator quant_responder responder_state.responder_nonce
           (PubKey quant_responder_key)
         in
         Bag.mem_remove message3_input
           (ma_auth_input_term session initiator responder Initiator) (s2p_state s_p).inputs;
         assert (message3_input <> ma_auth_input_term session initiator responder Initiator)
       | None -> ());
      if quant_responder = initiator && quant_session = session then
        assert (ma_nsl_responder_output_enabled (s2p_state s_p')
            quant_session quant_responder quant_initiator quant_responder_key <==>
           ma_nsl_responder_output_enabled (s2p_state s_p)
            quant_session quant_responder quant_initiator quant_responder_key)
      else
        assert (ma_nsl_responder_output_enabled (s2p_state s_p')
            quant_session quant_responder quant_initiator quant_responder_key <==>
           ma_nsl_responder_output_enabled (s2p_state s_p)
            quant_session quant_responder quant_initiator quant_responder_key)
    in
    let post_sim_receive_enabled_eq ()
        : Lemma
          (ensures
            (ma_sim_receive_message3_enabled (s2p_state s_q')
              quant_session quant_responder quant_initiator quant_responder_key <==>
             ma_sim_receive_message3_enabled (s2p_state s_q)
              quant_session quant_responder quant_initiator quant_responder_key)) =
      (match ma_sim_responder_session_state (s2p_state s_q) quant_responder quant_session with
       | Some responder_state ->
         let message3_input = ma_nsl_message3_network_term
           quant_session quant_initiator quant_responder responder_state.responder_nonce
           (PubKey quant_responder_key)
         in
         Bag.mem_remove message3_input
           (ma_auth_input_term session initiator responder Initiator) (s2p_state s_q).inputs;
         assert (message3_input <> ma_auth_input_term session initiator responder Initiator)
       | None -> ());
      assert (ma_sim_receive_message3_enabled (s2p_state s_q')
          quant_session quant_responder quant_initiator quant_responder_key <==>
         ma_sim_receive_message3_enabled (s2p_state s_q)
          quant_session quant_responder quant_initiator quant_responder_key)
    in
    assert (ma_ideal_request_matches_sim_session s_q');
    assert (ma_output_token_matches_sim_phase s_q');
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q
      quant_session quant_responder quant_initiator quant_responder_key);
    post_impl_enabled_eq ();
    post_sim_receive_enabled_eq ();
    let post_ideal_enabled_eq ()
        : Lemma
          (ensures
            ((ma_sim_receive_message3_enabled (s2p_state s_q')
                quant_session quant_responder quant_initiator quant_responder_key /\
              ma_ideal_deliver_enabled
                (ma_sim_receive_message3_state (s2p_state s_q')
                  quant_session quant_responder quant_initiator quant_responder_key)
                quant_session quant_responder quant_initiator Responder) <==>
             (ma_sim_receive_message3_enabled (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key /\
              ma_ideal_deliver_enabled
                (ma_sim_receive_message3_state (s2p_state s_q)
                  quant_session quant_responder quant_initiator quant_responder_key)
                quant_session quant_responder quant_initiator Responder))) =
      // The initiator-start witness may add a complementary request for this
      // responder-output query, so bare `ma_ideal_deliver_enabled` is not stable.
      // The stable fact is the whole responder-output right-hand side: whenever
      // simulator Message3 receive is enabled in the pre-state, structural
      // correspondence makes the implementation responder-output step enabled,
      // and the old bisimulation clause then forces the ideal-deliver side.
      let pre_sim_receive_implies_impl_output ()
          : Lemma
            (ensures
              ma_sim_receive_message3_enabled (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key ==>
              ma_nsl_responder_output_enabled (s2p_state s_p)
                quant_session quant_responder quant_initiator quant_responder_key) =
        assert (ma_same_inputs s_p s_q /\
           ma_same_key_directory key_directory s_p s_q /\
           ma_responder_session_correspondence s_p s_q) ;
        let h_corr : squash (ma_responder_session_correspondence s_p s_q) = () in
        let h_corr_session = FStar.Classical.Sugar.forall_elim quant_session h_corr in
        let _h_corr_instance = FStar.Classical.Sugar.forall_elim quant_responder h_corr_session in
        let impl_entry =
          ma_responder_session_state (s2p_state s_p) quant_responder quant_session in
        let sim_entry =
          ma_sim_responder_session_state (s2p_state s_q) quant_responder quant_session in
        match sim_entry with
        | None ->
          assert (ma_sim_receive_message3_enabled (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key ==>
              ma_nsl_responder_output_enabled (s2p_state s_p)
                quant_session quant_responder quant_initiator quant_responder_key)
        | Some sim_state ->
          assert (Some? impl_entry) ;
          match impl_entry with
          | None ->
            assert (False)
          | Some impl_state ->
            assert (impl_state.responder == sim_state.responder /\
               impl_state.initiator == sim_state.initiator /\
               impl_state.responder_nonce == sim_state.responder_nonce /\
               impl_state.output_sent == sim_state.output_forwarded) ;
            let _h_impl
              : squash
                  (ma_sim_receive_message3_enabled (s2p_state s_q)
                     quant_session quant_responder quant_initiator quant_responder_key ==>
                   ma_nsl_responder_output_enabled (s2p_state s_p)
                     quant_session quant_responder quant_initiator quant_responder_key)
              = FStar.Classical.Sugar.implies_intro
                (ma_sim_receive_message3_enabled (s2p_state s_q)
                  quant_session quant_responder quant_initiator quant_responder_key)
                (fun _ ->
                  ma_nsl_responder_output_enabled (s2p_state s_p)
                    quant_session quant_responder quant_initiator quant_responder_key)
                (fun h_enabled ->
            assert (sim_state.responder == quant_responder /\
               sim_state.initiator == quant_initiator /\
               not sim_state.output_forwarded /\
               PartialMap.sel (s2p_state s_q).internal.key_directory quant_responder == Some quant_responder_key /\
               Bag.mem (ma_nsl_message3_network_term
                 quant_session quant_initiator quant_responder sim_state.responder_nonce (PubKey quant_responder_key))
                 (s2p_state s_q).inputs) ;
            assert (impl_state.responder == quant_responder /\
               impl_state.initiator == quant_initiator /\
               impl_state.responder_nonce == sim_state.responder_nonce /\
               not impl_state.output_sent) ;
            assert (PartialMap.sel (s2p_state s_p).internal.key_directory quant_responder == Some quant_responder_key) ;
            let sim_message3_input = ma_nsl_message3_network_term
              quant_session quant_initiator quant_responder sim_state.responder_nonce (PubKey quant_responder_key) in
            let impl_message3_input = ma_nsl_message3_network_term
              quant_session quant_initiator quant_responder impl_state.responder_nonce (PubKey quant_responder_key) in
            assert (impl_message3_input == sim_message3_input) ;
            assert (Bag.mem sim_message3_input (s2p_state s_p).inputs) ;
            assert (Bag.mem impl_message3_input (s2p_state s_p).inputs) ;
            assert (ma_responder_session_state (s2p_state s_p) quant_responder quant_session == Some impl_state) ;
            assert (impl_state.responder == quant_responder) ;
            assert (impl_state.initiator == quant_initiator) ;
            assert (not impl_state.output_sent) ;
            assert (PartialMap.sel (s2p_state s_p).internal.key_directory quant_responder == Some quant_responder_key) ;
            assert (Bag.mem (ma_nsl_message3_network_term
                 quant_session quant_initiator quant_responder impl_state.responder_nonce (PubKey quant_responder_key))
                 (s2p_state s_p).inputs) ;
            assert (impl_state.responder == quant_responder /\
               impl_state.initiator == quant_initiator /\
               not impl_state.output_sent /\
               PartialMap.sel (s2p_state s_p).internal.key_directory quant_responder == Some quant_responder_key /\
               Bag.mem (ma_nsl_message3_network_term
                 quant_session quant_initiator quant_responder impl_state.responder_nonce (PubKey quant_responder_key))
                 (s2p_state s_p).inputs) ;
            assert (ma_nsl_responder_output_enabled (s2p_state s_p)
                 quant_session quant_responder quant_initiator quant_responder_key <==>
               (match impl_entry with
                | Some responder_state ->
                  responder_state.responder == quant_responder /\
                  responder_state.initiator == quant_initiator /\
                  not responder_state.output_sent /\
                  PartialMap.sel (s2p_state s_p).internal.key_directory quant_responder == Some quant_responder_key /\
                  Bag.mem (ma_nsl_message3_network_term
                    quant_session quant_initiator quant_responder responder_state.responder_nonce (PubKey quant_responder_key))
                    (s2p_state s_p).inputs
                | None -> False)) ;
            assert (ma_nsl_responder_output_enabled (s2p_state s_p)
                quant_session quant_responder quant_initiator quant_responder_key) ;
            (() <: squash
              (ma_nsl_responder_output_enabled (s2p_state s_p)
                quant_session quant_responder quant_initiator quant_responder_key)))
            in
            ()
      in
      let pre_sim_receive_implies_pre_ideal_deliver ()
          : Lemma
            (ensures
              ma_sim_receive_message3_enabled (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key ==>
              ma_ideal_deliver_enabled
                (ma_sim_receive_message3_state (s2p_state s_q)
                  quant_session quant_responder quant_initiator quant_responder_key)
                quant_session quant_responder quant_initiator Responder) =
        pre_sim_receive_implies_impl_output ();
        assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p s_q
            quant_session quant_responder quant_initiator quant_responder_key) ;
        assert (ma_sim_receive_message3_enabled (s2p_state s_q)
              quant_session quant_responder quant_initiator quant_responder_key ==>
            ma_ideal_deliver_enabled
              (ma_sim_receive_message3_state (s2p_state s_q)
                quant_session quant_responder quant_initiator quant_responder_key)
              quant_session quant_responder quant_initiator Responder)
      in
      pre_sim_receive_implies_pre_ideal_deliver ();
      ma_impl_initiator_start_ideal_witness_updated_session_requests
        s_q session initiator responder initiator_nonce responder_pubkey
        quant_session;
      ma_sim_receive_message3_state_session_requests_eq
        (s2p_state s_q) quant_session quant_responder quant_initiator
        quant_responder_key quant_session;
      ma_sim_receive_message3_state_session_requests_eq
        (s2p_state s_q') quant_session quant_responder quant_initiator
        quant_responder_key quant_session;
      assert ((ma_sim_receive_message3_enabled (s2p_state s_q')
            quant_session quant_responder quant_initiator quant_responder_key /\
          ma_ideal_deliver_enabled
            (ma_sim_receive_message3_state (s2p_state s_q')
              quant_session quant_responder quant_initiator quant_responder_key)
            quant_session quant_responder quant_initiator Responder) <==>
         (ma_sim_receive_message3_enabled (s2p_state s_q)
            quant_session quant_responder quant_initiator quant_responder_key /\
          ma_ideal_deliver_enabled
            (ma_sim_receive_message3_state (s2p_state s_q)
              quant_session quant_responder quant_initiator quant_responder_key)
            quant_session quant_responder quant_initiator Responder))
    in
    post_ideal_enabled_eq ();
    assert (ma_responder_output_equivalent_transitions_enabled_iff_instance s_p' s_q'
        quant_session quant_responder quant_initiator quant_responder_key)
  in
  assert (ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q') ;
  assert (ma_sim_session_matches_ideal_request s_q' /\
     ma_ideal_request_matches_sim_session s_q' /\
     ma_output_token_matches_sim_phase s_q' /\
     ma_initiator_output_token_matches_impl_pending_output s_p' s_q' /\
     ma_responder_output_equivalent_transitions_enabled_iff s_p' s_q')

let ma_obs_bisim_observable_step_impl_initiator_start_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_p': impl_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session
            initiator
            responder
            initiator_nonce
            responder_pubkey /\
          ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p') /\
          s_p'.know == Seq.snoc s_p.know sent_term))
      (ensures
        ma_bisim_relation corrupt key_directory
          s_p'
          (ma_impl_initiator_start_ideal_witness s_q
              session
              initiator
              responder
              initiator_nonce
              responder_pubkey)) =
  let s_q' =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  ma_obs_bisim_observable_step_impl_initiator_start_preserves_basic_clauses
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p';
  ma_obs_bisim_observable_step_impl_initiator_start_preserves_session_correspondence_clauses
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p';
  ma_obs_bisim_observable_step_impl_initiator_start_preserves_used_nonces_invariant_clauses
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p';
  ma_obs_bisim_observable_step_impl_initiator_start_preserves_ideal_bookkeeping_clauses
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p';
  ma_obs_bisim_observable_step_impl_initiator_start_preserves_transition_equivalence_clauses
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p';
  ma_impl_initiator_start_preserves_secrecy_clauses
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p';
  // Re-establish the ideal-side invariant at the post-state via the witness
  // preservation lemma instead of carrying it as a precondition.
  assert (ma_initiator_start_equivalent_transitions_enabled_iff_instance s_p s_q
      session initiator responder initiator_nonce responder_pubkey) ;
  assert (ma_ideal_initiate_enabled (s2p_state s_q) session initiator responder Initiator) ;
  assert (ma_sim_send_message1_enabled
      (ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator)
      session initiator responder initiator_nonce responder_pubkey) ;
  ma_impl_initiator_start_ideal_witness_preserves_inv
    corrupt key_directory s_q session initiator responder initiator_nonce responder_pubkey;
  assert (ma_ideal_system_inv corrupt key_directory s_q') ;
  assert (ma_bisim_relation corrupt key_directory s_p' s_q')

#pop-options


let ma_obs_bisim_observable_step_ideal_send_message1_preserves_relation
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term{PubKey? responder_pubkey})
      (s_q': ideal_system_state)
    : Lemma
      (requires
        (let sent_term =
            ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
          in
          ma_bisim_relation corrupt key_directory s_p s_q /\
          ma_nsl_initiator_start_enabled (s2p_state s_p)
            session
            initiator
            responder
            initiator_nonce
            responder_pubkey /\
          (exists (s_q_mid: ideal_system_state).
              // ma_ideal_initiate_protocol_transition is existentially
              // quantified over the party, peer, and role parameters that
              // determine stepped to state for the transition. As a result, the
              // `ma_ideal_initiate_protocol_transition (s2p_state s_q) session
              // (s2p_state s_q_mid)` relation could hold here for different
              // parameters. We therefore explicitly characterize the
              // existentially quantified transition parameters by adding the
              // stepped to state here. When this proof is used in the main
              // bisimulation proof, these parameters and facts can be pulled
              // from the `ma_ideal_initiate_protocol_transition` assumption.
              (s2p_state s_q_mid == ma_ideal_initiate_state (s2p_state s_q) session initiator responder Initiator) /\
              ma_ideal_initiate_protocol_transition (s2p_state s_q) session initiator responder Initiator (s2p_state s_q_mid) /\
              s_q_mid.know == s_q.know /\
              ma_sim_send_message1_protocol_transition (s2p_state s_q_mid)
                session
                initiator
                responder
                sent_term
                (s2p_state s_q') /\
              s_q'.know == Seq.snoc s_q_mid.know sent_term)))
      (ensures
        ma_bisim_relation corrupt key_directory
          (ma_ideal_send_message1_impl_witness s_p
              session
              initiator
              responder
              initiator_nonce
              responder_pubkey)
          s_q') =
  let sent_term =
    ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey
  in
  let s_p' =
    ma_ideal_send_message1_impl_witness
      s_p session initiator responder initiator_nonce responder_pubkey
  in
  let s_q_witness =
    ma_impl_initiator_start_ideal_witness
      s_q session initiator responder initiator_nonce responder_pubkey
  in
  assert (s2p_state s_p' ==
      ma_nsl_initiator_start_state
        (s2p_state s_p) session initiator responder initiator_nonce) ;
  assert (s_p'.know == Seq.snoc s_p.know sent_term) ;
  assert (sent_term == MA.NSL.ma_nsl_message1_term
      session initiator responder initiator_nonce responder_pubkey) ;
  introduce exists initiator' responder' initiator_nonce' responder_pubkey'.
    ma_nsl_initiator_start_enabled
      (s2p_state s_p) session initiator' responder' initiator_nonce' responder_pubkey' /\
    sent_term == MA.NSL.ma_nsl_message1_term
      session initiator' responder' initiator_nonce' responder_pubkey' /\
    s2p_state s_p' ==
      ma_nsl_initiator_start_state
        (s2p_state s_p) session initiator' responder' initiator_nonce'
  with initiator responder initiator_nonce responder_pubkey
  and ();
  assert (ma_nsl_initiator_start_transition (s2p_state s_p) session initiator responder sent_term (s2p_state s_p')) ;
  assert (ma_bisim_relation corrupt key_directory s_p s_q) ;
  // ma_ideal_send_message1_transition_uses_selected_initiate
  //   key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_q';
  assert (s_q'.know == Seq.snoc s_q.know sent_term) ;
  assert (s_q' == s_q_witness) ;
  ma_obs_bisim_observable_step_impl_initiator_start_preserves_relation
    corrupt key_directory s_p s_q session initiator responder initiator_nonce responder_pubkey s_p'
