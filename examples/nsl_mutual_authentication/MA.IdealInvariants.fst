module MA.IdealInvariants

open SymbolicTypes
open AencTerms
open AdversaryAenc
open TestedSystem
open Bag

open MA.Types
open MA.NSL
open MA.Ideal
open MA.Adversary
open MA.TestedProtocols

module PartialMap = FStar.PartialMap
module Set = FStar.Set
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module List = FStar.List.Tot.Base

/// ===========================================================================
/// Nonce-in-knowledge derivation lemmas.
/// ===========================================================================

private
let rec ma_term_list_nonces_index_subset
      (ts: list term)
      (i: nat {i < List.length ts})
      (t: term)
    : Lemma
      (requires List.index ts i == t)
      (ensures Set.subset (ma_term_nonces t) (ma_term_list_nonces ts)) =
  match ts with
  | [] -> ()
  | hd :: tl ->
    if i = 0 then
      (assert (t == hd);
       let helper (n: nonce)
           : Lemma (ensures Set.mem n (ma_term_nonces t) ==> Set.mem n (ma_term_list_nonces ts)) =
         Set.mem_union n (ma_term_nonces hd) (ma_term_list_nonces tl)
       in
       FStar.Classical.forall_intro helper;
       Set.mem_subset (ma_term_nonces t) (ma_term_list_nonces ts))
    else
      (ma_term_list_nonces_index_subset tl (i - 1) t;
       Set.subset_mem (ma_term_nonces t) (ma_term_list_nonces tl);
       let helper (n: nonce)
           : Lemma (ensures Set.mem n (ma_term_nonces t) ==> Set.mem n (ma_term_list_nonces ts)) =
         Set.mem_union n (ma_term_nonces hd) (ma_term_list_nonces tl)
       in
       FStar.Classical.forall_intro helper;
       Set.mem_subset (ma_term_nonces t) (ma_term_list_nonces ts))

private
let ma_knowledge_nonces_index_subset
      (know: knowledge term)
      (i: nat {i < Seq.length know})
      (t: term)
    : Lemma
      (requires Seq.index know i == t)
      (ensures Set.subset (ma_term_nonces t) (ma_knowledge_nonces know)) =
  SeqProps.lemma_index_is_nth know i;
  ma_term_list_nonces_index_subset (Seq.seq_to_list know) i t

private
let rec ma_derive_term_nonces_in_knowledge_nonces
      (know: knowledge term)
      (d: derivation)
      (t: term)
    : Lemma
      (requires derive d know = Some t)
      (ensures Set.subset (ma_term_nonces t) (ma_knowledge_nonces know)) =
  match d with
  | DeriveObserved observed_index ->
    if observed_index < Seq.length know then
      ma_knowledge_nonces_index_subset know observed_index t
    else assert false
  | DeriveAEncrypt plaintext_derivation key_derivation ->
    (match derive plaintext_derivation know, derive key_derivation know with
    | Some plaintext, Some (PubKey key) ->
      ma_derive_term_nonces_in_knowledge_nonces know plaintext_derivation plaintext;
      assert (t == Aenc plaintext key)
    | _, _ -> assert false)
  | DeriveADecrypt ciphertext_derivation key_derivation ->
    (match derive ciphertext_derivation know, derive key_derivation know with
    | Some (Aenc plaintext key1), Some (PrivKey key2) ->
      if key1 = key2 then
        (ma_derive_term_nonces_in_knowledge_nonces know ciphertext_derivation (Aenc plaintext key1);
         assert (t == plaintext))
      else assert false
    | _, _ -> assert false)
  | DerivePair left_derivation right_derivation ->
    (match derive left_derivation know, derive right_derivation know with
    | Some left, Some right ->
      ma_derive_term_nonces_in_knowledge_nonces know left_derivation left;
      ma_derive_term_nonces_in_knowledge_nonces know right_derivation right;
      assert (t == Pair left right);
      Set.subset_mem (ma_term_nonces left) (ma_knowledge_nonces know);
      Set.subset_mem (ma_term_nonces right) (ma_knowledge_nonces know);
      let helper (n: nonce)
          : Lemma (ensures Set.mem n (ma_term_nonces t) ==> Set.mem n (ma_knowledge_nonces know)) =
        Set.mem_union n (ma_term_nonces left) (ma_term_nonces right)
      in
      FStar.Classical.forall_intro helper;
      Set.mem_subset (ma_term_nonces t) (ma_knowledge_nonces know)
    | _, _ -> assert false)
  | DerivePairLeft pair_derivation ->
    (match derive pair_derivation know with
    | Some (Pair left right) ->
      ma_derive_term_nonces_in_knowledge_nonces know pair_derivation (Pair left right);
      assert (t == left);
      Set.subset_mem (ma_term_nonces (Pair left right)) (ma_knowledge_nonces know);
      let helper (n: nonce)
          : Lemma (ensures Set.mem n (ma_term_nonces t) ==> Set.mem n (ma_knowledge_nonces know)) =
        Set.mem_union n (ma_term_nonces left) (ma_term_nonces right)
      in
      FStar.Classical.forall_intro helper;
      Set.mem_subset (ma_term_nonces t) (ma_knowledge_nonces know)
    | _ -> assert false)
  | DerivePairRight pair_derivation ->
    (match derive pair_derivation know with
    | Some (Pair left right) ->
      ma_derive_term_nonces_in_knowledge_nonces know pair_derivation (Pair left right);
      assert (t == right);
      Set.subset_mem (ma_term_nonces (Pair left right)) (ma_knowledge_nonces know);
      let helper (n: nonce)
          : Lemma (ensures Set.mem n (ma_term_nonces t) ==> Set.mem n (ma_knowledge_nonces know)) =
        Set.mem_union n (ma_term_nonces left) (ma_term_nonces right)
      in
      FStar.Classical.forall_intro helper;
      Set.mem_subset (ma_term_nonces t) (ma_knowledge_nonces know)
    | _ -> assert false)


/// ===========================================================================
/// State invariant preservation.
///
/// Establishes `ma_ideal_state_inv` at the initial state and proves it is
/// preserved by every ideal+simulator protocol transition.
/// ===========================================================================

/// If two states agree pointwise on their `ma_session_requests` maps, then I2
/// transfers from one to the other.  Factored into a pure, low-fuel lemma so the
/// requests-unchanged preservation helpers (send1/send2/send3/recv3/deliver) can
/// discharge I2 explicitly and locally instead of relying on the I2(s)
/// quantifier being re-triggered through the SMTPat rewrite (which is fragile in
/// this large module).
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private
let _requests_eq_preserves_one_request_per_party
      (s sx: ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_inv_one_request_per_party s /\
        (forall (i: session_id). ma_session_requests sx i == ma_session_requests s i))
      (ensures ma_ideal_inv_one_request_per_party sx) =
  introduce forall (i: session_id) (r1 r2: auth_request).
    (Set.mem r1 (ma_session_requests sx i) /\
     Set.mem r2 (ma_session_requests sx i) /\
     r1.party == r2.party) ==> r1 == r2
  with introduce _ ==> _ with _hmem.
    assert (ma_session_requests sx i == ma_session_requests s i)
#pop-options

/// If two states share the same `internal.requests` map, their per-session
/// `ma_session_requests` agree pointwise.  Pure, low-fuel; unfolds the single
/// `PartialMap.sel` that `ma_session_requests` performs.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private
let _internal_requests_eq_session_requests_eq
      (s sx: ideal_proto_state)
    : Lemma
      (requires sx.internal.requests == s.internal.requests)
      (ensures forall (i: session_id). ma_session_requests sx i == ma_session_requests s i) =
  introduce forall (i: session_id). ma_session_requests sx i == ma_session_requests s i
  with assert (ma_session_requests sx i == ma_session_requests s i)
#pop-options

/// --- Initial state establishes the invariant ---
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let ma_ideal_state_inv_init key_directory corrupt know0 =
  let s = ma_ideal_protocol_init key_directory corrupt know0 in
  // Requests map, both channels, and the session map are empty, so every
  // conjunct of the invariant is vacuously true.
  assert (forall (i: session_id). ma_session_requests s i == Set.empty);
  assert (s.internal.ideal_to_sim_channel == Set.empty);
  assert (s.internal.sim_to_ideal_channel == Set.empty)
#pop-options

/// `send1` lacks a packaged `get_updated_sim_participant_session_state` lemma in
/// `MA.Ideal`, so we derive one here from the generic update lemmas (the outer
/// record update of `ma_sim_send_message1_state` leaves the
/// `sim_participant_sessions` field untouched).  Defined before the preservation
/// helpers so `ma_ideal_state_inv_preserved_send1` can use it; it is also reused
/// by the freshness/provenance helpers further down.
private
let _send1_get_updated
      (s: ideal_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (qp: participant_id)
      (qs: session_id)
    : Lemma
      (ensures (
        let s' = ma_sim_send_message1_state s session initiator responder initiator_nonce in
        let new_state =
          SimInitiatorSession
            {
              initiator = initiator;
              responder = responder;
              initiator_nonce = initiator_nonce;
              ack_sent = false
            }
        in
        if qp = initiator && qs = session then
          ma_get_sim_participant_session_state s' qp qs == Some new_state
        else
          ma_get_sim_participant_session_state s' qp qs ==
          ma_get_sim_participant_session_state s qp qs)) =
  let new_state =
    SimInitiatorSession
      {
        initiator = initiator;
        responder = responder;
        initiator_nonce = initiator_nonce;
        ack_sent = false
      }
  in
  let upd = ma_update_sim_participant_session_state s initiator session new_state in
  // The outer record update only touches `used_nonces` and `ideal_to_sim_channel`,
  // so the simulator-session map is exactly that of `upd`.
  assert (ma_get_sim_participant_session_state
            (ma_sim_send_message1_state s session initiator responder initiator_nonce) qp qs ==
          ma_get_sim_participant_session_state upd qp qs);
  if qp = initiator && qs = session then
    ma_get_sim_participant_session_state_after_update_same s initiator session new_state
  else
    ma_get_sim_participant_session_state_after_update_different s initiator session new_state qp qs

/// `MA.Ideal` also ships no `session_requests`-preservation SMTPat for send1
/// (unlike send2/send3/recv3).  send1 only updates `used_nonces`,
/// `ideal_to_sim_channel`, and `sim_participant_sessions`, leaving the request
/// map untouched, so this is trivially `()`.  Supplying the SMTPat lets the
/// request-bookkeeping conjuncts (I2, H_auth_*, H_init/H_resp) connect
/// `ma_session_requests sx` to `ma_session_requests s` automatically.
private
let _send1_preserves_session_requests
      (s: ideal_proto_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (query_session: session_id)
    : Lemma
      (ensures
        ma_session_requests
          (ma_sim_send_message1_state s session initiator responder initiator_nonce)
          query_session ==
        ma_session_requests s query_session)
      [SMTPat (ma_session_requests
        (ma_sim_send_message1_state s session initiator responder initiator_nonce)
        query_session)] =
  ()

/// --- Per-transition preservation helpers ---
#push-options "--fuel 1 --ifuel 2 --z3rlimit 100"

#push-options "--z3rlimit 80 --ifuel 2"
let ma_ideal_state_inv_preserved_initiate
      (s: ideal_proto_state) (session: session_id)
      (party peer: participant_id) (r: role) (s': ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_state_inv s /\
        ma_ideal_initiate_protocol_transition s session party peer r s')
      (ensures ma_ideal_state_inv s')
  = let added = { party = party; peer = peer; role = r } in
    // I2: at most one request per party per session.
    introduce forall (i: session_id) (r1 r2: auth_request).
      (Set.mem r1 (ma_session_requests s' i) /\
       Set.mem r2 (ma_session_requests s' i) /\
       r1.party == r2.party) ==> r1 == r2
    with introduce _ ==> _ with _hmem. ();
    // H_auth_init: leaked Initiator notification implies the request is stored.
    introduce forall (i: session_id) (p q: participant_id).
      Set.mem (ma_authenticating_term i p q Initiator) s'.internal.ideal_to_sim_channel ==>
      Set.mem ({ party = p; peer = q; role = Initiator }) (ma_session_requests s' i)
    with introduce _ ==> _ with _hmem. ();
    // H_auth_resp: leaked Responder notification implies the request is stored.
    introduce forall (i: session_id) (p q: participant_id).
      Set.mem (ma_authenticating_term i p q Responder) s'.internal.ideal_to_sim_channel ==>
      Set.mem ({ party = p; peer = q; role = Responder }) (ma_session_requests s' i)
    with introduce _ ==> _ with _hmem. ()
#pop-options

let ma_ideal_state_inv_preserved_send1
      (s: ideal_proto_state) (session: session_id)
      (party peer: participant_id) (sent_t: term) (s': ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_state_inv s /\
        ma_sim_send_message1_protocol_transition s session party peer sent_t s')
      (ensures ma_ideal_state_inv s')
  = eliminate exists (initiator_nonce: nonce)
                     (responder_pubkey: term {PubKey? responder_pubkey}).
      ma_sim_send_message1_enabled s session party peer initiator_nonce responder_pubkey /\
      sent_t == ma_nsl_message1_term session party peer initiator_nonce responder_pubkey /\
      s' == ma_sim_send_message1_state s session party peer initiator_nonce
    returns ma_ideal_state_inv s'
    with _h.
      let sx = ma_sim_send_message1_state s session party peer initiator_nonce in
      // send1 leaves the request map untouched; transfer I2 explicitly.
      _send1_preserves_session_requests s session party peer initiator_nonce session;
      assert (forall (i: session_id). ma_session_requests sx i == ma_session_requests s i);
      _requests_eq_preserves_one_request_per_party s sx;
      assert (ma_ideal_inv_one_request_per_party sx);
      // send1 leaves the recorded requests and the relevant ideal->sim channel
      // membership unchanged, so the H_auth_* conjuncts transfer directly.
      assert (ma_ideal_inv_auth_init_has_request sx);
      assert (ma_ideal_inv_auth_resp_has_request sx);
      assert (ma_ideal_state_inv sx)

let ma_ideal_state_inv_preserved_send2
      (s: ideal_proto_state) (session: session_id)
      (party peer: participant_id) (sent_t: term) (s': ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_state_inv s /\
        ma_sim_send_message2_protocol_transition s session party peer sent_t s')
      (ensures ma_ideal_state_inv s')
  = eliminate exists (initiator_nonce responder_nonce: nonce)
                     (responder_key: priv_key)
                     (initiator_pubkey: term {PubKey? initiator_pubkey}).
      ma_sim_send_message2_enabled
        s session party peer initiator_nonce responder_nonce responder_key initiator_pubkey /\
      sent_t == ma_nsl_message2_term
        session peer party initiator_nonce responder_nonce initiator_pubkey /\
      s' == ma_sim_send_message2_state
        s session party peer initiator_nonce responder_nonce responder_key
    returns ma_ideal_state_inv s'
    with _h.
      let sx = ma_sim_send_message2_state
        s session party peer initiator_nonce responder_nonce responder_key in
      // send2 leaves the request map untouched, so transfer every conjunct that
      // only depends on the requests to `sx` explicitly and locally (rather than
      // hoping the I2(s) quantifier triggers through the SMTPat rewrite).
      ma_sim_send_message2_state_preserves_requests
        s session party peer initiator_nonce responder_nonce responder_key;
      assert (forall (i: session_id). ma_session_requests sx i == ma_session_requests s i);
      _requests_eq_preserves_one_request_per_party s sx;
      assert (ma_ideal_inv_one_request_per_party sx);
      // send2 leaves the recorded requests and the relevant ideal->sim channel
      // membership unchanged, so the H_auth_* conjuncts transfer directly.
      assert (ma_ideal_inv_auth_init_has_request sx);
      assert (ma_ideal_inv_auth_resp_has_request sx);
      assert (ma_ideal_state_inv sx)

let ma_ideal_state_inv_preserved_send3
      (s: ideal_proto_state) (session: session_id)
      (party peer: participant_id) (sent_t: term) (s': ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_state_inv s /\
        ma_sim_send_message3_protocol_transition s session party peer sent_t s')
      (ensures ma_ideal_state_inv s')
  = eliminate exists (responder_nonce: nonce)
                     (initiator_key: priv_key)
                     (responder_pubkey: term {PubKey? responder_pubkey}).
      ma_sim_send_message3_enabled
        s session party peer responder_nonce initiator_key responder_pubkey /\
      sent_t == ma_nsl_message3_term session party peer responder_nonce responder_pubkey /\
      s' == ma_sim_send_message3_state s session party peer responder_nonce initiator_key
    returns ma_ideal_state_inv s'
    with _h.
      let sx = ma_sim_send_message3_state s session party peer responder_nonce initiator_key in
      // send3 leaves the request map untouched; transfer I2 explicitly.
      ma_sim_send_message3_state_session_requests_eq s session party peer responder_nonce initiator_key session;
      assert (forall (i: session_id). ma_session_requests sx i == ma_session_requests s i);
      _requests_eq_preserves_one_request_per_party s sx;
      assert (ma_ideal_inv_one_request_per_party sx);
      // send3 leaves the recorded requests and the ideal->sim channel untouched,
      // so the H_auth_* conjuncts transfer directly.
      assert (ma_ideal_state_inv sx)

let ma_ideal_state_inv_preserved_recv3
      (s: ideal_proto_state) (session: session_id)
      (party peer: participant_id) (s': ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_state_inv s /\
        ma_sim_receive_message3_protocol_transition s session party peer s')
      (ensures ma_ideal_state_inv s')
  = eliminate exists (responder_key: priv_key).
      ma_sim_receive_message3_enabled s session party peer responder_key /\
      s' == ma_sim_receive_message3_state s session party peer responder_key
    returns ma_ideal_state_inv s'
    with _h.
      let sx = ma_sim_receive_message3_state s session party peer responder_key in
      // recv3 leaves the request map untouched; transfer I2 explicitly.
      ma_sim_receive_message3_state_preserves_requests s session party peer responder_key;
      _internal_requests_eq_session_requests_eq s sx;
      _requests_eq_preserves_one_request_per_party s sx;
      assert (ma_ideal_inv_one_request_per_party sx);
      // recv3 leaves the recorded requests and the ideal->sim channel untouched,
      // so the H_auth_* conjuncts transfer directly.
      assert (ma_ideal_state_inv sx)

let ma_ideal_state_inv_preserved_deliver
      (s: ideal_proto_state) (session: session_id)
      (party peer: participant_id) (r: role) (output_t: term) (s': ideal_proto_state)
    : Lemma
      (requires
        ma_ideal_state_inv s /\
        ma_ideal_deliver_protocol_transition s session party peer r output_t s')
      (ensures ma_ideal_state_inv s')
  = let sx = ma_ideal_deliver_state s session party peer in
    // deliver leaves the request map untouched; transfer I2 explicitly.
    ma_ideal_deliver_state_session_requests_eq s session party peer session;
    assert (forall (i: session_id). ma_session_requests sx i == ma_session_requests s i);
    _requests_eq_preserves_one_request_per_party s sx;
    assert (ma_ideal_inv_one_request_per_party sx);
    // deliver leaves the recorded requests and the ideal->sim channel untouched,
    // so the H_auth_* conjuncts transfer directly.
    assert (ma_ideal_state_inv sx)

#pop-options

/// --- Dispatcher: case-split on the transition label ---
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let ma_ideal_state_inv_preserved s l s' =
  match l with
  | Protocol.Observable NetSend sent_t lid ->
    (match lid.role with
     | Initiator ->
       assert (
         ma_sim_send_message1_protocol_transition s lid.session lid.party lid.peer sent_t s' \/
         ma_sim_send_message3_protocol_transition s lid.session lid.party lid.peer sent_t s');
       eliminate
         ma_sim_send_message1_protocol_transition s lid.session lid.party lid.peer sent_t s' \/
         ma_sim_send_message3_protocol_transition s lid.session lid.party lid.peer sent_t s'
       returns ma_ideal_state_inv s'
       with _h1.
         ma_ideal_state_inv_preserved_send1 s lid.session lid.party lid.peer sent_t s'
       and _h3.
         ma_ideal_state_inv_preserved_send3 s lid.session lid.party lid.peer sent_t s'
     | Responder ->
       ma_ideal_state_inv_preserved_send2 s lid.session lid.party lid.peer sent_t s')
  | Protocol.Observable IoSend output_t lid ->
    ma_ideal_state_inv_preserved_deliver s lid.session lid.party lid.peer lid.role output_t s'
  | Protocol.Internal lid ->
    assert (
      ma_ideal_initiate_protocol_transition s lid.session lid.party lid.peer lid.role s' \/
      (match lid.role with
       | Responder ->
         ma_sim_receive_message3_protocol_transition s lid.session lid.party lid.peer s'
       | Initiator -> False));
    (match lid.role with
     | Initiator ->
       ma_ideal_state_inv_preserved_initiate s lid.session lid.party lid.peer lid.role s'
     | Responder ->
       eliminate
         ma_ideal_initiate_protocol_transition s lid.session lid.party lid.peer lid.role s' \/
         ma_sim_receive_message3_protocol_transition s lid.session lid.party lid.peer s'
       returns ma_ideal_state_inv s'
       with _hi.
         ma_ideal_state_inv_preserved_initiate s lid.session lid.party lid.peer lid.role s'
       and _hr.
         ma_ideal_state_inv_preserved_recv3 s lid.session lid.party lid.peer s')
#pop-options


/// ===========================================================================
/// Secrecy preservation building blocks
///
/// Knowledge only ever grows by appending the term emitted on an `Observable`
/// step.  That term is either a session ciphertext `Aenc (Pair (SessionId i) m
/// k)` whose encryption key `k` is a directory private key (the three NSL
/// sends), or the public authenticated term (the ideal deliver step).  In both
/// cases the symbolic adversary corollaries (`MA.Adversary`) reduce any new
/// derivation of a private key or nonce back to a derivation from the previous
/// knowledge, which the secrecy invariants of `s` already rule out.
/// ===========================================================================

/// Appending a session ciphertext whose plaintext has no private-key subterms
/// preserves private-key secrecy (C3).  Works for both honest and corrupt
/// encryption keys: the `no_private_key_subterms` condition on the
/// underapproximate derivable subterms of the ciphertext is sufficient.
private
let _send_ciphertext_preserves_key_secrecy
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (i: session_id)
      (m: term)
      (k: priv_key)
    : Lemma
      (requires
        ma_private_keys_not_derivable corrupt key_directory s /\
        no_private_key_subterms
          (derivable_subterms_underapproximate_keys s.know (Aenc (Pair (SessionId i) m) k)) /\
        s'.know == Seq.snoc s.know (Aenc (Pair (SessionId i) m) k))
      (ensures ma_private_keys_not_derivable corrupt key_directory s') =
  introduce
    forall (participant: participant_id) (k': priv_key) (d: adv.derivation).
      PartialMap.sel key_directory participant == Some k' /\
      not (Set.mem participant corrupt) ==>
      not (adv.derive d s'.know = Some (PrivKey k'))
  with
    introduce _ ==> _ with _hsel.
      if adv.derive d s'.know = Some (PrivKey k') then (
        derivable_from_observed_term_without_private_key_subterms
          s.know (Aenc (Pair (SessionId i) m) k) d (PrivKey k');
        derivable_subterms_underapproximate_keys_exact_with_no_privkeys
          s.know (Aenc (Pair (SessionId i) m) k);
        private_key_built_from_subterms_already_derivable
          s.know
          (derivable_subterms s.know (Aenc (Pair (SessionId i) m) k))
          k'
      )

/// A nonce that is fresh (not yet in `used_nonces`) is not derivable from the
/// current adversary knowledge.  The adversary cannot mint nonces, so every nonce
/// it can derive occurs syntactically in its knowledge
/// (`ma_derive_term_nonces_in_knowledge_nonces`), and the freshness invariant
/// bounds those nonces by `used_nonces`.
private
let _fresh_nonce_not_derivable
      (s: ideal_system_state)
      (n: nonce)
    : Lemma
      (requires
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ~(Set.mem n s.internal.used_nonces))
      (ensures (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce n)))) =
  introduce forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce n))
  with
    if adv.derive d s.know = Some (Nonce n) then
      (assert (adv.derive d s.know == derive d s.know) by (FStar.Tactics.trefl ());
       ma_derive_term_nonces_in_knowledge_nonces s.know d (Nonce n);
       // ma_term_nonces (Nonce n) = {n} ⊆ ma_knowledge_nonces s.know ⊆ used_nonces
       FStar.Set.Properties.set_subset_transitive
         (ma_term_nonces (Nonce n)) (ma_knowledge_nonces s.know) s.internal.used_nonces;
       assert (Set.mem n (ma_term_nonces (Nonce n))))

/// Appending a session ciphertext whose key is unguessable preserves
/// underivability of a *single* nonce `n`: if the adversary could not derive
/// `Nonce n` before, it still cannot after observing the ciphertext (the key is
/// secret, so the encrypted nonce stays hidden).
private
let _send_ciphertext_preserves_nonce_not_derivable
      (s s': ideal_system_state)
      (i: session_id)
      (m: term)
      (k: priv_key)
      (n: nonce)
    : Lemma
      (requires
        (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce n))) /\
        ~(derivable s.know (PrivKey k)) /\
        s'.know == Seq.snoc s.know (Aenc (Pair (SessionId i) m) k))
      (ensures (forall (d: adv.derivation). not (adv.derive d s'.know = Some (Nonce n)))) =
  introduce forall (d: adv.derivation). not (adv.derive d s'.know = Some (Nonce n))
  with
    if adv.derive d s'.know = Some (Nonce n) then
      nonces_learned_from_session_ciphertext_already_derivable s.know i m k n d

/// Appending the public authenticated output term preserves private-key secrecy.
private
let _deliver_preserves_key_secrecy
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (i: session_id)
      (party peer: participant_id)
    : Lemma
      (requires
        ma_private_keys_not_derivable corrupt key_directory s /\
        s'.know == Seq.snoc s.know (ma_authenticated_term i party peer))
      (ensures ma_private_keys_not_derivable corrupt key_directory s') =
  introduce
    forall (participant: participant_id) (k': priv_key) (d: adv.derivation).
      PartialMap.sel key_directory participant == Some k' /\
      not (Set.mem participant corrupt) ==>
      not (adv.derive d s'.know = Some (PrivKey k'))
  with
    introduce _ ==> _ with _hsel.
      if adv.derive d s'.know = Some (PrivKey k') then
        private_keys_learned_from_public_output_already_derivable
          s.know i party peer k' d

/// Appending the public authenticated output term preserves underivability of a
/// single nonce `n` (the output carries no nonces, so it cannot help the
/// adversary derive any).
private
let _deliver_preserves_nonce_not_derivable
      (s s': ideal_system_state)
      (i: session_id)
      (party peer: participant_id)
      (n: nonce)
    : Lemma
      (requires
        (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce n))) /\
        s'.know == Seq.snoc s.know (ma_authenticated_term i party peer))
      (ensures (forall (d: adv.derivation). not (adv.derive d s'.know = Some (Nonce n)))) =
  introduce forall (d: adv.derivation). not (adv.derive d s'.know = Some (Nonce n))
  with
    if adv.derive d s'.know = Some (Nonce n) then
      nonces_learned_from_public_output_already_derivable s.know i party peer n d

/// A private key registered in the directory for a non-corrupt participant cannot
/// be derived (C3 specialized): if `derive d s.know` ever returned `PrivKey k`,
/// that would witness `derivable s.know (PrivKey k)`, which C3 forbids for every
/// non-corrupt directory key.
private
let _directory_key_not_derivable
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
      (participant: participant_id)
      (k: priv_key)
    : Lemma
      (requires
        ma_private_keys_not_derivable corrupt key_directory s /\
        PartialMap.sel key_directory participant == Some k /\
        not (Set.mem participant corrupt))
      (ensures ~(derivable s.know (PrivKey k))) =
  let aux () : Lemma (requires derivable s.know (PrivKey k)) (ensures False) =
    assert (exists (d: adv.derivation). adv.derive d s.know = Some (PrivKey k));
    eliminate exists (d: adv.derivation). adv.derive d s.know = Some (PrivKey k)
    returns False
    with _hd. ()
  in
  FStar.Classical.move_requires aux ()

/// ---------------------------------------------------------------------------
/// Directory-key extraction from the (unfold) `enabled` predicates.

private
let _enabled1_dir
      (s: ideal_system_state) (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_sim_send_message1_enabled
          (s2p_state s) session initiator responder initiator_nonce responder_pubkey)
      (ensures
        PartialMap.sel s.internal.key_directory responder ==
        Some (PubKey?.priv responder_pubkey)) =
  ()

private
let _enabled2_dir
      (s: ideal_system_state) (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : Lemma
      (requires
        ma_sim_send_message2_enabled
          (s2p_state s) session responder initiator initiator_nonce responder_nonce
          responder_key initiator_pubkey)
      (ensures
        PartialMap.sel s.internal.key_directory initiator ==
        Some (PubKey?.priv initiator_pubkey)) =
  ()

private
let _enabled3_dir
      (s: ideal_system_state) (session: session_id)
      (initiator responder: participant_id)
      (responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_sim_send_message3_enabled
          (s2p_state s) session initiator responder responder_nonce initiator_key responder_pubkey)
      (ensures
        Some? (ma_sim_initiator_session_state (s2p_state s) initiator session) /\
        PartialMap.sel s.internal.key_directory responder ==
        Some (PubKey?.priv responder_pubkey)) =
  ()

/// ---------------------------------------------------------------------------
/// Per-transition secrecy wrappers.
///
/// Each emitting transition produces a session ciphertext (or, for `deliver`,
/// the public authenticated term).  These wrappers eliminate the existential
/// witnesses of the protocol transition, expose the encryption key as a
/// directory key (using `ma_key_directory_matches`), discharge that the key is
/// unguessable (using `ma_private_keys_not_derivable`), and conclude via the
/// generic secrecy building blocks above.
/// ---------------------------------------------------------------------------

/// Generic stored-nonce-secrecy preservation across a step that appends a session
/// ciphertext `Aenc (Pair (SessionId i) m) k`.  The key `k` need not be secret;
/// the callers supply underivability from `s.know` only for honest sessions.
/// Corrupt sessions satisfy the predicate vacuously (their antecedents are false).
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private
let _ciphertext_preserves_valid_nonces
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (i: session_id) (m: term) (k: priv_key)
    : Lemma
      (requires
        ~(derivable s.know (PrivKey k)) /\
        s'.know == Seq.snoc s.know (Aenc (Pair (SessionId i) m) k) /\
        (forall (sess: session_id) (p q: participant_id) (nn: nonce).
           matches_initiator_state s' sess p q nn /\
           not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
           (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))) /\
        (forall (sess: session_id) (p q: participant_id) (nn: nonce).
           matches_responder_state s' sess p q nn /\
           not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
           (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))))
      (ensures
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  introduce forall (session: session_id) (initiator responder: participant_id)
                   (initiator_nonce: nonce) (d: adv.derivation).
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       (ist.initiator == initiator /\ ist.responder == responder /\
        ist.initiator_nonce == initiator_nonce /\
        not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce initiator_nonce))
     | None -> True)
  with
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       introduce
         (ist.initiator == initiator /\ ist.responder == responder /\
          ist.initiator_nonce == initiator_nonce /\
          not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce initiator_nonce))
       with _heq.
         (assert (matches_initiator_state s' session initiator responder initiator_nonce);
          _send_ciphertext_preserves_nonce_not_derivable s s' i m k initiator_nonce)
     | None -> ());
  introduce forall (session: session_id) (responder initiator: participant_id)
                   (responder_nonce: nonce) (d: adv.derivation).
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       (rst.responder == responder /\ rst.initiator == initiator /\
        rst.responder_nonce == responder_nonce /\
        not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce responder_nonce))
     | None -> True)
  with
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       introduce
         (rst.responder == responder /\ rst.initiator == initiator /\
          rst.responder_nonce == responder_nonce /\
          not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce responder_nonce))
       with _heq.
         (assert (matches_responder_state s' session responder initiator responder_nonce);
          _send_ciphertext_preserves_nonce_not_derivable s s' i m k responder_nonce)
     | None -> ())
#pop-options

/// Deliver analogue of `_ciphertext_preserves_valid_nonces`: the appended public
/// authenticated term carries no nonces, so stored-nonce underivability is carried
/// across by `_deliver_preserves_nonce_not_derivable`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private
let _deliver_preserves_valid_nonces
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (i: session_id) (party peer: participant_id)
    : Lemma
      (requires
        s'.know == Seq.snoc s.know (ma_authenticated_term i party peer) /\
        (forall (sess: session_id) (p q: participant_id) (nn: nonce).
           matches_initiator_state s' sess p q nn /\
           not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
           (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))) /\
        (forall (sess: session_id) (p q: participant_id) (nn: nonce).
           matches_responder_state s' sess p q nn /\
           not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
           (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))))
      (ensures
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  introduce forall (session: session_id) (initiator responder: participant_id)
                   (initiator_nonce: nonce) (d: adv.derivation).
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       (ist.initiator == initiator /\ ist.responder == responder /\
        ist.initiator_nonce == initiator_nonce /\
        not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce initiator_nonce))
     | None -> True)
  with
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       introduce
         (ist.initiator == initiator /\ ist.responder == responder /\
          ist.initiator_nonce == initiator_nonce /\
          not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce initiator_nonce))
       with _heq.
         (assert (matches_initiator_state s' session initiator responder initiator_nonce);
          _deliver_preserves_nonce_not_derivable s s' i party peer initiator_nonce)
     | None -> ());
  introduce forall (session: session_id) (responder initiator: participant_id)
                   (responder_nonce: nonce) (d: adv.derivation).
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       (rst.responder == responder /\ rst.initiator == initiator /\
        rst.responder_nonce == responder_nonce /\
        not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce responder_nonce))
     | None -> True)
  with
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       introduce
         (rst.responder == responder /\ rst.initiator == initiator /\
          rst.responder_nonce == responder_nonce /\
          not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce responder_nonce))
       with _heq.
         (assert (matches_responder_state s' session responder initiator responder_nonce);
          _deliver_preserves_nonce_not_derivable s s' i party peer responder_nonce)
     | None -> ())
#pop-options

/// Helper lemma: the initiator nonce of any stored initiator session in `s` is
/// in `s.internal.used_nonces`, given `ma_ideal_used_nonces_invariant s`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private
let _initiator_nonce_in_used_nonces
      (s: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (n: nonce)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        matches_initiator_state s session initiator responder n)
      (ensures Set.mem n s.internal.used_nonces) =
  unfold_ma_sim_initiator_session_state (s2p_state s) initiator session
#pop-options

/// Helper lemma: the responder nonce of any stored responder session in `s` is
/// in `s.internal.used_nonces`, given `ma_ideal_used_nonces_invariant s`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private
let _responder_nonce_in_used_nonces
      (s: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (n: nonce)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        matches_responder_state s session responder initiator n)
      (ensures Set.mem n s.internal.used_nonces) =
  unfold_ma_sim_responder_session_state (s2p_state s) responder session
#pop-options

/// Helper lemma: the nonce `n'` from an unchanged initiator session is not a
/// member of the underapproximate derivable subterms of the Message1 ciphertext
/// `Aenc (Pair (SessionId i) (Pair (Nonce n) (ParticipantId party))) k`, provided
/// `n' ≠ n`.  Requires fuel 4 to unfold `derivable_subterms_underapproximate_keys`
/// recursively through Aenc → Pair → Pair → Nonce.
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
private
let _send1_nonce_not_in_ciphertext_subterms
      (know: knowledge term)
      (i: session_id)
      (party: participant_id)
      (n n': nonce)
      (k: priv_key)
    : Lemma
      (requires n' <> n)
      (ensures ~(Set.mem (Nonce n')
        (derivable_subterms_underapproximate_keys know
          (Aenc (Pair (SessionId i) (Pair (Nonce n) (ParticipantId party))) k))))
    = ()
#pop-options

/// Helper lemma: if a nonce `old_n` is not derivable from `know`, and `old_n ≠ new_n`,
/// then it is also not derivable from `Seq.snoc know (Aenc (Pair (SessionId i) (Pair (Nonce new_n) (ParticipantId party))) k)`.
/// This handles the case where the encryption key k may be derivable (corrupt key owner).
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private
let _send1_nonce_not_newly_derivable_from_ciphertext
      (know: knowledge term)
      (i: session_id)
      (party: participant_id)
      (new_n old_n: nonce)
      (k: priv_key)
      (d: adv.derivation)
    : Lemma
      (requires
        old_n <> new_n /\
        no_private_key_subterms (derivable_subterms_underapproximate_keys know
          (Aenc (Pair (SessionId i) (Pair (Nonce new_n) (ParticipantId party))) k)) /\
        (forall (d': adv.derivation). not (adv.derive d' know = Some (Nonce old_n))) /\
        adv.derive d (Seq.snoc know
          (Aenc (Pair (SessionId i) (Pair (Nonce new_n) (ParticipantId party))) k)) = Some (Nonce old_n))
      (ensures False) =
  let sent_term = Aenc (Pair (SessionId i) (Pair (Nonce new_n) (ParticipantId party))) k in
  derivable_from_observed_term_without_private_key_subterms know sent_term d (Nonce old_n);
  derivable_subterms_underapproximate_keys_exact_with_no_privkeys know sent_term;
  _send1_nonce_not_in_ciphertext_subterms know i party new_n old_n k;
  built_from_subterms_nonce_derivable know (derivable_subterms know sent_term) old_n
#pop-options

/// Corrupt-peer Message1 case (initiator side): the freshly-stored initiator
/// nonce belongs to a session whose responder is the corrupt `peer`, so its
/// stored-nonce-secrecy clause is vacuous; every other initiator session is
/// unchanged from `s`, and its nonce (distinct from the fresh `initiator_nonce`)
/// stays underivable across the appended Message1 ciphertext.  Extracted as a
/// named helper so the manual reconstruction of
/// `ma_valid_initiator_nonces_not_derivable` (which the honest branch instead
/// delegates to `_ciphertext_preserves_valid_nonces`) lives in one place with a
/// type-checked contract.
#push-options "--fuel 4 --ifuel 2 --z3rlimit 100"
private
let _send1_corrupt_valid_initiator_nonces
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (sess0: session_id)
      (party peer: participant_id)
      (initiator_nonce: nonce)
      (k: priv_key)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        Set.mem peer corrupt /\
        not (Set.mem initiator_nonce s.internal.used_nonces) /\
        no_private_key_subterms (derivable_subterms_underapproximate_keys s.know
          (Aenc (Pair (SessionId sess0) (Pair (Nonce initiator_nonce) (ParticipantId party))) k)) /\
        s2p_state s' == ma_sim_send_message1_state (s2p_state s) sess0 party peer initiator_nonce /\
        s'.know == Seq.snoc s.know
          (Aenc (Pair (SessionId sess0) (Pair (Nonce initiator_nonce) (ParticipantId party))) k))
      (ensures ma_valid_initiator_nonces_not_derivable corrupt s') =
  introduce forall (session: session_id) (initiator responder: participant_id)
                   (initiator_nonce': nonce) (d: adv.derivation).
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       (ist.initiator == initiator /\ ist.responder == responder /\
        ist.initiator_nonce == initiator_nonce' /\
        not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce initiator_nonce'))
     | None -> True)
  with
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       introduce
         (ist.initiator == initiator /\ ist.responder == responder /\
          ist.initiator_nonce == initiator_nonce' /\
          not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce initiator_nonce'))
       with _heq.
         (_send1_get_updated (s2p_state s) sess0 party peer initiator_nonce initiator session;
          unfold_ma_sim_initiator_session_state (s2p_state s') initiator session;
          if initiator = party && session = sess0 then
            // New session: responder = peer which is corrupt → antecedent false.
            assert (responder == peer)
          else (
            // Unchanged session (both parties honest): its nonce was underivable
            // from s.know and differs from the fresh `initiator_nonce`, so it
            // stays underivable across the appended Message1 ciphertext.
            participant_session_eq_implies_initiator_session_eq
              (s2p_state s) initiator session (s2p_state s') initiator session;
            assert (matches_initiator_state s session initiator responder initiator_nonce');
            _initiator_nonce_in_used_nonces s session initiator responder initiator_nonce';
            assert (initiator_nonce' <> initiator_nonce);
            if adv.derive d s'.know = Some (Nonce initiator_nonce') then
              _send1_nonce_not_newly_derivable_from_ciphertext
                s.know sess0 party initiator_nonce initiator_nonce' k d
          ))
     | None -> ())
#pop-options

/// Corrupt-peer Message1 case (responder side): `send1` creates no responder
/// session, so every stored responder session is unchanged from `s`; its nonce
/// differs from the fresh `initiator_nonce` and stays underivable across the
/// appended Message1 ciphertext.  Extracted alongside
/// `_send1_corrupt_valid_initiator_nonces` so the manual reconstruction of
/// `ma_valid_responder_nonces_not_derivable` has a single type-checked home.
#push-options "--fuel 4 --ifuel 2 --z3rlimit 100"
private
let _send1_corrupt_valid_responder_nonces
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (sess0: session_id)
      (party peer: participant_id)
      (initiator_nonce: nonce)
      (k: priv_key)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        not (Set.mem initiator_nonce s.internal.used_nonces) /\
        no_private_key_subterms (derivable_subterms_underapproximate_keys s.know
          (Aenc (Pair (SessionId sess0) (Pair (Nonce initiator_nonce) (ParticipantId party))) k)) /\
        s2p_state s' == ma_sim_send_message1_state (s2p_state s) sess0 party peer initiator_nonce /\
        s'.know == Seq.snoc s.know
          (Aenc (Pair (SessionId sess0) (Pair (Nonce initiator_nonce) (ParticipantId party))) k))
      (ensures ma_valid_responder_nonces_not_derivable corrupt s') =
  introduce forall (session: session_id) (responder initiator: participant_id)
                   (responder_nonce: nonce) (d: adv.derivation).
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       (rst.responder == responder /\ rst.initiator == initiator /\
        rst.responder_nonce == responder_nonce /\
        not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce responder_nonce))
     | None -> True)
  with
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       introduce
         (rst.responder == responder /\ rst.initiator == initiator /\
          rst.responder_nonce == responder_nonce /\
          not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce responder_nonce))
       with _heq.
         (_send1_get_updated (s2p_state s) sess0 party peer initiator_nonce responder session;
          unfold_ma_sim_responder_session_state (s2p_state s') responder session;
          participant_session_eq_implies_responder_session_eq
            (s2p_state s) responder session (s2p_state s') responder session;
          assert (matches_responder_state s session responder initiator responder_nonce);
          _responder_nonce_in_used_nonces s session responder initiator responder_nonce;
          assert (responder_nonce <> initiator_nonce);
          if adv.derive d s'.know = Some (Nonce responder_nonce) then
            _send1_nonce_not_newly_derivable_from_ciphertext
              s.know sess0 party initiator_nonce responder_nonce k d)
     | None -> ())
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
private
let _obs_send1_secrecy
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_corrupt_set_matches corrupt s /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_ideal_used_nonces_invariant s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_private_keys_not_derivable corrupt key_directory s' /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns
    ma_private_keys_not_derivable corrupt key_directory s' /\
    ma_valid_initiator_nonces_not_derivable corrupt s' /\
    ma_valid_responder_nonces_not_derivable corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     let m = Pair (Nonce initiator_nonce) (ParticipantId lid.party) in
     assert (ma_sim_send_message1_enabled
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey);
     _enabled1_dir s lid.session lid.party lid.peer initiator_nonce responder_pubkey;
     assert (PartialMap.sel s.internal.key_directory lid.peer == Some k);
     assert (s.internal.key_directory == key_directory);
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     assert (s'.know == Seq.snoc s.know (Aenc (Pair (SessionId lid.session) m) k));
     // Message1 plaintext m = Pair (Nonce ni) (ParticipantId A) has no PrivKey
     // subterms, so the underapprox derivable subterms of the ciphertext are
     // key-free in both honest and corrupt key scenarios.
     assert (no_private_key_subterms
       (derivable_subterms_underapproximate_keys s.know (Aenc (Pair (SessionId lid.session) m) k)));
     _send_ciphertext_preserves_key_secrecy corrupt key_directory s s' lid.session m k;
     // The freshly created initiator session of `lid.party` stores the fresh
     // `initiator_nonce`; every other stored session is unchanged from `s`.
     assert (not (Set.mem initiator_nonce s.internal.used_nonces));
     // For the new session, if lid.peer is honest use freshness; if lid.peer is
     // corrupt nonce secrecy is vacuous (antecedent has not corrupt lid.peer).
     // For unchanged sessions, the nonce secrecy from the IH still applies.
     // Either way, key secrecy (~derivable (PrivKey k)) holds when lid.peer is
     // honest (needed by _ciphertext_preserves_valid_nonces).
     // If lid.peer is corrupt, the nonce of the NEW session is vacuous, and
     // unchanged sessions' nonces are still undeducible (same IH applies since
     // the new ciphertext has no PrivKey plaintext subterms).
     if not (Set.mem lid.peer corrupt) then (
       _directory_key_not_derivable corrupt key_directory s lid.peer k;
       // Initiator stored nonces of `s'` are underivable from `s.know`.
       introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
         matches_initiator_state s' sess p q nn /\
         not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
         (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
       with introduce _ ==> _ with _hm.
         (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce p sess;
          unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
          if p = lid.party && sess = lid.session then
            (assert (nn == initiator_nonce);
             _fresh_nonce_not_derivable s initiator_nonce)
          else
            (participant_session_eq_implies_initiator_session_eq
               (s2p_state s) p sess (s2p_state s') p sess;
             assert (matches_initiator_state s sess p q nn)));
       // Responder stored sessions of `s'` are unchanged from `s`.
       introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
         matches_responder_state s' sess p q nn /\
         not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
         (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
       with introduce _ ==> _ with _hm.
         (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce p sess;
          unfold_ma_sim_responder_session_state (s2p_state s') p sess;
          if p = lid.party && sess = lid.session then
            ()
          else
            (participant_session_eq_implies_responder_session_eq
               (s2p_state s) p sess (s2p_state s') p sess;
             assert (matches_responder_state s sess p q nn)));
       _ciphertext_preserves_valid_nonces corrupt s s' lid.session m k
     ) else (
       // lid.peer is corrupt, so `_ciphertext_preserves_valid_nonces` (which needs
       // ~(derivable (PrivKey k))) does not apply.  The new session's initiator
       // nonce is vacuous (its responder is the corrupt peer) and every other
       // session is unchanged; the two helpers reconstruct the stored-nonce
       // secrecy clauses for `s'`.
       _send1_corrupt_valid_initiator_nonces corrupt s s' lid.session lid.party lid.peer initiator_nonce k;
       _send1_corrupt_valid_responder_nonces corrupt s s' lid.session lid.party lid.peer initiator_nonce k
     )
    )
#pop-options

/// Helper lemma: neither nonce `ni'` nor `nr'` from unchanged sessions is a
/// member of the underapproximate derivable subterms of the Message2 ciphertext
/// `Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId p)))) k`,
/// provided `n' ∉ {ni, nr}`.  Requires fuel 5 to unfold
/// `derivable_subterms_underapproximate_keys` through Aenc → Pair → Pair → Pair → Nonce.
#push-options "--fuel 5 --ifuel 2 --z3rlimit 40"
private
let _send2_nonce_not_in_ciphertext_subterms
      (know: knowledge term)
      (i: session_id)
      (party: participant_id)
      (ni nr n': nonce)
      (k: priv_key)
    : Lemma
      (requires n' <> ni /\ n' <> nr)
      (ensures ~(Set.mem (Nonce n')
        (derivable_subterms_underapproximate_keys know
          (Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId party)))) k))))
    = ()
#pop-options

/// Helper lemma: the nonce `n'` from an unchanged session is not a member of
/// the underapproximate derivable subterms of the Message3 ciphertext
/// `Aenc (Pair (SessionId i) (Nonce nr)) k`, provided `n' ≠ nr`.  Requires
/// fuel 3 to unfold `derivable_subterms_underapproximate_keys` through
/// Aenc → Pair → Nonce.
#push-options "--fuel 3 --ifuel 2 --z3rlimit 40"
private
let _send3_nonce_not_in_ciphertext_subterms
      (know: knowledge term)
      (i: session_id)
      (nr n': nonce)
      (k: priv_key)
    : Lemma
      (requires n' <> nr)
      (ensures ~(Set.mem (Nonce n')
        (derivable_subterms_underapproximate_keys know
          (Aenc (Pair (SessionId i) (Nonce nr)) k))))
    = ()
#pop-options

/// Send2 analogue of `_send1_nonce_not_newly_derivable_from_ciphertext`: a nonce
/// `n'` that is undeducible from `know` and differs from both nonces of the
/// emitted Message2 ciphertext stays undeducible after the ciphertext is appended
/// — even when the encryption key `k` is derivable (corrupt key owner).
#push-options "--fuel 5 --ifuel 2 --z3rlimit 80"
private
let _send2_nonce_not_newly_derivable_from_ciphertext
      (know: knowledge term)
      (i: session_id)
      (party: participant_id)
      (ni nr n': nonce)
      (k: priv_key)
      (d: adv.derivation)
    : Lemma
      (requires
        n' <> ni /\ n' <> nr /\
        no_private_key_subterms (derivable_subterms_underapproximate_keys know
          (Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId party)))) k)) /\
        (forall (d': adv.derivation). not (adv.derive d' know = Some (Nonce n'))) /\
        adv.derive d (Seq.snoc know
          (Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId party)))) k))
          = Some (Nonce n'))
      (ensures False) =
  let sent_term =
    Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId party)))) k in
  derivable_from_observed_term_without_private_key_subterms know sent_term d (Nonce n');
  derivable_subterms_underapproximate_keys_exact_with_no_privkeys know sent_term;
  _send2_nonce_not_in_ciphertext_subterms know i party ni nr n' k;
  built_from_subterms_nonce_derivable know (derivable_subterms know sent_term) n'
#pop-options

/// Send3 analogue of `_send1_nonce_not_newly_derivable_from_ciphertext`.
#push-options "--fuel 3 --ifuel 2 --z3rlimit 80"
private
let _send3_nonce_not_newly_derivable_from_ciphertext
      (know: knowledge term)
      (i: session_id)
      (nr n': nonce)
      (k: priv_key)
      (d: adv.derivation)
    : Lemma
      (requires
        n' <> nr /\
        no_private_key_subterms (derivable_subterms_underapproximate_keys know
          (Aenc (Pair (SessionId i) (Nonce nr)) k)) /\
        (forall (d': adv.derivation). not (adv.derive d' know = Some (Nonce n'))) /\
        adv.derive d (Seq.snoc know (Aenc (Pair (SessionId i) (Nonce nr)) k)) = Some (Nonce n'))
      (ensures False) =
  let sent_term = Aenc (Pair (SessionId i) (Nonce nr)) k in
  derivable_from_observed_term_without_private_key_subterms know sent_term d (Nonce n');
  derivable_subterms_underapproximate_keys_exact_with_no_privkeys know sent_term;
  _send3_nonce_not_in_ciphertext_subterms know i nr n' k;
  built_from_subterms_nonce_derivable know (derivable_subterms know sent_term) n'
#pop-options

/// Introduce `ma_is_honest_session_nonce` from a concrete both-honest session.
private
let _honest_session_nonce_intro
      (corrupt: Set.set participant_id) (s: ideal_system_state)
      (sess: session_id) (a b: participant_id) (m: nonce)
    : Lemma
      (requires
        (matches_initiator_state s sess a b m \/ matches_responder_state s sess a b m) /\
        not (Set.mem a corrupt) /\ not (Set.mem b corrupt))
      (ensures ma_is_honest_session_nonce corrupt s m) = ()

/// Targeted instantiations of the knowledge-structure invariants (their SMT
/// triggers do not pin down the index / nonce witnesses on their own).
private
let _honest_msg1_names
      (corrupt: Set.set participant_id) (s: ideal_system_state)
      (idx: nat) (sess: session_id) (m: nonce) (p: participant_id) (k: priv_key)
    : Lemma
      (requires
        ma_honest_msg1_names_non_corrupt corrupt s /\
        idx < Seq.length s.know /\
        aenc_subterm
          (Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) k)
          (Seq.index s.know idx) /\
        ma_is_honest_session_nonce corrupt s m)
      (ensures not (Set.mem p corrupt)) = ()

private
let _honest_msg2_names
      (corrupt: Set.set participant_id) (s: ideal_system_state)
      (idx: nat) (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key)
    : Lemma
      (requires
        ma_honest_msg2_names_non_corrupt corrupt s /\
        idx < Seq.length s.know /\
        aenc_subterm
          (Aenc (Pair (SessionId sess)
                  (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k)
          (Seq.index s.know idx) /\
        ma_is_honest_session_nonce corrupt s mr)
      (ensures not (Set.mem p corrupt)) = ()

private
let _honest_msg2_key
      (corrupt: Set.set participant_id) (s: ideal_system_state)
      (idx: nat) (sess: session_id) (mi mr: nonce) (p initiator: participant_id) (k: priv_key)
    : Lemma
      (requires
        ma_honest_msg2_key_matches_initiator corrupt s /\
        idx < Seq.length s.know /\
        aenc_subterm
          (Aenc (Pair (SessionId sess)
                  (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k)
          (Seq.index s.know idx) /\
        ma_is_honest_session_nonce corrupt s mr /\
        matches_responder_state s sess p initiator mr)
      (ensures PartialMap.sel s.internal.key_directory initiator == Some k) = ()

private
let _honest_carrier_shallow_at
      (corrupt: Set.set participant_id) (s: ideal_system_state) (idx: nat) (m: nonce)
    : Lemma
      (requires
        ma_honest_carrier_shallow corrupt s /\
        idx < Seq.length s.know /\
        Set.mem m (ma_term_nonces (Seq.index s.know idx)) /\
        ma_is_honest_session_nonce corrupt s m)
      (ensures shallow_aenc (Seq.index s.know idx)) = ()

/// Received-nonce provenance for the corrupt-peer Message2 emission.  The
/// `initiator_nonce` echoed into the emitted Message2 came from a received
/// Message1 (in `s.inputs`) attributed to the corrupt `peer`.  If it coincided
/// with an honest session's stored nonce `n'`, then — since `n'` is unguessable —
/// that Message1 ciphertext could only have been *observed* (the adversary cannot
/// re-encrypt it), so it occurs in `s.know`; C_msg1 then forces its named
/// initiator to be non-corrupt, contradicting that it names the corrupt `peer`.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 300"
private
let _send2_received_nonce_neq_honest
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
      (i: session_id)
      (peer party: participant_id)
      (ni: nonce)
      (rk: priv_key)
      (sess: session_id) (a b: participant_id) (n': nonce)
    : Lemma
      (requires
        ma_ideal_inputs_derivable s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        Set.mem peer corrupt /\
        Bag.mem (ma_nsl_message1_network_term i peer party ni (PubKey rk)) s.inputs /\
        (matches_initiator_state s sess a b n' \/ matches_responder_state s sess a b n') /\
        not (Set.mem a corrupt) /\ not (Set.mem b corrupt))
      (ensures n' <> ni) =
  let plaintext1 = Pair (SessionId i) (Pair (Nonce ni) (ParticipantId peer)) in
  let msg1 = Aenc plaintext1 rk in
  let net = ma_nsl_message1_network_term i peer party ni (PubKey rk) in
  assert (net == Pair (Data (data_of_string "NetInput")) msg1);
  assert (derivable s.know net);
  derivable_pair_right s.know (Data (data_of_string "NetInput")) msg1;
  assert (derivable s.know msg1);
  let contra () : Lemma (requires n' = ni) (ensures False) =
    let not_deriv () : Lemma (requires derivable s.know (Nonce ni)) (ensures False) =
      eliminate exists (dn: adv.derivation). derive dn s.know = Some (Nonce ni)
      returns False
      with _hdn. (assert (adv.derive dn s.know == derive dn s.know) by (FStar.Tactics.trefl ()))
    in
    FStar.Classical.move_requires not_deriv ();
    let pt_extract () : Lemma (requires derivable s.know plaintext1) (ensures False) =
      derivable_pair_right s.know (SessionId i) (Pair (Nonce ni) (ParticipantId peer));
      derivable_pair_left s.know (Nonce ni) (ParticipantId peer)
    in
    FStar.Classical.move_requires pt_extract ();
    assert (~(derivable s.know plaintext1));
    // ni = n' is a protected (both-honest) session nonce.
    _honest_session_nonce_intro corrupt s sess a b n';
    assert (ma_is_honest_session_nonce corrupt s ni);
    eliminate exists (d0: adv.derivation). adv.derive d0 s.know = Some msg1
    returns False
    with _hd0.
      (assert (adv.derive d0 s.know == derive d0 s.know) by (FStar.Tactics.trefl ());
       aenc_subterm_in_derived_implies_observed s.know plaintext1 rk msg1 d0;
       eliminate exists (idx: nat).
         idx < Seq.length s.know /\ aenc_subterm msg1 (Seq.index s.know idx)
       returns False
       with _hidx.
         (// C_msg1: the observed Message1 carries the protected nonce ni, so its
          // named initiator `peer` is non-corrupt — contradicting `peer` corrupt.
          _honest_msg1_names corrupt s idx i ni peer rk))
  in
  FStar.Classical.move_requires contra ()
#pop-options

/// Received-nonce provenance for the corrupt-peer Message3 emission.  Symmetric to
/// `_send2_received_nonce_neq_honest` but for the `responder_nonce` echoed into the
/// emitted Message3, sourced from a received Message2 attributed to corrupt `peer`.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 300"
private
let _send3_received_nonce_neq_honest
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
      (i: session_id)
      (party peer: participant_id)
      (ini nr: nonce)
      (ik: priv_key)
      (sess: session_id) (a b: participant_id) (n': nonce)
    : Lemma
      (requires
        ma_ideal_inputs_derivable s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        Set.mem peer corrupt /\
        Bag.mem (ma_nsl_message2_network_term i party peer ini nr (PubKey ik)) s.inputs /\
        (matches_initiator_state s sess a b n' \/ matches_responder_state s sess a b n') /\
        not (Set.mem a corrupt) /\ not (Set.mem b corrupt))
      (ensures n' <> nr) =
  let plaintext2 = Pair (SessionId i) (Pair (Nonce ini) (Pair (Nonce nr) (ParticipantId peer))) in
  let msg2 = Aenc plaintext2 ik in
  let net = ma_nsl_message2_network_term i party peer ini nr (PubKey ik) in
  assert (net == Pair (Data (data_of_string "NetInput")) msg2);
  assert (derivable s.know net);
  derivable_pair_right s.know (Data (data_of_string "NetInput")) msg2;
  assert (derivable s.know msg2);
  let contra () : Lemma (requires n' = nr) (ensures False) =
    let not_deriv () : Lemma (requires derivable s.know (Nonce nr)) (ensures False) =
      eliminate exists (dn: adv.derivation). derive dn s.know = Some (Nonce nr)
      returns False
      with _hdn. (assert (adv.derive dn s.know == derive dn s.know) by (FStar.Tactics.trefl ()))
    in
    FStar.Classical.move_requires not_deriv ();
    let pt_extract () : Lemma (requires derivable s.know plaintext2) (ensures False) =
      derivable_pair_right s.know (SessionId i) (Pair (Nonce ini) (Pair (Nonce nr) (ParticipantId peer)));
      derivable_pair_right s.know (Nonce ini) (Pair (Nonce nr) (ParticipantId peer));
      derivable_pair_left s.know (Nonce nr) (ParticipantId peer)
    in
    FStar.Classical.move_requires pt_extract ();
    assert (~(derivable s.know plaintext2));
    // nr = n' is a protected (both-honest) session nonce.
    _honest_session_nonce_intro corrupt s sess a b n';
    assert (ma_is_honest_session_nonce corrupt s nr);
    eliminate exists (d0: adv.derivation). adv.derive d0 s.know = Some msg2
    returns False
    with _hd0.
      (assert (adv.derive d0 s.know == derive d0 s.know) by (FStar.Tactics.trefl ());
       aenc_subterm_in_derived_implies_observed s.know plaintext2 ik msg2 d0;
       eliminate exists (idx: nat).
         idx < Seq.length s.know /\ aenc_subterm msg2 (Seq.index s.know idx)
       returns False
       with _hidx.
         (// C_msg2: the observed Message2 carries the protected responder nonce nr,
          // so its named responder `peer` is non-corrupt — contradicting `peer`.
          _honest_msg2_names corrupt s idx i ini nr peer ik))
  in
  FStar.Classical.move_requires contra ()
#pop-options

#push-options "--fuel 5 --ifuel 2 --z3rlimit 200"
private
let _obs_send2_secrecy
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_corrupt_set_matches corrupt s /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_ideal_used_nonces_invariant s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_ideal_inputs_derivable s /\
        ma_session_nonces_unique s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_private_keys_not_derivable corrupt key_directory s' /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns
    ma_private_keys_not_derivable corrupt key_directory s' /\
    ma_valid_initiator_nonces_not_derivable corrupt s' /\
    ma_valid_responder_nonces_not_derivable corrupt s'
  with _he.
    (let k = PubKey?.priv initiator_pubkey in
     let m =
       Pair (Nonce initiator_nonce)
         (Pair (Nonce responder_nonce) (ParticipantId lid.party))
     in
     _enabled2_dir s lid.session lid.party lid.peer
       initiator_nonce responder_nonce responder_key initiator_pubkey;
     assert (PartialMap.sel s.internal.key_directory lid.peer == Some k);
     assert (s.internal.key_directory == key_directory);
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.know == Seq.snoc s.know (Aenc (Pair (SessionId lid.session) m) k));
     // Message2 plaintext has no PrivKey subterms.
     assert (no_private_key_subterms
       (derivable_subterms_underapproximate_keys s.know (Aenc (Pair (SessionId lid.session) m) k)));
     _send_ciphertext_preserves_key_secrecy corrupt key_directory s s' lid.session m k;
     assert (not (Set.mem responder_nonce s.internal.used_nonces));
     if not (Set.mem lid.peer corrupt) then (
       _directory_key_not_derivable corrupt key_directory s lid.peer k;
       introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
         matches_initiator_state s' sess p q nn /\
         not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
         (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
       with introduce _ ==> _ with _hm.
         (ma_sim_send_message2_state_get_updated_sim_participant_session_state
            (s2p_state s) lid.session lid.party lid.peer
            initiator_nonce responder_nonce responder_key p sess;
          unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
          if p = lid.party && sess = lid.session then
            ()
          else
            (participant_session_eq_implies_initiator_session_eq
               (s2p_state s) p sess (s2p_state s') p sess;
             assert (matches_initiator_state s sess p q nn)));
       introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
         matches_responder_state s' sess p q nn /\
         not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
         (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
       with introduce _ ==> _ with _hm.
         (ma_sim_send_message2_state_get_updated_sim_participant_session_state
            (s2p_state s) lid.session lid.party lid.peer
            initiator_nonce responder_nonce responder_key p sess;
          unfold_ma_sim_responder_session_state (s2p_state s') p sess;
          if p = lid.party && sess = lid.session then
            (assert (nn == responder_nonce);
             _fresh_nonce_not_derivable s responder_nonce)
          else
            (participant_session_eq_implies_responder_session_eq
               (s2p_state s) p sess (s2p_state s') p sess;
             assert (matches_responder_state s sess p q nn)));
       _ciphertext_preserves_valid_nonces corrupt s s' lid.session m k
     ) else (
       // lid.peer is corrupt: new session has corrupt initiator → vacuous nonce
       // secrecy. Unchanged sessions use the no_privkey subterms argument.
       introduce forall (session: session_id) (initiator responder: participant_id)
                        (initiator_nonce': nonce) (d: adv.derivation).
         (match ma_sim_initiator_session_state (s2p_state s') initiator session with
          | Some ist ->
            (ist.initiator == initiator /\ ist.responder == responder /\
             ist.initiator_nonce == initiator_nonce' /\
             not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
            not (adv.derive d s'.know = Some (Nonce initiator_nonce'))
          | None -> True)
       with
         (match ma_sim_initiator_session_state (s2p_state s') initiator session with
          | Some ist ->
            introduce
              (ist.initiator == initiator /\ ist.responder == responder /\
               ist.initiator_nonce == initiator_nonce' /\
               not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
              not (adv.derive d s'.know = Some (Nonce initiator_nonce'))
            with _heq.
              (ma_sim_send_message2_state_get_updated_sim_participant_session_state
                 (s2p_state s) lid.session lid.party lid.peer
                 initiator_nonce responder_nonce responder_key initiator session;
               unfold_ma_sim_initiator_session_state (s2p_state s') initiator session;
               // send2 creates a responder session, not initiator; unchanged
               participant_session_eq_implies_initiator_session_eq
                 (s2p_state s) initiator session (s2p_state s') initiator session;
               assert (matches_initiator_state s session initiator responder initiator_nonce');
               if adv.derive d s'.know = Some (Nonce initiator_nonce') then (
                 // initiator_nonce' (honest) differs from the fresh responder_nonce
                 // (freshness) and from the received initiator_nonce (provenance), so
                 // it is not exposed by the corrupt-key Message2 ciphertext.
                 _initiator_nonce_in_used_nonces s session initiator responder initiator_nonce';
                 _send2_received_nonce_neq_honest corrupt s lid.session lid.peer lid.party
                   initiator_nonce responder_key session initiator responder initiator_nonce';
                 _send2_nonce_not_newly_derivable_from_ciphertext
                   s.know lid.session lid.party initiator_nonce responder_nonce initiator_nonce' k d
               ))
          | None -> ());
       introduce forall (session: session_id) (responder initiator: participant_id)
                        (responder_nonce': nonce) (d: adv.derivation).
         (match ma_sim_responder_session_state (s2p_state s') responder session with
          | Some rst ->
            (rst.responder == responder /\ rst.initiator == initiator /\
             rst.responder_nonce == responder_nonce' /\
             not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
            not (adv.derive d s'.know = Some (Nonce responder_nonce'))
          | None -> True)
       with
         (match ma_sim_responder_session_state (s2p_state s') responder session with
          | Some rst ->
            introduce
              (rst.responder == responder /\ rst.initiator == initiator /\
               rst.responder_nonce == responder_nonce' /\
               not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
              not (adv.derive d s'.know = Some (Nonce responder_nonce'))
            with _heq.
              (ma_sim_send_message2_state_get_updated_sim_participant_session_state
                 (s2p_state s) lid.session lid.party lid.peer
                 initiator_nonce responder_nonce responder_key responder session;
               unfold_ma_sim_responder_session_state (s2p_state s') responder session;
               if responder = lid.party && session = lid.session then
                 // New responder session: initiator = lid.peer which is corrupt → vacuous
                 assert (initiator == lid.peer)
               else (
                 participant_session_eq_implies_responder_session_eq
                   (s2p_state s) responder session (s2p_state s') responder session;
                 assert (matches_responder_state s session responder initiator responder_nonce');
                 if adv.derive d s'.know = Some (Nonce responder_nonce') then (
                   // responder_nonce' (honest, stored) differs from the fresh
                   // responder_nonce (freshness) and the received initiator_nonce
                   // (provenance).
                   _responder_nonce_in_used_nonces s session responder initiator responder_nonce';
                   _send2_received_nonce_neq_honest corrupt s lid.session lid.peer lid.party
                     initiator_nonce responder_key session responder initiator responder_nonce';
                   _send2_nonce_not_newly_derivable_from_ciphertext
                     s.know lid.session lid.party initiator_nonce responder_nonce responder_nonce' k d
                 )
               ))
          | None -> ())
     )
    )
#pop-options

#push-options "--fuel 5 --ifuel 2 --z3rlimit 300"
private
let _obs_send3_secrecy
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_corrupt_set_matches corrupt s /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_ideal_used_nonces_invariant s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_ideal_inputs_derivable s /\
        ma_session_nonces_unique s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_private_keys_not_derivable corrupt key_directory s' /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns
    ma_private_keys_not_derivable corrupt key_directory s' /\
    ma_valid_initiator_nonces_not_derivable corrupt s' /\
    ma_valid_responder_nonces_not_derivable corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     let m = Nonce responder_nonce in
     _enabled3_dir s lid.session lid.party lid.peer
       responder_nonce initiator_key responder_pubkey;
     assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
     assert (PartialMap.sel s.internal.key_directory lid.peer == Some k);
     assert (s.internal.key_directory == key_directory);
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.know == Seq.snoc s.know (Aenc (Pair (SessionId lid.session) m) k));
     // Message3 plaintext m = Nonce nr has no PrivKey subterms.
     assert (no_private_key_subterms
       (derivable_subterms_underapproximate_keys s.know (Aenc (Pair (SessionId lid.session) m) k)));
     _send_ciphertext_preserves_key_secrecy corrupt key_directory s s' lid.session m k;
     // send3 only flips the `ack_sent` bit of `lid.party`'s initiator session, so
     // every stored nonce is unchanged from `s`.
     if not (Set.mem lid.peer corrupt) then (
       _directory_key_not_derivable corrupt key_directory s lid.peer k;
       introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
         matches_initiator_state s' sess p q nn /\
         not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
         (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
       with introduce _ ==> _ with _hm.
         (ma_sim_send_message3_state_get_updated_sim_participant_session_state
            (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key p sess;
          unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
          unfold_ma_sim_initiator_session_state (s2p_state s) p sess;
          if p = lid.party && sess = lid.session then
            (assert (matches_initiator_state s sess p q nn))
          else
            (participant_session_eq_implies_initiator_session_eq
               (s2p_state s) p sess (s2p_state s') p sess;
             assert (matches_initiator_state s sess p q nn)));
       introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
         matches_responder_state s' sess p q nn /\
         not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
         (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
       with introduce _ ==> _ with _hm.
         (ma_sim_send_message3_state_get_updated_sim_responder_session_state
            (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key p sess;
          assert (matches_responder_state s sess p q nn));
       _ciphertext_preserves_valid_nonces corrupt s s' lid.session m k
     ) else (
       // lid.peer is corrupt; all stored sessions are unchanged from s.  The
       // emitted Message3 echoes `responder_nonce`, received in the Message2 that
       // enabled this step (carrying `lid.party`'s initiator-session nonce `ini`).
       let ini =
         (Some?.v (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session)).initiator_nonce in
       assert (Bag.mem (ma_nsl_message2_network_term
         lid.session lid.party lid.peer ini responder_nonce (PubKey initiator_key)) s.inputs);
       introduce forall (session: session_id) (initiator responder: participant_id)
                        (initiator_nonce: nonce) (d: adv.derivation).
         (match ma_sim_initiator_session_state (s2p_state s') initiator session with
          | Some ist ->
            (ist.initiator == initiator /\ ist.responder == responder /\
             ist.initiator_nonce == initiator_nonce /\
             not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
            not (adv.derive d s'.know = Some (Nonce initiator_nonce))
          | None -> True)
       with
         (match ma_sim_initiator_session_state (s2p_state s') initiator session with
          | Some ist ->
            introduce
              (ist.initiator == initiator /\ ist.responder == responder /\
               ist.initiator_nonce == initiator_nonce /\
               not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
              not (adv.derive d s'.know = Some (Nonce initiator_nonce))
            with _heq.
              (ma_sim_send_message3_state_get_updated_sim_participant_session_state
                 (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key initiator session;
               unfold_ma_sim_initiator_session_state (s2p_state s') initiator session;
               unfold_ma_sim_initiator_session_state (s2p_state s) initiator session;
               if initiator = lid.party && session = lid.session then
                 // Existing session but lid.peer = responder which is corrupt → vacuous
                 assert (responder == lid.peer)
               else (
                 participant_session_eq_implies_initiator_session_eq
                   (s2p_state s) initiator session (s2p_state s') initiator session;
                 assert (matches_initiator_state s session initiator responder initiator_nonce);
                 if adv.derive d s'.know = Some (Nonce initiator_nonce) then (
                   // initiator_nonce (honest) differs from the received responder_nonce
                   // (provenance), so it is not exposed by the Message3 ciphertext.
                   _send3_received_nonce_neq_honest corrupt s lid.session lid.party lid.peer
                     ini responder_nonce initiator_key session initiator responder initiator_nonce;
                   _send3_nonce_not_newly_derivable_from_ciphertext
                     s.know lid.session responder_nonce initiator_nonce k d
                 )
               ))
          | None -> ());
       introduce forall (session: session_id) (responder initiator: participant_id)
                        (responder_nonce': nonce) (d: adv.derivation).
         (match ma_sim_responder_session_state (s2p_state s') responder session with
          | Some rst ->
            (rst.responder == responder /\ rst.initiator == initiator /\
             rst.responder_nonce == responder_nonce' /\
             not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
            not (adv.derive d s'.know = Some (Nonce responder_nonce'))
          | None -> True)
       with
         (match ma_sim_responder_session_state (s2p_state s') responder session with
          | Some rst ->
            introduce
              (rst.responder == responder /\ rst.initiator == initiator /\
               rst.responder_nonce == responder_nonce' /\
               not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
              not (adv.derive d s'.know = Some (Nonce responder_nonce'))
            with _heq.
              (ma_sim_send_message3_state_get_updated_sim_responder_session_state
                 (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder session;
               assert (matches_responder_state s session responder initiator responder_nonce');
               if adv.derive d s'.know = Some (Nonce responder_nonce') then (
                 // responder_nonce' (honest, stored) differs from the received
                 // responder_nonce (provenance).
                 _send3_received_nonce_neq_honest corrupt s lid.session lid.party lid.peer
                   ini responder_nonce initiator_key session responder initiator responder_nonce';
                 _send3_nonce_not_newly_derivable_from_ciphertext
                   s.know lid.session responder_nonce responder_nonce' k d
               ))
          | None -> ())
     )
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
private
let _obs_deliver_secrecy
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_private_keys_not_derivable corrupt key_directory s' /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  assert (s'.know ==
    Seq.snoc s.know (ma_authenticated_term lid.session lid.party lid.peer));
  assert (s2p_state s' == ma_ideal_deliver_state (s2p_state s) lid.session lid.party lid.peer);
  _deliver_preserves_key_secrecy corrupt key_directory s s' lid.session lid.party lid.peer;
  // deliver leaves the simulator session map unchanged (SMTPat
  // `ma_ideal_deliver_state_preserves_get_sim_participant_session_state`), so every
  // stored nonce is unchanged from `s` and underivable by the IH.
  introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
    matches_initiator_state s' sess p q nn /\
    not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
    (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
  with introduce _ ==> _ with _hm.
    (participant_session_eq_implies_initiator_session_eq
       (s2p_state s) p sess (s2p_state s') p sess;
     assert (matches_initiator_state s sess p q nn));
  introduce forall (sess: session_id) (p q: participant_id) (nn: nonce).
    matches_responder_state s' sess p q nn /\
    not (Set.mem p corrupt) /\ not (Set.mem q corrupt) ==>
    (forall (d: adv.derivation). not (adv.derive d s.know = Some (Nonce nn)))
  with introduce _ ==> _ with _hm.
    (participant_session_eq_implies_responder_session_eq
       (s2p_state s) p sess (s2p_state s') p sess;
     assert (matches_responder_state s sess p q nn));
  _deliver_preserves_valid_nonces corrupt s s' lid.session lid.party lid.peer
#pop-options

/// The ideal `receive_message3` step leaves the key directory unchanged.
private
let _simrecv_preserves_key_directory
      (s: ideal_proto_state) (session: session_id)
      (responder initiator: participant_id) (responder_key: priv_key)
    : Lemma (requires Some? (ma_sim_responder_session_state s responder session))
            (ensures
              (ma_sim_receive_message3_state s session responder initiator responder_key)
                .internal.key_directory == s.internal.key_directory) = ()

/// Every ideal protocol transition leaves the key directory unchanged (C_kd).
/// Centralizes the per-sub-transition case analysis so both the `Internal` and
/// `Observable` arms of the preservation proof can reuse it.
private
let _protocol_transition_preserves_key_directory
      (sp: ideal_proto_state)
      (l: Protocol.label term ma_effect ma_label_id)
      (sp': ideal_proto_state)
    : Lemma
      (requires ma_ideal_protocol_transition sp l sp')
      (ensures sp'.internal.key_directory == sp.internal.key_directory) =
  match l with
  | Protocol.Observable NetSend sent_t lid ->
    // send1 \/ send3 (Initiator) or send2 (Responder); SMTPats on
    // `(ma_sim_send_messageX_state ...).internal.key_directory` close each case.
    ()
  | Protocol.Observable IoSend output_t lid ->
    // deliver; SMTPat on `(ma_ideal_deliver_state ...).internal.key_directory`.
    ()
  | Protocol.Internal lid ->
    eliminate
      ma_ideal_initiate_protocol_transition sp lid.session lid.party lid.peer lid.role sp'
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition sp lid.session lid.party lid.peer sp'
          | Initiator -> False)
    returns sp'.internal.key_directory == sp.internal.key_directory
    with _hi. ()
    and _hr.
      (match lid.role with
       | Responder ->
         eliminate exists (responder_key: priv_key).
           ma_sim_receive_message3_enabled sp lid.session lid.party lid.peer responder_key /\
           sp' == ma_sim_receive_message3_state sp lid.session lid.party lid.peer responder_key
         returns sp'.internal.key_directory == sp.internal.key_directory
         with _hre.
           (assert (Some? (ma_sim_responder_session_state sp lid.party lid.session));
            _simrecv_preserves_key_directory sp lid.session lid.party lid.peer responder_key))

/// Frame lemma: `ma_ideal_state_inv` reads only the `internal` component of a
/// protocol state (through `s.internal.*`, `ma_session_requests`, and
/// `ma_sim_*_session_state`), so two states that agree on `internal` satisfy it
/// together.  Used to transfer C0 across the tester's `Input` step, which only
/// modifies the input bag.
private
let ma_ideal_state_inv_frame (s1 s2: ideal_proto_state)
    : Lemma (requires ma_ideal_state_inv s1 /\ s2.internal == s1.internal)
            (ensures ma_ideal_state_inv s2)
  =
  assert (forall (i: session_id).
            ma_session_requests s2 i == ma_session_requests s1 i);
  assert (forall (p: participant_id) (i: session_id).
            ma_sim_initiator_session_state s2 p i ==
            ma_sim_initiator_session_state s1 p i);
  assert (forall (p: participant_id) (i: session_id).
            ma_sim_responder_session_state s2 p i ==
            ma_sim_responder_session_state s1 p i)

// `ma_ideal_core_inv_init` and `ma_ideal_core_inv_preserved` are defined
// after the freshness section below: their bodies establish the bundled freshness
// conjunct (`ma_ideal_used_nonces_invariant`) via the per-transition `_freshness_*`
// helpers, which depend on definitions appearing later in this module.

/// ===========================================================================
/// Freshness, provenance, and output-complementary preservation.
/// ===========================================================================

/// ===========================================================================
/// Generic set / monotonicity helpers
/// ===========================================================================

private
let _subset_refl (#a: eqtype) (s: Set.set a) : Lemma (ensures Set.subset s s) =
  let h (x: a) : Lemma (ensures Set.mem x s ==> Set.mem x s) = () in
  FStar.Classical.forall_intro h;
  Set.mem_subset s s

private
let _subset_add (x: nonce) (u: Set.set nonce)
    : Lemma (ensures Set.subset u (Set.add x u)) =
  let h (n: nonce) : Lemma (ensures Set.mem n u ==> Set.mem n (Set.add x u)) = () in
  FStar.Classical.forall_intro h;
  Set.mem_subset u (Set.add x u)

/// Knowledge-nonce subset is monotone in the used-nonce set.
private
let _knowledge_nonces_weaken (u1 u2: Set.set nonce) (know: knowledge term)
    : Lemma
      (requires ma_knowledge_nonces_are_used u1 know /\ Set.subset u1 u2)
      (ensures ma_knowledge_nonces_are_used u2 know) =
  FStar.Set.Properties.set_subset_transitive (ma_knowledge_nonces know) u1 u2

/// Inputs-nonce membership is monotone in the used-nonce set.
private
let _inputs_nonces_weaken (u1 u2: Set.set nonce) (inputs: bag term)
    : Lemma
      (requires ma_inputs_nonces_are_used u1 inputs /\ Set.subset u1 u2)
      (ensures ma_inputs_nonces_are_used u2 inputs) =
  let h (t: term)
      : Lemma (ensures Bag.mem t inputs ==> ma_term_nonces_are_used u2 t) =
    if Bag.mem t inputs then
      FStar.Set.Properties.set_subset_transitive (ma_term_nonces t) u1 u2
  in
  FStar.Classical.forall_intro h

/// Inputs-nonce membership transfers along bag inclusion (`inputs2 ⊆ inputs1`).
private
let _inputs_nonces_subset (used: Set.set nonce) (inputs1 inputs2: bag term)
    : Lemma
      (requires ma_inputs_nonces_are_used used inputs1 /\ Bag.subset inputs2 inputs1)
      (ensures ma_inputs_nonces_are_used used inputs2) =
  let h (t: term)
      : Lemma (ensures Bag.mem t inputs2 ==> ma_term_nonces_are_used used t) =
    if Bag.mem t inputs2 then Bag.subset_mem t inputs2 inputs1
  in
  FStar.Classical.forall_intro h

/// ===========================================================================
/// Message-term nonce facts (local copies of the trivial
/// `MA.ObservationalBisimulation.Proof.MessageDerivability` lemmas; the heavy
/// derivability module is intentionally not opened here).
/// ===========================================================================

private
let _msg1_nonces_used
      (used_nonces: Set.set nonce)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires Set.mem initiator_nonce used_nonces)
      (ensures
        ma_term_nonces_are_used used_nonces
          (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey)) =
  assert (ma_term_nonces_are_used used_nonces
      (ma_nsl_message1_term session initiator responder initiator_nonce responder_pubkey))

private
let _msg2_nonces_used
      (used_nonces: Set.set nonce)
      (inputs: bag term)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
    : Lemma
      (requires
        ma_inputs_nonces_are_used used_nonces inputs /\
        Bag.mem (ma_nsl_message1_network_term
          session initiator responder initiator_nonce (PubKey responder_key)) inputs /\
        Set.mem responder_nonce used_nonces)
      (ensures
        ma_term_nonces_are_used used_nonces
          (ma_nsl_message2_term
            session initiator responder initiator_nonce responder_nonce initiator_pubkey)) =
  assert (ma_term_nonces_are_used used_nonces
      (ma_nsl_message2_term
        session initiator responder initiator_nonce responder_nonce initiator_pubkey))

private
let _msg3_nonces_used
      (used_nonces: Set.set nonce)
      (inputs: bag term)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
    : Lemma
      (requires
        ma_inputs_nonces_are_used used_nonces inputs /\
        Bag.mem
          (ma_nsl_message2_network_term
            session initiator responder initiator_nonce responder_nonce
            (PubKey initiator_key))
          inputs)
      (ensures
        ma_term_nonces_are_used used_nonces
          (ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey)) =
  assert (ma_term_nonces_are_used used_nonces
      (ma_nsl_message3_term session initiator responder responder_nonce responder_pubkey))

/// ===========================================================================
/// Per-transition freshness preservation
///
/// Each helper proves `ma_ideal_used_nonces_invariant s'` for one tested-system
/// sub-transition.  The `Bag.subset s'.inputs s.inputs` hypothesis is supplied
/// by `ma_ideal_valid_transitions` in the dispatcher and discharges the inputs
/// conjunct uniformly.
/// ===========================================================================

private
let _freshness_input
      (s s': ideal_system_state)
      (d: adv.derivation)
      (t: term)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        derive d s.know == Some t /\
        s'.inputs == Bag.insert t s.inputs /\
        s'.know == s.know /\
        s'.internal == s.internal)
      (ensures ma_ideal_used_nonces_invariant s') =
  let used = s.internal.used_nonces in
  // stored, knowledge: `internal` and `know` unchanged.
  // inputs: the freshly derived term's nonces are knowledge nonces, hence used.
  ma_derive_term_nonces_in_knowledge_nonces s.know d t;
  FStar.Set.Properties.set_subset_transitive
    (ma_term_nonces t) (ma_knowledge_nonces s.know) used;
  let h (input_t: term)
      : Lemma
        (ensures
          Bag.mem input_t s'.inputs ==> ma_term_nonces_are_used used input_t) =
    Bag.mem_insert input_t t s.inputs
  in
  FStar.Classical.forall_intro h

private
let _freshness_initiate
      (s s': ideal_system_state)
      (lid: ma_label_id)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        Bag.subset s'.inputs s.inputs /\
        ma_ideal_initiate_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s') /\
        s'.know == s.know)
      (ensures ma_ideal_used_nonces_invariant s') =
  let used = s.internal.used_nonces in
  // used_nonces, sessions, knowledge all unchanged (SMTPat lemmas); inputs shrink.
  ma_ideal_initiate_state_preserves_used_nonces
    (s2p_state s) lid.session lid.party lid.peer lid.role;
  _inputs_nonces_subset used s.inputs s'.inputs

private
let _freshness_receive3
      (s s': ideal_system_state)
      (lid: ma_label_id)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        Bag.subset s'.inputs s.inputs /\
        ma_sim_receive_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer (s2p_state s') /\
        s'.know == s.know)
      (ensures ma_ideal_used_nonces_invariant s') =
  eliminate exists (responder_key: priv_key).
    ma_sim_receive_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_key /\
    s2p_state s' ==
      ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
  returns ma_ideal_used_nonces_invariant s'
  with _he.
    (let used = s.internal.used_nonces in
     // Some? responder session (from enabled) lets the get_updated SMTPat fire.
     assert (Some? (ma_sim_responder_session_state (s2p_state s) lid.party lid.session));
     ma_sim_receive_message3_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer responder_key;
     let stored_helper (qp: participant_id) (qs: session_id) (n: nonce)
         : Lemma
           (ensures (
             match PartialMap.sel (ma_sim_participant_sessions (s2p_state s') qp) qs with
             | Some (SimInitiatorSession ist) -> ist.initiator_nonce == n ==> Set.mem n s'.internal.used_nonces
             | Some (SimResponderSession rst) -> rst.responder_nonce == n ==> Set.mem n s'.internal.used_nonces
             | None -> True)) = ()
     in
     FStar.Classical.forall_intro_3 stored_helper;
     _inputs_nonces_subset used s.inputs s'.inputs)

private
let _freshness_send1
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        Bag.subset s'.inputs s.inputs /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_ideal_used_nonces_invariant s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns ma_ideal_used_nonces_invariant s'
  with _he.
    (let used = s.internal.used_nonces in
     let used' = s'.internal.used_nonces in
     // used' == Set.add initiator_nonce used
     ma_sim_send_message1_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce;
     _subset_add initiator_nonce used;
     Set.subset_mem used used';
     // stored
     let stored_helper (qp: participant_id) (qs: session_id) (n: nonce)
         : Lemma
           (ensures (
             match PartialMap.sel (ma_sim_participant_sessions (s2p_state s') qp) qs with
             | Some (SimInitiatorSession ist) -> ist.initiator_nonce == n ==> Set.mem n used'
             | Some (SimResponderSession rst) -> rst.responder_nonce == n ==> Set.mem n used'
             | None -> True)) =
       _send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce qp qs
     in
     FStar.Classical.forall_intro_3 stored_helper;
     // inputs: shrink then weaken
     _inputs_nonces_subset used s.inputs s'.inputs;
     _inputs_nonces_weaken used used' s'.inputs;
     // knowledge: weaken then snoc message1 (nonces = {initiator_nonce} ⊆ used')
     _knowledge_nonces_weaken used used' s.know;
     _msg1_nonces_used used' lid.session lid.party lid.peer initiator_nonce responder_pubkey;
     ma_knowledge_nonces_snoc_preserves_subset s.know t used')

private
let _freshness_send2
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        Bag.subset s'.inputs s.inputs /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_ideal_used_nonces_invariant s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns ma_ideal_used_nonces_invariant s'
  with _he.
    (let used = s.internal.used_nonces in
     let used' = s'.internal.used_nonces in
     // used' == Set.add responder_nonce used
     ma_sim_send_message2_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer
       initiator_nonce responder_nonce responder_key;
     _subset_add responder_nonce used;
     Set.subset_mem used used';
     // stored (new responder session nonce = responder_nonce ∈ used'; SMTPat get_updated)
     let stored_helper (qp: participant_id) (qs: session_id) (n: nonce)
         : Lemma
           (ensures (
             match PartialMap.sel (ma_sim_participant_sessions (s2p_state s') qp) qs with
             | Some (SimInitiatorSession ist) -> ist.initiator_nonce == n ==> Set.mem n used'
             | Some (SimResponderSession rst) -> rst.responder_nonce == n ==> Set.mem n used'
             | None -> True)) = ()
     in
     FStar.Classical.forall_intro_3 stored_helper;
     // inputs: shrink then weaken
     _inputs_nonces_subset used s.inputs s'.inputs;
     _inputs_nonces_weaken used used' s'.inputs;
     // knowledge: message2 nonces = {initiator_nonce, responder_nonce} ⊆ used'.
     // initiator_nonce ∈ used (from the message1 network input) ⊆ used';
     // responder_nonce ∈ used' (just added).
     _inputs_nonces_weaken used used' s.inputs;
     _msg2_nonces_used used' s.inputs
       lid.session lid.peer lid.party initiator_nonce responder_nonce responder_key initiator_pubkey;
     _knowledge_nonces_weaken used used' s.know;
     ma_knowledge_nonces_snoc_preserves_subset s.know t used')

private
let _freshness_send3
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        Bag.subset s'.inputs s.inputs /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_ideal_used_nonces_invariant s') =
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns ma_ideal_used_nonces_invariant s'
  with _he.
    (let used = s.internal.used_nonces in
     // used_nonces unchanged.
     assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
     let initiator_state =
       Some?.v (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session) in
     ma_sim_send_message3_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key;
     // stored (initiator session: only the ack bit changes; nonce unchanged ∈ used)
     let stored_helper (qp: participant_id) (qs: session_id) (n: nonce)
         : Lemma
           (ensures (
             match PartialMap.sel (ma_sim_participant_sessions (s2p_state s') qp) qs with
             | Some (SimInitiatorSession ist) -> ist.initiator_nonce == n ==> Set.mem n s'.internal.used_nonces
             | Some (SimResponderSession rst) -> rst.responder_nonce == n ==> Set.mem n s'.internal.used_nonces
             | None -> True)) = ()
     in
     FStar.Classical.forall_intro_3 stored_helper;
     _inputs_nonces_subset used s.inputs s'.inputs;
     // knowledge: message3 nonces = {responder_nonce}; responder_nonce ∈ used from
     // the message2 network input.
     _msg3_nonces_used used s.inputs
       lid.session lid.party lid.peer initiator_state.initiator_nonce responder_nonce
       initiator_key responder_pubkey;
     ma_knowledge_nonces_snoc_preserves_subset s.know t s'.internal.used_nonces)

private
let _freshness_deliver
      (s s': ideal_system_state)
      (lid: ma_label_id)
      (t: term)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        Bag.subset s'.inputs s.inputs /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_ideal_used_nonces_invariant s') =
  let used = s.internal.used_nonces in
  // used_nonces and sessions unchanged (SMTPat lemmas); inputs unchanged.
  ma_ideal_deliver_state_preserves_used_nonces (s2p_state s) lid.session lid.party lid.peer;
  _inputs_nonces_subset used s.inputs s'.inputs;
  // knowledge: the authenticated output term carries no nonces.
  FStar.Tactics.Effect.assert_by_tactic
    (Set.equal (ma_term_nonces t) Set.empty)
    (fun _ ->
        (let open FStar.Tactics.V2 in
          norm [delta_only [`%ma_authenticated_term; `%ma_term_nonces]; zeta; iota];
          smt ()));
  ma_knowledge_nonces_snoc_empty_preserves_subset s.know t used

/// ===========================================================================
/// Secrecy invariant: initialization and preservation.
///
/// Defined here (after the freshness helpers) because the bundled freshness
/// conjunct `ma_ideal_used_nonces_invariant` is re-established at `s'` via the
/// per-transition `_freshness_*` helpers above, and stored-nonce secrecy at `s'`
/// via the `_obs_*_secrecy` helpers (Observable) or the knowledge-unchanged
/// transfer helper below (Input / Internal).
/// ===========================================================================

/// When the knowledge is unchanged and every stored session of `s'` already
/// existed (with the same nonce) in `s`, stored-nonce secrecy transfers verbatim.
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
private
let _know_unchanged_preserves_valid_nonces
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
    : Lemma
      (requires
        s'.know == s.know /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        (forall (sess: session_id) (p q: participant_id) (nn: nonce).
           matches_initiator_state s' sess p q nn ==> matches_initiator_state s sess p q nn) /\
        (forall (sess: session_id) (p q: participant_id) (nn: nonce).
           matches_responder_state s' sess p q nn ==> matches_responder_state s sess p q nn))
      (ensures
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        ma_valid_responder_nonces_not_derivable corrupt s') =
  introduce forall (session: session_id) (initiator responder: participant_id)
                   (initiator_nonce: nonce) (d: adv.derivation).
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       (ist.initiator == initiator /\ ist.responder == responder /\
        ist.initiator_nonce == initiator_nonce /\
        not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce initiator_nonce))
     | None -> True)
  with
    (match ma_sim_initiator_session_state (s2p_state s') initiator session with
     | Some ist ->
       introduce
         (ist.initiator == initiator /\ ist.responder == responder /\
          ist.initiator_nonce == initiator_nonce /\
          not (Set.mem initiator corrupt) /\ not (Set.mem responder corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce initiator_nonce))
       with _heq.
         (assert (matches_initiator_state s' session initiator responder initiator_nonce);
          assert (matches_initiator_state s session initiator responder initiator_nonce))
     | None -> ());
  introduce forall (session: session_id) (responder initiator: participant_id)
                   (responder_nonce: nonce) (d: adv.derivation).
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       (rst.responder == responder /\ rst.initiator == initiator /\
        rst.responder_nonce == responder_nonce /\
        not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
       not (adv.derive d s'.know = Some (Nonce responder_nonce))
     | None -> True)
  with
    (match ma_sim_responder_session_state (s2p_state s') responder session with
     | Some rst ->
       introduce
         (rst.responder == responder /\ rst.initiator == initiator /\
          rst.responder_nonce == responder_nonce /\
          not (Set.mem responder corrupt) /\ not (Set.mem initiator corrupt)) ==>
         not (adv.derive d s'.know = Some (Nonce responder_nonce))
       with _heq.
         (assert (matches_responder_state s' session responder initiator responder_nonce);
          assert (matches_responder_state s session responder initiator responder_nonce))
     | None -> ())
#pop-options

/// ---------------------------------------------------------------------------
/// Nonce-uniqueness preservation helpers.
///
/// `ma_session_nonces_unique` is preserved by any transition whose session map
/// is a subset of the old map (Input, Internal, send3, deliver), and by the
/// two session-creating transitions (send1, send2) because the new session's
/// nonce is fresh (not in `used_nonces`) while all existing sessions' nonces
/// are already in `used_nonces` (by `ma_ideal_stored_nonces_are_used`).
/// ---------------------------------------------------------------------------

/// Nonce uniqueness is preserved when sessions in `s'` are a subset of those
/// in `s` (i.e., no new sessions are added and no nonces change).
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
private
let _nonce_uniqueness_preserved_by_subset_sessions
      (s s': ideal_system_state)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          matches_initiator_state s' sess p q n ==> matches_initiator_state s sess p q n) /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          matches_responder_state s' sess p q n ==> matches_responder_state s sess p q n))
      (ensures ma_session_nonces_unique s') =
  ()
#pop-options

/// Nonce uniqueness is preserved by send1, which adds a fresh-nonce initiator
/// session.  Existing sessions have nonces in `used_nonces`; the fresh nonce
/// is not, so they cannot collide.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
private
let _nonce_uniqueness_preserved_by_send1
      (s s': ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce: nonce)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        ma_ideal_used_nonces_invariant s /\
        not (Set.mem initiator_nonce s.internal.used_nonces) /\
        s2p_state s' ==
          ma_sim_send_message1_state
            (s2p_state s) session initiator responder initiator_nonce /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          matches_responder_state s' sess p q n ==> matches_responder_state s sess p q n))
      (ensures ma_session_nonces_unique s') =
  introduce forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_initiator_state s' sess1 p1 q1 n /\
    matches_initiator_state s' sess2 p2 q2 n ==>
    sess1 == sess2 /\ p1 == p2
  with introduce _ ==> _ with _hpair.
    (_send1_get_updated (s2p_state s) session initiator responder initiator_nonce p1 sess1;
     _send1_get_updated (s2p_state s) session initiator responder initiator_nonce p2 sess2;
     unfold_ma_sim_initiator_session_state (s2p_state s') p1 sess1;
     unfold_ma_sim_initiator_session_state (s2p_state s') p2 sess2;
     if (p1 = initiator && sess1 = session) && (p2 = initiator && sess2 = session) then
       ()
     else if p1 = initiator && sess1 = session then (
       // sess1/p1 is the new session (nonce = initiator_nonce), sess2/p2 is old
       assert (n == initiator_nonce);
       unfold_ma_sim_initiator_session_state (s2p_state s) p2 sess2;
       participant_session_eq_implies_initiator_session_eq
         (s2p_state s) p2 sess2 (s2p_state s') p2 sess2;
       _initiator_nonce_in_used_nonces s sess2 p2 q2 n
     ) else if p2 = initiator && sess2 = session then (
       // sess2/p2 is the new session (nonce = initiator_nonce), sess1/p1 is old
       assert (n == initiator_nonce);
       unfold_ma_sim_initiator_session_state (s2p_state s) p1 sess1;
       participant_session_eq_implies_initiator_session_eq
         (s2p_state s) p1 sess1 (s2p_state s') p1 sess1;
       _initiator_nonce_in_used_nonces s sess1 p1 q1 n
     ) else (
       // Both are old sessions
       unfold_ma_sim_initiator_session_state (s2p_state s) p1 sess1;
       unfold_ma_sim_initiator_session_state (s2p_state s) p2 sess2;
       participant_session_eq_implies_initiator_session_eq
         (s2p_state s) p1 sess1 (s2p_state s') p1 sess1;
       participant_session_eq_implies_initiator_session_eq
         (s2p_state s) p2 sess2 (s2p_state s') p2 sess2;
       assert (matches_initiator_state s sess1 p1 q1 n);
       assert (matches_initiator_state s sess2 p2 q2 n)
     ));
  // Clause 2 (responder/responder): send1 leaves responder sessions unchanged.
  introduce forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_responder_state s' sess1 p1 q1 n /\
    matches_responder_state s' sess2 p2 q2 n ==>
    sess1 == sess2 /\ p1 == p2
  with introduce _ ==> _ with _hpair. ();
  // Clause 3 (initiator nonce ≠ responder nonce).  Responder sessions are
  // unchanged; for the new initiator session the fresh nonce is not a used nonce,
  // while every responder nonce is, so they cannot coincide.
  introduce forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_initiator_state s' sess1 p1 q1 n ==>
    ~(matches_responder_state s' sess2 p2 q2 n)
  with introduce _ ==> _ with _hi.
    (_send1_get_updated (s2p_state s) session initiator responder initiator_nonce p1 sess1;
     unfold_ma_sim_initiator_session_state (s2p_state s') p1 sess1;
     if p1 = initiator && sess1 = session then
       (assert (n == initiator_nonce);
        introduce matches_responder_state s' sess2 p2 q2 n ==> False
        with _hr.
          (assert (matches_responder_state s sess2 p2 q2 n);
           _responder_nonce_in_used_nonces s sess2 p2 q2 n))
     else
       (unfold_ma_sim_initiator_session_state (s2p_state s) p1 sess1;
        participant_session_eq_implies_initiator_session_eq
          (s2p_state s) p1 sess1 (s2p_state s') p1 sess1;
        assert (matches_initiator_state s sess1 p1 q1 n)))
#pop-options

/// Nonce uniqueness is preserved by send2, which adds a fresh-nonce responder
/// session.
#push-options "--fuel 1 --ifuel 2 --z3rlimit 80"
private
let _nonce_uniqueness_preserved_by_send2
      (s s': ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (responder_key: priv_key)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        ma_ideal_used_nonces_invariant s /\
        not (Set.mem responder_nonce s.internal.used_nonces) /\
        s2p_state s' ==
          ma_sim_send_message2_state
            (s2p_state s) session responder initiator initiator_nonce responder_nonce responder_key /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          matches_initiator_state s' sess p q n ==> matches_initiator_state s sess p q n))
      (ensures ma_session_nonces_unique s') =
  introduce forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_responder_state s' sess1 p1 q1 n /\
    matches_responder_state s' sess2 p2 q2 n ==>
    sess1 == sess2 /\ p1 == p2
  with introduce _ ==> _ with _hpair.
    (unfold_ma_sim_responder_session_state (s2p_state s') p1 sess1;
     unfold_ma_sim_responder_session_state (s2p_state s') p2 sess2;
     if (p1 = responder && sess1 = session) && (p2 = responder && sess2 = session) then
       ()
     else if p1 = responder && sess1 = session then (
       assert (n == responder_nonce);
       unfold_ma_sim_responder_session_state (s2p_state s) p2 sess2;
       participant_session_eq_implies_responder_session_eq
         (s2p_state s) p2 sess2 (s2p_state s') p2 sess2;
       _responder_nonce_in_used_nonces s sess2 p2 q2 n
     ) else if p2 = responder && sess2 = session then (
       assert (n == responder_nonce);
       unfold_ma_sim_responder_session_state (s2p_state s) p1 sess1;
       participant_session_eq_implies_responder_session_eq
         (s2p_state s) p1 sess1 (s2p_state s') p1 sess1;
       _responder_nonce_in_used_nonces s sess1 p1 q1 n
     ) else (
       unfold_ma_sim_responder_session_state (s2p_state s) p1 sess1;
       unfold_ma_sim_responder_session_state (s2p_state s) p2 sess2;
       participant_session_eq_implies_responder_session_eq
         (s2p_state s) p1 sess1 (s2p_state s') p1 sess1;
       participant_session_eq_implies_responder_session_eq
         (s2p_state s) p2 sess2 (s2p_state s') p2 sess2;
       assert (matches_responder_state s sess1 p1 q1 n);
       assert (matches_responder_state s sess2 p2 q2 n)
     ));
  // Initiator-responder cross-type uniqueness: the new responder nonce is fresh,
  // initiator nonces of s' = s are all in used_nonces → different from fresh nr.
  introduce forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_initiator_state s' sess1 p1 q1 n ==>
    ~(matches_responder_state s' sess2 p2 q2 n)
  with introduce _ ==> _ with _hi.
    introduce matches_responder_state s' sess2 p2 q2 n ==> False
    with _hr.
      (// initiator sessions are unchanged by send2, so n is a used nonce
       assert (matches_initiator_state s sess1 p1 q1 n);
       _initiator_nonce_in_used_nonces s sess1 p1 q1 n;
       unfold_ma_sim_responder_session_state (s2p_state s') p2 sess2;
       if p2 = responder && sess2 = session then
         // new responder session: n = responder_nonce ∉ used_nonces — contradiction
         assert (n == responder_nonce)
       else (
         // old responder session: contradicts IH cross-type uniqueness at s
         participant_session_eq_implies_responder_session_eq
           (s2p_state s) p2 sess2 (s2p_state s') p2 sess2;
         assert (matches_responder_state s sess2 p2 q2 n)))
#pop-options

/// ===========================================================================
/// Snoc-based preservation of the knowledge-structure invariants.  Each
/// Observable step appends a single term `t` to `s.know`.  The invariants are
/// conditioned on a *protected nonce* (`ma_is_honest_session_nonce`), so the
/// only knowledge terms they constrain are those carrying such a nonce.  For an
/// *old* index the term is unchanged: if it still carries a protected nonce of
/// `s'`, that nonce is in the (monotone) knowledge nonces of `s.know` and so,
/// by backward session preservation, was already protected at `s` — the old
/// invariant then discharges the obligation (`_honest_nonce_back`).  For the
/// *new* index the appended `t` is `shallow_aenc`, so a Message-shaped
/// `aenc_subterm` of it equals `t`; the caller supplies the (`t`-shape) fact.
/// ===========================================================================

/// A protected nonce of `s'` that occurs in the knowledge nonces of `s.know`
/// was already a protected nonce of `s`.  The witnessing `s'` session is, by
/// backward session preservation, either an `s` session — or carries a nonce not
/// in `used_nonces`; but a knowledge nonce of `s.know` *is* in `used_nonces`
/// (C_fresh), so the latter is impossible.  This is the index-free replacement
/// for "the fresh nonce is absent from the initial-knowledge prefix": it pins a
/// protected nonce to a session that predates the append, with no reference to
/// any initial-knowledge length.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
private
let _honest_nonce_back
      (corrupt: Set.set participant_id) (s s': ideal_system_state) (m: nonce)
    : Lemma
      (requires
        ma_ideal_used_nonces_invariant s /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
          ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
           ~(Set.mem n s.internal.used_nonces))) /\
        Set.mem m (ma_knowledge_nonces s.know) /\
        ma_is_honest_session_nonce corrupt s' m)
      (ensures ma_is_honest_session_nonce corrupt s m) =
  Set.subset_mem (ma_knowledge_nonces s.know) s.internal.used_nonces;
  assert (Set.mem m s.internal.used_nonces);
  eliminate exists (sess: session_id) (a b: participant_id).
    (matches_initiator_state s' sess a b m \/ matches_responder_state s' sess a b m) /\
    not (Set.mem a corrupt) /\ not (Set.mem b corrupt)
  returns ma_is_honest_session_nonce corrupt s m
  with _h.
    _honest_session_nonce_intro corrupt s sess a b m
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 150"
private
let _honest_msg1_preserved_snoc
      (corrupt: Set.set participant_id) (s s': ideal_system_state) (t: term)
    : Lemma
      (requires
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        s'.know == Seq.snoc s.know t /\
        shallow_aenc t /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
          ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
           ~(Set.mem n s.internal.used_nonces))) /\
        (forall (sess: session_id) (m: nonce) (p: participant_id) (k: priv_key).
          Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) k == t /\
          ma_is_honest_session_nonce corrupt s' m ==> not (Set.mem p corrupt)))
      (ensures ma_honest_msg1_names_non_corrupt corrupt s') =
  let kn = Seq.length s.know in
  introduce forall (idx: nat) (sess: session_id) (m: nonce) (p: participant_id) (k: priv_key).
      idx < Seq.length s'.know /\
      aenc_subterm
        (Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) k)
        (Seq.index s'.know idx) /\
      ma_is_honest_session_nonce corrupt s' m ==>
      not (Set.mem p corrupt)
  with introduce _ ==> _ with _h.
    (let c = Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) k in
     if idx < kn then
       (Seq.lemma_index_app1 s.know (Seq.create 1 t) idx;
        let kt = Seq.index s.know idx in
        aenc_subterm_nonces_subset c kt;
        assert (Set.mem m (ma_term_nonces c));
        Set.subset_mem (ma_term_nonces c) (ma_term_nonces kt);
        ma_knowledge_nonces_index s.know idx kt;
        Set.subset_mem (ma_term_nonces kt) (ma_knowledge_nonces s.know);
        _honest_nonce_back corrupt s s' m;
        _honest_msg1_names corrupt s idx sess m p k)
     else
       (Seq.lemma_index_app2 s.know (Seq.create 1 t) idx;
        Seq.lemma_index_create 1 t (idx - kn);
        aenc_subterm_shallow_eq c t))
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 150"
private
let _honest_msg2_preserved_snoc
      (corrupt: Set.set participant_id) (s s': ideal_system_state) (t: term)
    : Lemma
      (requires
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        s'.know == Seq.snoc s.know t /\
        shallow_aenc t /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
          ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
           ~(Set.mem n s.internal.used_nonces))) /\
        (forall (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key).
          Aenc (Pair (SessionId sess)
                 (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k == t /\
          ma_is_honest_session_nonce corrupt s' mr ==> not (Set.mem p corrupt)))
      (ensures ma_honest_msg2_names_non_corrupt corrupt s') =
  let kn = Seq.length s.know in
  introduce forall (idx: nat) (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key).
      idx < Seq.length s'.know /\
      aenc_subterm
        (Aenc (Pair (SessionId sess)
                (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k)
        (Seq.index s'.know idx) /\
      ma_is_honest_session_nonce corrupt s' mr ==>
      not (Set.mem p corrupt)
  with introduce _ ==> _ with _h.
    (let c = Aenc (Pair (SessionId sess)
                    (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k in
     if idx < kn then
       (Seq.lemma_index_app1 s.know (Seq.create 1 t) idx;
        let kt = Seq.index s.know idx in
        aenc_subterm_nonces_subset c kt;
        assert (Set.mem mr (ma_term_nonces c));
        Set.subset_mem (ma_term_nonces c) (ma_term_nonces kt);
        ma_knowledge_nonces_index s.know idx kt;
        Set.subset_mem (ma_term_nonces kt) (ma_knowledge_nonces s.know);
        _honest_nonce_back corrupt s s' mr;
        _honest_msg2_names corrupt s idx sess mi mr p k)
     else
       (Seq.lemma_index_app2 s.know (Seq.create 1 t) idx;
        Seq.lemma_index_create 1 t (idx - kn);
        aenc_subterm_shallow_eq c t))
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 200"
private
let _honest_msg2key_preserved_snoc
      (corrupt: Set.set participant_id) (s s': ideal_system_state) (t: term)
    : Lemma
      (requires
        ma_honest_msg2_key_matches_initiator corrupt s /\
        ma_honest_carrier_shallow corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        s'.know == Seq.snoc s.know t /\
        shallow_aenc t /\
        s'.internal.key_directory == s.internal.key_directory /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
          ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
           ~(Set.mem n s.internal.used_nonces))) /\
        // Responder-specific backward preservation: a post-state responder match with
        // a *used* nonce was already a responder match at `s` (it keeps its role).
        (forall (sess: session_id) (p initiator: participant_id) (mr: nonce).
          matches_responder_state s' sess p initiator mr ==>
          (matches_responder_state s sess p initiator mr \/
           ~(Set.mem mr s.internal.used_nonces))) /\
        (forall (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key).
          Aenc (Pair (SessionId sess)
                 (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k == t /\
          ma_is_honest_session_nonce corrupt s' mr ==>
          (forall (initiator: participant_id).
             matches_responder_state s' sess p initiator mr ==>
             PartialMap.sel s'.internal.key_directory initiator == Some k)))
      (ensures ma_honest_msg2_key_matches_initiator corrupt s') =
  let kn = Seq.length s.know in
  introduce forall (idx: nat) (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key).
      idx < Seq.length s'.know /\
      aenc_subterm
        (Aenc (Pair (SessionId sess)
                (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k)
        (Seq.index s'.know idx) /\
      ma_is_honest_session_nonce corrupt s' mr ==>
      (forall (initiator: participant_id).
         matches_responder_state s' sess p initiator mr ==>
         PartialMap.sel s'.internal.key_directory initiator == Some k)
  with introduce _ ==> _ with _h.
    (let c = Aenc (Pair (SessionId sess)
                    (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k in
     if idx < kn then
       (Seq.lemma_index_app1 s.know (Seq.create 1 t) idx;
        let kt = Seq.index s.know idx in
        aenc_subterm_nonces_subset c kt;
        assert (Set.mem mr (ma_term_nonces c));
        Set.subset_mem (ma_term_nonces c) (ma_term_nonces kt);
        ma_knowledge_nonces_index s.know idx kt;
        Set.subset_mem (ma_term_nonces kt) (ma_knowledge_nonces s.know);
        Set.subset_mem (ma_knowledge_nonces s.know) s.internal.used_nonces;
        assert (Set.mem mr s.internal.used_nonces);
        _honest_nonce_back corrupt s s' mr;
        introduce forall (initiator: participant_id).
          matches_responder_state s' sess p initiator mr ==>
          PartialMap.sel s'.internal.key_directory initiator == Some k
        with introduce _ ==> _ with _hi.
          (// mr used ⟹ the s' responder match is an old s match; C_msg2key at s
           // (applied at index idx) gives the key.
           assert (matches_responder_state s sess p initiator mr);
           _honest_msg2_key corrupt s idx sess mi mr p initiator k))
     else
       (Seq.lemma_index_app2 s.know (Seq.create 1 t) idx;
        Seq.lemma_index_create 1 t (idx - kn);
        aenc_subterm_shallow_eq c t))
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 150"
private
let _honest_carrier_shallow_preserved_snoc
      (corrupt: Set.set participant_id) (s s': ideal_system_state) (t: term)
    : Lemma
      (requires
        ma_honest_carrier_shallow corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        s'.know == Seq.snoc s.know t /\
        shallow_aenc t /\
        (forall (sess: session_id) (p q: participant_id) (n: nonce).
          (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
          ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
           ~(Set.mem n s.internal.used_nonces))))
      (ensures ma_honest_carrier_shallow corrupt s') =
  let kn = Seq.length s.know in
  introduce forall (idx: nat) (m: nonce).
      idx < Seq.length s'.know /\
      Set.mem m (ma_term_nonces (Seq.index s'.know idx)) /\
      ma_is_honest_session_nonce corrupt s' m ==>
      shallow_aenc (Seq.index s'.know idx)
  with introduce _ ==> _ with _h.
    (if idx < kn then
       (Seq.lemma_index_app1 s.know (Seq.create 1 t) idx;
        let kt = Seq.index s.know idx in
        ma_knowledge_nonces_index s.know idx kt;
        Set.subset_mem (ma_term_nonces kt) (ma_knowledge_nonces s.know);
        _honest_nonce_back corrupt s s' m;
        _honest_carrier_shallow_at corrupt s idx m)
     else
       (Seq.lemma_index_app2 s.know (Seq.create 1 t) idx;
        Seq.lemma_index_create 1 t (idx - kn)))
#pop-options

/// Knowledge-structure invariant preservation for the send1 Observable step.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 400"
private
let _structure_send1
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_honest_msg2_key_matches_initiator corrupt s /\
        ma_honest_carrier_shallow corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_session_nonces_unique s' /\
        ma_honest_msg1_names_non_corrupt corrupt s' /\
        ma_honest_msg2_names_non_corrupt corrupt s' /\
        ma_honest_msg2_key_matches_initiator corrupt s' /\
        ma_honest_carrier_shallow corrupt s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns
    ma_session_nonces_unique s' /\
    ma_honest_msg1_names_non_corrupt corrupt s' /\
    ma_honest_msg2_names_non_corrupt corrupt s' /\
    ma_honest_msg2_key_matches_initiator corrupt s' /\
    ma_honest_carrier_shallow corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     assert (t == Aenc (Pair (SessionId lid.session)
       (Pair (Nonce initiator_nonce) (ParticipantId lid.party))) k);
     assert (not (Set.mem initiator_nonce s.internal.used_nonces));
     ma_sim_send_message1_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce;
     // C_shallow is now a local fact about the appended Message1 ciphertext.
     assert (shallow_aenc t);
     // C_uniq.
     _nonce_uniqueness_preserved_by_send1 s s' lid.session lid.party lid.peer initiator_nonce;
     // The freshly created initiator session.
     _send1_get_updated (s2p_state s) lid.session lid.party lid.peer
       initiator_nonce lid.party lid.session;
     unfold_ma_sim_initiator_session_state (s2p_state s') lid.party lid.session;
     assert (matches_initiator_state s' lid.session lid.party lid.peer initiator_nonce);
     // Backward session preservation modulo the fresh nonce (consumed by the
     // snoc helpers): every s' session is an s session or carries the fresh nonce.
     introduce forall (sess: session_id) (p q: participant_id) (n: nonce).
       (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
       ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
        ~(Set.mem n s.internal.used_nonces))
     with introduce _ ==> _ with _hc.
       (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce p sess;
        unfold_ma_sim_initiator_session_state (s2p_state s) p sess;
        unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
        unfold_ma_sim_responder_session_state (s2p_state s) p sess;
        unfold_ma_sim_responder_session_state (s2p_state s') p sess);
     // Responder-specific backward preservation (consumed by the C_msg2key helper).
     introduce forall (sess: session_id) (p initiator: participant_id) (mr: nonce).
       matches_responder_state s' sess p initiator mr ==>
       (matches_responder_state s sess p initiator mr \/ ~(Set.mem mr s.internal.used_nonces))
     with introduce _ ==> _ with _hb.
       (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce p sess;
        unfold_ma_sim_responder_session_state (s2p_state s) p sess;
        unfold_ma_sim_responder_session_state (s2p_state s') p sess);
     // C_msg1 (new index): the appended Message1 names lid.party.  If it carries a
     // protected nonce m, then m = initiator_nonce, whose unique session is the
     // just-created both-honest one, so its named initiator lid.party is non-corrupt.
     introduce forall (sess: session_id) (m: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) kk == t /\
       ma_is_honest_session_nonce corrupt s' m ==> not (Set.mem p corrupt)
     with introduce _ ==> _ with _ht.
       (eliminate exists (sess1: session_id) (a1 b1: participant_id).
          (matches_initiator_state s' sess1 a1 b1 m \/ matches_responder_state s' sess1 a1 b1 m) /\
          not (Set.mem a1 corrupt) /\ not (Set.mem b1 corrupt)
        returns not (Set.mem p corrupt)
        with _hw.
          (assert (matches_initiator_state s' lid.session lid.party lid.peer initiator_nonce);
           assert (a1 == lid.party)));
     _honest_msg1_preserved_snoc corrupt s s' t;
     // C_msg2 / C_msg2key (new index): Message1 is never a Message2-shaped
     // ciphertext, so the new-index hypotheses are vacuous.
     introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
       ma_is_honest_session_nonce corrupt s' mr ==> not (Set.mem p corrupt)
     with introduce _ ==> _ with _ht. ();
     _honest_msg2_preserved_snoc corrupt s s' t;
     introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
       ma_is_honest_session_nonce corrupt s' mr ==>
       (forall (initiator: participant_id).
          matches_responder_state s' sess p initiator mr ==>
          PartialMap.sel s'.internal.key_directory initiator == Some kk)
     with introduce _ ==> _ with _ht. ();
     _honest_carrier_shallow_preserved_snoc corrupt s s' t;
     _honest_msg2key_preserved_snoc corrupt s s' t)
#pop-options

/// Knowledge-structure invariant preservation for the send2 Observable step.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 400"
private
let _structure_send2
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_honest_msg2_key_matches_initiator corrupt s /\
        ma_honest_carrier_shallow corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_session_nonces_unique s' /\
        ma_honest_msg1_names_non_corrupt corrupt s' /\
        ma_honest_msg2_names_non_corrupt corrupt s' /\
        ma_honest_msg2_key_matches_initiator corrupt s' /\
        ma_honest_carrier_shallow corrupt s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns
    ma_session_nonces_unique s' /\
    ma_honest_msg1_names_non_corrupt corrupt s' /\
    ma_honest_msg2_names_non_corrupt corrupt s' /\
    ma_honest_msg2_key_matches_initiator corrupt s' /\
    ma_honest_carrier_shallow corrupt s'
  with _he.
    (let k = PubKey?.priv initiator_pubkey in
     assert (t == Aenc (Pair (SessionId lid.session)
       (Pair (Nonce initiator_nonce) (Pair (Nonce responder_nonce) (ParticipantId lid.party)))) k);
     assert (not (Set.mem responder_nonce s.internal.used_nonces));
     ma_sim_send_message2_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key;
     assert (s'.internal.key_directory == s.internal.key_directory);
     assert (shallow_aenc t);
     // C_uniq.
     _nonce_uniqueness_preserved_by_send2 s s' lid.session lid.party lid.peer
       initiator_nonce responder_nonce responder_key;
     // The freshly created responder session (responder lid.party, initiator lid.peer).
     ma_sim_send_message2_state_get_updated_sim_participant_session_state
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
       lid.party lid.session;
     unfold_ma_sim_responder_session_state (s2p_state s') lid.party lid.session;
     assert (matches_responder_state s' lid.session lid.party lid.peer responder_nonce);
     // Backward session preservation modulo the fresh nonce.
     introduce forall (sess: session_id) (p q: participant_id) (n: nonce).
       (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
       ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
        ~(Set.mem n s.internal.used_nonces))
     with introduce _ ==> _ with _hc.
       (ma_sim_send_message2_state_get_updated_sim_participant_session_state
          (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key p sess;
        unfold_ma_sim_initiator_session_state (s2p_state s) p sess;
        unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
        unfold_ma_sim_responder_session_state (s2p_state s) p sess;
        unfold_ma_sim_responder_session_state (s2p_state s') p sess);
     // Responder-specific backward preservation (consumed by the C_msg2key helper).
     introduce forall (sess: session_id) (p initiator: participant_id) (mr: nonce).
       matches_responder_state s' sess p initiator mr ==>
       (matches_responder_state s sess p initiator mr \/ ~(Set.mem mr s.internal.used_nonces))
     with introduce _ ==> _ with _hb.
       (ma_sim_send_message2_state_get_updated_sim_participant_session_state
          (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key p sess;
        unfold_ma_sim_responder_session_state (s2p_state s) p sess;
        unfold_ma_sim_responder_session_state (s2p_state s') p sess);
     // The emitted Message2 is encrypted to the initiator `lid.peer`'s directory key.
     _enabled2_dir s lid.session lid.party lid.peer
       initiator_nonce responder_nonce responder_key initiator_pubkey;
     // C_msg1 (new index): Message2 is never Message1-shaped — vacuous.
     introduce forall (sess: session_id) (m: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) kk == t /\
       ma_is_honest_session_nonce corrupt s' m ==> not (Set.mem p corrupt)
     with introduce _ ==> _ with _ht. ();
     _honest_msg1_preserved_snoc corrupt s s' t;
     // C_msg2 (new index): the appended Message2 names lid.party (the responder of
     // the just-created session); if it carries a protected responder nonce mr, then
     // mr = responder_nonce, whose unique responder session is both-honest, so
     // lid.party is non-corrupt.
     introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
       ma_is_honest_session_nonce corrupt s' mr ==> not (Set.mem p corrupt)
     with introduce _ ==> _ with _ht.
       (eliminate exists (sess1: session_id) (a1 b1: participant_id).
          (matches_initiator_state s' sess1 a1 b1 mr \/ matches_responder_state s' sess1 a1 b1 mr) /\
          not (Set.mem a1 corrupt) /\ not (Set.mem b1 corrupt)
        returns not (Set.mem p corrupt)
        with _hw.
          (assert (matches_responder_state s' lid.session lid.party lid.peer responder_nonce);
           assert (a1 == lid.party)));
     _honest_msg2_preserved_snoc corrupt s s' t;
     // C_msg2key (new index): the Message2 is encrypted to the initiator lid.peer's
     // directory key, and its responder session fixes the initiator to lid.peer.
     introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
       ma_is_honest_session_nonce corrupt s' mr ==>
       (forall (initiator: participant_id).
          matches_responder_state s' sess p initiator mr ==>
          PartialMap.sel s'.internal.key_directory initiator == Some kk)
     with introduce _ ==> _ with _ht.
       (introduce forall (initiator: participant_id).
          matches_responder_state s' sess p initiator mr ==>
          PartialMap.sel s'.internal.key_directory initiator == Some kk
        with introduce _ ==> _ with _hi.
          (// equality fixes sess = lid.session, mr = responder_nonce, p = lid.party,
           // kk = k; responder-session functionality fixes initiator = lid.peer.
           unfold_ma_sim_responder_session_state (s2p_state s') p sess));
     _honest_carrier_shallow_preserved_snoc corrupt s s' t;
     _honest_msg2key_preserved_snoc corrupt s s' t)
#pop-options

/// Knowledge-structure invariant preservation for the send3 Observable step.
/// send3 flips only the `ack_sent` bit of an existing initiator session, so no
/// new session is created and all stored nonces are unchanged.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 400"
private
let _structure_send3
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_honest_msg2_key_matches_initiator corrupt s /\
        ma_honest_carrier_shallow corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_session_nonces_unique s' /\
        ma_honest_msg1_names_non_corrupt corrupt s' /\
        ma_honest_msg2_names_non_corrupt corrupt s' /\
        ma_honest_msg2_key_matches_initiator corrupt s' /\
        ma_honest_carrier_shallow corrupt s') =
  eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns
    ma_session_nonces_unique s' /\
    ma_honest_msg1_names_non_corrupt corrupt s' /\
    ma_honest_msg2_names_non_corrupt corrupt s' /\
    ma_honest_msg2_key_matches_initiator corrupt s' /\
    ma_honest_carrier_shallow corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
     assert (t == Aenc (Pair (SessionId lid.session) (Nonce responder_nonce)) k);
     ma_sim_send_message3_state_preserves_used_nonces
       (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key;
     assert (s'.internal.key_directory == s.internal.key_directory);
     assert (shallow_aenc t);
     _nonce_uniqueness_preserved_by_subset_sessions s s';
     // No new session: backward session preservation (matches s' ⟹ matches s).
     introduce forall (sess: session_id) (p q: participant_id) (n: nonce).
       (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
       ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
        ~(Set.mem n s.internal.used_nonces))
     with introduce _ ==> _ with _hc.
       (ma_sim_send_message3_state_get_updated_sim_participant_session_state
          (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key p sess;
        unfold_ma_sim_initiator_session_state (s2p_state s) p sess;
        unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
        ma_sim_send_message3_state_get_updated_sim_responder_session_state
          (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key p sess;
        unfold_ma_sim_responder_session_state (s2p_state s) p sess;
        unfold_ma_sim_responder_session_state (s2p_state s') p sess);
     // Responder-specific backward preservation (consumed by the C_msg2key helper).
     introduce forall (sess: session_id) (p initiator: participant_id) (mr: nonce).
       matches_responder_state s' sess p initiator mr ==>
       (matches_responder_state s sess p initiator mr \/ ~(Set.mem mr s.internal.used_nonces))
     with introduce _ ==> _ with _hb.
       (ma_sim_send_message3_state_get_updated_sim_responder_session_state
          (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key p sess;
        unfold_ma_sim_responder_session_state (s2p_state s) p sess;
        unfold_ma_sim_responder_session_state (s2p_state s') p sess);
     // C_msg1/C_msg2/C_msg2key (new index): Message3 is neither Message1- nor
     // Message2-shaped, so the new-index hypotheses are vacuous.
     introduce forall (sess: session_id) (m: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) kk == t /\
       ma_is_honest_session_nonce corrupt s' m ==> not (Set.mem p corrupt)
     with introduce _ ==> _ with _ht. ();
     _honest_msg1_preserved_snoc corrupt s s' t;
     introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
       ma_is_honest_session_nonce corrupt s' mr ==> not (Set.mem p corrupt)
     with introduce _ ==> _ with _ht. ();
     _honest_msg2_preserved_snoc corrupt s s' t;
     introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
       Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
       ma_is_honest_session_nonce corrupt s' mr ==>
       (forall (initiator: participant_id).
          matches_responder_state s' sess p initiator mr ==>
          PartialMap.sel s'.internal.key_directory initiator == Some kk)
     with introduce _ ==> _ with _ht. ();
     _honest_carrier_shallow_preserved_snoc corrupt s s' t;
     _honest_msg2key_preserved_snoc corrupt s s' t)
#pop-options

/// Knowledge-structure invariant preservation for the deliver Observable step.
/// deliver only edits the sim→ideal channel, leaving the session map untouched;
/// the appended authenticated term is Aenc-free.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 300"
private
let _structure_deliver
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_session_nonces_unique s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_honest_msg2_key_matches_initiator corrupt s /\
        ma_honest_carrier_shallow corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures
        ma_session_nonces_unique s' /\
        ma_honest_msg1_names_non_corrupt corrupt s' /\
        ma_honest_msg2_names_non_corrupt corrupt s' /\
        ma_honest_msg2_key_matches_initiator corrupt s' /\
        ma_honest_carrier_shallow corrupt s') =
  assert (t == ma_authenticated_term lid.session lid.party lid.peer);
  assert (s'.internal.key_directory == s.internal.key_directory);
  // The session map is unchanged by deliver, so matches_* coincide on s and s'.
  introduce forall (sess: session_id) (p q: participant_id) (n: nonce).
    (matches_initiator_state s' sess p q n \/ matches_responder_state s' sess p q n) ==>
    ((matches_initiator_state s sess p q n \/ matches_responder_state s sess p q n) \/
     ~(Set.mem n s.internal.used_nonces))
  with introduce _ ==> _ with _hc.
    (unfold_ma_sim_initiator_session_state (s2p_state s) p sess;
     unfold_ma_sim_initiator_session_state (s2p_state s') p sess;
     unfold_ma_sim_responder_session_state (s2p_state s) p sess;
     unfold_ma_sim_responder_session_state (s2p_state s') p sess);
  // Responder-specific backward preservation (consumed by the C_msg2key helper).
  introduce forall (sess: session_id) (p initiator: participant_id) (mr: nonce).
    matches_responder_state s' sess p initiator mr ==>
    (matches_responder_state s sess p initiator mr \/ ~(Set.mem mr s.internal.used_nonces))
  with introduce _ ==> _ with _hb.
    (unfold_ma_sim_responder_session_state (s2p_state s) p sess;
     unfold_ma_sim_responder_session_state (s2p_state s') p sess);
  assert (shallow_aenc t);
  _nonce_uniqueness_preserved_by_subset_sessions s s';
  // C_msg1/C_msg2/C_msg2key (new index): the authenticated term is a `Pair`
  // (never a Message-shaped `Aenc`), so the new-index hypotheses are vacuous.
  introduce forall (sess: session_id) (m: nonce) (p: participant_id) (kk: priv_key).
    Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) kk == t /\
    ma_is_honest_session_nonce corrupt s' m ==> not (Set.mem p corrupt)
  with introduce _ ==> _ with _ht. ();
  _honest_msg1_preserved_snoc corrupt s s' t;
  introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
    Aenc (Pair (SessionId sess)
           (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
    ma_is_honest_session_nonce corrupt s' mr ==> not (Set.mem p corrupt)
  with introduce _ ==> _ with _ht. ();
  _honest_msg2_preserved_snoc corrupt s s' t;
  introduce forall (sess: session_id) (mi mr: nonce) (p: participant_id) (kk: priv_key).
    Aenc (Pair (SessionId sess)
           (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) kk == t /\
    ma_is_honest_session_nonce corrupt s' mr ==>
    (forall (initiator: participant_id).
       matches_responder_state s' sess p initiator mr ==>
       PartialMap.sel s'.internal.key_directory initiator == Some kk)
  with introduce _ ==> _ with _ht. ();
  _honest_carrier_shallow_preserved_snoc corrupt s s' t;
  _honest_msg2key_preserved_snoc corrupt s s' t
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let ma_ideal_core_inv_init corrupt key_directory know0 =
  let s0 = (ma_ideal_system corrupt key_directory know0).init in
  // C0: `s2p_state s0` coincides with `ma_ideal_protocol_init`.
  ma_ideal_state_inv_init key_directory corrupt know0;
  // C_kd / C_corrupt / C2 / C3: directory/corrupt set are fixed, input bag empty.
  assert (ma_key_directory_matches key_directory s0);
  assert (ma_corrupt_set_matches corrupt s0);
  assert (ma_ideal_inputs_derivable s0);
  assert (s0.know == know0);
  assert (ma_private_keys_not_derivable corrupt key_directory s0);
  // C_fresh: the initial `used_nonces` is exactly `ma_knowledge_nonces know0`, the
  // input bag and the simulator session map are empty.
  assert (s0.internal.used_nonces == ma_knowledge_nonces know0);
  _subset_refl (ma_knowledge_nonces s0.know);
  assert (ma_ideal_used_nonces_invariant s0);
  // C4i / C4r: stored-nonce secrecy holds vacuously (no stored sessions).
  assert (ma_valid_initiator_nonces_not_derivable corrupt s0);
  assert (ma_valid_responder_nonces_not_derivable corrupt s0);
  // C_uniq: session nonce uniqueness holds vacuously (no stored sessions).
  assert (ma_session_nonces_unique s0);
  // C_msg1/C_msg2/C_msg2key: hold vacuously — there are no stored sessions, so no
  // nonce is a protected session nonce (`ma_is_honest_session_nonce` is always
  // false), and every clause is conditioned on a protected nonce.
  assert (ma_honest_msg1_names_non_corrupt corrupt s0);
  assert (ma_honest_msg2_names_non_corrupt corrupt s0);
  assert (ma_honest_msg2_key_matches_initiator corrupt s0);
  assert (ma_honest_carrier_shallow corrupt s0)
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60 --split_queries always"
let ma_ideal_core_inv_preserved corrupt key_directory know0 s s' l =
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns ma_ideal_core_inv corrupt key_directory s'
    with _pf.
      // C0: `internal` unchanged. C2: `t` derivable, prior inputs stay derivable.
      // C_kd / C3: `know`/`internal` unchanged. C_fresh: `_freshness_input`.
      // C4: `internal` unchanged ⟹ identical sessions ⟹ stored-nonce secrecy transfers.
      (assert (derivable s.know t);
       ma_ideal_state_inv_frame (s2p_state s) (s2p_state s');
       assert (forall (u: term). Bag.mem u s'.inputs ==> derivable s'.know u);
       _freshness_input s s' d t;
       assert (forall (sess: session_id) (p q: participant_id) (nn: nonce).
                 matches_initiator_state s' sess p q nn ==> matches_initiator_state s sess p q nn);
       assert (forall (sess: session_id) (p q: participant_id) (nn: nonce).
                 matches_responder_state s' sess p q nn ==> matches_responder_state s sess p q nn);
       _know_unchanged_preserves_valid_nonces corrupt s s')
  | Internal lid ->
    ma_ideal_state_inv_preserved
      (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    ma_ideal_valid_transitions
      (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    _protocol_transition_preserves_key_directory
      (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    assert (s'.know == s.know);
    introduce forall (u: term). Bag.mem u s'.inputs ==> derivable s'.know u
    with introduce _ ==> _ with _hu.
      Bag.subset_mem u s'.inputs s.inputs;
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns ma_ideal_core_inv corrupt key_directory s'
    with _hi.
      // initiate leaves the simulator session map unchanged (SMTPat), so stored
      // nonces transfer; `_freshness_initiate` re-establishes freshness.
      (_freshness_initiate s s' lid;
       assert (forall (sess: session_id) (p q: participant_id) (nn: nonce).
                 matches_initiator_state s' sess p q nn ==> matches_initiator_state s sess p q nn);
       assert (forall (sess: session_id) (p q: participant_id) (nn: nonce).
                 matches_responder_state s' sess p q nn ==> matches_responder_state s sess p q nn);
       _know_unchanged_preserves_valid_nonces corrupt s s')
    and _hr.
      (match lid.role with
       | Responder ->
         eliminate exists (responder_key: priv_key).
           ma_sim_receive_message3_enabled
             (s2p_state s) lid.session lid.party lid.peer responder_key /\
           s2p_state s' ==
             ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
         returns ma_ideal_core_inv corrupt key_directory s'
         with _he.
           // recv3 only flips a responder session's `output_forwarded` bit (nonce
           // unchanged, SMTPat), so stored nonces transfer.
           (assert (Some? (ma_sim_responder_session_state (s2p_state s) lid.party lid.session));
            _freshness_receive3 s s' lid;
            assert (forall (sess: session_id) (p q: participant_id) (nn: nonce).
                      matches_initiator_state s' sess p q nn ==> matches_initiator_state s sess p q nn);
            assert (forall (sess: session_id) (p q: participant_id) (nn: nonce).
                      matches_responder_state s' sess p q nn ==> matches_responder_state s sess p q nn);
            _know_unchanged_preserves_valid_nonces corrupt s s')
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns ma_ideal_core_inv corrupt key_directory s'
    with _pf.
      // C0 / C2 / C_kd as before; C3 + C4 via `_obs_*_secrecy`; C_fresh via `_freshness_*`.
      (ma_ideal_state_inv_preserved
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       introduce forall (u: term). Bag.mem u s'.inputs ==> derivable s'.know u
       with introduce _ ==> _ with _hu.
         Bag.subset_mem u s'.inputs s.inputs;
       _protocol_transition_preserves_key_directory
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       (match o with
        | NetSend ->
          (match lid.role with
           | Initiator ->
             eliminate
               ma_sim_send_message1_protocol_transition
                 (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
               \/ ma_sim_send_message3_protocol_transition
                 (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
             returns
               ma_private_keys_not_derivable corrupt key_directory s' /\
               ma_valid_initiator_nonces_not_derivable corrupt s' /\
               ma_valid_responder_nonces_not_derivable corrupt s' /\
               ma_ideal_used_nonces_invariant s' /\
               ma_session_nonces_unique s' /\
               ma_honest_msg1_names_non_corrupt corrupt s' /\
               ma_honest_msg2_names_non_corrupt corrupt s' /\
               ma_honest_msg2_key_matches_initiator corrupt s' /\
               ma_honest_carrier_shallow corrupt s'
             with _h1.
               (_obs_send1_secrecy corrupt key_directory s s' lid t;
                _freshness_send1 s s' lid t;
                _structure_send1 corrupt s s' lid t)
             and _h3.
               (_obs_send3_secrecy corrupt key_directory s s' lid t;
                _freshness_send3 s s' lid t;
                _structure_send3 corrupt s s' lid t)
           | Responder ->
             _obs_send2_secrecy corrupt key_directory s s' lid t;
             _freshness_send2 s s' lid t;
             _structure_send2 corrupt s s' lid t)
        | IoSend ->
          _obs_deliver_secrecy corrupt key_directory s s' lid t;
          _freshness_deliver s s' lid t;
          _structure_deliver corrupt s s' lid t))
#pop-options

/// ===========================================================================
/// Message2 provenance and the derivable-Message2 authentication clause.
/// ===========================================================================

/// --- Structural facts about the Message2 ciphertext -------------------------
///
/// `ma_nsl_message2_term i a b ni nr (PubKey ik)
///    = Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr)
///             (ParticipantId b)))) ik`.
/// The plaintext shape differs from every other emitted term, so a Message2
/// ciphertext is never (syntactically) equal to a Message1/Message3 ciphertext
/// or to the public authenticated term; and equality of two Message2
/// ciphertexts forces their term arguments (session id, both nonces, responder
/// identity, and encryption key) to agree.

#push-options "--fuel 8 --ifuel 2"

private
let _msg2_neq_msg1
      (i: session_id) (a b: participant_id) (ni nr: nonce) (pk: term{PubKey? pk})
      (j: session_id) (c e: participant_id) (mi: nonce) (rpk: term{PubKey? rpk})
    : Lemma
      (~(ma_nsl_message2_term i a b ni nr pk == ma_nsl_message1_term j c e mi rpk)) =
  ()

private
let _msg2_neq_msg3
      (i: session_id) (a b: participant_id) (ni nr: nonce) (pk: term{PubKey? pk})
      (j: session_id) (c e: participant_id) (mr: nonce) (rpk: term{PubKey? rpk})
    : Lemma
      (~(ma_nsl_message2_term i a b ni nr pk == ma_nsl_message3_term j c e mr rpk)) =
  ()

/// Equality of two Message2 ciphertexts forces the session id, both nonces, the
/// responder identity, and the encryption key to agree.
private
let _msg2_eq_args
      (i: session_id) (a b: participant_id) (ni nr: nonce) (pk: term{PubKey? pk})
      (j: session_id) (c e: participant_id) (mi mr: nonce) (qk: term{PubKey? qk})
    : Lemma
      (requires
        ma_nsl_message2_term i a b ni nr pk == ma_nsl_message2_term j c e mi mr qk)
      (ensures
        i == j /\ ni == mi /\ nr == mr /\ b == e /\
        PubKey?.priv pk == PubKey?.priv qk) =
  let px = Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId b))) in
  let py = Pair (SessionId j) (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId e))) in
  assert (ma_nsl_message2_term i a b ni nr pk == Aenc px (PubKey?.priv pk));
  assert (ma_nsl_message2_term j c e mi mr qk == Aenc py (PubKey?.priv qk))

#pop-options

/// --- Non-forgeability of a derivable Message2 ciphertext --------------------
///
/// A Message2 ciphertext is `Aenc plaintext ik` whose plaintext carries the
/// secret nonces.  When such a ciphertext is `built_with_subterms` from the
/// previous knowledge and a set of `subterms` that contains no bare nonce and no
/// pair, the ciphertext could not have been reconstructed: it is either already
/// derivable from the previous knowledge, or it is itself one of the `subterms`
/// Knowledge-growth monotonicity (contrapositive): if `Nonce n` is not derivable
/// from the extended knowledge `snoc s.know x`, it was not derivable from `s.know`.
/// Used to push the provenance-clause antecedent `~(derivable s'.know (Nonce ·))`
/// (about the *post*-state) back to the pre-state `s.know` consumed by
/// `_msg2_built_elim` / `_msg3_built_elim`.
private
let _nonce_not_derivable_snoc
      (s s': ideal_system_state) (x: term) (n: nonce)
    : Lemma
      (requires s'.know == Seq.snoc s.know x /\ ~(derivable s'.know (Nonce n)))
      (ensures ~(derivable s.know (Nonce n))) =
  let aux () : Lemma (requires derivable s.know (Nonce n)) (ensures False) =
    append_preserves_derivable s.know (Seq.create 1 x) (Nonce n);
    assert (Seq.snoc s.know x == Seq.append s.know (Seq.create 1 x))
  in
  FStar.Classical.move_requires aux ()

/// A nonce occurring in a Message2 (resp. Message3) ciphertext that is derivable
/// from `s.know` is necessarily a *used* nonce: it occurs syntactically in the
/// knowledge (`ma_derive_term_nonces_in_knowledge_nonces`), and the freshness
/// invariant `ma_knowledge_nonces_are_used` bounds the knowledge nonces by
/// `used_nonces`.  This is what lets the provenance preservation invoke the
/// backward (used-nonce) session-recovery lemmas `_minit_back` / `_mresp_back`.
#push-options "--fuel 6 --ifuel 2"
private
let _msg2_nonce_used
      (s: ideal_system_state)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key) (d: derivation)
    : Lemma
      (requires
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        derive d s.know = Some (ma_nsl_message2_term i a b ni nr (PubKey ik)))
      (ensures Set.mem ni s.internal.used_nonces) =
  let msg2 = ma_nsl_message2_term i a b ni nr (PubKey ik) in
  ma_derive_term_nonces_in_knowledge_nonces s.know d msg2;
  assert (Set.mem ni (ma_term_nonces msg2));
  Set.subset_mem (ma_term_nonces msg2) (ma_knowledge_nonces s.know);
  Set.subset_mem (ma_knowledge_nonces s.know) s.internal.used_nonces
#pop-options

#push-options "--fuel 6 --ifuel 2"
private
let _msg3_nonce_used
      (s: ideal_system_state)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key) (d: derivation)
    : Lemma
      (requires
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        derive d s.know = Some (ma_nsl_message3_term i a b nr (PubKey pk)))
      (ensures Set.mem nr s.internal.used_nonces) =
  let msg3 = ma_nsl_message3_term i a b nr (PubKey pk) in
  ma_derive_term_nonces_in_knowledge_nonces s.know d msg3;
  assert (Set.mem nr (ma_term_nonces msg3));
  Set.subset_mem (ma_term_nonces msg3) (ma_knowledge_nonces s.know);
  Set.subset_mem (ma_knowledge_nonces s.know) s.internal.used_nonces
#pop-options

/// (an observed term).  The decomposition case is impossible because it would
/// require building the inner `Nonce ni`, which is neither derivable (the
/// `~(derivable s.know (Nonce ni))` hypothesis, supplied by the caller from the
/// provenance-clause antecedent) nor a member of `subterms`.
#push-options "--fuel 4 --ifuel 2"
private
let _msg2_built_elim
      (s: ideal_system_state)
      (subterms: Set.set term)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key)
    : Lemma
      (requires
        ~(derivable s.know (Nonce ni)) /\
        (forall (n: nonce). ~(Set.mem (Nonce n) subterms)) /\
        (forall (l r: term). ~(Set.mem (Pair l r) subterms)) /\
        built_with_subterms s.know subterms (ma_nsl_message2_term i a b ni nr (PubKey ik)))
      (ensures
        derivable s.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) \/
        Set.mem (ma_nsl_message2_term i a b ni nr (PubKey ik)) subterms) =
  let msg2 = ma_nsl_message2_term i a b ni nr (PubKey ik) in
  let r2 = Pair (Nonce nr) (ParticipantId b) in
  let r1 = Pair (Nonce ni) r2 in
  let plaintext = Pair (SessionId i) r1 in
  assert (msg2 == Aenc plaintext ik);
  let contra ()
      : Lemma (requires ~(derivable s.know msg2) /\ ~(Set.mem msg2 subterms)) (ensures False) =
    built_from_subterms_aenc_components s.know subterms plaintext ik;
    built_from_subterms_pair_right s.know subterms (SessionId i) r1;
    built_from_subterms_pair_left s.know subterms (Nonce ni) r2;
    built_from_subterms_nonce_derivable s.know subterms ni;
    assert (derivable s.know (Nonce ni))
  in
  FStar.Classical.move_requires contra ()
#pop-options

/// --- Preservation of responder-session matching across transitions ----------

unfold
let _resp_pres (s s': ideal_system_state) : prop =
  s'.internal.key_directory == s.internal.key_directory /\
  (forall (i: session_id) (b a: participant_id) (nr: nonce).
    matches_responder_state s i b a nr ==> matches_responder_state s' i b a nr)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _responder_matches_preserved_transition
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures _resp_pres s s') =
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns _resp_pres s s'
    with _pf.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s')))
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns _resp_pres s s'
    with _hi.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s')))
    and _hr.
      (match lid.role with
       | Responder ->
         eliminate exists (responder_key: priv_key).
           ma_sim_receive_message3_enabled
             (s2p_state s) lid.session lid.party lid.peer responder_key /\
           s2p_state s' ==
             ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
         returns _resp_pres s s'
         with _he.
           (assert (Some? (ma_sim_responder_session_state (s2p_state s) lid.party lid.session));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s')))
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns _resp_pres s s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns _resp_pres s s'
            with _h1.
              (eliminate exists (initiator_nonce: nonce)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message1_enabled
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 t == ma_nsl_message1_term
                   lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message1_state
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce
               returns _resp_pres s s'
               with _he.
                 (FStar.Classical.forall_intro_2
                    (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce);
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
            and _h3.
              (eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message3_enabled
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
                 t == ma_nsl_message3_term
                   lid.session lid.party lid.peer responder_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message3_state
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
               returns _resp_pres s s'
               with _he.
                 (assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
          | Responder ->
            eliminate exists (initiator_nonce responder_nonce: nonce)
                             (responder_key: priv_key)
                             (initiator_pubkey: term {PubKey? initiator_pubkey}).
              ma_sim_send_message2_enabled
                (s2p_state s) lid.session lid.party lid.peer
                initiator_nonce responder_nonce responder_key initiator_pubkey /\
              t == ma_nsl_message2_term
                lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
              s2p_state s' == ma_sim_send_message2_state
                (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
            returns _resp_pres s s'
            with _he.
              (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
               FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
       | IoSend ->
         (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
          FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
#pop-options

/// --- Backward (used-nonce) recovery of initiator-session matching -----------
///
/// The provenance preservation proof needs to invoke the inductive hypothesis
/// (provenance at the pre-state `s`), whose antecedent is now
/// `matches_initiator_state s …`.  At the post-state `s'` we only have
/// `matches_initiator_state s' …`.  These differ only when the session was just
/// created (by a Message1 send), in which case its nonce is *fresh*
/// (`ma_sim_nonce_is_fresh`, hence ∉ `used_nonces s`).  So whenever the nonce is
/// already a *used* nonce of `s`, the matching session must have existed at `s`.
/// This is the freshness-based argument that lets the weakened provenance clause
/// stay inductive without any assumption on the adversary's initial knowledge.
unfold
let _minit_back (s s': ideal_system_state) : prop =
  forall (i: session_id) (a b: participant_id) (ni: nonce).
    matches_initiator_state s' i a b ni /\ Set.mem ni s.internal.used_nonces ==>
    matches_initiator_state s i a b ni

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
private
let _initiator_matches_back_transition
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures _minit_back s s') =
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns _minit_back s s'
    with _pf.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s')))
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns _minit_back s s'
    with _hi.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s')))
    and _hr.
      (match lid.role with
       | Responder ->
         eliminate exists (responder_key: priv_key).
           ma_sim_receive_message3_enabled
             (s2p_state s) lid.session lid.party lid.peer responder_key /\
           s2p_state s' ==
             ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
         returns _minit_back s s'
         with _he.
           (assert (Some? (ma_sim_responder_session_state (s2p_state s) lid.party lid.session));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s')))
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns _minit_back s s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns _minit_back s s'
            with _h1.
              (eliminate exists (initiator_nonce: nonce)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message1_enabled
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 t == ma_nsl_message1_term
                   lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message1_state
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce
               returns _minit_back s s'
               with _he.
                 (// the freshly created initiator session uses a fresh nonce, so a
                  // *used* nonce cannot belong to the new session: it existed at `s`.
                  assert (not (Set.mem initiator_nonce s.internal.used_nonces));
                  FStar.Classical.forall_intro_2
                    (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce);
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
            and _h3.
              (eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message3_enabled
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
                 t == ma_nsl_message3_term
                   lid.session lid.party lid.peer responder_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message3_state
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
               returns _minit_back s s'
               with _he.
                 (assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
          | Responder ->
            eliminate exists (initiator_nonce responder_nonce: nonce)
                             (responder_key: priv_key)
                             (initiator_pubkey: term {PubKey? initiator_pubkey}).
              ma_sim_send_message2_enabled
                (s2p_state s) lid.session lid.party lid.peer
                initiator_nonce responder_nonce responder_key initiator_pubkey /\
              t == ma_nsl_message2_term
                lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
              s2p_state s' == ma_sim_send_message2_state
                (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
            returns _minit_back s s'
            with _he.
              (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
               FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
       | IoSend ->
         (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
          FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
#pop-options

/// Bridges stored-nonce secrecy to the `~(derivable …)` form required by the
/// provenance-clause antecedents: a nonce stored in a matching initiator
/// (resp. responder) session is not adversary-derivable.
private
let _matches_initiator_implies_not_derivable
      (corrupt: Set.set participant_id)
      (s: ideal_system_state) (sess: session_id) (p q: participant_id) (nn: nonce)
    : Lemma
      (requires ma_valid_initiator_nonces_not_derivable corrupt s /\
                matches_initiator_state s sess p q nn /\
                not (Set.mem p corrupt) /\
                not (Set.mem q corrupt))
      (ensures ~(derivable s.know (Nonce nn))) =
  let aux () : Lemma (requires derivable s.know (Nonce nn)) (ensures False) =
    eliminate exists (d: adv.derivation). derive d s.know = Some (Nonce nn)
    returns False
    with _hd. (assert (adv.derive d s.know == derive d s.know) by (FStar.Tactics.trefl ()))
  in
  FStar.Classical.move_requires aux ()

private
let _matches_responder_implies_not_derivable
      (corrupt: Set.set participant_id)
      (s: ideal_system_state) (sess: session_id) (p q: participant_id) (nn: nonce)
    : Lemma
      (requires ma_valid_responder_nonces_not_derivable corrupt s /\
                matches_responder_state s sess p q nn /\
                not (Set.mem p corrupt) /\
                not (Set.mem q corrupt))
      (ensures ~(derivable s.know (Nonce nn))) =
  let aux () : Lemma (requires derivable s.know (Nonce nn)) (ensures False) =
    eliminate exists (d: adv.derivation). derive d s.know = Some (Nonce nn)
    returns False
    with _hd. (assert (adv.derive d s.know == derive d s.know) by (FStar.Tactics.trefl ()))
  in
  FStar.Classical.move_requires aux ()

/// --- Transfer of provenance for a Message2 derivable from the old knowledge --
private
let _m2_transfer_old
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key)
    : Lemma
      (requires
        ma_message2_provenance corrupt s /\
        matches_initiator_state s i a b ni /\
        PartialMap.sel s.internal.key_directory a == Some ik /\
        derivable s.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        _resp_pres s s')
      (ensures matches_responder_state s' i b a nr) =
  // provenance at `s` yields the responder match, which is forward-preserved
  assert (matches_responder_state s i b a nr)

/// --- New occurrence introduced by a Message2 send ---------------------------
/// The derivable Message2 ciphertext is the very term `t` just emitted by the
/// Message2 send, so its arguments coincide with the fresh responder session's.
private
let _m2_new_occurrence_send2
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (lid: ma_label_id) (t: term)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.internal.key_directory == s.internal.key_directory /\
        // the (pinned) provenance-clause antecedent for the emitted Message2
        matches_initiator_state s' i a b ni /\
        PartialMap.sel s'.internal.key_directory a == Some ik /\
        ma_nsl_message2_term i a b ni nr (PubKey ik) == t)
      (ensures matches_responder_state s' i b a nr) =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns matches_responder_state s' i b a nr
  with _he.
    (// equality with the emitted Message2 forces the (non-vacuous) term arguments
     // to agree: session, responder identity `b`, responder nonce, and key.
     _msg2_eq_args i a b ni nr (PubKey ik)
       lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey;
     assert (i == lid.session);
     assert (nr == responder_nonce);
     assert (b == lid.party);
     assert (ik == PubKey?.priv initiator_pubkey);
     // send2 enabling: the believed initiator `lid.peer` owns key `ik`
     assert (PartialMap.sel s.internal.key_directory lid.peer
               == Some (PubKey?.priv initiator_pubkey));
     assert (PartialMap.sel s'.internal.key_directory lid.peer == Some ik);
     // pin `a = lid.peer` via directory injectivity (both own key `ik`)
     assert (s'.internal.key_directory == key_directory);
     assert (a == lid.peer);
     // the freshly created responder session matches
     unfold_ma_sim_responder_session_state (s2p_state s') lid.party lid.session;
     assert (matches_responder_state s' lid.session lid.party lid.peer responder_nonce))

/// --- The pointwise authenticity consequence of Message2 provenance ----------
/// (Public; declared in the interface as `ma_message2_provenance_matches_responder`.)
let ma_message2_provenance_matches_responder
      corrupt key_directory s session initiator responder
      initiator_nonce responder_nonce initiator_key d =
  // the network Message2 is derivable, hence so is its ciphertext component
  let net = ma_nsl_message2_network_term session initiator responder
              initiator_nonce responder_nonce (PubKey initiator_key) in
  let msg2 = ma_nsl_message2_term session initiator responder
               initiator_nonce responder_nonce (PubKey initiator_key) in
  assert (net == Pair (Data (data_of_string "NetInput")) msg2);
  assert (adv.derive d s.know == derive d s.know) by (FStar.Tactics.trefl ());
  assert (derivable s.know net);
  derivable_pair_right s.know (Data (data_of_string "NetInput")) msg2;
  assert (derivable s.know msg2);
  // The matching initiator session and `initiator`'s directory key discharge the
  // provenance-clause antecedent directly (with a = initiator, b = responder), so
  // provenance yields the responder match with no re-identification needed.
  assert (matches_initiator_state s session initiator responder initiator_nonce);
  assert (PartialMap.sel s.internal.key_directory initiator == Some initiator_key)

/// --- Message2 provenance is preserved by every transition -------------------

/// Core reduction for an `Observable` step that emits a session ciphertext
/// `t = Aenc (Pair (SessionId session) m) k` under an unguessable key `k`.  By
/// `derivable_from_session_encrypted_term_without_key`, any Message2 derivable
/// from `s'.know = snoc s.know t` is `built_with_subterms` from `s.know` and the
/// singleton `{t}`.  `_msg2_built_elim` then reduces that to: either the Message2
/// was already derivable from `s.know` (old provenance transfers), or it equals
/// the emitted `t` (handled by the caller-supplied implication).
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m2_obs_session_send
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (session: session_id) (m: term) (k: priv_key) (t: term)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key)
    : Lemma
      (requires
        matches_initiator_state s' i a b ni /\
        PartialMap.sel s'.internal.key_directory a == Some ik /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        ~(derivable s.know (PrivKey k)) /\
        t == Aenc (Pair (SessionId session) m) k /\
        s'.know == Seq.snoc s.know t /\
        derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
        ((ma_nsl_message2_term i a b ni nr (PubKey ik) == t) ==>
          matches_responder_state s' i b a nr))
      (ensures matches_responder_state s' i b a nr) =
  let msg2 = ma_nsl_message2_term i a b ni nr (PubKey ik) in
  // the matching initiator nonce is not adversary-derivable
  _matches_initiator_implies_not_derivable corrupt s' i a b ni;
  _nonce_not_derivable_snoc s s' t ni;
  let subterms = Set.as_set [t] in
  assert (exists (d2: derivation). derive d2 s'.know = Some msg2);
  eliminate exists (d2: derivation). derive d2 s'.know = Some msg2
  returns matches_responder_state s' i b a nr
  with _hd2.
    (derivable_from_session_encrypted_term_without_key s.know session m k d2 msg2;
     assert (built_with_subterms s.know subterms msg2);
     assert (forall (n: nonce). ~(Set.mem (Nonce n) subterms));
     assert (forall (l r: term). ~(Set.mem (Pair l r) subterms));
     _msg2_built_elim s subterms i a b ni nr ik;
     eliminate (derivable s.know msg2) \/ (Set.mem msg2 subterms)
     returns matches_responder_state s' i b a nr
     with _hd.
       (// Message2 was already derivable from the old knowledge: its nonce `ni`
        // is therefore a used nonce, so the matching initiator session existed at
        // `s` (a freshly created session would have an unused nonce), and old
        // provenance transfers.
        eliminate exists (d3: derivation). derive d3 s.know = Some msg2
        returns matches_responder_state s' i b a nr
        with _hd3.
          (_msg2_nonce_used s i a b ni nr ik d3;
           assert (matches_initiator_state s i a b ni);
           _m2_transfer_old corrupt s s' i a b ni nr ik))
     and _hm. ())
#pop-options

/// Corrupt-peer counterpart of `_m2_obs_session_send`.  When the emitted session
/// ciphertext `t` is encrypted under a *corrupt* peer's key `k`, the adversary
/// can decrypt it, so `derivable_from_session_encrypted_term_without_key` no
/// longer applies.  Instead, an honest Message2 (key `ik ≠ k`, secret nonce `ni`)
/// derivable from `s'.know` is — by `aenc_subterm_in_derived_implies_observed` —
/// *observed*; the shallow/`know0` invariants pin it to `s.know`, so old Message2
/// provenance transfers.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 400"
private
let _m2_obs_session_send_corrupt
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (session: session_id) (m: term) (k: priv_key) (t: term)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key)
    : Lemma
      (requires
        matches_initiator_state s' i a b ni /\
        PartialMap.sel s'.internal.key_directory a == Some ik /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        ik <> k /\
        t == Aenc (Pair (SessionId session) m) k /\
        s'.know == Seq.snoc s.know t /\
        derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)))
      (ensures matches_responder_state s' i b a nr) =
  let msg2 = ma_nsl_message2_term i a b ni nr (PubKey ik) in
  let plaintext2 = Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId b))) in
  assert (msg2 == Aenc plaintext2 ik);
  _matches_initiator_implies_not_derivable corrupt s' i a b ni;
  let pt_extract () : Lemma (requires derivable s'.know plaintext2) (ensures False) =
    derivable_pair_right s'.know (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr) (ParticipantId b)));
    derivable_pair_left s'.know (Nonce ni) (Pair (Nonce nr) (ParticipantId b))
  in
  FStar.Classical.move_requires pt_extract ();
  eliminate exists (d2: adv.derivation). adv.derive d2 s'.know = Some msg2
  returns matches_responder_state s' i b a nr
  with _hd2.
    (assert (adv.derive d2 s'.know == derive d2 s'.know) by (FStar.Tactics.trefl ());
     aenc_subterm_in_derived_implies_observed s'.know plaintext2 ik msg2 d2;
     eliminate exists (idx: nat).
       idx < Seq.length s'.know /\ aenc_subterm msg2 (Seq.index s'.know idx)
     returns matches_responder_state s' i b a nr
     with _hidx.
       (let kt = Seq.index s'.know idx in
        aenc_subterm_nonces_subset msg2 kt;
        assert (Set.mem ni (ma_term_nonces msg2));
        Set.subset_mem (ma_term_nonces msg2) (ma_term_nonces kt);
        assert (Set.mem ni (ma_term_nonces kt));
        // ni is a protected nonce; C_shallow forces its carrier kt to be shallow,
        // so the observed ciphertext kt equals msg2.
        _honest_session_nonce_intro corrupt s' i a b ni;
        _honest_carrier_shallow_at corrupt s' idx ni;
        aenc_subterm_shallow_eq msg2 kt;
        // kt == msg2; since ik ≠ k, msg2 ≠ t, so idx < length s.know
        if idx < Seq.length s.know then
          (Seq.lemma_index_app1 s.know (Seq.create 1 t) idx;
           assert (Seq.index s.know idx == msg2);
           introduce exists (d3: adv.derivation). adv.derive d3 s.know = Some msg2
           with (DeriveObserved idx) and
             (assert (adv.derive (DeriveObserved idx) s.know == derive (DeriveObserved idx) s.know)
               by (FStar.Tactics.trefl ()));
           _msg2_nonce_used s i a b ni nr ik (DeriveObserved idx);
           _m2_transfer_old corrupt s s' i a b ni nr ik)
        else
          (// idx == length s.know ⟹ kt == t, contradicting kt == msg2 ≠ t
           Seq.lemma_index_app2 s.know (Seq.create 1 t) idx;
           Seq.lemma_index_create 1 t (idx - Seq.length s.know))))
#pop-options

/// Core reduction for the `Observable` deliver step that emits the public
/// authenticated term `t`.  By `derivable_from_public_output_term`, any Message2
/// derivable from `snoc s.know t` is `built_with_subterms` from `s.know` and the
/// base-term subterms of `t`; since a Message2 ciphertext is an `Aenc` (never one
/// of those base terms), it must already have been derivable from `s.know`.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m2_obs_deliver
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (session: session_id) (party peer: participant_id) (t: term)
      (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key)
    : Lemma
      (requires
        matches_initiator_state s' i a b ni /\
        PartialMap.sel s'.internal.key_directory a == Some ik /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        t == ma_authenticated_term session party peer /\
        s'.know == Seq.snoc s.know t /\
        derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)))
      (ensures matches_responder_state s' i b a nr) =
  let msg2 = ma_nsl_message2_term i a b ni nr (PubKey ik) in
  _matches_initiator_implies_not_derivable corrupt s' i a b ni;
  _nonce_not_derivable_snoc s s' t ni;
  let subterms = Set.as_set [SessionId session; ParticipantId party; ParticipantId peer] in
  assert (exists (d2: derivation). derive d2 s'.know = Some msg2);
  eliminate exists (d2: derivation). derive d2 s'.know = Some msg2
  returns matches_responder_state s' i b a nr
  with _hd2.
    (derivable_from_public_output_term s.know session party peer d2 msg2;
     assert (built_with_subterms s.know subterms msg2);
     assert (forall (n: nonce). ~(Set.mem (Nonce n) subterms));
     assert (forall (l r: term). ~(Set.mem (Pair l r) subterms));
     _msg2_built_elim s subterms i a b ni nr ik;
     eliminate (derivable s.know msg2) \/ (Set.mem msg2 subterms)
     returns matches_responder_state s' i b a nr
     with _hd.
       (eliminate exists (d3: derivation). derive d3 s.know = Some msg2
        returns matches_responder_state s' i b a nr
        with _hd3.
          (_msg2_nonce_used s i a b ni nr ik d3;
           assert (matches_initiator_state s i a b ni);
           _m2_transfer_old corrupt s s' i a b ni nr ik))
     and _hm. ())
#pop-options

/// Per-send dispatch wrappers.  Each extracts the emitted ciphertext shape and
/// the unguessable encryption key from the send-enabling condition, then reduces
/// to the core helper above.  The "equals the emitted term" branch is vacuous for
/// Message1/Message3 sends (a Message2 ciphertext is structurally distinct) and is
/// supplied by `_m2_new_occurrence_send2` for the Message2 send.

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m2_pres_send1
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message2_provenance corrupt s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns ma_message2_provenance corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     let m = Pair (Nonce initiator_nonce) (ParticipantId lid.party) in
     _enabled1_dir s lid.session lid.party lid.peer initiator_nonce responder_pubkey;
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.internal.key_directory == key_directory);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
       matches_initiator_state s' i a b ni /\
       PartialMap.sel s'.internal.key_directory a == Some ik /\
       derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
       not (Set.mem a corrupt) /\
       not (Set.mem b corrupt) ==>
       matches_responder_state s' i b a nr
     with introduce _ ==> _ with _hd.
       (_msg2_neq_msg1 i a b ni nr (PubKey ik)
          lid.session lid.party lid.peer initiator_nonce responder_pubkey;
        if not (Set.mem lid.peer corrupt) then
          (_directory_key_not_derivable corrupt key_directory s lid.peer k;
           _m2_obs_session_send corrupt s s' lid.session m k t i a b ni nr ik)
        else
          (// a is honest, lid.peer is corrupt, key_directory injective ⟹ ik ≠ k
           assert (PartialMap.sel key_directory a == Some ik);
           assert (ik <> k);
           _m2_obs_session_send_corrupt corrupt s s' lid.session m k t i a b ni nr ik)))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m2_pres_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message2_provenance corrupt s') =
  eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message3_state (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns ma_message2_provenance corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     let m = Nonce responder_nonce in
     _enabled3_dir s lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey;
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.internal.key_directory == key_directory);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
       matches_initiator_state s' i a b ni /\
       PartialMap.sel s'.internal.key_directory a == Some ik /\
       derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
       not (Set.mem a corrupt) /\
       not (Set.mem b corrupt) ==>
       matches_responder_state s' i b a nr
     with introduce _ ==> _ with _hd.
       (_msg2_neq_msg3 i a b ni nr (PubKey ik)
          lid.session lid.party lid.peer responder_nonce responder_pubkey;
        if not (Set.mem lid.peer corrupt) then
          (_directory_key_not_derivable corrupt key_directory s lid.peer k;
           _m2_obs_session_send corrupt s s' lid.session m k t i a b ni nr ik)
        else
          (assert (PartialMap.sel key_directory a == Some ik);
           assert (ik <> k);
           _m2_obs_session_send_corrupt corrupt s s' lid.session m k t i a b ni nr ik)))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m2_pres_send2
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message2_provenance corrupt s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns ma_message2_provenance corrupt s'
  with _he.
    (let k = PubKey?.priv initiator_pubkey in
     let m = Pair (Nonce initiator_nonce)
               (Pair (Nonce responder_nonce) (ParticipantId lid.party)) in
     _enabled2_dir s lid.session lid.party lid.peer
       initiator_nonce responder_nonce responder_key initiator_pubkey;
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.internal.key_directory == key_directory);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
       matches_initiator_state s' i a b ni /\
       PartialMap.sel s'.internal.key_directory a == Some ik /\
       derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
       not (Set.mem a corrupt) /\
       not (Set.mem b corrupt) ==>
       matches_responder_state s' i b a nr
     with introduce _ ==> _ with _hd.
       (if not (Set.mem lid.peer corrupt) then
          (_directory_key_not_derivable corrupt key_directory s lid.peer k;
           introduce (ma_nsl_message2_term i a b ni nr (PubKey ik) == t) ==>
             matches_responder_state s' i b a nr
           with _heq.
             _m2_new_occurrence_send2 key_directory s s' lid t i a b ni nr ik;
           _m2_obs_session_send corrupt s s' lid.session m k t i a b ni nr ik)
        else
          (// a is honest, lid.peer is corrupt, key_directory injective ⟹ ik ≠ k
           assert (PartialMap.sel key_directory a == Some ik);
           assert (ik <> k);
           _m2_obs_session_send_corrupt corrupt s s' lid.session m k t i a b ni nr ik)))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m2_pres_deliver
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_initiator_nonces_not_derivable corrupt s' /\
        _minit_back s s' /\
        ma_message2_provenance corrupt s /\
        _resp_pres s s' /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message2_provenance corrupt s') =
  assert (t == ma_authenticated_term lid.session lid.party lid.peer);
  introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
    matches_initiator_state s' i a b ni /\
    PartialMap.sel s'.internal.key_directory a == Some ik /\
    derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
    not (Set.mem a corrupt) /\
    not (Set.mem b corrupt) ==>
    matches_responder_state s' i b a nr
  with introduce _ ==> _ with _hd.
    _m2_obs_deliver corrupt s s' lid.session lid.party lid.peer t i a b ni nr ik
#pop-options

#push-options "--z3rlimit 20"
private
let _m2_provenance_preserved
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures ma_message2_provenance corrupt s') =
  _responder_matches_preserved_transition corrupt key_directory know0 s s' l;
  // Backward (used-nonce) initiator-session recovery, and stored-nonce secrecy at
  // the post-state, are needed to invoke the inductive hypothesis under the
  // stored-session-conditioned provenance clause.
  _initiator_matches_back_transition corrupt key_directory know0 s s' l;
  ma_ideal_core_inv_preserved corrupt key_directory know0 s s' l;
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns ma_message2_provenance corrupt s'
    with _pf.
      (introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
         matches_initiator_state s' i a b ni /\
         PartialMap.sel s'.internal.key_directory a == Some ik /\
         derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
         not (Set.mem a corrupt) /\
         not (Set.mem b corrupt) ==>
         matches_responder_state s' i b a nr
       with introduce _ ==> _ with _h.
         (// sessions and knowledge are unchanged by an Input step
          assert (matches_initiator_state s i a b ni);
          _m2_transfer_old corrupt s s' i a b ni nr ik))
  | Internal lid ->
    introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
      matches_initiator_state s' i a b ni /\
      PartialMap.sel s'.internal.key_directory a == Some ik /\
      derivable s'.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
      not (Set.mem a corrupt) /\
      not (Set.mem b corrupt) ==>
      matches_responder_state s' i b a nr
    with introduce _ ==> _ with _h.
      (// an Internal step leaves the knowledge unchanged, so the Message2 is
       // already derivable from `s.know`; its nonce is therefore used, and the
       // matching initiator session existed at `s`.
       assert (derivable s.know (ma_nsl_message2_term i a b ni nr (PubKey ik)));
       eliminate exists (d3: derivation).
         derive d3 s.know = Some (ma_nsl_message2_term i a b ni nr (PubKey ik))
       returns matches_responder_state s' i b a nr
       with _hd3.
         (_msg2_nonce_used s i a b ni nr ik d3;
          assert (matches_initiator_state s i a b ni);
          _m2_transfer_old corrupt s s' i a b ni nr ik))
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns ma_message2_provenance corrupt s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns ma_message2_provenance corrupt s'
            with _h1. _m2_pres_send1 corrupt key_directory s s' lid t
            and _h3. _m2_pres_send3 corrupt key_directory s s' lid t
          | Responder -> _m2_pres_send2 corrupt key_directory s s' lid t)
       | IoSend -> _m2_pres_deliver corrupt s s' lid t)
#pop-options

/// ===========================================================================
/// Message3 provenance and the derivable-Message3 authentication clause.
/// ===========================================================================

/// --- Structural facts about the Message3 ciphertext -------------------------
///
/// `ma_nsl_message3_term i a b nr (PubKey pk)
///    = Aenc (Pair (SessionId i) (Nonce nr)) pk`.
/// The plaintext shape differs from every other emitted term, so a Message3
/// ciphertext is never (syntactically) equal to a Message1/Message2 ciphertext
/// or to the public authenticated term; and equality of two Message3
/// ciphertexts forces their session id, responder nonce, and encryption key to
/// agree (the identity arguments are discarded by the constructor).

#push-options "--fuel 8 --ifuel 2"

private
let _msg3_neq_msg1
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: term{PubKey? pk})
      (j: session_id) (c e: participant_id) (mi: nonce) (rpk: term{PubKey? rpk})
    : Lemma
      (~(ma_nsl_message3_term i a b nr pk == ma_nsl_message1_term j c e mi rpk)) =
  ()

private
let _msg3_neq_msg2
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: term{PubKey? pk})
      (j: session_id) (c e: participant_id) (mi mr: nonce) (ipk: term{PubKey? ipk})
    : Lemma
      (~(ma_nsl_message3_term i a b nr pk == ma_nsl_message2_term j c e mi mr ipk)) =
  ()

/// Equality of two Message3 ciphertexts forces the session id, the responder
/// nonce, and the encryption key to agree.
private
let _msg3_eq_args
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: term{PubKey? pk})
      (j: session_id) (c e: participant_id) (mr: nonce) (qk: term{PubKey? qk})
    : Lemma
      (requires
        ma_nsl_message3_term i a b nr pk == ma_nsl_message3_term j c e mr qk)
      (ensures i == j /\ nr == mr /\ PubKey?.priv pk == PubKey?.priv qk) =
  let px = Pair (SessionId i) (Nonce nr) in
  let py = Pair (SessionId j) (Nonce mr) in
  assert (ma_nsl_message3_term i a b nr pk == Aenc px (PubKey?.priv pk));
  assert (ma_nsl_message3_term j c e mr qk == Aenc py (PubKey?.priv qk))

#pop-options

/// --- Non-forgeability of a derivable Message3 ciphertext --------------------
///
/// The Message3 analogue of `_msg2_built_elim`: a Message3 ciphertext
/// `Aenc (Pair (SessionId i) (Nonce nr)) pk` that is `built_with_subterms` from
/// `s.know` and a nonce-free, pair-free `subterms` set is either already
/// derivable from `s.know` or one of the `subterms`.  The decomposition case is
/// ruled out because it would require building the inner `Nonce nr`.
#push-options "--fuel 4 --ifuel 2"
private
let _msg3_built_elim
      (s: ideal_system_state)
      (subterms: Set.set term)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key)
    : Lemma
      (requires
        ~(derivable s.know (Nonce nr)) /\
        (forall (n: nonce). ~(Set.mem (Nonce n) subterms)) /\
        (forall (l r: term). ~(Set.mem (Pair l r) subterms)) /\
        built_with_subterms s.know subterms (ma_nsl_message3_term i a b nr (PubKey pk)))
      (ensures
        derivable s.know (ma_nsl_message3_term i a b nr (PubKey pk)) \/
        Set.mem (ma_nsl_message3_term i a b nr (PubKey pk)) subterms) =
  let msg3 = ma_nsl_message3_term i a b nr (PubKey pk) in
  let plaintext = Pair (SessionId i) (Nonce nr) in
  assert (msg3 == Aenc plaintext pk);
  let contra ()
      : Lemma (requires ~(derivable s.know msg3) /\ ~(Set.mem msg3 subterms)) (ensures False) =
    built_from_subterms_aenc_components s.know subterms plaintext pk;
    built_from_subterms_pair_right s.know subterms (SessionId i) (Nonce nr);
    built_from_subterms_nonce_derivable s.know subterms nr;
    assert (derivable s.know (Nonce nr))
  in
  FStar.Classical.move_requires contra ()
#pop-options

/// --- Functionality of a simulator responder session ------------------------
///
/// `matches_responder_state s i b a nr` and `matches_responder_state s i b a0 nr`
/// read the *same* simulator responder session for `(b, i)`, whose `initiator`
/// field is unique; hence the two believed initiators coincide.
private
let _resp_session_functional
      (s: ideal_system_state)
      (i: session_id) (b a a0: participant_id) (nr: nonce)
    : Lemma
      (requires
        matches_responder_state s i b a nr /\
        matches_responder_state s i b a0 nr)
      (ensures a == a0) =
  ()

/// --- Preservation of initiator-peer matching across transitions -------------

unfold
let _ipeer_pres (s s': ideal_system_state) : prop =
  forall (i: session_id) (a b: participant_id).
    matches_initiator_peer_state s i a b ==> matches_initiator_peer_state s' i a b

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
private
let _initiator_peer_matches_preserved_transition
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures _ipeer_pres s s') =
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns _ipeer_pres s s'
    with _pf.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s')))
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns _ipeer_pres s s'
    with _hi.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s')))
    and _hr.
      (match lid.role with
       | Responder ->
         eliminate exists (responder_key: priv_key).
           ma_sim_receive_message3_enabled
             (s2p_state s) lid.session lid.party lid.peer responder_key /\
           s2p_state s' ==
             ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
         returns _ipeer_pres s s'
         with _he.
           (assert (Some? (ma_sim_responder_session_state (s2p_state s) lid.party lid.session));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s')))
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns _ipeer_pres s s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns _ipeer_pres s s'
            with _h1.
              (eliminate exists (initiator_nonce: nonce)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message1_enabled
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 t == ma_nsl_message1_term
                   lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message1_state
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce
               returns _ipeer_pres s s'
               with _he.
                 (FStar.Classical.forall_intro_2
                    (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce);
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
            and _h3.
              (eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message3_enabled
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
                 t == ma_nsl_message3_term
                   lid.session lid.party lid.peer responder_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message3_state
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
               returns _ipeer_pres s s'
               with _he.
                 (assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
          | Responder ->
            eliminate exists (initiator_nonce responder_nonce: nonce)
                             (responder_key: priv_key)
                             (initiator_pubkey: term {PubKey? initiator_pubkey}).
              ma_sim_send_message2_enabled
                (s2p_state s) lid.session lid.party lid.peer
                initiator_nonce responder_nonce responder_key initiator_pubkey /\
              t == ma_nsl_message2_term
                lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
              s2p_state s' == ma_sim_send_message2_state
                (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
            returns _ipeer_pres s s'
            with _he.
              (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
               FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
       | IoSend ->
         (FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s));
          FStar.Classical.forall_intro_2 (unfold_ma_sim_initiator_session_state (s2p_state s'))))
#pop-options

/// --- The pointwise authenticity consequence of Message3 provenance ----------
/// (Public; declared in the interface as `ma_message3_provenance_matches_initiator`.)
/// The (stored-session, key-pinned) provenance clause now concludes the initiator
/// peer match directly, so no injectivity/functionality disentangling is needed
/// here: the consumer already holds the responder session and `responder`'s key.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let ma_message3_provenance_matches_initiator
      corrupt key_directory s session responder initiator
      responder_nonce responder_key d =
  // the network Message3 is derivable, hence so is its ciphertext component
  let net = ma_nsl_message3_network_term session initiator responder
              responder_nonce (PubKey responder_key) in
  let msg3 = ma_nsl_message3_term session initiator responder
               responder_nonce (PubKey responder_key) in
  assert (net == Pair (Data (data_of_string "NetInput")) msg3);
  assert (adv.derive d s.know == derive d s.know) by (FStar.Tactics.trefl ());
  assert (derivable s.know net);
  derivable_pair_right s.know (Data (data_of_string "NetInput")) msg3;
  assert (derivable s.know msg3);
  // The matching responder session and `responder`'s directory key discharge the
  // provenance-clause antecedent directly (with b = responder, a = initiator).
  assert (matches_responder_state s session responder initiator responder_nonce);
  assert (PartialMap.sel s.internal.key_directory responder == Some responder_key)
#pop-options

/// --- Backward (used-nonce) recovery of responder-session matching -----------
///
/// Message3 analogue of `_initiator_matches_back_transition`: a responder session
/// is created only by a Message2 send, with a *fresh* responder nonce, so a
/// *used* nonce that matches a responder session at `s'` already matched one at
/// `s`.  Lets the Message3 provenance preservation invoke the inductive
/// hypothesis (whose antecedent is `exists b0 a0. matches_responder_state s
/// …`).
unfold
let _mresp_back (s s': ideal_system_state) : prop =
  forall (i: session_id) (b a: participant_id) (nr: nonce).
    matches_responder_state s' i b a nr /\ Set.mem nr s.internal.used_nonces ==>
    matches_responder_state s i b a nr

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1 --split_queries always"
private
let _responder_matches_back_transition
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures _mresp_back s s') =
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns _mresp_back s s'
    with _pf.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s')))
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns _mresp_back s s'
    with _hi.
      (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
       FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s')))
    and _hr.
      (match lid.role with
       | Responder ->
         eliminate exists (responder_key: priv_key).
           ma_sim_receive_message3_enabled
             (s2p_state s) lid.session lid.party lid.peer responder_key /\
           s2p_state s' ==
             ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
         returns _mresp_back s s'
         with _he.
           (assert (Some? (ma_sim_responder_session_state (s2p_state s) lid.party lid.session));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
            FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s')))
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns _mresp_back s s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns _mresp_back s s'
            with _h1.
              (eliminate exists (initiator_nonce: nonce)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message1_enabled
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 t == ma_nsl_message1_term
                   lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message1_state
                   (s2p_state s) lid.session lid.party lid.peer initiator_nonce
               returns _mresp_back s s'
               with _he.
                 (FStar.Classical.forall_intro_2
                    (_send1_get_updated (s2p_state s) lid.session lid.party lid.peer initiator_nonce);
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
            and _h3.
              (eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                                (responder_pubkey: term {PubKey? responder_pubkey}).
                 ma_sim_send_message3_enabled
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
                 t == ma_nsl_message3_term
                   lid.session lid.party lid.peer responder_nonce responder_pubkey /\
                 s2p_state s' == ma_sim_send_message3_state
                   (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
               returns _mresp_back s s'
               with _he.
                 (assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
                  FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
          | Responder ->
            eliminate exists (initiator_nonce responder_nonce: nonce)
                             (responder_key: priv_key)
                             (initiator_pubkey: term {PubKey? initiator_pubkey}).
              ma_sim_send_message2_enabled
                (s2p_state s) lid.session lid.party lid.peer
                initiator_nonce responder_nonce responder_key initiator_pubkey /\
              t == ma_nsl_message2_term
                lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
              s2p_state s' == ma_sim_send_message2_state
                (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
            returns _mresp_back s s'
            with _he.
              (// the freshly created responder session uses a fresh nonce
               assert (not (Set.mem responder_nonce s.internal.used_nonces));
               FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
               FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
       | IoSend ->
         (FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s));
          FStar.Classical.forall_intro_2 (unfold_ma_sim_responder_session_state (s2p_state s'))))
#pop-options

/// --- Transfer of provenance for a Message3 derivable from the old knowledge --
private
let _m3_transfer_old
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key)
    : Lemma
      (requires
        ma_message3_provenance corrupt s /\
        matches_responder_state s i b a nr /\
        PartialMap.sel s.internal.key_directory b == Some pk /\
        derivable s.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        _resp_pres s s' /\ _ipeer_pres s s')
      (ensures matches_initiator_peer_state s' i a b) =
  // provenance at `s` yields the initiator peer match, which is forward-preserved
  assert (matches_initiator_peer_state s i a b)

/// --- Single-obligation consumer of the pointwise Message2 authenticity lemma -
/// Thin wrapper around `ma_message2_provenance_matches_responder`.
private
let _apply_m2_clause
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
      (session: session_id)
      (initiator responder: participant_id)
      (initiator_nonce responder_nonce: nonce)
      (initiator_key: priv_key)
      (d: adv.derivation)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        matches_initiator_state s session initiator responder initiator_nonce /\
        PartialMap.sel s.internal.key_directory initiator == Some initiator_key /\
        not (Set.mem initiator corrupt) /\
        not (Set.mem responder corrupt) /\
        adv.derive d s.know = Some
          (ma_nsl_message2_network_term
            session initiator responder initiator_nonce responder_nonce (PubKey initiator_key)))
      (ensures matches_responder_state s session responder initiator responder_nonce) =
  ma_message2_provenance_matches_responder corrupt key_directory s session initiator responder
    initiator_nonce responder_nonce initiator_key d

/// --- New occurrence introduced by a Message3 send (the reduction to the
///     already-proven Message2 clause) ------------------------------------------
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_new_occurrence_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state)
      (lid: ma_label_id) (t: term)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.internal.key_directory == s.internal.key_directory /\
        _resp_pres s s' /\
        not (Set.mem lid.party corrupt) /\
        not (Set.mem lid.peer corrupt) /\
        // the (pinned) provenance-clause antecedent for the emitted Message3
        matches_responder_state s' i b a nr /\
        PartialMap.sel s'.internal.key_directory b == Some pk /\
        ma_nsl_message3_term i a b nr (PubKey pk) == t)
      (ensures matches_initiator_peer_state s' i a b) =
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns matches_initiator_peer_state s' i a b
  with _he.
    (// equality with the emitted Message3 forces the (non-vacuous) term arguments
     // to agree: session, responder nonce, and encryption key.
     _msg3_eq_args i a b nr (PubKey pk)
       lid.session lid.party lid.peer responder_nonce responder_pubkey;
     assert (i == lid.session);
     assert (nr == responder_nonce);
     assert (pk == PubKey?.priv responder_pubkey);
     // the firing initiator session for `(lid.party, lid.session)`
     assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session));
     let ist = Some?.v (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session) in
     assert (ist.initiator == lid.party);
     assert (ist.responder == lid.peer);
     assert (not ist.ack_sent);
     // key facts from the send3 enabling condition
     assert (PartialMap.sel s.internal.key_directory lid.party == Some initiator_key);
     assert (PartialMap.sel s.internal.key_directory lid.peer
               == Some (PubKey?.priv responder_pubkey));
     assert (PartialMap.sel s'.internal.key_directory lid.peer == Some pk);
     // the consumed Message2 network input is in `s.inputs`
     let msg2net =
       ma_nsl_message2_network_term lid.session lid.party lid.peer
         ist.initiator_nonce responder_nonce (PubKey initiator_key) in
     assert (Bag.mem msg2net s.inputs);
     // C2: that Message2 is derivable from `s.know`
     assert (derivable s.know msg2net);
     assert (exists (d2: derivation). derive d2 s.know == Some msg2net);
     // matches_initiator_state for the firing session
     assert (matches_initiator_state s lid.session lid.party lid.peer ist.initiator_nonce);
     // apply the already-proven Message2 clause to obtain the responder match
     eliminate exists (d2: derivation). derive d2 s.know == Some msg2net
     returns matches_responder_state s lid.session lid.peer lid.party responder_nonce
     with _hd2.
       (assert (adv.derive d2 s.know == derive d2 s.know) by (FStar.Tactics.trefl ());
        assert (adv.derive d2 s.know = Some msg2net);
        _apply_m2_clause corrupt key_directory s lid.session lid.party lid.peer
          ist.initiator_nonce responder_nonce initiator_key d2);
     // transfer the responder match to `s'` (send3 leaves responder sessions intact)
     assert (matches_responder_state s' lid.session lid.peer lid.party responder_nonce);
     // the now-acked initiator session still matches (initiator/responder unchanged)
     unfold_ma_sim_initiator_session_state (s2p_state s') lid.party lid.session;
     assert (matches_initiator_peer_state s' lid.session lid.party lid.peer);
     // pin `b = lid.peer` via directory injectivity (both own key `pk`) and
     // `a = lid.party` via responder-session functionality.
     assert (s'.internal.key_directory == key_directory);
     assert (b == lid.peer);
     _resp_session_functional s' lid.session lid.peer a lid.party responder_nonce;
     assert (a == lid.party))
#pop-options

/// --- Message3 provenance is preserved by every transition -------------------

/// Message3 analogue of `_m2_obs_session_send`: reduce a Message3 derivable from
/// `snoc s.know t` (for an emitted session ciphertext `t`) to either old
/// provenance or the "equals `t`" branch supplied by the caller.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_obs_session_send
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (session: session_id) (m: term) (k: priv_key) (t: term)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key)
    : Lemma
      (requires
        matches_responder_state s' i b a nr /\
        PartialMap.sel s'.internal.key_directory b == Some pk /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        ~(derivable s.know (PrivKey k)) /\
        t == Aenc (Pair (SessionId session) m) k /\
        s'.know == Seq.snoc s.know t /\
        derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
        ((ma_nsl_message3_term i a b nr (PubKey pk) == t) ==>
          matches_initiator_peer_state s' i a b))
      (ensures matches_initiator_peer_state s' i a b) =
  let msg3 = ma_nsl_message3_term i a b nr (PubKey pk) in
  // the matching responder nonce is not adversary-derivable
  _matches_responder_implies_not_derivable corrupt s' i b a nr;
  _nonce_not_derivable_snoc s s' t nr;
  let subterms = Set.as_set [t] in
  assert (exists (d2: derivation). derive d2 s'.know = Some msg3);
  eliminate exists (d2: derivation). derive d2 s'.know = Some msg3
  returns matches_initiator_peer_state s' i a b
  with _hd2.
    (derivable_from_session_encrypted_term_without_key s.know session m k d2 msg3;
     assert (built_with_subterms s.know subterms msg3);
     assert (forall (n: nonce). ~(Set.mem (Nonce n) subterms));
     assert (forall (l r: term). ~(Set.mem (Pair l r) subterms));
     _msg3_built_elim s subterms i a b nr pk;
     eliminate (derivable s.know msg3) \/ (Set.mem msg3 subterms)
     returns matches_initiator_peer_state s' i a b
     with _hd.
       (// Message3 was already derivable from the old knowledge: its nonce `nr`
        // is a used nonce, so the matching responder session existed at `s`.
        eliminate exists (d3: derivation). derive d3 s.know = Some msg3
        returns matches_initiator_peer_state s' i a b
        with _hd3.
          (_msg3_nonce_used s i a b nr pk d3;
           // `_mresp_back`: a *used* nonce matching a responder session at `s'`
           // already matched one at `s`.
           assert (matches_responder_state s i b a nr);
           _m3_transfer_old corrupt s s' i a b nr pk))
     and _hm2. ())
#pop-options

/// Corrupt-peer counterpart of `_m3_obs_session_send` (cf. `_m2_obs_session_send_corrupt`).
#push-options "--fuel 6 --ifuel 2 --z3rlimit 400"
private
let _m3_obs_session_send_corrupt
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (session: session_id) (m: term) (k: priv_key) (t: term)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key)
    : Lemma
      (requires
        matches_responder_state s' i b a nr /\
        PartialMap.sel s'.internal.key_directory b == Some pk /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        pk <> k /\
        t == Aenc (Pair (SessionId session) m) k /\
        s'.know == Seq.snoc s.know t /\
        derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)))
      (ensures matches_initiator_peer_state s' i a b) =
  let msg3 = ma_nsl_message3_term i a b nr (PubKey pk) in
  let plaintext3 = Pair (SessionId i) (Nonce nr) in
  assert (msg3 == Aenc plaintext3 pk);
  _matches_responder_implies_not_derivable corrupt s' i b a nr;
  let pt_extract () : Lemma (requires derivable s'.know plaintext3) (ensures False) =
    derivable_pair_right s'.know (SessionId i) (Nonce nr)
  in
  FStar.Classical.move_requires pt_extract ();
  eliminate exists (d2: adv.derivation). adv.derive d2 s'.know = Some msg3
  returns matches_initiator_peer_state s' i a b
  with _hd2.
    (assert (adv.derive d2 s'.know == derive d2 s'.know) by (FStar.Tactics.trefl ());
     aenc_subterm_in_derived_implies_observed s'.know plaintext3 pk msg3 d2;
     eliminate exists (idx: nat).
       idx < Seq.length s'.know /\ aenc_subterm msg3 (Seq.index s'.know idx)
     returns matches_initiator_peer_state s' i a b
     with _hidx.
       (let kt = Seq.index s'.know idx in
        aenc_subterm_nonces_subset msg3 kt;
        assert (Set.mem nr (ma_term_nonces msg3));
        Set.subset_mem (ma_term_nonces msg3) (ma_term_nonces kt);
        assert (Set.mem nr (ma_term_nonces kt));
        // nr is a protected nonce; C_shallow forces its carrier kt to be shallow,
        // so the observed ciphertext kt equals msg3.
        _honest_session_nonce_intro corrupt s' i b a nr;
        _honest_carrier_shallow_at corrupt s' idx nr;
        aenc_subterm_shallow_eq msg3 kt;
        if idx < Seq.length s.know then
          (Seq.lemma_index_app1 s.know (Seq.create 1 t) idx;
           assert (Seq.index s.know idx == msg3);
           introduce exists (d3: adv.derivation). adv.derive d3 s.know = Some msg3
           with (DeriveObserved idx) and
             (assert (adv.derive (DeriveObserved idx) s.know == derive (DeriveObserved idx) s.know)
               by (FStar.Tactics.trefl ()));
           _msg3_nonce_used s i a b nr pk (DeriveObserved idx);
           _m3_transfer_old corrupt s s' i a b nr pk)
        else
          (Seq.lemma_index_app2 s.know (Seq.create 1 t) idx;
           Seq.lemma_index_create 1 t (idx - Seq.length s.know))))
#pop-options

/// Message3 analogue of `_m2_obs_deliver`: the public authenticated term is built
/// from base subterms, so a derivable Message3 ciphertext (an `Aenc`) must have
/// already been derivable from `s.know`.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_obs_deliver
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (session: session_id) (party peer: participant_id) (t: term)
      (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key)
    : Lemma
      (requires
        matches_responder_state s' i b a nr /\
        PartialMap.sel s'.internal.key_directory b == Some pk /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        not (Set.mem a corrupt) /\
        not (Set.mem b corrupt) /\
        t == ma_authenticated_term session party peer /\
        s'.know == Seq.snoc s.know t /\
        derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)))
      (ensures matches_initiator_peer_state s' i a b) =
  let msg3 = ma_nsl_message3_term i a b nr (PubKey pk) in
  _matches_responder_implies_not_derivable corrupt s' i b a nr;
  _nonce_not_derivable_snoc s s' t nr;
  let subterms = Set.as_set [SessionId session; ParticipantId party; ParticipantId peer] in
  assert (exists (d2: derivation). derive d2 s'.know = Some msg3);
  eliminate exists (d2: derivation). derive d2 s'.know = Some msg3
  returns matches_initiator_peer_state s' i a b
  with _hd2.
    (derivable_from_public_output_term s.know session party peer d2 msg3;
     assert (built_with_subterms s.know subterms msg3);
     assert (forall (n: nonce). ~(Set.mem (Nonce n) subterms));
     assert (forall (l r: term). ~(Set.mem (Pair l r) subterms));
     _msg3_built_elim s subterms i a b nr pk;
     eliminate (derivable s.know msg3) \/ (Set.mem msg3 subterms)
     returns matches_initiator_peer_state s' i a b
     with _hd.
       (eliminate exists (d3: derivation). derive d3 s.know = Some msg3
        returns matches_initiator_peer_state s' i a b
        with _hd3.
          (_msg3_nonce_used s i a b nr pk d3;
           assert (matches_responder_state s i b a nr);
           _m3_transfer_old corrupt s s' i a b nr pk))
     and _hm2. ())
#pop-options

/// Per-send dispatch wrappers for Message3 provenance.

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_pres_send1
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message3_provenance corrupt s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns ma_message3_provenance corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     let m = Pair (Nonce initiator_nonce) (ParticipantId lid.party) in
     _enabled1_dir s lid.session lid.party lid.peer initiator_nonce responder_pubkey;
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.internal.key_directory == key_directory);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
       matches_responder_state s' i b a nr /\
       PartialMap.sel s'.internal.key_directory b == Some pk /\
       derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
       not (Set.mem a corrupt) /\
       not (Set.mem b corrupt) ==>
       matches_initiator_peer_state s' i a b
     with introduce _ ==> _ with _hd.
       (_msg3_neq_msg1 i a b nr (PubKey pk)
          lid.session lid.party lid.peer initiator_nonce responder_pubkey;
        if not (Set.mem lid.peer corrupt) then
          (_directory_key_not_derivable corrupt key_directory s lid.peer k;
           _m3_obs_session_send corrupt s s' lid.session m k t i a b nr pk)
        else
          (assert (PartialMap.sel key_directory b == Some pk);
           assert (pk <> k);
           _m3_obs_session_send_corrupt corrupt s s' lid.session m k t i a b nr pk)))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_pres_send2
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_key_directory_matches key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message3_provenance corrupt s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns ma_message3_provenance corrupt s'
  with _he.
    (let k = PubKey?.priv initiator_pubkey in
     let m = Pair (Nonce initiator_nonce)
               (Pair (Nonce responder_nonce) (ParticipantId lid.party)) in
     _enabled2_dir s lid.session lid.party lid.peer
       initiator_nonce responder_nonce responder_key initiator_pubkey;
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.internal.key_directory == key_directory);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
       matches_responder_state s' i b a nr /\
       PartialMap.sel s'.internal.key_directory b == Some pk /\
       derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
       not (Set.mem a corrupt) /\
       not (Set.mem b corrupt) ==>
       matches_initiator_peer_state s' i a b
     with introduce _ ==> _ with _hd.
       (_msg3_neq_msg2 i a b nr (PubKey pk)
          lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey;
        if not (Set.mem lid.peer corrupt) then
          (_directory_key_not_derivable corrupt key_directory s lid.peer k;
           _m3_obs_session_send corrupt s s' lid.session m k t i a b nr pk)
        else
          (assert (PartialMap.sel key_directory b == Some pk);
           assert (pk <> k);
           _m3_obs_session_send_corrupt corrupt s s' lid.session m k t i a b nr pk)))
#pop-options

/// In the `msg3 == t` case of send3 provenance, pin the clause's responder-session
/// initiator `a` to the firing initiator `lid.party` — even when `lid.party` is
/// corrupt.  The received Message2 (in `s.inputs`, hence derivable from `s.know`)
/// carries the *secret* responder nonce; by the ciphertext-observation inversion it
/// is *observed* in `s.know`, and the C_msg2/C_msg2key invariants then expose its
/// encryption key as `key_directory a`.  Since that key also equals
/// `key_directory lid.party` (the send3 enabling), directory injectivity forces
/// `a == lid.party`.
#push-options "--fuel 6 --ifuel 2 --z3rlimit 800"
private
let _m3_send3_pin_initiator
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id)
      (responder_nonce: nonce) (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (a: participant_id)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_key_directory_matches key_directory s /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_sim_send_message3_enabled
          (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
        s'.know == Seq.snoc s.know
          (ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey) /\
        matches_responder_state s' lid.session lid.peer a responder_nonce /\
        not (Set.mem a corrupt) /\
        not (Set.mem lid.peer corrupt))
      (ensures a == lid.party) =
  let t = ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey in
  // the firing initiator session and its received Message2
  let ist = Some?.v (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session) in
  let net = ma_nsl_message2_network_term lid.session lid.party lid.peer
              ist.initiator_nonce responder_nonce (PubKey initiator_key) in
  let msg2 = ma_nsl_message2_term lid.session lid.party lid.peer
               ist.initiator_nonce responder_nonce (PubKey initiator_key) in
  let plaintext2 = Pair (SessionId lid.session)
    (Pair (Nonce ist.initiator_nonce) (Pair (Nonce responder_nonce) (ParticipantId lid.peer))) in
  assert (msg2 == Aenc plaintext2 initiator_key);
  assert (PartialMap.sel key_directory lid.party == Some initiator_key);
  // the Message2 ciphertext is derivable from s.know (it is a pending input)
  assert (Bag.mem net s.inputs);
  assert (derivable s.know net);
  assert (net == Pair (Data (data_of_string "NetInput")) msg2);
  derivable_pair_right s.know (Data (data_of_string "NetInput")) msg2;
  assert (derivable s.know msg2);
  // the responder nonce is secret (honest responder session at s')
  _matches_responder_implies_not_derivable corrupt s' lid.session lid.peer a responder_nonce;
  _nonce_not_derivable_snoc s s' t responder_nonce;
  assert (~(derivable s.know (Nonce responder_nonce)));
  // hence the Message2 plaintext is not derivable (it would yield the secret nonce)
  let pt_extract () : Lemma (requires derivable s.know plaintext2) (ensures False) =
    derivable_pair_right s.know (SessionId lid.session)
      (Pair (Nonce ist.initiator_nonce) (Pair (Nonce responder_nonce) (ParticipantId lid.peer)));
    derivable_pair_right s.know (Nonce ist.initiator_nonce)
      (Pair (Nonce responder_nonce) (ParticipantId lid.peer));
    derivable_pair_left s.know (Nonce responder_nonce) (ParticipantId lid.peer)
  in
  FStar.Classical.move_requires pt_extract ();
  assert (~(derivable s.know plaintext2));
  eliminate exists (d2: adv.derivation). adv.derive d2 s.know = Some msg2
  returns a == lid.party
  with _hd2.
    (assert (adv.derive d2 s.know == derive d2 s.know) by (FStar.Tactics.trefl ());
     // observed: the ciphertext reaches some knowledge index
     aenc_subterm_in_derived_implies_observed s.know plaintext2 initiator_key msg2 d2;
     // responder_nonce is a used nonce (it occurs in a derivable knowledge term)
     ma_derive_term_nonces_in_knowledge_nonces s.know d2 msg2;
     assert (Set.mem responder_nonce (ma_term_nonces msg2));
     Set.subset_mem (ma_term_nonces msg2) (ma_knowledge_nonces s.know);
     Set.subset_mem (ma_knowledge_nonces s.know) s.internal.used_nonces;
     assert (Set.mem responder_nonce s.internal.used_nonces);
     // push the honest responder session back to s
     assert (matches_responder_state s lid.session lid.peer a responder_nonce);
     eliminate exists (idx: nat).
       idx < Seq.length s.know /\ aenc_subterm msg2 (Seq.index s.know idx)
     returns a == lid.party
     with _hidx.
       (let kt = Seq.index s.know idx in
        aenc_subterm_nonces_subset msg2 kt;
        assert (Set.mem responder_nonce (ma_term_nonces msg2));
        Set.subset_mem (ma_term_nonces msg2) (ma_term_nonces kt);
        assert (Set.mem responder_nonce (ma_term_nonces kt));
        // responder_nonce is protected; C_shallow ⟹ kt is shallow ⟹ kt == msg2.
        _honest_session_nonce_intro corrupt s lid.session lid.peer a responder_nonce;
        _honest_carrier_shallow_at corrupt s idx responder_nonce;
        aenc_subterm_shallow_eq msg2 kt;
        assert (kt == msg2);
        // C_msg2key: the observed Message2 (carrying the protected responder_nonce,
        // responder session (lid.session, lid.peer, a)) is encrypted under a's key.
        _honest_msg2_key corrupt s idx lid.session
          ist.initiator_nonce responder_nonce lid.peer a initiator_key;
        // key_directory a == Some initiator_key == key_directory lid.party
        assert (PartialMap.sel key_directory a == Some initiator_key)))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_pres_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_message2_provenance corrupt s /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        ma_honest_carrier_shallow corrupt s' /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message3_provenance corrupt s') =
  eliminate exists (responder_nonce: nonce) (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message3_state (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns ma_message3_provenance corrupt s'
  with _he.
    (let k = PubKey?.priv responder_pubkey in
     let m = Nonce responder_nonce in
     _enabled3_dir s lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey;
     assert (PartialMap.sel key_directory lid.peer == Some k);
     assert (s'.internal.key_directory == key_directory);
     assert (t == Aenc (Pair (SessionId lid.session) m) k);
     introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
       matches_responder_state s' i b a nr /\
       PartialMap.sel s'.internal.key_directory b == Some pk /\
       derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
       not (Set.mem a corrupt) /\
       not (Set.mem b corrupt) ==>
       matches_initiator_peer_state s' i a b
     with introduce _ ==> _ with _hd.
       (if not (Set.mem lid.peer corrupt) then
          (_directory_key_not_derivable corrupt key_directory s lid.peer k;
           introduce (ma_nsl_message3_term i a b nr (PubKey pk) == t) ==>
             matches_initiator_peer_state s' i a b
           with _heq.
             (// `msg3 == t` pins i/nr/pk; injectivity pins `b == lid.peer`; the
              // companion key-invariant then pins `a == lid.party` (so the firing
              // initiator is honest and `_m3_new_occurrence_send3` applies even when
              // the actual `lid.party` could have been corrupt).
              _msg3_eq_args i a b nr (PubKey pk)
                lid.session lid.party lid.peer responder_nonce responder_pubkey;
              assert (PartialMap.sel key_directory b == Some pk);
              assert (pk == k);
              assert (b == lid.peer);
              assert (matches_responder_state s' lid.session lid.peer a responder_nonce);
              _m3_send3_pin_initiator corrupt key_directory s s' lid
                responder_nonce initiator_key responder_pubkey a;
              assert (a == lid.party);
              _m3_new_occurrence_send3 corrupt key_directory s s' lid t i a b nr pk);
           _m3_obs_session_send corrupt s s' lid.session m k t i a b nr pk)
        else
          (assert (PartialMap.sel key_directory b == Some pk);
           assert (pk <> k);
           _m3_obs_session_send_corrupt corrupt s s' lid.session m k t i a b nr pk)))
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _m3_pres_deliver
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_knowledge_nonces_are_used s.internal.used_nonces s.know /\
        ma_valid_responder_nonces_not_derivable corrupt s' /\
        _mresp_back s s' /\
        ma_message3_provenance corrupt s /\
        _resp_pres s s' /\ _ipeer_pres s s' /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s') /\
        s'.know == Seq.snoc s.know t)
      (ensures ma_message3_provenance corrupt s') =
  assert (t == ma_authenticated_term lid.session lid.party lid.peer);
  introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
    matches_responder_state s' i b a nr /\
    PartialMap.sel s'.internal.key_directory b == Some pk /\
    derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
    not (Set.mem a corrupt) /\
    not (Set.mem b corrupt) ==>
    matches_initiator_peer_state s' i a b
  with introduce _ ==> _ with _hd.
    _m3_obs_deliver corrupt s s' lid.session lid.party lid.peer t i a b nr pk
#pop-options

#push-options "--z3rlimit 20"
private
let _m3_provenance_preserved
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        ma_message3_provenance corrupt s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures ma_message3_provenance corrupt s') =
  _responder_matches_preserved_transition corrupt key_directory know0 s s' l;
  _initiator_peer_matches_preserved_transition corrupt key_directory know0 s s' l;
  // Backward (used-nonce) responder-session recovery, plus stored-nonce secrecy
  // at the post-state, to invoke the inductive hypothesis under the
  // stored-session-conditioned Message3 provenance clause.
  _responder_matches_back_transition corrupt key_directory know0 s s' l;
  ma_ideal_core_inv_preserved corrupt key_directory know0 s s' l;
  match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns ma_message3_provenance corrupt s'
    with _pf.
      (introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
         matches_responder_state s' i b a nr /\
         PartialMap.sel s'.internal.key_directory b == Some pk /\
         derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
         not (Set.mem a corrupt) /\
         not (Set.mem b corrupt) ==>
         matches_initiator_peer_state s' i a b
       with introduce _ ==> _ with _h.
         (// sessions and knowledge are unchanged by an Input step
          assert (matches_responder_state s i b a nr);
          _m3_transfer_old corrupt s s' i a b nr pk))
  | Internal lid ->
    introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
      matches_responder_state s' i b a nr /\
      PartialMap.sel s'.internal.key_directory b == Some pk /\
      derivable s'.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
      not (Set.mem a corrupt) /\
      not (Set.mem b corrupt) ==>
      matches_initiator_peer_state s' i a b
    with introduce _ ==> _ with _h.
      (// an Internal step leaves the knowledge unchanged, so the Message3 is
       // already derivable from `s.know`; its nonce is therefore used, and the
       // matching responder session existed at `s`.
       assert (derivable s.know (ma_nsl_message3_term i a b nr (PubKey pk)));
       eliminate exists (d3: derivation).
         derive d3 s.know = Some (ma_nsl_message3_term i a b nr (PubKey pk))
       returns matches_initiator_peer_state s' i a b
       with _hd3.
         (_msg3_nonce_used s i a b nr pk d3;
          // `_mresp_back`: the used nonce matched a responder session at `s` too
          assert (matches_responder_state s i b a nr);
          _m3_transfer_old corrupt s s' i a b nr pk))
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns ma_message3_provenance corrupt s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns ma_message3_provenance corrupt s'
            with _h1. _m3_pres_send1 corrupt key_directory s s' lid t
            and _h3. _m3_pres_send3 corrupt key_directory s s' lid t
          | Responder -> _m3_pres_send2 corrupt key_directory s s' lid t)
       | IoSend -> _m3_pres_deliver corrupt s s' lid t)
#pop-options

/// ===========================================================================
/// The strong output-has-complementary-request consequence.
/// ===========================================================================

/// Single-obligation consumer of the pointwise Message3 authenticity lemma (the
/// analogue of `_apply_m2_clause`).  Turns a derivable Message3 ciphertext for
/// `(session, initiator, responder)` into the matching simulator initiator
/// session of `initiator`.
private
let _apply_m3_clause
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
      (session: session_id)
      (responder initiator: participant_id)
      (responder_nonce: nonce)
      (responder_key: priv_key)
      (d: adv.derivation)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message3_provenance corrupt s /\
        matches_responder_state s session responder initiator responder_nonce /\
        PartialMap.sel s.internal.key_directory responder == Some responder_key /\
        not (Set.mem initiator corrupt) /\
        not (Set.mem responder corrupt) /\
        adv.derive d s.know = Some
          (ma_nsl_message3_network_term
            session initiator responder responder_nonce (PubKey responder_key)))
      (ensures matches_initiator_peer_state s session initiator responder) =
  ma_message3_provenance_matches_initiator corrupt key_directory s session responder initiator
    responder_nonce responder_key d

/// Transfer an in-flight `Output(i, p)` complement from `s` to `s'`, given that
/// `i`'s recorded requests only grow across the transition.  The witnessing
/// request pair recorded in `s` survives because membership is monotone.
private
let _comp_transfer_one
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (i: session_id) (p: participant_id)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        Set.mem (ma_output_term i p) (s2p_state s).internal.sim_to_ideal_channel /\
        (forall (req: auth_request).
           Set.mem req (ma_session_requests (s2p_state s) i) ==>
           Set.mem req (ma_session_requests (s2p_state s') i)))
      (ensures
        (exists (peer: participant_id) (r: role).
           Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
           (Set.mem p corrupt \/ Set.mem peer corrupt \/
            Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))) =
  assert (exists (peer: participant_id) (r: role).
            Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s) i) /\
            (Set.mem p corrupt \/ Set.mem peer corrupt \/
             Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s) i)));
  eliminate exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s) i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s) i))
  returns
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
  with _hw. ()

/// Per-`(i, p)` frame step, isolated into its own (small) query so the trivial
/// channel/request-set congruences are discharged in a clean context rather than
/// competing with the rest of the module's quantifier background (which otherwise
/// starves these trivial obligations of solver budget).  The post-condition is the
/// raw existential (not the opaque `ma_output_has_complementary_request`), so no
/// predicate fold happens here.
#push-options "--fuel 4 --ifuel 2 --z3rlimit 50 --z3refresh"
private
let _comp_frame_pair
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (i: session_id) (p: participant_id)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        (s2p_state s').internal.requests == (s2p_state s).internal.requests /\
        (s2p_state s').internal.sim_to_ideal_channel == (s2p_state s).internal.sim_to_ideal_channel /\
        Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel)
      (ensures
        (exists (peer: participant_id) (r: role).
           Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
           (Set.mem p corrupt \/ Set.mem peer corrupt \/
            Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))) =
  assert (Set.mem (ma_output_term i p) (s2p_state s).internal.sim_to_ideal_channel);
  assert (forall (req: auth_request).
    Set.mem req (ma_session_requests (s2p_state s) i) ==>
    Set.mem req (ma_session_requests (s2p_state s') i));
  _comp_transfer_one corrupt s s' i p
#pop-options

/// Per-`(i, p)` implication, with the raw existential consequence (no opaque
/// predicate).  Isolated so its small query is unaffected by the rest of the
/// module's quantifier background.
#push-options "--fuel 4 --ifuel 2 --z3rlimit 50 --z3refresh"
private
let _comp_frame_impl
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
      (i: session_id) (p: participant_id)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        (s2p_state s').internal.requests == (s2p_state s).internal.requests /\
        (s2p_state s').internal.sim_to_ideal_channel == (s2p_state s).internal.sim_to_ideal_channel)
      (ensures
        Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
        (exists (peer: participant_id) (r: role).
           Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
           (Set.mem p corrupt \/ Set.mem peer corrupt \/
            Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))) =
  introduce
    Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
  with _hmem. _comp_frame_pair corrupt s s' i p
#pop-options

/// Frame the whole consequence across a transition that leaves both the
/// simulator-to-ideal channel and the recorded requests unchanged (Input,
/// Message1 send, Message2 send).  Establishes the per-`(i, p)` implication via
/// the isolated `_comp_frame_impl`, then folds it into the opaque predicate.  The
/// fold is discharged by a `norm` tactic that reduces the goal to the explicit
/// `forall` first: with the `s'/s` channel/request equalities in scope the solver
/// otherwise rewrites the goal's `s'` terms to their `s` counterparts before it
/// has unfolded the predicate, breaking the (purely definitional) match.
#push-options "--fuel 8 --ifuel 2 --z3rlimit 100"
private
let _comp_preserved_frame
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        (s2p_state s').internal.requests == (s2p_state s).internal.requests /\
        (s2p_state s').internal.sim_to_ideal_channel == (s2p_state s).internal.sim_to_ideal_channel)
      (ensures ma_output_has_complementary_request corrupt s') =
  introduce forall (i: session_id) (p: participant_id).
    Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
  with _comp_frame_impl corrupt s s' i p;
  assert (ma_output_has_complementary_request corrupt s')
    by (FStar.Tactics.norm [delta_only [`%ma_output_has_complementary_request]];
        FStar.Tactics.smt ())

/// Fold an already-established per-`(i, p)` `forall` into the opaque
/// `ma_output_has_complementary_request`.  Proven in its own (clean) context via a
/// `norm` tactic that reduces the predicate to its `forall` definition before
/// hitting SMT — the implicit fold otherwise fails for the `_comp_*` lemmas now
/// that the enlarged module background perturbs the solver's unfolding.
#push-options "--fuel 8 --ifuel 2 --z3rlimit 50"
private
let _fold_comp_pred
      (corrupt: Set.set participant_id)
      (s': ideal_system_state)
    : Lemma
      (requires
        (forall (i: session_id) (p: participant_id).
          Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
          (exists (peer: participant_id) (r: role).
             Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
             (Set.mem p corrupt \/ Set.mem peer corrupt \/
              Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))))
      (ensures ma_output_has_complementary_request corrupt s') =
  assert (ma_output_has_complementary_request corrupt s')
    by (FStar.Tactics.norm [delta_only [`%ma_output_has_complementary_request]];
        FStar.Tactics.smt ())
#pop-options

/// Recover the recorded request matching a stored simulator initiator/responder
/// session from `ma_sim_session_matches_ideal_request` (the system-level subsumer
/// of the former H_init / H_resp clauses).  `ma_sim_session_matches_ideal_request`
/// is a plain (non-`unfold`) `let`, so instantiate its quantifier explicitly and
/// bridge the stored-session map to `ma_get_sim_participant_session_state`.
private
let _initiator_session_has_request
      (s: ideal_system_state) (session: session_id) (participant: participant_id)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        Some? (ma_sim_initiator_session_state (s2p_state s) participant session))
      (ensures
        Set.mem
          { party = participant;
            peer = (Some?.v (ma_sim_initiator_session_state (s2p_state s) participant session)).responder;
            role = Initiator }
          (ma_session_requests (s2p_state s) session)) =
  unfold_ma_sim_initiator_session_state (s2p_state s) participant session;
  let h : squash (ma_sim_session_matches_ideal_request s) = () in
  let h_session = FStar.Classical.Sugar.forall_elim session h in
  let _h_instance = FStar.Classical.Sugar.forall_elim participant h_session in
  ()

private
let _responder_session_has_request
      (s: ideal_system_state) (session: session_id) (participant: participant_id)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        Some? (ma_sim_responder_session_state (s2p_state s) participant session))
      (ensures
        Set.mem
          { party = participant;
            peer = (Some?.v (ma_sim_responder_session_state (s2p_state s) participant session)).initiator;
            role = Responder }
          (ma_session_requests (s2p_state s) session)) =
  unfold_ma_sim_responder_session_state (s2p_state s) participant session;
  let h : squash (ma_sim_session_matches_ideal_request s) = () in
  let h_session = FStar.Classical.Sugar.forall_elim session h in
  let _h_instance = FStar.Classical.Sugar.forall_elim participant h_session in
  ()

/// The new `Output(lid.session, lid.party)` emitted by a Message3 *send* carries
/// the complement: `lid.party`'s own Initiator request (recovered from its stored
/// initiator session via `ma_sim_session_matches_ideal_request`) and the matching
/// Responder request of `lid.peer` (recovered from the consumed Message2 via the
/// Message2 authenticity lemma, then again via
/// `ma_sim_session_matches_ideal_request`).
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _comp_new_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        ma_sim_session_matches_ideal_request s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures
        (exists (peer: participant_id) (r: role).
           Set.mem ({ party = lid.party; peer = peer; role = r })
             (ma_session_requests (s2p_state s') lid.session) /\
           (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
            Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
              (ma_session_requests (s2p_state s') lid.session)))) =
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = lid.party; peer = peer; role = r })
         (ma_session_requests (s2p_state s') lid.session) /\
       (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
          (ma_session_requests (s2p_state s') lid.session)))
  with _he.
    (let sp = s2p_state s in
     // The firing initiator session for `(lid.party, lid.session)`.
     assert (Some? (ma_sim_initiator_session_state sp lid.party lid.session));
     let ist = Some?.v (ma_sim_initiator_session_state sp lid.party lid.session) in
     assert (ist.initiator == lid.party);
     assert (ist.responder == lid.peer);
     // `lid.party` recorded its own Initiator request (via the stored initiator
     // session and `ma_sim_session_matches_ideal_request`).
     _initiator_session_has_request s lid.session lid.party;
     assert (Set.mem ({ party = lid.party; peer = ist.responder; role = Initiator })
               (ma_session_requests sp lid.session));
     // Message3 send leaves the recorded requests unchanged.
     assert (ma_session_requests (s2p_state s') lid.session == ma_session_requests sp lid.session);
     if Set.mem lid.party corrupt || Set.mem lid.peer corrupt then (
       // At least one party is corrupt: use the corrupt disjunct directly —
       // the initiator's own request + the corrupt witness suffices.
       introduce exists (peer: participant_id) (r: role).
         Set.mem ({ party = lid.party; peer = peer; role = r })
           (ma_session_requests (s2p_state s') lid.session) /\
         (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
          Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
            (ma_session_requests (s2p_state s') lid.session))
       with lid.peer Initiator
       and ()
     ) else (
       // Both parties are honest: recover `lid.peer`'s responder session via
       // the Message2 provenance clause.
       let msg2net =
         ma_nsl_message2_network_term lid.session lid.party lid.peer
           ist.initiator_nonce responder_nonce (PubKey initiator_key) in
       assert (Bag.mem msg2net s.inputs);
       assert (derivable s.know msg2net);
       assert (exists (d2: derivation). derive d2 s.know == Some msg2net);
       assert (matches_initiator_state s lid.session lid.party lid.peer ist.initiator_nonce);
       assert (PartialMap.sel s.internal.key_directory lid.party == Some initiator_key);
       eliminate exists (d2: derivation). derive d2 s.know == Some msg2net
       returns matches_responder_state s lid.session lid.peer lid.party responder_nonce
       with _hd2.
         (assert (adv.derive d2 s.know == derive d2 s.know) by (FStar.Tactics.trefl ());
          _apply_m2_clause corrupt key_directory s lid.session lid.party lid.peer
            ist.initiator_nonce responder_nonce initiator_key d2);
       assert (matches_responder_state s lid.session lid.peer lid.party responder_nonce);
       assert (Some? (ma_sim_responder_session_state sp lid.peer lid.session));
       let rst = Some?.v (ma_sim_responder_session_state sp lid.peer lid.session) in
       assert (rst.initiator == lid.party);
       _responder_session_has_request s lid.session lid.peer;
       assert (Set.mem ({ party = lid.peer; peer = rst.initiator; role = Responder })
                 (ma_session_requests sp lid.session));
       introduce exists (peer: participant_id) (r: role).
         Set.mem ({ party = lid.party; peer = peer; role = r })
           (ma_session_requests (s2p_state s') lid.session) /\
         (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
          Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
            (ma_session_requests (s2p_state s') lid.session))
       with lid.peer Initiator
       and ()
     ))
#pop-options

/// The new `Output(lid.session, lid.party)` emitted by a Message3 *receive*
/// carries the complement: `lid.party`'s own Responder request (H_resp) and the
/// matching Initiator request of `lid.peer` (recovered from the consumed
/// Message3 via the derivable-Message3 clause, then H_init).
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private
let _comp_new_recv3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message3_provenance corrupt s /\
        ma_sim_session_matches_ideal_request s /\
        ma_sim_receive_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer (s2p_state s'))
      (ensures
        (exists (peer: participant_id) (r: role).
           Set.mem ({ party = lid.party; peer = peer; role = r })
             (ma_session_requests (s2p_state s') lid.session) /\
           (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
            Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
              (ma_session_requests (s2p_state s') lid.session)))) =
  eliminate exists (responder_key: priv_key).
    ma_sim_receive_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_key /\
    s2p_state s' == ma_sim_receive_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_key
  returns
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = lid.party; peer = peer; role = r })
         (ma_session_requests (s2p_state s') lid.session) /\
       (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
          (ma_session_requests (s2p_state s') lid.session)))
  with _he.
    (let sp = s2p_state s in
     // The firing responder session for `(lid.party, lid.session)`.
     assert (Some? (ma_sim_responder_session_state sp lid.party lid.session));
     let rst = Some?.v (ma_sim_responder_session_state sp lid.party lid.session) in
     assert (rst.responder == lid.party);
     assert (rst.initiator == lid.peer);
     // `lid.party` recorded its own Responder request (via the stored responder
     // session and `ma_sim_session_matches_ideal_request`).
     _responder_session_has_request s lid.session lid.party;
     assert (Set.mem ({ party = lid.party; peer = rst.initiator; role = Responder })
               (ma_session_requests sp lid.session));
     // Message3 receive leaves the recorded requests unchanged.
     ma_sim_receive_message3_state_session_requests_eq
       sp lid.session lid.party lid.peer responder_key lid.session;
     assert (ma_session_requests (s2p_state s') lid.session == ma_session_requests sp lid.session);
     if Set.mem lid.party corrupt || Set.mem lid.peer corrupt then (
       // At least one party is corrupt: use the corrupt disjunct directly —
       // the responder's own request + the corrupt witness suffices.
       introduce exists (peer: participant_id) (r: role).
         Set.mem ({ party = lid.party; peer = peer; role = r })
           (ma_session_requests (s2p_state s') lid.session) /\
         (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
          Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
            (ma_session_requests (s2p_state s') lid.session))
       with lid.peer Responder
       and ()
     ) else (
       // Both parties are honest: recover `lid.peer`'s initiator session via
       // the Message3 provenance clause.
       let msg3net =
         ma_nsl_message3_network_term lid.session lid.peer lid.party
           rst.responder_nonce (PubKey responder_key) in
       assert (Bag.mem msg3net s.inputs);
       assert (derivable s.know msg3net);
       assert (exists (d3: derivation). derive d3 s.know == Some msg3net);
       assert (matches_responder_state s lid.session lid.party lid.peer rst.responder_nonce);
       assert (PartialMap.sel s.internal.key_directory lid.party == Some responder_key);
       eliminate exists (d3: derivation). derive d3 s.know == Some msg3net
       returns matches_initiator_peer_state s lid.session lid.peer lid.party
       with _hd3.
         (assert (adv.derive d3 s.know == derive d3 s.know) by (FStar.Tactics.trefl ());
          _apply_m3_clause corrupt key_directory s lid.session lid.party lid.peer
            rst.responder_nonce responder_key d3);
       assert (matches_initiator_peer_state s lid.session lid.peer lid.party);
       assert (Some? (ma_sim_initiator_session_state sp lid.peer lid.session));
       let ist = Some?.v (ma_sim_initiator_session_state sp lid.peer lid.session) in
       assert (ist.responder == lid.party);
       _initiator_session_has_request s lid.session lid.peer;
       assert (Set.mem ({ party = lid.peer; peer = ist.responder; role = Initiator })
                 (ma_session_requests sp lid.session));
       introduce exists (peer: participant_id) (r: role).
         Set.mem ({ party = lid.party; peer = peer; role = r })
           (ma_session_requests (s2p_state s') lid.session) /\
         (Set.mem lid.party corrupt \/ Set.mem peer corrupt \/
          Set.mem ({ party = peer; peer = lid.party; role = complementary_role r })
            (ma_session_requests (s2p_state s') lid.session))
       with lid.peer Responder
       and ()
     ))
#pop-options

/// Message1 send: the simulator-to-ideal channel and recorded requests are
/// structurally untouched.
private
let _comp_send1
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_output_has_complementary_request corrupt s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message1_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns ma_output_has_complementary_request corrupt s'
  with _he.
    (assert ((s2p_state s').internal.requests == (s2p_state s).internal.requests);
     assert ((s2p_state s').internal.sim_to_ideal_channel == (s2p_state s).internal.sim_to_ideal_channel);
     _comp_preserved_frame corrupt s s')

/// Message2 send: the simulator-to-ideal channel and recorded requests are
/// preserved (explicit SMTPat lemmas).
private
let _comp_send2
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_output_has_complementary_request corrupt s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns ma_output_has_complementary_request corrupt s'
  with _he.
    (ma_sim_send_message2_state_preserves_requests
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key;
     ma_sim_send_message2_state_preserves_sim_to_ideal_channel
       (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key;
     _comp_preserved_frame corrupt s s')

/// Ideal initiate: the simulator-to-ideal channel is unchanged and the recorded
/// requests only grow.  Existing complements survive (monotone membership).
private
let _comp_initiate
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        ma_ideal_initiate_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s'))
      (ensures ma_output_has_complementary_request corrupt s') =
  introduce forall (i: session_id) (p: participant_id).
    Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
  with introduce _ ==> _ with _hmem.
    _comp_transfer_one corrupt s s' i p;
  _fold_comp_pred corrupt s'

/// Ideal deliver: removes the delivered `Output` and leaves recorded requests
/// unchanged.  Every surviving output keeps its complement.
private
let _comp_deliver
      (corrupt: Set.set participant_id)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s'))
      (ensures ma_output_has_complementary_request corrupt s') =
  introduce forall (i: session_id) (p: participant_id).
    Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
  with introduce _ ==> _ with _hmem.
    _comp_transfer_one corrupt s s' i p;
  _fold_comp_pred corrupt s'

/// Message3 send: combine the new-output complement with the monotone transfer
/// of every pre-existing output.
private
let _comp_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        ma_sim_session_matches_ideal_request s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_output_has_complementary_request corrupt s') =
  _comp_new_send3 corrupt key_directory s s' lid t;
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns ma_output_has_complementary_request corrupt s'
  with _he.
    (introduce forall (i: session_id) (p: participant_id).
       Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
       (exists (peer: participant_id) (r: role).
          Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
          (Set.mem p corrupt \/ Set.mem peer corrupt \/
           Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
     with introduce _ ==> _ with _hmem.
       (if i = lid.session && p = lid.party then ()
        else _comp_transfer_one corrupt s s' i p);
     _fold_comp_pred corrupt s')

/// Message3 receive: combine the new-output complement with the monotone
/// transfer of every pre-existing output.
private
let _comp_recv3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_output_has_complementary_request corrupt s /\
        ma_ideal_core_inv corrupt key_directory s /\
        ma_key_directory_injective key_directory /\
        ma_message3_provenance corrupt s /\
        ma_sim_session_matches_ideal_request s /\
        ma_sim_receive_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer (s2p_state s'))
      (ensures ma_output_has_complementary_request corrupt s') =
  _comp_new_recv3 corrupt key_directory s s' lid;
  eliminate exists (responder_key: priv_key).
    ma_sim_receive_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_key /\
    s2p_state s' == ma_sim_receive_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_key
  returns ma_output_has_complementary_request corrupt s'
  with _he.
    (// Message3 receive leaves recorded requests globally unchanged.
     introduce forall (query: session_id).
       ma_session_requests (s2p_state s') query == ma_session_requests (s2p_state s) query
     with
       ma_sim_receive_message3_state_session_requests_eq
         (s2p_state s) lid.session lid.party lid.peer responder_key query;
     introduce forall (i: session_id) (p: participant_id).
       Set.mem (ma_output_term i p) (s2p_state s').internal.sim_to_ideal_channel ==>
       (exists (peer: participant_id) (r: role).
          Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s') i) /\
          (Set.mem p corrupt \/ Set.mem peer corrupt \/
           Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s') i)))
     with introduce _ ==> _ with _hmem.
       (if i = lid.session && p = lid.party then ()
        else _comp_transfer_one corrupt s s' i p);
     _fold_comp_pred corrupt s')

/// ===========================================================================
/// Simulator-session / request bookkeeping clauses.
///
/// Clause A `ma_sim_session_matches_ideal_request` (session ==> request) and
/// clause C `ma_output_token_matches_sim_phase` (output token ==> phase).  Both
/// read only `s.internal` (the simulator session map, recorded requests, and the
/// simulator-to-ideal channel), so the tester's `Input` step frames them.
/// ===========================================================================

/// --- Clause A: ma_sim_session_matches_ideal_request ----------------------

/// Frame across a transition that leaves the simulator session map untouched and
/// only grows the recorded requests (Input, ideal initiate, ideal deliver).
private
let _sessreq_frame (s s': ideal_system_state)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        (forall (p: participant_id) (i: session_id).
           ma_get_sim_participant_session_state (s2p_state s') p i ==
           ma_get_sim_participant_session_state (s2p_state s) p i) /\
        (forall (i: session_id) (req: auth_request).
           Set.mem req (ma_session_requests (s2p_state s) i) ==>
           Set.mem req (ma_session_requests (s2p_state s') i)))
      (ensures ma_sim_session_matches_ideal_request s') =
  ()

/// Message1 send: a new initiator session for `(lid.party, lid.session)` is
/// created.  The session's request was already recorded, because send1 is
/// enabled only when the matching `Authenticating(.., Initiator)` notification is
/// on the ideal->sim channel, which (H_auth_init in `ma_ideal_state_inv`) implies
/// the request.  Every other session, and the recorded requests, are unchanged.
private
let _sessreq_send1 (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_ideal_state_inv (s2p_state s) /\
        ma_sim_session_matches_ideal_request s /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_sim_session_matches_ideal_request s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns ma_sim_session_matches_ideal_request s'
  with _he.
    (let sp = s2p_state s in
     // Requests are structurally unchanged (send1 only touches the simulator map,
     // used nonces, and the ideal->sim channel).
     assert ((s2p_state s').internal.requests == sp.internal.requests);
     // H_auth_init: the new session's Initiator request is already recorded.
     assert (Set.mem (ma_authenticating_term lid.session lid.party lid.peer Initiator)
               sp.internal.ideal_to_sim_channel);
     assert (Set.mem ({ party = lid.party; peer = lid.peer; role = Initiator })
               (ma_session_requests sp lid.session));
     introduce forall (p: participant_id) (i: session_id).
       (match ma_get_sim_participant_session_state (s2p_state s') p i with
        | Some (SimInitiatorSession ist) ->
          ist.initiator == p /\
          Set.mem { party = p; peer = ist.responder; role = Initiator }
            (ma_session_requests (s2p_state s') i)
        | Some (SimResponderSession rst) ->
          rst.responder == p /\
          Set.mem { party = p; peer = rst.initiator; role = Responder }
            (ma_session_requests (s2p_state s') i)
        | None -> True)
     with
       _send1_get_updated sp lid.session lid.party lid.peer initiator_nonce p i)

/// Message2 send: dual of send1 for a new responder session.  The request is
/// recovered from H_auth_resp.
private
let _sessreq_send2 (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_ideal_state_inv (s2p_state s) /\
        ma_sim_session_matches_ideal_request s /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_sim_session_matches_ideal_request s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns ma_sim_session_matches_ideal_request s'
  with _he.
    (let sp = s2p_state s in
     // H_auth_resp: the new session's Responder request is already recorded
     // (send2 is enabled only with the matching authenticating notification).
     assert (Set.mem (ma_authenticating_term lid.session lid.party lid.peer Responder)
               sp.internal.ideal_to_sim_channel);
     assert (Set.mem ({ party = lid.party; peer = lid.peer; role = Responder })
               (ma_session_requests sp lid.session)))

/// Message3 send: the firing initiator session is updated in place (only the
/// `ack_sent` flag flips); its party/peer fields and the recorded requests are
/// unchanged, so the pre-state clause carries over.
private
let _sessreq_send3 (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_sim_session_matches_ideal_request s') =
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns ma_sim_session_matches_ideal_request s'
  with _he.
    assert (Some? (ma_sim_initiator_session_state (s2p_state s) lid.party lid.session))

/// Message3 receive: dual of send3 for the firing responder session.
private
let _sessreq_recv3 (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        ma_sim_receive_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer (s2p_state s'))
      (ensures ma_sim_session_matches_ideal_request s') =
  eliminate exists (responder_key: priv_key).
    ma_sim_receive_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_key /\
    s2p_state s' ==
      ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
  returns ma_sim_session_matches_ideal_request s'
  with _he.
    (let sp = s2p_state s in
     assert (Some? (ma_sim_responder_session_state sp lid.party lid.session));
     introduce forall (query: session_id).
       ma_session_requests (s2p_state s') query == ma_session_requests sp query
     with
       ma_sim_receive_message3_state_session_requests_eq
         sp lid.session lid.party lid.peer responder_key query)

/// Ideal initiate: simulator sessions are untouched and the recorded requests
/// only grow.
private
let _sessreq_initiate (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        ma_ideal_initiate_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s'))
      (ensures ma_sim_session_matches_ideal_request s') =
  _sessreq_frame s s'

/// Ideal deliver: simulator sessions and recorded requests are unchanged.
private
let _sessreq_deliver (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_sim_session_matches_ideal_request s /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s'))
      (ensures ma_sim_session_matches_ideal_request s') =
  _sessreq_frame s s'

/// --- Clause C: ma_output_token_matches_sim_phase -------------------------

/// Frame across a transition that leaves the simulator session map untouched and
/// only shrinks (or keeps) the simulator-to-ideal channel (Input, ideal
/// initiate, ideal deliver).
private
let _tokphase_frame (s s': ideal_system_state)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        (forall (p: participant_id) (i: session_id).
           ma_get_sim_participant_session_state (s2p_state s') p i ==
           ma_get_sim_participant_session_state (s2p_state s) p i) /\
        (forall (i: session_id) (p: participant_id).
           Set.mem (ma_output_term i p) s'.internal.sim_to_ideal_channel ==>
           Set.mem (ma_output_term i p) s.internal.sim_to_ideal_channel))
      (ensures ma_output_token_matches_sim_phase s') =
  ()

/// Message1 send: the simulator-to-ideal channel is unchanged and a new
/// initiator session (with `ack_sent = false`) is created.  No output token can
/// reference that session yet: send1 is enabled only when no session exists for
/// `(lid.party, lid.session)`, so the pre-state clause rules out a pending
/// `Output(lid.session, lid.party)` token.
private
let _tokphase_send1 (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        ma_sim_send_message1_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_output_token_matches_sim_phase s') =
  eliminate exists (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message1_enabled
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    t == ma_nsl_message1_term lid.session lid.party lid.peer initiator_nonce responder_pubkey /\
    s2p_state s' ==
      ma_sim_send_message1_state (s2p_state s) lid.session lid.party lid.peer initiator_nonce
  returns ma_output_token_matches_sim_phase s'
  with _he.
    (let sp = s2p_state s in
     assert (s'.internal.sim_to_ideal_channel == s.internal.sim_to_ideal_channel);
     assert (ma_get_sim_participant_session_state sp lid.party lid.session == None);
     introduce forall (i: session_id) (p: participant_id).
       Set.mem (ma_output_term i p) s'.internal.sim_to_ideal_channel ==>
       (match ma_get_sim_participant_session_state (s2p_state s') p i with
        | Some (SimInitiatorSession ist) -> ist.initiator == p /\ ist.ack_sent
        | Some (SimResponderSession rst) -> rst.responder == p /\ rst.output_forwarded
        | None -> False)
     with introduce _ ==> _ with _hmem.
       _send1_get_updated sp lid.session lid.party lid.peer initiator_nonce p i)

/// Message2 send: dual of send1; channel unchanged, new responder session with
/// `output_forwarded = false`, and no token can reference it yet.
private
let _tokphase_send2 (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        ma_sim_send_message2_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_output_token_matches_sim_phase s') =
  eliminate exists (initiator_nonce responder_nonce: nonce)
                   (responder_key: priv_key)
                   (initiator_pubkey: term {PubKey? initiator_pubkey}).
    ma_sim_send_message2_enabled
      (s2p_state s) lid.session lid.party lid.peer
      initiator_nonce responder_nonce responder_key initiator_pubkey /\
    t == ma_nsl_message2_term
      lid.session lid.peer lid.party initiator_nonce responder_nonce initiator_pubkey /\
    s2p_state s' == ma_sim_send_message2_state
      (s2p_state s) lid.session lid.party lid.peer initiator_nonce responder_nonce responder_key
  returns ma_output_token_matches_sim_phase s'
  with _he.
    (let sp = s2p_state s in
     assert (ma_get_sim_participant_session_state sp lid.party lid.session == None))

/// Message3 send: adds the token `Output(lid.session, lid.party)` and flips the
/// firing initiator session's `ack_sent` to `true`.  The new token pins exactly
/// that just-acknowledged session; every other token is pre-existing and its
/// session is unchanged.
private
let _tokphase_send3 (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        ma_sim_send_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer t (s2p_state s'))
      (ensures ma_output_token_matches_sim_phase s') =
  eliminate exists (responder_nonce: nonce)
                   (initiator_key: priv_key)
                   (responder_pubkey: term {PubKey? responder_pubkey}).
    ma_sim_send_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key responder_pubkey /\
    t == ma_nsl_message3_term lid.session lid.party lid.peer responder_nonce responder_pubkey /\
    s2p_state s' == ma_sim_send_message3_state
      (s2p_state s) lid.session lid.party lid.peer responder_nonce initiator_key
  returns ma_output_token_matches_sim_phase s'
  with _he.
    (let sp = s2p_state s in
     assert (Some? (ma_sim_initiator_session_state sp lid.party lid.session));
     assert (s'.internal.sim_to_ideal_channel ==
       Set.add (ma_output_term lid.session lid.party) sp.internal.sim_to_ideal_channel);
     introduce forall (i: session_id) (p: participant_id).
       Set.mem (ma_output_term i p) s'.internal.sim_to_ideal_channel ==>
       (match ma_get_sim_participant_session_state (s2p_state s') p i with
        | Some (SimInitiatorSession ist) -> ist.initiator == p /\ ist.ack_sent
        | Some (SimResponderSession rst) -> rst.responder == p /\ rst.output_forwarded
        | None -> False)
     with introduce _ ==> _ with _hmem.
       ma_sim_send_message3_state_get_updated_sim_participant_session_state
         sp lid.session lid.party lid.peer responder_nonce initiator_key p i)

/// Message3 receive: dual of send3; adds `Output(lid.session, lid.party)` and
/// flips the firing responder session's `output_forwarded`.
private
let _tokphase_recv3 (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        ma_sim_receive_message3_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer (s2p_state s'))
      (ensures ma_output_token_matches_sim_phase s') =
  eliminate exists (responder_key: priv_key).
    ma_sim_receive_message3_enabled
      (s2p_state s) lid.session lid.party lid.peer responder_key /\
    s2p_state s' ==
      ma_sim_receive_message3_state (s2p_state s) lid.session lid.party lid.peer responder_key
  returns ma_output_token_matches_sim_phase s'
  with _he.
    (let sp = s2p_state s in
     assert (Some? (ma_sim_responder_session_state sp lid.party lid.session));
     ma_sim_receive_message3_state_sim_to_ideal_channel_eq
       sp lid.session lid.party lid.peer responder_key;
     assert (s'.internal.sim_to_ideal_channel ==
       Set.add (ma_output_term lid.session lid.party) sp.internal.sim_to_ideal_channel);
     introduce forall (i: session_id) (p: participant_id).
       Set.mem (ma_output_term i p) s'.internal.sim_to_ideal_channel ==>
       (match ma_get_sim_participant_session_state (s2p_state s') p i with
        | Some (SimInitiatorSession ist) -> ist.initiator == p /\ ist.ack_sent
        | Some (SimResponderSession rst) -> rst.responder == p /\ rst.output_forwarded
        | None -> False)
     with introduce _ ==> _ with _hmem.
       ma_sim_receive_message3_state_get_updated_sim_participant_session_state
         sp lid.session lid.party lid.peer responder_key p i)

/// Ideal initiate: the simulator-to-ideal channel and simulator sessions are
/// unchanged.
private
let _tokphase_initiate (s s': ideal_system_state) (lid: ma_label_id)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        ma_ideal_initiate_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s'))
      (ensures ma_output_token_matches_sim_phase s') =
  _tokphase_frame s s'

/// Ideal deliver: removes a token and leaves simulator sessions unchanged; every
/// surviving token keeps its (unchanged) post-acknowledgment session.
private
let _tokphase_deliver (s s': ideal_system_state) (lid: ma_label_id) (t: term)
    : Lemma
      (requires
        ma_output_token_matches_sim_phase s /\
        ma_ideal_deliver_protocol_transition
          (s2p_state s) lid.session lid.party lid.peer lid.role t (s2p_state s'))
      (ensures ma_output_token_matches_sim_phase s') =
  _tokphase_frame s s'

/// ===========================================================================
/// Top-level theorems
/// ===========================================================================

let ma_ideal_system_inv_init corrupt key_directory know0 =
  // `ma_ideal_system_inv` is `opaque_to_smt`; reveal its definition so the SMT
  // can assemble it from the conjuncts established below.
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv)
    (ma_ideal_system_inv corrupt key_directory (ma_ideal_system corrupt key_directory know0).init);
  // Conjunct 1: reuse the standalone tested-system invariant.
  ma_ideal_core_inv_init corrupt key_directory know0;
  let s0 = (ma_ideal_system corrupt key_directory know0).init in
  // Conjunct 2: the initial `used_nonces` is `ma_knowledge_nonces know0`,
  // the input bag is empty, and there are no stored simulator sessions.
  assert (s0.know == know0);
  assert (s0.internal.used_nonces == ma_knowledge_nonces know0);
  _subset_refl (ma_knowledge_nonces s0.know);
  // Conjunct 3 (directory injectivity) is a hypothesis.
  // Conjunct 4: Message2 provenance holds vacuously: the antecedent requires an
  // existing simulator initiator session, but the initial session map is empty.
  introduce forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
    matches_initiator_state s0 i a b ni /\
    PartialMap.sel s0.internal.key_directory a == Some ik /\
    derivable s0.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
    not (Set.mem a corrupt) /\
    not (Set.mem b corrupt) ==>
    matches_responder_state s0 i b a nr
  with introduce _ ==> _ with _h.
    (assert (ma_sim_initiator_session_state (s2p_state s0) a i == None));
  assert (ma_message2_provenance corrupt s0);
  // (The derivable-Message2 clause is not a conjunct; it is re-derived in
  // `ma_ideal_system_inv_elim` from this provenance clause + injectivity.)
  // Conjunct 5: Message3 provenance holds vacuously: the antecedent requires an
  // existing simulator responder session, but the initial session map is empty.
  introduce forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
    matches_responder_state s0 i b a nr /\
    PartialMap.sel s0.internal.key_directory b == Some pk /\
    derivable s0.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
    not (Set.mem a corrupt) /\
    not (Set.mem b corrupt) ==>
    matches_initiator_peer_state s0 i a b
  with introduce _ ==> _ with _h.
    (assert (ma_sim_responder_session_state (s2p_state s0) b i == None));
  assert (ma_message3_provenance corrupt s0);
  // (The derivable-Message3 clause is likewise re-derived in
  // `ma_ideal_system_inv_elim`.)
  // Conjunct 6: holds vacuously: the initial simulator-to-ideal channel is
  // empty, so no `Output` is in flight.
  introduce forall (i: session_id) (p: participant_id).
    Set.mem (ma_output_term i p) (s2p_state s0).internal.sim_to_ideal_channel ==>
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s0) i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s0) i)))
  with introduce _ ==> _ with _h. ();
  // Conjunct 7 (Clause A): vacuous, the initial simulator session map is empty,
  // so every `ma_get_sim_participant_session_state` is `None`.
  introduce forall (session: session_id) (participant: participant_id).
    (match ma_get_sim_participant_session_state (s2p_state s0) participant session with
     | Some (SimInitiatorSession ist) ->
       ist.initiator == participant /\
       Set.mem { party = participant; peer = ist.responder; role = Initiator }
         (ma_session_requests (s2p_state s0) session)
     | Some (SimResponderSession rst) ->
       rst.responder == participant /\
       Set.mem { party = participant; peer = rst.initiator; role = Responder }
         (ma_session_requests (s2p_state s0) session)
     | None -> True)
  with
    assert (ma_get_sim_participant_session_state (s2p_state s0) participant session == None);
  assert (ma_sim_session_matches_ideal_request s0);
  // Conjunct 8 (Clause C): vacuous, the initial simulator-to-ideal channel is empty.
  introduce forall (session: session_id) (participant: participant_id).
    Set.mem (ma_output_term session participant) s0.internal.sim_to_ideal_channel ==>
    (match ma_get_sim_participant_session_state (s2p_state s0) participant session with
     | Some (SimInitiatorSession ist) -> ist.initiator == participant /\ ist.ack_sent
     | Some (SimResponderSession rst) -> rst.responder == participant /\ rst.output_forwarded
     | None -> False)
  with introduce _ ==> _ with _h. ();
  assert (ma_output_token_matches_sim_phase s0)

// The final conjunction assembles eight per-clause sub-proofs; verifying them as
// one monolithic VC is brittle, so split per conjunct (each sub-goal is
// discharged by its dedicated helper).
#push-options "--split_queries always"
let ma_ideal_system_inv_preserved corrupt key_directory know0 s s' l =
  // `ma_ideal_system_inv` is `opaque_to_smt`; reveal its definition at both `s`
  // (to access the inductive hypothesis) and `s'` (to assemble the goal).
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv) (ma_ideal_system_inv corrupt key_directory s);
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv) (ma_ideal_system_inv corrupt key_directory s');
  // Conjunct 1: reuse the standalone preservation theorem.  It also
  // re-establishes the (bundled) freshness invariant `ma_ideal_used_nonces_invariant`
  // and the stored-nonce-secrecy conjuncts at `s'`, so no separate freshness
  // dispatch is needed here.
  ma_ideal_core_inv_preserved corrupt key_directory know0 s s' l;
  // Conjunct 3 (directory injectivity) carries over: same `key_directory`.
  // Conjunct 4: Message2 provenance is preserved.  (The derivable-Message2
  // authentication clause is not a conjunct; it is re-derived on demand in
  // `ma_ideal_system_inv_elim` from this provenance clause + injectivity.)
  _m2_provenance_preserved corrupt key_directory know0 s s' l;
  // Conjunct 5: Message3 provenance is preserved.  (Likewise, the
  // derivable-Message3 clause is re-derived in `ma_ideal_system_inv_elim`.)
  _m3_provenance_preserved corrupt key_directory know0 s s' l;
  // The complementary-request preservation helpers `_comp_send3` / `_comp_recv3`
  // consume the (kept) Message2/Message3 provenance conjuncts at the *pre*-state
  // `s`, plus secrecy and directory injectivity, and recover the matching
  // session pointwise via the authenticity lemmas.
  // Conjunct 6: every in-flight `Output` keeps its complementary request pair.
  (match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns ma_output_has_complementary_request corrupt s'
    with _pf.
      _comp_preserved_frame corrupt s s'
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns ma_output_has_complementary_request corrupt s'
    with _hi. _comp_initiate corrupt s s' lid
    and _hr.
      (match lid.role with
       | Responder -> _comp_recv3 corrupt key_directory s s' lid
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns ma_output_has_complementary_request corrupt s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns ma_output_has_complementary_request corrupt s'
            with _h1. _comp_send1 corrupt s s' lid t
            and _h3. _comp_send3 corrupt key_directory s s' lid t
          | Responder -> _comp_send2 corrupt s s' lid t)
       | IoSend -> _comp_deliver corrupt s s' lid t));
  // Conjunct 7 (Clause A): every simulator session keeps its matching request.
  (match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns ma_sim_session_matches_ideal_request s'
    with _pf.
      _sessreq_frame s s'
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns ma_sim_session_matches_ideal_request s'
    with _hi. _sessreq_initiate s s' lid
    and _hr.
      (match lid.role with
       | Responder -> _sessreq_recv3 s s' lid
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns ma_sim_session_matches_ideal_request s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns ma_sim_session_matches_ideal_request s'
            with _h1. _sessreq_send1 s s' lid t
            and _h3. _sessreq_send3 s s' lid t
          | Responder -> _sessreq_send2 s s' lid t)
       | IoSend -> _sessreq_deliver s s' lid t));
  // Conjunct 8 (Clause C): every in-flight `Output` token pins its session to
  // the post-acknowledgment phase.
  (match l with
  | Input d ->
    eliminate exists (t: term).
      adversary_aenc.derive d s.know == Some t /\
      s'.inputs == Bag.insert t s.inputs /\
      s'.know == s.know /\
      s'.internal == s.internal
    returns ma_output_token_matches_sim_phase s'
    with _pf.
      _tokphase_frame s s'
  | Internal lid ->
    ma_ideal_valid_transitions (s2p_state s) (Protocol.Internal lid) (s2p_state s');
    eliminate
      ma_ideal_initiate_protocol_transition
        (s2p_state s) lid.session lid.party lid.peer lid.role (s2p_state s')
      \/ (match lid.role with
          | Responder ->
            ma_sim_receive_message3_protocol_transition
              (s2p_state s) lid.session lid.party lid.peer (s2p_state s')
          | Initiator -> False)
    returns ma_output_token_matches_sim_phase s'
    with _hi. _tokphase_initiate s s' lid
    and _hr.
      (match lid.role with
       | Responder -> _tokphase_recv3 s s' lid
       | Initiator -> ())
  | Observable o lid ->
    eliminate exists (t: term).
      ma_ideal_protocol_transition
        (s2p_state s) (Protocol.Observable o t lid) (s2p_state s') /\
      s'.know == Seq.snoc s.know t
    returns ma_output_token_matches_sim_phase s'
    with _pf.
      (ma_ideal_valid_transitions
         (s2p_state s) (Protocol.Observable o t lid) (s2p_state s');
       match o with
       | NetSend ->
         (match lid.role with
          | Initiator ->
            eliminate
              ma_sim_send_message1_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
              \/ ma_sim_send_message3_protocol_transition
                (s2p_state s) lid.session lid.party lid.peer t (s2p_state s')
            returns ma_output_token_matches_sim_phase s'
            with _h1. _tokphase_send1 s s' lid t
            and _h3. _tokphase_send3 s s' lid t
          | Responder -> _tokphase_send2 s s' lid t)
       | IoSend -> _tokphase_deliver s s' lid t))
#pop-options

let ma_ideal_system_inv_elim corrupt key_directory s =
  // Reveal the `opaque_to_smt` invariant so the SMT sees every (transparent)
  // conjunct — including the bundled `ma_ideal_core_inv` (its first conjunct) and
  // its two halves `ma_ideal_secrecy_inv` / `ma_ideal_bookkeeping_inv`, re-exposed
  // directly for consumers that need the whole core invariant.  Every `ensures`
  // entry is then a (possibly transitive) conjunct, so no further derivation is
  // needed.
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv) (ma_ideal_system_inv corrupt key_directory s)
  // The Message2/Message3 authenticity consequences are not exposed here;
  // consumers invoke `ma_message2_provenance_matches_responder` /
  // `ma_message3_provenance_matches_initiator` pointwise instead.
