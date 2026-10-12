module MA.IdealInvariants

/// Single inductive invariant for the NSL mutual-authentication ideal+simulator
/// *tested system* (`ma_ideal_system`).
///
/// This module owns the full ideal-side invariant: it bundles the protocol
/// state invariant (`ma_ideal_state_inv`), the cryptographic-secrecy facts
/// (private keys and nonces unguessable), the monotone nonce-freshness
/// discipline, directory injectivity, and the Message2/Message3
/// authentication-correspondence (provenance) clauses, together with the strong
/// `output-has-complementary-request` consequence that justifies the full I1
/// property.
///
/// All the per-clause predicates live here (rather than in
/// `MA.ObservationalBisimulation.Relation`) so that the single top-level
/// invariant `ma_ideal_system_inv` can be referenced both by `ma_bisim_relation`
/// and by the right-movable-modulo-invariant lemmas in `MA.PartitioningRole`.
///
/// The cryptographic-secrecy conjuncts are genuine inductive invariants of the
/// tested system: knowledge grows only by appending the term emitted on an
/// `Observable` step (a session ciphertext `Aenc (Pair (SessionId i) m) k` whose
/// encryption key `k` is a directory private key, or the public authenticated
/// term), and the symbolic adversary corollaries
/// (`nonces_learned_from_session_ciphertext_already_derivable` etc.) reduce any
/// new derivation back to a derivation from the previous knowledge.

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

/// -------------------------------------------------------------------------
/// State invariant for the ideal+simulator protocol.
///
/// This invariant over-approximates the reachable states of the ideal system
/// and is what the role-sensitive right-movability proof
/// (`MA.PartitioningRole`) conditions on (via
/// `ObservationalBisimulation.right_movable_mod_inv`). Every conjunct refers
/// only to `s.internal`, so adversary `Input` transitions (which touch only the
/// input bag) preserve it trivially.
/// -------------------------------------------------------------------------

/// I2: at most one authentication request per party per session.
unfold
let ma_ideal_inv_one_request_per_party (s: ideal_proto_state) : prop =
  forall (i: session_id) (r1 r2: auth_request).
    Set.mem r1 (ma_session_requests s i) /\
    Set.mem r2 (ma_session_requests s i) /\
    r1.party == r2.party ==> r1 == r2

/// H_auth_init: a leaked `Authenticating(i, p, q, Initiator)` notification on
/// the ideal→sim channel implies the corresponding request was recorded.
unfold
let ma_ideal_inv_auth_init_has_request (s: ideal_proto_state) : prop =
  forall (i: session_id) (p q: participant_id).
    Set.mem (ma_authenticating_term i p q Initiator) s.internal.ideal_to_sim_channel ==>
    Set.mem ({ party = p; peer = q; role = Initiator }) (ma_session_requests s i)

/// H_auth_resp: same as above for the `Responder` direction.
unfold
let ma_ideal_inv_auth_resp_has_request (s: ideal_proto_state) : prop =
  forall (i: session_id) (p q: participant_id).
    Set.mem (ma_authenticating_term i p q Responder) s.internal.ideal_to_sim_channel ==>
    Set.mem ({ party = p; peer = q; role = Responder }) (ma_session_requests s i)

/// Conjunction of the proto-state-level inductive base invariants of the
/// ideal+simulator protocol that are not subsumed by ideal-system lemmas.
let ma_ideal_state_inv (s: ideal_proto_state) : prop =
  ma_ideal_inv_one_request_per_party s /\
  ma_ideal_inv_auth_init_has_request s /\
  ma_ideal_inv_auth_resp_has_request s

/// The invariant holds at the initial ideal state.
val ma_ideal_state_inv_init
      (key_directory: PartialMap.t participant_id priv_key)
      (corrupt: Set.set participant_id)
      (know0: knowledge term)
    : Lemma (ensures ma_ideal_state_inv (ma_ideal_protocol_init key_directory corrupt know0))

/// The invariant is preserved by every ideal+simulator protocol transition.
val ma_ideal_state_inv_preserved
      (s: ideal_proto_state)
      (l: Protocol.label term ma_effect ma_label_id)
      (s': ideal_proto_state)
    : Lemma
      (requires ma_ideal_state_inv s /\ ma_ideal_protocol_transition s l s')
      (ensures ma_ideal_state_inv s')

/// ===========================================================================
/// Clause predicates.
/// ===========================================================================

// The private/public key pair for each participant is unique
let ma_key_directory_injective
      (key_directory: PartialMap.t participant_id priv_key)
    : prop =
  forall (participant1 participant2: participant_id)
         (key: priv_key).
    PartialMap.sel key_directory participant1 == Some key /\
    PartialMap.sel key_directory participant2 == Some key ==>
    participant1 == participant2

/// Every nonce syntactically present in a term has already been marked used.
/// This is the network/knowledge side of the monotone freshness discipline.
let ma_term_nonces_are_used
      (used_nonces: Set.set nonce)
      (t: term)
    : prop =
  Set.subset (ma_term_nonces t) used_nonces

let ma_inputs_nonces_are_used
      (used_nonces: Set.set nonce)
      (inputs: bag term)
    : prop =
  forall (input_t: term).
    Bag.mem input_t inputs ==> ma_term_nonces_are_used used_nonces input_t

let ma_knowledge_nonces_are_used
      (used_nonces: Set.set nonce)
      (know: knowledge term)
    : prop =
  Set.subset (ma_knowledge_nonces know) used_nonces

let ma_ideal_stored_nonces_are_used
      (s_q: ideal_system_state)
    : prop =
  forall (participant: participant_id) (session: session_id) (n: nonce).
    match PartialMap.sel (ma_sim_participant_sessions (s2p_state s_q) participant) session with
    | Some (SimInitiatorSession initiator_state) ->
      initiator_state.initiator_nonce == n ==> Set.mem n s_q.internal.used_nonces
    | Some (SimResponderSession responder_state) ->
      responder_state.responder_nonce == n ==> Set.mem n s_q.internal.used_nonces
    | None -> True

let ma_ideal_used_nonces_invariant
      (s_q: ideal_system_state)
    : prop =
  ma_ideal_stored_nonces_are_used s_q /\
  ma_inputs_nonces_are_used s_q.internal.used_nonces s_q.inputs /\
  ma_knowledge_nonces_are_used s_q.internal.used_nonces s_q.know

(**
  Private keys for non-corrupt participants are not derivable by the adversary.
  Corrupt participants' keys may be known to the adversary.
*)
let ma_private_keys_not_derivable
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: TestedSystem.state term 'internal)
    : prop =
  forall (participant: participant_id) (k: priv_key) (d: adv.derivation).
    PartialMap.sel key_directory participant == Some k /\
    not (Set.mem participant corrupt) ==>
    not (adv.derive d s.know = Some (PrivKey k))

(**
  Responder nonces stored in simulator-side responder sessions are valid
  protocol secrets when neither the responder nor initiator is corrupt.
  The responder nonce is in Message2, encrypted to the initiator; if the
  initiator is corrupt the adversary can decrypt Message2 and learn it.
  If the responder is corrupt the adversary is the responder and chose the nonce.
*)
let ma_valid_responder_nonces_not_derivable
      (corrupt: Set.set participant_id)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
         (responder initiator: participant_id)
         (responder_nonce: nonce)
         (d: adv.derivation).
    match ma_sim_responder_session_state (s2p_state s_q) responder session with
    | Some responder_state ->
      responder_state.responder == responder /\
      responder_state.initiator == initiator /\
      responder_state.responder_nonce == responder_nonce /\
      not (Set.mem responder corrupt) /\
      not (Set.mem initiator corrupt) ==>
      not (adv.derive d s_q.know = Some (Nonce responder_nonce))
    | None -> True

(**
  Initiator nonces stored in simulator-side initiator sessions are valid
  protocol secrets when neither the initiator nor responder is corrupt.
  The initiator nonce is encrypted to the responder in Message1; if the
  responder is corrupt the adversary can decrypt Message1 and learn it.
  If the initiator is corrupt the adversary is the initiator and chose the nonce.
*)
let ma_valid_initiator_nonces_not_derivable
      (corrupt: Set.set participant_id)
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id)
         (initiator responder: participant_id)
         (initiator_nonce: nonce)
         (d: adv.derivation).
    match ma_sim_initiator_session_state (s2p_state s_q) initiator session with
    | Some initiator_state ->
      initiator_state.initiator == initiator /\
      initiator_state.responder == responder /\
      initiator_state.initiator_nonce == initiator_nonce /\
      not (Set.mem initiator corrupt) /\
      not (Set.mem responder corrupt) ==>
      not (adv.derive d s_q.know = Some (Nonce initiator_nonce))
    | None -> True

/// ===========================================================================
/// Simulator-session / request bookkeeping clauses:
///
///  * `ma_sim_session_matches_ideal_request` (session ==> request): a simulator
///    session is created only after the corresponding authentication request was
///    recorded (the `auth*_has_request` conjuncts of `ma_ideal_state_inv`), and
///    requests are never retracted, so every stored simulator session has a
///    matching request whose party field equals the storage key.
///
///  * `ma_output_token_matches_sim_phase` (output token ==> phase): an
///    `Output(i, p)` delivery command is placed on the simulator-to-ideal
///    channel only by the Message3 send/receive steps, which simultaneously
///    record `ack_sent` / `output_forwarded` on `p`'s simulator session; no step
///    regresses those phase flags or removes a session, so a pending output token
///    always pins its session to the post-acknowledgment phase.
///
/// NOTE: the *converse* request-matches-session clause
/// (`ma_ideal_request_matches_sim_session`, "every request has a matching
/// session") is deliberately NOT included here.  A standalone `ma_ideal_initiate`
/// transition records a request before the simulator session exists, so that
/// clause is not an inductive invariant of the ideal system; it remains a
/// conjunct of `ma_bisim_relation` instead (where the paired bisimulation steps
/// keep request and session creation atomic).

let ma_sim_session_matches_ideal_request
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id) (participant: participant_id).
    match ma_get_sim_participant_session_state (s2p_state s_q) participant session with
    | Some (SimInitiatorSession initiator_state) ->
      initiator_state.initiator == participant /\
      Set.mem
        { party = participant; peer = initiator_state.responder; role = Initiator }
        (ma_session_requests (s2p_state s_q) session)
    | Some (SimResponderSession responder_state) ->
      responder_state.responder == participant /\
      Set.mem
        { party = participant; peer = responder_state.initiator; role = Responder }
        (ma_session_requests (s2p_state s_q) session)
    | None -> True

let ma_output_token_matches_sim_phase
      (s_q: ideal_system_state)
    : prop =
  forall (session: session_id) (participant: participant_id).
    Set.mem (ma_output_term session participant) s_q.internal.sim_to_ideal_channel ==>
    (match ma_get_sim_participant_session_state (s2p_state s_q) participant session with
    | Some (SimInitiatorSession initiator_state) ->
      initiator_state.initiator == participant /\ initiator_state.ack_sent
    | Some (SimResponderSession responder_state) ->
      responder_state.responder == participant /\ responder_state.output_forwarded
    | None -> False)

let matches_initiator_state
    (s_q: ideal_system_state)
    (session: session_id)
    (initiator responder: participant_id)
    (initiator_nonce: nonce)
    : prop =
  match ma_sim_initiator_session_state (s2p_state s_q) initiator session with
  | Some initiator_state ->
    initiator_state.initiator == initiator /\
    initiator_state.responder == responder /\
    initiator_state.initiator_nonce == initiator_nonce
  | None -> False

let matches_responder_state
    (s_q: ideal_system_state)
    (session: session_id)
    (responder initiator: participant_id)
    (responder_nonce: nonce)
    : prop =
  match ma_sim_responder_session_state (s2p_state s_q) responder session with
  | Some responder_state ->
    responder_state.responder == responder /\
    responder_state.initiator == initiator /\
    responder_state.responder_nonce == responder_nonce
  | None -> False

let matches_initiator_peer_state
    (s_q: ideal_system_state)
    (session: session_id)
    (initiator responder: participant_id)
    : prop =
  match ma_sim_initiator_session_state (s2p_state s_q) initiator session with
  | Some initiator_state ->
    initiator_state.initiator == initiator /\
    initiator_state.responder == responder
  | None -> False

let matches_initiator_state_eq_states
    (s_q: ideal_system_state)
    (s_q': ideal_system_state)
    (session: session_id)
    (initiator responder: participant_id)
    (initiator_nonce: nonce)
    : Lemma
        (requires
          ma_sim_initiator_session_state (s2p_state s_q) initiator session
          == ma_sim_initiator_session_state (s2p_state s_q') initiator session)
        (ensures
          matches_initiator_state s_q session initiator responder initiator_nonce
          == matches_initiator_state s_q' session initiator responder initiator_nonce)
= ()

let matches_responder_state_eq_states
    (s_q: ideal_system_state)
    (s_q': ideal_system_state)
    (session: session_id)
    (responder initiator: participant_id)
    (responder_nonce: nonce)
    : Lemma
        (requires
          ma_sim_responder_session_state (s2p_state s_q) responder session
          == ma_sim_responder_session_state (s2p_state s_q') responder session)
        (ensures
          matches_responder_state s_q session responder initiator responder_nonce
          == matches_responder_state s_q' session responder initiator responder_nonce)
= ()

let matches_initiator_peer_state_eq_states
    (s_q: ideal_system_state)
    (s_q': ideal_system_state)
    (session: session_id)
    (initiator responder: participant_id)
    : Lemma
        (requires
          ma_sim_initiator_session_state (s2p_state s_q) initiator session
          == ma_sim_initiator_session_state (s2p_state s_q') initiator session)
        (ensures
          matches_initiator_peer_state s_q session initiator responder
          == matches_initiator_peer_state s_q' session initiator responder)
= ()

/// ===========================================================================
/// Message-provenance clauses.
/// ===========================================================================
///
/// Message2 provenance.
///
/// The NSL Message2 ciphertext
///   `ma_nsl_message2_term i A B ni nr (PubKey ik)
///      = Aenc (Pair (SessionId i) (Pair (Nonce ni) (Pair (Nonce nr)
///               (ParticipantId B)))) ik`
/// carries the *responder* identity `B`, both nonces `ni`/`nr`, and is
/// encrypted with the *initiator's* private key `ik`.  Crucially it does NOT
/// carry the initiator identity `A` on the wire (`A` is recovered only through
/// the encryption key `ik` together with directory injectivity).
///
/// `ma_message2_provenance` records that whenever a Message2 ciphertext is
/// derivable from the adversary knowledge, the simulator responder session for
/// the same session `i`, responder identity `b`, believed initiator `a`, and
/// responder nonce `nr` already exists.
///
/// The clause is conditioned on `ni` being the nonce of an *existing* simulator
/// initiator session (`matches_initiator_state s i a b ni`), with believed
/// responder `b` equal to the responder identity carried by the ciphertext.  The
/// initiator `a` (which is *not* on the wire) is pinned to the encryption key by
/// `key_directory a == Some ik`; directory injectivity then makes `a` unique.
///
/// A stored initiator nonce is fresh when its session is created
/// (`ma_sim_nonce_is_fresh`) and never adversary-derivable
/// (`ma_valid_initiator_nonces_not_derivable`), so a derivable Message2 carrying
/// it cannot have been forged and must have been observed
/// (`built_with_subterms`); that is how this clause stays inductive. Because the
/// antecedent requires a stored session, the clause holds *vacuously* at the
/// initial state (empty session map) with no assumption on the adversary's
/// initial knowledge.
/// `ma_message2_provenance` is conditional on neither party being corrupt.
/// When the responder is corrupt the adversary learns the initiator nonce from
/// Message1 (encrypted to the corrupt responder) and can forge Message2; when
/// the initiator is corrupt the adversary chose the initiator nonce.
let ma_message2_provenance
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (i: session_id) (a b: participant_id) (ni nr: nonce) (ik: priv_key).
    matches_initiator_state s i a b ni /\
    PartialMap.sel s.internal.key_directory a == Some ik /\
    derivable s.know (ma_nsl_message2_term i a b ni nr (PubKey ik)) /\
    not (Set.mem a corrupt) /\
    not (Set.mem b corrupt) ==>
    matches_responder_state s i b a nr

/// ===========================================================================
/// Message3 provenance.
///
/// The NSL Message3 ciphertext
///   `ma_nsl_message3_term i a b nr (PubKey pk)
///      = Aenc (Pair (SessionId i) (Nonce nr)) pk`
/// carries ONLY the session id `i`, the responder nonce `nr`, and is encrypted
/// with the *responder's* private key `pk`.  Crucially it carries NEITHER the
/// initiator identity `a` NOR the responder identity `b` on the wire (both `a`
/// and `b` are vacuous arguments of the constructor, kept only to match its
/// arity; the witnessing participants are recovered existentially below).
///
/// `ma_message3_provenance` records that whenever a Message3 ciphertext is
/// derivable from the adversary knowledge, there already exist matching
/// simulator sessions for the same session `i`: a responder session owned by
/// the participant `b0` whose key `pk` encrypts the ciphertext (with believed
/// initiator `a0` and responder nonce `nr`), together with the complementary
/// initiator session of `a0` whose believed responder is `b0`.
///
/// As with Message2, the clause is conditioned on `nr` being the nonce of an
/// *existing* simulator responder session.  Unlike Message2, neither participant
/// appears on the wire, so the universally-quantified responder `b` is pinned to
/// the session by `matches_responder_state s i b a nr`, and `b` is further pinned
/// to the encryption key by `key_directory b == Some pk` (directory injectivity
/// then makes `b` unique). A stored responder nonce is fresh at creation and
/// never adversary-derivable (`ma_valid_responder_nonces_not_derivable`), so a
/// derivable Message3 carrying it must have been observed rather than forged; and
/// the antecedent is false at the initial (empty) session map, so the clause holds
/// vacuously there with no assumption on the adversary's initial knowledge.
/// `ma_message3_provenance` is conditional on neither party being corrupt.
/// When the initiator is corrupt the adversary learns the responder nonce from
/// Message2 (encrypted to the corrupt initiator) and can forge Message3; when
/// the responder is corrupt the adversary chose the responder nonce.
let ma_message3_provenance
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (i: session_id) (a b: participant_id) (nr: nonce) (pk: priv_key).
    matches_responder_state s i b a nr /\
    PartialMap.sel s.internal.key_directory b == Some pk /\
    derivable s.know (ma_nsl_message3_term i a b nr (PubKey pk)) /\
    not (Set.mem a corrupt) /\
    not (Set.mem b corrupt) ==>
    matches_initiator_peer_state s i a b

/// ===========================================================================
/// Strong injective-agreement consequence.
///
/// Whenever an `Output(i, p)` is in flight on the simulator-to-ideal channel,
/// the session `i` has recorded BOTH `p`'s own authentication request AND the
/// complementary request of `p`'s peer (with the dual role).  This is the
/// strong form of the agreement property I1: an output for `p` is forwarded
/// only after the genuine matching conversation exists on both sides.  The
/// complement on the two output-emitting steps (Message3 send and Message3
/// receive) is recovered via the pointwise Message2/Message3 authenticity
/// lemmas, which give the peer's matching session, hence (via the ideal-state
/// session-has-request invariants) the peer's recorded request.
/// When Output(i,p) is pending, p's own request always exists. When both p
/// and the peer are non-corrupt, the complementary request also exists (since
/// genuine NSL messages were needed to advance to that point). When at least
/// one party is corrupt, only p's request is guaranteed.
let ma_output_has_complementary_request
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (i: session_id) (p: participant_id).
    Set.mem (ma_output_term i p) (s2p_state s).internal.sim_to_ideal_channel ==>
    (exists (peer: participant_id) (r: role).
       Set.mem ({ party = p; peer = peer; role = r }) (ma_session_requests (s2p_state s) i) /\
       (Set.mem p corrupt \/ Set.mem peer corrupt \/
        Set.mem ({ party = peer; peer = p; role = complementary_role r }) (ma_session_requests (s2p_state s) i)))

/// ---------------------------------------------------------------------------
/// Tested-system bookkeeping clauses.

/// C2: every pending protocol input is derivable from current knowledge.
let ma_ideal_inputs_derivable (s: ideal_system_state) : prop =
  forall (t: term). Bag.mem t s.inputs ==> derivable s.know t

/// C_kd: the tested-system key directory is the fixed parameter directory.
/// Needed to connect the per-transition enabling conditions (which read
/// `s.internal.key_directory`) to the secrecy hypotheses about `key_directory`.
let ma_key_directory_matches
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
    : prop =
  s.internal.key_directory == key_directory

/// C_corrupt: the stored corrupt set equals the fixed parameter.
/// Needed to connect the delivery condition (which reads `s.internal.corrupt`)
/// to the secrecy hypotheses about `corrupt`.
let ma_corrupt_set_matches
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  s.internal.corrupt == corrupt

/// C_uniq: each nonce is used by at most one simulator session across all
/// participants and session IDs.  This prevents the adversary from "borrowing"
/// the nonce of one honest session to break secrecy of another after a corrupt
/// party's encryption is observed.
///
/// The invariant follows from the monotone `used_nonces` discipline: every
/// session is created with a *fresh* nonce (not yet in `used_nonces`), and
/// `used_nonces` only grows, so two sessions cannot share a nonce.
let ma_session_nonces_unique (s: ideal_system_state) : prop =
  // Two initiator sessions with the same nonce are the same session/party.
  (forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_initiator_state s sess1 p1 q1 n /\
    matches_initiator_state s sess2 p2 q2 n ==>
    sess1 == sess2 /\ p1 == p2) /\
  // Two responder sessions with the same nonce are the same session/party.
  (forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_responder_state s sess1 p1 q1 n /\
    matches_responder_state s sess2 p2 q2 n ==>
    sess1 == sess2 /\ p1 == p2) /\
  // An initiator nonce cannot equal any responder nonce.
  (forall (sess1 sess2: session_id) (p1 p2 q1 q2: participant_id) (n: nonce).
    matches_initiator_state s sess1 p1 q1 n ==>
    ~(matches_responder_state s sess2 p2 q2 n))

/// `m` is a *protected* session nonce: it belongs to a stored simulator session
/// both of whose participants are non-corrupt — exactly the nonces the secrecy
/// invariant (C4i/C4r) keeps undeducible.  The knowledge-structure invariants
/// below are conditioned on this predicate rather than on a knowledge index.
/// This is what lets them range over *all* of `s.know` — the adversary's initial
/// knowledge `know0` included — with no reference to an initial-knowledge prefix:
/// a protected nonce is fresh when its session is created, so by
/// `ma_ideal_used_nonces_invariant` (every knowledge nonce is a used nonce) it
/// cannot occur in any knowledge term that predates the session.  Hence the only
/// `s.know` terms carrying it are that session's own protocol messages, and the
/// adversary's seeded `know0` terms — carrying no protected nonce — satisfy the
/// invariants vacuously.
let ma_is_honest_session_nonce
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
      (m: nonce)
    : prop =
  exists (sess: session_id) (a b: participant_id).
    (matches_initiator_state s sess a b m \/ matches_responder_state s sess a b m) /\
    not (Set.mem a corrupt) /\ not (Set.mem b corrupt)

/// C_msg1: any Message1-shaped ciphertext occurring (as an `aenc_subterm`)
/// anywhere in `s.know` and carrying a protected nonce `m` names a *non-corrupt*
/// initiator.  A protected nonce only ever appears in its own session's protocol
/// messages, and that session's Message1 names its (non-corrupt) initiator; so a
/// Message1 naming a corrupt party cannot carry a protected nonce.  Used in the
/// corrupt-peer send2 secrecy proof: the received Message1 naming the corrupt
/// peer cannot carry an honest session's nonce.
let ma_honest_msg1_names_non_corrupt
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (idx: nat) (sess: session_id) (m: nonce) (p: participant_id) (k: priv_key).
    idx < Seq.length s.know /\
    aenc_subterm
      (Aenc (Pair (SessionId sess) (Pair (Nonce m) (ParticipantId p))) k)
      (Seq.index s.know idx) /\
    ma_is_honest_session_nonce corrupt s m ==>
    not (Set.mem p corrupt)

/// C_msg2: any Message2-shaped ciphertext occurring in `s.know` and carrying a
/// protected nonce `mr` in the *responder* position names a non-corrupt
/// responder.  Symmetric to C_msg1; used in the corrupt-peer send3 secrecy proof.
let ma_honest_msg2_names_non_corrupt
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (idx: nat) (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key).
    idx < Seq.length s.know /\
    aenc_subterm
      (Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k)
      (Seq.index s.know idx) /\
    ma_is_honest_session_nonce corrupt s mr ==>
    not (Set.mem p corrupt)

/// C_msg2key: any Message2-shaped ciphertext occurring in `s.know` and carrying a
/// protected responder nonce `mr` is encrypted under the directory key of *its*
/// responder session's initiator.  A responder session `(p, initiator, mr)` is
/// created in `send2`, which emits the Message2 encrypted to `initiator`'s public
/// key; so the encryption key `k` equals `key_directory initiator`.  This exposes
/// the key↔initiator link that C_msg2 leaves implicit and lets the send3-provenance
/// proof pin the firing initiator even when that initiator is corrupt.
let ma_honest_msg2_key_matches_initiator
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (idx: nat) (sess: session_id) (mi mr: nonce) (p: participant_id) (k: priv_key).
    idx < Seq.length s.know /\
    aenc_subterm
      (Aenc (Pair (SessionId sess)
              (Pair (Nonce mi) (Pair (Nonce mr) (ParticipantId p)))) k)
      (Seq.index s.know idx) /\
    ma_is_honest_session_nonce corrupt s mr ==>
    (forall (initiator: participant_id).
       matches_responder_state s sess p initiator mr ==>
       PartialMap.sel s.internal.key_directory initiator == Some k)

/// C_shallow: any `s.know` term that carries a protected nonce is `shallow_aenc`
/// (a single-layer ciphertext).  Such a term is necessarily a protocol-emitted
/// message — the adversary's seeded `know0` terms carry no protected nonce (a
/// protected nonce is fresh, hence absent from the initial knowledge) — and every
/// protocol message is shallow.  This is the index-free replacement for "every
/// protocol-emitted know term is shallow": it lets the ciphertext-observation
/// inversion conclude that an *observed* honest ciphertext `Aenc p k` reaching
/// `s.know[idx]` actually *equals* `s.know[idx]` (no proper nesting), which the
/// Message-occurrence and provenance arguments then tie to a session.
let ma_honest_carrier_shallow
      (corrupt: Set.set participant_id)
      (s: ideal_system_state)
    : prop =
  forall (idx: nat) (m: nonce).
    idx < Seq.length s.know /\
    Set.mem m (ma_term_nonces (Seq.index s.know idx)) /\
    ma_is_honest_session_nonce corrupt s m ==>
    shallow_aenc (Seq.index s.know idx)

/// The cryptographic-secrecy invariant: the three "the adversary cannot derive
/// this secret" conjuncts and nothing else.
///
///   C3  directory private keys of non-corrupt participants are not derivable
///       (`ma_private_keys_not_derivable`).
///   C4i/C4r stored-nonce secrecy for sessions whose initiator and responder are
///       both non-corrupt: neither a stored initiator nonce
///       (`ma_valid_initiator_nonces_not_derivable`) nor a stored responder nonce
///       (`ma_valid_responder_nonces_not_derivable`) is adversary-derivable.
///
/// C4i/C4r replace the former (too-strong) "no nonce is derivable" conjunct.
/// They are genuine inductive invariants: a stored session nonce is fresh when
/// generated (`ma_sim_nonce_is_fresh` ⟹ ∉ `used_nonces`) and, since the adversary
/// cannot mint nonces and the freshness invariant (`ma_ideal_used_nonces_invariant`,
/// part of `ma_ideal_bookkeeping_inv`) bounds the knowledge nonces by `used_nonces`,
/// a fresh nonce is not derivable from the prior knowledge; the key-secrecy /
/// no-private-key-subterm reduction lemmas then carry that across every emitting
/// step.  The supporting bookkeeping (freshness, nonce uniqueness, the
/// knowledge↔session correspondence) lives in `ma_ideal_bookkeeping_inv`; the two
/// are always carried together as `ma_ideal_core_inv` because the secrecy
/// preservation proofs consume the bookkeeping facts.
let ma_ideal_secrecy_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
    : prop =
  ma_private_keys_not_derivable corrupt key_directory s /\
  ma_valid_initiator_nonces_not_derivable corrupt s /\
  ma_valid_responder_nonces_not_derivable corrupt s

/// The structural-bookkeeping invariant: the non-secrecy conjuncts that the
/// secrecy preservation proofs (and the bisimulation) rely on.  None of these is
/// itself a "secret X is not derivable" statement — they are state/parameter
/// agreement, monotone freshness, nonce uniqueness, and the knowledge↔session
/// correspondence facts that *support* secrecy.
///
///   C0  `ma_ideal_state_inv` lifted to the tested-system protocol state
///   C_kd the directory is the fixed parameter (`ma_key_directory_matches`)
///   C_corrupt the corruption set is the fixed parameter (`ma_corrupt_set_matches`)
///   C2  every pending input is derivable (`ma_ideal_inputs_derivable`)
///   C_fresh the monotone nonce-freshness discipline
///       (`ma_ideal_used_nonces_invariant`): every nonce occurring in the
///       adversary knowledge, the input bag, or a stored simulator session is in
///       `used_nonces`.
///   C_uniq session nonces are unique across stored simulator sessions
///       (`ma_session_nonces_unique`).
///   C_msg1/C_msg2 knowledge↔session correspondence, conditioned on protected
///       nonces: any Message1/Message2 ciphertext in `s.know` that carries a
///       both-honest session's nonce names a non-corrupt initiator/responder
///       (`ma_honest_msg1_names_non_corrupt` / `ma_honest_msg2_names_non_corrupt`).
///   C_msg2key any Message2 in `s.know` carrying a protected responder nonce is
///       encrypted under the directory key of *its* responder session's initiator
///       (`ma_honest_msg2_key_matches_initiator`).  This exposes the key↔initiator
///       link C_msg2 leaves implicit and lets the Message3-send provenance proof
///       pin the firing initiator even when that initiator is corrupt.
///
/// C_msg1/C_msg2/C_msg2key are conditioned on `ma_is_honest_session_nonce` rather
/// than on a knowledge index, so they range over all of `s.know` (the adversary's
/// initial knowledge included) without any initial-knowledge bookkeeping.
let ma_ideal_bookkeeping_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
    : prop =
  ma_ideal_state_inv (s2p_state s) /\
  ma_key_directory_matches key_directory s /\
  ma_corrupt_set_matches corrupt s /\
  ma_ideal_inputs_derivable s /\
  ma_ideal_used_nonces_invariant s /\
  ma_session_nonces_unique s /\
  ma_honest_msg1_names_non_corrupt corrupt s /\
  ma_honest_msg2_names_non_corrupt corrupt s /\
  ma_honest_msg2_key_matches_initiator corrupt s /\
  ma_honest_carrier_shallow corrupt s

/// The inductive core of the ideal-side invariant: the cryptographic-secrecy
/// conjuncts (`ma_ideal_secrecy_inv`) together with the structural bookkeeping
/// (`ma_ideal_bookkeeping_inv`) they depend on.  These two are bundled because
/// the stored-nonce-secrecy preservation needs the freshness / uniqueness /
/// correspondence bookkeeping; carrying them as a single predicate keeps the
/// preservation lemma (`ma_ideal_core_inv_preserved`) and its consumers concise.
/// It sits below `ma_ideal_system_inv`, which adds directory injectivity, the
/// Message2/Message3 provenance clauses, and the request/output bookkeeping.
let ma_ideal_core_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
    : prop =
  ma_ideal_secrecy_inv corrupt key_directory s /\
  ma_ideal_bookkeeping_inv corrupt key_directory s

/// The single top-level ideal-side inductive invariant: the inductive core
/// invariant (`ma_ideal_core_inv`, bundling the cryptographic-secrecy conjuncts
/// and the structural bookkeeping they depend on), directory injectivity, the
/// Message2 and Message3 provenance invariants, the strong
/// output-has-complementary-request consequence, and the two simulator-session /
/// request bookkeeping clauses (`ma_sim_session_matches_ideal_request` and
/// `ma_output_token_matches_sim_phase`).
///
/// The Message2/Message3 authenticity consequences are NOT separate conjuncts:
/// each follows pointwise from the corresponding provenance clause (plus secrecy
/// and directory injectivity, all kept) and is recovered on demand via
/// `ma_message2_provenance_matches_responder` /
/// `ma_message3_provenance_matches_initiator`.
///
/// Marked `opaque_to_smt` so that carrying it as a conjunct of `ma_bisim_relation`
/// does not flood the many bisimulation destructure proofs with its (heavily
/// quantified) definition.  Sites that need its conjuncts unfold it with
/// `reveal_opaque (`%ma_ideal_system_inv) ...`.
[@@ "opaque_to_smt"]
let ma_ideal_system_inv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
    : prop =
  ma_ideal_core_inv corrupt key_directory s /\
  ma_key_directory_injective key_directory /\
  ma_message2_provenance corrupt s /\
  ma_message3_provenance corrupt s /\
  ma_output_has_complementary_request corrupt s /\
  ma_sim_session_matches_ideal_request s /\
  ma_output_token_matches_sim_phase s

/// The invariant holds at the initial tested-system state.
///
/// The single `requires` is the standard "honest start" assumption on the
/// adversary's *initial* knowledge `know0`: it leaks no directory private key.
/// (No nonce precondition is needed: stored-nonce secrecy holds vacuously at the
/// empty initial session map, and the freshness invariant holds because the
/// initial `used_nonces` is exactly `ma_knowledge_nonces know0`.  The protocol's
/// own state invariant and input-derivability are unconditional at the empty
/// initial configuration.)
val ma_ideal_core_inv_init
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
      (requires
        (forall (participant: participant_id) (k: priv_key) (d: adv.derivation).
          PartialMap.sel key_directory participant == Some k /\
          not (Set.mem participant corrupt) ==>
          not (adv.derive d know0 = Some (PrivKey k))))
      (ensures ma_ideal_core_inv corrupt key_directory (ma_ideal_system corrupt key_directory know0).init)

/// The invariant is preserved by every tested-system transition (Internal,
/// Observable, and adversary Input).
val ma_ideal_core_inv_preserved
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_core_inv corrupt key_directory s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures ma_ideal_core_inv corrupt key_directory s')

/// ===========================================================================
/// Pointwise authenticity consequences of the provenance clauses.
///
/// These two lemmas replace the former `ma_derivable_message2_matches_responder_session`
/// / `ma_derivable_message3_matches_initiator_session` predicates: rather than a
/// universally quantified clause carried alongside provenance, a consumer that
/// has a concrete derivable network message invokes the relevant lemma to obtain
/// the matching simulator session directly.  Each derives its conclusion from the
/// corresponding provenance clause, secrecy (`s.internal.key_directory ==
/// key_directory`), and directory injectivity.
/// ===========================================================================

/// Message2 authenticity (pointwise).  If `initiator` has an initiator session
/// with `responder` using `initiator_nonce`, owns `initiator_key`, and the
/// adversary can derive the corresponding Message2 network reply, then
/// `responder` has the matching responder session with `responder_nonce`.
val ma_message2_provenance_matches_responder
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
            session initiator responder initiator_nonce responder_nonce
            (PubKey initiator_key)))
      (ensures matches_responder_state s session responder initiator responder_nonce)

/// Message3 authenticity (pointwise).  If `responder` has a responder session
/// with `initiator` using `responder_nonce`, owns `responder_key`, and the
/// adversary can derive the corresponding Message3 network message, then
/// `initiator` has the complementary initiator session for `responder`.
val ma_message3_provenance_matches_initiator
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
      (ensures matches_initiator_peer_state s session initiator responder)

/// The single invariant holds at the initial tested-system state.
///
/// The `requires` are the honest-start assumptions of
/// `ma_ideal_core_inv_init` (the adversary's initial knowledge `know0` leaks
/// no directory private key) plus directory injectivity.  No
/// no-derivable-protocol-ciphertext assumption is needed: the provenance clauses
/// are conditioned on an existing simulator session, so they hold vacuously at
/// the empty initial session map regardless of what ciphertexts `know0` contains.
/// Likewise no nonce-secrecy precondition is needed: the stored-nonce-secrecy
/// conjuncts hold vacuously at the empty session map, and the freshness conjunct
/// holds because the initial `used_nonces` set is, by construction,
/// `ma_knowledge_nonces know0`.
val ma_ideal_system_inv_init
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
    : Lemma
      (requires
        (forall (participant: participant_id) (k: priv_key) (d: adv.derivation).
          PartialMap.sel key_directory participant == Some k /\
          not (Set.mem participant corrupt) ==>
          not (adv.derive d know0 = Some (PrivKey k))) /\
        ma_key_directory_injective key_directory)
      (ensures ma_ideal_system_inv corrupt key_directory (ma_ideal_system corrupt key_directory know0).init)

/// The single invariant is preserved by every tested-system transition
/// (Internal, Observable, and adversary Input).
val ma_ideal_system_inv_preserved
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (s s': ideal_system_state)
      (l: system_label)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s /\
        (ma_ideal_system corrupt key_directory know0).transitions s l s')
      (ensures ma_ideal_system_inv corrupt key_directory s')

/// Elimination lemma: reveal the `opaque_to_smt` invariant and expose every
/// conjunct (and the immediate cryptographic consequences) as plain facts.  This
/// is the single entry point `ma_bisim_relation` destructure sites use to recover
/// the ideal-side clauses subsumed by `ma_ideal_system_inv`.
///
/// Every entry of the `ensures` is a (possibly transitive) conjunct of the
/// invariant, so the lemma is a pure `reveal_opaque`.  The bundled
/// `ma_ideal_core_inv` is exposed directly (it is the first conjunct of
/// `ma_ideal_system_inv`) so that consumers requiring the whole core invariant
/// — e.g. `ma_message2_provenance_matches_responder` /
/// `ma_message3_provenance_matches_initiator` — get it without re-bundling its
/// constituents; its two halves (`ma_ideal_secrecy_inv` and
/// `ma_ideal_bookkeeping_inv`) and the individual conjuncts
/// (`ma_valid_initiator_nonces_not_derivable` / `ma_valid_responder_nonces_not_derivable`,
/// `ma_ideal_used_nonces_invariant`, …) are also listed for convenience.
///
/// The Message2/Message3 authenticity consequences are NOT exposed here as
/// universally quantified clauses; a consumer that holds a concrete derivable
/// network message instead invokes `ma_message2_provenance_matches_responder` /
/// `ma_message3_provenance_matches_initiator` (which take the same surviving
/// provenance + secrecy + injectivity conjuncts) to obtain the matching
/// simulator session pointwise.
val ma_ideal_system_inv_elim
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s: ideal_system_state)
    : Lemma
      (requires ma_ideal_system_inv corrupt key_directory s)
      (ensures
        ma_ideal_core_inv corrupt key_directory s /\
        ma_ideal_secrecy_inv corrupt key_directory s /\
        ma_ideal_bookkeeping_inv corrupt key_directory s /\
        ma_ideal_state_inv (s2p_state s) /\
        ma_key_directory_matches key_directory s /\
        ma_corrupt_set_matches corrupt s /\
        ma_ideal_inputs_derivable s /\
        ma_private_keys_not_derivable corrupt key_directory s /\
        ma_valid_responder_nonces_not_derivable corrupt s /\
        ma_valid_initiator_nonces_not_derivable corrupt s /\
        ma_ideal_used_nonces_invariant s /\
        ma_session_nonces_unique s /\
        ma_honest_msg1_names_non_corrupt corrupt s /\
        ma_honest_msg2_names_non_corrupt corrupt s /\
        ma_honest_msg2_key_matches_initiator corrupt s /\
        ma_honest_carrier_shallow corrupt s /\
        ma_key_directory_injective key_directory /\
        ma_message2_provenance corrupt s /\
        ma_message3_provenance corrupt s /\
        ma_output_has_complementary_request corrupt s /\
        ma_sim_session_matches_ideal_request s /\
        ma_output_token_matches_sim_phase s)
