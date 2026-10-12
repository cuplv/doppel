/// Specification of an implementation of a two-party secure message delivery
/// protocol.

module SMD.Implementation

open SymbolicTypes

open SencTerms

open SMD.Adversary

open SMD.Types

open Bag

module Protocol = Protocol

module Set = FStar.Set

module Seq = FStar.Seq



/// -------------------------------------------------------------------------
/// Protocol typeclass instance for the SMD implementation
/// (paper §3.1)
/// -------------------------------------------------------------------------

/// Internal state for the Protocol instance: the non-knowledge parts of
/// `impl_state`.  The `knowledge` field is managed by `TestedSystem`.

noeq
type impl_internal_state = {
  key:key;
  sent_sessions:Set.set session_id;
  received_sessions:Set.set session_id;
  messages:PartialMap.t session_id term // State used only for proofs
}



/// Protocol transition.  Observable steps read from the inputs bag but do
/// NOT modify it (TestedSystem handles knowledge accumulation separately).
///
///   Send: Pair(SessionId s, m) ∈ inputs, session not yet sent
///         → Observable () (Senc(Pair(SessionId s, m), key)) s
///
///   Receive: Senc(Pair(SessionId s, m), key) ∈ inputs, session not yet received
///         → Observable () (Pair(SessionId s, m)) s

unfold
let smd_impl_protocol_send_enabled
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (message: term)
      (k: key)
    : prop =
  let trigger_input = Pair (SessionId session) message in
  k == s.internal.key /\
  not (Set.mem session s.internal.sent_sessions) /\
  Bag.mem trigger_input s.inputs

unfold
let smd_impl_protocol_send_state
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (message: term)
    : Protocol.state term impl_internal_state =
  let trigger_input = Pair (SessionId session) message in
  {
    inputs = Bag.remove trigger_input s.inputs;
    internal =
    {
      s.internal with
      sent_sessions = Set.add session s.internal.sent_sessions;
      messages = PartialMap.upd s.internal.messages session message
    }
  }

let smd_impl_protocol_send_transition
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (sent_term: term)
      (s': Protocol.state term impl_internal_state)
    : prop =
  // The sent out term is the encryption of the session and message pair under the shared key.
  match sent_term with
  | Senc (Pair (SessionId sid) message) k ->
    sid == session /\
    smd_impl_protocol_send_enabled s session message k /\
    s' == smd_impl_protocol_send_state s session message
  | _ -> False

let smd_impl_protocol_receive_enabled
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (message: term)
    : prop =
  let trigger_input = Senc (Pair (SessionId session) message) s.internal.key in
  not (Set.mem session s.internal.received_sessions) /\
  Bag.mem trigger_input s.inputs

let smd_impl_protocol_receive_state
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (message: term)
    : Protocol.state term impl_internal_state =
  let trigger_input = Senc (Pair (SessionId session) message) s.internal.key in
  {
    inputs = Bag.remove trigger_input s.inputs;
    internal =
    { s.internal with received_sessions = Set.add session s.internal.received_sessions }
  }

let smd_impl_protocol_receive_transition
      (s: Protocol.state term impl_internal_state)
      (session: session_id)
      (t: term)
      (s': Protocol.state term impl_internal_state)
    : prop =
  // The delivered term is the session-id / message pair decrypted from the ciphertext in inputs.
  match t with
  | Pair (SessionId sid) message ->
    sid == session /\
    smd_impl_protocol_receive_enabled s session message /\
    s' == smd_impl_protocol_receive_state s session message
  | _ -> False

/// Helper function used in proofs to recognize a valid receive trigger shape.

let is_receive_trigger_for_session (session: session_id) (key: key) (term: term) : bool =
  match term with
  | Senc (Pair (SessionId sid) _) k -> sid = session && k = key
  | _ -> false

let smd_impl_protocol_transition
      (s: Protocol.state term impl_internal_state)
      (l: Protocol.label term smd_effect session_id)
      (s': Protocol.state term impl_internal_state)
    : prop =
  match l with
  | Protocol.Observable NetSend t session -> smd_impl_protocol_send_transition s session t s'
  | Protocol.Observable IoSend t session -> smd_impl_protocol_receive_transition s session t s'
  | Protocol.Internal _ -> False

let smd_impl_protocol_init (k: key) : Protocol.state term impl_internal_state =
  {
    inputs = Bag.empty;
    internal
    =
    {
      key = k;
      sent_sessions = Set.empty;
      received_sessions = Set.empty;
      messages = PartialMap.empty session_id term
    }
  }



/// `valid_transitions` is satisfied because both send and receive transitions
/// only remove from inputs, so `Bag.subset s'.inputs s.inputs` holds trivially.

val smd_impl_valid_transitions
      (s: Protocol.state term impl_internal_state)
      (l: Protocol.label term smd_effect session_id)
      (s': Protocol.state term impl_internal_state)
    : squash (smd_impl_protocol_transition s l s' ==> Bag.subset s'.inputs s.inputs)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let smd_impl_protocol (k: key) : Protocol.protocol term smd_effect session_id impl_internal_state =
  {
    transition = smd_impl_protocol_transition;
    init = smd_impl_protocol_init k;
    valid_transitions = smd_impl_valid_transitions
  }
