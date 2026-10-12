module SMD.Ideal

open SymbolicTypes

open SencTerms

open SMD.Adversary

open SMD.Types

module Set = FStar.Set

open FStar.Set.Properties

module PartialMap = FStar.PartialMap

module Seq = FStar.Seq

open Bag

module Protocol = Protocol

/// -------------------------------------------------------------------------
/// Protocol typeclass instance for the SMD ideal
/// (paper §3.1)
/// -------------------------------------------------------------------------

/// Internal state for the SMD ideal protocol. The adversary knowledge is
/// tracked separately by `TestedSystem`.

noeq
type ideal_internal_state = {
  ideal_to_sim_channel:Set.set term;
  sim_to_ideal_channel:Set.set term;
  messages:PartialMap.t session_id term;
  sim_key:key;
  sim_sent_sessions:Set.set session_id;
  sim_received_sessions:Set.set session_id
}



/// Protocol transition for the SMD ideal, using combined transitions.
///
///   Combined ideal-commit + sim-send:
///     Pair(SessionId s, m) ∈ inputs, session not yet sim_sent, not yet committed
///       → Observable () (Senc(SessionId s, sim_key)) s
///
///   Combined sim-receive + ideal-deliver:
///     Senc(SessionId s, sim_key) ∈ inputs, session not yet sim_received, message committed
///       → Observable () (Pair(SessionId s, message)) s

unfold
let smd_ideal_protocol_send_enabled
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : prop =
  let trigger_input = Pair (SessionId session) message in
  not (Set.mem session s.internal.sim_sent_sessions) /\
  not (PartialMap.contains s.internal.messages session) /\
  Bag.mem trigger_input s.inputs

unfold
let smd_ideal_protocol_send_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : Protocol.state term ideal_internal_state =
  let trigger_input = Pair (SessionId session) message in
  {
    inputs = Bag.remove trigger_input s.inputs;
    internal =
    {
      s.internal with
      messages = PartialMap.upd s.internal.messages session message;
      sim_sent_sessions = Set.add session s.internal.sim_sent_sessions;
      ideal_to_sim_channel = Set.remove (SessionId session) s.internal.ideal_to_sim_channel
    }
  }

let smd_ideal_protocol_send_transition
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (t: term)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  // Combined ideal commit + sim send: Pair(SessionId s, m) ∈ inputs → Observable NetSend
  match t with
  | Senc (SessionId sid) sim_key ->
    sid == session /\
    sim_key == s.internal.sim_key /\
    (exists message.
        smd_ideal_protocol_send_enabled s session message /\
        s' == smd_ideal_protocol_send_state s session message)
  | _ -> False

let smd_ideal_protocol_receive_enabled
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : prop =
  let trigger_input = Senc (SessionId session) s.internal.sim_key in
  not (Set.mem session s.internal.sim_received_sessions) /\
  PartialMap.sel s.internal.messages session == Some message /\
  Bag.mem trigger_input s.inputs

let smd_ideal_protocol_receive_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : Protocol.state term ideal_internal_state =
  let trigger_input = Senc (SessionId session) s.internal.sim_key in
  {
    inputs = Bag.remove trigger_input s.inputs;
    internal =
    {
      s.internal with
      sim_received_sessions = Set.add session s.internal.sim_received_sessions;
      sim_to_ideal_channel = Set.remove (SessionId session) s.internal.sim_to_ideal_channel
    }
  }

let smd_ideal_protocol_receive_transition
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (t: term)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  // Combined sim receive + ideal deliver: Senc(SessionId s, sim_key) ∈ inputs → Observable IoSend
  match t with
  | Pair (SessionId sid) message ->
    sid == session /\
    smd_ideal_protocol_receive_enabled s session message /\
    s' == smd_ideal_protocol_receive_state s session message
  | _ -> False


/// -------------------------------------------------------------------------
/// Individual ideal and simulator transitions at the Protocol level.
///
///   Ideal commit (Internal):
///     Pair(SessionId s, m) ∈ inputs, session not yet committed
///       → remove input, store m in messages, notify simulator (add SessionId s
///         to ideal_to_sim_channel)
///
///   Simulator send (Observable NetSend):
///     SessionId s ∈ ideal_to_sim_channel, session not yet sim_sent
///       → emit Senc(SessionId s, sim_key), remove notification, record sim_sent
///
///   Simulator receive (Internal):
///     Senc(SessionId s, sim_key) ∈ inputs, session not yet sim_received
///       → remove input, notify ideal (add SessionId s to sim_to_ideal_channel),
///         record sim_received
///
///   Ideal deliver (Observable IoSend):
///     SessionId s ∈ sim_to_ideal_channel, messages[s] = some message
///       → emit Pair(SessionId s, messages[s]), remove notification
/// -------------------------------------------------------------------------

unfold
let smd_ideal_commit_enabled
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : prop =
  let trigger_input = Pair (SessionId session) message in
  not (PartialMap.contains s.internal.messages session) /\
  Bag.mem trigger_input s.inputs

unfold
let smd_ideal_commit_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : Protocol.state term ideal_internal_state =
  let trigger_input = Pair (SessionId session) message in
  {
    inputs = Bag.remove trigger_input s.inputs;
    internal =
    {
      s.internal with
      messages = PartialMap.upd s.internal.messages session message;
      ideal_to_sim_channel = Set.add (SessionId session) s.internal.ideal_to_sim_channel
    }
  }

let smd_ideal_commit_protocol_transition
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  exists (message: term).
    smd_ideal_commit_enabled s session message /\
    s' == smd_ideal_commit_state s session message


unfold
let smd_sim_send_enabled
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
    : prop =
  not (Set.mem session s.internal.sim_sent_sessions) /\
  Set.mem (SessionId session) s.internal.ideal_to_sim_channel

unfold
let smd_sim_send_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
    : Protocol.state term ideal_internal_state =
  {
    s with
    internal =
    {
      s.internal with
      sim_sent_sessions = Set.add session s.internal.sim_sent_sessions;
      ideal_to_sim_channel = Set.remove (SessionId session) s.internal.ideal_to_sim_channel
    }
  }

let smd_sim_send_protocol_transition
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (t: term)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  match t with
  | Senc (SessionId sid) k ->
    sid == session /\
    k == s.internal.sim_key /\
    smd_sim_send_enabled s session /\
    s' == smd_sim_send_state s session
  | _ -> False


unfold
let smd_sim_receive_enabled
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
    : prop =
  let trigger_input = Senc (SessionId session) s.internal.sim_key in
  not (Set.mem session s.internal.sim_received_sessions) /\
  Bag.mem trigger_input s.inputs

unfold
let smd_sim_receive_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
    : Protocol.state term ideal_internal_state =
  let trigger_input = Senc (SessionId session) s.internal.sim_key in
  {
    inputs = Bag.remove trigger_input s.inputs;
    internal =
    {
      s.internal with
      sim_received_sessions = Set.add session s.internal.sim_received_sessions;
      sim_to_ideal_channel = Set.add (SessionId session) s.internal.sim_to_ideal_channel
    }
  }

let smd_sim_receive_protocol_transition
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  smd_sim_receive_enabled s session /\
  s' == smd_sim_receive_state s session


unfold
let smd_ideal_deliver_enabled
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : prop =
  PartialMap.sel s.internal.messages session == Some message /\
  Set.mem (SessionId session) s.internal.sim_to_ideal_channel

unfold
let smd_ideal_deliver_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
    : Protocol.state term ideal_internal_state =
  {
    s with
    internal =
    {
      s.internal with
      sim_to_ideal_channel = Set.remove (SessionId session) s.internal.sim_to_ideal_channel
    }
  }

let smd_ideal_deliver_protocol_transition
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (t: term)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  match t with
  | Pair (SessionId sid) message ->
    sid == session /\
    smd_ideal_deliver_enabled s session message /\
    s' == smd_ideal_deliver_state s session
  | _ -> False


/// The combined protocol state after commit + sim_send equals
/// smd_ideal_protocol_send_state.

let commit_then_sim_send_equals_send_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : Lemma
      (ensures
        smd_sim_send_state (smd_ideal_commit_state s session message) session ==
        smd_ideal_protocol_send_state s session message)
    =
    FStar.Set.Properties.remove_add (SessionId session) s.internal.ideal_to_sim_channel


/// The combined protocol state after sim_receive + deliver equals
/// smd_ideal_protocol_receive_state.

let sim_receive_then_deliver_equals_receive_state
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : Lemma
      (requires
        smd_sim_receive_enabled s session /\
        PartialMap.sel s.internal.messages session == Some message)
      (ensures
        smd_ideal_deliver_state (smd_sim_receive_state s session) session ==
        smd_ideal_protocol_receive_state s session message)
    =
    FStar.Set.Properties.remove_add (SessionId session) s.internal.sim_to_ideal_channel


let smd_ideal_protocol_transition
      (s: Protocol.state term ideal_internal_state)
      (l: Protocol.label term smd_effect session_id)
      (s': Protocol.state term ideal_internal_state)
    : prop =
  match l with
  | Protocol.Observable NetSend t session -> smd_sim_send_protocol_transition s session t s'
  | Protocol.Observable IoSend t session -> smd_ideal_deliver_protocol_transition s session t s'
  | Protocol.Internal session ->
    smd_ideal_commit_protocol_transition s session s' \/
    smd_sim_receive_protocol_transition s session s'

let smd_ideal_protocol_init (k: key) : Protocol.state term ideal_internal_state =
  {
    inputs = Bag.empty;
    internal
    =
    {
      ideal_to_sim_channel = Set.empty;
      sim_to_ideal_channel = Set.empty;
      messages = PartialMap.empty session_id term;
      sim_key = k;
      sim_sent_sessions = Set.empty;
      sim_received_sessions = Set.empty
    }
  }



/// `valid_transitions` is satisfied because both combined transitions consume
/// one triggering input term via `Bag.remove`, so `Bag.subset s'.inputs s.inputs` holds.

val smd_ideal_valid_transitions
      (s: Protocol.state term ideal_internal_state)
      (l: Protocol.label term smd_effect session_id)
      (s': Protocol.state term ideal_internal_state)
    : squash (smd_ideal_protocol_transition s l s' ==> Bag.subset s'.inputs s.inputs)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let smd_ideal_protocol (k: key) : Protocol.protocol term smd_effect session_id ideal_internal_state =
  {
    transition = smd_ideal_protocol_transition;
    init = smd_ideal_protocol_init k;
    valid_transitions = smd_ideal_valid_transitions
  }
