module SMD.ObservationalBisimulation.Witnesses

/// Explicit witnesses for the simulation steps in the SMD observational
/// bisimulation proof.
///
/// This module provides concrete successor-state constructors together with
/// lemmas that show each constructor produces a state the ideal (or impl)
/// system can actually transition to.  Separating the witnesses from the
/// bookkeeping in SMD.ObservationalBisimulation.Protocol keeps both modules
/// focused and makes the existential witnesses inspectable.

open SymbolicTypes

open SencTerms

open SMD.Implementation

open SMD.Ideal

open SMD.Types

open TestedSystem

open Bag

module PartialMap = FStar.PartialMap.Ext

module Set = FStar.Set

open SMD.ObservationalBisimulation.Relation

open SMD.Bijection

open SMD.TestedProtocols

open ObservationalBisimulation

open TestEquivalence

open SMD.TestedProtocols



/// =========================================================================
/// Impl NetSend witness
/// =========================================================================
///
/// When the implementation takes a NetSend step for `session` (encrypting
/// `message` under `k`), the ideal system responds with the combined
/// ideal-commit + sim-send transition.  The resulting ideal state is:
///
///   - knowledge extended with  Senc(SessionId session, k)
///   - messages updated to record  smd_bi_subst message impl.messages k k  for session
///   - sim_sent_sessions extended with session
///   - ideal_to_sim_channel cleared of the SessionId session notification
///   - inputs remove the triggering ideal input
///       Pair(SessionId session, smd_bi_subst message impl.messages k k)
///   - all other fields unchanged

let smd_impl_send_ideal_witness
      (k: key)
      (impl_messages: PartialMap.t session_id term)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : TestedSystem.state term ideal_internal_state =
  let ideal_message = smd_bi_subst message impl_messages k k in
  let t_ideal = Senc (SessionId session) k in
  let ideal_trigger_input = Pair (SessionId session) ideal_message in
  {
    know = Seq.snoc s_q.know t_ideal;
    inputs = Bag.remove ideal_trigger_input s_q.inputs;
    internal = {
      s_q.internal with
      messages = PartialMap.upd s_q.internal.messages session ideal_message;
      sim_sent_sessions = Set.add session s_q.internal.sim_sent_sessions;
      ideal_to_sim_channel = Set.remove (SessionId session) s_q.internal.ideal_to_sim_channel
    }
  }



/// The witness state is reachable: the ideal system can take a NetSend step
/// from `s_q` to `smd_impl_send_ideal_witness k s_p.internal.messages s_q session message`
/// whenever the bisimulation relation holds and the impl has just taken its
/// NetSend step for `session` emitting `Senc(Pair(SessionId session, message), k)`.

val smd_obs_bisim_observable_step_impl_send
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_p': TestedSystem.state term impl_internal_state)
    : Lemma
      (requires (
        let impl_trigger_input = Pair (SessionId session) message in
        smd_bisim_relation k s_p s_q /\
        smd_impl_protocol_send_transition ({ inputs = s_p.inputs; internal = s_p.internal })
          session
          (Senc impl_trigger_input k)
          ({ inputs = s_p'.inputs; internal = s_p'.internal }) /\
        s_p'.know == Seq.snoc s_p.know (Senc impl_trigger_input k) /\
        s_p'.inputs == Bag.remove impl_trigger_input s_p.inputs))
      (ensures
        eventually_observable_step (smd_ideal_system k know0) s_q
          [TestedSystem.Internal session; TestedSystem.Observable NetSend session]
          (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message))



/// =========================================================================
/// Impl IoSend witness
/// =========================================================================
///
/// When the implementation takes an IoSend step for `session` (delivering the
/// decrypted `message`), the ideal system responds with the combined
/// sim-receive + ideal-deliver transition.  The resulting ideal state is:
///
///   - knowledge extended with  Pair(SessionId session, smd_bi_subst message impl.messages k k)
///   - inputs cleared of the Senc(SessionId session, k) sim trigger
///   - sim_received_sessions extended with session
///   - sim_to_ideal_channel cleared of the SessionId session notification
///   - all other fields unchanged

let smd_impl_receive_ideal_witness
      (k: key)
      (impl_messages: PartialMap.t session_id term)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : TestedSystem.state term ideal_internal_state =
  let ideal_message = smd_bi_subst message impl_messages k k in
  let ideal_trigger_input = Senc (SessionId session) k in
  {
    know = Seq.snoc s_q.know (Pair (SessionId session) ideal_message);
    inputs = Bag.remove ideal_trigger_input s_q.inputs;
    internal = {
      s_q.internal with
      sim_received_sessions = Set.add session s_q.internal.sim_received_sessions;
      sim_to_ideal_channel = Set.remove (SessionId session) s_q.internal.sim_to_ideal_channel
    }
  }



/// The witness state is reachable: the ideal system can take an IoSend step
/// from `s_q` to `smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message`
/// whenever the bisimulation relation holds and the impl has just taken its
/// IoSend step for `session` delivering `Pair(SessionId session, message)`.

val smd_obs_bisim_observable_step_impl_receive
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_p': TestedSystem.state term impl_internal_state)
    : Lemma
      (requires (
        let impl_trigger_input = Senc (Pair (SessionId session) message) k in
        smd_bisim_relation k s_p s_q /\
        smd_impl_protocol_receive_transition ({ inputs = s_p.inputs; internal = s_p.internal })
          session
          (Pair (SessionId session) message)
          ({ inputs = s_p'.inputs; internal = s_p'.internal }) /\
        s_p'.know == Seq.snoc s_p.know (Pair (SessionId session) message)
      ))
      (ensures
        eventually_observable_step (smd_ideal_system k know0) s_q
          [TestedSystem.Internal session; TestedSystem.Observable IoSend session]
          (smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message))



/// =========================================================================
/// Ideal NetSend witness
/// =========================================================================
///
/// When the ideal takes a NetSend step for `session` (emitting the decoy
/// Senc(SessionId session, k)), the implementation responds with its own
/// NetSend transition.  The resulting impl state is:
///
///   - knowledge extended with  Senc(Pair(SessionId session, impl_message), k)
///     where  impl_message = smd_bi_subst ideal_message impl.messages k k
///   - inputs cleared of the Pair(SessionId session, impl_message) trigger
///   - sent_sessions extended with session
///   - messages updated to record impl_message for session
///   - all other fields unchanged

let smd_ideal_send_impl_witness
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (session: session_id)
      (ideal_message: term)
    : TestedSystem.state term impl_internal_state =
  let impl_message = smd_bi_subst ideal_message s_p.internal.messages k k in
  let impl_trigger_input = Pair (SessionId session) impl_message in
  {
    know = Seq.snoc s_p.know (Senc (Pair (SessionId session) impl_message) k);
    inputs = Bag.remove impl_trigger_input s_p.inputs;
    internal = {
      s_p.internal with
      sent_sessions = Set.add session s_p.internal.sent_sessions;
      messages = PartialMap.upd s_p.internal.messages session impl_message
    }
  }



/// The witness state is reachable: the impl system can take a NetSend step
/// from `s_p` to `smd_ideal_send_impl_witness k s_p session message` whenever
/// the bisimulation relation holds and the ideal has just taken its NetSend step
/// for `session` emitting `Senc(SessionId session, k)`, with `message` being the
/// ideal-world trigger Pair(SessionId session, message) that was in ideal inputs.

val smd_obs_bisim_observable_step_ideal_send
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires (
        smd_bisim_relation k s_p s_q /\
        smd_ideal_protocol_send_enabled ({ inputs = s_q.inputs; internal = s_q.internal })
          session
          message /\
        smd_ideal_protocol_send_transition ({ inputs = s_q.inputs; internal = s_q.internal })
          session
          (Senc (SessionId session) k)
          ({ inputs = s_q'.inputs; internal = s_q'.internal }) /\
        s_q'.know == Seq.snoc s_q.know (Senc (SessionId session) k)))
      (ensures (
        let impl_message = smd_bi_subst message s_p.internal.messages k k in
        let s_p' = smd_ideal_send_impl_witness k s_p session message in
        (smd_impl_system k know0).transitions s_p
          (TestedSystem.Observable NetSend session)
          s_p' /\
        smd_impl_protocol_send_transition
          ({ inputs = s_p.inputs; internal = s_p.internal })
          session
          (Senc (Pair (SessionId session) impl_message) k)
          ({ inputs = s_p'.inputs; internal = s_p'.internal }) /\
        s_p'.know == Seq.snoc s_p.know (Senc (Pair (SessionId session) impl_message) k)))



/// =========================================================================
/// Ideal IoSend witness
/// =========================================================================
///
/// When the ideal takes an IoSend step for `session` (delivering
/// Pair(SessionId session, message) where message = ideal.messages[session]),
/// the implementation responds with its own IoSend transition.  The resulting
/// impl state is:
///
///   - knowledge extended with  Pair(SessionId session, impl_message)
///     where  impl_message = smd_bi_subst message impl.messages k k
///   - inputs cleared of the Senc(Pair(SessionId session, impl_message), k) trigger
///   - received_sessions extended with session
///   - all other fields unchanged

let smd_ideal_receive_impl_witness
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (session: session_id)
      (ideal_message: term)
    : TestedSystem.state term impl_internal_state =
  let impl_message = smd_bi_subst ideal_message s_p.internal.messages k k in
  let impl_trigger_input = Senc (Pair (SessionId session) impl_message) k in
  {
    know = Seq.snoc s_p.know (Pair (SessionId session) impl_message);
    inputs = Bag.remove impl_trigger_input s_p.inputs;
    internal = {
      s_p.internal with
      received_sessions = Set.add session s_p.internal.received_sessions
    }
  }



/// The witness state is reachable: the impl system can take an IoSend step
/// from `s_p` to `smd_ideal_receive_impl_witness k s_p session message` whenever
/// the bisimulation relation holds and the ideal has just taken its IoSend step
/// for `session` delivering `Pair(SessionId session, message)`.

val smd_obs_bisim_observable_step_ideal_receive
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires (
        smd_bisim_relation k s_p s_q /\
        smd_ideal_protocol_receive_transition ({ inputs = s_q.inputs; internal = s_q.internal })
          session
          (Pair (SessionId session) message)
          ({ inputs = s_q'.inputs; internal = s_q'.internal }) /\
        s_q'.know == Seq.snoc s_q.know (Pair (SessionId session) message)))
      (ensures (
        let impl_message = smd_bi_subst message s_p.internal.messages k k in
        let s_p' = smd_ideal_receive_impl_witness k s_p session message in
        (smd_impl_system k know0).transitions s_p
          (TestedSystem.Observable IoSend session)
          s_p' /\
        // Note: for some reason the fact that
        // `smd_impl_protocol_receive_transition` must transition to the witness
        // state was not getting derived from the fact that the tested system
        // transitions to it. This clause was added to the lemma to make it
        // explicit.
        smd_impl_protocol_receive_transition (s2p_state s_p)
          session
          (Pair (SessionId session) impl_message)
          (s2p_state s_p')))
