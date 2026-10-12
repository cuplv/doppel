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

val smd_obs_bisim_observable_step_impl_recv_preserves_relation
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
        smd_bisim_relation k s_p' (smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message))

val smd_obs_bisim_observable_step_ideal_recv_preserves_relation
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
        smd_bisim_relation k s_p' s_q'))
