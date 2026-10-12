module SMD.ObservationalBisimulation.Proof.IdealSendRelation

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

val smd_obs_bisim_observable_step_ideal_send_preserves_relation
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (ideal_message: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires (
        let s_p' = smd_ideal_send_impl_witness k s_p session ideal_message in
        let impl_message = smd_bi_subst ideal_message s_p.internal.messages k k in
        smd_bisim_relation k s_p s_q /\
        smd_ideal_protocol_send_transition
          (s2p_state s_q)
          session
          (Senc (SessionId session) k)
          (s2p_state s_q')
        /\ (s2p_state s_q') == smd_ideal_protocol_send_state (s2p_state s_q) session ideal_message
        /\ s_q'.know == Seq.snoc s_q.know (Senc (SessionId session) k)
        /\ smd_impl_protocol_send_transition (s2p_state s_p)
          session
          (Senc (Pair (SessionId session) impl_message) k)
          (s2p_state s_p')
      ))
      (ensures (
        let s_p' = smd_ideal_send_impl_witness k s_p session ideal_message in
        smd_bisim_relation k s_p' s_q'))
