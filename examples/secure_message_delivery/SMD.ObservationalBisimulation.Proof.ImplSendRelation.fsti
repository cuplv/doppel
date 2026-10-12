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

val smd_obs_bisim_observable_step_impl_send_preserves_relation
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
        smd_bisim_relation k s_p' (smd_impl_send_ideal_witness k s_p.internal.messages s_q session message))
