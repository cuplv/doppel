module SMD.ObservationalBisimulation.Proof.SendHelpers

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

val _derive_observed_inversion (i: knowledge_index) (kn: knowledge term) (t: term)
  : Lemma (requires adv.derive (DeriveObserved i) kn = Some t)
          (ensures i < Seq.length kn /\ Seq.index kn i == t)

val _snoc_index_eq_last (#a: Type) (kn kn': Seq.seq a) (x: a) (n: nat) (idx: nat)
  : Lemma
    (requires
      kn' == Seq.snoc kn x /\
      n == Seq.length kn /\
      idx < Seq.length kn' /\
      ~(idx < n))
    (ensures idx == n /\ Seq.index kn' n == x)

val canonical_ideal_built_from
      (know: knowledge term) (k: key) (m: term) (t: term)
    : Lemma
      (requires
        built_from_know_and_ciphertext know m k t /\
        ~(derivable know (Key k)) /\
        canonical_ideal (Senc m k) k /\
        (forall (d: derivation) (t': term).
           derive d know = Some t' ==> canonical_ideal t' k))
      (ensures canonical_ideal t k)
      (decreases t)

val no_ideal_senc_built_from
      (know: knowledge term) (k: key) (m: term) (i: session_id) (t: term)
    : Lemma
      (requires
        built_from_know_and_ciphertext know m k t /\
        ~(derivable know (Key k)) /\
        ~(in_term (Senc m k) (Senc (SessionId i) k)) /\
        (forall (d: derivation) (t': term).
           derive d know = Some t' ==> ~(in_term t' (Senc (SessionId i) k))))
      (ensures ~(in_term t (Senc (SessionId i) k)))
      (decreases t)

val outputs_derivable_with_same_derivation
  (impl_knowledge ideal_knowledge: knowledge term)
  (impl_message ideal_message: term)
  (session: session_id)
  : prop

val mem_remove_neq_forall (#a: eqtype) (y: a) (b: Bag.bag a)
  : Lemma (forall x. x <> y ==> (Bag.mem x (Bag.remove y b) == Bag.mem x b))

val count_remove_bijective (#t1 #t2: eqtype) (query removed: t1) (b1: Bag.bag t1) (b2: Bag.bag t2) (f: Bijection.cbij t1 t2)
  : Lemma
      (requires Bag.count b1 query == Bag.count b2 (f.cright query))
      (ensures
        (Bag.count (Bag.remove removed b1) query) ==
        (Bag.count (Bag.remove (f.cright removed) b2) (f.cright query)))
      [SMTPat (Bag.count (Bag.remove removed b1) query);
       SMTPat (Bag.count (Bag.remove (f.cright removed) b2) (f.cright query))]

val _messages_p_stored_value_derivable
    (k: key)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (sid: session_id)
    (w: term)
  : Lemma
    (requires
      smd_bisim_relation k s_p s_q /\
      PartialMap.sel s_p.internal.messages sid == Some w)
    (ensures derivable s_p.know w)

val _impl_irrelevant_update_on_derivable
    (k: key) (session: session_id) (message: term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (t: term)
  : Lemma
    (requires
      smd_bisim_relation k s_p s_q /\
      PartialMap.sel s_p.internal.messages session == None /\
      derivable s_p.know t)
    (ensures
      smd_bi_subst t s_p.internal.messages k k =
      smd_bi_subst t (PartialMap.upd s_p.internal.messages session message) k k)

val obs_from_old_knowledge
    (s_p_know: knowledge term)
    (impl_observed: term)
    (k: key)
    (qs: session_id)
    (qim: term)
    (n: nat)
    (idx: knowledge_index)
  : Lemma
    (requires
      n == Seq.length s_p_know /\
      adv.derive (DeriveObserved idx) (Seq.snoc s_p_know impl_observed) =
        Some (Senc (Pair (SessionId qs) qim) k) /\
      idx < n)
    (ensures
      Seq.index s_p_know idx == Senc (Pair (SessionId qs) qim) k /\
      adv.derive (DeriveObserved idx) s_p_know = Some (Senc (Pair (SessionId qs) qim) k))
