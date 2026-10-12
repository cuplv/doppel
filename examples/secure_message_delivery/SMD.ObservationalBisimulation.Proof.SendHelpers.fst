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

#push-options "--z3rlimit_factor 8"

// Helpers for indexing into snoc'd sequences, used by obs_from_old_knowledge
// and directly by the two large send-relation lemmas.
let _derive_observed_inversion (i: knowledge_index) (kn: knowledge term) (t: term)
  : Lemma (requires adv.derive (DeriveObserved i) kn = Some t)
          (ensures i < Seq.length kn /\ Seq.index kn i == t) =
  assert_norm (adv.derive (DeriveObserved i) kn ==
               (if i < Seq.length kn then Some (Seq.index kn i) else None))

private
let _derive_observed_intro (i: knowledge_index) (kn: knowledge term) (t: term)
  : Lemma (requires i < Seq.length kn /\ Seq.index kn i == t)
          (ensures adv.derive (DeriveObserved i) kn = Some t) =
  assert_norm (adv.derive (DeriveObserved i) kn ==
               (if i < Seq.length kn then Some (Seq.index kn i) else None))

private
let _snoc_index_before (#a: Type) (kn: Seq.seq a) (x: a) (i: nat)
  : Lemma (requires i < Seq.length kn)
          (ensures Seq.index (Seq.snoc kn x) i == Seq.index kn i) =
  Seq.lemma_index_app1 kn (Seq.create 1 x) i

private
let _snoc_index_last (#a: Type) (kn: Seq.seq a) (x: a)
  : Lemma (ensures
      Seq.length (Seq.snoc kn x) == Seq.length kn + 1 /\
      Seq.index (Seq.snoc kn x) (Seq.length kn) == x) =
  Seq.lemma_index_app2 kn (Seq.create 1 x) (Seq.length kn)

let _snoc_index_eq_last (#a: Type) (kn kn': Seq.seq a) (x: a) (n: nat) (idx: nat)
  : Lemma
    (requires
      kn' == Seq.snoc kn x /\
      n == Seq.length kn /\
      idx < Seq.length kn' /\
      ~(idx < n))
    (ensures idx == n /\ Seq.index kn' n == x) =
  _snoc_index_last kn x

let rec canonical_ideal_built_from
      (know: knowledge term) (k: key) (m: term) (t: term)
    : Lemma
      (requires
        built_from_know_and_ciphertext know m k t /\
        ~(derivable know (Key k)) /\
        canonical_ideal (Senc m k) k /\
        (forall (d: derivation) (t': term).
           derive d know = Some t' ==> canonical_ideal t' k))
      (ensures canonical_ideal t k)
      (decreases t) =
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know t) then ()
  else if t = Senc m k then ()
  else
    match t with
    | Pair l r ->
      canonical_ideal_built_from know k m l;
      canonical_ideal_built_from know k m r
    | Senc p k' ->
      canonical_ideal_built_from know k m p
    | _ -> ()

let rec no_ideal_senc_built_from
      (know: knowledge term) (k: key) (m: term) (i: session_id) (t: term)
    : Lemma
      (requires
        built_from_know_and_ciphertext know m k t /\
        ~(derivable know (Key k)) /\
        ~(in_term (Senc m k) (Senc (SessionId i) k)) /\
        (forall (d: derivation) (t': term).
           derive d know = Some t' ==> ~(in_term t' (Senc (SessionId i) k))))
      (ensures ~(in_term t (Senc (SessionId i) k)))
      (decreases t) =
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know t) then ()
  else if t = Senc m k then ()
  else
    match t with
    | Pair l r ->
      no_ideal_senc_built_from know k m i l;
      no_ideal_senc_built_from know k m i r
    | Senc p k' ->
      no_ideal_senc_built_from know k m i p
    | _ -> ()

let outputs_derivable_with_same_derivation
  (impl_knowledge ideal_knowledge: knowledge term)
  (impl_message ideal_message: term)
  (session: session_id)
  : prop =
    // Both protocols output session-message pairs
    let impl_observed = Pair (SessionId session) impl_message in
    let ideal_observed = Pair (SessionId session) ideal_message in
    exists original_input_derivation.
      adv.derive original_input_derivation impl_knowledge = Some impl_observed /\
      adv.derive original_input_derivation ideal_knowledge =
      Some ideal_observed

let mem_remove_neq_forall (#a: eqtype) (y: a) (b: Bag.bag a)
  : Lemma (forall x. x <> y ==> (Bag.mem x (Bag.remove y b) == Bag.mem x b)) =
  let preserve_for_x (x: a)
    : Lemma (x <> y ==> (Bag.mem x (Bag.remove y b) == Bag.mem x b)) =
    Bag.mem_remove x y b
  in
  FStar.Classical.forall_intro preserve_for_x

let count_remove_bijective (#t1 #t2: eqtype) (query removed: t1) (b1: Bag.bag t1) (b2: Bag.bag t2) (f: Bijection.cbij t1 t2)
  : Lemma
      (requires Bag.count b1 query == Bag.count b2 (f.cright query))
      (ensures
        (Bag.count (Bag.remove removed b1) query) ==
        (Bag.count (Bag.remove (f.cright removed) b2) (f.cright query)))
      [SMTPat (Bag.count (Bag.remove removed b1) query);
       SMTPat (Bag.count (Bag.remove (f.cright removed) b2) (f.cright query))]
= if (query = removed)
  then ()
  else BijectionExt.bijection_right_injective f query removed

/// Helper: every value stored in s_p.internal.messages is derivable from
/// s_p.know.  Proof: bisim's messages-correspondence relates the impl entry
/// to a corresponding ideal entry; the ideal_invariant_committed_messages_
/// derivable_from_knowledge invariant gives a derivation of
/// `Pair (SessionId sid) (smd_bi_subst w s_p.messages k k)` on the ideal
/// side; by bijective_correspondence_on_derivations the same derivation on
/// the impl side yields `Pair (SessionId sid) w`; finally DerivePairRight
/// extracts `w`.
let _messages_p_stored_value_derivable
    (k: key)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (sid: session_id)
    (w: term)
  : Lemma
    (requires
      smd_bisim_relation k s_p s_q /\
      PartialMap.sel s_p.internal.messages sid == Some w)
    (ensures derivable s_p.know w) =
  let bij = smd_subst_bijection k k s_p.internal.messages in
  let v = smd_bi_subst w s_p.internal.messages k k in
  // Messages correspondence: ideal stores Some v.
  assert (PartialMap.sel s_q.internal.messages sid ==
          Option.mapTot (fun m -> smd_bi_subst m s_p.internal.messages k k)
                        (PartialMap.sel s_p.internal.messages sid));
  assert (PartialMap.sel s_q.internal.messages sid == Some v);
  // ideal_invariant_committed_messages_derivable_from_knowledge gives
  // derivable s_q.know (Pair (SessionId sid) v).
  assert (derivable s_q.know (Pair (SessionId sid) v));
  let d_pair_q = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_q.know = Some (Pair (SessionId sid) v)) in
  // Bijective correspondence: derive d_pair_q s_q.know = Option.mapTot bij.cright (derive d_pair_q s_p.know).
  // So derive d_pair_q s_p.know = Some t with bij.cright t = Pair(SessionId sid) v.
  derive_bijection_implies_inverse adv s_p.know s_q.know bij d_pair_q;
  assert (adv.derive d_pair_q s_p.know ==
          Option.mapTot bij.cleft (adv.derive d_pair_q s_q.know));
  assert (adv.derive d_pair_q s_p.know ==
          Some (bij.cleft (Pair (SessionId sid) v)));
  // smd_bi_subst is self-inverse, so bij.cleft (Pair sid v) = smd_bi_subst (Pair sid v) ...
  // and Pair recurses: SessionId sid is atom, smd_bi_subst v ... = w (self-inverse on w).
  smd_subst_bijection_left k k s_p.internal.messages (Pair (SessionId sid) v);
  assert_norm (smd_bi_subst (Pair (SessionId sid) v) s_p.internal.messages k k ==
               Pair (smd_bi_subst (SessionId sid) s_p.internal.messages k k)
                    (smd_bi_subst v s_p.internal.messages k k));
  assert_norm (smd_bi_subst (SessionId sid) s_p.internal.messages k k == SessionId sid);
  // smd_bi_subst v s_p.messages k k = smd_bi_subst (smd_bi_subst w ...) ... = w (self-inverse).
  smd_subst_bijection_right k k s_p.internal.messages w;
  assert (bij.cright w == v);
  assert (bij.cleft v == bij.cleft (bij.cright w));
  assert (bij.cleft (bij.cright w) == w);
  smd_subst_bijection_left k k s_p.internal.messages v;
  assert (smd_bi_subst v s_p.internal.messages k k == w);
  assert (bij.cleft (Pair (SessionId sid) v) == Pair (SessionId sid) w);
  assert (adv.derive d_pair_q s_p.know == Some (Pair (SessionId sid) w));
  let d_w = DerivePairRight d_pair_q in
  assert (adv.derive d_w s_p.know == Some w)

/// Helper: any term derivable from s_p.know in a state where
/// s_p.messages[session] = None has the in_term preconditions required by
/// `smd_bi_subst_preserved_by_irrelevant_update`, hence smd_bi_subst on it
/// is unchanged when extending the map at session.
let _impl_irrelevant_update_on_derivable
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
      smd_bi_subst t (PartialMap.upd s_p.internal.messages session message) k k) =
  let d_t = FStar.IndefiniteDescription.indefinite_description_ghost derivation
    (fun d -> adv.derive d s_p.know = Some t) in
  // From no-ideal-form-senc invariant on impl derivable terms (instantiate i := session).
  assert (forall (i: session_id).
            adv.derive d_t s_p.know = Some t ==>
            in_term t (Senc (SessionId i) k) == false);
  assert (in_term t (Senc (SessionId session) k) == false);
  // From impl_invariant_messages_consistent_with_knowledge contrapositively:
  // messages[session] = None ==> for all derivable t, in_term t (Senc(Pair(SessionId session) m') k) == false for any m'.
  assert (~(PartialMap.contains s_p.internal.messages session));
  assert (implementation_invariants s_p);
  assert (impl_invariant_messages_consistent_with_knowledge s_p);
  // The invariant says: derivable t /\ in_term t (Senc(Pair(SessionId session) m) k) ==> messages[session] = Some m.
  // Since messages[session] = None, the in_term predicate must be false.
  assert (in_term t (Senc (Pair (SessionId session) message) k) == false);
  smd_bi_subst_preserved_by_irrelevant_update t s_p.internal.messages k k session message

/// Helper: given an observation index into the extended knowledge (snoc),
/// if idx < n then the observation was already in the old knowledge and
/// we can derive it from the old knowledge too.
let obs_from_old_knowledge
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
      adv.derive (DeriveObserved idx) s_p_know = Some (Senc (Pair (SessionId qs) qim) k)) =
  _derive_observed_inversion idx (Seq.snoc s_p_know impl_observed) (Senc (Pair (SessionId qs) qim) k);
  _snoc_index_before s_p_know impl_observed idx;
  _derive_observed_intro idx s_p_know (Senc (Pair (SessionId qs) qim) k)

#pop-options
