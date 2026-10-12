module MA.ObservationalBisimulation.Proof.Common

/// Common helpers extracted from MA.ObservationalBisimulation.Proof for
/// faster iteration. These lemmas are reused across multiple proof families
/// (initiator_start, initiator_output, initiator_ack, responder_reply,
/// responder_output, ideal_send_messageN, input_step). Keeping them in a
/// separate, small module lets a developer iterate on one family without
/// re-verifying the entire proof.
///
/// Verification time: ~4s (clean)

open SymbolicTypes
open AencTerms
open AdversaryAenc
open MA.NSL
open MA.Ideal
open MA.Adversary
open MA.Types
open StaticEquivalence
open TestedSystem

module PartialMap = FStar.PartialMap
module Set = FStar.Set
module SeqProps = FStar.Seq.Properties
module List = FStar.List.Tot.Base

open MA.ObservationalBisimulation.Relation
open MA.IdealInvariants
open MA.TestedProtocols

/// Effect tag of an `ma_effect`-tagged observable label, used to state the
/// effect-matching obligation in the per-instance simulation lemmas on both
/// sides of the bisimulation.
let ma_observable_effect (eff: ma_effect) : TestEquivalence.tested_effect term ma_effect adversary_aenc =
  TestEquivalence.Observable eff

let rec indistinguishable_refl (t: term) : Lemma (ensures (indistinguishable t t)) (decreases t) =
  match t with
  | Pair t1 t2 ->
    indistinguishable_refl t1;
    indistinguishable_refl t2
  | _ -> ()

let statically_equivalent_refl (know: knowledge term)
    : Lemma (ensures (statically_equivalent adv know know)) =
  let indist_helper (d: derivation)
      : Lemma
      (ensures (indistinguishable' adv.indistinguishable (adv.derive d know) (adv.derive d know))) =
    match adv.derive d know with
    | None -> ()
    | Some t -> indistinguishable_refl t
  in
  FStar.Classical.forall_intro indist_helper;
  let eq_helper (d1 d2: derivation)
      : Lemma
      (ensures
        ((adv.derive d1 know = adv.derive d2 know) <==> (adv.derive d1 know = adv.derive d2 know)))
  =
    ()
  in
  FStar.Classical.forall_intro_2 eq_helper

let ma_init_related (corrupt: Set.set participant_id) (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
    : Lemma
      (requires
        ma_key_directory_injective key_directory /\
        ma_private_keys_not_derivable corrupt key_directory
          (ma_impl_system corrupt key_directory know0).init)
      (ensures
        ma_bisim_relation corrupt key_directory
          (ma_impl_system corrupt key_directory know0).init
          (ma_ideal_system corrupt key_directory know0).init) =
  let s_p = (ma_impl_system corrupt key_directory know0).init in
  let s_q = (ma_ideal_system corrupt key_directory know0).init in
  statically_equivalent_refl know0;
  // The ideal-side invariant at the initial state (a conjunct of the relation).
  assert ((ma_impl_system corrupt key_directory know0).init.know == know0);
  ma_ideal_system_inv_init corrupt key_directory know0;
  assert (ma_bisim_relation corrupt key_directory s_p s_q);
  ()

let ma_static_equiv_from_rel_helper
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (s_p: impl_system_state)
      (s_q: ideal_system_state)
    : Lemma
    (ma_bisim_relation corrupt key_directory s_p s_q ==> statically_equivalent adv s_p.know s_q.know) =
  assert (ma_bisim_relation corrupt key_directory s_p s_q ==>
      s_p.know == s_q.know);
  statically_equivalent_refl s_p.know

let ma_static_equiv_from_rel (corrupt: Set.set participant_id) (key_directory: PartialMap.t participant_id priv_key)
    : Lemma
    (forall (s_p: impl_system_state) (s_q: ideal_system_state).
        ma_bisim_relation corrupt key_directory s_p s_q ==> statically_equivalent adv s_p.know s_q.know) =
  FStar.Classical.forall_intro_2 (ma_static_equiv_from_rel_helper corrupt key_directory)

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

let ma_knowledge_nonces_index_subset
      (know: knowledge term)
      (i: nat {i < Seq.length know})
      (t: term)
    : Lemma
      (requires Seq.index know i == t)
      (ensures Set.subset (ma_term_nonces t) (ma_knowledge_nonces know)) =
  SeqProps.lemma_index_is_nth know i;
  ma_term_list_nonces_index_subset (Seq.seq_to_list know) i t

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

let ma_derive_nonce_in_knowledge_nonces
      (know: knowledge term)
      (d: derivation)
      (n: nonce)
    : Lemma
      (requires derive d know = Some (Nonce n))
      (ensures Set.mem n (ma_knowledge_nonces know)) =
  ma_derive_term_nonces_in_knowledge_nonces know d (Nonce n);
  Set.subset_mem (ma_term_nonces (Nonce n)) (ma_knowledge_nonces know)

let ma_set_mem_add (#a: eqtype) (x y: a) (s: Set.set a)
  : Lemma (ensures Set.mem x (Set.add y s) == (Set.mem x s || x = y)) =
  Set.mem_union x s (Set.singleton y);
  Set.mem_singleton y x

