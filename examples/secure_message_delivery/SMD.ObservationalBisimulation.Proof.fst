module SMD.ObservationalBisimulation.Proof

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
open SMD.ObservationalBisimulation.Proof.ImplSendRelation
open SMD.ObservationalBisimulation.Proof.IdealSendRelation
open SMD.ObservationalBisimulation.Proof.RecvRelation

// The current F* requires a larger SMT budget for the proofs in this module
// than the original commit assumed (the per-`#push-options` rlimits below were
// calibrated against an older F*). A module-level rlimit multiplier uniformly
// scales every local rlimit so the existing proof structure is preserved.
#push-options "--z3rlimit_factor 8"



/// =========================================================================
/// Partition equivalence proof
/// =========================================================================

private
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

private
let _snoc_index_eq_last (#a: Type) (kn kn': Seq.seq a) (x: a) (n: nat) (idx: nat)
  : Lemma
    (requires
      kn' == Seq.snoc kn x /\
      n == Seq.length kn /\
      idx < Seq.length kn' /\
      ~(idx < n))
    (ensures idx == n /\ Seq.index kn' n == x) =
  _snoc_index_last kn x

private
let smd_refl_lemma (x: TestedSystem.label term smd_effect session_id adversary_senc)
    : Lemma (smd_label_in_same_partition x x) = ()

private
let smd_symm_lemma (x y: TestedSystem.label term smd_effect session_id adversary_senc)
    : Lemma (smd_label_in_same_partition x y ==> smd_label_in_same_partition y x) = ()

private
let smd_trans_lemma (x y z: TestedSystem.label term smd_effect session_id adversary_senc)
    : Lemma
    (smd_label_in_same_partition x y /\ smd_label_in_same_partition y z ==>
      smd_label_in_same_partition x z) = ()

let smd_label_in_same_partition_equiv () =
  FStar.Classical.forall_intro smd_refl_lemma;
  FStar.Classical.forall_intro_2 smd_symm_lemma;
  FStar.Classical.forall_intro_3 smd_trans_lemma;
  ()



/// =========================================================================
/// No internal transitions (impl and ideal)
/// =========================================================================

/// Both protocols define `Protocol.Internal _ -> False` in their transition
/// relations, so `is_internal tau` can never be satisfied by a reachable
/// transition — `right_movable` holds vacuously.

private
let smd_impl_no_internal_transitions (k: key) (know0: knowledge term)
    : Lemma
    (forall s (tau: TestedSystem.label term smd_effect session_id adversary_senc) s'.
    (smd_impl_system k know0).transitions s tau s' ==> ~(ObservationalBisimulation.is_internal tau)) =
  ()

/// =========================================================================
/// Right-movability
/// =========================================================================

private
let smd_right_movable_impl (k: key) (know0: knowledge term)
    : Lemma (right_movable (smd_impl_system k know0) smd_partition) =
  ()

// ---- Commutativity helpers for the ideal right-movability proof ----

private
let _pm_upd_commute (#k: eqtype) (#v: Type) (m: PartialMap.t k v)
    (k1: k) (v1: v) (k2: k) (v2: v)
    : Lemma (requires k1 <> k2)
            (ensures PartialMap.upd (PartialMap.upd m k1 v1) k2 v2 ==
                     PartialMap.upd (PartialMap.upd m k2 v2) k1 v1) =
  PartialMap.eq_intro (PartialMap.upd (PartialMap.upd m k1 v1) k2 v2)
                      (PartialMap.upd (PartialMap.upd m k2 v2) k1 v1);
  PartialMap.eq_elim  (PartialMap.upd (PartialMap.upd m k1 v1) k2 v2)
                      (PartialMap.upd (PartialMap.upd m k2 v2) k1 v1)

private
let _set_add_commute (#a: eqtype) (x y: a) (s: Set.set a)
    : Lemma (Set.add x (Set.add y s) == Set.add y (Set.add x s)) =
  Set.lemma_equal_intro (Set.add x (Set.add y s)) (Set.add y (Set.add x s));
  Set.lemma_equal_elim (Set.add x (Set.add y s)) (Set.add y (Set.add x s))

private
let _set_add_remove_commute (#a: eqtype) (x y: a) (s: Set.set a)
    : Lemma (requires x <> y)
            (ensures Set.add x (Set.remove y s) == Set.remove y (Set.add x s)) =
  Set.lemma_equal_intro (Set.add x (Set.remove y s)) (Set.remove y (Set.add x s));
  Set.lemma_equal_elim (Set.add x (Set.remove y s)) (Set.remove y (Set.add x s))

private
let _set_remove_add_commute (#a: eqtype) (x y: a) (s: Set.set a)
    : Lemma (requires x <> y)
            (ensures Set.remove x (Set.add y s) == Set.add y (Set.remove x s)) =
  Set.lemma_equal_intro (Set.remove x (Set.add y s)) (Set.add y (Set.remove x s));
  Set.lemma_equal_elim (Set.remove x (Set.add y s)) (Set.add y (Set.remove x s))

// ---- Internal tau commutes with Input alpha ----

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _ideal_internal_input_commute
      (k: key) (know0: knowledge term)
      (session1: session_id) (d: adv.derivation)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        (smd_ideal_system k know0).transitions s (TestedSystem.Internal session1) s_mid /\
        (smd_ideal_system k know0).transitions s_mid (TestedSystem.Input d) s')
      (ensures
        exists s_mid'.
          (smd_ideal_system k know0).transitions s (TestedSystem.Input d) s_mid' /\
          (smd_ideal_system k know0).transitions s_mid' (TestedSystem.Internal session1) s') =
  let t = Some?.v (adv.derive d s_mid.know) in
  let _s_mid' : ideal_system_state =
    { know = s.know; inputs = Bag.insert t s.inputs; internal = s.internal } in
  let bag_hint (x: term)
    : Lemma (requires Bag.mem x s.inputs)
            (ensures Bag.remove x (Bag.insert t s.inputs) ==
                     Bag.insert t (Bag.remove x s.inputs)) =
    Bag.remove_insert_commute x t s.inputs
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires bag_hint)
#pop-options

// ---- commit(s2, msg2) commutes with any Internal(s1) ----

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2 --split_queries no"
private
let _ideal_commit_commutes
      (k: key) (know0: knowledge term)
      (session1 session2: session_id) (msg2: term)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        session1 <> session2 /\
        (smd_ideal_system k know0).transitions s (TestedSystem.Internal session1) s_mid /\
        smd_ideal_commit_enabled (s2p_state s_mid) session2 msg2 /\
        s2p_state s' == smd_ideal_commit_state (s2p_state s_mid) session2 msg2 /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (smd_ideal_system k know0).transitions s (TestedSystem.Internal session2) s_mid' /\
          (smd_ideal_system k know0).transitions s_mid' (TestedSystem.Internal session1) s') =
  let _s_mid' : ideal_system_state =
    p2s_state (smd_ideal_commit_state (s2p_state s) session2 msg2) s.know in
  let brr (x y: term)
    : Lemma (Bag.remove x (Bag.remove y s.inputs) ==
             Bag.remove y (Bag.remove x s.inputs)) =
    Bag.remove_remove_commute x y s.inputs in
  FStar.Classical.forall_intro_2 brr;
  let pm_hint (v1: term)
    : Lemma (PartialMap.upd (PartialMap.upd s.internal.messages session1 v1) session2 msg2 ==
             PartialMap.upd (PartialMap.upd s.internal.messages session2 msg2) session1 v1) =
    _pm_upd_commute s.internal.messages session1 v1 session2 msg2 in
  FStar.Classical.forall_intro pm_hint;
  _set_add_commute (SessionId session1) (SessionId session2) s.internal.ideal_to_sim_channel

// ---- sim_receive(s2) commutes with any Internal(s1) ----

private
let _ideal_recv_commutes
      (k: key) (know0: knowledge term)
      (session1 session2: session_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        session1 <> session2 /\
        (smd_ideal_system k know0).transitions s (TestedSystem.Internal session1) s_mid /\
        smd_sim_receive_protocol_transition (s2p_state s_mid) session2 (s2p_state s') /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (smd_ideal_system k know0).transitions s (TestedSystem.Internal session2) s_mid' /\
          (smd_ideal_system k know0).transitions s_mid' (TestedSystem.Internal session1) s') =
  let _s_mid' : ideal_system_state =
    p2s_state (smd_sim_receive_state (s2p_state s) session2) s.know in
  let brr (x y: term)
    : Lemma (Bag.remove x (Bag.remove y s.inputs) ==
             Bag.remove y (Bag.remove x s.inputs)) =
    Bag.remove_remove_commute x y s.inputs in
  FStar.Classical.forall_intro_2 brr;
  _set_add_commute session1 session2 s.internal.sim_received_sessions;
  _set_add_commute (SessionId session1) (SessionId session2) s.internal.sim_to_ideal_channel;
  _set_add_commute (SessionId session1) (SessionId session2) s.internal.ideal_to_sim_channel

// ---- Internal(s1) commutes with Internal(s2) (combined) ----

private
let _ideal_internal_internal_commute
      (k: key) (know0: knowledge term)
      (session1 session2: session_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        session1 <> session2 /\
        (smd_ideal_system k know0).transitions s (TestedSystem.Internal session1) s_mid /\
        (smd_ideal_system k know0).transitions s_mid (TestedSystem.Internal session2) s')
      (ensures
        exists s_mid'.
          (smd_ideal_system k know0).transitions s (TestedSystem.Internal session2) s_mid' /\
          (smd_ideal_system k know0).transitions s_mid' (TestedSystem.Internal session1) s') =
  let the_goal : prop =
    exists s_mid'.
      (smd_ideal_system k know0).transitions s (TestedSystem.Internal session2) s_mid' /\
      (smd_ideal_system k know0).transitions s_mid' (TestedSystem.Internal session1) s' in
  let handle_commit
    (_: squash (smd_ideal_commit_protocol_transition (s2p_state s_mid) session2 (s2p_state s')))
    : Lemma (the_goal) =
    FStar.Classical.exists_elim the_goal #term
      #(fun msg2 -> smd_ideal_commit_enabled (s2p_state s_mid) session2 msg2 /\
                     s2p_state s' == smd_ideal_commit_state (s2p_state s_mid) session2 msg2)
      ()
      (fun msg2 -> _ideal_commit_commutes k know0 session1 session2 msg2 s s_mid s')
  in
  let handle_recv
    (_: squash (smd_sim_receive_protocol_transition (s2p_state s_mid) session2 (s2p_state s')))
    : Lemma (the_goal) =
    _ideal_recv_commutes k know0 session1 session2 s s_mid s'
  in
  FStar.Classical.or_elim
    #(smd_ideal_commit_protocol_transition (s2p_state s_mid) session2 (s2p_state s'))
    #(smd_sim_receive_protocol_transition (s2p_state s_mid) session2 (s2p_state s'))
    #(fun _ -> the_goal)
    handle_commit
    handle_recv

// ---- Internal(s1) commutes with Observable(eff, s2) ----

private
let _ideal_internal_observable_commute
      (k: key) (know0: knowledge term)
      (session1 session2: session_id) (eff: smd_effect)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        session1 <> session2 /\
        (smd_ideal_system k know0).transitions s (TestedSystem.Internal session1) s_mid /\
        (smd_ideal_system k know0).transitions s_mid (TestedSystem.Observable eff session2) s')
      (ensures
        exists s_mid'.
          (smd_ideal_system k know0).transitions s (TestedSystem.Observable eff session2) s_mid' /\
          (smd_ideal_system k know0).transitions s_mid' (TestedSystem.Internal session1) s') =
  _set_add_remove_commute (SessionId session1) (SessionId session2) s.internal.ideal_to_sim_channel;
  _set_remove_add_commute (SessionId session2) (SessionId session1) s.internal.ideal_to_sim_channel;
  _set_add_remove_commute (SessionId session1) (SessionId session2) s.internal.sim_to_ideal_channel;
  _set_remove_add_commute (SessionId session2) (SessionId session1) s.internal.sim_to_ideal_channel;
  _set_add_commute session1 session2 s.internal.sim_sent_sessions;
  _set_add_commute session1 session2 s.internal.sim_received_sessions;
  _set_add_commute (SessionId session1) (SessionId session2) s.internal.ideal_to_sim_channel;
  _set_add_commute (SessionId session1) (SessionId session2) s.internal.sim_to_ideal_channel;
  match eff with
  | NetSend ->
    let emitted = Senc (SessionId session2) s.internal.sim_key in
    let _s_mid' : ideal_system_state =
      p2s_state (smd_sim_send_state (s2p_state s) session2) (Seq.snoc s.know emitted) in
    ()
  | IoSend ->
    let message = Some?.v (PartialMap.sel s.internal.messages session2) in
    let emitted = Pair (SessionId session2) message in
    let _s_mid' : ideal_system_state =
      p2s_state (smd_ideal_deliver_state (s2p_state s) session2) (Seq.snoc s.know emitted) in
    ()
#pop-options

// The ideal protocol now has internal transitions (commit and sim_receive).
// Right-movability requires that an internal transition tau for session s1
// commutes with any transition alpha in a different partition (different session
// s2 or Input). This holds because transitions for different sessions modify
// independent state (different keys in PartialMap, different Set members),
// and Input transitions only add to the bag which commutes with everything.

// ---- Core dispatch: is_internal tau, ~same(tau, alpha) => commutable ----

#push-options "--z3rlimit 20 --split_queries no"
private
let _ideal_commutativity_core (k: key) (know0: knowledge term)
      (tau alpha: system_label) (s s_mid s': ideal_system_state)
    : Lemma
      (requires is_internal tau /\ ~(smd_label_in_same_partition tau alpha) /\
               (smd_ideal_system k know0).transitions s tau s_mid /\
               (smd_ideal_system k know0).transitions s_mid alpha s')
      (ensures exists s_mid'.
               (smd_ideal_system k know0).transitions s alpha s_mid' /\
               (smd_ideal_system k know0).transitions s_mid' tau s') =
  let TestedSystem.Internal session1 = tau in
  match alpha with
  | TestedSystem.Internal session2 ->
    _ideal_internal_internal_commute k know0 session1 session2 s s_mid s'
  | TestedSystem.Observable eff session2 ->
    _ideal_internal_observable_commute k know0 session1 session2 eff s s_mid s'
  | TestedSystem.Input d ->
    _ideal_internal_input_commute k know0 session1 d s s_mid s'

// ---- Right-movability for ideal ----

private
let smd_right_movable_ideal (k: key) (know0: knowledge term)
    : Lemma (right_movable (smd_ideal_system k know0) smd_partition) =
  smd_label_in_same_partition_equiv ();
  let p = smd_ideal_system k know0 in
  introduce forall (rho: system_label) (rho': system_label).
    ~(smd_partition.in_same_partition rho rho') ==>
    (forall (tau: system_label) (alpha: system_label)
        (s: ideal_system_state) (s_mid: ideal_system_state) (s': ideal_system_state).
      smd_partition.in_same_partition tau rho /\ is_internal tau /\
      smd_partition.in_same_partition alpha rho' /\
      p.transitions s tau s_mid /\ p.transitions s_mid alpha s' ==>
      (exists (s_mid': ideal_system_state).
        p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s'))
  with (
    introduce _ ==> _
    with _h. (
      introduce forall (tau: system_label) (alpha: system_label)
          (s: ideal_system_state) (s_mid: ideal_system_state) (s': ideal_system_state).
        smd_partition.in_same_partition tau rho /\ is_internal tau /\
        smd_partition.in_same_partition alpha rho' /\
        p.transitions s tau s_mid /\ p.transitions s_mid alpha s' ==>
        (exists (s_mid': ideal_system_state).
          p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s')
      with (
        introduce _ ==> _
        with _h2. (
          smd_symm_lemma tau rho;
          smd_trans_lemma rho tau alpha;
          smd_trans_lemma rho alpha rho';
          _ideal_commutativity_core k know0 tau alpha s s_mid s'
        )
      )
    )
  )
#pop-options



/// =========================================================================
/// Initial states satisfy the bisimulation relation
/// =========================================================================

private
let rec no_impl_senc_implies_canonical_ideal (t: term) (k: key)
  : Lemma
    (requires forall (i: session_id) (m: term). ~(in_term t (Senc (Pair (SessionId i) m) k)))
    (ensures canonical_ideal t k)
    (decreases t) =
  match t with
  | Senc m k' ->
    no_impl_senc_implies_canonical_ideal m k
  | Pair t1 t2 ->
    no_impl_senc_implies_canonical_ideal t1 k;
    no_impl_senc_implies_canonical_ideal t2 k
  | _ -> ()

(**
  Structural preservation of `canonical_ideal` under
  `built_from_know_and_ciphertext`: if the ciphertext is itself
  canonical_ideal, every term in `know` derives canonically, and `Key k` is
  not derivable from `know`, then any `built_from` term is canonical_ideal.
*)
private
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

(**
  Structural preservation of "no Senc(SessionId i) k subterm" under
  `built_from_know_and_ciphertext`: if the ciphertext has no such subterm,
  every term in `know` has no such subterm in any derivation, and `Key k`
  is not derivable from `know`, then any `built_from` term has no such
  subterm.
*)
private
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
      // built_from gives derivable know (Key k'); ¬derivable know (Key k) ⇒ k' <> k.
      // Hence Senc p k' <> Senc(SessionId i) k, and in_term reduces to in_term p ...
      no_ideal_senc_built_from know k m i p
    | _ -> ()

private
let rec smd_bi_subst_empty_identity (t: term) (k: key)
  : Lemma
    (ensures smd_bi_subst t (PartialMap.empty session_id term) k k == t)
    (decreases t) =
  match t with
  | Pair t1 t2 ->
    smd_bi_subst_empty_identity t1 k;
    smd_bi_subst_empty_identity t2 k
  | Senc m _ ->
    smd_bi_subst_empty_identity m k
  | _ -> ()

private
let count_empty_is_zero (t: term)
  : Lemma (Bag.count (Bag.empty #term) t == 0) =
  Bag.mem_count t (Bag.empty #term);
  Bag.mem_empty t

private
let rec indistinguishable_refl (t: term)
  : Lemma (ensures (indistinguishable t t))
    (decreases t) =
  match t with
  | Pair t1 t2 ->
    indistinguishable_refl t1;
    indistinguishable_refl t2
  | _ -> ()

private
let statically_equivalent_refl (know: knowledge term)
  : Lemma (ensures (statically_equivalent adv know know)) =
  let indist_helper (d: derivation)
    : Lemma (ensures (indistinguishable' adv.indistinguishable
        (adv.derive d know)
        (adv.derive d know))) =
    match adv.derive d know with
    | None -> ()
    | Some t ->
      indistinguishable_refl t
  in
  FStar.Classical.forall_intro indist_helper;
  let eq_helper (d1 d2: derivation)
    : Lemma (ensures ((adv.derive d1 know = adv.derive d2 know) <==>
             (adv.derive d1 know = adv.derive d2 know))) = ()
  in
  FStar.Classical.forall_intro_2 eq_helper

private
let smd_init_bijective_correspondence (k: key) (know0: knowledge term)
  : Lemma
    (ensures
      bijective_correspondence_on_derivations adv know0 know0
        (smd_subst_bijection k k (PartialMap.empty session_id term))) =
  let bij = smd_subst_bijection k k (PartialMap.empty session_id term) in
  let bij_helper (d: derivation)
    : Lemma (derive d know0 = Option.mapTot bij.cright (derive d know0)) =
    match derive d know0 with
    | None -> ()
    | Some t ->
      smd_bi_subst_empty_identity t k
  in
  FStar.Classical.forall_intro bij_helper

private
let smd_init_input_bag_correspondence (k: key) (know0: knowledge term)
  : Lemma
    (ensures (forall t.
      Bag.count ((smd_impl_system k know0).init).inputs t ==
      Bag.count ((smd_ideal_system k know0).init).inputs
        ((smd_subst_bijection k k (PartialMap.empty session_id term)).cright t))) =
  let s_impl = (smd_impl_system k know0).init in
  let s_ideal = (smd_ideal_system k know0).init in
  let bij = smd_subst_bijection k k (PartialMap.empty session_id term) in
  let count_helper (t: term)
    : Lemma (Bag.count s_impl.inputs t == Bag.count s_ideal.inputs (bij.cright t)) =
    count_empty_is_zero t;
    count_empty_is_zero (bij.cright t)
  in
  FStar.Classical.forall_intro count_helper

private
let smd_init_related (k: key) (know0: knowledge term)
  : Lemma
    (requires
      ~(derivable know0 (Key k))
      /\ (forall (d: derivation) (t: term) (i: session_id) (m: term).
          derive d know0 = Some t ==>
          ~(in_term t (Senc (Pair (SessionId i) m) k)))
      /\ (forall (d: derivation) (t: term) (i: session_id).
          derive d know0 = Some t ==>
          ~(in_term t (Senc (SessionId i) k))))
    (ensures smd_bisim_relation k (smd_impl_system k know0).init (smd_ideal_system k know0).init) =
  smd_init_bijective_correspondence k know0;
  statically_equivalent_refl know0;
  smd_init_input_bag_correspondence k know0;
  // Discharge the canonical_ideal clause on derivable terms: initial know0
  // has no Senc(Pair(SessionId _) _) k subterm in any derivable term, so
  // by the structural lemma below every derivable term is canonical_ideal.
  let canonical_helper (d: derivation)
    : Lemma (forall t. derive d know0 = Some t ==> canonical_ideal t k) =
    match derive d know0 with
    | None -> ()
    | Some t -> no_impl_senc_implies_canonical_ideal t k
  in
  FStar.Classical.forall_intro canonical_helper;
  ()



/// =========================================================================
/// Static equivalence from the bisimulation relation
/// =========================================================================

private
let smd_static_equiv_from_rel (k: key)
    : Lemma
    (forall (s_p: TestedSystem.state term impl_internal_state)
        (s_q: TestedSystem.state term ideal_internal_state).
        smd_bisim_relation k s_p s_q ==> statically_equivalent adv s_p.know s_q.know) = ()



/// =========================================================================
/// Input step simulation: adding a term to the inputs bag
/// =========================================================================

(**
  For the impl-to-ideal direction: if s_p takes an Input step (the adversary
  derives a term using derivation `d` and injects it into the inputs bag), then the same step in the ideal world can occur and the new states remain related by the bisimulation relation.

  Relies on: the bisimulation relation is preserved under inputs-bag extension,
  using bijective_correspondence_on_derivations and append_preserves_derive.
*)

#push-options "--z3rlimit 20 --fuel 8 --ifuel 4"
private
let derivable_senc_implies_message_stored
      (k: key)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        derivable s_p.know (Senc (Pair (SessionId session) message) k))
      (ensures
        PartialMap.sel s_p.internal.messages session == Some message /\
        PartialMap.sel s_q.internal.messages session
          == Some (smd_bi_subst message s_p.internal.messages k k))
  =
  let impl_trig = Senc (Pair (SessionId session) message) k in
  assert_norm (in_term impl_trig impl_trig);
  let d_impl_trig = FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation
    (fun d' -> adv.derive d' s_p.know = Some impl_trig) in
  assert (adv.derive d_impl_trig s_p.know = Some impl_trig);
  assert (impl_invariant_messages_consistent_with_knowledge s_p)
  by (
    let open FStar.Tactics.V2 in
    iter (fun b ->
      norm_binding_type
        [delta_only [`%implementation_invariants; `%smd_bisim_relation]]
        b)
      (cur_vars ());
    smt ()
  );
  assert (PartialMap.sel s_p.internal.messages session == Some message)
  by (
    let open FStar.Tactics.V2 in
    iter (fun b ->
      norm_binding_type
        [delta_only [`%impl_invariant_messages_consistent_with_knowledge]]
        b)
      (cur_vars ());
    set_options "--z3rlimit 40";
    smt ()
  )
#pop-options

#push-options "--z3rlimit 20 --fuel 8 --ifuel 4 --split_queries no"
private
let smd_obs_bisim_input_step_impl
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (d: adv.derivation)
      (s_p': TestedSystem.state term impl_internal_state)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        (smd_impl_system k know0).transitions s_p (TestedSystem.Input d) s_p')
      (ensures (
        exists s_q'.
          (smd_ideal_system k know0).transitions s_q (TestedSystem.Input d) s_q'
          /\ smd_bisim_relation k s_p' s_q'
      )) =
  let bij = SMD.Bijection.smd_subst_bijection k k s_p.internal.messages in
  // bijective_correspondence_on_derivations gives:
  //   derive d s_q.know == Option.mapTot bij.cright (derive d s_p.know)
  assert (adv.derive d s_q.know == Option.mapTot bij.cright (adv.derive d s_p.know));
  // The Input transition requires adv.derive d s_p.know to be Some.
  assert (Some? (adv.derive d s_p.know));
  let t_impl = Some?.v (adv.derive d s_p.know) in
  let t_ideal = bij.cright t_impl in
  assert (s_p'.inputs == Bag.insert t_impl s_p.inputs);
  assert (s_p'.know == s_p.know);
  assert (s_p'.internal == s_p.internal);
  // Construct the ideal witness state: same knowledge and internal, with
  // `t_ideal` inserted into the inputs bag.
  let s_q': TestedSystem.state term ideal_internal_state = {
    know = s_q.know;
    inputs = Bag.insert t_ideal s_q.inputs;
    internal = s_q.internal
  } in
  // Ideal transition: witness `t_ideal` in the Input existential.
  assert ((smd_ideal_system k know0).transitions s_q (TestedSystem.Input d) s_q');
  // Count correspondence after insert: uses bijection injectivity to handle
  // the discriminator `x = t_impl <==> bij.cright x = bij.cright t_impl`.
  let count_aux (x: term)
    : Lemma (Bag.count s_p'.inputs x == Bag.count s_q'.inputs (bij.cright x)) =
    if x = t_impl then ()
    else FStar.Bijection.Ext.bijection_right_injective bij x t_impl
  in
  FStar.Classical.forall_intro count_aux;
  // Derivability of inputs: `t_impl` is derivable (via `d`), and every other
  // term in s_p'.inputs was already derivable from s_p.know = s_p'.know.
  assert (derivable s_p.know t_impl);
  assert (derivable s_q.know t_ideal);
  assert (forall t. Bag.mem t s_p'.inputs ==> derivable s_p'.know t);
  assert (forall t. Bag.mem t s_q'.inputs ==> derivable s_q'.know t);
  // The send / receive enabled iffs require showing that membership of the
  // triggering term in the impl and ideal inputs bags correspond through the
  // substitution bijection.  The count correspondence above gives this, but
  // SMT needs help to see that smd_bi_subst distributes over Pair / Senc of
  // the specific trigger shapes.
  let send_enabled_aux (session: session_id) (message: term)
    : Lemma (
        smd_impl_protocol_send_enabled (s2p_state s_p') session message k <==>
        smd_ideal_protocol_send_enabled (s2p_state s_q') session
          (smd_bi_subst message s_p.internal.messages k k)) =
    let impl_trig = Pair (SessionId session) message in
    SMD.Bijection.smd_subst_bijection_right k k s_p.internal.messages impl_trig;
    count_aux impl_trig
  in
  FStar.Classical.forall_intro_2 send_enabled_aux;
  // The receive_enabled iff requires matching the ideal side's
  // `PartialMap.sel messages session == Some (smd_bi_subst message ...)` check.
  // This follows from:
  //   (a) impl_invariant_messages_consistent_with_knowledge: if Senc(Pair(SessionId s, m), k)
  //       is derivable, then impl.messages[s] = Some m.
  //   (b) messages correspondence in the bisim: ideal.messages[s] = mapTot(smd_bi_subst _ impl.messages k k, impl.messages[s]).
  //   (c) The old receive_enabled iff at s_p/s_q, which covers the case where the
  //       trigger was already present in inputs.
  let receive_enabled_aux (session: session_id) (message: term)
    : Lemma (
        smd_impl_protocol_receive_enabled (s2p_state s_p') session message <==>
        smd_ideal_protocol_receive_enabled (s2p_state s_q') session
          (smd_bi_subst message s_p.internal.messages k k)) =
    let impl_trig = Senc (Pair (SessionId session) message) k in
    let ideal_m = smd_bi_subst message s_p.internal.messages k k in
    SMD.Bijection.smd_subst_bijection_right k k s_p.internal.messages impl_trig;
    count_aux impl_trig;
    if Bag.mem impl_trig s_p'.inputs then
      derivable_senc_implies_message_stored k s_p s_q session message
    else begin
      // Reverse direction: if ideal side is enabled, derive that the impl map
      // stores `message`, which then makes count_aux line up impl and ideal
      // triggers.
      match PartialMap.sel s_p.internal.messages session with
      | Some m_p ->
        // Bisim messages correspondence gives:
        //   sel s_q.messages session == Some (smd_bi_subst m_p)
        // If ideal side is enabled, sel s_q.messages session == Some ideal_m
        //   so smd_bi_subst m_p == ideal_m == smd_bi_subst message.
        // By bijection injectivity, m_p == message.
        if PartialMap.sel s_q.internal.messages session = Some ideal_m then
          FStar.Bijection.Ext.bijection_injective bij m_p message
      | None -> ()
    end
  in
  FStar.Classical.forall_intro_2 receive_enabled_aux
#pop-options



/// For the ideal-to-impl direction: if s_q takes an Input step, the bisimulation
/// relation is preserved with the unchanged impl state s_p.

#push-options "--z3rlimit 20 --fuel 8 --ifuel 4 --split_queries no"
private
let smd_obs_bisim_input_step_ideal
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (d: adv.derivation)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        (smd_ideal_system k know0).transitions s_q (TestedSystem.Input d) s_q')
      (ensures
        exists s_p'.
          (smd_impl_system k know0).transitions s_p (TestedSystem.Input d) s_p'
          /\ smd_bisim_relation k s_p' s_q') =
  let bij = SMD.Bijection.smd_subst_bijection k k s_p.internal.messages in
  assert (adv.derive d s_q.know == Option.mapTot bij.cright (adv.derive d s_p.know));
  assert (Some? (adv.derive d s_q.know));
  assert (Some? (adv.derive d s_p.know));
  let t_impl = Some?.v (adv.derive d s_p.know) in
  let t_ideal = bij.cright t_impl in
  assert (s_q'.inputs == Bag.insert t_ideal s_q.inputs);
  assert (s_q'.know == s_q.know);
  assert (s_q'.internal == s_q.internal);
  let s_p': TestedSystem.state term impl_internal_state = {
    know = s_p.know;
    inputs = Bag.insert t_impl s_p.inputs;
    internal = s_p.internal
  } in
  assert ((smd_impl_system k know0).transitions s_p (TestedSystem.Input d) s_p');
  let count_aux (x: term)
    : Lemma (Bag.count s_p'.inputs x == Bag.count s_q'.inputs (bij.cright x)) =
    if x = t_impl then ()
    else FStar.Bijection.Ext.bijection_right_injective bij x t_impl
  in
  FStar.Classical.forall_intro count_aux;
  assert (derivable s_p.know t_impl);
  assert (derivable s_q.know t_ideal);
  assert (forall t. Bag.mem t s_p'.inputs ==> derivable s_p'.know t);
  assert (forall t. Bag.mem t s_q'.inputs ==> derivable s_q'.know t);
  let send_enabled_aux (session: session_id) (message: term)
    : Lemma (
        smd_impl_protocol_send_enabled (s2p_state s_p') session message k <==>
        smd_ideal_protocol_send_enabled (s2p_state s_q') session
          (smd_bi_subst message s_p.internal.messages k k)) =
    let impl_trig = Pair (SessionId session) message in
    SMD.Bijection.smd_subst_bijection_right k k s_p.internal.messages impl_trig;
    count_aux impl_trig
  in
  FStar.Classical.forall_intro_2 send_enabled_aux;
  let receive_enabled_aux (session: session_id) (message: term)
    : Lemma (
        smd_impl_protocol_receive_enabled (s2p_state s_p') session message <==>
        smd_ideal_protocol_receive_enabled (s2p_state s_q') session
          (smd_bi_subst message s_p.internal.messages k k)) =
    let impl_trig = Senc (Pair (SessionId session) message) k in
    let ideal_m = smd_bi_subst message s_p.internal.messages k k in
    SMD.Bijection.smd_subst_bijection_right k k s_p.internal.messages impl_trig;
    count_aux impl_trig;
    if Bag.mem impl_trig s_p'.inputs then
      derivable_senc_implies_message_stored k s_p s_q session message
    else begin
      match PartialMap.sel s_p.internal.messages session with
      | Some m_p ->
        if PartialMap.sel s_q.internal.messages session = Some ideal_m then
          FStar.Bijection.Ext.bijection_injective bij m_p message
      | None -> ()
    end
  in
  FStar.Classical.forall_intro_2 receive_enabled_aux
#pop-options


/// =========================================================================
/// Observable step simulation: split by effect (send / receive)
/// =========================================================================
///
/// The full simulation lemmas split by the observable effect label:
///   - NetSend: implementation sends Senc(Pair(SessionId, m), k)
///              ideal responds with Senc(SessionId, sim_key)
///   - IoSend:  implementation delivers Pair(SessionId, m)
///              ideal delivers the corresponding stored ideal message
///
/// Each case ultimately relies on the algebraic bisimulation lemmas in
/// SMD.ObservationalBisimulation (impl_send_implies_ideal_commit_sim_send_equivalent_preserves_observational_bisimulation_relation, etc.).
/// Those lemmas work at the impl_state / ideal tested-system level; bridging
/// them to the full TestedSystem protocol state and smd_bisim_relation is
/// future work.

/// Impl sends (NetSend): proved in SMD.ObservationalBisimulation.Witnesses.
/// See `smd_obs_bisim_observable_step_impl_send` there for the statement with
/// an explicit witness state (`smd_impl_send_ideal_witness`).

private
let smd_obs_bisim_observable_step_impl_send
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
      smd_impl_protocol_send_transition (s2p_state s_p)
        session
        (Senc impl_trigger_input k)
        (s2p_state s_p') /\ s_p'.know == Seq.snoc s_p.know (Senc impl_trigger_input k)
    ))
    (ensures
      exists (lbls': list system_label) s_q'.
        label_effects lbls'
          == [TestEquivalence.Observable NetSend] /\
        eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q' /\
        smd_bisim_relation k s_p' s_q') =
  let s_q' = smd_impl_send_ideal_witness k s_p.internal.messages s_q session message in
  smd_obs_bisim_observable_step_impl_send k know0 s_p s_q session message s_p';
  smd_obs_bisim_observable_step_impl_send_preserves_relation k know0 s_p s_q session message s_p';
  let lbls' : list system_label = [TestedSystem.Internal session; TestedSystem.Observable NetSend session] in
  // The current F* normalizer does not inline the `let`-bound `lbls'` into an
  // `assert_norm` goal, so reduce `label_effects` over the explicit literal
  // (which is definitionally `lbls'`) instead.
  assert_norm (label_effects ([TestedSystem.Internal session; TestedSystem.Observable NetSend session] <: list system_label)
               == [TestEquivalence.Observable NetSend]);
  ()



/// Impl receives (IoSend): show ideal can match with a corresponding IoSend step.

private
let smd_obs_bisim_observable_step_impl_recv
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (session: session_id)
    (message: term)
    (s_p': TestedSystem.state term impl_internal_state)
  : Lemma
    (requires (
      let t = Pair (SessionId session) message in
      smd_bisim_relation k s_p s_q /\
      smd_impl_protocol_receive_transition (s2p_state s_p)
        session
        t
        (s2p_state s_p') /\ s_p'.know == Seq.snoc s_p.know t
    ))
    (ensures
      exists (lbls': list system_label) s_q'.
        label_effects lbls'
          == [TestEquivalence.Observable IoSend] /\
        eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q' /\
        smd_bisim_relation k s_p' s_q') =
  let s_q' = smd_impl_receive_ideal_witness k s_p.internal.messages s_q session message in
  smd_obs_bisim_observable_step_impl_receive k know0 s_p s_q session message s_p';
  smd_obs_bisim_observable_step_impl_recv_preserves_relation k know0 s_p s_q session message s_p';
  let lbls' : list system_label = [TestedSystem.Internal session; TestedSystem.Observable IoSend session] in
  // See note above: reduce `label_effects` over the explicit literal.
  assert_norm (label_effects ([TestedSystem.Internal session; TestedSystem.Observable IoSend session] <: list system_label)
               == [TestEquivalence.Observable IoSend]);
  ()


/// Combine send and receive into the full observable step lemma for impl→ideal.

private
let smd_obs_bisim_observable_step_impl
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (session: session_id)
    (eff: smd_effect)
    (s_p': TestedSystem.state term impl_internal_state)
  : Lemma
    (requires
      smd_bisim_relation k s_p s_q /\
      (smd_impl_system k know0).transitions s_p (TestedSystem.Observable eff session) s_p')
    (ensures
      exists (lbls': list system_label) s_q'.
        label_effects lbls' == [TestEquivalence.Observable eff] /\
        eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q' /\
        smd_bisim_relation k s_p' s_q') =
  match eff with
  | NetSend ->
    let impl_message = Some?.v (PartialMap.sel s_p'.internal.messages session) in
    smd_obs_bisim_observable_step_impl_send k know0 s_p s_q session impl_message s_p'
  | IoSend ->
    // Extract the delivered `Pair (SessionId session) message` from the
    // transition existential, then project out the payload `message`.
    let p_t (t: term) : prop =
      smd_impl_protocol_receive_transition (s2p_state s_p) session t (s2p_state s_p') /\
      s_p'.know == Seq.snoc s_p.know t
    in
    assert (exists t. p_t t);
    let t = FStar.IndefiniteDescription.indefinite_description_ghost term p_t in
    assert (p_t t);
    (match t with
     | Pair t1 message ->
       (match t1 with
        | SessionId _ ->
          smd_obs_bisim_observable_step_impl_recv k know0 s_p s_q session message s_p'
        | _ -> assert False)
     | _ -> assert False)



/// Ideal sends (NetSend): show impl can match with a corresponding NetSend step.

private
let smd_obs_bisim_observable_step_ideal_send
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (t: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        smd_ideal_protocol_send_transition ({ inputs = s_q.inputs; internal = s_q.internal })
          session
          t
          ({ inputs = s_q'.inputs; internal = s_q'.internal }) /\ s_q'.know == Seq.snoc s_q.know t)
      (ensures
        exists s_p'.
          (smd_impl_system k know0).transitions s_p (TestedSystem.Observable NetSend session) s_p' /\
          smd_bisim_relation k s_p' s_q') =
  // Extract the ideal trigger message from the transition existential.
  let p_msg (m: term) : prop =
    smd_ideal_protocol_send_enabled (s2p_state s_q) session m /\
    (s2p_state s_q') == smd_ideal_protocol_send_state (s2p_state s_q) session m
  in
  assert (exists m. p_msg m);
  let ideal_message =
    FStar.IndefiniteDescription.indefinite_description_ghost term p_msg
  in
  assert (p_msg ideal_message);
  let s_p' = smd_ideal_send_impl_witness k s_p session ideal_message in
  smd_obs_bisim_observable_step_ideal_send k know0 s_p s_q session ideal_message s_q';
  smd_obs_bisim_observable_step_ideal_send_preserves_relation k know0 s_p s_q session ideal_message s_q';
  ()



/// Ideal receives (IoSend): show impl can match with a corresponding IoSend step.

private
let smd_obs_bisim_observable_step_ideal_recv
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (message: term)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires (
        let t = Pair (SessionId session) message in
        smd_bisim_relation k s_p s_q /\
        smd_ideal_protocol_receive_transition (s2p_state s_q)
          session
          t
          (s2p_state s_q') /\ s_q'.know == Seq.snoc s_q.know t))
      (ensures
        exists s_p'.
          (smd_impl_system k know0).transitions s_p (TestedSystem.Observable IoSend session) s_p' /\
          smd_bisim_relation k s_p' s_q') =
  let s_p' = smd_ideal_receive_impl_witness k s_p session message in
  smd_obs_bisim_observable_step_ideal_receive k know0 s_p s_q session message s_q';
  smd_obs_bisim_observable_step_ideal_recv_preserves_relation k know0 s_p s_q session message s_q';
  ()



/// Combine send and receive into the full observable step lemma for ideal→impl.

private
let smd_obs_bisim_observable_step_ideal
      (k: key)
      (know0: knowledge term)
      (s_p: TestedSystem.state term impl_internal_state)
      (s_q: TestedSystem.state term ideal_internal_state)
      (session: session_id)
      (eff: smd_effect)
      (s_q': TestedSystem.state term ideal_internal_state)
    : Lemma
      (requires
        smd_bisim_relation k s_p s_q /\
        (smd_ideal_system k know0).transitions s_q (TestedSystem.Observable eff session) s_q')
      (ensures
        exists s_p'.
          (smd_impl_system k know0).transitions s_p (TestedSystem.Observable eff session) s_p' /\
          smd_bisim_relation k s_p' s_q') =
  match eff with
  | NetSend ->
    let t = Senc (SessionId session) k in
    smd_obs_bisim_observable_step_ideal_send k know0 s_p s_q session t s_q'
  | IoSend ->
    // Extract the delivered `Pair (SessionId session) message` from the
    // transition existential, then project out the payload `message`.
    let p_t (t: term) : prop =
      smd_ideal_protocol_receive_transition (s2p_state s_q)
        session t (s2p_state s_q') /\
      s_q'.know == Seq.snoc s_q.know t
    in
    assert (exists t. p_t t);
    let t = FStar.IndefiniteDescription.indefinite_description_ghost term p_t in
    assert (p_t t);
    (match t with
     | Pair t1 message ->
       (match t1 with
        | SessionId _ ->
          smd_obs_bisim_observable_step_ideal_recv k know0 s_p s_q session message s_q'
        | _ -> assert False)
     | _ -> assert False)



/// =========================================================================
/// Main observational bisimulation up to partitions
/// =========================================================================
///
/// obs_bisim_up_to_partitions uses eventually_observable_step (multi-step via
/// right-movable internal transitions), which requires more than single-step
/// simulation.  The full proof is deferred; the single-step helpers above
/// provide the structure for completing it.

private
let smd_obs_sim_impl_ideal_instance
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (partition_l: system_label)
    (lbls: list system_label)
    (s_p': TestedSystem.state term impl_internal_state)
  : Lemma
    (requires (
      smd_bisim_relation k s_p s_q /\
      lbls_in_partition lbls smd_partition partition_l /\
      eventually_observable_step (smd_impl_system k know0) s_p lbls s_p'))
    (ensures (
      exists lbls' s_q'.
        label_effects lbls' == label_effects lbls
        /\ eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q'
        /\ smd_bisim_relation k s_p' s_q')) =
  match lbls with
  | [TestedSystem.Observable eff session] ->
    smd_obs_bisim_observable_step_impl k know0 s_p s_q session eff s_p';
    assert (exists (lbls'': list system_label) s_q'.
      label_effects lbls'' == [TestEquivalence.Observable eff] /\
      eventually_observable_step (smd_ideal_system k know0) s_q lbls'' s_q' /\
      smd_bisim_relation k s_p' s_q');
    ()
  | [TestedSystem.Input d] ->
    let lbls' : list system_label = [TestedSystem.Input d] in
    assert (label_effects lbls' == label_effects lbls);
    smd_obs_bisim_input_step_impl k know0 s_p s_q d s_p';
    assert (exists s_q'.
      (smd_ideal_system k know0).transitions s_q (TestedSystem.Input d) s_q'
      /\ eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q'
      /\ smd_bisim_relation k s_p' s_q');
    ()
  // Trivial, no transition.
  | [] -> ()
  // Trivial, all valid eventually observable transitions have already been handled.
  | _ -> ()


/// =========================================================================
/// Characterization lemmas for ideal eventually-observable steps
/// =========================================================================

/// Helper: the ideal protocol has no internal transition for session when
/// commit is not enabled and sim_receive is not enabled.
private
let ideal_internal_transition_cases
      (k: key)
      (s: Protocol.state term ideal_internal_state)
      (session: session_id)
      (s': Protocol.state term ideal_internal_state)
    : Lemma
      (requires
        s.internal.sim_key == k /\
        smd_ideal_protocol_transition s (Protocol.Internal session) s')
      (ensures
        smd_ideal_commit_protocol_transition s session s' \/
        smd_sim_receive_protocol_transition s session s')
    = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"

/// Auxiliary: Senc (SessionId session) k is NOT in inputs at a state satisfying
/// the ideal invariants when session is not in sim_sent_sessions.
private
let senc_not_in_inputs
      (s: TestedSystem.state term ideal_internal_state)
      (session: session_id)
    : Lemma
      (requires
        ideal_invariants s /\
        ideal_invariant_inputs_are_derivable s /\
        ~(Set.mem session s.internal.sim_sent_sessions))
      (ensures
        ~(Bag.mem (Senc (SessionId session) s.internal.sim_key) s.inputs))
    =
    let k = s.internal.sim_key in
    let t = Senc (SessionId session) k in
    // Help SMT: for any derivation d producing t, session must be in sim_sent.
    // The overall proof: if Bag.mem t s.inputs, then derivable s.know t (by inputs_are_derivable),
    // so some derivation produces t, but ideal_invariant_cannot_derive_valid_response_before_send
    // says that implies session in sim_sent_sessions, contradicting the requires.
    // Strategy: prove contrapositive — derivable s.know t ==> session in sim_sent (contradiction).
    assert (ideal_invariant_cannot_derive_valid_response_before_send s);
    let aux (d: derivation)
      : Lemma (requires (derive d s.know = Some t))
              (ensures (Set.mem session s.internal.sim_sent_sessions))
      =
      in_term_refl t;
      assert (adv.derive d s.know = Some t);
      assert (in_term t (Senc (SessionId session) k));
      assert (ideal_invariant_cannot_derive_valid_response_before_send s);
      assert (Set.mem session s.internal.sim_sent_sessions)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let smd_ideal_eventually_observable_send_characterization
      (k: key)
      (know0: knowledge term)
      (s s': TestedSystem.state term ideal_internal_state)
      (lbls: list (TestedSystem.label term smd_effect session_id adversary_senc))
      (session: session_id)
    : Lemma
      (requires
        ideal_invariants s /\
        ideal_invariant_inputs_are_derivable s /\
        s.internal.sim_key == k /\
        not (PartialMap.contains s.internal.messages session) /\
        ObservationalBisimulation.eventually_observable_step
          (smd_ideal_system k know0) s lbls s' /\
        (forall l. List.memP l lbls ==>
          smd_label_in_same_partition l
            (TestedSystem.Observable NetSend session)))
      (ensures
        lbls == [TestedSystem.Internal session;
                 TestedSystem.Observable NetSend session] /\
        s'.know == Seq.snoc s.know (Senc (SessionId session) k) /\
        smd_ideal_protocol_send_transition
          (s2p_state s) session (Senc (SessionId session) k) (s2p_state s'))
    =
  // Key facts from invariants
  senc_not_in_inputs s session;
  assert (~(Set.mem session s.internal.sim_sent_sessions));
  assert (~(Bag.mem (Senc (SessionId session) k) s.inputs));
  assert (~(Set.mem (SessionId session) s.internal.ideal_to_sim_channel));
  assert (~(Set.mem (SessionId session) s.internal.sim_to_ideal_channel));
  // Case-split on the list structure
  match lbls with
  | [] -> () // is_eventually_observable [] = false
  | [l] ->
    // l must be Observable (from is_eventually_observable [l] = not (is_internal l))
    // From partition, l = Observable _ session.
    // At s, channels empty → neither sim_send (needs ideal_to_sim_channel)
    // nor deliver (needs sim_to_ideal_channel) is enabled → contradiction.
    ()
  | [l1; l2] ->
    // l1 = Internal session, l2 = Observable eff session
    // multi_transitions: exists s_mid. tr s l1 s_mid /\ tr s_mid l2 s'
    //
    // Internal transition at s: commit or sim_receive.
    //   sim_receive needs PartialMap.contains messages session → false.
    //   So must be commit.
    // After commit: ideal_to_sim_channel has SessionId session.
    //   Observable NetSend (sim_send) is enabled.
    //   Observable IoSend (deliver) needs sim_to_ideal_channel → still empty → not enabled.
    // So l2 = Observable NetSend session.
    // Combined effect matches smd_ideal_protocol_send_transition.
    let tr = (smd_ideal_system k know0).transitions in
    // Extract intermediate state
    let p_mid (s_mid: TestedSystem.state term ideal_internal_state) : prop =
      tr s (TestedSystem.Internal session) s_mid /\
      multi_transitions tr s_mid [l2] s'
    in
    assert (exists s_mid. p_mid s_mid);
    let s_mid =
      FStar.IndefiniteDescription.indefinite_description_ghost
        (TestedSystem.state term ideal_internal_state) p_mid
    in
    assert (p_mid s_mid);
    // The internal transition must be commit (sim_receive is blocked)
    assert (smd_ideal_commit_protocol_transition (s2p_state s) session (s2p_state s_mid));
    // Extract the commit message witness
    let p_msg (m: term) : prop =
      smd_ideal_commit_enabled (s2p_state s) session m /\
      (s2p_state s_mid) == smd_ideal_commit_state (s2p_state s) session m
    in
    assert (exists m. p_msg m);
    let message =
      FStar.IndefiniteDescription.indefinite_description_ghost term p_msg
    in
    assert (p_msg message);
    // After commit, ideal_to_sim_channel has SessionId session
    assert (Set.mem (SessionId session) s_mid.internal.ideal_to_sim_channel);
    // sim_to_ideal_channel is still empty
    assert (~(Set.mem (SessionId session) s_mid.internal.sim_to_ideal_channel));
    // So l2 must be Observable NetSend session (not IoSend)
    // The sim_send step emits Senc (SessionId session) k
    assert (s'.know == Seq.snoc s.know (Senc (SessionId session) k));
    // Combined effect matches smd_ideal_protocol_send_transition
    commit_then_sim_send_equals_send_state (s2p_state s) session message;
    assert (smd_ideal_protocol_send_transition
      (s2p_state s) session (Senc (SessionId session) k) (s2p_state s'))
  | l1 :: l2 :: l3 :: rest ->
    // l1 = Internal session (from is_eventually_observable)
    // After l1 (commit), no second Internal is possible for session.
    // But l2 must be Internal (from is_eventually_observable, since l3::rest is non-empty).
    // Contradiction.
    let tr = (smd_ideal_system k know0).transitions in
    let p_mid (s_mid: TestedSystem.state term ideal_internal_state) : prop =
      tr s (TestedSystem.Internal session) s_mid /\
      multi_transitions tr s_mid (l2 :: l3 :: rest) s'
    in
    assert (exists s_mid. p_mid s_mid);
    let s_mid =
      FStar.IndefiniteDescription.indefinite_description_ghost
        (TestedSystem.state term ideal_internal_state) p_mid
    in
    assert (p_mid s_mid);
    // The internal step is commit
    assert (smd_ideal_commit_protocol_transition (s2p_state s) session (s2p_state s_mid));
    let p_msg (m: term) : prop =
      smd_ideal_commit_enabled (s2p_state s) session m /\
      (s2p_state s_mid) == smd_ideal_commit_state (s2p_state s) session m
    in
    assert (exists m. p_msg m);
    let message =
      FStar.IndefiniteDescription.indefinite_description_ghost term p_msg
    in
    assert (p_msg message);
    // After commit: messages[session] is set → commit blocked
    assert (PartialMap.contains s_mid.internal.messages session);
    // Senc not in s.inputs (proved above), and commit only removes Pair trigger
    // so Senc not in s_mid.inputs either → sim_receive blocked
    assert (~(Bag.mem (Senc (SessionId session) k) s_mid.inputs));
    // l2 must be Internal (from is_eventually_observable, since l3::rest non-empty)
    // But no Internal for session is possible at s_mid → contradiction
    assert False

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"

let smd_ideal_eventually_observable_receive_characterization
      (k: key)
      (know0: knowledge term)
      (s s': TestedSystem.state term ideal_internal_state)
      (lbls: list (TestedSystem.label term smd_effect session_id adversary_senc))
      (session: session_id)
    : Lemma
      (requires
        ideal_invariants s /\
        ideal_invariant_inputs_are_derivable s /\
        s.internal.sim_key == k /\
        PartialMap.contains s.internal.messages session /\
        ObservationalBisimulation.eventually_observable_step
          (smd_ideal_system k know0) s lbls s' /\
        (forall l. List.memP l lbls ==>
          smd_label_in_same_partition l
            (TestedSystem.Observable IoSend session)))
      (ensures
        exists (message: term).
          lbls == [TestedSystem.Internal session;
                   TestedSystem.Observable IoSend session] /\
          s'.know == Seq.snoc s.know (Pair (SessionId session) message) /\
          smd_ideal_protocol_receive_transition
            (s2p_state s) session
            (Pair (SessionId session) message) (s2p_state s'))
    =
  // Key facts from invariants
  assert (ideal_invariant_private_channels_empty s);
  assert (~(Set.mem (SessionId session) s.internal.ideal_to_sim_channel));
  assert (~(Set.mem (SessionId session) s.internal.sim_to_ideal_channel));
  assert (PartialMap.contains s.internal.messages session);
  // Case-split on the list structure
  match lbls with
  | [] -> () // is_eventually_observable [] = false
  | [l] ->
    // Observable requires channels → empty → contradiction
    ()
  | [l1; l2] ->
    // l1 = Internal session, l2 = Observable eff session
    // Internal at s: commit or sim_receive.
    //   commit needs not (PartialMap.contains messages session) → false (we have contains).
    //   So must be sim_receive.
    // After sim_receive: sim_to_ideal_channel has SessionId session.
    //   deliver (IoSend) is enabled.
    //   sim_send (NetSend) needs ideal_to_sim_channel → still empty → not enabled.
    // So l2 = Observable IoSend session.
    let tr = (smd_ideal_system k know0).transitions in
    let p_mid (s_mid: TestedSystem.state term ideal_internal_state) : prop =
      tr s (TestedSystem.Internal session) s_mid /\
      multi_transitions tr s_mid [l2] s'
    in
    assert (exists s_mid. p_mid s_mid);
    let s_mid =
      FStar.IndefiniteDescription.indefinite_description_ghost
        (TestedSystem.state term ideal_internal_state) p_mid
    in
    assert (p_mid s_mid);
    // The internal transition must be sim_receive (commit is blocked)
    assert (smd_sim_receive_protocol_transition (s2p_state s) session (s2p_state s_mid));
    // After sim_receive, sim_to_ideal_channel has SessionId session
    assert (Set.mem (SessionId session) s_mid.internal.sim_to_ideal_channel);
    // ideal_to_sim_channel is still empty (sim_receive doesn't change it)
    assert (~(Set.mem (SessionId session) s_mid.internal.ideal_to_sim_channel));
    // So l2 must be Observable IoSend session
    // Extract the message for the postcondition
    let msg = Some?.v (PartialMap.sel s.internal.messages session) in
    assert (s'.know == Seq.snoc s.know (Pair (SessionId session) msg));
    // Show combined effect matches smd_ideal_protocol_receive_transition
    sim_receive_then_deliver_equals_receive_state (s2p_state s) session msg;
    assert (smd_ideal_protocol_receive_transition
      (s2p_state s) session (Pair (SessionId session) msg) (s2p_state s'))
  | l1 :: l2 :: l3 :: rest ->
    // l1 = Internal session (sim_receive).
    // After sim_receive: sim_received_sessions has session → no more sim_receive.
    // And messages[session] set → no commit.
    // So no second Internal → l2 can't be Internal → contradiction with is_eventually_observable.
    let tr = (smd_ideal_system k know0).transitions in
    let p_mid (s_mid: TestedSystem.state term ideal_internal_state) : prop =
      tr s (TestedSystem.Internal session) s_mid /\
      multi_transitions tr s_mid (l2 :: l3 :: rest) s'
    in
    assert (exists s_mid. p_mid s_mid);
    let s_mid =
      FStar.IndefiniteDescription.indefinite_description_ghost
        (TestedSystem.state term ideal_internal_state) p_mid
    in
    assert (p_mid s_mid);
    // After sim_receive
    assert (smd_sim_receive_protocol_transition (s2p_state s) session (s2p_state s_mid));
    // After sim_receive: messages still set, sim_received_sessions has session
    // No commit (messages set) and no sim_receive (sim_received_sessions has session)
    // So no Internal transition for session at s_mid → l2 can't be Internal → contradiction
    assert False

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"

/// Helper: if an [Internal session; Observable NetSend session] eventually_observable_step
/// is possible, then messages does not contain session (so the Internal must be commit).
private
let internal_netsend_implies_not_committed
    (k: key)
    (know0: knowledge term)
    (s_q: TestedSystem.state term ideal_internal_state)
    (s_q': TestedSystem.state term ideal_internal_state)
    (session: session_id)
  : Lemma
    (requires (
      ideal_invariants s_q /\
      (forall t. Bag.mem t s_q.inputs ==> derivable s_q.know t) /\
      s_q.internal.sim_key == k /\
      eventually_observable_step (smd_ideal_system k know0) s_q
        [TestedSystem.Internal session; TestedSystem.Observable NetSend session] s_q'))
    (ensures not (PartialMap.contains s_q.internal.messages session))
  =
  // By contradiction: assume PartialMap.contains s_q.internal.messages session.
  // Then Internal session must be sim_receive (commit is blocked by contains).
  // sim_receive requires Bag.mem (Senc (SessionId session) k) s_q.inputs.
  // By inputs_are_derivable, this is derivable.
  // By ideal_invariant_cannot_derive_valid_response_before_send,
  // derivable Senc(SessionId session, k) implies session in sim_sent_sessions.
  // After sim_receive, sim_sent_sessions is unchanged.
  // sim_send requires not (Set.mem session sim_sent_sessions) → contradiction.
  FStar.Classical.move_requires (senc_not_in_inputs s_q) session;
  // senc_not_in_inputs gives: if session not in sim_sent, then Senc not in inputs.
  // But we need the contrapositive: if sim_receive fires → Senc in inputs → session in sim_sent → sim_send blocked.
  // Actually, we just need: if PartialMap.contains messages session, the Internal step is sim_receive,
  // which requires Senc in inputs, which requires session in sim_sent (from invariant),
  // which blocks sim_send.
  // This should follow by SMT from the invariants and transition definitions.
  ()

/// Helper: if an [Internal session; Observable IoSend session] eventually_observable_step
/// is possible, then messages contains session (so the Internal must be sim_receive).
private
let internal_iosend_implies_committed
    (k: key)
    (know0: knowledge term)
    (s_q: TestedSystem.state term ideal_internal_state)
    (s_q': TestedSystem.state term ideal_internal_state)
    (session: session_id)
  : Lemma
    (requires (
      ideal_invariants s_q /\
      (forall t. Bag.mem t s_q.inputs ==> derivable s_q.know t) /\
      s_q.internal.sim_key == k /\
      eventually_observable_step (smd_ideal_system k know0) s_q
        [TestedSystem.Internal session; TestedSystem.Observable IoSend session] s_q'))
    (ensures PartialMap.contains s_q.internal.messages session)
  =
  // If messages does not contain session, Internal must be commit.
  // After commit: ideal_to_sim_channel has SessionId session, sim_to_ideal_channel doesn't.
  // Observable IoSend = deliver requires sim_to_ideal_channel has SessionId session → blocked.
  // Contradiction.
  ()

private
let smd_obs_sim_ideal_impl_internal_observable
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (session: session_id)
    (eff: smd_effect)
    (session': session_id)
    (s_q': TestedSystem.state term ideal_internal_state)
  : Lemma
    (requires (
      let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable eff session'] in
      smd_bisim_relation k s_p s_q /\
      eventually_observable_step (smd_ideal_system k know0) s_q lbls s_q' /\
      smd_label_in_same_partition (TestedSystem.Internal session) (TestedSystem.Observable eff session')))
    (ensures (
      let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable eff session'] in
      exists lbls' s_p'.
        label_effects lbls' == label_effects lbls
        /\ eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p'
        /\ smd_bisim_relation k s_p' s_q')) =
  // session == session' from the partition constraint
  assert (session == session');
  let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable eff session] in
  // label_effects [Internal session; Observable eff session] == [Observable eff]
  assert (label_effects #term #smd_effect #session_id #adversary_senc lbls
    == [TestEquivalence.Observable eff])
    by (let open FStar.Tactics.V2 in norm [delta_only [`%label_effects; `%lbl_to_effect]; zeta; iota]; smt ());
  match eff with
  | NetSend ->
    let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable NetSend session] in
    // Establish characterization lemma preconditions
    internal_netsend_implies_not_committed k know0 s_q s_q' session;
    assert (forall l. List.memP l lbls ==>
      smd_label_in_same_partition l (TestedSystem.Observable NetSend session))
      by (let open FStar.Tactics.V2 in norm [delta_only [`%List.memP]; zeta; iota]; smt ());
    // Apply characterization lemma
    smd_ideal_eventually_observable_send_characterization k know0 s_q s_q' lbls session;
    // Now we have: smd_ideal_protocol_send_transition (s2p_state s_q) session t (s2p_state s_q')
    let t = Senc (SessionId session) k in
    // Use existing helper for single-step impl send
    smd_obs_bisim_observable_step_ideal_send k know0 s_p s_q session t s_q';
    // Lift to eventually_observable_step
    let lbls' : list system_label = [TestedSystem.Observable NetSend session] in
    assert (label_effects lbls' == [TestEquivalence.Observable NetSend])
      by (let open FStar.Tactics.V2 in norm [delta_only [`%label_effects; `%lbl_to_effect]; zeta; iota]; smt ());
    let p_sp (s_p': TestedSystem.state term impl_internal_state) : prop =
      (smd_impl_system k know0).transitions s_p (TestedSystem.Observable NetSend session) s_p' /\
      smd_bisim_relation k s_p' s_q'
    in
    assert (exists s_p'. p_sp s_p');
    let s_p' = FStar.IndefiniteDescription.indefinite_description_ghost _ p_sp in
    assert (eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p')
      by (let open FStar.Tactics.V2 in
          norm [delta_only [`%eventually_observable_step; `%is_eventually_observable; `%is_internal; `%lbl_to_effect; `%multi_transitions]; zeta; iota];
          smt ())
  | IoSend ->
    let lbls : list system_label = [TestedSystem.Internal session; TestedSystem.Observable IoSend session] in
    // Establish characterization lemma preconditions
    internal_iosend_implies_committed k know0 s_q s_q' session;
    assert (forall l. List.memP l lbls ==>
      smd_label_in_same_partition l (TestedSystem.Observable IoSend session))
      by (let open FStar.Tactics.V2 in norm [delta_only [`%List.memP]; zeta; iota]; smt ());
    // Apply characterization lemma
    smd_ideal_eventually_observable_receive_characterization k know0 s_q s_q' lbls session;
    // Now: exists message. smd_ideal_protocol_receive_transition ...
    let p_msg (message: term) : prop =
      smd_ideal_protocol_receive_transition (s2p_state s_q) session
        (Pair (SessionId session) message) (s2p_state s_q') /\
      s_q'.know == Seq.snoc s_q.know (Pair (SessionId session) message)
    in
    assert (exists message. p_msg message);
    let message = FStar.IndefiniteDescription.indefinite_description_ghost term p_msg in
    assert (p_msg message);
    // Use existing helper
    smd_obs_bisim_observable_step_ideal_recv k know0 s_p s_q session message s_q';
    let lbls' : list system_label = [TestedSystem.Observable IoSend session] in
    assert (label_effects lbls' == [TestEquivalence.Observable IoSend])
      by (let open FStar.Tactics.V2 in norm [delta_only [`%label_effects; `%lbl_to_effect]; zeta; iota]; smt ());
    let p_sp (s_p': TestedSystem.state term impl_internal_state) : prop =
      (smd_impl_system k know0).transitions s_p (TestedSystem.Observable IoSend session) s_p' /\
      smd_bisim_relation k s_p' s_q'
    in
    assert (exists s_p'. p_sp s_p');
    let s_p' = FStar.IndefiniteDescription.indefinite_description_ghost _ p_sp in
    assert (eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p')
      by (let open FStar.Tactics.V2 in
          norm [delta_only [`%eventually_observable_step; `%is_eventually_observable; `%is_internal; `%lbl_to_effect; `%multi_transitions]; zeta; iota];
          smt ());
    assert (smd_bisim_relation k s_p' s_q');
    ()

#pop-options

private
let smd_obs_sim_ideal_impl_instance
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (partition_l: system_label)
    (lbls: list system_label)
    (s_q': TestedSystem.state term ideal_internal_state)
  : Lemma
    (requires (
      smd_bisim_relation k s_p s_q /\
      lbls_in_partition lbls smd_partition partition_l /\
      eventually_observable_step (smd_ideal_system k know0) s_q lbls s_q'))
    (ensures (
      exists lbls' s_p'.
        label_effects lbls' == label_effects lbls
        /\ eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p'
        /\ smd_bisim_relation k s_p' s_q')) =
  match lbls with
  // Protocol transitions that are matched by implementation transitions.
  | [TestedSystem.Internal session; TestedSystem.Observable eff session'] ->
      assert (smd_label_in_same_partition (TestedSystem.Internal session) (TestedSystem.Observable eff session'));
      smd_obs_sim_ideal_impl_internal_observable k know0 s_p s_q session eff session' s_q'
  | [TestedSystem.Input d] ->
    let lbls' : list system_label = [TestedSystem.Input d] in
    assert (label_effects lbls' == label_effects lbls);
    smd_obs_bisim_input_step_ideal k know0 s_p s_q d s_q';
    assert (exists s_p'.
      (smd_impl_system k know0).transitions s_p (TestedSystem.Input d) s_p'
      /\ eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p'
      /\ smd_bisim_relation k s_p' s_q');
    ()
  // Trivial, no transition.
  | [] -> ()
  | [TestedSystem.Internal _] ->
      assert False by (
        let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step; `%is_eventually_observable]; zeta; iota];
        smt ()
      )
  // Any lbls reaching here have 1 or 3+ elements (the 2-element [Internal; Observable] case was handled above).
  // is_eventually_observable + partition constraint means: all elements are Internal(session) or Observable(eff, session).
  // The characterization lemmas prove lbls == [Internal; Observable], contradicting 1 or 3+ elements.
  | TestedSystem.Internal session :: _ ->
      // From smd_bisim_relation we get the characterization lemma preconditions
      assert (ideal_invariants s_q);
      assert (s_q.internal.sim_key == k);
      // ideal_invariant_inputs_are_derivable
      assert (forall t. Bag.mem t s_q.inputs ==> derivable s_q.know t);
      // All labels are in the same partition as (Internal session).
      // Since Internal s is in lbls, and lbls_in_partition says all are in same partition,
      // transitivity gives: all labels share the session.
      // smd_label_in_same_partition (Internal s) (Observable _ s) = True for any eff.
      if PartialMap.contains s_q.internal.messages session then begin
        assert (forall l. List.memP l lbls ==>
          smd_label_in_same_partition l (TestedSystem.Observable IoSend session));
        smd_ideal_eventually_observable_receive_characterization k know0 s_q s_q' lbls session
        // ensures: lbls == [Internal session; Observable IoSend session] — contradicts 3+ elements
      end else begin
        assert (forall l. List.memP l lbls ==>
          smd_label_in_same_partition l (TestedSystem.Observable NetSend session));
        smd_ideal_eventually_observable_send_characterization k know0 s_q s_q' lbls session
        // ensures: lbls == [Internal session; Observable NetSend session] — contradicts 3+ elements
      end
  // Unreachable: first element must be Internal (from is_eventually_observable with 2+ elements)
  | TestedSystem.Observable _ _ :: _ ->
      assert False by (
        let open FStar.Tactics.V2 in
        norm [delta_only [`%eventually_observable_step; `%is_eventually_observable]; zeta; iota];
        smt ()
      )

#push-options "--split_queries no --z3rlimit 20"

private
let smd_obs_sim_impl_ideal_move_requires
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (part_l: system_label)
    (lbls: list system_label)
    (s_p': TestedSystem.state term impl_internal_state)
  : Lemma
    (smd_bisim_relation k s_p s_q /\
     lbls_in_partition lbls smd_partition part_l /\
     eventually_observable_step (smd_impl_system k know0) s_p lbls s_p' ==>
     (exists (lbls': list system_label)
        (s_q': TestedSystem.state term ideal_internal_state).
        label_effects lbls' == label_effects lbls /\
        eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q' /\
        smd_bisim_relation k s_p' s_q')) =
  FStar.Classical.move_requires
    (smd_obs_sim_impl_ideal_instance k know0 s_p s_q part_l lbls) s_p'

private
let smd_obs_sim_impl_ideal (k: key) (know0: knowledge term)
    : Lemma
  (obs_sim_up_to_partitions (smd_impl_system k know0)
    (smd_ideal_system k know0)
        smd_partition
        (smd_bisim_relation k)) =
  introduce forall
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (part_l: system_label)
    (lbls: list system_label)
    (s_p': TestedSystem.state term impl_internal_state).
    smd_bisim_relation k s_p s_q /\
    lbls_in_partition lbls smd_partition part_l /\
    eventually_observable_step (smd_impl_system k know0) s_p lbls s_p' ==>
    (exists (lbls': list system_label)
       (s_q': TestedSystem.state term ideal_internal_state).
       label_effects lbls' == label_effects lbls /\
       eventually_observable_step (smd_ideal_system k know0) s_q lbls' s_q' /\
       smd_bisim_relation k s_p' s_q')
  with smd_obs_sim_impl_ideal_move_requires k know0 s_p s_q part_l lbls s_p'

private
let smd_obs_sim_ideal_impl_move_requires
    (k: key)
    (know0: knowledge term)
    (s_p: TestedSystem.state term impl_internal_state)
    (s_q: TestedSystem.state term ideal_internal_state)
    (part_l: system_label)
    (lbls: list system_label)
    (s_q': TestedSystem.state term ideal_internal_state)
  : Lemma
    (smd_bisim_relation k s_p s_q /\
     lbls_in_partition lbls smd_partition part_l /\
     eventually_observable_step (smd_ideal_system k know0) s_q lbls s_q' ==>
     (exists (lbls': list system_label)
        (s_p': TestedSystem.state term impl_internal_state).
        label_effects lbls' == label_effects lbls /\
        eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p' /\
        smd_bisim_relation k s_p' s_q')) =
  FStar.Classical.move_requires
    (smd_obs_sim_ideal_impl_instance k know0 s_p s_q part_l lbls) s_q'

private
let smd_obs_sim_ideal_impl (k: key) (know0: knowledge term)
    : Lemma
  (obs_sim_up_to_partitions (smd_ideal_system k know0)
    (smd_impl_system k know0)
        smd_partition
        (fun s_q s_p -> smd_bisim_relation k s_p s_q)) =
  introduce forall
    (s_q: TestedSystem.state term ideal_internal_state)
    (s_p: TestedSystem.state term impl_internal_state)
    (part_l: system_label)
    (lbls: list system_label)
    (s_q': TestedSystem.state term ideal_internal_state).
    (fun s_q s_p -> smd_bisim_relation k s_p s_q) s_q s_p /\
    lbls_in_partition lbls smd_partition part_l /\
    eventually_observable_step (smd_ideal_system k know0) s_q lbls s_q' ==>
    (exists (lbls': list system_label)
       (s_p': TestedSystem.state term impl_internal_state).
       label_effects lbls' == label_effects lbls /\
       eventually_observable_step (smd_impl_system k know0) s_p lbls' s_p' /\
       (fun s_q s_p -> smd_bisim_relation k s_p s_q) s_q' s_p')
  with smd_obs_sim_ideal_impl_move_requires k know0 s_p s_q part_l lbls s_q'

#pop-options

#push-options "--split_queries no --z3rlimit 20"

private
let smd_obs_bisim (k: key) (know0: knowledge term)
    : Lemma
  (obs_bisim_up_to_partitions (smd_impl_system k know0)
    (smd_ideal_system k know0)
        smd_partition
        smd_partition
        (smd_bisim_relation k)) =
  smd_obs_sim_impl_ideal k know0;
  smd_obs_sim_ideal_impl k know0;
  norm_spec [delta_only [`%obs_bisim_up_to_partitions]]
    (obs_bisim_up_to_partitions (smd_impl_system k know0)
      (smd_ideal_system k know0)
          smd_partition
          smd_partition
          (smd_bisim_relation k))

#pop-options



/// =========================================================================
/// Main theorem: SMD implementation and ideal are T-equivalent
/// =========================================================================

let smd_t_equivalence k know0 =
  smd_right_movable_impl k know0;
  smd_right_movable_ideal k know0;
  smd_init_related k know0;
  smd_static_equiv_from_rel k;
  smd_obs_bisim k know0;
  // The lemma composes the protocols with the adversary via `TestedSystem.system`
  // (matching `smd_impl_system` / `smd_ideal_system`), so transition validity
  // holds by construction and need not be supplied here.
  obs_bisim_up_to_partitions_implies_t_equivalence know0
    (smd_impl_protocol k)
    (smd_ideal_protocol k)
    smd_partition
    smd_partition
    (smd_bisim_relation k)

#pop-options
