module SMD.ObservationalBisimulation.Relation

open Adversary
open AdversarySenc
open SencTerms
open StaticEquivalence
open TestedSystem
open SMD.Adversary
open SMD.Ideal
open SMD.IdealInvariants
open SMD.Implementation
open SMD.ImplementationInvariants
open SMD.TestedProtocols

open SMD.Bijection

module Option = FStar.Option
module PartialMap = FStar.PartialMap.Ext
module Set = FStar.Set

let send_equivalent_transitions_enabled_iff
  (impl: Protocol.state term impl_internal_state)
  (ideal: Protocol.state term ideal_internal_state)
  : prop
= forall (session: session_id) (message: term).
    (smd_impl_protocol_send_enabled impl session message impl.internal.key <==>
      smd_ideal_protocol_send_enabled ideal session
        (smd_bi_subst message impl.internal.messages impl.internal.key ideal.internal.sim_key))

let send_equivalent_transitions_completed_iff
  (impl: Protocol.state term impl_internal_state)
  (ideal: Protocol.state term ideal_internal_state)
  : prop
= forall (session: session_id).
    (Set.mem session impl.internal.sent_sessions <==> Set.mem session ideal.internal.sim_sent_sessions)

let receive_equivalent_transitions_enabled_iff
  (impl: Protocol.state term impl_internal_state)
  (ideal: Protocol.state term ideal_internal_state)
  : prop
= forall (session: session_id) (message: term).
    (smd_impl_protocol_receive_enabled impl session message <==>
      smd_ideal_protocol_receive_enabled ideal session
        (smd_bi_subst message impl.internal.messages impl.internal.key ideal.internal.sim_key))

let receive_equivalent_transitions_completed_iff
  (impl: Protocol.state term impl_internal_state)
  (ideal: Protocol.state term ideal_internal_state)
  : prop
= forall (session: session_id).
    (Set.mem session impl.internal.received_sessions <==> Set.mem session ideal.internal.sim_received_sessions)

let valid_encrypted_responses_indistinguishable_from_stored_ideal_messages
      (impl: impl_system_state)
      (ideal: ideal_system_state)
    : prop =
  forall (session: session_id)
    (impl_message: term)
    (ideal_message: term)
    (d: adv.derivation)
    (derived_term: term).
    let valid_impl_response = Senc (Pair (SessionId session) impl_message) impl.internal.key in
    adv.derive d impl.know = Some derived_term /\ in_term derived_term valid_impl_response /\
    PartialMap.sel ideal.internal.messages session = Some ideal_message ==>
    indistinguishable impl_message ideal_message

let to_be_delivered_messages_already_derivable_by_same_derivation
      (impl: impl_system_state)
      (ideal: ideal_system_state)
    : prop =
  forall (session: session_id)
    (impl_message: term)
    (ideal_message: term)
    (d: derivation)
    (derived_impl: term)
    (derived_ideal: term).
    let impl_session_message_pair = Pair (SessionId session) impl_message in
    let impl_valid_response = Senc impl_session_message_pair impl.internal.key in
    let ideal_valid_response = Senc (SessionId session) ideal.internal.sim_key in
    adv.derive d impl.know = Some derived_impl /\
    adv.derive d ideal.know = Some derived_ideal /\ in_term derived_impl impl_valid_response /\
    in_term derived_ideal ideal_valid_response /\
    PartialMap.sel ideal.internal.messages session = Some ideal_message ==>
    (exists trigger_derivation.
      adv.derive trigger_derivation impl.know = Some impl_session_message_pair /\
        adv.derive trigger_derivation ideal.know =
        Some (Pair (SessionId session) ideal_message))

/// Lifted bisimulation relation over TestedSystem states.
///
/// Combines the algebraic observational_bisimulation_relation with additional
/// conditions on the inputs bag correspondence needed to bridge to the
/// typeclass framework.

let smd_bisim_relation
      (k: key)
      (s_impl: TestedSystem.state term impl_internal_state)
      (s_ideal: TestedSystem.state term ideal_internal_state)
    : prop =
  statically_equivalent adv s_impl.know s_ideal.know /\
  implementation_invariants s_impl /\
  ideal_invariants s_ideal /\ s_impl.internal.key == k /\
  s_ideal.internal.sim_key == k /\
  send_equivalent_transitions_enabled_iff (s2p_state s_impl) (s2p_state s_ideal) /\
  send_equivalent_transitions_completed_iff (s2p_state s_impl) (s2p_state s_ideal) /\
  receive_equivalent_transitions_enabled_iff (s2p_state s_impl) (s2p_state s_ideal) /\
  receive_equivalent_transitions_completed_iff (s2p_state s_impl) (s2p_state s_ideal) /\
  valid_encrypted_responses_indistinguishable_from_stored_ideal_messages s_impl
    s_ideal /\
  to_be_delivered_messages_already_derivable_by_same_derivation s_impl
    s_ideal /\
  StaticEquivalence.bijective_correspondence_on_derivations
    adv
    s_impl.know
    s_ideal.know
    (SMD.Bijection.smd_subst_bijection k k s_impl.internal.messages) /\
  // Correspondence on the inputs bag: each term injected into the impl inputs
  // bag has a counterpart in the ideal inputs bag related by the same
  // substitution used for derivable terms, and vice versa.
  (forall t.
      Bag.count s_impl.inputs t ==
      Bag.count s_ideal.inputs ((SMD.Bijection.smd_subst_bijection k k s_impl.internal.messages).cright t)) /\
  // Messages correspondence: the ideal messages map is pointwise the
  // smd_bi_subst of the impl messages map.  This is maintained because both
  // sides consume corresponding adversary-derived triggers through the
  // substitution bijection.  Using smd_bi_subst (the self-inverse bijection
  // function) keeps the correspondence compatible with the bag correspondence
  // and injectivity arguments.
  (forall (session: session_id).
      PartialMap.sel s_ideal.internal.messages session ==
      Option.mapTot
        (fun m -> SMD.Bijection.smd_bi_subst m s_impl.internal.messages k k)
        (PartialMap.sel s_impl.internal.messages session)) /\
  // Canonical-form invariant for ideal derivable terms: no impl-form Senc
  // subterm `Senc(Pair(SessionId _) _) k` can appear.  Initially true
  // (from smd_t_equivalence preconditions on know0) and preserved by each
  // transition (ideal protocol emits only canonical_ideal terms, and
  // derivations from canonical_ideal knowledge stay canonical_ideal since
  // the adversary cannot derive the secret key).
  (forall (d: adv.derivation) (t: term).
      adv.derive d s_ideal.know = Some t ==> SMD.Bijection.canonical_ideal t k) /\
  // Canonical-form invariant for impl derivable terms: no ideal-form Senc
  // subterm `Senc(SessionId _) k` can appear.  Initially true (from the
  // smd_init_related preconditions on know0) and preserved by each
  // transition (impl protocol emits only `Senc(Pair(SessionId _) _) k` or
  // `Pair(SessionId _) _` terms, neither of which introduces an ideal-form
  // Senc subterm; adversary derivations cannot forge them since the
  // secret key is not derivable).  Used to discharge condition 5 of
  // `bijective_correspondence_preserved_by_additional_message_in_map`.
  (forall (d: adv.derivation) (t: term) (i: session_id).
      adv.derive d s_impl.know = Some t ==> in_term t (Senc (SessionId i) k) == false)
