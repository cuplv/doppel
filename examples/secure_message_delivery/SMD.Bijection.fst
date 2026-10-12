module SMD.Bijection

open AdversarySenc
open FStar.Bijection

// =============================================================================
// Self-inverse lemma for smd_bi_subst.
//
// The key invariant that makes `smd_bi_subst` a valid bijection right/left
// for `FStar.Bijection.bijection term term`: applied twice, it is the
// identity on every term.
// =============================================================================

private let rec smd_bi_subst_self_inverse
      (t: term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
    : Lemma
      (ensures
         smd_bi_subst (smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key)
                      session_to_term_map impl_secret_key ideal_secret_key
         == t)
      (decreases t) =
  match t with
  | Bool _ | SessionId _ | Data _ | Key _ -> ()
  | Pair t1 t2 ->
    smd_bi_subst_self_inverse t1 session_to_term_map impl_secret_key ideal_secret_key;
    smd_bi_subst_self_inverse t2 session_to_term_map impl_secret_key ideal_secret_key
  | Senc m k ->
    smd_bi_subst_self_inverse m session_to_term_map impl_secret_key ideal_secret_key


// =============================================================================
// The bijection: right = left = smd_bi_subst.
// =============================================================================

let smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map =
  let subst : term -> term = fun t ->
    smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key
  in
  let inv (x: term) : squash (subst (subst x) == x) =
    smd_bi_subst_self_inverse x session_to_term_map impl_secret_key ideal_secret_key
  in
  FStar.Bijection.mk_cbij subst subst inv inv

let smd_subst_bijection_right impl_secret_key ideal_secret_key session_to_term_map t = ()

let smd_subst_bijection_left impl_secret_key ideal_secret_key session_to_term_map t = ()


// =============================================================================
// Indistinguishability: smd_bi_subst produces indistinguishable terms.
// =============================================================================

private let rec smd_bi_subst_indistinguishable_term
      (t: term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
    : Lemma
      (ensures indistinguishable t
         (smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key))
      (decreases t) =
  match t with
  | Bool _ | SessionId _ | Data _ | Key _ -> ()
  | Pair t1 t2 ->
    smd_bi_subst_indistinguishable_term t1 session_to_term_map impl_secret_key ideal_secret_key;
    smd_bi_subst_indistinguishable_term t2 session_to_term_map impl_secret_key ideal_secret_key
  | Senc _ _ ->
    // Both sides are `Senc _ _`; `indistinguishable` is trivially True on Senc.
    ()

let smd_subst_bijection_maps_to_indistinguishable_terms impl_secret_key ideal_secret_key session_to_term_map =
  let bij = smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map in
  let helper (t: term)
      : Lemma (adv.indistinguishable t (bij.cright t)) =
    smd_bi_subst_indistinguishable_term t session_to_term_map impl_secret_key ideal_secret_key
  in
  FStar.Classical.forall_intro helper


// =============================================================================
// Equal lengths follow from bijective correspondence + indistinguishability.
// =============================================================================

private let static_equiv_equal_length (impl_knowledge ideal_knowledge: knowledge term)
    : Lemma (requires statically_equivalent adv impl_knowledge ideal_knowledge)
      (ensures Seq.length impl_knowledge = Seq.length ideal_knowledge) =
  let n = Seq.length impl_knowledge in
  let n_ideal = Seq.length ideal_knowledge in
  (if n < n_ideal then (
    assert (adv.derive (DeriveObserved n) impl_knowledge = None);
    assert (adv.derive (DeriveObserved n) ideal_knowledge = Some (Seq.index ideal_knowledge n));
    assert (indistinguishable' adv.indistinguishable
      (adv.derive (DeriveObserved n) impl_knowledge)
      (adv.derive (DeriveObserved n) ideal_knowledge));
    assert False
  ) else ());
  (if n_ideal < n then (
    assert (adv.derive (DeriveObserved n_ideal) ideal_knowledge = None);
    assert (adv.derive (DeriveObserved n_ideal) impl_knowledge = Some (Seq.index impl_knowledge n_ideal));
    assert (indistinguishable' adv.indistinguishable
      (adv.derive (DeriveObserved n_ideal) impl_knowledge)
      (adv.derive (DeriveObserved n_ideal) ideal_knowledge));
    assert False
  ) else ());
  assert (n = n_ideal)


// =============================================================================
// bc_helper: bijective-correspondence inductive helper.
//
// Ensures, for each derivation d, that the ideal derivation result equals
// `smd_bi_subst` of the impl derivation result.  With the self-inverse
// bijection, this is exactly `Option.mapTot bij.cright`.
// =============================================================================

/// Ensures: one conjunct in smd_bi_subst form, which matches
/// `bijective_correspondence_on_derivations` after SMT pattern rewrite.
private let bc_ens
      (impl_extended ideal_extended: knowledge term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
      (d: adv.derivation)
    : prop =
  adv.derive d ideal_extended =
    Option.mapTot
      (fun t -> smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key)
      (adv.derive d impl_extended)

/// Shared precondition for all _bc_* helper lemmas
private let bc_req
      (impl_knowledge ideal_knowledge: knowledge term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
      (session: session_id)
      (message: term)
    : prop =
  ~(derivable impl_knowledge (Key impl_secret_key)) /\
  ~(derivable ideal_knowledge (Key ideal_secret_key)) /\
  PartialMap.sel session_to_term_map session == Some message

/// Separate lemma for the DeriveSEncrypt arm, with IH as requires
private let bc_SEncrypt
      (impl_knowledge ideal_knowledge: knowledge term)
      (impl_extended ideal_extended: knowledge term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
      (session: session_id)
      (message: term)
      (pt_d key_d: adv.derivation)
    : Lemma
      (requires
        bc_req impl_knowledge ideal_knowledge session_to_term_map impl_secret_key ideal_secret_key session message /\
        impl_extended = Seq.snoc impl_knowledge (Senc (Pair (SessionId session) message) impl_secret_key) /\
        ideal_extended = Seq.snoc ideal_knowledge (Senc (SessionId session) ideal_secret_key) /\
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key pt_d /\
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key key_d)
      (ensures
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key (DeriveSEncrypt pt_d key_d)) =
  (match adv.derive pt_d impl_extended, adv.derive key_d impl_extended with
   | Some plaintext, Some (Key k) ->
     keys_learned_from_ciphertext_already_derivable impl_knowledge
       (Pair (SessionId session) message) impl_secret_key k (key_d <: derivation);
     assert (k <> impl_secret_key);
     keys_learned_from_ciphertext_already_derivable ideal_knowledge
       (SessionId session) ideal_secret_key k (key_d <: derivation);
     assert (k <> ideal_secret_key)
   | _ -> (
    assert (adv.derive (DeriveSEncrypt pt_d key_d) impl_extended = None);
    assert (adv.derive (DeriveSEncrypt pt_d key_d) ideal_extended = None)
   ))

/// Separate lemma for the DeriveSDecrypt arm, with IH as requires
private let bc_SDecrypt
      (impl_knowledge ideal_knowledge: knowledge term)
      (impl_extended ideal_extended: knowledge term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
      (session: session_id)
      (message: term)
      (ct_d key_d: adv.derivation)
    : Lemma
      (requires
        bc_req impl_knowledge ideal_knowledge session_to_term_map impl_secret_key ideal_secret_key session message /\
        impl_extended = Seq.snoc impl_knowledge (Senc (Pair (SessionId session) message) impl_secret_key) /\
        ideal_extended = Seq.snoc ideal_knowledge (Senc (SessionId session) ideal_secret_key) /\
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key ct_d /\
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key key_d)
      (ensures
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key (DeriveSDecrypt ct_d key_d)) =
  (match adv.derive ct_d impl_extended, adv.derive key_d impl_extended with
   | Some (Senc plaintext k1), Some (Key k2) ->
     // From impl side: k2 was derivable without impl_secret_key → k2 ≠ impl_secret_key
     keys_learned_from_ciphertext_already_derivable impl_knowledge
       (Pair (SessionId session) message) impl_secret_key k2 (key_d <: derivation);
     assert (k2 <> impl_secret_key);
     // From ideal side: k2 was derivable without ideal_secret_key → k2 ≠ ideal_secret_key
     keys_learned_from_ciphertext_already_derivable ideal_knowledge
       (SessionId session) ideal_secret_key k2 (key_d <: derivation);
     assert (k2 <> ideal_secret_key);
     let subst_f = fun t -> smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key in
     // Ideal-side ciphertext = smd_bi_subst (Senc plaintext k1).  Because k1 is
     // the encryption key, if k1 = impl_secret_key or k1 = ideal_secret_key the
     // smd_bi_subst-image may carry a different outer key, but decryption with
     // k2 ≠ impl_k and k2 ≠ ideal_k then fails on both sides.
     assert (adv.derive ct_d ideal_extended = Some (subst_f (Senc plaintext k1)));
     if k1 = k2 then (
       // k2 ≠ impl_secret_key and k2 ≠ ideal_secret_key so k1 ≠ impl/ideal.
       // In that case smd_bi_subst (Senc plaintext k1) = Senc (smd_bi_subst plaintext) k1.
       let k = k1 in
       let pt' = subst_f plaintext in
       assert (adv.derive ct_d ideal_extended = Some (Senc pt' k));
       assert (adv.derive (DeriveSDecrypt ct_d key_d) ideal_extended = Some pt');
       assert (adv.derive (DeriveSDecrypt ct_d key_d) impl_extended = Some plaintext)
     ) else (
       // k1 ≠ k2: impl decryption fails.  On the ideal side, the ciphertext is
       // `smd_bi_subst (Senc plaintext k1)`.  Its outer key is either k1 (if
       // smd_bi_subst did not reshape it) or ideal_secret_key (after collapse)
       // or impl_secret_key (after expansion).  In all cases, since k2 ≠
       // impl_k and k2 ≠ ideal_k, decryption with k2 still fails.
       assert (adv.derive (DeriveSDecrypt ct_d key_d) impl_extended = None);
       assert (adv.derive (DeriveSDecrypt ct_d key_d) ideal_extended = None)
     )
   | _ -> ())

/// Main recursive helper — inductive dispatcher.
#push-options "--split_queries always"
private let rec bc_helper
      (impl_knowledge ideal_knowledge: knowledge term)
      (impl_extended ideal_extended: knowledge term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
      (session: session_id)
      (message: term)
      (n: nat)
      (d: adv.derivation)
    : Lemma
      (requires
        bijective_correspondence_on_derivations adv impl_knowledge ideal_knowledge
          (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map) /\
        bc_req impl_knowledge ideal_knowledge session_to_term_map impl_secret_key ideal_secret_key session message /\
        impl_extended = Seq.snoc impl_knowledge (Senc (Pair (SessionId session) message) impl_secret_key) /\
        ideal_extended = Seq.snoc ideal_knowledge (Senc (SessionId session) ideal_secret_key) /\
        n = Seq.length impl_knowledge /\
        n = Seq.length ideal_knowledge)
      (ensures
        bc_ens impl_extended ideal_extended session_to_term_map impl_secret_key ideal_secret_key d)
      (decreases (d <: derivation)) =
  let impl_senc = Senc (Pair (SessionId session) message) impl_secret_key in
  let ideal_senc = Senc (SessionId session) ideal_secret_key in
  match (d <: derivation) with
  | DeriveObserved i ->
    if i < n then (
      append_preserves_derive d impl_knowledge (Seq.create 1 impl_senc);
      append_preserves_derive d ideal_knowledge (Seq.create 1 ideal_senc);
      // Bijective correspondence hypothesis is exactly bc_ens on original knowledges.
      ()
    ) else if i = n then (
      // Observing the newly added senc: confirm smd_bi_subst collapses it to
      // the ideal form (requires map[session] = Some message from bc_req).
      assert (adv.derive d impl_extended = Some impl_senc);
      assert (adv.derive d ideal_extended = Some ideal_senc);
      // smd_bi_subst on Senc (Pair (SessionId session) message) impl_k with
      // map[session] = Some message collapses to Senc (SessionId session) ideal_k.
      assert (smd_bi_subst impl_senc session_to_term_map impl_secret_key ideal_secret_key = ideal_senc)
    ) else (
      assert (adv.derive d impl_extended = None);
      assert (adv.derive d ideal_extended = None)
    )
  | DeriveSEncrypt pt_d key_d ->
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n pt_d;
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n key_d;
    bc_SEncrypt impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message pt_d key_d
  | DeriveSDecrypt ct_d key_d ->
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n ct_d;
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n key_d;
    bc_SDecrypt impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message ct_d key_d
  | DerivePair l_d r_d ->
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n l_d;
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n r_d
  | DerivePairLeft p_d ->
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n p_d
  | DerivePairRight p_d ->
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n p_d
#pop-options

let bijective_correspondence_preserved_learning_secret_encrypted_response
  impl_knowledge ideal_knowledge session_to_term_map impl_secret_key ideal_secret_key session message =
  let bij = smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map in
  let impl_senc = Senc (Pair (SessionId session) message) impl_secret_key in
  let ideal_senc = Senc (SessionId session) ideal_secret_key in
  let impl_extended = Seq.snoc impl_knowledge impl_senc in
  let ideal_extended = Seq.snoc ideal_knowledge ideal_senc in
  smd_subst_bijection_maps_to_indistinguishable_terms impl_secret_key ideal_secret_key session_to_term_map;
  bijective_correspondence_implies_static_equivalence adv impl_knowledge ideal_knowledge bij;
  static_equiv_equal_length impl_knowledge ideal_knowledge;
  let n = Seq.length impl_knowledge in
  let helper (d: adv.derivation) : Lemma (
    adv.derive d ideal_extended = Option.mapTot bij.cright (adv.derive d impl_extended)
  ) =
    bc_helper impl_knowledge ideal_knowledge impl_extended ideal_extended session_to_term_map
      impl_secret_key ideal_secret_key session message n d
    // bc_helper establishes bc_ens which says
    //   adv.derive d ideal_extended = Option.mapTot smd_bi_subst (adv.derive d impl_extended)
    // The SMTPat for smd_subst_bijection_right connects bij.cright with smd_bi_subst.
  in
  FStar.Classical.forall_intro helper


// =============================================================================
// Map-irrelevance: smd_bi_subst is unchanged when updating the map at a
// session whose ideal-form `Senc (SessionId session) ideal_k` is absent.
// =============================================================================

let rec smd_bi_subst_preserved_by_irrelevant_update
    (t: term)
    (session_to_term_map: PartialMap.t session_id term)
    (impl_secret_key ideal_secret_key: key)
    (session: session_id)
    (impl_message: term)
  : Lemma
    (requires
      // The session was not previously in the map, so the update is the only
      // change.  This matches the precondition in
      // `bijective_correspondence_preserved_by_additional_message_in_map`.
      ~(PartialMap.contains session_to_term_map session) /\
      in_term t (Senc (SessionId session) ideal_secret_key) == false /\
      // No prior impl-form collapse at this session: the new map entry
      // `Some impl_message` would newly trigger a collapse on
      // `Senc (Pair (SessionId session) impl_message) impl_k` subterms.
      in_term t (Senc (Pair (SessionId session) impl_message) impl_secret_key) == false)
    (ensures
      smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key =
      smd_bi_subst t (PartialMap.upd session_to_term_map session impl_message) impl_secret_key ideal_secret_key)
    (decreases t)
  =
  let map' = PartialMap.upd session_to_term_map session impl_message in
  match t with
  | Senc m k ->
    smd_bi_subst_preserved_by_irrelevant_update m session_to_term_map impl_secret_key ideal_secret_key session impl_message;
    // The body-level recursion handles the body; now we must show the outer
    // Senc-level rewrite agrees between the two maps.  The two maps differ
    // only at `session` (None vs Some impl_message).  Case analysis on the
    // shape of `m`:
    (match m with
     | Pair (SessionId i) message ->
       // Only relevant when k = impl_secret_key.  The collapse condition
       // requires map[i] = Some message.  Both maps agree at `i <> session`.
       // If `i = session`: old map has None (collapse ⇒ identity), new map has
       // Some impl_message (collapse ⇒ only if message = impl_message; but
       // that's excluded by the in_term precondition).
       assert (i = session ==> PartialMap.sel session_to_term_map i = None);
       assert (i = session ==> message <> impl_message \/ k <> impl_secret_key)
     | SessionId i ->
       // Collapse condition requires map[i] = Some mapped.  Old map None, new
       // map: if i = session then Some impl_message else unchanged.
       // `i = session` is excluded by the ideal-form in_term precondition
       // when k = ideal_secret_key.
       assert (i = session ==> PartialMap.sel session_to_term_map i = None);
       assert (k = ideal_secret_key /\ i = session ==>
               t = Senc (SessionId session) ideal_secret_key)
     | _ -> ())
  | Pair t1 t2 ->
    smd_bi_subst_preserved_by_irrelevant_update t1 session_to_term_map impl_secret_key ideal_secret_key session impl_message;
    smd_bi_subst_preserved_by_irrelevant_update t2 session_to_term_map impl_secret_key ideal_secret_key session impl_message
  | Bool _ | SessionId _ | Data _ | Key _ -> ()


let bijective_correspondence_preserved_by_additional_message_in_map
    impl_knowledge
    ideal_knowledge
    session_to_term_map
    impl_secret_key
    ideal_secret_key
    session
    impl_message
=
  let session_to_term_map' = PartialMap.upd session_to_term_map session impl_message in
  let bij_new = smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map' in
  let helper (d: adv.derivation) : Lemma (
    adv.derive d ideal_knowledge = Option.mapTot bij_new.cright (adv.derive d impl_knowledge)
  ) =
    match adv.derive d impl_knowledge with
    | None -> ()
    | Some impl_t ->
      // From the preconditions, impl_t lacks both the ideal-form at `session`
      // and the impl-form at `session` for `impl_message`.  Applying the
      // map-irrelevance lemma yields that `smd_bi_subst` on impl_t is the
      // same under the old and new maps.
      smd_bi_subst_preserved_by_irrelevant_update
        impl_t session_to_term_map impl_secret_key ideal_secret_key session impl_message
  in
  FStar.Classical.forall_intro helper


private let bijective_correspondence_implies_equal_lengths
  (impl_knowledge ideal_knowledge: knowledge term)
  (session_to_term_map: PartialMap.t session_id term)
  (impl_secret_key ideal_secret_key: key)
  : Lemma
    (requires (
      bijective_correspondence_on_derivations adv impl_knowledge ideal_knowledge
        (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map)))
    (ensures Seq.length impl_knowledge = Seq.length ideal_knowledge) =
  let bij = smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map in
  smd_subst_bijection_maps_to_indistinguishable_terms impl_secret_key ideal_secret_key session_to_term_map;
  bijective_correspondence_implies_static_equivalence adv impl_knowledge ideal_knowledge bij;
  static_equiv_equal_length impl_knowledge ideal_knowledge

let bijective_correspondence_preserved_by_derivable_messages
    impl_knowledge
    ideal_knowledge
    session_to_term_map
    impl_secret_key
    ideal_secret_key
    d
=
  let bij = smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map in
  let impl_t = Some?.v (adv.derive d impl_knowledge) in
  let ideal_t = Some?.v (adv.derive d ideal_knowledge) in
  let n = Seq.length impl_knowledge in
  let n_ideal = Seq.length ideal_knowledge in
  bijective_correspondence_implies_equal_lengths impl_knowledge ideal_knowledge session_to_term_map impl_secret_key ideal_secret_key;
  assert (n = n_ideal);
  let helper (d': adv.derivation) : Lemma (
    adv.derive d' (Seq.snoc ideal_knowledge ideal_t) = Option.mapTot bij.cright (adv.derive d' (Seq.snoc impl_knowledge impl_t))
  ) =
    replace_observed_derivation_eq impl_knowledge impl_t d d';
    replace_observed_derivation_eq ideal_knowledge ideal_t d d';
    let d_r = replace_observed_derivation n d d' in
    assert (adv.derive d' (Seq.snoc impl_knowledge impl_t) = adv.derive d_r impl_knowledge);
    assert (adv.derive d' (Seq.snoc ideal_knowledge ideal_t) = adv.derive d_r ideal_knowledge);
    assert (adv.derive d_r ideal_knowledge = Option.mapTot bij.cright (adv.derive d_r impl_knowledge))
  in
  FStar.Classical.forall_intro helper
