module SMD.Bijection

open Adversary
open AdversarySenc
open FStar.Bijection
open SencTerms
open StaticEquivalence
open SymbolicTypes
open SMD.Adversary

(**
  Self-inverse substitution function used for both directions of the
  `smd_subst_bijection`.  It collapses `Senc (Pair (SessionId i) m) impl_k`
  to `Senc (SessionId i) ideal_k` exactly when `map[i] = Some m`, and
  expands `Senc (SessionId i) ideal_k` to `Senc (Pair (SessionId i) m) impl_k`
  when `map[i] = Some m`.  For every other term it recurses through `Pair`
  and unmatched `Senc` bodies, leaving the structure unchanged.  Being
  unconditionally self-inverse on every term is what `FStar.Bijection`
  requires for the `right` and `left` round-trip proofs.
*)
let rec smd_bi_subst
      (t: term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
    : term =
  match t with
  | Bool _ | SessionId _ | Data _ | Key _ -> t
  | Pair t1 t2 ->
    Pair (smd_bi_subst t1 session_to_term_map impl_secret_key ideal_secret_key)
         (smd_bi_subst t2 session_to_term_map impl_secret_key ideal_secret_key)
  // Substitute terms of the form `Senc (i, m) impl_k` <-> `Senc i ideal_k`, but
  // only when `m` is the message stored by the `session_to_term_map` for
  // session `i`. This ensures the substitution is self-inverse, and is
  // therefore bijective.
  | Senc m k ->
    if k = impl_secret_key then
      (match m with
       | Pair (SessionId i) message ->
         (match PartialMap.sel session_to_term_map i with
          | Some mapped ->
            if mapped = message
            then Senc (SessionId i) ideal_secret_key
            else t
          | None -> t)
       | SessionId i ->
         // Only reachable when impl_k = ideal_k; handle canonical ideal-form.
         if k = ideal_secret_key
         then
           (match PartialMap.sel session_to_term_map i with
            | Some mapped -> Senc (Pair (SessionId i) mapped) impl_secret_key
            | None -> t)
         else Senc (smd_bi_subst m session_to_term_map impl_secret_key ideal_secret_key) k
       | _ -> Senc (smd_bi_subst m session_to_term_map impl_secret_key ideal_secret_key) k)
    else if k = ideal_secret_key then
      (match m with
       | SessionId i ->
         (match PartialMap.sel session_to_term_map i with
          | Some mapped -> Senc (Pair (SessionId i) mapped) impl_secret_key
          | None -> t)
       | _ -> Senc (smd_bi_subst m session_to_term_map impl_secret_key ideal_secret_key) k)
    else Senc (smd_bi_subst m session_to_term_map impl_secret_key ideal_secret_key) k

(**
  Predicate capturing that every `Senc` subterm of `t` is "ideal-world
  canonical":
    - No `Senc (Pair (SessionId i) m) impl_k` subterm occurs.
    - Other subterms recurse canonically.

  Derivable ideal-world terms satisfy this.
*)
let rec canonical_ideal
      (t: term)
      (impl_secret_key: key)
    : bool =
  match t with
  | Bool _ | SessionId _ | Data _ | Key _ -> true
  | Pair t1 t2 ->
    canonical_ideal t1 impl_secret_key &&
    canonical_ideal t2 impl_secret_key
  | Senc m k ->
    let rec_body = canonical_ideal m impl_secret_key in
    if k = impl_secret_key then
      (match m with
       | Pair (SessionId _) _ -> false
       | _ -> rec_body)
    else rec_body

(**
  The bijection between impl and ideal terms, parameterized by the secret keys
  and the session-to-message map.  Both `right` and `left` use the
  self-inverse `smd_bi_subst`.
*)
val smd_subst_bijection
    (impl_secret_key ideal_secret_key: key)
    (session_to_term_map: PartialMap.t session_id term)
    : cbij term term

(** The executable right component equals `smd_bi_subst`. *)
val smd_subst_bijection_right
    (impl_secret_key ideal_secret_key: key)
    (session_to_term_map: PartialMap.t session_id term)
    (t: term)
    : Lemma
      ((smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map).cright t
       == smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key)
      [SMTPat ((smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map).cright t)]

(** The executable left component equals `smd_bi_subst` (the function is self-inverse). *)
val smd_subst_bijection_left
    (impl_secret_key ideal_secret_key: key)
    (session_to_term_map: PartialMap.t session_id term)
    (t: term)
    : Lemma
      ((smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map).cleft t
       == smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key)
      [SMTPat ((smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map).cleft t)]

val smd_subst_bijection_maps_to_indistinguishable_terms
    (impl_secret_key ideal_secret_key: key)
    (session_to_term_map: PartialMap.t session_id term)
    : Lemma
      (ensures bijection_maps_to_indistinguishable_terms adv
         (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map))

(**
  Observing new encrypted responses, that the adversary cannot decrypt,
  preserves the bijective correspondence between the Impl and Ideal worlds.
*)
val bijective_correspondence_preserved_learning_secret_encrypted_response
      (impl_knowledge ideal_knowledge: knowledge term)
      (session_to_term_map: PartialMap.t session_id term)
      (impl_secret_key ideal_secret_key: key)
      (session: session_id)
      (impl_message: term)
    : Lemma
      (requires (
        bijective_correspondence_on_derivations adv impl_knowledge ideal_knowledge
          (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map)
        // The message being learned in the Impl world must be consistent with the map
        /\ PartialMap.sel session_to_term_map session == Some impl_message
        // And the adversary must not already be able to derive the secret keys in either world
        /\ ~(adv.derivable impl_knowledge (Key impl_secret_key))
        /\ ~(adv.derivable ideal_knowledge (Key ideal_secret_key))
      ))
      (ensures (
        let impl_senc = Senc (Pair (SessionId session) impl_message) impl_secret_key in
        let ideal_senc = Senc (SessionId session) ideal_secret_key in
        bijective_correspondence_on_derivations
          adv
          (Seq.snoc impl_knowledge impl_senc)
          (Seq.snoc ideal_knowledge ideal_senc)
          (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map)
      ))

(**
  Map-irrelevance lemma: extending the map at a fresh `session` (where the
  ideal-form `Senc(SessionId session) ideal_k` and impl-form
  `Senc(Pair(SessionId session) impl_message) impl_k` are absent from `t`)
  does not change the result of `smd_bi_subst`.  Useful for proving that
  derivable terms keep the same image under the bijection after a send
  transition extends the map.
*)
val smd_bi_subst_preserved_by_irrelevant_update
    (t: term)
    (session_to_term_map: PartialMap.t session_id term)
    (impl_secret_key ideal_secret_key: key)
    (session: session_id)
    (impl_message: term)
  : Lemma
    (requires
      ~(PartialMap.contains session_to_term_map session) /\
      in_term t (Senc (SessionId session) ideal_secret_key) == false /\
      in_term t (Senc (Pair (SessionId session) impl_message) impl_secret_key) == false)
    (ensures
      smd_bi_subst t session_to_term_map impl_secret_key ideal_secret_key =
      smd_bi_subst t (PartialMap.upd session_to_term_map session impl_message) impl_secret_key ideal_secret_key)

(**
  If the session_to_term_map is extended with an entry for a new session, and
  the valid encrypted response for that session is not already derivable, then
  the bijective correspondence is preserved.
*)
val bijective_correspondence_preserved_by_additional_message_in_map
    (impl_knowledge ideal_knowledge: knowledge term)
    (session_to_term_map: PartialMap.t session_id term)
    (impl_secret_key ideal_secret_key: key)
    (session: session_id)
    (impl_message: term)
  : Lemma
    (requires (
      // If a new value is being added to the map
      ~(PartialMap.contains session_to_term_map session)
      // And the bijective correspondence holds for the original map
      /\ bijective_correspondence_on_derivations adv impl_knowledge ideal_knowledge
           (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map)
      // And the ideal valid encrypted response for the given session is not
      // present in any derivable term.
      /\ (forall d.
            match adv.derive d ideal_knowledge with
            | None -> True
            | Some t -> in_term t (Senc (SessionId session) ideal_secret_key) == false)
      // And the impl-form for the new entry is not present in any derivable
      // impl term.  In the SMD setting this follows from
      // `impl_invariant_messages_consistent_with_knowledge` combined with
      // `~(contains session_to_term_map session)`: no derivable impl term
      // contains `Senc(Pair(SessionId session) m) impl_k` for any m.
      /\ (forall d.
            match adv.derive d impl_knowledge with
            | None -> True
            | Some t -> in_term t (Senc (Pair (SessionId session) impl_message) impl_secret_key) == false)
      // And the ideal-form for this session is not present in any derivable
      // impl term.  (Since map[session] = None, smd_bi_subst preserves such
      // subterms, so this follows from the ideal-side precondition above via
      // the bijective correspondence — the caller can also establish it
      // directly from any SMD invariant that rules out bare
      // `Senc(SessionId s) k` subterms in impl-world terms.)
      /\ (forall d.
            match adv.derive d impl_knowledge with
            | None -> True
            | Some t -> in_term t (Senc (SessionId session) ideal_secret_key) == false)
    ))
    (ensures (
      let session_to_term_map' = PartialMap.upd session_to_term_map session impl_message in
      // Then the bijective correspondence still holds for the extended map
      bijective_correspondence_on_derivations adv impl_knowledge ideal_knowledge
        (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map')
    ))

val bijective_correspondence_preserved_by_derivable_messages
    (impl_knowledge ideal_knowledge: knowledge term)
    (session_to_term_map: PartialMap.t session_id term)
    (impl_secret_key ideal_secret_key: key)
    (d: adv.derivation)
  : Lemma
    (requires (
      bijective_correspondence_on_derivations adv impl_knowledge ideal_knowledge
        (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map)
      /\ Some? (adv.derive d impl_knowledge)
      /\ Some? (adv.derive d ideal_knowledge)
    ))
    (ensures (
      let impl_t = Some?.v (adv.derive d impl_knowledge) in
      let ideal_t = Some?.v (adv.derive d ideal_knowledge) in
      bijective_correspondence_on_derivations adv (Seq.snoc impl_knowledge impl_t) (Seq.snoc ideal_knowledge ideal_t)
        (smd_subst_bijection impl_secret_key ideal_secret_key session_to_term_map)
    ))
