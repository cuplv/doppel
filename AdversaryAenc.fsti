module AdversaryAenc

open Adversary

open SymbolicTypes

open AencTerms
open StaticEquivalence

open FStar.Classical
open FStar.IndefiniteDescription

module PartialMap = FStar.PartialMap
module Set = FStar.Set



/// Derivations available to the adversary. The derivation bundles indices
/// into the adversary's knowledge along with the capability the adversary
/// can use to derive a new term.
///
/// Bundling the indices into the Derivation type ensures that the
/// derivation always has the correct number of arguments.

type derivation =
  /// Any observed, or initially known, term can be derived by the adversary
  | DeriveObserved : observed_index: knowledge_index -> derivation
  /// Asymmetric encryption using a public key
  | DeriveAEncrypt : plaintext_derivation: derivation -> key_derivation: derivation -> derivation
  /// Asymmetric decryption using a private key
  | DeriveADecrypt : ciphertext_derivation: derivation -> key_derivation: derivation -> derivation
  /// Construct a pair
  | DerivePair : left_derivation: derivation -> right_derivation: derivation -> derivation
  /// Extract the left sub-term of a pair
  | DerivePairLeft : pair_derivation: derivation -> derivation
  /// Extract the right sub-term of a pair
  | DerivePairRight : pair_derivation: derivation -> derivation



(**
  Function modeling the adversary's ability to derive new terms from their
  knowledge. `Some t` is returned if the adversary derives term `t` using the
  given derivaiton and current knowledge, while `None` is returned if the
  adversary cannot derive a term using this derivation.
*)

let rec derive (d: derivation) (know: knowledge term) : option term =
  match d with
  | DeriveObserved observed_index ->
    if observed_index < Seq.length know then Some (Seq.index know observed_index) else None
  | DeriveAEncrypt plaintext_derivation key_derivation ->
    (match derive plaintext_derivation know, derive key_derivation know with
      | Some plaintext, Some (PubKey k) -> Some (Aenc plaintext k)
      | _, _ -> None)
  | DeriveADecrypt ciphertext_derivation key_derivation ->
    (match derive ciphertext_derivation know, derive key_derivation know with
      // Asymmetric decryption only succeeds if the private key used for decryption corresponds to the public key used for encryption.
      | Some (Aenc plaintext k1), Some (PrivKey k2) -> (if k1 = k2 then Some plaintext else None)
      | _, _ -> None)
  | DerivePair left_derivation right_derivation ->
    (match derive left_derivation know, derive right_derivation know with
      | Some left, Some right -> Some (Pair left right)
      | _, _ -> None)
  | DerivePairLeft pair_derivation ->
    (match derive pair_derivation know with
      | Some (Pair left right) -> Some left
      | _ -> None)
  | DerivePairRight pair_derivation ->
    (match derive pair_derivation know with
      | Some (Pair left right) -> Some right
      | _ -> None)

let derivable (know: knowledge term) (t: term) : (r: prop{r == (exists d. derive d know = Some t)}) =
  exists d. derive d know = Some t

let rec indistinguishable (term1 term2: term) : prop =
  match term1, term2 with
  // Encrypted terms are always statically indistinguishable since they require decrypting to distinguish.
  | Aenc _ _, Aenc _ _ -> True
  // Nonces are considered indistinguishable, assuming they are drawn from a
  // sufficiently large space and unbiased distribution. Note that deriving the
  // same nonce twice is still possible, so indistinguishability does not imply
  // static equivalence.
  | Nonce _, Nonce _ -> True
  | Pair a1 b1, Pair a2 b2 -> indistinguishable a1 a2 /\ indistinguishable b1 b2
  | ParticipantId p1, ParticipantId p2 -> p1 = p2
  | SessionId sid1, SessionId sid2 -> sid1 = sid2
  | Data d1, Data d2 -> d1 = d2
  | PrivKey k1, PrivKey k2
  | PubKey k1, PubKey k2 -> k1 = k2
  // Different term constructors are distinguishable
  | _, _ -> False

(** Indistinguishability is an equivalence relation. *)

val indistinguishable_refl (t: term) : Lemma (indistinguishable t t)

val indistinguishable_symm (t1 t2: term)
    : Lemma (indistinguishable t1 t2 ==> indistinguishable t2 t1)

val indistinguishable_trans (t1 t2 t3: term)
    : Lemma (indistinguishable t1 t2 /\ indistinguishable t2 t3 ==> indistinguishable t1 t3)

val append_preserves_derive (d: derivation) (know1 know2: knowledge term)
    : Lemma
      (ensures (forall t. derive d know1 = Some t ==> derive d (Seq.append know1 know2) = Some t))
      [SMTPat (derive d know1); SMTPat (derive d (Seq.append know1 know2))]

[@@ FStar.Tactics.Typeclasses.tcinstance]
let adversary_aenc:adversary term =
  {
    derivation = derivation;
    derive = derive;
    indistinguishable = indistinguishable;
    indistinguishable_equiv
    =
    (fun () ->
        FStar.Classical.forall_intro indistinguishable_refl;
        FStar.Classical.forall_intro_2 indistinguishable_symm;
        FStar.Classical.forall_intro_3 indistinguishable_trans);
    derivable = derivable;
    append_preserves_derive
    =
    let append_preserves_derive_proof d know1 know2 =
      append_preserves_derive d know1 know2;
      ()
    in
    append_preserves_derive_proof
  }



(** Extends the `append_preserves_derive_proof` to the `derivable` proposition. *)

val append_preserves_derivable (know1 know2: knowledge term) (t: term)
    : Lemma (requires derivable know1 t)
      (ensures derivable (Seq.append know1 know2) t)
      [SMTPat (derivable know1 t); SMTPat (derivable (Seq.append know1 know2) t)]



(**
  Intuition behind this function is that when a term `t` is already derivable
  using derivation `replacement`, and when `t` is observed, then any derivation
  that uses the new observation will produce the same term as a derivation where
  the observation is replaced by `replacement`. This function carries out that
  replacement to help prove subsequent lemmas.
*)

let rec replace_observed_derivation (pivot: knowledge_index) (replacement d: derivation)
    : derivation =
  match d with
  | DeriveObserved i -> if i = pivot then replacement else DeriveObserved i
  | DeriveAEncrypt plaintext_derivation key_derivation ->
    DeriveAEncrypt (replace_observed_derivation pivot replacement plaintext_derivation)
      (replace_observed_derivation pivot replacement key_derivation)
  | DeriveADecrypt ciphertext_derivation key_derivation ->
    DeriveADecrypt (replace_observed_derivation pivot replacement ciphertext_derivation)
      (replace_observed_derivation pivot replacement key_derivation)
  | DerivePair left_derivation right_derivation ->
    DerivePair (replace_observed_derivation pivot replacement left_derivation)
      (replace_observed_derivation pivot replacement right_derivation)
  | DerivePairLeft pair_derivation ->
    DerivePairLeft (replace_observed_derivation pivot replacement pair_derivation)
  | DerivePairRight pair_derivation ->
    DerivePairRight (replace_observed_derivation pivot replacement pair_derivation)



(**
  Bidirectional equality: deriving with `d` from the extended knowledge
  `Seq.snoc know observed_term` is the same as deriving with
  `replace_observed_derivation (Seq.length know) replacement d` from `know`,
  provided `replacement` derives `observed_term` from `know`.
*)

val replace_observed_derivation_eq
      (know: knowledge term)
      (observed_term: term)
      (replacement d: derivation)
    : Lemma
      (requires derive replacement know = Some observed_term)
      (ensures
        derive d (Seq.snoc know observed_term) =
        derive (replace_observed_derivation (Seq.length know) replacement d) know)



(**
  Helper lemma that no new information can be derived after observing a term
  that was already derivable.
*)

val observe_derivable_no_new_derivations (know: knowledge term) (t t': term)
    : Lemma (requires derivable know t /\ derivable (Seq.snoc know t) t')
      (ensures derivable know t')
      [SMTPat (derivable know t); SMTPat (derivable (Seq.snoc know t) t')]

(**
  Proposition that the given term `t` is built from a combination of the given
  knowledge and set of subterms.

  Subterms are reconstruction seeds extracted from an observed term. Base terms
  are subterms and ciphertexts are also subterms, even when they can be
  decrypted since they can be derived without knowing the public key to
  reconstruct them. In contrast, pairs are _not_ subterms. They are decomposed
  into their components.

  This proposition is useful for reasoning about whether or not a term can be
  constructed from a current knowledge and newly observed term. This is
  particularly useful when reasoning about whether or not a secret key can be
  newly derived. See `derivable_from_session_encrypted_term_without_key` in
  `examples/nsl_mutual_authentication/MA.Adversary.fst` for one example of how
  this proposition can be established.
*)
let rec built_with_subterms
      (know: knowledge term)
      (subterms : Set.set term)
      (t: term)
    : Tot prop
    (decreases size_of_term t)
=
  derivable know t \/ Set.mem t subterms \/
  (match t with
    | Pair l r ->
      built_with_subterms know subterms l /\
      built_with_subterms know subterms r
    | Aenc p k' ->
      built_with_subterms know subterms p /\
      built_with_subterms know subterms (PubKey k')
    | _ -> False)

val derivable_pair_left
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires derivable know (Pair l r))
      (ensures derivable know l)

val derivable_pair_right
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires derivable know (Pair l r))
      (ensures derivable know r)

val derivable_pair_intro
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires derivable know l /\ derivable know r)
      (ensures derivable know (Pair l r))

val not_derivable_pair_intro_left
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires ~ (derivable know l))
      (ensures ~ (derivable know (Pair l r)))

val not_derivable_pair_intro_right
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires ~ (derivable know r))
      (ensures ~ (derivable know (Pair l r)))

val not_derivable_pair_elim
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires ~ (derivable know (Pair l r)))
      (ensures ~ (derivable know l) \/ ~ (derivable know r))

val derivable_aenc_intro
      (know: knowledge term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires derivable know p /\ derivable know (PubKey k))
      (ensures derivable know (Aenc p k))

(**
  Returns the set of derivable subterms of `t` given current knowledge `know`.
  Derivable subterms are the smaller subterms of `t` that could be derived using
  the current knowledge and the derivable subterms of `t`. Note that deriving
  subterms could enable further subterms to be derived, for example when a
  private key subterm is derived that enables decryption of a ciphertext subterm
  to reveal new subterms. This function is not decidable (it relies on the
  undecidable `derivable` proposition) so it is given the `GTot` effect.

  Base terms are subterms and ciphertexts are also subterms, even when they can
  be decrypted since they can be derived without knowing the public key to
  reconstruct them. Furthermore, if a ciphertext can be decrypted, the subterms
  of its contained plaintext are also subterms. In contrast, pairs are _not_
  subterms. They are decomposed into their components.

  For example, given a term `Pair (SessionId session) (Aenc m k)` where the key
  `k` is not currently derivable, the derivable subterms are `{SessionId
  session, Aenc m k}`. However, the term `Pair (PrivKey k) (Aenc m k)` would
  have derivable subterms `{PrivKey k, Aenc m k, derivable_subterms (know ++
  [PrivKey k; Aenc m k]) m}`, that is the private key, the ciphertext, and any
  subterms of the plaintext that become derivable once the private key and
  ciphertext are added to the knowledge.
*)
val derivable_subterms (know: knowledge term) (t: term) : GTot (Set.set term)

(**
  Under-approximation of `derivable_subterms`. It does not consider private keys
  that could have been learned through the derived subterms.

  This function is easier to reason about than `derivable_subterms` and exactly
  coincides with it when no private key subterms are immediately derivable. See
  `derivable_subterms_underapproximate_keys_exact_with_no_privkeys` for an
  example of how this function can be used in place of the more general
  `derivable_subterms` function.
*)
let rec derivable_subterms_underapproximate_keys
      (know: knowledge term)
      (t: term)
    : GTot (Set.set term)
    (decreases size_of_term t)
  =
  match t with
  | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
    Set.singleton t
  | Pair l r ->
    Set.union
      (derivable_subterms_underapproximate_keys know l)
      (derivable_subterms_underapproximate_keys know r)
  | Aenc p k ->
    if strong_excluded_middle (derivable know (PrivKey k))
    then Set.add t (derivable_subterms_underapproximate_keys know p)
    else Set.singleton t

let no_private_key_subterms (subterms: Set.set term) : prop =
  forall k. ~(Set.mem (PrivKey k) subterms)

val built_from_subterms_pair_left
      (know: knowledge term)
      (subterms: Set.set term)
      (l r: term)
    : Lemma
      (requires built_with_subterms know subterms (Pair l r) /\
                ~(Set.mem (Pair l r) subterms))
      (ensures built_with_subterms know subterms l)

val built_from_subterms_pair_right
      (know: knowledge term)
      (subterms: Set.set term)
      (l r: term)
    : Lemma
      (requires built_with_subterms know subterms (Pair l r) /\
                ~(Set.mem (Pair l r) subterms))
      (ensures built_with_subterms know subterms r)

val built_from_subterms_aenc_components
      (know: knowledge term)
      (subterms: Set.set term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires built_with_subterms know subterms (Aenc p k) /\
                ~(derivable know (Aenc p k)) /\
                ~(Set.mem (Aenc p k) subterms))
      (ensures built_with_subterms know subterms p /\
               built_with_subterms know subterms (PubKey k))

val built_from_subterms_data_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (d: data)
    : Lemma
      (requires built_with_subterms know subterms (Data d) /\
                ~(Set.mem (Data d) subterms))
      (ensures derivable know (Data d))

val built_from_subterms_session_id_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (sid: session_id)
    : Lemma
      (requires built_with_subterms know subterms (SessionId sid) /\
                ~(Set.mem (SessionId sid) subterms))
      (ensures derivable know (SessionId sid))

val built_from_subterms_nonce_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (n: nonce)
    : Lemma
      (requires built_with_subterms know subterms (Nonce n) /\
                ~(Set.mem (Nonce n) subterms))
      (ensures derivable know (Nonce n))

val built_from_subterms_participant_id_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (p: participant_id)
    : Lemma
      (requires built_with_subterms know subterms (ParticipantId p) /\
                ~(Set.mem (ParticipantId p) subterms))
      (ensures derivable know (ParticipantId p))

val built_from_subterms_pubkey_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (k: priv_key)
    : Lemma
      (requires built_with_subterms know subterms (PubKey k) /\
                ~(Set.mem (PubKey k) subterms))
      (ensures derivable know (PubKey k))

(**
  When a set of subterms has no private key members, any private key
  built from those subterms must already be derivable from the base
  knowledge.  Used together with `derivable_from_observed_term_without_private_key_subterms`
  to argue that observing a key-free term cannot expose a new private key.
*)
val private_key_built_from_subterms_already_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (k: priv_key)
    : Lemma
      (requires no_private_key_subterms subterms /\ built_with_subterms know subterms (PrivKey k))
      (ensures derivable know (PrivKey k))

(**
  When no private key subterms can be immediately derived from term `t`, then
  the simpler `derivable_subterms_underapproximate_keys` coincides with
  `derivable_subterms`.
*)
val derivable_subterms_underapproximate_keys_exact_with_no_privkeys
      (know: knowledge term)
      (t: term)
    : Lemma
      (requires no_private_key_subterms (derivable_subterms_underapproximate_keys know t))
      (ensures Set.equal
        (derivable_subterms_underapproximate_keys know t)
        (derivable_subterms know t))

(**
  When no private key subterms can be immediately derived from an observed term,
  then any term derived from that observation must be built from the current
  knowledge and the derivable subterms of the observed term.

  This lemma is useful for reasoning about what new terms can be derived after
  observing a term. In particular, it is useful for reasoning about whether or
  not a secret key can be newly derived after observing an encrypted term when
  the corresponding private key is not already derivable. See
  `derivable_from_session_encrypted_term_without_key` in
  `examples/nsl_mutual_authentication/MA.Adversary.fst` for one application of
  this lemma.
*)
val derivable_from_observed_term_without_private_key_subterms
      (know: knowledge term)
      (observed_term: term)
      (d: derivation)
      (derived_term: term)
    : Lemma
      (requires
        no_private_key_subterms (derivable_subterms_underapproximate_keys know observed_term) /\
        derive d (Seq.snoc know observed_term) = Some derived_term)
      (ensures built_with_subterms know (derivable_subterms know observed_term) derived_term)

(**
  If two knowledges are statically equivalent, then they must have an equal
  number of observations. Otherwise they could be distinguished by some
  `DeriveObserved` derivation.
*)
val statically_equivalent_length (impl_know ideal_know: knowledge term)
  : Lemma
    (requires statically_equivalent adversary_aenc impl_know ideal_know)
    (ensures Seq.length impl_know == Seq.length ideal_know)
    [SMTPat (statically_equivalent adversary_aenc impl_know ideal_know)]
