module AdversarySenc

open Adversary

open SymbolicTypes

open SencTerms
open StaticEquivalence

open FStar.Classical

module PartialMap = FStar.PartialMap



/// Derivations available to the adversary. The derivation bundles indices
/// into the adversary's knowledge along with the capability the adversary
/// can use to derive a new term.
///
/// Bundling the indices into the Derivation type ensures that the
/// derivation always has the correct number of arguments.

type derivation =
  /// Any observed, or initially known, term can be derived by the adversary
  | DeriveObserved : observed_index: knowledge_index -> derivation
  /// Symmetric encryption
  | DeriveSEncrypt : plaintext_derivation: derivation -> key_derivation: derivation -> derivation
  /// Symmetric decryption
  | DeriveSDecrypt : ciphertext_derivation: derivation -> key_derivation: derivation -> derivation
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
  | DeriveSEncrypt plaintext_derivation key_derivation ->
    (match derive plaintext_derivation know, derive key_derivation know with
      | Some plaintext, Some (Key k) -> Some (Senc plaintext k)
      | _, _ -> None)
  | DeriveSDecrypt ciphertext_derivation key_derivation ->
    (match derive ciphertext_derivation know, derive key_derivation know with
      | Some (Senc plaintext k1), Some (Key k2) -> (if k1 = k2 then Some plaintext else None)
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
  | Senc _ _, Senc _ _ ->
    // Encrypted terms are always statically indistinguishable since they require decrypting to distinguish.
    True
  | Pair a1 b1, Pair a2 b2 -> indistinguishable a1 a2 /\ indistinguishable b1 b2
  | SessionId sid1, SessionId sid2 -> sid1 = sid2
  | Data d1, Data d2 -> d1 = d2
  | Key k1, Key k2 -> k1 = k2
  | Bool b1, Bool b2 -> b1 = b2
  | _, _ ->
    // Different term constructors are distinguishable
    False

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
let adversary_senc:adversary term =
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
  | DeriveSEncrypt plaintext_derivation key_derivation ->
    DeriveSEncrypt (replace_observed_derivation pivot replacement plaintext_derivation)
      (replace_observed_derivation pivot replacement key_derivation)
  | DeriveSDecrypt ciphertext_derivation key_derivation ->
    DeriveSDecrypt (replace_observed_derivation pivot replacement ciphertext_derivation)
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

  This holds for all derivations `d` regardless of whether they succeed,
  because the replacement preserves `None` results too.
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
  A subterm is contained within a term if it is the term or is contained within one of the .
*)

let rec in_term (t subterm: term) : bool =
  t = subterm ||
  (match t with
    | Senc plaintext _ ->
      // Note: the key contained in `Senc` is not a term, so it cannot contain the
      // subterm.
      in_term plaintext subterm
    | Pair left right -> in_term left subterm || in_term right subterm
    | _ -> false)

let in_term_refl (t: term) : Lemma (in_term t t) [SMTPat (in_term t t)] = ()

(**
  Structural decomposition: every term derivable from
  `know ++ [Senc m k]` (when `Key k` is not derivable from `know`) is built
  by combining know-derivable subterms and copies of `Senc m k` via
  `Pair`/`Senc`-with-derivable-key.
*)
let rec built_from_know_and_ciphertext
      (know: knowledge term)
      (m: term)
      (k: key)
      (t: term)
    : prop =
  derivable know t \/ t == Senc m k \/
  (match t with
    | Pair l r ->
      built_from_know_and_ciphertext know m k l /\ built_from_know_and_ciphertext know m k r
    | Senc p k' -> built_from_know_and_ciphertext know m k p /\ derivable know (Key k')
    | _ -> False)

val derivable_from_encrypted_term_without_key
      (know: knowledge term)
      (m: term)
      (k: key)
      (d: derivation)
      (derived_term: term)
    : Lemma
      (requires
        (~(derivable know (Key k))) /\ (derive d (Seq.snoc know (Senc m k)) = Some derived_term))
      (ensures built_from_know_and_ciphertext know m k derived_term)



(**
  Any key term derivable after observing an encrypted term (whose key was
  previously unknown) must have already been derivable before the observation.

  This is a corollary of `derivable_from_encrypted_term_without_key`:
  the `built_from_know_and_ciphertext` predicate for a `Key k'` term immediately
  collapses to `derivable know (Key k')` because `Key k'` is neither the
  ciphertext itself nor a compound term (Pair/Senc).
*)

val keys_learned_from_ciphertext_already_derivable
      (know: knowledge term)
      (m: term)
      (k k': key)
      (d: derivation)
    : Lemma
      (requires
        (~(derivable know (Key k))) /\ (derive d (Seq.snoc know (Senc m k)) = Some (Key k')))
      (ensures derivable know (Key k'))


(**
  If two knowledges are statically equivalent, then they must have an equal
  number of observations. Otherwise they could be distinguished by some
  `DeriveObserved` derivation.
*)
val statically_equivalent_length (impl_know ideal_know: knowledge term)
  : Lemma
    (requires statically_equivalent adversary_senc impl_know ideal_know)
    (ensures Seq.length impl_know == Seq.length ideal_know)
    [SMTPat (statically_equivalent adversary_senc impl_know ideal_know)]
