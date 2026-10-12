module AdversaryAenc

open FStar.List.Tot
open FStar.Set.Properties


let rec indistinguishable_refl (t: term) : Lemma (indistinguishable t t) =
  match t with
  | Pair a b ->
    indistinguishable_refl a;
    indistinguishable_refl b
  | _ -> ()

let rec indistinguishable_symm (t1 t2: term)
    : Lemma (indistinguishable t1 t2 ==> indistinguishable t2 t1) =
  match t1, t2 with
  | Pair a1 b1, Pair a2 b2 ->
    indistinguishable_symm a1 a2;
    indistinguishable_symm b1 b2
  | _, _ -> ()

let rec indistinguishable_trans (t1 t2 t3: term)
    : Lemma (indistinguishable t1 t2 /\ indistinguishable t2 t3 ==> indistinguishable t1 t3) =
  match t1, t2, t3 with
  | Pair a1 b1, Pair a2 b2, Pair a3 b3 ->
    indistinguishable_trans a1 a2 a3;
    indistinguishable_trans b1 b2 b3
  | _, _, _ -> ()

let rec append_preserves_derive (d: derivation) (know1 know2: knowledge term)
    : Lemma
    (ensures
      (forall t. derive d know1 = Some t ==> derive d (Seq.append know1 know2) = Some t)) =
  match d with
  | DeriveObserved observed_index -> ()
  | DeriveAEncrypt plaintext_derivation key_derivation ->
    append_preserves_derive plaintext_derivation know1 know2;
    append_preserves_derive key_derivation know1 know2
  | DeriveADecrypt ciphertext_derivation key_derivation ->
    append_preserves_derive ciphertext_derivation know1 know2;
    append_preserves_derive key_derivation know1 know2
  | DerivePair left_derivation right_derivation ->
    append_preserves_derive left_derivation know1 know2;
    append_preserves_derive right_derivation know1 know2
  | DerivePairLeft pair_derivation -> append_preserves_derive pair_derivation know1 know2
  | DerivePairRight pair_derivation -> append_preserves_derive pair_derivation know1 know2

let append_preserves_derivable (know1 know2: knowledge term) (t: term)
    : Lemma (requires derivable know1 t) (ensures derivable (Seq.append know1 know2) t) =
  let open FStar.Classical in
  let p: derivation -> prop = (fun d -> derive d know1 = Some t) in
  let d =
    FStar.IndefiniteDescription.indefinite_description_ghost derivation p
  in
  append_preserves_derive d know1 know2;
  exists_intro (fun d -> derive d (Seq.append know1 know2) = Some t) d

let rec replace_observed_derivation_eq
      (know: knowledge term)
      (observed_term: term)
      (replacement d: derivation)
    : Lemma
      (requires derive replacement know = Some observed_term)
      (ensures
        derive d (Seq.snoc know observed_term) =
        derive (replace_observed_derivation (Seq.length know) replacement d) know) =
  match d with
  | DeriveObserved i ->
    if i < Seq.length know
    then
      assert (Seq.index (Seq.snoc know observed_term) i == Seq.index know i)
    else if i = Seq.length know
    then
      assert (Seq.index (Seq.snoc know observed_term) i == observed_term)
    else ()
  | DeriveAEncrypt pt kd ->
    replace_observed_derivation_eq know observed_term replacement pt;
    replace_observed_derivation_eq know observed_term replacement kd
  | DeriveADecrypt ct kd ->
    replace_observed_derivation_eq know observed_term replacement ct;
    replace_observed_derivation_eq know observed_term replacement kd
  | DerivePair l r ->
    replace_observed_derivation_eq know observed_term replacement l;
    replace_observed_derivation_eq know observed_term replacement r
  | DerivePairLeft p ->
    replace_observed_derivation_eq know observed_term replacement p
  | DerivePairRight p ->
    replace_observed_derivation_eq know observed_term replacement p

let observe_derivable_no_new_derivations (know: knowledge term) (t t': term)
    : Lemma (requires derivable know t /\ derivable (Seq.snoc know t) t')
      (ensures derivable know t') =
  let p_replacement: derivation -> prop = (fun d -> derive d know = Some t) in
  let replacement =
    FStar.IndefiniteDescription.indefinite_description_ghost derivation p_replacement
  in
  assert (derive replacement know = Some t);
  let p_d: derivation -> prop = (fun d -> derive d (Seq.snoc know t) = Some t') in
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable (Seq.snoc know t) t')
  then
    (let d = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_d in
      replace_observed_derivation_eq know t replacement d;
      assert (derive (replace_observed_derivation (Seq.length know) replacement d) know = Some t');
      exists_intro (fun d' -> derive d' know = Some t')
        (replace_observed_derivation (Seq.length know) replacement d))

let derivable_pair_left
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires derivable know (Pair l r))
      (ensures derivable know l) =
  let p_pair: derivation -> prop =
    (fun d -> derive d know = Some (Pair l r))
  in
  let d_pair = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_pair in
  assert (derive (DerivePairLeft d_pair) know = Some l);
  exists_intro (fun d -> derive d know = Some l) (DerivePairLeft d_pair)

let derivable_pair_right
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires derivable know (Pair l r))
      (ensures derivable know r) =
  let p_pair: derivation -> prop =
    (fun d -> derive d know = Some (Pair l r))
  in
  let d_pair = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_pair in
  assert (derive (DerivePairRight d_pair) know = Some r);
  exists_intro (fun d -> derive d know = Some r) (DerivePairRight d_pair)

let derivable_pair_intro
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires derivable know l /\ derivable know r)
      (ensures derivable know (Pair l r)) =
  let p_left: derivation -> prop =
    (fun d -> derive d know = Some l)
  in
  let d_left = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_left in
  let p_right: derivation -> prop =
    (fun d -> derive d know = Some r)
  in
  let d_right = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_right in
  assert (derive (DerivePair d_left d_right) know = Some (Pair l r));
  exists_intro (fun d -> derive d know = Some (Pair l r)) (DerivePair d_left d_right)

let not_derivable_pair_intro_left
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires ~ (derivable know l))
      (ensures ~ (derivable know (Pair l r)))
=
  introduce (derivable know (Pair l r)) ==> False
  with _h. (
    derivable_pair_left know l r;
    assert false
  )

let not_derivable_pair_intro_right
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires ~ (derivable know r))
      (ensures ~ (derivable know (Pair l r)))
=
  introduce (derivable know (Pair l r)) ==> False
  with _h. (
    derivable_pair_right know l r;
    assert false
  )

let not_derivable_pair_elim
      (know: knowledge term)
      (l r: term)
    : Lemma
      (requires ~ (derivable know (Pair l r)))
      (ensures ~ (derivable know l) \/ ~ (derivable know r))
=
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know l)
  then (
    introduce (derivable know r) ==> False
    with _h. (
      derivable_pair_intro know l r;
      assert false
    )
  )
  else ()

let derivable_aenc_intro
      (know: knowledge term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires derivable know p /\ derivable know (PubKey k))
      (ensures derivable know (Aenc p k)) =
  let p_plaintext: derivation -> prop =
    (fun d -> derive d know = Some p)
  in
  let d_plaintext = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_plaintext in
  let p_key: derivation -> prop =
    (fun d -> derive d know = Some (PubKey k))
  in
  let d_key = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_key in
  assert (derive (DeriveAEncrypt d_plaintext d_key) know = Some (Aenc p k));
  exists_intro (fun d -> derive d know = Some (Aenc p k)) (DeriveAEncrypt d_plaintext d_key)

let derivable_aenc_plaintext
      (know: knowledge term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires derivable know (Aenc p k) /\ derivable know (PrivKey k))
      (ensures derivable know p) =
  let p_ciphertext: derivation -> prop =
    (fun d -> derive d know = Some (Aenc p k))
  in
  let d_ciphertext = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_ciphertext in
  let p_key: derivation -> prop =
    (fun d -> derive d know = Some (PrivKey k))
  in
  let d_key = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_key in
  assert (derive (DeriveADecrypt d_ciphertext d_key) know = Some p);
  exists_intro (fun d -> derive d know = Some p) (DeriveADecrypt d_ciphertext d_key)

let rec built_from_subterms_monotone
      (know: knowledge term)
      (subterms1 subterms2: Set.set term)
      (t: term)
    : Lemma
      (requires built_with_subterms know subterms1 t /\ Set.subset subterms1 subterms2)
      (ensures built_with_subterms know subterms2 t)
      (decreases size_of_term t) =
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know t)
  then ()
  else if strong_excluded_middle (Set.mem t subterms1)
  then ()
  else
    match t with
    | Pair l r ->
      built_from_subterms_monotone know subterms1 subterms2 l;
      built_from_subterms_monotone know subterms1 subterms2 r
    | Aenc p k ->
      built_from_subterms_monotone know subterms1 subterms2 p;
      built_from_subterms_monotone know subterms1 subterms2 (PubKey k)
    | _ ->
      Set.subset_mem subterms1 subterms2;
      assert (Set.mem t subterms2)

(**
  The size of a list of terms is simply the sum of the term sizes. Used to prove
  termination of recursive calls.
*)
let rec term_list_size (terms: list term) : nat =
  match terms with
  | [] -> 0
  | t::ts -> size_of_term t + term_list_size ts

let rec term_list_size_append (terms1 terms2: list term) : Lemma
    (ensures term_list_size (terms1 @ terms2) == term_list_size terms1 + term_list_size terms2)
    [SMTPat (term_list_size (terms1 @ terms2))]
  = match terms1 with
    | [] -> ()
    | t::ts -> term_list_size_append ts terms2

let rec derivable_subterms_helper_round
      (know: knowledge term)
      (terms: list term)
      // Returns a list of subterms that could be determined to be within
      // `terms` (stored as a list, rather than a set, so it can easily be
      // appended to the knowledge for subsequent rounds), and the list of terms
      // that is still pending resolution (e.g. encrypted terms that may still
      // have their key derived from the other terms).
      : GTot (
        (list term)
        & (pending: list term {
          // Either decreases in remaining size or returns the same pending
          // list, which means a fixed point has been reached.
          pending == terms \/ term_list_size pending < term_list_size terms
        }))
  (decreases (term_list_size terms))
  =
  match terms with
  | [] -> [], []
  | t::ts ->
    match t with
    | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
      let subterms, pending = derivable_subterms_helper_round know ts in
      t :: subterms, pending
    | Aenc p k ->
      // `derivable` is not decidable, so we use `strong_excluded_middle` to get a boolean we can branch on.
      let can_derive_k = strong_excluded_middle (derivable know (PrivKey k)) in
      if can_derive_k
      // If the key is derivable, then the ciphertext can be decrypted as well.
      // We consider the ciphertext term to be a subterm, in that it is an
      // intermediate derivation that does not need knowledge of the public key
      // to reconstruct. Any subterms contained in the plaintext must also
      // be included.
      then (
        let p_subterms, pending = derivable_subterms_helper_round know (p :: ts) in
        t :: p_subterms, pending
      )
      // Otherwise, the key could potentially still be derived from the other terms, so we keep this encrypted term in the pending list for now.
      else
        let subterms, pending = derivable_subterms_helper_round know ts in
        subterms, t :: pending
    | Pair l r ->
      let subterms_l, pending_l = derivable_subterms_helper_round know [l] in
      let subterms_r, pending_r = derivable_subterms_helper_round know [r] in
      let subterms_rest, pending_rest = derivable_subterms_helper_round know ts in
      assert (size_of_term (Pair l r) > size_of_term l + size_of_term r);
      assert (term_list_size ((Pair l r) :: ts) > term_list_size (l :: r :: ts));
      assert (term_list_size pending_l <= size_of_term l);
      assert (term_list_size pending_r <= size_of_term r);
      subterms_l @ subterms_r @ subterms_rest, pending_l @ pending_r @ pending_rest

let rec derivable_subterms_helper
      (know: knowledge term)
      (subterms: list term)
      (terms: list term)
    : GTot (list term)
    // Terminates since, as a result of calling
    // `derivable_subterms_helper_round`, either a fixed point was reached
    // (`pending = terms`) or the size of remaining pending terms strictly
    // decreased.
    (decreases (term_list_size terms))
  =
  let new_subterms, pending = derivable_subterms_helper_round know terms in
  let total_subterms = subterms @ new_subterms in
  if pending = terms
  // If we couldn't resolve any new subterms in this round, then any remaining terms must also be subterms since they could not be decomposed further.
  then total_subterms @ pending
  // Otherwise progress was made in resolving subterms, so we continue trying to resolve the remaining pending terms with the new knowledge of subterms.
  else (
    derivable_subterms_helper (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending
  )

let derivable_subterms (know: knowledge term) (t: term) : GTot (Set.set term) =
  Set.as_set (derivable_subterms_helper know [] [t])


let rec derivable_subterms_underapproximate_keys_list
      (know: knowledge term)
      (terms: list term)
    : GTot (Set.set term)
    (decreases term_list_size terms)
  =
  match terms with
  | [] -> Set.empty
  | t::ts ->
    Set.union
      (derivable_subterms_underapproximate_keys know t)
      (derivable_subterms_underapproximate_keys_list know ts)

let derivable_subterms_helper_round_subterms
      (know: knowledge term)
      (terms: list term)
    : GTot (list term) =
  let subterms, _ = derivable_subterms_helper_round know terms in
  subterms

let derivable_subterms_helper_round_pending
      (know: knowledge term)
      (terms: list term)
    : GTot (list term) =
  let _, pending = derivable_subterms_helper_round know terms in
  pending

let derivable_subterms_underapproximate_keys_list_singleton
      (know: knowledge term)
      (t: term)
    : Lemma
      (ensures derivable_subterms_underapproximate_keys_list know [t] == derivable_subterms_underapproximate_keys know t) =
  assert (forall x.
    Set.mem x (derivable_subterms_underapproximate_keys_list know [t]) =
    Set.mem x (derivable_subterms_underapproximate_keys know t));
  Set.lemma_equal_intro
    (derivable_subterms_underapproximate_keys_list know [t])
    (derivable_subterms_underapproximate_keys know t);
  Set.lemma_equal_elim
    (derivable_subterms_underapproximate_keys_list know [t])
    (derivable_subterms_underapproximate_keys know t)

let rec derivable_subterms_underapproximate_keys_list_append_left_subset
      (know: knowledge term)
      (terms1 terms2: list term)
    : Lemma
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys_list know terms1)
        (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)))
      (decreases term_list_size terms1) =
  match terms1 with
  | [] ->
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys_list know terms1) ==>
      Set.mem x (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys_list know terms1)
      (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2))
  | t::ts ->
    derivable_subterms_underapproximate_keys_list_append_left_subset know ts terms2;
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys_list know terms1) ==>
      Set.mem x (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys_list know terms1)
      (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2))

let rec derivable_subterms_underapproximate_keys_list_append_right_subset
      (know: knowledge term)
      (terms1 terms2: list term)
    : Lemma
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys_list know terms2)
        (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)))
      (decreases term_list_size terms1) =
  match terms1 with
  | [] ->
    assert (terms1 @ terms2 == terms2);
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys_list know terms2) ==>
      Set.mem x (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys_list know terms2)
      (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2))
  | t::ts ->
    derivable_subterms_underapproximate_keys_list_append_right_subset know ts terms2;
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys_list know terms2) ==>
      Set.mem x (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys_list know terms2)
      (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2))

let rec derivable_subterms_underapproximate_keys_list_append_subset
      (know: knowledge term)
      (terms1 terms2: list term)
      (target: Set.set term)
    : Lemma
      (requires
        Set.subset (derivable_subterms_underapproximate_keys_list know terms1) target /\
        Set.subset (derivable_subterms_underapproximate_keys_list know terms2) target)
      (ensures Set.subset (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)) target)
      (decreases term_list_size terms1) =
  match terms1 with
  | [] ->
    assert (terms1 @ terms2 == terms2);
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)) ==> Set.mem x target);
    Set.mem_subset (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)) target
  | t::ts ->
    derivable_subterms_underapproximate_keys_list_append_subset know ts terms2 target;
    Set.subset_mem (derivable_subterms_underapproximate_keys_list know terms1) target;
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)) ==> Set.mem x target);
    Set.mem_subset (derivable_subterms_underapproximate_keys_list know (terms1 @ terms2)) target

let rec derivable_subterms_underapproximate_keys_monotone_knowledge
      (know1 know2: knowledge term)
      (t: term)
    : Lemma
      (requires forall k. derivable know1 (PrivKey k) ==> derivable know2 (PrivKey k))
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys know1 t)
        (derivable_subterms_underapproximate_keys know2 t))
      (decreases size_of_term t) =
  let open FStar.IndefiniteDescription in
  match t with
  | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know1 t) ==> Set.mem x (derivable_subterms_underapproximate_keys know2 t));
    Set.mem_subset (derivable_subterms_underapproximate_keys know1 t) (derivable_subterms_underapproximate_keys know2 t)
  | Pair l r ->
    derivable_subterms_underapproximate_keys_monotone_knowledge know1 know2 l;
    derivable_subterms_underapproximate_keys_monotone_knowledge know1 know2 r;
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know1 t) ==> Set.mem x (derivable_subterms_underapproximate_keys know2 t));
    Set.mem_subset (derivable_subterms_underapproximate_keys know1 t) (derivable_subterms_underapproximate_keys know2 t)
  | Aenc p k ->
    if strong_excluded_middle (derivable know1 (PrivKey k))
    then (
      assert (derivable know2 (PrivKey k));
      if strong_excluded_middle (derivable know2 (PrivKey k))
      then (
        derivable_subterms_underapproximate_keys_monotone_knowledge know1 know2 p;
        assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know1 t) ==> Set.mem x (derivable_subterms_underapproximate_keys know2 t));
        Set.mem_subset (derivable_subterms_underapproximate_keys know1 t) (derivable_subterms_underapproximate_keys know2 t)
      )
      else assert false
    )
    else (
      assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know1 t) ==> Set.mem x (derivable_subterms_underapproximate_keys know2 t));
      Set.mem_subset (derivable_subterms_underapproximate_keys know1 t) (derivable_subterms_underapproximate_keys know2 t)
    )

let rec derivable_subterms_underapproximate_keys_list_monotone_knowledge
      (know1 know2: knowledge term)
      (terms: list term)
    : Lemma
      (requires forall k. derivable know1 (PrivKey k) ==> derivable know2 (PrivKey k))
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys_list know1 terms)
        (derivable_subterms_underapproximate_keys_list know2 terms))
      (decreases term_list_size terms) =
  match terms with
  | [] ->
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know1 terms) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know2 terms));
    Set.mem_subset (derivable_subterms_underapproximate_keys_list know1 terms) (derivable_subterms_underapproximate_keys_list know2 terms)
  | t::ts ->
    derivable_subterms_underapproximate_keys_monotone_knowledge know1 know2 t;
    derivable_subterms_underapproximate_keys_list_monotone_knowledge know1 know2 ts;
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know1 terms) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know2 terms));
    Set.mem_subset (derivable_subterms_underapproximate_keys_list know1 terms) (derivable_subterms_underapproximate_keys_list know2 terms)

  #push-options "--split_queries always"
let rec derivable_subterms_helper_round_covers_underapprox_list
      (know: knowledge term)
      (terms: list term)
    : Lemma
      (ensures
        Set.subset
          (derivable_subterms_underapproximate_keys_list know terms)
          (Set.union
            (Set.as_set (derivable_subterms_helper_round_subterms know terms))
            (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms))))
      (decreases term_list_size terms) =
  let open FStar.IndefiniteDescription in
  match terms with
  | [] ->
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==>
      Set.mem x (Set.union (Set.as_set []) (derivable_subterms_underapproximate_keys_list know [])));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys_list know terms)
      (Set.union (Set.as_set []) (derivable_subterms_underapproximate_keys_list know []))
  | t::ts ->
    (match t with
    | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
      derivable_subterms_helper_round_covers_underapprox_list know ts;
      let subterms, pending = derivable_subterms_helper_round know ts in
      assert (forall x.
        Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==>
        Set.mem x (Set.union (Set.as_set (t :: subterms)) (derivable_subterms_underapproximate_keys_list know pending)));
      Set.mem_subset
        (derivable_subterms_underapproximate_keys_list know terms)
        (Set.union (Set.as_set (t :: subterms)) (derivable_subterms_underapproximate_keys_list know pending))
    | Aenc p k ->
      if strong_excluded_middle (derivable know (PrivKey k))
      then (
        derivable_subterms_helper_round_covers_underapprox_list know (p :: ts);
        let p_subterms, pending = derivable_subterms_helper_round know (p :: ts) in
        assert (forall x.
          Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==>
          Set.mem x (Set.union (Set.as_set (t :: p_subterms)) (derivable_subterms_underapproximate_keys_list know pending)));
        Set.mem_subset
          (derivable_subterms_underapproximate_keys_list know terms)
          (Set.union (Set.as_set (t :: p_subterms)) (derivable_subterms_underapproximate_keys_list know pending))
      )
      else (
        derivable_subterms_helper_round_covers_underapprox_list know ts;
        let subterms, pending = derivable_subterms_helper_round know ts in
        assert (forall x.
          Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==>
          Set.mem x (Set.union (Set.as_set subterms) (derivable_subterms_underapproximate_keys_list know (t :: pending))));
        Set.mem_subset
          (derivable_subterms_underapproximate_keys_list know terms)
          (Set.union (Set.as_set subterms) (derivable_subterms_underapproximate_keys_list know (t :: pending)))
      )
    | Pair l r ->
      derivable_subterms_helper_round_covers_underapprox_list know [l];
      derivable_subterms_helper_round_covers_underapprox_list know [r];
      derivable_subterms_helper_round_covers_underapprox_list know ts;
      let subterms_l, pending_l = derivable_subterms_helper_round know [l] in
      let subterms_r, pending_r = derivable_subterms_helper_round know [r] in
      let subterms_rest, pending_rest = derivable_subterms_helper_round know ts in
      FStar.List.Tot.append_assoc subterms_l subterms_r subterms_rest;
      FStar.List.Tot.append_assoc pending_l pending_r pending_rest;
      as_set_append_left_subset subterms_l (subterms_r @ subterms_rest);
      as_set_append_right_subset subterms_l (subterms_r @ subterms_rest);
      as_set_append_left_subset subterms_r subterms_rest;
      as_set_append_right_subset subterms_r subterms_rest;
      derivable_subterms_underapproximate_keys_list_append_left_subset know pending_l (pending_r @ pending_rest);
      derivable_subterms_underapproximate_keys_list_append_right_subset know pending_l (pending_r @ pending_rest);
      derivable_subterms_underapproximate_keys_list_append_left_subset know pending_r pending_rest;
      derivable_subterms_underapproximate_keys_list_append_right_subset know pending_r pending_rest;
      let target_subterms = Set.as_set (subterms_l @ subterms_r @ subterms_rest) in
      let target_pending = derivable_subterms_underapproximate_keys_list know (pending_l @ pending_r @ pending_rest) in
      let target = Set.union target_subterms target_pending in
      set_subset_union_left target_subterms target_pending;
      set_subset_union_right target_subterms target_pending;
      assert (Set.subset (Set.as_set subterms_l) target_subterms);
      assert (Set.subset (Set.as_set subterms_r) target_subterms);
      assert (Set.subset (Set.as_set subterms_rest) target_subterms);
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know pending_l) target_pending);
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know pending_r) target_pending);
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know pending_rest) target_pending);
      set_subset_transitive (Set.as_set subterms_l) target_subterms target;
      set_subset_transitive (Set.as_set subterms_r) target_subterms target;
      set_subset_transitive (Set.as_set subterms_rest) target_subterms target;
      set_subset_transitive (derivable_subterms_underapproximate_keys_list know pending_l) target_pending target;
      set_subset_transitive (derivable_subterms_underapproximate_keys_list know pending_r) target_pending target;
      set_subset_transitive (derivable_subterms_underapproximate_keys_list know pending_rest) target_pending target;
      assert (Set.subset
        (derivable_subterms_underapproximate_keys_list know [l])
        (Set.union (Set.as_set subterms_l) (derivable_subterms_underapproximate_keys_list know pending_l)));
      assert (Set.subset
        (derivable_subterms_underapproximate_keys_list know [r])
        (Set.union (Set.as_set subterms_r) (derivable_subterms_underapproximate_keys_list know pending_r)));
      assert (Set.subset
        (derivable_subterms_underapproximate_keys_list know ts)
        (Set.union (Set.as_set subterms_rest) (derivable_subterms_underapproximate_keys_list know pending_rest)));
      set_subset_union (Set.as_set subterms_l) (derivable_subterms_underapproximate_keys_list know pending_l) target;
      set_subset_union (Set.as_set subterms_r) (derivable_subterms_underapproximate_keys_list know pending_r) target;
      set_subset_union (Set.as_set subterms_rest) (derivable_subterms_underapproximate_keys_list know pending_rest) target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know [l])
        (Set.union (Set.as_set subterms_l) (derivable_subterms_underapproximate_keys_list know pending_l))
        target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know [r])
        (Set.union (Set.as_set subterms_r) (derivable_subterms_underapproximate_keys_list know pending_r))
        target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know ts)
        (Set.union (Set.as_set subterms_rest) (derivable_subterms_underapproximate_keys_list know pending_rest))
        target;
      assert (forall x.
        Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==>
        Set.mem x (Set.union
          (Set.as_set (subterms_l @ subterms_r @ subterms_rest))
          (derivable_subterms_underapproximate_keys_list know (pending_l @ pending_r @ pending_rest))));
      Set.mem_subset
        (derivable_subterms_underapproximate_keys_list know terms)
        (Set.union
          (Set.as_set (subterms_l @ subterms_r @ subterms_rest))
          (derivable_subterms_underapproximate_keys_list know (pending_l @ pending_r @ pending_rest)))
    )
#pop-options

let rec derivable_subterms_helper_round_no_progress_underapprox_list_subset_terms
      (know: knowledge term)
      (terms: list term)
    : Lemma
      (requires
        derivable_subterms_helper_round_pending know terms == terms)
      (ensures Set.subset (derivable_subterms_underapproximate_keys_list know terms) (Set.as_set terms))
      (decreases term_list_size terms) =
  let open FStar.IndefiniteDescription in
  match terms with
  | [] ->
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==> Set.mem x (Set.as_set terms));
    Set.mem_subset (derivable_subterms_underapproximate_keys_list know terms) (Set.as_set terms)
  | t::ts ->
    (match t with
    | Aenc p k ->
      if strong_excluded_middle (derivable know (PrivKey k))
      then (
        let _, pending = derivable_subterms_helper_round know (p :: ts) in
        assert (term_list_size pending <= term_list_size (p :: ts));
        assert (term_list_size pending == term_list_size terms);
        assert false
      )
      else (
        let _, pending = derivable_subterms_helper_round know ts in
        assert (pending == ts);
        derivable_subterms_helper_round_no_progress_underapprox_list_subset_terms know ts;
        assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==> Set.mem x (Set.as_set terms));
        Set.mem_subset (derivable_subterms_underapproximate_keys_list know terms) (Set.as_set terms)
      )
    | Pair l r ->
      let _, pending_l = derivable_subterms_helper_round know [l] in
      let _, pending_r = derivable_subterms_helper_round know [r] in
      let _, pending_rest = derivable_subterms_helper_round know ts in
      term_list_size_append pending_l pending_r;
      term_list_size_append (pending_l @ pending_r) pending_rest;
      assert (term_list_size (pending_l @ pending_r @ pending_rest) < term_list_size terms);
      assert false
    | _ ->
      let _, pending = derivable_subterms_helper_round know ts in
      assert (term_list_size pending <= term_list_size ts);
      assert (term_list_size pending == term_list_size terms);
      assert false)

let rec derivable_subterms_helper_contains_acc
      (know: knowledge term)
      (acc terms: list term)
    : Lemma
      (ensures Set.subset (Set.as_set acc) (Set.as_set (derivable_subterms_helper know acc terms)))
      (decreases term_list_size terms) =
  let new_subterms, pending = derivable_subterms_helper_round know terms in
  let total_subterms = acc @ new_subterms in
  if pending = terms
  then (
    as_set_append_left_subset acc new_subterms;
    as_set_append_left_subset total_subterms pending;
    set_subset_transitive (Set.as_set acc) (Set.as_set total_subterms) (Set.as_set (total_subterms @ pending))
  )
  else (
    derivable_subterms_helper_contains_acc
      (Seq.append know (Seq.seq_of_list total_subterms))
      total_subterms
      pending;
    as_set_append_left_subset acc new_subterms;
    assert (Set.subset (Set.as_set acc) (Set.as_set total_subterms));
    assert (Set.subset
      (Set.as_set total_subterms)
      (Set.as_set (derivable_subterms_helper
        (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending)));
        assert (Set.subset (Set.as_set acc) (Set.as_set total_subterms) /\
            Set.subset
              (Set.as_set total_subterms)
              (Set.as_set (derivable_subterms_helper
                (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending)));
    set_subset_transitive
      (Set.as_set acc)
      (Set.as_set total_subterms)
      (Set.as_set (derivable_subterms_helper
        (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending))
  )

let rec derivable_subterms_helper_contains_underapprox_list
      (know: knowledge term)
      (acc terms: list term)
    : Lemma
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys_list know terms)
        (Set.as_set (derivable_subterms_helper know acc terms)))
      (decreases term_list_size terms) =
  let new_subterms, pending = derivable_subterms_helper_round know terms in
  let total_subterms = acc @ new_subterms in
  if pending = terms
  then (
    derivable_subterms_helper_round_no_progress_underapprox_list_subset_terms know terms;
    as_set_append_right_subset total_subterms pending;
    set_subset_transitive
      (derivable_subterms_underapproximate_keys_list know terms)
      (Set.as_set terms)
      (Set.as_set (total_subterms @ pending))
  )
  else (
    derivable_subterms_helper_round_covers_underapprox_list know terms;
    derivable_subterms_helper_contains_acc
      (Seq.append know (Seq.seq_of_list total_subterms))
      total_subterms
      pending;
    derivable_subterms_helper_contains_underapprox_list
      (Seq.append know (Seq.seq_of_list total_subterms))
      total_subterms
      pending;
    assert (forall k. derivable know (PrivKey k) ==> derivable (Seq.append know (Seq.seq_of_list total_subterms)) (PrivKey k));
    derivable_subterms_underapproximate_keys_list_monotone_knowledge
      know
      (Seq.append know (Seq.seq_of_list total_subterms))
      pending;
    assert (Set.subset
      (derivable_subterms_underapproximate_keys_list know pending)
      (Set.as_set (derivable_subterms_helper (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending)));
    as_set_append_right_subset acc new_subterms;
    assert (Set.subset (Set.as_set new_subterms) (Set.as_set (derivable_subterms_helper (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending)));
    set_subset_union
      (Set.as_set new_subterms)
      (derivable_subterms_underapproximate_keys_list know pending)
      (Set.as_set (derivable_subterms_helper (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending));
    set_subset_transitive
      (derivable_subterms_underapproximate_keys_list know terms)
      (Set.union (Set.as_set new_subterms) (derivable_subterms_underapproximate_keys_list know pending))
      (Set.as_set (derivable_subterms_helper (Seq.append know (Seq.seq_of_list total_subterms)) total_subterms pending))
  )

let derivable_subterms_underapproximate_keys_subset_derivable_subterms
      (know: knowledge term)
      (t: term)
    : Lemma
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys know t)
        (derivable_subterms know t))
      (decreases size_of_term t) =
  derivable_subterms_helper_contains_underapprox_list know [] [t];
  derivable_subterms_underapproximate_keys_list_singleton know t;
  assert (Set.subset
    (derivable_subterms_underapproximate_keys know t)
    (derivable_subterms know t))

let derivable_subterms_underapproximate_keys_pair_left_subset
      (know: knowledge term)
      (l r: term)
    : Lemma
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys know l)
        (derivable_subterms_underapproximate_keys know (Pair l r))) =
  assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know l) ==> Set.mem x (derivable_subterms_underapproximate_keys know (Pair l r)));
  Set.mem_subset (derivable_subterms_underapproximate_keys know l) (derivable_subterms_underapproximate_keys know (Pair l r))

let derivable_subterms_underapproximate_keys_pair_right_subset
      (know: knowledge term)
      (l r: term)
    : Lemma
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys know r)
        (derivable_subterms_underapproximate_keys know (Pair l r))) =
  assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know r) ==> Set.mem x (derivable_subterms_underapproximate_keys know (Pair l r)));
  Set.mem_subset (derivable_subterms_underapproximate_keys know r) (derivable_subterms_underapproximate_keys know (Pair l r))

let derivable_subterms_underapproximate_keys_aenc_plaintext_subset
      (know: knowledge term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires derivable know (PrivKey k))
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys know p)
        (derivable_subterms_underapproximate_keys know (Aenc p k))) =
  if FStar.IndefiniteDescription.strong_excluded_middle (derivable know (PrivKey k))
  then (
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys know p) ==> Set.mem x (derivable_subterms_underapproximate_keys know (Aenc p k)));
    Set.mem_subset (derivable_subterms_underapproximate_keys know p) (derivable_subterms_underapproximate_keys know (Aenc p k))
  )
  else assert false

let rec derivable_subterms_underapproximate_keys_transitive
      (know: knowledge term)
      (root child: term)
    : Lemma
      (requires Set.mem child (derivable_subterms_underapproximate_keys know root))
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys know child)
        (derivable_subterms_underapproximate_keys know root))
      (decreases size_of_term root) =
  let open FStar.IndefiniteDescription in
  match root with
  | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
    assert (child == root);
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys know child) ==>
      Set.mem x (derivable_subterms_underapproximate_keys know root));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys know child)
      (derivable_subterms_underapproximate_keys know root)
  | Pair l r ->
    let left_subterms = derivable_subterms_underapproximate_keys know l in
    let right_subterms = derivable_subterms_underapproximate_keys know r in
    if strong_excluded_middle (Set.mem child left_subterms)
    then (
      derivable_subterms_underapproximate_keys_transitive know l child;
      derivable_subterms_underapproximate_keys_pair_left_subset know l r;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys know child)
        left_subterms
        (derivable_subterms_underapproximate_keys know root)
    )
    else (
      assert (Set.mem child right_subterms);
      derivable_subterms_underapproximate_keys_transitive know r child;
      derivable_subterms_underapproximate_keys_pair_right_subset know l r;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys know child)
        right_subterms
        (derivable_subterms_underapproximate_keys know root)
    )
  | Aenc p k ->
    if strong_excluded_middle (derivable know (PrivKey k))
    then (
      if child = root
      then (
        assert (forall x.
          Set.mem x (derivable_subterms_underapproximate_keys know child) ==>
          Set.mem x (derivable_subterms_underapproximate_keys know root));
        Set.mem_subset
          (derivable_subterms_underapproximate_keys know child)
          (derivable_subterms_underapproximate_keys know root)
      )
      else (
        assert (Set.mem child (derivable_subterms_underapproximate_keys know p));
        derivable_subterms_underapproximate_keys_transitive know p child;
        derivable_subterms_underapproximate_keys_aenc_plaintext_subset know p k;
        set_subset_transitive
          (derivable_subterms_underapproximate_keys know child)
          (derivable_subterms_underapproximate_keys know p)
          (derivable_subterms_underapproximate_keys know root)
      )
    )
    else (
      assert (child == root);
      assert (forall x.
        Set.mem x (derivable_subterms_underapproximate_keys know child) ==>
        Set.mem x (derivable_subterms_underapproximate_keys know root));
      Set.mem_subset
        (derivable_subterms_underapproximate_keys know child)
        (derivable_subterms_underapproximate_keys know root)
    )

let rec derivable_subterms_underapproximate_keys_list_transitive
      (know: knowledge term)
      (root: term)
      (terms: list term)
    : Lemma
      (requires Set.subset
        (Set.as_set terms)
        (derivable_subterms_underapproximate_keys know root))
      (ensures Set.subset
        (derivable_subterms_underapproximate_keys_list know terms)
        (derivable_subterms_underapproximate_keys know root))
      (decreases term_list_size terms) =
  match terms with
  | [] ->
    assert (forall x.
      Set.mem x (derivable_subterms_underapproximate_keys_list know terms) ==>
      Set.mem x (derivable_subterms_underapproximate_keys know root));
    Set.mem_subset
      (derivable_subterms_underapproximate_keys_list know terms)
      (derivable_subterms_underapproximate_keys know root)
  | t::ts ->
    Set.subset_mem (Set.as_set terms) (derivable_subterms_underapproximate_keys know root);
    derivable_subterms_underapproximate_keys_transitive know root t;
    assert (Set.subset (Set.as_set ts) (derivable_subterms_underapproximate_keys know root));
    derivable_subterms_underapproximate_keys_list_transitive know root ts;
    set_subset_union
      (derivable_subterms_underapproximate_keys know t)
      (derivable_subterms_underapproximate_keys_list know ts)
      (derivable_subterms_underapproximate_keys know root)

let rec observed_term_built_from_derivable_subterms_underapproximate_keys
      (know: knowledge term)
      (observed_term: term)
    : Lemma
      (ensures built_with_subterms know (derivable_subterms_underapproximate_keys know observed_term) observed_term)
      (decreases size_of_term observed_term) =
  let open FStar.IndefiniteDescription in
  match observed_term with
  | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
    Set.mem_singleton observed_term observed_term;
    assert (Set.mem observed_term (derivable_subterms_underapproximate_keys know observed_term))
  | Pair l r ->
    observed_term_built_from_derivable_subterms_underapproximate_keys know l;
    derivable_subterms_underapproximate_keys_pair_left_subset know l r;
    built_from_subterms_monotone know (derivable_subterms_underapproximate_keys know l) (derivable_subterms_underapproximate_keys know observed_term) l;
    observed_term_built_from_derivable_subterms_underapproximate_keys know r;
    derivable_subterms_underapproximate_keys_pair_right_subset know l r;
    built_from_subterms_monotone know (derivable_subterms_underapproximate_keys know r) (derivable_subterms_underapproximate_keys know observed_term) r
  | Aenc p k ->
    if strong_excluded_middle (derivable know (PrivKey k))
    then (
      Set.mem_union observed_term (derivable_subterms_underapproximate_keys know p) (Set.singleton observed_term);
      Set.mem_singleton observed_term observed_term;
      assert (Set.mem observed_term (derivable_subterms_underapproximate_keys know observed_term))
    )
    else (
      Set.mem_singleton observed_term observed_term;
      assert (Set.mem observed_term (derivable_subterms_underapproximate_keys know observed_term))
    )

let rec derivable_subterms_underapproximate_keys_decryptable_ciphertext_plaintext_built
      (know: knowledge term)
      (observed_term: term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires
        Set.mem (Aenc p k) (derivable_subterms_underapproximate_keys know observed_term) /\
        derivable know (PrivKey k))
      (ensures built_with_subterms know (derivable_subterms_underapproximate_keys know observed_term) p)
      (decreases size_of_term observed_term) =
  let target = Aenc p k in
  let open FStar.IndefiniteDescription in
  match observed_term with
  | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
    Set.mem_singleton observed_term target;
    assert false
  | Pair l r ->
    Set.mem_union target (derivable_subterms_underapproximate_keys know l) (derivable_subterms_underapproximate_keys know r);
    if strong_excluded_middle (Set.mem target (derivable_subterms_underapproximate_keys know l))
    then (
      derivable_subterms_underapproximate_keys_decryptable_ciphertext_plaintext_built know l p k;
      derivable_subterms_underapproximate_keys_pair_left_subset know l r;
      built_from_subterms_monotone know (derivable_subterms_underapproximate_keys know l) (derivable_subterms_underapproximate_keys know observed_term) p
    )
    else (
      assert (Set.mem target (derivable_subterms_underapproximate_keys know r));
      derivable_subterms_underapproximate_keys_decryptable_ciphertext_plaintext_built know r p k;
      derivable_subterms_underapproximate_keys_pair_right_subset know l r;
      built_from_subterms_monotone know (derivable_subterms_underapproximate_keys know r) (derivable_subterms_underapproximate_keys know observed_term) p
    )
  | Aenc q j ->
    if strong_excluded_middle (derivable know (PrivKey j))
    then (
      Set.mem_union target (derivable_subterms_underapproximate_keys know q) (Set.singleton observed_term);
      Set.mem_singleton observed_term target;
      if strong_excluded_middle (Set.mem target (derivable_subterms_underapproximate_keys know q))
      then (
        derivable_subterms_underapproximate_keys_decryptable_ciphertext_plaintext_built know q p k;
        derivable_subterms_underapproximate_keys_aenc_plaintext_subset know q j;
        built_from_subterms_monotone know (derivable_subterms_underapproximate_keys know q) (derivable_subterms_underapproximate_keys know observed_term) p
      )
      else (
        assert (target == observed_term);
        assert (p == q);
        observed_term_built_from_derivable_subterms_underapproximate_keys know q;
        derivable_subterms_underapproximate_keys_aenc_plaintext_subset know q j;
        built_from_subterms_monotone know (derivable_subterms_underapproximate_keys know q) (derivable_subterms_underapproximate_keys know observed_term) q
      )
    )
    else (
      Set.mem_singleton observed_term target;
      assert (target == observed_term);
      assert (k == j);
      assert false
    )

let built_from_derivable_subterms_underapproximate_keys_aenc_plaintext
      (know: knowledge term)
      (observed_term: term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires
        built_with_subterms know (derivable_subterms_underapproximate_keys know observed_term) (Aenc p k) /\
        derivable know (PrivKey k))
      (ensures built_with_subterms know (derivable_subterms_underapproximate_keys know observed_term) p) =
  let subterms = derivable_subterms_underapproximate_keys know observed_term in
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know (Aenc p k))
  then (
    derivable_aenc_plaintext know p k
  )
  else if strong_excluded_middle (Set.mem (Aenc p k) subterms)
  then derivable_subterms_underapproximate_keys_decryptable_ciphertext_plaintext_built know observed_term p k
  else ()

let rec derivable_subterms_underapproximate_keys_no_pair
      (know: knowledge term)
      (observed_term: term)
      (l r: term)
    : Lemma
      (ensures ~(Set.mem (Pair l r) (derivable_subterms_underapproximate_keys know observed_term)))
      (decreases size_of_term observed_term) =
  let open FStar.IndefiniteDescription in
  match observed_term with
  | Pair left right ->
    derivable_subterms_underapproximate_keys_no_pair know left l r;
    derivable_subterms_underapproximate_keys_no_pair know right l r;
    if strong_excluded_middle (Set.mem (Pair l r) (derivable_subterms_underapproximate_keys know left))
    then assert false
    else if strong_excluded_middle (Set.mem (Pair l r) (derivable_subterms_underapproximate_keys know right))
    then assert false
    else ()
  | Aenc plaintext key ->
    if strong_excluded_middle (derivable know (PrivKey key))
    then (
      derivable_subterms_underapproximate_keys_no_pair know plaintext l r;
      if strong_excluded_middle (Set.mem (Pair l r) (derivable_subterms_underapproximate_keys know plaintext))
      then assert false
      else ()
    )
    else ()
  | _ -> ()

let built_from_subterms_pair_left
      (know: knowledge term)
      (subterms: Set.set term)
      (l r: term)
    : Lemma
        (requires built_with_subterms know subterms (Pair l r) /\ ~(Set.mem (Pair l r) subterms))
      (ensures built_with_subterms know subterms l) =
  if FStar.IndefiniteDescription.strong_excluded_middle (derivable know (Pair l r))
  then derivable_pair_left know l r
    else (
    assert (~(derivable know (Pair l r)));
    assert (~(Set.mem (Pair l r) subterms));
      assert (built_with_subterms know subterms l /\ built_with_subterms know subterms r)
    )

let built_from_subterms_pair_right
      (know: knowledge term)
      (subterms: Set.set term)
      (l r: term)
    : Lemma
      (requires built_with_subterms know subterms (Pair l r) /\ ~(Set.mem (Pair l r) subterms))
      (ensures built_with_subterms know subterms r) =
  if FStar.IndefiniteDescription.strong_excluded_middle (derivable know (Pair l r))
  then derivable_pair_right know l r
  else (
    assert (~(derivable know (Pair l r)));
    assert (~(Set.mem (Pair l r) subterms));
    assert (built_with_subterms know subterms l /\ built_with_subterms know subterms r)
  )

let built_from_subterms_aenc_components
      (know: knowledge term)
      (subterms: Set.set term)
      (p: term)
      (k: priv_key)
    : Lemma
      (requires built_with_subterms know subterms (Aenc p k) /\
                ~(derivable know (Aenc p k)) /\
                ~(Set.mem (Aenc p k) subterms))
      (ensures built_with_subterms know subterms p /\
               built_with_subterms know subterms (PubKey k)) =
  assert (built_with_subterms know subterms p /\
          built_with_subterms know subterms (PubKey k))

let built_from_subterms_data_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (d: data)
    : Lemma
      (requires built_with_subterms know subterms (Data d) /\
                ~(Set.mem (Data d) subterms))
      (ensures derivable know (Data d)) =
  assert (derivable know (Data d))

let built_from_subterms_session_id_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (sid: session_id)
    : Lemma
      (requires built_with_subterms know subterms (SessionId sid) /\
                ~(Set.mem (SessionId sid) subterms))
      (ensures derivable know (SessionId sid)) =
  assert (derivable know (SessionId sid))

let built_from_subterms_nonce_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (n: nonce)
    : Lemma
      (requires built_with_subterms know subterms (Nonce n) /\
                ~(Set.mem (Nonce n) subterms))
      (ensures derivable know (Nonce n)) =
  assert (derivable know (Nonce n))

let built_from_subterms_participant_id_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (p: participant_id)
    : Lemma
      (requires built_with_subterms know subterms (ParticipantId p) /\
                ~(Set.mem (ParticipantId p) subterms))
      (ensures derivable know (ParticipantId p)) =
  assert (derivable know (ParticipantId p))

let built_from_subterms_pubkey_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (k: priv_key)
    : Lemma
      (requires built_with_subterms know subterms (PubKey k) /\
                ~(Set.mem (PubKey k) subterms))
      (ensures derivable know (PubKey k)) =
  assert (derivable know (PubKey k))

let rec seq_of_list_index_mem
      (terms: list term)
      (i: nat {i < Seq.length (Seq.seq_of_list terms)})
    : Lemma
      (ensures Set.mem (Seq.index (Seq.seq_of_list terms) i) (Set.as_set terms))
      (decreases term_list_size terms) =
  match terms with
  | [] ->
    Seq.lemma_empty (Seq.seq_of_list terms);
    assert false
  | t::ts ->
    Seq.lemma_seq_of_list_cons t ts;
    if i = 0
    then (
      Seq.lemma_index_app1 (Seq.create 1 t) (Seq.seq_of_list ts) i;
      Seq.lemma_index_create 1 t 0;
      assert (Seq.index (Seq.seq_of_list terms) i == t)
    )
    else (
      Seq.lemma_index_app2 (Seq.create 1 t) (Seq.seq_of_list ts) i;
      seq_of_list_index_mem ts (i - 1);
      assert (Seq.index (Seq.seq_of_list terms) i == Seq.index (Seq.seq_of_list ts) (i - 1));
      assert (Set.mem (Seq.index (Seq.seq_of_list terms) i) (Set.as_set terms))
    )

let private_key_built_from_subterms_already_derivable
      (know: knowledge term)
      (subterms: Set.set term)
      (k: priv_key)
    : Lemma
      (requires no_private_key_subterms subterms /\ built_with_subterms know subterms (PrivKey k))
      (ensures derivable know (PrivKey k)) =
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know (PrivKey k))
  then ()
  else (
    assert (Set.mem (PrivKey k) subterms);
    assert false
  )

let rec derivable_from_context_and_observed_list_built_from_underapprox
      (root_know current_know: knowledge term)
      (root_term: term)
      (observed: list term)
      (d: derivation)
      (derived_term: term)
    : Lemma
      (requires
        no_private_key_subterms (derivable_subterms_underapproximate_keys root_know root_term) /\
        (forall x. derivable current_know x ==> built_with_subterms root_know (derivable_subterms_underapproximate_keys root_know root_term) x) /\
        (forall x. Set.mem x (Set.as_set observed) ==> built_with_subterms root_know (derivable_subterms_underapproximate_keys root_know root_term) x) /\
        derive d (Seq.append current_know (Seq.seq_of_list observed)) = Some derived_term)
      (ensures built_with_subterms root_know (derivable_subterms_underapproximate_keys root_know root_term) derived_term) =
  let current = Seq.append current_know (Seq.seq_of_list observed) in
  let root_subterms = derivable_subterms_underapproximate_keys root_know root_term in
  match d with
  | DeriveObserved observed_index ->
    if observed_index < Seq.length current_know
    then (
      Seq.lemma_index_app1 current_know (Seq.seq_of_list observed) observed_index;
      assert (derive (DeriveObserved observed_index) current_know = Some derived_term);
      exists_intro (fun d' -> derive d' current_know = Some derived_term) (DeriveObserved observed_index);
      assert (derivable current_know derived_term)
    )
    else if observed_index < Seq.length current
    then (
      Seq.lemma_index_app2 current_know (Seq.seq_of_list observed) observed_index;
      seq_of_list_index_mem observed (observed_index - Seq.length current_know);
      assert (Set.mem derived_term (Set.as_set observed))
    )
    else (
      assert (derive d current = None);
      assert false
    )
  | DeriveAEncrypt plaintext_derivation key_derivation ->
    (match derive plaintext_derivation current, derive key_derivation current with
    | Some plaintext, Some (PubKey key) ->
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed plaintext_derivation plaintext;
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed key_derivation (PubKey key);
      assert (derived_term == Aenc plaintext key)
    | _, _ -> ())
  | DeriveADecrypt ciphertext_derivation key_derivation ->
    (match derive ciphertext_derivation current, derive key_derivation current with
    | Some (Aenc plaintext key1), Some (PrivKey key2) ->
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed ciphertext_derivation (Aenc plaintext key1);
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed key_derivation (PrivKey key2);
      private_key_built_from_subterms_already_derivable root_know root_subterms key2;
      if key1 = key2
      then (
        assert (derived_term == plaintext);
        built_from_derivable_subterms_underapproximate_keys_aenc_plaintext root_know root_term plaintext key1
      )
      else (
        assert (derive d current = None);
        assert false
      )
    | _, _ -> ())
  | DerivePair left_derivation right_derivation ->
    (match derive left_derivation current, derive right_derivation current with
    | Some left, Some right ->
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed left_derivation left;
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed right_derivation right;
      assert (derived_term == Pair left right)
    | _, _ -> ())
  | DerivePairLeft pair_derivation ->
    (match derive pair_derivation current with
    | Some (Pair left right) ->
      assert (derived_term == left);
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed pair_derivation (Pair left right);
      derivable_subterms_underapproximate_keys_no_pair root_know root_term left right;
      built_from_subterms_pair_left root_know root_subterms left right
    | _ -> ())
  | DerivePairRight pair_derivation ->
    (match derive pair_derivation current with
    | Some (Pair left right) ->
      assert (derived_term == right);
      derivable_from_context_and_observed_list_built_from_underapprox
        root_know current_know root_term observed pair_derivation (Pair left right);
      derivable_subterms_underapproximate_keys_no_pair root_know root_term left right;
      built_from_subterms_pair_right root_know root_subterms left right
    | _ -> ())

let private_key_derivable_from_context_and_observed_list_already_derivable
      (root_know current_know: knowledge term)
      (root_term: term)
      (observed: list term)
      (key: priv_key)
    : Lemma
      (requires
        no_private_key_subterms (derivable_subterms_underapproximate_keys root_know root_term) /\
        (forall x. derivable current_know x ==> built_with_subterms root_know (derivable_subterms_underapproximate_keys root_know root_term) x) /\
        (forall x. Set.mem x (Set.as_set observed) ==> built_with_subterms root_know (derivable_subterms_underapproximate_keys root_know root_term) x) /\
        derivable (Seq.append current_know (Seq.seq_of_list observed)) (PrivKey key))
      (ensures derivable root_know (PrivKey key)) =
  let p: derivation -> prop =
    fun d -> derive d (Seq.append current_know (Seq.seq_of_list observed)) = Some (PrivKey key) in
  let d = FStar.IndefiniteDescription.indefinite_description_ghost derivation p in
  derivable_from_context_and_observed_list_built_from_underapprox
    root_know current_know root_term observed d (PrivKey key);
  private_key_built_from_subterms_already_derivable
    root_know
    (derivable_subterms_underapproximate_keys root_know root_term)
    key

  #push-options "--split_queries always"

let rec derivable_subterms_helper_round_components_subset_underapprox_list
      (know: knowledge term)
      (terms: list term)
    : Lemma
      (ensures
        Set.subset
          (Set.as_set (derivable_subterms_helper_round_subterms know terms))
          (derivable_subterms_underapproximate_keys_list know terms) /\
        Set.subset
          (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms))
          (derivable_subterms_underapproximate_keys_list know terms))
      (decreases term_list_size terms) =
  let open FStar.IndefiniteDescription in
  match terms with
  | [] ->
    assert (forall x. Set.mem x (Set.as_set []) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
    assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know []) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
    Set.mem_subset (Set.as_set []) (derivable_subterms_underapproximate_keys_list know terms);
    Set.mem_subset (derivable_subterms_underapproximate_keys_list know []) (derivable_subterms_underapproximate_keys_list know terms)
  | t::ts ->
    (match t with
    | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
      derivable_subterms_helper_round_components_subset_underapprox_list know ts;
      let subterms, pending = derivable_subterms_helper_round know ts in
      assert (forall x. Set.mem x (Set.as_set (t :: subterms)) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
      assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know pending) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
      Set.mem_subset (Set.as_set (t :: subterms)) (derivable_subterms_underapproximate_keys_list know terms);
      Set.mem_subset (derivable_subterms_underapproximate_keys_list know pending) (derivable_subterms_underapproximate_keys_list know terms)
    | Aenc p k ->
      if strong_excluded_middle (derivable know (PrivKey k))
      then (
        derivable_subterms_helper_round_components_subset_underapprox_list know (p :: ts);
        let p_subterms, pending = derivable_subterms_helper_round know (p :: ts) in
        assert (forall x. Set.mem x (Set.as_set (t :: p_subterms)) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
        assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know pending) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
        Set.mem_subset (Set.as_set (t :: p_subterms)) (derivable_subterms_underapproximate_keys_list know terms);
        Set.mem_subset (derivable_subterms_underapproximate_keys_list know pending) (derivable_subterms_underapproximate_keys_list know terms)
      )
      else (
        derivable_subterms_helper_round_components_subset_underapprox_list know ts;
        let subterms, pending = derivable_subterms_helper_round know ts in
        assert (forall x. Set.mem x (Set.as_set subterms) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
        assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know (t :: pending)) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
        Set.mem_subset (Set.as_set subterms) (derivable_subterms_underapproximate_keys_list know terms);
        Set.mem_subset (derivable_subterms_underapproximate_keys_list know (t :: pending)) (derivable_subterms_underapproximate_keys_list know terms)
      )
    | Pair l r ->
      derivable_subterms_helper_round_components_subset_underapprox_list know [l];
      derivable_subterms_helper_round_components_subset_underapprox_list know [r];
      derivable_subterms_helper_round_components_subset_underapprox_list know ts;
      let subterms_l, pending_l = derivable_subterms_helper_round know [l] in
      let subterms_r, pending_r = derivable_subterms_helper_round know [r] in
      let subterms_rest, pending_rest = derivable_subterms_helper_round know ts in
      assert (subterms_l == derivable_subterms_helper_round_subterms know [l]);
      assert (subterms_r == derivable_subterms_helper_round_subterms know [r]);
      assert (subterms_rest == derivable_subterms_helper_round_subterms know ts);
      assert (pending_l == derivable_subterms_helper_round_pending know [l]);
      assert (pending_r == derivable_subterms_helper_round_pending know [r]);
      assert (pending_rest == derivable_subterms_helper_round_pending know ts);
      assert (Set.subset (Set.as_set subterms_l) (derivable_subterms_underapproximate_keys_list know [l]));
      assert (Set.subset (Set.as_set subterms_r) (derivable_subterms_underapproximate_keys_list know [r]));
      assert (Set.subset (Set.as_set subterms_rest) (derivable_subterms_underapproximate_keys_list know ts));
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know pending_l) (derivable_subterms_underapproximate_keys_list know [l]));
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know pending_r) (derivable_subterms_underapproximate_keys_list know [r]));
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know pending_rest) (derivable_subterms_underapproximate_keys_list know ts));
      FStar.List.Tot.append_assoc subterms_l subterms_r subterms_rest;
      FStar.List.Tot.append_assoc pending_l pending_r pending_rest;
      as_set_append_left_subset subterms_l (subterms_r @ subterms_rest);
      as_set_append_right_subset subterms_l (subterms_r @ subterms_rest);
      as_set_append_left_subset subterms_r subterms_rest;
      as_set_append_right_subset subterms_r subterms_rest;
      derivable_subterms_underapproximate_keys_list_append_left_subset know pending_l (pending_r @ pending_rest);
      derivable_subterms_underapproximate_keys_list_append_right_subset know pending_l (pending_r @ pending_rest);
      derivable_subterms_underapproximate_keys_list_append_left_subset know pending_r pending_rest;
      derivable_subterms_underapproximate_keys_list_append_right_subset know pending_r pending_rest;
      let target = derivable_subterms_underapproximate_keys_list know terms in
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know [l]) target);
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know [r]) target);
      assert (Set.subset (derivable_subterms_underapproximate_keys_list know ts) target);
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know pending_l)
        (derivable_subterms_underapproximate_keys_list know [l])
        target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know pending_r)
        (derivable_subterms_underapproximate_keys_list know [r])
        target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know pending_rest)
        (derivable_subterms_underapproximate_keys_list know ts)
        target;
      set_subset_transitive
        (Set.as_set subterms_l)
        (derivable_subterms_underapproximate_keys_list know [l])
        target;
      set_subset_transitive
        (Set.as_set subterms_r)
        (derivable_subterms_underapproximate_keys_list know [r])
        target;
      set_subset_transitive
        (Set.as_set subterms_rest)
        (derivable_subterms_underapproximate_keys_list know ts)
        target;
      as_set_append_subset subterms_l subterms_r target;
      as_set_append_subset (subterms_l @ subterms_r) subterms_rest target;
      derivable_subterms_underapproximate_keys_list_append_subset know pending_l pending_r target;
      derivable_subterms_underapproximate_keys_list_append_subset know (pending_l @ pending_r) pending_rest target;
      assert (forall x. Set.mem x (Set.as_set (subterms_l @ subterms_r @ subterms_rest)) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
      assert (forall x. Set.mem x (derivable_subterms_underapproximate_keys_list know (pending_l @ pending_r @ pending_rest)) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
      Set.mem_subset (Set.as_set (subterms_l @ subterms_r @ subterms_rest)) (derivable_subterms_underapproximate_keys_list know terms);
      Set.mem_subset (derivable_subterms_underapproximate_keys_list know (pending_l @ pending_r @ pending_rest)) (derivable_subterms_underapproximate_keys_list know terms)
    )

let rec derivable_subterms_helper_round_pending_terms_subset_underapprox_list
      (know: knowledge term)
      (terms: list term)
    : Lemma
      (ensures Set.subset
        (Set.as_set (derivable_subterms_helper_round_pending know terms))
        (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms)))
      (decreases term_list_size terms) =
  let open FStar.IndefiniteDescription in
  match terms with
  | [] ->
    assert (forall x.
      Set.mem x (Set.as_set (derivable_subterms_helper_round_pending know terms)) ==>
      Set.mem x (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms)));
    Set.mem_subset
      (Set.as_set (derivable_subterms_helper_round_pending know terms))
      (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms))
  | t::ts ->
    (match t with
    | ParticipantId _ | SessionId _ | Data _ | PrivKey _ | PubKey _ | Nonce _ ->
      derivable_subterms_helper_round_pending_terms_subset_underapprox_list know ts;
      let _, pending = derivable_subterms_helper_round know ts in
      assert (derivable_subterms_helper_round_pending know terms == pending);
      assert (forall x.
        Set.mem x (Set.as_set (derivable_subterms_helper_round_pending know terms)) ==>
        Set.mem x (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms)));
      Set.mem_subset
        (Set.as_set (derivable_subterms_helper_round_pending know terms))
        (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms))
    | Aenc p k ->
      if strong_excluded_middle (derivable know (PrivKey k))
      then (
        derivable_subterms_helper_round_pending_terms_subset_underapprox_list know (p :: ts);
        let _, pending = derivable_subterms_helper_round know (p :: ts) in
        assert (derivable_subterms_helper_round_pending know terms == pending);
        assert (forall x.
          Set.mem x (Set.as_set (derivable_subterms_helper_round_pending know terms)) ==>
          Set.mem x (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms)));
        Set.mem_subset
          (Set.as_set (derivable_subterms_helper_round_pending know terms))
          (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms))
      )
      else (
        derivable_subterms_helper_round_pending_terms_subset_underapprox_list know ts;
        let _, pending = derivable_subterms_helper_round know ts in
        assert (derivable_subterms_helper_round_pending know terms == t :: pending);
        assert (Set.mem t (derivable_subterms_underapproximate_keys know t));
        assert (forall x.
          Set.mem x (Set.as_set (derivable_subterms_helper_round_pending know terms)) ==>
          Set.mem x (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms)));
        Set.mem_subset
          (Set.as_set (derivable_subterms_helper_round_pending know terms))
          (derivable_subterms_underapproximate_keys_list know (derivable_subterms_helper_round_pending know terms))
      )
    | Pair l r ->
      derivable_subterms_helper_round_pending_terms_subset_underapprox_list know [l];
      derivable_subterms_helper_round_pending_terms_subset_underapprox_list know [r];
      derivable_subterms_helper_round_pending_terms_subset_underapprox_list know ts;
      let _, pending_l = derivable_subterms_helper_round know [l] in
      let _, pending_r = derivable_subterms_helper_round know [r] in
      let _, pending_rest = derivable_subterms_helper_round know ts in
      let pending = pending_l @ pending_r @ pending_rest in
      assert (derivable_subterms_helper_round_pending know terms == pending);
      FStar.List.Tot.append_assoc pending_l pending_r pending_rest;
      derivable_subterms_underapproximate_keys_list_append_left_subset know pending_l (pending_r @ pending_rest);
      derivable_subterms_underapproximate_keys_list_append_right_subset know pending_l (pending_r @ pending_rest);
      derivable_subterms_underapproximate_keys_list_append_left_subset know pending_r pending_rest;
      derivable_subterms_underapproximate_keys_list_append_right_subset know pending_r pending_rest;
      let target = derivable_subterms_underapproximate_keys_list know pending in
      set_subset_transitive
        (Set.as_set pending_l)
        (derivable_subterms_underapproximate_keys_list know pending_l)
        target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know pending_r)
        (derivable_subterms_underapproximate_keys_list know (pending_r @ pending_rest))
        target;
      set_subset_transitive
        (Set.as_set pending_r)
        (derivable_subterms_underapproximate_keys_list know pending_r)
        target;
      set_subset_transitive
        (derivable_subterms_underapproximate_keys_list know pending_rest)
        (derivable_subterms_underapproximate_keys_list know (pending_r @ pending_rest))
        target;
      set_subset_transitive
        (Set.as_set pending_rest)
        (derivable_subterms_underapproximate_keys_list know pending_rest)
        target;
      as_set_append_subset pending_l pending_r target;
      as_set_append_subset (pending_l @ pending_r) pending_rest target;
      assert (forall x. Set.mem x (Set.as_set pending) ==> Set.mem x target);
      Set.mem_subset (Set.as_set pending) target
    )

let rec derivable_subterms_helper_round_no_progress_terms_subset_underapprox_list
      (know: knowledge term)
      (terms: list term)
    : Lemma
      (requires derivable_subterms_helper_round_pending know terms == terms)
      (ensures Set.subset (Set.as_set terms) (derivable_subterms_underapproximate_keys_list know terms))
      (decreases term_list_size terms) =
  let open FStar.IndefiniteDescription in
  match terms with
  | [] ->
    assert (forall x. Set.mem x (Set.as_set terms) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
    Set.mem_subset (Set.as_set terms) (derivable_subterms_underapproximate_keys_list know terms)
  | t::ts ->
    (match t with
    | Aenc p k ->
      if strong_excluded_middle (derivable know (PrivKey k))
      then (
        let _, pending = derivable_subterms_helper_round know (p :: ts) in
        assert (term_list_size pending <= term_list_size (p :: ts));
        assert (term_list_size pending == term_list_size terms);
        assert false
      )
      else (
        let _, pending = derivable_subterms_helper_round know ts in
        assert (pending == ts);
        derivable_subterms_helper_round_no_progress_terms_subset_underapprox_list know ts;
        assert (forall x. Set.mem x (Set.as_set terms) ==> Set.mem x (derivable_subterms_underapproximate_keys_list know terms));
        Set.mem_subset (Set.as_set terms) (derivable_subterms_underapproximate_keys_list know terms)
      )
    | Pair l r ->
      let _, pending_l = derivable_subterms_helper_round know [l] in
      let _, pending_r = derivable_subterms_helper_round know [r] in
      let _, pending_rest = derivable_subterms_helper_round know ts in
      term_list_size_append pending_l pending_r;
      term_list_size_append (pending_l @ pending_r) pending_rest;
      assert (term_list_size (pending_l @ pending_r @ pending_rest) < term_list_size terms);
      assert false
    | _ ->
      let _, pending = derivable_subterms_helper_round know ts in
      assert (term_list_size pending <= term_list_size ts);
      assert (term_list_size pending == term_list_size terms);
      assert false)

let rec derivable_subterms_helper_subset_underroot
      (root_know current_know: knowledge term)
      (root_term: term)
      (acc terms: list term)
    : Lemma
      (requires
        no_private_key_subterms (derivable_subterms_underapproximate_keys root_know root_term) /\
        (forall x. derivable current_know x ==> built_with_subterms root_know (derivable_subterms_underapproximate_keys root_know root_term) x) /\
        Set.subset (Set.as_set acc) (derivable_subterms_underapproximate_keys root_know root_term) /\
        Set.subset (derivable_subterms_underapproximate_keys_list current_know terms) (derivable_subterms_underapproximate_keys root_know root_term))
      (ensures Set.subset
        (Set.as_set (derivable_subterms_helper current_know acc terms))
        (derivable_subterms_underapproximate_keys root_know root_term))
      (decreases term_list_size terms) =
  let root_subterms = derivable_subterms_underapproximate_keys root_know root_term in
  let new_subterms, pending = derivable_subterms_helper_round current_know terms in
  let total_subterms = acc @ new_subterms in
  derivable_subterms_helper_round_components_subset_underapprox_list current_know terms;
  assert (Set.subset (Set.as_set new_subterms) root_subterms);
  as_set_append_left_subset acc new_subterms;
  as_set_append_right_subset acc new_subterms;
  set_subset_union (Set.as_set acc) (Set.as_set new_subterms) root_subterms;
  as_set_append_subset acc new_subterms root_subterms;
  assert (Set.subset (Set.as_set total_subterms) root_subterms);
  if pending = terms
  then (
    derivable_subterms_helper_round_no_progress_terms_subset_underapprox_list current_know terms;
    set_subset_transitive (Set.as_set terms) (derivable_subterms_underapproximate_keys_list current_know terms) root_subterms;
    as_set_append_left_subset total_subterms pending;
    as_set_append_right_subset total_subterms pending;
    set_subset_union (Set.as_set total_subterms) (Set.as_set pending) root_subterms;
    as_set_append_subset total_subterms pending root_subterms;
    assert (Set.subset (Set.as_set (total_subterms @ pending)) root_subterms)
  )
  else (
    let next_know = Seq.append current_know (Seq.seq_of_list total_subterms) in
    assert (forall x. Set.mem x (Set.as_set total_subterms) ==> built_with_subterms root_know root_subterms x);
      let private_key_stability (key: priv_key)
        : Lemma
          (requires derivable next_know (PrivKey key))
          (ensures derivable root_know (PrivKey key)) =
        private_key_derivable_from_context_and_observed_list_already_derivable
          root_know current_know root_term total_subterms key
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires private_key_stability);
      assert (forall key. derivable next_know (PrivKey key) ==> derivable root_know (PrivKey key));
    derivable_subterms_underapproximate_keys_list_monotone_knowledge next_know root_know pending;
    assert (Set.subset
      (derivable_subterms_underapproximate_keys_list current_know pending)
      (derivable_subterms_underapproximate_keys_list current_know terms));
    assert (Set.subset (derivable_subterms_underapproximate_keys_list current_know pending) root_subterms);
      derivable_subterms_helper_round_pending_terms_subset_underapprox_list current_know terms;
      assert (pending == derivable_subterms_helper_round_pending current_know terms);
      set_subset_transitive
        (Set.as_set pending)
        (derivable_subterms_underapproximate_keys_list current_know pending)
        root_subterms;
      derivable_subterms_underapproximate_keys_list_transitive root_know root_term pending;
    set_subset_transitive
      (derivable_subterms_underapproximate_keys_list next_know pending)
        (derivable_subterms_underapproximate_keys_list root_know pending)
      root_subterms;
    assert (Set.subset (derivable_subterms_underapproximate_keys_list next_know pending) root_subterms);
      let derivable_stability (x: term)
        : Lemma
          (requires derivable next_know x)
          (ensures built_with_subterms root_know root_subterms x) =
        let p: derivation -> prop =
          fun d -> derive d next_know = Some x in
        let d = FStar.IndefiniteDescription.indefinite_description_ghost derivation p in
        derivable_from_context_and_observed_list_built_from_underapprox
          root_know current_know root_term total_subterms d x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires derivable_stability);
      assert (forall x. derivable next_know x ==> built_with_subterms root_know root_subterms x);
    derivable_subterms_helper_subset_underroot root_know next_know root_term total_subterms pending
  )

#pop-options

let derivable_subterms_underapproximate_keys_exact_with_no_privkeys
      (know: knowledge term)
      (t: term)
    : Lemma
      (requires no_private_key_subterms (derivable_subterms_underapproximate_keys know t))
      (ensures Set.equal
        (derivable_subterms_underapproximate_keys know t)
        (derivable_subterms know t)) =
  derivable_subterms_underapproximate_keys_subset_derivable_subterms know t;
  assert (forall x. derivable know x ==> built_with_subterms know (derivable_subterms_underapproximate_keys know t) x);
  derivable_subterms_underapproximate_keys_list_singleton know t;
  derivable_subterms_helper_subset_underroot know know t [] [t];
  assert (Set.subset (derivable_subterms know t) (derivable_subterms_underapproximate_keys know t));
  Set.lemma_equal_intro
    (derivable_subterms_underapproximate_keys know t)
    (derivable_subterms know t)

let rec derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
      (know: knowledge term)
      (observed_term: term)
      (d: derivation)
      (derived_term: term)
    : Lemma
      (requires
        no_private_key_subterms (derivable_subterms_underapproximate_keys know observed_term) /\
        derive d (Seq.snoc know observed_term) = Some derived_term)
      (ensures built_with_subterms know (derivable_subterms_underapproximate_keys know observed_term) derived_term) =
  let subterms = derivable_subterms_underapproximate_keys know observed_term in
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know derived_term)
  then ()
  else
    match d with
    | DeriveObserved observed_index ->
      if observed_index < Seq.length know
      then (
        assert (derive d know = Some derived_term);
        exists_intro (fun d' -> derive d' know = Some derived_term) d;
        assert false
      )
      else if observed_index = Seq.length know
      then (
        assert (derived_term == observed_term);
        observed_term_built_from_derivable_subterms_underapproximate_keys know observed_term
      )
      else (
        assert (derive d (Seq.snoc know observed_term) = None);
        assert false
      )
    | DeriveAEncrypt plaintext_derivation key_derivation ->
      (match
          derive plaintext_derivation (Seq.snoc know observed_term),
          derive key_derivation (Seq.snoc know observed_term)
        with
        | Some plaintext, Some (PubKey key) ->
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term plaintext_derivation plaintext;
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term key_derivation (PubKey key);
          assert (derived_term == Aenc plaintext key)
        | _, _ -> ())
    | DeriveADecrypt ciphertext_derivation key_derivation ->
      (match
          derive ciphertext_derivation (Seq.snoc know observed_term),
          derive key_derivation (Seq.snoc know observed_term)
        with
        | Some (Aenc plaintext key1), Some (PrivKey key2) ->
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term key_derivation (PrivKey key2);
          private_key_built_from_subterms_already_derivable know subterms key2;
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term ciphertext_derivation (Aenc plaintext key1);
          if key1 = key2
          then (
            assert (derived_term == plaintext);
            built_from_derivable_subterms_underapproximate_keys_aenc_plaintext know observed_term plaintext key1
          )
          else (
            assert (derive d (Seq.snoc know observed_term) = None);
            assert false
          )
        | _, _ -> ())
    | DerivePair left_derivation right_derivation ->
      (match
          derive left_derivation (Seq.snoc know observed_term),
          derive right_derivation (Seq.snoc know observed_term)
        with
        | Some left, Some right ->
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term left_derivation left;
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term right_derivation right;
          assert (derived_term == Pair left right)
        | _, _ -> ())
    | DerivePairLeft pair_derivation ->
      (match derive pair_derivation (Seq.snoc know observed_term) with
        | Some (Pair left right) ->
          assert (derived_term == left);
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term pair_derivation (Pair left right);
          derivable_subterms_underapproximate_keys_no_pair know observed_term left right;
          built_from_subterms_pair_left know subterms left right
        | _ -> ())
    | DerivePairRight pair_derivation ->
      (match derive pair_derivation (Seq.snoc know observed_term) with
        | Some (Pair left right) ->
          assert (derived_term == right);
          derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
            know observed_term pair_derivation (Pair left right);
          derivable_subterms_underapproximate_keys_no_pair know observed_term left right;
          built_from_subterms_pair_right know subterms left right
        | _ -> ())

let derivable_from_observed_term_without_private_key_subterms
      (know: knowledge term)
      (observed_term: term)
      (d: derivation)
      (derived_term: term)
    : Lemma
      (requires
        no_private_key_subterms (derivable_subterms_underapproximate_keys know observed_term) /\
        derive d (Seq.snoc know observed_term) = Some derived_term)
      (ensures built_with_subterms know (derivable_subterms know observed_term) derived_term) =
  derivable_subterms_underapproximate_keys_exact_with_no_privkeys know observed_term;
  assert (Set.equal
    (derivable_subterms know observed_term)
    (derivable_subterms_underapproximate_keys know observed_term));
  derivable_from_observed_term_without_private_key_subterms_underapproximate_keys
    know observed_term d derived_term

let statically_equivalent_length (impl_know ideal_know: knowledge term)
  : Lemma
    (requires statically_equivalent adversary_aenc impl_know ideal_know)
    (ensures Seq.length impl_know == Seq.length ideal_know)
= assert (forall i. (i < Seq.length impl_know) == Some? (adversary_aenc.derive (DeriveObserved i) impl_know))
