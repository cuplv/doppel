module AdversarySenc

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
  | DeriveSEncrypt plaintext_derivation key_derivation ->
    append_preserves_derive plaintext_derivation know1 know2;
    append_preserves_derive key_derivation know1 know2
  | DeriveSDecrypt ciphertext_derivation key_derivation ->
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
  | DeriveSEncrypt pt kd ->
    replace_observed_derivation_eq know observed_term replacement pt;
    replace_observed_derivation_eq know observed_term replacement kd
  | DeriveSDecrypt ct kd ->
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
  let d = FStar.IndefiniteDescription.indefinite_description_ghost derivation p_d in
  replace_observed_derivation_eq know t replacement d;
  exists_intro (fun d' -> derive d' know = Some t')
    (replace_observed_derivation (Seq.length know) replacement d)



let rec derivable_from_encrypted_term_without_key
      (know: knowledge term)
      (m: term)
      (k: key)
      (d: derivation)
      (derived_term: term)
    : Lemma
      (requires
        (~(derivable know (Key k))) /\ (derive d (Seq.snoc know (Senc m k)) = Some derived_term))
      (ensures built_from_know_and_ciphertext know m k derived_term) =
  let open FStar.IndefiniteDescription in
  if strong_excluded_middle (derivable know derived_term)
  then ()
  else
    (match d with
      | DeriveObserved observed_index ->
        (if observed_index < Seq.length know
          then
            (assert (derive d know = Some derived_term);
              exists_intro (fun d' -> derive d' know = Some derived_term) d;
              assert (derivable know derived_term);
              assert false)
          else
            if observed_index = Seq.length know
            then
              (assert (derived_term = Senc m k);
                ())
            else
              (assert (derive d (Seq.snoc know (Senc m k)) = None);
                assert false))
      | DeriveSEncrypt plaintext_derivation key_derivation ->
        (match
            derive plaintext_derivation (Seq.snoc know (Senc m k)),
            derive key_derivation (Seq.snoc know (Senc m k))
          with
          | Some plaintext, Some (Key key') ->
            (derivable_from_encrypted_term_without_key know m k key_derivation (Key key');
              assert (derivable know (Key key'));
              derivable_from_encrypted_term_without_key know m k plaintext_derivation plaintext;
              assert (derived_term == Senc plaintext key');
              ())
          | _, _ -> ())
      | DeriveSDecrypt ciphertext_derivation key_derivation ->
        (match
            derive ciphertext_derivation (Seq.snoc know (Senc m k)),
            derive key_derivation (Seq.snoc know (Senc m k))
          with
          | Some (Senc plaintext key1), Some (Key key2) ->
            (derivable_from_encrypted_term_without_key know m k key_derivation (Key key2);
              assert (derivable know (Key key2));
              derivable_from_encrypted_term_without_key know
                m
                k
                ciphertext_derivation
                (Senc plaintext key1);
              if key1 = key2
              then
                (assert (derived_term == plaintext);
                  if strong_excluded_middle (derivable know (Senc plaintext key1))
                  then
                    (let p_c: derivation -> prop =
                        (fun d' -> derive d' know = Some (Senc plaintext key1))
                      in
                      let d_c =
                        FStar.IndefiniteDescription.indefinite_description_ghost derivation p_c
                      in
                      let p_k: derivation -> prop = (fun d' -> derive d' know = Some (Key key2)) in
                      let d_k =
                        FStar.IndefiniteDescription.indefinite_description_ghost derivation p_k
                      in
                      assert (derive (DeriveSDecrypt d_c d_k) know = Some plaintext);
                      exists_intro (fun d' -> derive d' know = Some plaintext)
                        (DeriveSDecrypt d_c d_k);
                      ())
                  else
                    if Senc plaintext key1 = Senc m k
                    then
                      (assert (key1 == k);
                        assert (derivable know (Key k));
                        assert false))
              else
                (assert (derive d (Seq.snoc know (Senc m k)) = None);
                  assert false))
          | _, _ -> ())
      | DerivePair left_derivation right_derivation ->
        (match
            derive left_derivation (Seq.snoc know (Senc m k)),
            derive right_derivation (Seq.snoc know (Senc m k))
          with
          | Some left, Some right ->
            (derivable_from_encrypted_term_without_key know m k left_derivation left;
              derivable_from_encrypted_term_without_key know m k right_derivation right;
              assert (derived_term == Pair left right);
              ())
          | _, _ -> ())
      | DerivePairLeft pair_derivation ->
        (match derive pair_derivation (Seq.snoc know (Senc m k)) with
          | Some (Pair left right) ->
            (assert (derived_term == left);
              derivable_from_encrypted_term_without_key know
                m
                k
                pair_derivation
                (Pair left right);
              // Pair left right <> Senc m k (different constructors), so third disjunct
              // of built_from holds: built_from ... left /\ built_from ... right.
              // SMT extracts built_from ... left = built_from ... derived_term.
              if strong_excluded_middle (derivable know (Pair left right))
              then
                (let p_pair: derivation -> prop =
                    (fun d' -> derive d' know = Some (Pair left right))
                  in
                  let d_pair =
                    FStar.IndefiniteDescription.indefinite_description_ghost derivation p_pair
                  in
                  assert (derive (DerivePairLeft d_pair) know = Some left);
                  exists_intro (fun d' -> derive d' know = Some left) (DerivePairLeft d_pair);
                  ()))
          | _ -> ())
      | DerivePairRight pair_derivation ->
        (match derive pair_derivation (Seq.snoc know (Senc m k)) with
          | Some (Pair left right) ->
            (assert (derived_term == right);
              derivable_from_encrypted_term_without_key know
                m
                k
                pair_derivation
                (Pair left right);
              // Symmetric to DerivePairLeft: third disjunct gives built_from ... right.
              if strong_excluded_middle (derivable know (Pair left right))
              then
                (let p_pair: derivation -> prop =
                    (fun d' -> derive d' know = Some (Pair left right))
                  in
                  let d_pair =
                    FStar.IndefiniteDescription.indefinite_description_ghost derivation p_pair
                  in
                  assert (derive (DerivePairRight d_pair) know = Some right);
                  exists_intro (fun d' -> derive d' know = Some right) (DerivePairRight d_pair);
                  ()))
          | _ -> ()))

let keys_learned_from_ciphertext_already_derivable
      (know: knowledge term)
      (m: term)
      (k k': key)
      (d: derivation)
    : Lemma
      (requires
        (~(derivable know (Key k))) /\ (derive d (Seq.snoc know (Senc m k)) = Some (Key k')))
      (ensures derivable know (Key k')) =
  // derivable_from_encrypted_term_without_key gives:
  //   built_from_know_and_ciphertext know m k (Key k')
  // which expands to:
  //   derivable know (Key k') \/ Key k' == Senc m k \/ (match Key k' with ... | _ -> False)
  // The second and third disjuncts are impossible (Key ≠ Senc by constructor discrimination),
  // so derivable know (Key k') must hold.
  derivable_from_encrypted_term_without_key know m k d (Key k')


let statically_equivalent_length (impl_know ideal_know: knowledge term)
  : Lemma
    (requires statically_equivalent adversary_senc impl_know ideal_know)
    (ensures Seq.length impl_know == Seq.length ideal_know)
= assert (forall i. (i < Seq.length impl_know) == Some? (adversary_senc.derive (DeriveObserved i) impl_know))
