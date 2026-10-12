module MA.Adversary

open SymbolicTypes

open AencTerms

open AdversaryAenc

open MA.Types

module Set = FStar.Set


(** Adversary for mutual authentication protocols using asymmetric encryption and decryption. *)

let adv = adversary_aenc


(**
  Newly derivable terms after observing the `Aenc (Pair (SessionId session) m)
  k` terms used by the mutual authentication network messages.  The session id
  is intentionally encrypted with the message payload: otherwise an adversary
  could reuse the same opaque ciphertext under a different public session tag,
  making the peers authenticate the same run under different session ids.
*)
let derivable_from_session_encrypted_term_without_key
			(know: knowledge term)
			(session: session_id)
			(m: term)
			(k: priv_key)
			(d: derivation)
			(derived_term: term)
		: Lemma
			(requires
				(~(derivable know (PrivKey k))) /\
				(derive d (Seq.snoc know (Aenc (Pair (SessionId session) m) k)) = Some derived_term))
			(ensures built_with_subterms know (Set.as_set [Aenc (Pair (SessionId session) m) k]) derived_term) =
	assert (Set.equal
		(derivable_subterms_underapproximate_keys know (Aenc (Pair (SessionId session) m) k))
		(Set.as_set [Aenc (Pair (SessionId session) m) k]));
	assert (no_private_key_subterms (Set.as_set [Aenc (Pair (SessionId session) m) k]));
	derivable_subterms_underapproximate_keys_exact_with_no_privkeys know (Aenc (Pair (SessionId session) m) k);
	assert (Set.equal
		(derivable_subterms know (Aenc (Pair (SessionId session) m) k))
		(Set.as_set [Aenc (Pair (SessionId session) m) k]));
	derivable_from_observed_term_without_private_key_subterms know (Aenc (Pair (SessionId session) m) k) d derived_term

(**
  Corollary of `derivable_from_session_encrypted_term_without_key` that ensures
  any newly derivable nonces must have already been known.
*)
let nonces_learned_from_session_ciphertext_already_derivable
			(know: knowledge term)
			(session: session_id)
			(m: term)
			(k: priv_key)
			(n: nonce)
			(d: derivation)
		: Lemma
			(requires
				(~(derivable know (PrivKey k))) /\
				(derive d (Seq.snoc know (Aenc (Pair (SessionId session) m) k)) = Some (Nonce n)))
			(ensures derivable know (Nonce n)) =
	derivable_from_session_encrypted_term_without_key know session m k d (Nonce n);
	assert (~(Set.mem (Nonce n) (Set.as_set [Aenc (Pair (SessionId session) m) k])))

(**
	Newly derivable terms after observing the public authenticated output term.
	Since this output contains only a session id and participant ids, it cannot
	expose private keys or nonces except by reusing old knowledge.
*)
let derivable_from_public_output_term
			(know: knowledge term)
			(session: session_id)
			(party peer: participant_id)
			(d: derivation)
			(derived_term: term)
		: Lemma
			(requires
				derive d (Seq.snoc know (ma_authenticated_term session party peer)) = Some derived_term)
			(ensures
				built_with_subterms know
					(Set.as_set [SessionId session; ParticipantId party; ParticipantId peer])
					derived_term) =
	assert (Set.equal
		(derivable_subterms_underapproximate_keys know (ma_authenticated_term session party peer))
		(Set.as_set [SessionId session; ParticipantId party; ParticipantId peer]));
	assert (no_private_key_subterms
		(Set.as_set [SessionId session; ParticipantId party; ParticipantId peer]));
	derivable_subterms_underapproximate_keys_exact_with_no_privkeys
		know (ma_authenticated_term session party peer);
	assert (Set.equal
		(derivable_subterms know (ma_authenticated_term session party peer))
		(Set.as_set [SessionId session; ParticipantId party; ParticipantId peer]));
	derivable_from_observed_term_without_private_key_subterms
		know (ma_authenticated_term session party peer) d derived_term

(**
  Corollary of `derivable_from_public_output_term` that ensures any newly derivable
  private keys must have already been known.
*)
let private_keys_learned_from_public_output_already_derivable
			(know: knowledge term)
			(session: session_id)
			(party peer: participant_id)
			(k: priv_key)
			(d: derivation)
		: Lemma
			(requires
				derive d (Seq.snoc know (ma_authenticated_term session party peer)) = Some (PrivKey k))
			(ensures derivable know (PrivKey k)) =
	derivable_from_public_output_term know session party peer d (PrivKey k);
	assert (~(Set.mem (PrivKey k)
		(Set.as_set [SessionId session; ParticipantId party; ParticipantId peer])))

(**
  Corollary of `derivable_from_public_output_term` that ensures any newly derivable
  nonces must have already been known.
*)
let nonces_learned_from_public_output_already_derivable
			(know: knowledge term)
			(session: session_id)
			(party peer: participant_id)
			(n: nonce)
			(d: derivation)
		: Lemma
			(requires
				derive d (Seq.snoc know (ma_authenticated_term session party peer)) = Some (Nonce n))
			(ensures derivable know (Nonce n)) =
	derivable_from_public_output_term know session party peer d (Nonce n);
	assert (~(Set.mem (Nonce n)
		(Set.as_set [SessionId session; ParticipantId party; ParticipantId peer])))


(**
	Any nonce that is derivable from the knowledge must be contained in the set of
  used nonces.
*)
let rec nonce_in_derived_term_implies_in_knowledge_nonces
      (know: knowledge term)
      (n: nonce)
			(t: term)
      (d: derivation)
    : Lemma
      (requires
				derive d know == Some t
				/\ Set.mem n (ma_term_nonces t)
			)
      (ensures Set.mem n (ma_knowledge_nonces know))
			(decreases d) =
	match d with
	| DeriveObserved idx ->
		ma_knowledge_nonces_index know idx t
	| DeriveAEncrypt d_plaintext d_key ->
		let t' = Some?.v (derive d_plaintext know) in
		assert (Set.mem n (ma_term_nonces t'));
		nonce_in_derived_term_implies_in_knowledge_nonces know n t' d_plaintext
	| DeriveADecrypt d_ciphertext d_key ->
		let t_ciphertext = Some?.v (derive d_ciphertext know) in
		nonce_in_derived_term_implies_in_knowledge_nonces know n t_ciphertext d_ciphertext
	| DerivePair d_left d_right ->
		let t_left = Some?.v (derive d_left know) in
		let t_right = Some?.v (derive d_right know) in
		if Set.mem n (ma_term_nonces t_left)
		then nonce_in_derived_term_implies_in_knowledge_nonces know n t_left d_left
		else nonce_in_derived_term_implies_in_knowledge_nonces know n t_right d_right
	| DerivePairLeft d_pair
	| DerivePairRight d_pair ->
		let t_pair = Some?.v (derive d_pair know) in
		nonce_in_derived_term_implies_in_knowledge_nonces know n t_pair d_pair

(**
  Inversion lemma for ciphertext provenance.  If the ciphertext `Aenc p k`
  occurs (reachable by `aenc_subterm`) inside some derived term `t`, but its
  plaintext `p` is *not* itself derivable, then `Aenc p k` could not have been
  freshly built by the adversary (asymmetric encryption requires deriving the
  plaintext).  Hence it must occur in an *observed* knowledge element.
*)
#push-options "--fuel 2 --ifuel 2"
let rec aenc_subterm_in_derived_implies_observed
      (know: knowledge term)
      (p: term)
      (k: priv_key)
      (t: term)
      (d: derivation)
    : Lemma
      (requires
        derive d know == Some t /\
        aenc_subterm (Aenc p k) t /\
        ~(derivable know p))
      (ensures
        (exists (idx: nat). idx < Seq.length know /\
          aenc_subterm (Aenc p k) (Seq.index know idx)))
      (decreases d) =
  match d with
  | DeriveObserved idx ->
    introduce exists (i: nat). i < Seq.length know /\
      aenc_subterm (Aenc p k) (Seq.index know i)
    with idx and ()
  | DeriveAEncrypt d_p d_k ->
    let pt = Some?.v (derive d_p know) in
    if Aenc p k = t then
      // t == Aenc pt _, so p == pt is derivable via d_p — contradicts ~derivable
      assert (derive d_p know == Some p)
    else
      (assert (aenc_subterm (Aenc p k) pt);
       aenc_subterm_in_derived_implies_observed know p k pt d_p)
  | DeriveADecrypt d_c d_k ->
    let c = Some?.v (derive d_c know) in   // c == Aenc t _
    assert (aenc_subterm (Aenc p k) c);
    aenc_subterm_in_derived_implies_observed know p k c d_c
  | DerivePair d_l d_r ->
    let tl = Some?.v (derive d_l know) in
    let tr = Some?.v (derive d_r know) in
    if aenc_subterm (Aenc p k) tl
    then aenc_subterm_in_derived_implies_observed know p k tl d_l
    else aenc_subterm_in_derived_implies_observed know p k tr d_r
  | DerivePairLeft d_pair
  | DerivePairRight d_pair ->
    let pr = Some?.v (derive d_pair know) in   // pr == Pair _ _
    assert (aenc_subterm (Aenc p k) pr);
    aenc_subterm_in_derived_implies_observed know p k pr d_pair
#pop-options
