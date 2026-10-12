module SMD.ImplementationInvariants

open SymbolicTypes
open TestedSystem

open SMD.Implementation

open SMD.Adversary
open SMD.TestedProtocols

open AdversarySenc

module PartialMap = FStar.PartialMap

module Set = FStar.Set

module Seq = FStar.Seq

let smd_impl_send_effect
      (session: session_id)
      (message: term)
      (state new_state: impl_system_state)
    : prop =
  smd_impl_protocol_send_enabled (s2p_state state) session message state.internal.key /\
  s2p_state new_state == smd_impl_protocol_send_state (s2p_state state) session message /\
  new_state.know == Seq.snoc state.know (Senc (Pair (SessionId session) message) state.internal.key)

let smd_impl_receive_effect
      (session: session_id)
      (message: term)
      (state new_state: impl_system_state)
    : prop =
  smd_impl_protocol_receive_enabled (s2p_state state) session message /\
  s2p_state new_state == smd_impl_protocol_receive_state (s2p_state state) session message /\
  new_state.know == Seq.snoc state.know (Pair (SessionId session) message)

let _cannot_derive_secret_key_after_send
      (session: session_id)
      (trigger_message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_send_effect session trigger_message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) trigger_message))
      (ensures adv.derive d new_state.know <> Some (Key state.internal.key)) =
  let trigger_input = Pair (SessionId session) trigger_message in
  match adv.derive d new_state.know with
  | Some t ->
    if t = Key state.internal.key
    then
      derivable_from_encrypted_term_without_key state.know
        trigger_input
        state.internal.key
        d
        (Key state.internal.key)
  | _ -> ()

let rec _send_preserves_impl_invariant_cannot_derive_response_before_send
      (session: session_id)
      (trigger_message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (valid_response derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_send_effect session trigger_message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) trigger_message) /\
        is_receive_trigger_for_session quantified_session new_state.internal.key valid_response /\
        (adv.derive d new_state.know = Some derived_term) /\
        in_term derived_term valid_response)
      (ensures Set.mem quantified_session new_state.internal.sent_sessions) =
  let sent_term = Senc (Pair (SessionId session) trigger_message) state.internal.key in
  assert (new_state.internal.key == state.internal.key);
  match d with
  | DeriveObserved i ->
    if i = Seq.length state.know
    then
      (assert (adv.derive d new_state.know = Some sent_term);
        assert (derived_term == sent_term);
        if session = quantified_session
        then ()
        else (assert (in_term (Pair (SessionId session) trigger_message) valid_response)))
  | DeriveSEncrypt derive_plaintext derive_key ->
    if adv.derive derive_key new_state.know = Some (Key new_state.internal.key)
    then
      // Contradiction: the adversary cannot derive the secret key, so the
      // adversary could not derive a valid response through encryption.
      _cannot_derive_secret_key_after_send
        session
        trigger_message
        trigger_derivation
        state
        new_state
        derive_key
    else
      (match
          adv.derive derive_key new_state.know, adv.derive derive_plaintext new_state.know
        with
        | Some (Key key), Some m ->
          // Inductive hypothesis ensures that if `valid_response` is in the
          // derived plaintext, then a message must have been sent for the
          // `quantified_session`. One of the premises for this lemma is that
          // `valid_response` is in `enc(m,key)`, which is equivalent to
          // `derived_term` for this case. Since in this case `key` is not the
          // secret key used by the protocol, `valid_response` must also be in
          // the derived plaintext. Therefore the inductive hypothesis is
          // sufficient for this case.
          _send_preserves_impl_invariant_cannot_derive_response_before_send session
            trigger_message
            trigger_derivation
            state
            new_state
            derive_plaintext
            quantified_session
            valid_response
            m
        | _, _ -> ())
  | DeriveSDecrypt derive_ciphertext derive_key ->
    (match adv.derive derive_ciphertext new_state.know with
      | Some ciphertext ->
        // Inductive hypothesis ensures that if `valid_response` is in the
        // derived ciphertext, then a message must have been sent for the
        // `quantified_session`. One of the premises for this lemma is that
        // `valid_response` is in `m`, which is equivalent to `derived_term` for
        // this case, so `valid_response` must also be in the derived
        // ciphertext. Therefore the inductive hypothesis is sufficient for this
        // case.
        (_send_preserves_impl_invariant_cannot_derive_response_before_send session
          trigger_message
            trigger_derivation
            state
            new_state
            derive_ciphertext
            quantified_session
            valid_response
            ciphertext)
      | _ -> ())
  | DerivePair derive_left derive_right ->
    (match
        adv.derive derive_left new_state.know, adv.derive derive_right new_state.know
      with
      | Some left, Some right ->
        // If `valid_response` is in `Pair left right`, then it must be in
        // either `left` or `right`. The inductive hypotheses ensure that in
        // either case, a message must have been sent for the
        // `quantified_session`.
        if in_term left valid_response
        then
          _send_preserves_impl_invariant_cannot_derive_response_before_send session
            trigger_message
            trigger_derivation
            state
            new_state
            derive_left
            quantified_session
            valid_response
            left
        else
          if in_term right valid_response
          then
            _send_preserves_impl_invariant_cannot_derive_response_before_send session
              trigger_message
              trigger_derivation
              state
              new_state
              derive_right
              quantified_session
              valid_response
              right
      | _, _ -> ())
  | DerivePairLeft derive_pair
  | DerivePairRight derive_pair ->
    (match adv.derive derive_pair new_state.know with
      | Some (Pair left right) ->
        // Inductive hypothesis ensures that if `valid_response` is in `Pair
        // left right`, then a message must have been sent for the
        // `quantified_session`. One of the premises for this lemma is that
        // `valid_response` is in `left` (or `right`), which is equivalent to
        // `derived_term` for this case, so `valid_response` must also be in
        // `Pair left right`. Therefore the inductive hypothesis is sufficient
        // for this case.
        (_send_preserves_impl_invariant_cannot_derive_response_before_send session
          trigger_message
            trigger_derivation
            state
            new_state
            derive_pair
            quantified_session
            valid_response
            (Pair left right))
      | _ -> ())

let rec _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge
      (session: session_id)
      (trigger_message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (quantified_message derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_send_effect session trigger_message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) trigger_message) /\
        (adv.derive d new_state.know == Some derived_term) /\
        // If a derived term contains a valid response for the quantified session...
        (in_term derived_term
            (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key)))
      (ensures
        // ... then the response must have come from the protocol so the message
        // needed to construct that valid response must already be derivable
        // (since it must have been used to trigger the send transition for that
        // session).
        derivable new_state.know (Pair (SessionId quantified_session) quantified_message)) =
  let valid_response =
    (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key)
  in
  let sent_term = Senc (Pair (SessionId session) trigger_message) state.internal.key in
  assert (new_state.internal.key == state.internal.key);
  match d with
  | DeriveObserved i ->
    if i = Seq.length state.know
    then
      // The derived term is exactly the newly appended ciphertext.
      (assert (adv.derive d new_state.know = Some sent_term);
        assert (derived_term == sent_term);
        if session = quantified_session && trigger_message = quantified_message
        then
          // Exact-match case: the newly appended ciphertext is exactly the
          // quantified valid response, so the quantified pair is the same
          // trigger pair that was already derivable in `state`.
          (assert (adv.derive trigger_derivation state.know =
                Some (Pair (SessionId quantified_session) quantified_message));
            assert (derivable state.know
                  (Pair (SessionId quantified_session) quantified_message));
            assert (new_state.know == Seq.snoc state.know sent_term);
            ())
        else
          // Nested-subterm case: the quantified valid response cannot
          // appear inside of the session id, so it must appear inside of the
          // trigger message. Since that trigger message is derivable in
          // `state`, the invariant ensures that the quantified pair is too.
          (assert (in_term derived_term valid_response);
            assert (in_term (Pair (SessionId session) trigger_message) valid_response);
            assert (in_term trigger_message valid_response);
            assert (adv.derive (DerivePairRight trigger_derivation) state.know =
                Some trigger_message);
            assert (derivable state.know trigger_message);
            assert (impl_invariant_to_be_delivered_messages_in_knowledge state);
            assert (in_term trigger_message
                  (Senc (Pair (SessionId quantified_session) quantified_message) state.internal.key) /\
                derivable state.know trigger_message);
            assert (derivable state.know
                  (Pair (SessionId quantified_session) quantified_message));
            assert (new_state.know == Seq.snoc state.know sent_term);
            ()))
    else
      // The `derived_term` is from the previous knowledge, and the set of
      // derivable terms and derivations monotonically increases, so the
      // invariant already ensures that the quantified pair is derivable.
      (append_preserves_derive d
          state.know
          (Seq.create 1 sent_term);
        assert (adv.derive d state.know = Some derived_term);
        assert (in_term derived_term
              (Senc (Pair (SessionId quantified_session) quantified_message) state.internal.key));
        assert (derivable state.know derived_term);
        assert (impl_invariant_to_be_delivered_messages_in_knowledge state);
        assert (in_term derived_term valid_response /\ derivable state.know derived_term);
        assert (derivable state.know
              (Pair (SessionId quantified_session) quantified_message));
        assert (new_state.know == Seq.snoc state.know sent_term);
        ())
  | DeriveSEncrypt derive_plaintext derive_key ->
    (match
        adv.derive derive_key new_state.know, adv.derive derive_plaintext new_state.know
      with
      | Some (Key key), Some plaintext ->
        (if key = new_state.internal.key
          then
            // Contradiction: the adversary cannot derive the secret key, so the
            // adversary could not derive a valid response through encryption.
            _cannot_derive_secret_key_after_send session
              trigger_message
              trigger_derivation
              state
              new_state
              derive_key
          else
            // Inductive hypothesis ensures that if `valid_response` is in the
            // derived plaintext, then the quantified session and message pair
            // must be derivable. One of the premises for this lemma is that
            // `valid_response` is in `enc(m,key)`, which is equivalent to
            // `derived_term` for this case. Since in this case `key` is not the
            // secret key used by the protocol, `valid_response` must also be in
            // the derived plaintext. Therefore the inductive hypothesis is
            // sufficient for this case.
            _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
              trigger_message
              trigger_derivation
              state
              new_state
              derive_plaintext
              quantified_session
              quantified_message
              plaintext)
      | _, _ -> ())
  | DeriveSDecrypt derive_ciphertext derive_key ->
    (match adv.derive derive_ciphertext new_state.know with
      | Some ciphertext ->
        // Inductive hypothesis ensures that if `valid_response` is in the
        // derived ciphertext, then the quantified session and message pair must
        // be derivable. One of the premises for this lemma is that
        // `valid_response` is in `m`, which is equivalent to `derived_term` for
        // this case, so `valid_response` must also be in the derived
        // ciphertext. Therefore the inductive hypothesis is sufficient for this
        // case.
        _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
          trigger_message
          trigger_derivation
          state
          new_state
          derive_ciphertext
          quantified_session
          quantified_message
          ciphertext
      | _ -> ())
  | DerivePair derive_left derive_right ->
    (match
        adv.derive derive_left new_state.know, adv.derive derive_right new_state.know
      with
      | Some left, Some right ->
        // If `valid_response` is in `Pair left right`, then it must be in
        // either `left` or `right`. The inductive hypotheses ensure that in
        // either case, the quantified session and message pair must be
        // derivable.
        (if in_term left valid_response
          then
            _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
              trigger_message
              trigger_derivation
              state
              new_state
              derive_left
              quantified_session
              quantified_message
              left
          else
            if in_term right valid_response
            then
              _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
                trigger_message
                trigger_derivation
                state
                new_state
                derive_right
                quantified_session
                quantified_message
                right)
      | _, _ -> ())
  | DerivePairLeft derive_pair
  | DerivePairRight derive_pair ->
    (match adv.derive derive_pair new_state.know with
      | Some (Pair left right) ->
        // Inductive hypothesis ensures that if `valid_response` is in `Pair
        // left right`, then the quantified session and message pair must be
        // derivable. One of the premises for this lemma is that
        // `valid_response` is in `left` (or `right`), which is equivalent to
        // `derived_term` for this case, so `valid_response` must also be in
        // `Pair left right`. Therefore the inductive hypothesis is sufficient
        // for this case.
        _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
          trigger_message
          trigger_derivation
          state
          new_state
          derive_pair
          quantified_session
          quantified_message
          (Pair left right)
      | _ -> ())



(**
  Helper: given a witness `idx_state` such that `DeriveObserved idx_state`
  derives `valid_response` in `state.knowledge`, and `new_state.knowledge =
  Seq.snoc state.knowledge enc_term`, produce an existential witness for
  `new_state.knowledge` using `append_preserves_derive`.
*)

let _lift_observed_idx_to_new_state
      (state new_state: impl_system_state)
      (enc_term valid_response: term)
      (idx_state: knowledge_index)
    : Lemma
      (requires
        adv.derive (DeriveObserved idx_state) state.know = Some valid_response /\
        new_state.know == Seq.snoc state.know enc_term)
      (ensures exists idx. adv.derive (DeriveObserved idx) new_state.know = Some valid_response
      ) =
  append_preserves_derive (DeriveObserved idx_state) state.know (Seq.create 1 enc_term);
  assert (adv.derive (DeriveObserved idx_state) new_state.know = Some valid_response);
  FStar.Classical.exists_intro (fun idx ->
        adv.derive (DeriveObserved idx) new_state.know = Some valid_response)
    idx_state

let _inputs_derivable_preserved_by_observation
      (state new_state: impl_system_state)
      (trigger_input observed_term: term)
    : Lemma
      (requires
        (forall (t: term). Bag.mem t state.inputs ==> derivable state.know t) /\
        new_state.inputs == Bag.remove trigger_input state.inputs /\
        new_state.know == Seq.snoc state.know observed_term)
      (ensures forall (t: term). Bag.mem t new_state.inputs ==> derivable new_state.know t) =
  let aux (t: term)
    : Lemma
      (requires Bag.mem t new_state.inputs)
      (ensures derivable new_state.know t) =
    Bag.subset_refl state.inputs;
    Bag.remove_preserves_subset trigger_input state.inputs state.inputs;
    assert (Bag.subset (Bag.remove trigger_input state.inputs) state.inputs);
    assert (Bag.subset new_state.inputs state.inputs);
    Bag.mem_count t new_state.inputs;
    Bag.mem_count t state.inputs;
    assert (Bag.mem t state.inputs);
    assert (derivable state.know t);
    append_preserves_derivable state.know (Seq.create 1 observed_term) t
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let impl_valid_response_is_observed
      (state: impl_system_state)
      (session: session_id)
      (message: term)
      (d: adv.derivation)
      (derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        adv.derive d state.know = Some derived_term /\
        in_term derived_term (Senc (Pair (SessionId session) message) state.internal.key))
      (ensures
        exists (idx: knowledge_index).
          adv.derive (DeriveObserved idx) state.know =
          Some (Senc (Pair (SessionId session) message) state.internal.key)) =
  assert (exists (idx: knowledge_index).
    adv.derive (DeriveObserved idx) state.know =
    Some (Senc (Pair (SessionId session) message) state.internal.key))
  by (
    let open FStar.Tactics.V2 in
    iter (fun b ->
      norm_binding_type
        [delta_only
           [`%impl_invariant_derived_valid_response_equivalent_to_observed_response;
            `%implementation_invariants]]
        b)
      (cur_vars ());
    set_options "--z3rlimit 40";
    smt ()
  )

let _lift_valid_response_observation_to_new_state
      (state new_state: impl_system_state)
      (observed_term: term)
      (session: session_id)
      (message: term)
      (d: adv.derivation)
      (derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        adv.derive d state.know = Some derived_term /\
        in_term derived_term (Senc (Pair (SessionId session) message) state.internal.key) /\
        new_state.internal.key == state.internal.key /\
        new_state.know == Seq.snoc state.know observed_term)
      (ensures
        exists (idx: knowledge_index).
          adv.derive (DeriveObserved idx) new_state.know =
          Some (Senc (Pair (SessionId session) message) new_state.internal.key)) =
  let valid_response = Senc (Pair (SessionId session) message) state.internal.key in
  impl_valid_response_is_observed state session message d derived_term;
  let idx_state =
    FStar.IndefiniteDescription.indefinite_description_ghost knowledge_index
      (fun idx -> adv.derive (DeriveObserved idx) state.know = Some valid_response)
  in
  _lift_observed_idx_to_new_state state new_state observed_term valid_response idx_state

let rec _send_preserves_derived_valid_response_equivalent_to_observed_response
      (session: session_id)
      (trigger_message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (quantified_session: session_id)
      (quantified_message: term)
      (d: adv.derivation)
      (derived_term: term)
    : Lemma
      (requires
        (let valid_response = Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key in
          implementation_invariants state /\
          smd_impl_send_effect session trigger_message state new_state /\
          adv.derive trigger_derivation state.know = Some (Pair (SessionId session) trigger_message) /\
          adv.derive d new_state.know = Some derived_term /\
          in_term derived_term valid_response))
      (ensures
        (let valid_response = Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key in
          exists idx. adv.derive (DeriveObserved idx) new_state.know = Some valid_response)) =
  let valid_response = Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key in
  let enc_term = Senc (Pair (SessionId session) trigger_message) state.internal.key in
  assert (new_state.internal.key == state.internal.key);
  assert (new_state.know == Seq.snoc state.know enc_term);
  match d with
      | DeriveObserved i ->
        if i = Seq.length state.know
        then
          // derived_term = enc_term (the newly appended ciphertext).
          if derived_term = valid_response
          then
            // The ciphertext IS the valid_response: i is the direct witness.
            FStar.Classical.exists_intro (fun idx ->
                  adv.derive (DeriveObserved idx) new_state.know = Some valid_response)
              i
          else
            // enc_term ≠ valid_response but in_term enc_term valid_response.
            // Unfold in_term: enc_term = Senc (Pair (SessionId sid) trigger_message) state.key
            // => in_term trigger_message valid_response (SessionId leaf is irrelevant)
            // trigger_message is derivable in state.knowledge via DerivePairRight trigger_derivation.
            // Apply state invariant to get idx_state in state.knowledge, then lift it.
            (assert (adv.derive (DerivePairRight trigger_derivation) state.know =
                  Some trigger_message);
              assert (in_term (Pair (SessionId session) trigger_message) valid_response);
              assert (in_term trigger_message valid_response);
              _lift_valid_response_observation_to_new_state
                state
                new_state
                enc_term
                quantified_session
                quantified_message
                (DerivePairRight trigger_derivation)
                trigger_message)
        else
          // i < Seq.length state.knowledge: derived_term was already in state.knowledge.
          // Since new_state.knowledge = Seq.snoc = Seq.append ... (Seq.create 1 enc_term),
          // append_preserves_derive establishes adv.derive d state.knowledge = Some derived_term.
          // Apply state invariant and lift the witness.
          (append_preserves_derive d state.know (Seq.create 1 enc_term);
            assert (adv.derive d state.know = Some derived_term);
            _lift_valid_response_observation_to_new_state
              state
              new_state
              enc_term
              quantified_session
              quantified_message
              d
              derived_term)
      | DeriveSEncrypt derive_plaintext derive_key ->
        if adv.derive derive_key new_state.know = Some (Key new_state.internal.key)
        then
          // Contradiction: the adversary cannot derive the secret key.
          _cannot_derive_secret_key_after_send
            session
            trigger_message
            trigger_derivation
            state
            new_state
            derive_key
        else
          // derived_term = Senc m key with key ≠ new_state.key, so derived_term ≠ valid_response,
          // meaning valid_response must be inside m. Recurse on derive_plaintext.
          (match
              adv.derive derive_key new_state.know,
              adv.derive derive_plaintext new_state.know
            with
            | Some (Key key), Some m ->
              assert (in_term m valid_response);
              _send_preserves_derived_valid_response_equivalent_to_observed_response session
                trigger_message
                trigger_derivation
                state
                new_state
                quantified_session
                quantified_message
                derive_plaintext
                m
            | _, _ -> ())
      | DeriveSDecrypt derive_ciphertext derive_key ->
        // derived_term is the plaintext of a decryption; valid_response inside plaintext
        // implies it is inside the ciphertext. Recurse on derive_ciphertext.
        (match adv.derive derive_ciphertext new_state.know with
          | Some ciphertext ->
            assert (in_term ciphertext valid_response);
            _send_preserves_derived_valid_response_equivalent_to_observed_response session
              trigger_message
              trigger_derivation
              state
              new_state
              quantified_session
              quantified_message
              derive_ciphertext
              ciphertext
          | _ -> ())
      | DerivePair derive_left derive_right ->
        // derived_term = Pair left right; valid_response is in left or right.
        (match
            adv.derive derive_left new_state.know, adv.derive derive_right new_state.know
          with
          | Some left, Some right ->
            if in_term left valid_response
            then
              _send_preserves_derived_valid_response_equivalent_to_observed_response session
                trigger_message
                trigger_derivation
                state
                new_state
                quantified_session
                quantified_message
                derive_left
                left
            else
              _send_preserves_derived_valid_response_equivalent_to_observed_response session
                trigger_message
                trigger_derivation
                state
                new_state
                quantified_session
                quantified_message
                derive_right
                right
          | _, _ -> ())
      | DerivePairLeft dp ->
        (match adv.derive dp new_state.know with
          | Some (Pair left right) ->
            _send_preserves_derived_valid_response_equivalent_to_observed_response session
              trigger_message
              trigger_derivation
              state
              new_state
              quantified_session
              quantified_message
              dp
              (Pair left right)
          | _ -> ())
      | DerivePairRight dp ->
        (match adv.derive dp new_state.know with
          | Some (Pair left right) ->
            _send_preserves_derived_valid_response_equivalent_to_observed_response session
              trigger_message
              trigger_derivation
              state
              new_state
              quantified_session
              quantified_message
              dp
              (Pair left right)
          | _ -> ())

let implementation_invariants_preserved_after_send
      (session: session_id)
      (trigger_message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
    : Lemma
      (requires
        implementation_invariants state /\
        (forall (t: term). Bag.mem t state.inputs ==> derivable state.know t) /\        smd_impl_send_effect session trigger_message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) trigger_message))
      (ensures implementation_invariants new_state) =
  let sent_term = Senc (Pair (SessionId session) trigger_message) state.internal.key in
  assert (new_state.internal.key == state.internal.key);
  assert (new_state.know == Seq.snoc state.know sent_term);
    let _helper_cannot_derive_secret_key_after_send (d: adv.derivation)
        : // Auxiliary helper lemma that just instantiates the
        // `_cannot_derive_secret_key_after_send` lemma with the given
        // derivation. Used to guide instantiation for the SMT solver.
        Lemma (ensures adv.derive d new_state.know <> Some (Key state.internal.key))
          [SMTPat (adv.derive d new_state.know)] =
      _cannot_derive_secret_key_after_send session
        trigger_message
        trigger_derivation
        state
        new_state
        d
    in
    assert (impl_invariant_secret_key_not_derivable new_state);
    let _helper_send_preserves_impl_invariant_cannot_derive_response_before_send
          (d: adv.derivation)
          (quantified_session: session_id)
          (valid_response derived_term: term)
        : Lemma
          (requires
            is_receive_trigger_for_session quantified_session new_state.internal.key valid_response /\
            (adv.derive d new_state.know = Some derived_term) /\
            in_term derived_term valid_response)
          (ensures Set.mem quantified_session new_state.internal.sent_sessions)
          [
            SMTPat (is_receive_trigger_for_session quantified_session new_state.internal.key valid_response);
            SMTPat (adv.derive d new_state.know);
            SMTPat (in_term derived_term valid_response)
          ] =
      _send_preserves_impl_invariant_cannot_derive_response_before_send session
        trigger_message
        trigger_derivation
        state
        new_state
        d
        quantified_session
        valid_response
        derived_term
    in
    assert (impl_invariant_cannot_derive_response_before_send new_state);
    let _helper_send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge
          (d: adv.derivation)
          (quantified_session: session_id)
          (quantified_message derived_term: term)
        : Lemma
          (requires
            ((adv.derive d new_state.know = Some derived_term) /\
              in_term derived_term
                (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key)))
          (ensures
            derivable new_state.know (Pair (SessionId quantified_session) quantified_message))
          [
            SMTPat (adv.derive d new_state.know);
            SMTPat
            (derivable new_state.know (Pair (SessionId quantified_session) quantified_message));
            SMTPat
            (in_term derived_term
                (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key))
          ] =
      _send_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
        trigger_message
        trigger_derivation
        state
        new_state
        d
        quantified_session
        quantified_message
        derived_term
    in
    assert (impl_invariant_to_be_delivered_messages_in_knowledge new_state);
    FStar.Classical.forall_intro_4
      (FStar.Classical.move_requires_4
        (_send_preserves_derived_valid_response_equivalent_to_observed_response session
          trigger_message
          trigger_derivation
          state
          new_state));
    assert (impl_invariant_derived_valid_response_equivalent_to_observed_response new_state);
    // The send transition updates both sent_sessions and messages in sync,
    // so the new invariant holds trivially: any session in new_state.sent_sessions
    // is either `session` (added this transition, and new_state.messages contains it
    // via PartialMap.upd) or was already in state.sent_sessions (and therefore
    // already in state.messages by the invariant on state).
    assert (impl_invariant_sent_sessions_have_messages new_state);
    // Messages consistent with knowledge: for any derivation d that yields a
    // term containing Senc(Pair(SessionId qs, qm), k) in new_state.knowledge,
    // we need messages[qs] = Some qm.
    let _helper_send_preserves_impl_invariant_messages_consistent_with_knowledge
          (qs: session_id) (qm: term)
          (d: adv.derivation) (derived_term: term)
        : Lemma
          (requires
            adv.derive d new_state.know = Some derived_term /\
            in_term derived_term (Senc (Pair (SessionId qs) qm) new_state.internal.key))
          (ensures PartialMap.sel new_state.internal.messages qs == Some qm)
          [SMTPat (adv.derive d new_state.know);
           SMTPat (in_term derived_term (Senc (Pair (SessionId qs) qm) new_state.internal.key))] =
      // By the already-proved derived_valid_response_equivalent_to_observed_response:
      assert (exists (idx: knowledge_index).
        adv.derive (DeriveObserved idx) new_state.know =
        Some (Senc (Pair (SessionId qs) qm) state.internal.key));
      let idx = FStar.IndefiniteDescription.indefinite_description_ghost knowledge_index
        (fun idx -> adv.derive (DeriveObserved idx) new_state.know =
                    Some (Senc (Pair (SessionId qs) qm) state.internal.key)) in
      let n = Seq.length state.know in
      if idx < n then begin
        // The observation was in old knowledge.
        Seq.lemma_index_app1 state.know (Seq.create 1 sent_term) idx;
        assert (adv.derive (DeriveObserved idx) state.know =
                Some (Senc (Pair (SessionId qs) qm) state.internal.key));
        assert_norm (in_term (Senc (Pair (SessionId qs) qm) state.internal.key)
                             (Senc (Pair (SessionId qs) qm) state.internal.key));
        // Old invariant gives messages[qs] = Some qm in old state.
        assert (PartialMap.sel state.internal.messages qs == Some qm);
        // qs <> session: if qs = session, then by cannot_derive_response_before_send on
        // old state, session ∈ sent_sessions, contradicting send_enabled.
        assert (Set.mem qs state.internal.sent_sessions);
        assert (not (Set.mem session state.internal.sent_sessions));
        assert (qs <> session)
      end else begin
        // The observation is the newly-appended term.
        Seq.lemma_index_app2 state.know (Seq.create 1 sent_term) idx;
        assert (qs == session /\ qm == trigger_message)
      end
    in
    let trigger_input = Pair (SessionId session) trigger_message in
    assert (new_state.inputs == Bag.remove trigger_input state.inputs);
    _inputs_derivable_preserved_by_observation state new_state trigger_input sent_term;
    assert (impl_invariant_messages_consistent_with_knowledge new_state)

let _receive_preserves_impl_invariant_secret_key_not_derivable
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (Pair (SessionId session) message) state.internal.key))
      (ensures adv.derive d new_state.know <> Some (Key state.internal.key)) =
  let trigger_term = Senc (Pair (SessionId session) message) state.internal.key in
  assert (impl_invariant_to_be_delivered_messages_in_knowledge state);
  assert (in_term trigger_term trigger_term);
  assert (exists idx. adv.derive (DeriveObserved idx) state.know = Some trigger_term);
  assert (derivable state.know (Pair (SessionId session) message));
  match adv.derive d new_state.know with
  | Some t -> observe_derivable_no_new_derivations state.know (Pair (SessionId session) message) t
  | _ -> ()

let _receive_preserves_impl_invariant_cannot_derive_response_before_send
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (valid_response derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (Pair (SessionId session) message) state.internal.key) /\
        is_receive_trigger_for_session quantified_session new_state.internal.key valid_response /\
        (adv.derive d new_state.know = Some derived_term) /\
        in_term derived_term valid_response)
      (ensures Set.mem quantified_session new_state.internal.sent_sessions) =
  let trigger_term = Senc (Pair (SessionId session) message) state.internal.key in
  assert (derivable state.know trigger_term);
  assert (in_term trigger_term trigger_term);
  assert (derivable state.know (Pair (SessionId session) message));
  observe_derivable_no_new_derivations state.know (Pair (SessionId session) message) derived_term

let _receive_preserves_impl_invariant_to_be_delivered_messages_in_knowledge
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (quantified_message derived_term: term)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (Pair (SessionId session) message) state.internal.key) /\
        ((adv.derive d new_state.know = Some derived_term) /\
          in_term derived_term
            (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key)))
      (ensures
        derivable new_state.know (Pair (SessionId quantified_session) quantified_message)) =
  let trigger_term = Senc (Pair (SessionId session) message) state.internal.key in
  assert (impl_invariant_to_be_delivered_messages_in_knowledge state);
  assert (in_term trigger_term trigger_term);
  assert (derivable state.know (Pair (SessionId session) message));
  observe_derivable_no_new_derivations state.know (Pair (SessionId session) message) derived_term

let _receive_preserves_impl_invariant_derived_valid_response_equivalent_to_observed_response
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (quantified_message derived_term: term)
    : Lemma
      (requires
        (let valid_response = Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key in
          implementation_invariants state /\
          smd_impl_receive_effect session message state new_state /\
          adv.derive trigger_derivation state.know =
          Some (Senc (Pair (SessionId session) message) state.internal.key) /\
          adv.derive d new_state.know = Some derived_term /\
          in_term derived_term valid_response))
      (ensures
        (let valid_response = Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key in
          exists (idx: knowledge_index).
            adv.derive (DeriveObserved idx) new_state.know = Some valid_response)) =
  let valid_response = Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key in
  let deliver_term = Pair (SessionId session) message in
  assert (new_state.internal.key == state.internal.key);
  assert (new_state.know == Seq.snoc state.know deliver_term);
  assert (impl_invariant_to_be_delivered_messages_in_knowledge state);
  assert (in_term (Senc deliver_term state.internal.key) (Senc deliver_term state.internal.key));
  assert (derivable state.know (Senc deliver_term state.internal.key));
  assert (derivable state.know deliver_term);
  observe_derivable_no_new_derivations state.know deliver_term derived_term;
  assert (derivable state.know derived_term);
  let d_state =
    FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation
      (fun d' -> adv.derive d' state.know = Some derived_term)
  in
  assert (adv.derive d_state state.know = Some derived_term);
  _lift_valid_response_observation_to_new_state
    state
    new_state
    deliver_term
    quantified_session
    quantified_message
    d_state
    derived_term

let implementation_invariants_preserved_after_receive
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: impl_system_state)
    : Lemma
      (requires
        implementation_invariants state /\
        smd_impl_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (Pair (SessionId session) message) state.internal.key))
      (ensures implementation_invariants new_state) =
  let trigger_term = Senc (Pair (SessionId session) message) state.internal.key in
  let deliver_term = Pair (SessionId session) message in
  assert (new_state.internal.key == state.internal.key);
  assert (new_state.know == Seq.snoc state.know deliver_term);
  let _helper_receive_preserves_impl_invariant_secret_key_not_derivable (d: adv.derivation)
        : Lemma (ensures adv.derive d new_state.know <> Some (Key state.internal.key))
          [SMTPat (adv.derive d new_state.know)] =
      _receive_preserves_impl_invariant_secret_key_not_derivable session
        message
        trigger_derivation
        state
        new_state
        d
  in
  assert (impl_invariant_secret_key_not_derivable new_state);
  let _helper_receive_preserves_impl_invariant_cannot_derive_response_before_send
        (d: adv.derivation)
        (quantified_session: session_id)
        (valid_response derived_term: term)
      : Lemma
          (requires
            is_receive_trigger_for_session quantified_session new_state.internal.key valid_response /\
            (adv.derive d new_state.know = Some derived_term) /\
            in_term derived_term valid_response)
          (ensures Set.mem quantified_session new_state.internal.sent_sessions)
          [
            SMTPat
            (is_receive_trigger_for_session quantified_session new_state.internal.key valid_response);
            SMTPat (adv.derive d new_state.know);
            SMTPat (in_term derived_term valid_response)
          ] =
    _receive_preserves_impl_invariant_cannot_derive_response_before_send session
      message
      trigger_derivation
      state
      new_state
      d
      quantified_session
      valid_response
      derived_term
  in
  assert (impl_invariant_cannot_derive_response_before_send new_state);
  let _helper_receive_preserves_impl_invariant_to_be_delivered_messages_in_knowledge
        (d: adv.derivation)
        (quantified_session: session_id)
        (quantified_message derived_term: term)
      : Lemma
          (requires
            ((adv.derive d new_state.know = Some derived_term) /\
              in_term derived_term
                (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key)))
          (ensures
            derivable new_state.know (Pair (SessionId quantified_session) quantified_message))
          [
            SMTPat (adv.derive d new_state.know);
            SMTPat
            (derivable new_state.know
                (Pair (SessionId quantified_session) quantified_message));
            SMTPat
            (in_term derived_term
                (Senc (Pair (SessionId quantified_session) quantified_message) new_state.internal.key))
          ] =
    _receive_preserves_impl_invariant_to_be_delivered_messages_in_knowledge session
      message
      trigger_derivation
      state
      new_state
      d
      quantified_session
      quantified_message
      derived_term
  in
  assert (impl_invariant_to_be_delivered_messages_in_knowledge new_state);
  FStar.Classical.forall_intro_4
    (FStar.Classical.move_requires_4
      (fun quantified_session quantified_message d derived_term ->
        _receive_preserves_impl_invariant_derived_valid_response_equivalent_to_observed_response session
          message
          trigger_derivation
          state
          new_state
          d
          quantified_session
          quantified_message
          derived_term));
  assert (impl_invariant_derived_valid_response_equivalent_to_observed_response new_state);
  assert (impl_invariant_sent_sessions_have_messages new_state);
  let _helper_receive_preserves_messages_consistent
        (qs: session_id) (qm: term)
        (d: adv.derivation) (derived_term: term)
      : Lemma
          (requires
            adv.derive d new_state.know = Some derived_term /\
            in_term derived_term (Senc (Pair (SessionId qs) qm) new_state.internal.key))
          (ensures PartialMap.sel new_state.internal.messages qs == Some qm)
          [SMTPat (adv.derive d new_state.know);
           SMTPat (in_term derived_term (Senc (Pair (SessionId qs) qm) new_state.internal.key))] =
    assert (impl_invariant_to_be_delivered_messages_in_knowledge state);
    assert (in_term trigger_term trigger_term);
    assert (derivable state.know trigger_term);
    assert (derivable state.know deliver_term);
    observe_derivable_no_new_derivations state.know deliver_term derived_term
  in
  assert (new_state.inputs == Bag.remove trigger_term state.inputs);
  _inputs_derivable_preserved_by_observation state new_state trigger_term deliver_term;
  assert (impl_invariant_messages_consistent_with_knowledge new_state)

let implementation_invariants_preserved_after_send'
      (session: session_id)
      (message: term)
      (state new_state: impl_system_state)
    : Lemma
      (requires (
        let sent_term = Senc (Pair (SessionId session) message) state.internal.key in
        implementation_invariants state /\
        impl_invariant_inputs_are_derivable state /\
        smd_impl_protocol_send_transition (s2p_state state)
          session
          sent_term
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know sent_term))
      (ensures implementation_invariants new_state) =
  let trigger_input = Pair (SessionId session) message in
  assert (smd_impl_protocol_send_enabled (s2p_state state) session message state.internal.key);
  assert (smd_impl_send_effect session message state new_state);
  assert (Bag.mem trigger_input state.inputs);
  assert (impl_invariant_inputs_are_derivable state);
  assert (derivable state.know trigger_input);
  let trigger_derivation =
    FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation
      (fun d -> adv.derive d state.know = Some trigger_input)
  in
  assert (adv.derive trigger_derivation state.know = Some trigger_input);
  implementation_invariants_preserved_after_send
    session
    message
    trigger_derivation
    state
    new_state

let implementation_invariants_preserved_after_receive'
      (session: session_id)
      (message: term)
      (state new_state: impl_system_state)
    : Lemma
      (requires
        implementation_invariants state /\
        impl_invariant_inputs_are_derivable state /\
        smd_impl_protocol_receive_transition (s2p_state state)
          session
          (Pair (SessionId session) message)
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know (Pair (SessionId session) message))
      (ensures implementation_invariants new_state) =
  let trigger_term = Senc (Pair (SessionId session) message) state.internal.key in
  assert (smd_impl_protocol_receive_enabled (s2p_state state) session message);
  assert (smd_impl_receive_effect session message state new_state);
  assert (Bag.mem trigger_term state.inputs);
  assert (impl_invariant_inputs_are_derivable state);
  assert (derivable state.know trigger_term);
  let trigger_derivation =
    FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation
      (fun d -> adv.derive d state.know = Some trigger_term)
  in
  assert (adv.derive trigger_derivation state.know = Some trigger_term);
  implementation_invariants_preserved_after_receive
    session
    message
    trigger_derivation
    state
    new_state
