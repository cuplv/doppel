module SMD.IdealInvariants

open AdversarySenc
open SencTerms
open SymbolicTypes
open TestedSystem

open SMD.Adversary
open SMD.Ideal
open SMD.TestedProtocols

module PartialMap = FStar.PartialMap

module Set = FStar.Set

let smd_ideal_send_effect
      (session: session_id)
      (message: term)
      (state new_state: ideal_system_state)
    : prop =
  smd_ideal_protocol_send_enabled (s2p_state state) session message /\
  s2p_state new_state == smd_ideal_protocol_send_state (s2p_state state) session message /\
  new_state.know == Seq.snoc state.know (Senc (SessionId session) state.internal.sim_key)

let smd_ideal_receive_effect
      (session: session_id)
      (message: term)
      (state new_state: ideal_system_state)
    : prop =
  smd_ideal_protocol_receive_enabled (s2p_state state) session message /\
  s2p_state new_state == smd_ideal_protocol_receive_state (s2p_state state) session message /\
  new_state.know == Seq.snoc state.know (Pair (SessionId session) message)

let _cannot_derive_secret_key_after_smd_ideal_send
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
      (d: adv.derivation)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_send_effect session message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) message))
      (ensures adv.derive d new_state.know <> Some (Key state.internal.sim_key)) =
  match adv.derive trigger_derivation state.know with
  | Some (Pair (SessionId sid) trigger_message) ->
    (match adv.derive d new_state.know with
      | Some t ->
        if t = Key state.internal.sim_key
        then
          derivable_from_encrypted_term_without_key state.know
            (SessionId session)
            state.internal.sim_key
            d
            (Key state.internal.sim_key)
      | _ -> ())
  | _ -> ()

let _smd_ideal_send_preserves_committed_messages_derivable_from_knowledge
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
      (quantified_session: session_id)
      (quantified_message: term)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_send_effect session message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) message) /\
        PartialMap.sel new_state.internal.messages quantified_session = Some quantified_message)
      (ensures adv.derivable new_state.know (Pair (SessionId quantified_session) quantified_message)) =
  let target = Pair (SessionId quantified_session) quantified_message in
  assert (adv.derivable state.know target);
  assert (adv.derivable new_state.know target)

let rec _smd_ideal_send_preserves_valid_response_not_present_before_send
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (derived_term: term)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_send_effect session message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) message) /\
        in_term derived_term (Senc (SessionId quantified_session) state.internal.sim_key) /\
        adv.derive d new_state.know = Some derived_term)
      (ensures Set.mem quantified_session new_state.internal.sim_sent_sessions) =
  let valid_response = Senc (SessionId quantified_session) state.internal.sim_key in
  match d with
  | DeriveObserved i -> ()
  | DeriveSEncrypt derive_plaintext derive_key ->
    if adv.derive derive_key new_state.know = Some (Key state.internal.sim_key)
    then
      _cannot_derive_secret_key_after_smd_ideal_send session
        message
        trigger_derivation
        state
        new_state
        derive_key
    else
      (match adv.derive derive_key new_state.know, adv.derive derive_plaintext new_state.know with
      | Some (Key key), Some plaintext ->
        _smd_ideal_send_preserves_valid_response_not_present_before_send
          session
          message
          trigger_derivation
          state
          new_state
          derive_plaintext
          quantified_session
          plaintext
      | _, _ -> ())
  | DeriveSDecrypt derive_ciphertext derive_key ->
    (match adv.derive derive_ciphertext new_state.know with
    | Some ciphertext ->
      _smd_ideal_send_preserves_valid_response_not_present_before_send
        session
        message
        trigger_derivation
        state
        new_state
        derive_ciphertext
        quantified_session
        ciphertext
    | _ -> ())
  | DerivePair derive_left derive_right ->
    (match adv.derive derive_left new_state.know, adv.derive derive_right new_state.know with
    | Some left, Some right ->
      if in_term left valid_response
      then
        _smd_ideal_send_preserves_valid_response_not_present_before_send
          session
          message
          trigger_derivation
          state
          new_state
          derive_left
          quantified_session
          left
      else if in_term right valid_response
      then
        _smd_ideal_send_preserves_valid_response_not_present_before_send
          session
          message
          trigger_derivation
          state
          new_state
          derive_right
          quantified_session
          right
    | _, _ -> ())
  | DerivePairLeft derive_pair
  | DerivePairRight derive_pair ->
    (match adv.derive derive_pair new_state.know with
    | Some (Pair left right) ->
      _smd_ideal_send_preserves_valid_response_not_present_before_send
        session
        message
        trigger_derivation
        state
        new_state
        derive_pair
        quantified_session
        (Pair left right)
    | _ -> ())

let _inputs_derivable_preserved_by_observation
      (state new_state: ideal_system_state)
      (trigger_input observed_term: term)
    : Lemma
      (requires
        ideal_invariant_inputs_are_derivable state /\
        new_state.inputs == Bag.remove trigger_input state.inputs /\
        new_state.know == Seq.snoc state.know observed_term)
      (ensures ideal_invariant_inputs_are_derivable new_state) =
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

let ideal_invariants_preserved_after_smd_ideal_send_effect
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_send_effect session message state new_state /\
        adv.derive trigger_derivation state.know = Some (Pair (SessionId session) message))
      (ensures ideal_invariants new_state) =
  let _helper_cannot_derive_secret_key_after_smd_ideal_send
        (d: adv.derivation)
      : Lemma (ensures adv.derive d new_state.know <> Some (Key state.internal.sim_key))
        [SMTPat (adv.derive d new_state.know)] =
    _cannot_derive_secret_key_after_smd_ideal_send session
      message
      trigger_derivation
      state
      new_state
      d
  in
  assert (ideal_invariant_secret_key_not_derivable new_state);
  let _helper_smd_ideal_send_preserves_committed_messages_derivable_from_knowledge
        (quantified_session: session_id)
        (quantified_message: term)
      : Lemma
        (requires PartialMap.sel new_state.internal.messages quantified_session = Some quantified_message)
        (ensures adv.derivable new_state.know (Pair (SessionId quantified_session) quantified_message))
        [
          SMTPat (PartialMap.sel new_state.internal.messages quantified_session);
          SMTPat (adv.derivable new_state.know (Pair (SessionId quantified_session) quantified_message))
        ] =
    _smd_ideal_send_preserves_committed_messages_derivable_from_knowledge session
      message
      trigger_derivation
      state
      new_state
      quantified_session
      quantified_message
  in
  assert (ideal_invariant_committed_messages_derivable_from_knowledge new_state);
  assert (ideal_invariant_private_channels_empty new_state);
  let _helper_smd_ideal_send_preserves_valid_response_not_present_before_send
        (d: adv.derivation)
        (quantified_session: session_id)
        (derived_term: term)
      : Lemma
        (requires
          in_term derived_term (Senc (SessionId quantified_session) state.internal.sim_key) /\
          adv.derive d new_state.know = Some derived_term)
        (ensures Set.mem quantified_session new_state.internal.sim_sent_sessions)
        [
          SMTPat (in_term derived_term (Senc (SessionId quantified_session) state.internal.sim_key));
          SMTPat (adv.derive d new_state.know);
          SMTPat (Set.mem quantified_session new_state.internal.sim_sent_sessions)
        ] =
    _smd_ideal_send_preserves_valid_response_not_present_before_send session
      message
      trigger_derivation
      state
      new_state
      d
      quantified_session
      derived_term
  in
  assert (ideal_invariant_cannot_derive_valid_response_before_send new_state);
  assert (ideal_invariant_sim_sent_only_after_ideal_commit new_state);
  let trigger_input = Pair (SessionId session) message in
  let observed_term = Senc (SessionId session) state.internal.sim_key in
  assert (new_state.inputs == Bag.remove trigger_input state.inputs);
  _inputs_derivable_preserved_by_observation state new_state trigger_input observed_term;
  assert (ideal_invariant_inputs_are_derivable new_state)

let _smd_ideal_receive_preserves_secret_key_not_derivable
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
      (d: adv.derivation)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (SessionId session) state.internal.sim_key))
      (ensures adv.derive d new_state.know <> Some (Key state.internal.sim_key)) =
  match adv.derive d new_state.know with
  | Some t ->
    observe_derivable_no_new_derivations state.know (Pair (SessionId session) message) t
  | _ -> ()

let _smd_ideal_receive_preserves_cannot_derive_valid_response_before_send
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
      (d: adv.derivation)
      (quantified_session: session_id)
      (derived_term: term)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (SessionId session) state.internal.sim_key) /\
        in_term derived_term (Senc (SessionId quantified_session) state.internal.sim_key) /\
        adv.derive d new_state.know = Some derived_term)
      (ensures Set.mem quantified_session new_state.internal.sim_sent_sessions) =
  match adv.derive d new_state.know with
  | Some t ->
    observe_derivable_no_new_derivations state.know (Pair (SessionId session) message) t
  | _ -> ()

let ideal_invariants_preserved_after_smd_ideal_receive_effect
      (session: session_id)
      (message: term)
      (trigger_derivation: adv.derivation)
      (state new_state: ideal_system_state)
    : Lemma
      (requires
        ideal_invariants state /\
        smd_ideal_receive_effect session message state new_state /\
        adv.derive trigger_derivation state.know =
        Some (Senc (SessionId session) state.internal.sim_key))
      (ensures ideal_invariants new_state) =
  let _helper_smd_ideal_receive_preserves_secret_key_not_derivable
        (d: adv.derivation)
      : Lemma (ensures adv.derive d new_state.know <> Some (Key state.internal.sim_key))
        [SMTPat (adv.derive d new_state.know)] =
    _smd_ideal_receive_preserves_secret_key_not_derivable session
      message
      trigger_derivation
      state
      new_state
      d
  in
  assert (ideal_invariant_secret_key_not_derivable new_state);
  assert (ideal_invariant_committed_messages_derivable_from_knowledge new_state);
  assert (ideal_invariant_private_channels_empty new_state);
  let _helper_smd_ideal_receive_preserves_cannot_derive_valid_response_before_send
        (d: adv.derivation)
        (quantified_session: session_id)
        (derived_term: term)
      : Lemma
        (requires
          in_term derived_term (Senc (SessionId quantified_session) state.internal.sim_key) /\
          adv.derive d new_state.know = Some derived_term)
        (ensures Set.mem quantified_session new_state.internal.sim_sent_sessions)
        [
          SMTPat (in_term derived_term (Senc (SessionId quantified_session) state.internal.sim_key));
          SMTPat (adv.derive d new_state.know);
          SMTPat (Set.mem quantified_session new_state.internal.sim_sent_sessions)
        ] =
    _smd_ideal_receive_preserves_cannot_derive_valid_response_before_send session
      message
      trigger_derivation
      state
      new_state
      d
      quantified_session
      derived_term
  in
  assert (ideal_invariant_cannot_derive_valid_response_before_send new_state);
  assert (ideal_invariant_sim_sent_only_after_ideal_commit new_state);
  let trigger_input = Senc (SessionId session) state.internal.sim_key in
  let observed_term = Pair (SessionId session) message in
  assert (new_state.inputs == Bag.remove trigger_input state.inputs);
  _inputs_derivable_preserved_by_observation state new_state trigger_input observed_term;
  assert (ideal_invariant_inputs_are_derivable new_state)

let ideal_invariants_preserved_after_send'
      (session: session_id)
      (state new_state: ideal_system_state)
    : Lemma
      (requires (
        let sent_term = Senc (SessionId session) state.internal.sim_key in
        ideal_invariants state /\
        ideal_invariant_inputs_are_derivable state /\
        smd_ideal_protocol_send_transition (s2p_state state)
          session
          sent_term
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know sent_term))
      (ensures ideal_invariants new_state) =
  let sent_term = Senc (SessionId session) state.internal.sim_key in
  let msg =
    FStar.IndefiniteDescription.indefinite_description_ghost term
      (fun m ->
        smd_ideal_protocol_send_enabled (s2p_state state) session m /\
        s2p_state new_state == smd_ideal_protocol_send_state (s2p_state state) session m)
  in
  let trigger_input = Pair (SessionId session) msg in
  assert (Bag.mem trigger_input state.inputs);
  assert (derivable state.know trigger_input);
  let trigger_derivation =
    FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation
      (fun d -> adv.derive d state.know = Some trigger_input)
  in
  assert (adv.derive trigger_derivation state.know = Some trigger_input);
  assert (smd_ideal_send_effect session msg state new_state);
  assert (ideal_invariant_inputs_are_derivable state);
  ideal_invariants_preserved_after_smd_ideal_send_effect
    session
    msg
    trigger_derivation
    state
    new_state

let ideal_invariants_preserved_after_receive'
      (session: session_id)
      (message: term)
      (state new_state: ideal_system_state)
    : Lemma
      (requires
        ideal_invariants state /\
        ideal_invariant_inputs_are_derivable state /\
        smd_ideal_protocol_receive_transition (s2p_state state)
          session
          (Pair (SessionId session) message)
          (s2p_state new_state) /\
        new_state.know == Seq.snoc state.know (Pair (SessionId session) message))
      (ensures ideal_invariants new_state)
 =
  let trigger_term = Senc (SessionId session) state.internal.sim_key in
  assert (smd_ideal_protocol_receive_enabled (s2p_state state) session message);
  assert (Bag.mem trigger_term state.inputs);
  assert (derivable state.know trigger_term);
  let trigger_derivation =
    FStar.IndefiniteDescription.indefinite_description_ghost adv.derivation
      (fun d -> adv.derive d state.know = Some trigger_term)
  in
  assert (adv.derive trigger_derivation state.know = Some trigger_term);
  assert (smd_ideal_receive_effect session message state new_state);
  assert (ideal_invariant_inputs_are_derivable state);
  ideal_invariants_preserved_after_smd_ideal_receive_effect
    session
    message
    trigger_derivation
    state
    new_state
