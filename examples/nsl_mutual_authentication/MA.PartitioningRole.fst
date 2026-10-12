module MA.PartitioningRole


open SymbolicTypes

open AencTerms

open AdversaryAenc

open MA.NSL

open MA.Ideal

open MA.Adversary

open MA.Types

open TestedSystem

open ObservationalBisimulation

module PartialMap = FStar.PartialMap

module PartialMapExt = FStar.PartialMap.Ext

open MA.TestedProtocols

module Set = FStar.Set

open FStar.Set.Properties

module Seq = FStar.Seq

open Bag

module Protocol = Protocol

open MA.IdealInvariants


/// =========================================================================
/// Partition equivalence
/// =========================================================================
///
/// `ma_label_in_same_partition_role` is reflexive/symmetric/transitive because
/// it is built from componentwise equality of the label identifier fields.

private
let role_refl_lemma (x: TestedSystem.label term ma_effect ma_label_id adversary_aenc)
    : Lemma (ma_label_in_same_partition_role x x) = ()

private
let role_symm_lemma (x y: TestedSystem.label term ma_effect ma_label_id adversary_aenc)
    : Lemma (ma_label_in_same_partition_role x y ==> ma_label_in_same_partition_role y x) = ()

private
let role_trans_lemma (x y z: TestedSystem.label term ma_effect ma_label_id adversary_aenc)
    : Lemma
    (ma_label_in_same_partition_role x y /\ ma_label_in_same_partition_role y z ==>
      ma_label_in_same_partition_role x z) = ()

let ma_label_in_same_partition_role_equiv () =
  FStar.Classical.forall_intro role_refl_lemma;
  FStar.Classical.forall_intro_2 role_symm_lemma;
  FStar.Classical.forall_intro_3 role_trans_lemma;
  ()


/// =========================================================================
/// Right-movability for the implementation
/// =========================================================================
///
/// `ma_nsl_protocol_transition` rules out internal transitions, so there is
/// no `tau` with `is_internal tau` and the `right_movable` premise is
/// unsatisfiable, independent of the partition.

let ma_right_movable_impl_role corrupt key_directory know0 = ()


/// =========================================================================
/// Right-movability for the ideal+simulator
/// =========================================================================
///
/// We prove that the role-sensitive partition `ma_partition_role` is
/// right-movable modulo the ideal agreement invariants: for every
/// role-distinct pair `(tau, alpha)` with `tau` internal, the two transitions
/// commute on any state `s` satisfying `ma_ideal_system_inv corrupt key_directory s`.
///
/// The main theorem `ma_right_movable_ideal_role` (bottom of the file)
/// dispatches on the SHAPE of `alpha`:
///
///   * `alpha = Internal idalpha`        -> `_ideal_internal_internal_commute`
///   * `alpha = Observable NetSend idalpha` -> `_ideal_internal_netsend_commute`
///   * `alpha = Input d`                 -> `_ideal_input_commute`
///   * `alpha = Observable IoSend idalpha` (deliver) -> handled INLINE below,
///        because this is the only case whose commutation is conditioned on the
///        agreement invariant.
///
/// The `_ideal_*` lemmas (and their per-pair `_commute_*` leaves) take the
/// precise label-distinctness they need as a hypothesis
/// (`~(ma_label_id_in_same_partition_role idtau idalpha)`), deriving the actual
/// disjointness of the touched state from transition *feasibility* (e.g. two
/// distinct `Auth` inputs, disjoint request/channel additions) rather than from
/// the partition itself. They therefore cover every role-distinct internal /
/// netsend / input alpha uniformly, across both same- and different-session
/// pairs.
///
/// ----------------------------------------------------------------------
/// THE TWO INVARIANT-BLOCKED DELIVER CONFIGURATIONS (handled inline)
/// ----------------------------------------------------------------------
///
/// For `alpha = deliver` two role-distinct shapes do NOT commute on arbitrary
/// (unreachable) states; they are instead discharged as GENUINELY INFEASIBLE on
/// states satisfying `ma_ideal_system_inv` (`subcase_A_infeasible` /
/// `subcase_B_infeasible`), so the swap goal holds vacuously.
///
/// (A) tau = ma_ideal_initiate(i, p, q, r)          [id (i, p, q, r)]
///     alpha = ma_ideal_deliver(i, q, p, comp r)    [id (i, q, p, complementary r)]
///
///     `tau` adds the request `{p, q, r}` to `requests[i]`, which is exactly
///     the *complementary* request that `alpha = deliver(i, q, p, comp r)`
///     reads. So `tau` *enables* `alpha`: at `s_mid` both requests are present,
///     but at `s` the request `{p, q, r}` is absent (`tau`'s own precondition
///     requires that *no* request with `party = p` exists at `s`). Hence
///     `alpha` is NOT enabled at `s`.
///
///     WHY IT NEVER HAPPENS ON REACHABLE STATES: invariant (I1) — no
///     `output_term(i, B)` may be in flight unless `requests[i]` already holds
///     B's request AND its complement. Combined with (I2) at-most-one-request-
///     per-party, (I1) forces `{p, q, r} ∈ requests[i]` at s, contradicting
///     tau's precondition. So such an `s` is unreachable.
///
/// (B) tau = ma_sim_receive_message3(i, p, q)        [id (i, p, q, Responder)]
///     alpha = ma_ideal_deliver(i, p, q, Initiator)  [id (i, p, q, Initiator)]
///
///     `tau` adds `output_term(i, p)` to `sim_to_ideal_channel`, which
///     `alpha = deliver(i, p, q, Initiator)` also reads, so `tau` enables
///     `alpha`. On reachable states it is ruled out by (I2): `tau`'s responder
///     session records that p requested `{p, q, Responder}`, so by
///     at-most-one-request-per-party p cannot also hold `{p, q, Initiator}`,
///     hence deliver(i, p, q, Initiator) is infeasible.
///
/// HOW (A) AND (B) ARE DISCHARGED:
///   The `ma_ideal_system_inv corrupt key_directory s` hypothesis carried by the commute
///   body is exactly the supplied reachability invariant. It implies the
///   relevant state predicates — I2 (`ma_ideal_inv_one_request_per_party`),
///   session-has-request (`ma_sim_session_matches_ideal_request`, the
///   system-level subsumer of the former H_resp clause), and strong-I1
///   (`ma_output_has_complementary_request`) — for `s2p_state s`. Each of (A)
///   and (B) is then shown to be INFEASIBLE (`ensures False`) on such `s`. See
///   `subcase_A_infeasible` / `subcase_B_infeasible`.
///
/// ----------------------------------------------------------------------
/// PROVABLE DELIVER PAIRS (genuinely commuting):
///   * tau = sim_receive_message3(i, p, q) vs. alpha = deliver(a, b, c, r) with
///     `(a, b) != (i, p)` — commute (the output terms differ, so alpha is
///     enabled at s independently of tau).  [`rl_commute_simrecv_deliver_diff_party`]
///   * tau = initiate(i, p, q, r) vs. alpha = deliver NOT in the subcase-(A)
///     shape — commute (tau does not enable alpha).  [`rl_commute_initiate_deliver`]
/// Both derive their precise label-distinctness from feasibility / pure label
/// arithmetic, and cover every non-infeasible role-distinct deliver pair.

/// ----------------------------------------------------------------------
/// Subcase (A): infeasible on states satisfying `ma_ideal_system_inv`.
///
///   tau   = ma_ideal_initiate(i, P, Q, r)        [idτ = (i, P, Q, r)]
///   alpha = ma_ideal_deliver(i, Q, P, comp r)    [idα = (i, Q, P, comp r)]
///
/// First-order infeasibility from the invariant alone (no derivability):
///   1. `alpha` enabled at `s_mid` (deliver) reads `Output(i, Q)`; `tau`
///      (initiate) preserves `sim_to_ideal_channel`, so `Output(i, Q)` is
///      already in flight at `s`.
///   2. Strong-I1 (`ma_output_has_complementary_request`): `Output(i, Q)` in
///      flight forces `{Q, peer', r'}` and its complement `{peer', Q, comp r'}`
///      into `requests s i`.
///   3. `alpha` enabled at `s_mid` also reads `{Q, P, comp r}`; initiate only
///      ADDS the party-P request `{P, Q, r}`, so `{Q, P, comp r}` (party Q) was
///      already in `requests s i`.
///   4. I2 (`ma_ideal_inv_one_request_per_party`): Q has at most one request,
///      so `{Q, peer', r'} == {Q, P, comp r}`, hence its complement is
///      `{P, Q, comp (comp r)} == {P, Q, r}` in `requests s i`.
///   5. But `tau = initiate(i, P, Q, r)` enabled at `s` requires NO party-P
///      request in `requests s i`. Contradiction with step 4.
private
let subcase_A_infeasible
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idtau idalpha: ma_label_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s /\
        not (Set.mem idtau.party corrupt) /\
        not (Set.mem idtau.peer corrupt) /\
        idtau.session == idalpha.session /\
        idalpha.party == idtau.peer /\ idalpha.peer == idtau.party /\
        idalpha.role == complementary_role idtau.role /\
        ma_ideal_initiate_protocol_transition (TestedSystem.s2p_state s)
          idtau.session idtau.party idtau.peer idtau.role (TestedSystem.s2p_state s_mid) /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid
          (TestedSystem.Observable IoSend idalpha) s')
      (ensures False) =
  // `ma_ideal_system_inv` is `opaque_to_smt`; reveal it to access its conjuncts.
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv) (ma_ideal_system_inv corrupt key_directory s);
  let i = idtau.session in
  let pP = idtau.party in
  let qQ = idtau.peer in
  let r = idtau.role in
  let s_p = TestedSystem.s2p_state s in
  let s_mid_p = TestedSystem.s2p_state s_mid in
  complementary_role_involutive r;
  let init_state = ma_ideal_initiate_state s_p i pP qQ r in
  // From the initiate transition.
  assert (ma_ideal_initiate_enabled s_p i pP qQ r);
  assert (s_mid_p == init_state);
  // initiate preserves the channel and adds exactly the party-P request.
  assert (init_state.internal.sim_to_ideal_channel == s_p.internal.sim_to_ideal_channel);
  assert (ma_session_requests init_state i ==
          Set.add ({ party = pP; peer = qQ; role = r }) (ma_session_requests s_p i));
  // From the deliver enabledness at s_mid (= initiate state) for (i, Q, P, comp r).
  assert (ma_ideal_deliver_enabled s_mid_p
            idalpha.session idalpha.party idalpha.peer idalpha.role);
  assert (Set.mem (ma_output_term i qQ) s_p.internal.sim_to_ideal_channel);
  assert (Set.mem ({ party = qQ; peer = pP; role = complementary_role r })
            (ma_session_requests s_p i));
  // Strong-I1 + I2 force the party-P request {P, Q, r} into requests s i.
  assert (ma_output_has_complementary_request corrupt s);
  assert (ma_ideal_inv_one_request_per_party s_p);
  assert (Set.mem ({ party = pP; peer = qQ; role = r }) (ma_session_requests s_p i));
  // ... contradicting the initiate precondition (no party-P request at s).
  ()

/// ----------------------------------------------------------------------
/// Subcase (B): infeasible on states satisfying `ma_ideal_system_inv`.
///
///   tau   = ma_sim_receive_message3(i, P, Q)     [idτ = (i, P, Q, Responder)]
///   alpha = ma_ideal_deliver(i, P, Q, Initiator) [idα = (i, P, Q, Initiator)]
///
///   1. `tau` (recv3) enabled at `s` records a simulator responder session for
///      P in i with initiator Q; `ma_sim_session_matches_ideal_request` (the
///      system-level subsumer of the former H_resp clause) gives
///      `{P, Q, Responder}` in `requests s i`.
///   2. `alpha` (deliver(i, P, Q, Initiator)) enabled at `s_mid` reads
///      `{P, Q, Initiator}`; recv3 does NOT change `requests`, so
///      `{P, Q, Initiator}` is already in `requests s i`.
///   3. I2: P has at most one request, so
///      `{P, Q, Responder} == {P, Q, Initiator}` ==> `Responder == Initiator`.
///      Contradiction.
private
let subcase_B_infeasible
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idtau idalpha: ma_label_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s /\
        idtau.role == Responder /\
        idalpha.session == idtau.session /\
        idalpha.party == idtau.party /\
        ~(ma_label_id_in_same_partition_role idtau idalpha) /\
        ma_sim_receive_message3_protocol_transition (TestedSystem.s2p_state s)
          idtau.session idtau.party idtau.peer (TestedSystem.s2p_state s_mid) /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid
          (TestedSystem.Observable IoSend idalpha) s')
      (ensures False) =
  // `ma_ideal_system_inv` is `opaque_to_smt`; reveal it to access its conjuncts.
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv) (ma_ideal_system_inv corrupt key_directory s);
  let i = idtau.session in
  let pP = idtau.party in   // responder
  let qQ = idtau.peer in    // initiator
  let s_p = TestedSystem.s2p_state s in
  let s_mid_p = TestedSystem.s2p_state s_mid in
  assert (ma_ideal_inv_one_request_per_party s_p);
  // deliver enabledness at s_mid for idα (same session and party as idτ).
  assert (ma_ideal_deliver_enabled s_mid_p
            idalpha.session idalpha.party idalpha.peer idalpha.role);
  // expose the recv3 witness so we can transport requests and read the session.
  assert (exists (rk: priv_key).
    ma_sim_receive_message3_enabled s_p i pP qQ rk /\
    s_mid_p == ma_sim_receive_message3_state s_p i pP qQ rk);
  eliminate exists (rk: priv_key).
    ma_sim_receive_message3_enabled s_p i pP qQ rk /\
    s_mid_p == ma_sim_receive_message3_state s_p i pP qQ rk
  returns False
  with _hk. (
    ma_sim_receive_message3_state_session_requests_eq s_p i pP qQ rk i;
    // recv3 enabled: P has a responder session in i with initiator Q.
    assert (Some? (ma_sim_responder_session_state s_p pP i));
    assert ((Some?.v (ma_sim_responder_session_state s_p pP i)).initiator == qQ);
    // ma_sim_session_matches_ideal_request gives: P's stored responder session
    // in i yields the recorded Responder request {P, Q, Responder}.  Bridge the
    // stored-session map to `ma_get_sim_participant_session_state`, then
    // instantiate the clause pointwise at (i, P).
    unfold_ma_sim_responder_session_state s_p pP i;
    let h_sim_matches : squash (ma_sim_session_matches_ideal_request s) = () in
    let h_sim_matches_session = FStar.Classical.Sugar.forall_elim i h_sim_matches in
    let _h_sim_matches_instance = FStar.Classical.Sugar.forall_elim pP h_sim_matches_session in
    assert (Set.mem ({ party = pP; peer = qQ; role = Responder }) (ma_session_requests s_p i));
    // deliver reads idα's request {P, peer_α, role_α} at s_mid; recv3 preserves
    // requests so it is present at s as well.
    assert (Set.mem ({ party = pP; peer = idalpha.peer; role = idalpha.role })
              (ma_session_requests s_mid_p i));
    assert (ma_session_requests s_mid_p i == ma_session_requests s_p i);
    assert (Set.mem ({ party = pP; peer = idalpha.peer; role = idalpha.role })
              (ma_session_requests s_p i));
    // I2: P has at most one request in session i, so the two coincide, forcing
    // peer_α == Q and role_α == Responder, i.e. idα == idτ — contradicting
    // role-distinctness.
    assert (idalpha.peer == qQ /\ idalpha.role == Responder);
    ()
  )

/// =========================================================================
/// Residual commuting machinery (role partition, ROLE-DISTINCT)
/// =========================================================================
///
/// The label-distinctness these lemmas need is supplied as a PRECISE hypothesis
/// (derived in the main theorem from transition feasibility + `ma_ideal_system_inv`)
/// rather than from a coarse partition relation.


// ---- tau internal × alpha = Observable IoSend idα (deliver), residual ----

// (i-corrupt) τ = ma_ideal_initiate, subcase (A) with at least one corrupt party.
// The deliver α is already enabled at s (before initiate τ) because the
// at_least_one_corrupt disjunct of ma_ideal_deliver_enabled holds.  The two
// transitions touch disjoint state components and commute.
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2 --split_queries no"
private
let subcase_A_commute_corrupt
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (output_t: term)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ma_ideal_system_inv corrupt key_directory s /\
        (Set.mem idτ.party corrupt \/ Set.mem idτ.peer corrupt) /\
        idα.session == idτ.session /\
        idα.party == idτ.peer /\ idα.peer == idτ.party /\
        idα.role == complementary_role idτ.role /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        output_t == ma_authenticated_term idα.session idα.party idα.peer /\
        ma_ideal_deliver_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer idα.role /\
        s2p_state s' == ma_ideal_deliver_state (s2p_state s_mid)
                          idα.session idα.party idα.peer /\
        s'.know == Seq.snoc s_mid.know output_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable IoSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  // `ma_ideal_system_inv` is `opaque_to_smt`; reveal it for `ma_corrupt_set_matches`.
  FStar.Pervasives.reveal_opaque (`%ma_ideal_system_inv) (ma_ideal_system_inv corrupt key_directory s);
  let s_p = s2p_state s in
  let s_mid_p = s2p_state s_mid in
  let i = idτ.session in
  // `s.internal.corrupt == corrupt`, so the corrupt-disjunct of deliver-enabledness
  // at `s` follows from the parameter-level corruption hypothesis.
  assert (s_p.internal.corrupt == corrupt);
  // initiate preserves the sim-to-ideal channel; the requested `Output` α reads is
  // therefore already present at `s`.
  ma_ideal_initiate_state_preserves_sim_to_ideal_channel s_p i idτ.party idτ.peer idτ.role;
  assert (s_mid_p.internal.sim_to_ideal_channel == s_p.internal.sim_to_ideal_channel);
  // initiate adds only the party-`idτ.party` request; α's own request
  // {idτ.peer, idτ.party, comp idτ.role} differs (the role is complementary), so it
  // is already in `requests s i`.
  ma_ideal_initiate_state_session_requests_eq s_p i idτ.party idτ.peer idτ.role i;
  complementary_role_involutive idτ.role;
  assert (Set.mem ({ party = idα.party; peer = idα.peer; role = idα.role })
            (ma_session_requests s_p i));
  // deliver α is enabled at `s` (own request present + at_least_one_corrupt).
  assert (ma_ideal_deliver_enabled s_p idα.session idα.party idα.peer idα.role);
  let s_mid'_p = ma_ideal_deliver_state (s2p_state s)
    idα.session idα.party idα.peer in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know output_t) in
  ()
#pop-options


// (i) τ = ma_ideal_initiate, NOT subcase (A): the request τ adds differs from
// both requests α reads, so α (deliver) is enabled at s independently of τ.
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2 --split_queries no"
private
let rl_commute_initiate_deliver
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (output_t: term)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        ~(idα.session == idτ.session /\ idα.party == idτ.peer /\ idα.peer == idτ.party /\
          idα.role == complementary_role idτ.role) /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        output_t == ma_authenticated_term idα.session idα.party idα.peer /\
        ma_ideal_deliver_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer idα.role /\
        s2p_state s' == ma_ideal_deliver_state (s2p_state s_mid)
                          idα.session idα.party idα.peer /\
        s'.know == Seq.snoc s_mid.know output_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable IoSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let s_mid'_p = ma_ideal_deliver_state (s2p_state s)
    idα.session idα.party idα.peer in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know output_t) in
  ()
#pop-options


// (ii) τ = ma_sim_receive_message3, deliver at a DIFFERENT party: the output
// term τ adds differs from the one α reads, so α is enabled at s.
#push-options "--z3rlimit 180 --fuel 3 --ifuel 3 --split_queries no"
private
let rl_commute_simrecv_deliver_diff_party
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (responder_key_τ: priv_key) (output_t: term)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(idτ.session == idα.session /\ idτ.party == idα.party) /\
        idτ.role == Responder /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        output_t == ma_authenticated_term idα.session idα.party idα.peer /\
        ma_ideal_deliver_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer idα.role /\
        s2p_state s' == ma_ideal_deliver_state (s2p_state s_mid)
                          idα.session idα.party idα.peer /\
        s'.know == Seq.snoc s_mid.know output_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable IoSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  let out_τ = ma_output_term idτ.session idτ.party in
  let out_α = ma_output_term idα.session idα.party in
  remove_add_commute out_α out_τ s.internal.sim_to_ideal_channel;
  let s_mid'_p = ma_ideal_deliver_state (s2p_state s)
    idα.session idα.party idα.peer in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know output_t) in
  ()
#pop-options

/// =========================================================================
/// Commutativity machinery for the internal / netsend / input alpha cases.
/// =========================================================================
///
/// The private `_commute_*` / `_ideal_*` helpers below prove genuine
/// commutation for every role-distinct pair `(tau, alpha)` (each taking the
/// precise `~(ma_label_id_in_same_partition_role idτ idα)` hypothesis). They
/// are dispatched by `ma_right_movable_ideal_role` for the
/// `Internal` / `NetSend` / `Input` shapes of `alpha`.


// ---- tau internal × alpha = Input d ----
//
// Input only inserts into the inputs bag, so any internal tau that removes
// a term `x` already in `s.inputs` commutes with it by Bag.remove_insert.

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let _ideal_input_commute
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key)
      (know0: knowledge term)
      (tau: system_label{is_internal tau})
      (d: adversary_aenc.derivation)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        (ma_ideal_system corrupt key_directory know0).transitions s tau s_mid /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Input d) s')
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Input d) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid' tau s') =
  let t = Some?.v (adversary_aenc.derive d s_mid.know) in
  let _s_mid' : ideal_system_state =
    { know = s.know; inputs = Bag.insert t s.inputs; internal = s.internal } in
  let bag_hint (x: term)
    : Lemma (requires Bag.mem x s.inputs)
            (ensures Bag.remove x (Bag.insert t s.inputs) ==
                     Bag.insert t (Bag.remove x s.inputs)) =
    Bag.remove_insert_commute x t s.inputs
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires bag_hint)
#pop-options


// ---- tau internal × alpha = Internal idα ----
//
// Decomposed into four per-pair helpers (one per (τ-kind, α-kind)
// combination), then dispatched via FStar.Classical.or_elim on the
// disjunction in `ma_ideal_protocol_transition`.

// (c) τ = ma_sim_receive_message3, α = ma_ideal_initiate.
//
// State pieces are essentially disjoint:
//   - inputs: both remove a term; the removed terms (msg3 net term and
//     auth_input_term) are constructor-disjoint (NetInput vs IoInput tag),
//     so Bag.remove_remove_commute.
//   - requests / ideal_to_sim_channel: touched only by α.
//   - sim_to_ideal_channel / sim_participant_sessions: touched only by τ.
//   - key_directory / used_nonces: preserved by both.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_simrecv_initiate
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (responder_key_τ: priv_key)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idτ.role == Responder /\
        ma_sim_receive_message3_enabled (s2p_state s) idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_ideal_initiate_enabled (s2p_state s_mid) idα.session idα.party idα.peer idα.role /\
        s2p_state s' == ma_ideal_initiate_state (s2p_state s_mid)
                          idα.session idα.party idα.peer idα.role /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  let rstate = Some?.v (ma_sim_responder_session_state (s2p_state s) idτ.party idτ.session) in
  let msg3_t = ma_nsl_message3_network_term
    idτ.session idτ.peer idτ.party rstate.responder_nonce (PubKey responder_key_τ) in
  let auth_t = ma_auth_input_term idα.session idα.party idα.peer idα.role in
  let s_mid'_p = ma_ideal_initiate_state (s2p_state s) idα.session idα.party idα.peer idα.role in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p s.know in
  Bag.remove_remove_commute auth_t msg3_t s.inputs
#pop-options


// (b) τ = ma_ideal_initiate, α = ma_sim_receive_message3. Dual of (c).
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_initiate_simrecv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (responder_key_α: priv_key)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idα.role == Responder /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        ma_sim_receive_message3_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer responder_key_α /\
        s2p_state s' == ma_sim_receive_message3_state (s2p_state s_mid)
                          idα.session idα.party idα.peer responder_key_α /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let rstate = Some?.v (ma_sim_responder_session_state (s2p_state s) idα.party idα.session) in
  let msg3_t = ma_nsl_message3_network_term
    idα.session idα.peer idα.party rstate.responder_nonce (PubKey responder_key_α) in
  let auth_t = ma_auth_input_term idτ.session idτ.party idτ.peer idτ.role in
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  let s_mid'_p = ma_sim_receive_message3_state (s2p_state s)
    idα.session idα.party idα.peer responder_key_α in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p s.know in
  Bag.remove_remove_commute auth_t msg3_t s.inputs
#pop-options


// (a) τ = ma_ideal_initiate, α = ma_ideal_initiate.
//
// Partition distinctness implies (s_τ != s_α) or ({p_τ, q_τ} != {p_α, q_α}).
// Combined with feasibility (alpha enabled at s_mid: no stored request with
// party=p_α; tau enabled at s: no stored request with party=p_τ), it follows
// that p_τ != p_α and the auth_input terms differ. Set adds and PartialMap
// updates commute accordingly.
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_initiate_initiate
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        ma_ideal_initiate_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer idα.role /\
        s2p_state s' == ma_ideal_initiate_state (s2p_state s_mid)
                          idα.session idα.party idα.peer idα.role /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let auth_τ = ma_auth_input_term idτ.session idτ.party idτ.peer idτ.role in
  let auth_α = ma_auth_input_term idα.session idα.party idα.peer idα.role in
  let authing_τ = ma_authenticating_term idτ.session idτ.party idτ.peer idτ.role in
  let authing_α = ma_authenticating_term idα.session idα.party idα.peer idα.role in
  let req_τ = { party = idτ.party; peer = idτ.peer; role = idτ.role } in
  let req_α = { party = idα.party; peer = idα.peer; role = idα.role } in
  let s_mid'_p = ma_ideal_initiate_state (s2p_state s)
    idα.session idα.party idα.peer idα.role in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p s.know in
  Bag.remove_remove_commute auth_τ auth_α s.inputs;
  add_commute authing_τ authing_α s.internal.ideal_to_sim_channel;
  let req_set_s_τ = ma_session_requests (s2p_state s) idτ.session in
  let req_set_s_α = ma_session_requests (s2p_state s) idα.session in
  if idτ.session = idα.session then
    (add_commute req_τ req_α req_set_s_τ;
     // Both updates write to the same map key. The single resulting value
     // matches after the swap by Set.add commutativity.
     PartialMap.eq_intro
       (PartialMap.upd
         (PartialMap.upd s.internal.requests idτ.session
           (Set.add req_τ req_set_s_τ))
         idα.session
         (Set.add req_α (Set.add req_τ req_set_s_τ)))
       (PartialMap.upd
         (PartialMap.upd s.internal.requests idα.session
           (Set.add req_α req_set_s_α))
         idτ.session
         (Set.add req_τ (Set.add req_α req_set_s_α))))
  else
    PartialMapExt.upd_commute s.internal.requests
      idτ.session (Set.add req_τ req_set_s_τ)
      idα.session (Set.add req_α req_set_s_α)
#pop-options


// (d) τ = ma_sim_receive_message3, α = ma_sim_receive_message3.
//
// Both update sim_participant_sessions at (party, session). Case splits:
//   - (idτ.party, idτ.session) = (idα.party, idα.session): vacuous via
//     τ setting output_forwarded=true so α's enabledness at s_mid fails.
//   - idτ.party != idα.party: different outer keys; outer PartialMapExt.upd_commute.
//   - idτ.party == idα.party, idτ.session != idα.session: same outer,
//     different inner; inner PartialMapExt.upd_commute.

// Subcase: idτ.party != idα.party. Outer key differs, so the lookup at
// (idα.party, idα.session) in s_mid equals the lookup at s; symmetric
// for τ at s_mid'.
#push-options "--z3rlimit 240 --fuel 3 --ifuel 3 --split_queries no"
private
let _commute_simrecv_simrecv_diff_party
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (responder_key_τ responder_key_α: priv_key)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        idτ.party <> idα.party /\
        idτ.role == Responder /\ idα.role == Responder /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_sim_receive_message3_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer responder_key_α /\
        s2p_state s' == ma_sim_receive_message3_state (s2p_state s_mid)
                          idα.session idα.party idα.peer responder_key_α /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let rstate_τ = Some?.v (ma_sim_responder_session_state (s2p_state s) idτ.party idτ.session) in
  let rstate_α = Some?.v (ma_sim_responder_session_state (s2p_state s) idα.party idα.session) in
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idα.session idα.party idα.peer responder_key_α;
  let msg3_τ = ma_nsl_message3_network_term
    idτ.session idτ.peer idτ.party rstate_τ.responder_nonce (PubKey responder_key_τ) in
  let msg3_α = ma_nsl_message3_network_term
    idα.session idα.peer idα.party rstate_α.responder_nonce (PubKey responder_key_α) in
  let out_τ = ma_output_term idτ.session idτ.party in
  let out_α = ma_output_term idα.session idα.party in
  add_commute out_τ out_α s.internal.sim_to_ideal_channel;
  Bag.remove_remove_commute msg3_τ msg3_α s.inputs;
  let s_inner_τ = ma_sim_participant_sessions (s2p_state s) idτ.party in
  let s_inner_α = ma_sim_participant_sessions (s2p_state s) idα.party in
  let v_τ : sim_participant_session_state =
    SimResponderSession { rstate_τ with output_forwarded = true } in
  let v_α : sim_participant_session_state =
    SimResponderSession { rstate_α with output_forwarded = true } in
  PartialMapExt.upd_commute s.internal.sim_participant_sessions
    idτ.party (PartialMap.upd s_inner_τ idτ.session v_τ)
    idα.party (PartialMap.upd s_inner_α idα.session v_α);
  let s_mid'_p = ma_sim_receive_message3_state (s2p_state s)
    idα.session idα.party idα.peer responder_key_α in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p s.know in
  ()
#pop-options


// Subcase: idτ.party == idα.party.
//
// If idτ.session == idα.session: τ writes output_forwarded=true at the
// shared key; α's enabledness at s_mid requires output_forwarded=false at
// that key, contradiction → trace infeasible.
//
// If idτ.session != idα.session: same outer key, different inner keys.
// The composed sim_participant_sessions[party] update is `PartialMap.upd
// (PartialMap.upd s_inner idτ.session V_τ) idα.session V_α`, which by
// inner PartialMapExt.upd_commute equals the same expression with the order
// swapped (V_α/V_τ unchanged because they're computed from rstates that
// are unaffected by the cross update — different inner keys).
#push-options "--z3rlimit 240 --fuel 3 --ifuel 3 --split_queries no"
private
let _commute_simrecv_simrecv_same_party
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (responder_key_τ responder_key_α: priv_key)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        idτ.party == idα.party /\
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idτ.role == Responder /\ idα.role == Responder /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_sim_receive_message3_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer responder_key_α /\
        s2p_state s' == ma_sim_receive_message3_state (s2p_state s_mid)
                          idα.session idα.party idα.peer responder_key_α /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let rstate_τ = Some?.v (ma_sim_responder_session_state (s2p_state s) idτ.party idτ.session) in
  // The SMTPat on
  // `ma_sim_receive_message3_state_get_updated_sim_participant_session_state`
  // tells z3: lookup at (idα.party, idα.session) after τ equals either
  // the updated entry (if same session) or the pre-τ entry. Combined with
  // α-enabledness requiring `not output_forwarded`, this rules out
  // idτ.session == idα.session.
  assert (Some? (ma_sim_responder_session_state (s2p_state s_mid) idα.party idα.session));
  if idτ.session = idα.session then begin
    // Vacuous: output_forwarded clash. Force z3 to look at the entry.
    ma_sim_receive_message3_state_get_updated_sim_participant_session_state
      (s2p_state s) idτ.session idτ.party idτ.peer responder_key_τ
      idα.party idα.session
  end
  else begin
    // Same outer key (party), different inner keys (session). The
    // composed sim_participant_sessions update is
    //   outer_upd s.sps party (inner_upd (inner_upd s_inner sτ Vτ) sα Vα)
    // when τ then α; the swapped order swaps the inner updates. By
    // PartialMapExt.upd_commute (sτ != sα), the inner maps are equal; by outer
    // record equality, the whole sim_participant_sessions matches.
    ma_sim_receive_message3_state_get_updated_sim_participant_session_state
      (s2p_state s) idτ.session idτ.party idτ.peer responder_key_τ
      idα.party idα.session;
    // Preservation hints for τ (so rstate_α at s_mid agrees with at s).
    ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
      idτ.session idτ.party idτ.peer responder_key_τ;
    ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
      idτ.session idτ.party idτ.peer responder_key_τ;
    ma_sim_receive_message3_state_preserves_requests (s2p_state s)
      idτ.session idτ.party idτ.peer responder_key_τ;
    ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
      idτ.session idτ.party idτ.peer responder_key_τ;
    ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
      idτ.session idτ.party idτ.peer responder_key_τ;
    ma_sim_receive_message3_state_inputs_eq (s2p_state s)
      idτ.session idτ.party idτ.peer responder_key_τ;
    // Same hints with α-params at state s (rstate_α and msg3_α exist there).
    let rstate_α = Some?.v (ma_sim_responder_session_state (s2p_state s) idα.party idα.session) in
    ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
      idα.session idα.party idα.peer responder_key_α;
    ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
      idα.session idα.party idα.peer responder_key_α;
    ma_sim_receive_message3_state_preserves_requests (s2p_state s)
      idα.session idα.party idα.peer responder_key_α;
    ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
      idα.session idα.party idα.peer responder_key_α;
    ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
      idα.session idα.party idα.peer responder_key_α;
    ma_sim_receive_message3_state_inputs_eq (s2p_state s)
      idα.session idα.party idα.peer responder_key_α;
    let msg3_τ = ma_nsl_message3_network_term
      idτ.session idτ.peer idτ.party rstate_τ.responder_nonce (PubKey responder_key_τ) in
    let msg3_α = ma_nsl_message3_network_term
      idα.session idα.peer idα.party rstate_α.responder_nonce (PubKey responder_key_α) in
    let out_τ = ma_output_term idτ.session idτ.party in
    let out_α = ma_output_term idα.session idα.party in
    add_commute out_τ out_α s.internal.sim_to_ideal_channel;
    Bag.remove_remove_commute msg3_τ msg3_α s.inputs;
    // Inner-map commutativity: at the shared outer party.
    let s_inner = ma_sim_participant_sessions (s2p_state s) idτ.party in
    let v_τ : sim_participant_session_state =
      SimResponderSession { rstate_τ with output_forwarded = true } in
    let v_α : sim_participant_session_state =
      SimResponderSession { rstate_α with output_forwarded = true } in
    PartialMapExt.upd_commute s_inner idτ.session v_τ idα.session v_α;
    // Also do the outer-with-same-key collapse on sim_participant_sessions:
    // upd (upd m k v1) k v2 == upd m k v2 — this gives us the composite map
    // equality that z3 needs to identify s_mid'_p's inner map.
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idτ.party
          (PartialMap.upd s_inner idτ.session v_τ))
        idα.party
        (PartialMap.upd
          (PartialMap.upd s_inner idτ.session v_τ)
          idα.session v_α))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd
          (PartialMap.upd s_inner idτ.session v_τ)
          idα.session v_α));
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idα.party
          (PartialMap.upd s_inner idα.session v_α))
        idτ.party
        (PartialMap.upd
          (PartialMap.upd s_inner idα.session v_α)
          idτ.session v_τ))
      (PartialMap.upd s.internal.sim_participant_sessions idα.party
        (PartialMap.upd
          (PartialMap.upd s_inner idα.session v_α)
          idτ.session v_τ));
    let s_mid'_p = ma_sim_receive_message3_state (s2p_state s)
      idα.session idα.party idα.peer responder_key_α in
    let s_mid' : ideal_system_state = p2s_state s_mid'_p s.know in
    ()
  end
#pop-options


// Combined dispatcher for simrecv x simrecv that picks the right per-case
// proof or derives False from the vacuous coincidence case.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_simrecv_simrecv
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (responder_key_τ responder_key_α: priv_key)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idτ.role == Responder /\ idα.role == Responder /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_sim_receive_message3_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer responder_key_α /\
        s2p_state s' == ma_sim_receive_message3_state (s2p_state s_mid)
                          idα.session idα.party idα.peer responder_key_α /\
        s'.know == s_mid.know)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  if idτ.party <> idα.party then
    _commute_simrecv_simrecv_diff_party corrupt key_directory know0
      idτ idα responder_key_τ responder_key_α s s_mid s'
  else
    _commute_simrecv_simrecv_same_party corrupt key_directory know0
      idτ idα responder_key_τ responder_key_α s s_mid s'
#pop-options


// ---- Dispatcher for tau internal × alpha = Internal idα ----

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2 --split_queries no"
private
let _ideal_internal_internal_commute
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal idτ) s_mid /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid (TestedSystem.Internal idα) s')
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid' (TestedSystem.Internal idτ) s') =
  let the_goal : prop =
    exists s_mid'.
      (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal idα) s_mid' /\
      (ma_ideal_system corrupt key_directory know0).transitions s_mid' (TestedSystem.Internal idτ) s' in
  let s_p = s2p_state s in
  let s_mid_p = s2p_state s_mid in
  let s'_p = s2p_state s' in
  let tau_init_prop : prop =
    ma_ideal_initiate_protocol_transition s_p idτ.session idτ.party idτ.peer idτ.role s_mid_p in
  let tau_recv_prop : prop =
    (match idτ.role with
     | Responder ->
       ma_sim_receive_message3_protocol_transition s_p idτ.session idτ.party idτ.peer s_mid_p
     | Initiator -> False) in
  let alpha_init_prop : prop =
    ma_ideal_initiate_protocol_transition s_mid_p idα.session idα.party idα.peer idα.role s'_p in
  let alpha_recv_prop : prop =
    (match idα.role with
     | Responder ->
       ma_sim_receive_message3_protocol_transition s_mid_p idα.session idα.party idα.peer s'_p
     | Initiator -> False) in
  let handle_init_init (_: squash tau_init_prop) (_: squash alpha_init_prop)
    : Lemma the_goal =
    _commute_initiate_initiate corrupt key_directory know0 idτ idα s s_mid s'
  in
  let handle_init_recv (_: squash tau_init_prop) (_: squash alpha_recv_prop)
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #priv_key
      #(fun rk_α ->
         ma_sim_receive_message3_enabled s_mid_p idα.session idα.party idα.peer rk_α /\
         s'_p == ma_sim_receive_message3_state s_mid_p
                   idα.session idα.party idα.peer rk_α)
      ()
      (fun rk_α ->
        _commute_initiate_simrecv corrupt key_directory know0 idτ idα rk_α s s_mid s')
  in
  let handle_recv_init (_: squash tau_recv_prop) (_: squash alpha_init_prop)
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #priv_key
      #(fun rk_τ ->
         ma_sim_receive_message3_enabled s_p idτ.session idτ.party idτ.peer rk_τ /\
         s_mid_p == ma_sim_receive_message3_state s_p
                      idτ.session idτ.party idτ.peer rk_τ)
      ()
      (fun rk_τ ->
        _commute_simrecv_initiate corrupt key_directory know0 idτ idα rk_τ s s_mid s')
  in
  let handle_recv_recv (_: squash tau_recv_prop) (_: squash alpha_recv_prop)
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #priv_key
      #(fun rk_τ ->
         ma_sim_receive_message3_enabled s_p idτ.session idτ.party idτ.peer rk_τ /\
         s_mid_p == ma_sim_receive_message3_state s_p
                      idτ.session idτ.party idτ.peer rk_τ)
      ()
      (fun rk_τ ->
        FStar.Classical.exists_elim the_goal #priv_key
          #(fun rk_α ->
             ma_sim_receive_message3_enabled s_mid_p idα.session idα.party idα.peer rk_α /\
             s'_p == ma_sim_receive_message3_state s_mid_p
                       idα.session idα.party idα.peer rk_α)
          ()
          (fun rk_α ->
            _commute_simrecv_simrecv corrupt key_directory know0 idτ idα rk_τ rk_α s s_mid s'))
  in
  // For each of τ and α, the protocol transition is the disjunction
  // tau_init_prop ∨ tau_recv_prop (similarly for α). Dispatch via or_elim
  // on both disjunctions.
  let handle_tau_init (_: squash tau_init_prop) : Lemma the_goal =
    FStar.Classical.or_elim
      #alpha_init_prop #alpha_recv_prop #(fun _ -> the_goal)
      (fun h -> handle_init_init () h)
      (fun h -> handle_init_recv () h)
  in
  let handle_tau_recv (_: squash tau_recv_prop) : Lemma the_goal =
    FStar.Classical.or_elim
      #alpha_init_prop #alpha_recv_prop #(fun _ -> the_goal)
      (fun h -> handle_recv_init () h)
      (fun h -> handle_recv_recv () h)
  in
  FStar.Classical.or_elim
    #tau_init_prop #tau_recv_prop #(fun _ -> the_goal)
    handle_tau_init
    handle_tau_recv
#pop-options


// ---- tau internal × alpha = Observable NetSend idα ----
//
// Decomposed into six per-pair helpers (one per (τ-kind, α-kind)
// combination), dispatched via or_elim + exists_elim.

// (1) τ = ma_ideal_initiate, α = ma_sim_send_message1 (Initiator role).
// State pieces overlap only in ideal_to_sim_channel: τ adds the
// authenticating term, α removes it. Partition-distinctness forces the
// two terms to differ, so Set.add/Set.remove commute.
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_initiate_send1
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (initiator_nonce: nonce)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_t: term) (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idα.role == Initiator /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        ma_sim_send_message1_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer initiator_nonce responder_pubkey /\
        sent_t == ma_nsl_message1_term idα.session idα.party idα.peer
                    initiator_nonce responder_pubkey /\
        s2p_state s' == ma_sim_send_message1_state (s2p_state s_mid)
                          idα.session idα.party idα.peer initiator_nonce /\
        s'.know == Seq.snoc s_mid.know sent_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let authing_τ = ma_authenticating_term idτ.session idτ.party idτ.peer idτ.role in
  let authing_α = ma_authenticating_term idα.session idα.party idα.peer Initiator in
  add_remove_commute authing_τ authing_α s.internal.ideal_to_sim_channel;
  remove_add_commute authing_α authing_τ s.internal.ideal_to_sim_channel;
  let s_mid'_p = ma_sim_send_message1_state (s2p_state s)
    idα.session idα.party idα.peer initiator_nonce in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know sent_t) in
  ()
#pop-options


// (2) τ = ma_ideal_initiate, α = ma_sim_send_message2 (Responder role).
// Overlaps: inputs (different terms) and ideal_to_sim_channel (different
// auth terms when partition-distinct).
#push-options "--z3rlimit 180 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_initiate_send2
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (initiator_nonce responder_nonce: nonce) (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (sent_t: term) (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idα.role == Responder /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        ma_sim_send_message2_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer initiator_nonce responder_nonce
          responder_key initiator_pubkey /\
        sent_t == ma_nsl_message2_term idα.session idα.peer idα.party
                    initiator_nonce responder_nonce initiator_pubkey /\
        s2p_state s' == ma_sim_send_message2_state (s2p_state s_mid)
                          idα.session idα.party idα.peer
                          initiator_nonce responder_nonce responder_key /\
        s'.know == Seq.snoc s_mid.know sent_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let authing_τ = ma_authenticating_term idτ.session idτ.party idτ.peer idτ.role in
  let authing_α = ma_authenticating_term idα.session idα.party idα.peer Responder in
  let auth_input_τ = ma_auth_input_term idτ.session idτ.party idτ.peer idτ.role in
  let msg1_α = ma_nsl_message1_network_term idα.session idα.peer idα.party
    initiator_nonce (PubKey responder_key) in
  add_remove_commute authing_τ authing_α s.internal.ideal_to_sim_channel;
  remove_add_commute authing_α authing_τ s.internal.ideal_to_sim_channel;
  Bag.remove_remove_commute auth_input_τ msg1_α s.inputs;
  let s_mid'_p = ma_sim_send_message2_state (s2p_state s)
    idα.session idα.party idα.peer initiator_nonce responder_nonce responder_key in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know sent_t) in
  ()
#pop-options


// (4) τ = ma_sim_receive_message3, α = ma_sim_send_message1. Overlaps in
// sim_participant_sessions. Feasibility (α requires no existing entry at
// (α.party, α.session); τ's update is on (τ.party, τ.session)) blocks
// coincidence; otherwise PartialMap.upd commutes on different keys.
#push-options "--z3rlimit 240 --fuel 3 --ifuel 3 --split_queries no"
private
let _commute_simrecv_send1
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (responder_key_τ: priv_key)
      (initiator_nonce: nonce) (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_t: term) (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idτ.role == Responder /\ idα.role == Initiator /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_sim_send_message1_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer initiator_nonce responder_pubkey /\
        sent_t == ma_nsl_message1_term idα.session idα.party idα.peer
                    initiator_nonce responder_pubkey /\
        s2p_state s' == ma_sim_send_message1_state (s2p_state s_mid)
                          idα.session idα.party idα.peer initiator_nonce /\
        s'.know == Seq.snoc s_mid.know sent_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  // Chain the sim_participant_sessions lookup at (α.party, α.session)
  // through τ's update so z3 sees the SimResponderSession vs no-entry
  // dichotomy. In particular, if (idτ.party, idτ.session) ==
  // (idα.party, idα.session), the lookup at s_mid is Some, but α-enabled
  // requires not contains — contradiction.
  ma_sim_receive_message3_state_get_updated_sim_participant_session_state
    (s2p_state s) idτ.session idτ.party idτ.peer responder_key_τ
    idα.party idα.session;
  let s_p = s2p_state s in
  let rstate_τ = Some?.v (ma_sim_responder_session_state s_p idτ.party idτ.session) in
  let v_τ : sim_participant_session_state =
    SimResponderSession { rstate_τ with output_forwarded = true } in
  let v_α : sim_participant_session_state =
    SimInitiatorSession
      { initiator = idα.party; responder = idα.peer;
        initiator_nonce = initiator_nonce; ack_sent = false } in
  let inner_τ_s = ma_sim_participant_sessions s_p idτ.party in
  let inner_α_s = ma_sim_participant_sessions s_p idα.party in
  let s_mid'_p = ma_sim_send_message1_state s_p
    idα.session idα.party idα.peer initiator_nonce in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know sent_t) in
  // Outer-key disjointness case: party_τ != party_α.
  if idτ.party <> idα.party then begin
    PartialMapExt.upd_commute s.internal.sim_participant_sessions
      idτ.party (PartialMap.upd inner_τ_s idτ.session v_τ)
      idα.party (PartialMap.upd inner_α_s idα.session v_α)
  end
  else begin
    // Same outer key party_τ == party_α. The coincidence
    // sess_τ == sess_α is excluded by α's not-contains requirement at
    // s_mid (the SMTPat above gives the contradiction).
    // For sess_τ != sess_α, do inner-map commutativity and outer collapse.
    let inner = inner_τ_s in  // == inner_α_s
    PartialMapExt.upd_commute inner idτ.session v_τ idα.session v_α;
    // Forward composite: outer_upd (outer_upd SPS p (inner_upd inner sess_τ v_τ))
    //                              p (inner_upd (inner_upd inner sess_τ v_τ) sess_α v_α)
    // == outer_upd SPS p (inner_upd (inner_upd inner sess_τ v_τ) sess_α v_α)
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idτ.party
          (PartialMap.upd inner idτ.session v_τ))
        idα.party
        (PartialMap.upd (PartialMap.upd inner idτ.session v_τ) idα.session v_α))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd (PartialMap.upd inner idτ.session v_τ) idα.session v_α));
    // Reverse composite: outer_upd (outer_upd SPS p (inner_upd inner sess_α v_α))
    //                              p (inner_upd (inner_upd inner sess_α v_α) sess_τ v_τ)
    // == outer_upd SPS p (inner_upd (inner_upd inner sess_α v_α) sess_τ v_τ)
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idα.party
          (PartialMap.upd inner idα.session v_α))
        idτ.party
        (PartialMap.upd (PartialMap.upd inner idα.session v_α) idτ.session v_τ))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd (PartialMap.upd inner idα.session v_α) idτ.session v_τ))
  end
#pop-options


// (5) τ = ma_sim_receive_message3, α = ma_sim_send_message2.
#push-options "--z3rlimit 240 --fuel 3 --ifuel 3 --split_queries no"
private
let _commute_simrecv_send2
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (responder_key_τ: priv_key)
      (initiator_nonce responder_nonce: nonce) (responder_key: priv_key)
      (initiator_pubkey: term {PubKey? initiator_pubkey})
      (sent_t: term) (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idτ.role == Responder /\ idα.role == Responder /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_sim_send_message2_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer initiator_nonce responder_nonce
          responder_key initiator_pubkey /\
        sent_t == ma_nsl_message2_term idα.session idα.peer idα.party
                    initiator_nonce responder_nonce initiator_pubkey /\
        s2p_state s' == ma_sim_send_message2_state (s2p_state s_mid)
                          idα.session idα.party idα.peer
                          initiator_nonce responder_nonce responder_key /\
        s'.know == Seq.snoc s_mid.know sent_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let rstate_τ = Some?.v (ma_sim_responder_session_state (s2p_state s) idτ.party idτ.session) in
  let msg3_τ = ma_nsl_message3_network_term
    idτ.session idτ.peer idτ.party rstate_τ.responder_nonce (PubKey responder_key_τ) in
  let msg1_α = ma_nsl_message1_network_term idα.session idα.peer idα.party
    initiator_nonce (PubKey responder_key) in
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  Bag.remove_remove_commute msg3_τ msg1_α s.inputs;
  // Same overlap structure as _commute_simrecv_send1: τ updates
  // sim_participant_sessions at (τ.party, τ.session); α adds new
  // SimResponderSession at (α.party, α.session). The SMTPat below rules
  // out the coincidence case (α-enabled at s_mid requires not contains).
  ma_sim_receive_message3_state_get_updated_sim_participant_session_state
    (s2p_state s) idτ.session idτ.party idτ.peer responder_key_τ
    idα.party idα.session;
  let s_p = s2p_state s in
  let v_τ : sim_participant_session_state =
    SimResponderSession { rstate_τ with output_forwarded = true } in
  let v_α : sim_participant_session_state =
    SimResponderSession
      { responder = idα.party; initiator = idα.peer;
        responder_nonce = responder_nonce; output_forwarded = false } in
  let inner_τ_s = ma_sim_participant_sessions s_p idτ.party in
  let inner_α_s = ma_sim_participant_sessions s_p idα.party in
  let s_mid'_p = ma_sim_send_message2_state s_p
    idα.session idα.party idα.peer initiator_nonce responder_nonce responder_key in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know sent_t) in
  if idτ.party <> idα.party then begin
    PartialMapExt.upd_commute s.internal.sim_participant_sessions
      idτ.party (PartialMap.upd inner_τ_s idτ.session v_τ)
      idα.party (PartialMap.upd inner_α_s idα.session v_α)
  end
  else begin
    let inner = inner_τ_s in  // == inner_α_s
    PartialMapExt.upd_commute inner idτ.session v_τ idα.session v_α;
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idτ.party
          (PartialMap.upd inner idτ.session v_τ))
        idα.party
        (PartialMap.upd (PartialMap.upd inner idτ.session v_τ) idα.session v_α))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd (PartialMap.upd inner idτ.session v_τ) idα.session v_α));
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idα.party
          (PartialMap.upd inner idα.session v_α))
        idτ.party
        (PartialMap.upd (PartialMap.upd inner idα.session v_α) idτ.session v_τ))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd (PartialMap.upd inner idα.session v_α) idτ.session v_τ))
  end
#pop-options


// (6) τ = ma_sim_receive_message3, α = ma_sim_send_message3.
#push-options "--z3rlimit 240 --fuel 3 --ifuel 3 --split_queries no"
private
let _commute_simrecv_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id) (responder_key_τ: priv_key)
      (responder_nonce: nonce) (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_t: term) (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idτ.role == Responder /\ idα.role == Initiator /\
        ma_sim_receive_message3_enabled (s2p_state s)
          idτ.session idτ.party idτ.peer responder_key_τ /\
        s2p_state s_mid == ma_sim_receive_message3_state (s2p_state s)
                             idτ.session idτ.party idτ.peer responder_key_τ /\
        s_mid.know == s.know /\
        ma_sim_send_message3_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer responder_nonce initiator_key responder_pubkey /\
        sent_t == ma_nsl_message3_term idα.session idα.party idα.peer
                    responder_nonce responder_pubkey /\
        s2p_state s' == ma_sim_send_message3_state (s2p_state s_mid)
                          idα.session idα.party idα.peer responder_nonce initiator_key /\
        s'.know == Seq.snoc s_mid.know sent_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let rstate_τ = Some?.v (ma_sim_responder_session_state (s2p_state s) idτ.party idτ.session) in
  let istate_α = Some?.v (ma_sim_initiator_session_state (s2p_state s_mid) idα.party idα.session) in
  let msg3_τ = ma_nsl_message3_network_term
    idτ.session idτ.peer idτ.party rstate_τ.responder_nonce (PubKey responder_key_τ) in
  let msg2_α = ma_nsl_message2_network_term idα.session idα.party idα.peer
    istate_α.initiator_nonce responder_nonce (PubKey initiator_key) in
  let out_τ = ma_output_term idτ.session idτ.party in
  let out_α = ma_output_term idα.session idα.party in
  ma_sim_receive_message3_state_preserves_key_directory (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_used_nonces (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_requests (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_preserves_ideal_to_sim_channel (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_sim_to_ideal_channel_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  ma_sim_receive_message3_state_inputs_eq (s2p_state s)
    idτ.session idτ.party idτ.peer responder_key_τ;
  Bag.remove_remove_commute msg3_τ msg2_α s.inputs;
  add_commute out_τ out_α s.internal.sim_to_ideal_channel;
  // SMTPat dichotomy: the lookup at (idα.party, idα.session) after τ is
  // either (i) Some (SimResponderSession ...) when (idτ.party, idτ.session)
  // coincides with (idα.party, idα.session), in which case
  // ma_sim_initiator_session_state at s_mid is None and α's enabledness
  // fails (contradiction), or (ii) equal to the lookup in s, so at s the
  // entry is a SimInitiatorSession.
  ma_sim_receive_message3_state_get_updated_sim_participant_session_state
    (s2p_state s) idτ.session idτ.party idτ.peer responder_key_τ
    idα.party idα.session;
  let s_p = s2p_state s in
  let v_τ : sim_participant_session_state =
    SimResponderSession { rstate_τ with output_forwarded = true } in
  let v_α : sim_participant_session_state =
    SimInitiatorSession { istate_α with ack_sent = true } in
  let inner_τ_s = ma_sim_participant_sessions s_p idτ.party in
  let inner_α_s = ma_sim_participant_sessions s_p idα.party in
  let s_mid'_p = ma_sim_send_message3_state s_p
    idα.session idα.party idα.peer responder_nonce initiator_key in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know sent_t) in
  if idτ.party <> idα.party then begin
    PartialMapExt.upd_commute s.internal.sim_participant_sessions
      idτ.party (PartialMap.upd inner_τ_s idτ.session v_τ)
      idα.party (PartialMap.upd inner_α_s idα.session v_α)
  end
  else begin
    // Same outer key, sess_τ != sess_α (coincidence excluded above).
    let inner = inner_τ_s in
    PartialMapExt.upd_commute inner idτ.session v_τ idα.session v_α;
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idτ.party
          (PartialMap.upd inner idτ.session v_τ))
        idα.party
        (PartialMap.upd (PartialMap.upd inner idτ.session v_τ) idα.session v_α))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd (PartialMap.upd inner idτ.session v_τ) idα.session v_α));
    PartialMap.eq_intro
      (PartialMap.upd
        (PartialMap.upd s.internal.sim_participant_sessions idα.party
          (PartialMap.upd inner idα.session v_α))
        idτ.party
        (PartialMap.upd (PartialMap.upd inner idα.session v_α) idτ.session v_τ))
      (PartialMap.upd s.internal.sim_participant_sessions idτ.party
        (PartialMap.upd (PartialMap.upd inner idα.session v_α) idτ.session v_τ))
  end
#pop-options


// (3) τ = ma_ideal_initiate, α = ma_sim_send_message3 (Initiator role).
// Overlaps: inputs only (auth_input vs msg2 net term).
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2 --split_queries no"
private
let _commute_initiate_send3
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (responder_nonce: nonce) (initiator_key: priv_key)
      (responder_pubkey: term {PubKey? responder_pubkey})
      (sent_t: term) (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        idα.role == Initiator /\
        ma_ideal_initiate_enabled (s2p_state s) idτ.session idτ.party idτ.peer idτ.role /\
        s2p_state s_mid == ma_ideal_initiate_state (s2p_state s)
                             idτ.session idτ.party idτ.peer idτ.role /\
        s_mid.know == s.know /\
        ma_sim_send_message3_enabled (s2p_state s_mid)
          idα.session idα.party idα.peer responder_nonce initiator_key responder_pubkey /\
        sent_t == ma_nsl_message3_term idα.session idα.party idα.peer
                    responder_nonce responder_pubkey /\
        s2p_state s' == ma_sim_send_message3_state (s2p_state s_mid)
                          idα.session idα.party idα.peer responder_nonce initiator_key /\
        s'.know == Seq.snoc s_mid.know sent_t)
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
            (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
            (TestedSystem.Internal idτ) s') =
  let istate_α = Some?.v (ma_sim_initiator_session_state (s2p_state s) idα.party idα.session) in
  let auth_input_τ = ma_auth_input_term idτ.session idτ.party idτ.peer idτ.role in
  let msg2_α = ma_nsl_message2_network_term idα.session idα.party idα.peer
    istate_α.initiator_nonce responder_nonce (PubKey initiator_key) in
  Bag.remove_remove_commute auth_input_τ msg2_α s.inputs;
  let s_mid'_p = ma_sim_send_message3_state (s2p_state s)
    idα.session idα.party idα.peer responder_nonce initiator_key in
  let s_mid' : ideal_system_state = p2s_state s_mid'_p (Seq.snoc s.know sent_t) in
  ()
#pop-options


#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries no"
private
let _ideal_internal_netsend_commute
      (corrupt: Set.set participant_id)
      (key_directory: PartialMap.t participant_id priv_key) (know0: knowledge term)
      (idτ idα: ma_label_id)
      (s s_mid s': ideal_system_state)
    : Lemma
      (requires
        ~(ma_label_id_in_same_partition_role idτ idα) /\
        (ma_ideal_system corrupt key_directory know0).transitions s (TestedSystem.Internal idτ) s_mid /\
        (ma_ideal_system corrupt key_directory know0).transitions s_mid
            (TestedSystem.Observable NetSend idα) s')
      (ensures
        exists s_mid'.
          (ma_ideal_system corrupt key_directory know0).transitions s
              (TestedSystem.Observable NetSend idα) s_mid' /\
          (ma_ideal_system corrupt key_directory know0).transitions s_mid'
              (TestedSystem.Internal idτ) s') =
  let the_goal : prop =
    exists s_mid'.
      (ma_ideal_system corrupt key_directory know0).transitions s
        (TestedSystem.Observable NetSend idα) s_mid' /\
      (ma_ideal_system corrupt key_directory know0).transitions s_mid'
        (TestedSystem.Internal idτ) s' in
  let s_p = s2p_state s in
  let s_mid_p = s2p_state s_mid in
  let s'_p = s2p_state s' in
  // τ kind disjunction.
  let tau_init_prop : prop =
    ma_ideal_initiate_protocol_transition s_p idτ.session idτ.party idτ.peer idτ.role s_mid_p in
  let tau_recv_prop : prop =
    (match idτ.role with
     | Responder ->
       ma_sim_receive_message3_protocol_transition s_p idτ.session idτ.party idτ.peer s_mid_p
     | Initiator -> False) in
  // α-NetSend, given t. Decomposes by idα.role. Each pred also carries
  // the knowledge equation extracted from the existential, so it
  // propagates to the per-pair helpers.
  let alpha_send1_t (t: term) : prop =
    idα.role == Initiator /\
    ma_sim_send_message1_protocol_transition s_mid_p
      idα.session idα.party idα.peer t s'_p /\
    s'.know == Seq.snoc s_mid.know t in
  let alpha_send3_t (t: term) : prop =
    idα.role == Initiator /\
    ma_sim_send_message3_protocol_transition s_mid_p
      idα.session idα.party idα.peer t s'_p /\
    s'.know == Seq.snoc s_mid.know t in
  let alpha_send2_t (t: term) : prop =
    idα.role == Responder /\
    ma_sim_send_message2_protocol_transition s_mid_p
      idα.session idα.party idα.peer t s'_p /\
    s'.know == Seq.snoc s_mid.know t in
  // Per-pair handlers using the six already-proved helpers.
  let handle_init_send1 (t: term)
    (_: squash tau_init_prop) (_: squash (alpha_send1_t t))
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #nonce
      #(fun init_n ->
          exists (resp_pk: term {PubKey? resp_pk}).
            ma_sim_send_message1_enabled s_mid_p idα.session idα.party idα.peer init_n resp_pk /\
            t == ma_nsl_message1_term idα.session idα.party idα.peer init_n resp_pk /\
            s'_p == ma_sim_send_message1_state s_mid_p idα.session idα.party idα.peer init_n)
      ()
      (fun init_n ->
        FStar.Classical.exists_elim the_goal #(t: term {PubKey? t})
          #(fun resp_pk ->
              ma_sim_send_message1_enabled s_mid_p idα.session idα.party idα.peer init_n resp_pk /\
              t == ma_nsl_message1_term idα.session idα.party idα.peer init_n resp_pk /\
              s'_p == ma_sim_send_message1_state s_mid_p idα.session idα.party idα.peer init_n)
          ()
          (fun resp_pk ->
            _commute_initiate_send1 corrupt key_directory know0 idτ idα init_n resp_pk t s s_mid s'))
  in
  let handle_init_send2 (t: term)
    (_: squash tau_init_prop) (_: squash (alpha_send2_t t))
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #nonce
      #(fun init_n ->
          exists (resp_n: nonce) (resp_key: priv_key) (init_pk: term {PubKey? init_pk}).
            ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
              init_n resp_n resp_key init_pk /\
            t == ma_nsl_message2_term idα.session idα.peer idα.party init_n resp_n init_pk /\
            s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                      init_n resp_n resp_key)
      ()
      (fun init_n ->
        FStar.Classical.exists_elim the_goal #nonce
          #(fun resp_n ->
              exists (resp_key: priv_key) (init_pk: term {PubKey? init_pk}).
                ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                  init_n resp_n resp_key init_pk /\
                t == ma_nsl_message2_term idα.session idα.peer idα.party init_n resp_n init_pk /\
                s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                          init_n resp_n resp_key)
          ()
          (fun resp_n ->
            FStar.Classical.exists_elim the_goal #priv_key
              #(fun resp_key ->
                  exists (init_pk: term {PubKey? init_pk}).
                    ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                      init_n resp_n resp_key init_pk /\
                    t == ma_nsl_message2_term idα.session idα.peer idα.party init_n resp_n init_pk /\
                    s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                              init_n resp_n resp_key)
              ()
              (fun resp_key ->
                FStar.Classical.exists_elim the_goal #(t: term {PubKey? t})
                  #(fun init_pk ->
                      ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                        init_n resp_n resp_key init_pk /\
                      t == ma_nsl_message2_term idα.session idα.peer idα.party
                                  init_n resp_n init_pk /\
                      s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                                init_n resp_n resp_key)
                  ()
                  (fun init_pk ->
                    _commute_initiate_send2 corrupt key_directory know0 idτ idα
                      init_n resp_n resp_key init_pk t s s_mid s'))))
  in
  let handle_init_send3 (t: term)
    (_: squash tau_init_prop) (_: squash (alpha_send3_t t))
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #nonce
      #(fun resp_n ->
          exists (init_key: priv_key) (resp_pk: term {PubKey? resp_pk}).
            ma_sim_send_message3_enabled s_mid_p idα.session idα.party idα.peer
              resp_n init_key resp_pk /\
            t == ma_nsl_message3_term idα.session idα.party idα.peer resp_n resp_pk /\
            s'_p == ma_sim_send_message3_state s_mid_p idα.session idα.party idα.peer
                      resp_n init_key)
      ()
      (fun resp_n ->
        FStar.Classical.exists_elim the_goal #priv_key
          #(fun init_key ->
              exists (resp_pk: term {PubKey? resp_pk}).
                ma_sim_send_message3_enabled s_mid_p idα.session idα.party idα.peer
                  resp_n init_key resp_pk /\
                t == ma_nsl_message3_term idα.session idα.party idα.peer resp_n resp_pk /\
                s'_p == ma_sim_send_message3_state s_mid_p idα.session idα.party idα.peer
                          resp_n init_key)
          ()
          (fun init_key ->
            FStar.Classical.exists_elim the_goal #(t: term {PubKey? t})
              #(fun resp_pk ->
                  ma_sim_send_message3_enabled s_mid_p idα.session idα.party idα.peer
                    resp_n init_key resp_pk /\
                  t == ma_nsl_message3_term idα.session idα.party idα.peer resp_n resp_pk /\
                  s'_p == ma_sim_send_message3_state s_mid_p idα.session idα.party idα.peer
                            resp_n init_key)
              ()
              (fun resp_pk ->
                _commute_initiate_send3 corrupt key_directory know0 idτ idα
                  resp_n init_key resp_pk t s s_mid s')))
  in
  let handle_recv_send1 (t: term)
    (_: squash tau_recv_prop) (_: squash (alpha_send1_t t))
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #priv_key
      #(fun rk_τ ->
          ma_sim_receive_message3_enabled s_p idτ.session idτ.party idτ.peer rk_τ /\
          s_mid_p == ma_sim_receive_message3_state s_p
                       idτ.session idτ.party idτ.peer rk_τ)
      ()
      (fun rk_τ ->
        FStar.Classical.exists_elim the_goal #nonce
          #(fun init_n ->
              exists (resp_pk: term {PubKey? resp_pk}).
                ma_sim_send_message1_enabled s_mid_p idα.session idα.party idα.peer init_n resp_pk /\
                t == ma_nsl_message1_term idα.session idα.party idα.peer init_n resp_pk /\
                s'_p == ma_sim_send_message1_state s_mid_p idα.session idα.party idα.peer init_n)
          ()
          (fun init_n ->
            FStar.Classical.exists_elim the_goal #(t: term {PubKey? t})
              #(fun resp_pk ->
                  ma_sim_send_message1_enabled s_mid_p idα.session idα.party idα.peer init_n resp_pk /\
                  t == ma_nsl_message1_term idα.session idα.party idα.peer init_n resp_pk /\
                  s'_p == ma_sim_send_message1_state s_mid_p idα.session idα.party idα.peer init_n)
              ()
              (fun resp_pk ->
                _commute_simrecv_send1 corrupt key_directory know0 idτ idα rk_τ init_n resp_pk t s s_mid s')))
  in
  let handle_recv_send2 (t: term)
    (_: squash tau_recv_prop) (_: squash (alpha_send2_t t))
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #priv_key
      #(fun rk_τ ->
          ma_sim_receive_message3_enabled s_p idτ.session idτ.party idτ.peer rk_τ /\
          s_mid_p == ma_sim_receive_message3_state s_p
                       idτ.session idτ.party idτ.peer rk_τ)
      ()
      (fun rk_τ ->
        FStar.Classical.exists_elim the_goal #nonce
          #(fun init_n ->
              exists (resp_n: nonce) (resp_key: priv_key) (init_pk: term {PubKey? init_pk}).
                ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                  init_n resp_n resp_key init_pk /\
                t == ma_nsl_message2_term idα.session idα.peer idα.party init_n resp_n init_pk /\
                s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                          init_n resp_n resp_key)
          ()
          (fun init_n ->
            FStar.Classical.exists_elim the_goal #nonce
              #(fun resp_n ->
                  exists (resp_key: priv_key) (init_pk: term {PubKey? init_pk}).
                    ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                      init_n resp_n resp_key init_pk /\
                    t == ma_nsl_message2_term idα.session idα.peer idα.party init_n resp_n init_pk /\
                    s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                              init_n resp_n resp_key)
              ()
              (fun resp_n ->
                FStar.Classical.exists_elim the_goal #priv_key
                  #(fun resp_key ->
                      exists (init_pk: term {PubKey? init_pk}).
                        ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                          init_n resp_n resp_key init_pk /\
                        t == ma_nsl_message2_term idα.session idα.peer idα.party
                                    init_n resp_n init_pk /\
                        s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                                  init_n resp_n resp_key)
                  ()
                  (fun resp_key ->
                    FStar.Classical.exists_elim the_goal #(t: term {PubKey? t})
                      #(fun init_pk ->
                          ma_sim_send_message2_enabled s_mid_p idα.session idα.party idα.peer
                            init_n resp_n resp_key init_pk /\
                          t == ma_nsl_message2_term idα.session idα.peer idα.party
                                      init_n resp_n init_pk /\
                          s'_p == ma_sim_send_message2_state s_mid_p idα.session idα.party idα.peer
                                    init_n resp_n resp_key)
                      ()
                      (fun init_pk ->
                        _commute_simrecv_send2 corrupt key_directory know0 idτ idα rk_τ
                          init_n resp_n resp_key init_pk t s s_mid s')))))
  in
  let handle_recv_send3 (t: term)
    (_: squash tau_recv_prop) (_: squash (alpha_send3_t t))
    : Lemma the_goal =
    FStar.Classical.exists_elim the_goal #priv_key
      #(fun rk_τ ->
          ma_sim_receive_message3_enabled s_p idτ.session idτ.party idτ.peer rk_τ /\
          s_mid_p == ma_sim_receive_message3_state s_p
                       idτ.session idτ.party idτ.peer rk_τ)
      ()
      (fun rk_τ ->
        FStar.Classical.exists_elim the_goal #nonce
          #(fun resp_n ->
              exists (init_key: priv_key) (resp_pk: term {PubKey? resp_pk}).
                ma_sim_send_message3_enabled s_mid_p idα.session idα.party idα.peer
                  resp_n init_key resp_pk /\
                t == ma_nsl_message3_term idα.session idα.party idα.peer resp_n resp_pk /\
                s'_p == ma_sim_send_message3_state s_mid_p idα.session idα.party idα.peer
                          resp_n init_key)
          ()
          (fun resp_n ->
            FStar.Classical.exists_elim the_goal #priv_key
              #(fun init_key ->
                  exists (resp_pk: term {PubKey? resp_pk}).
                    ma_sim_send_message3_enabled s_mid_p idα.session idα.party idα.peer
                      resp_n init_key resp_pk /\
                    t == ma_nsl_message3_term idα.session idα.party idα.peer resp_n resp_pk /\
                    s'_p == ma_sim_send_message3_state s_mid_p idα.session idα.party idα.peer
                              resp_n init_key)
              ()
              (fun init_key ->
                FStar.Classical.exists_elim the_goal #(t: term {PubKey? t})
                  #(fun resp_pk ->
                      ma_sim_send_message3_enabled s_mid_p idα.session idα.party idα.peer
                        resp_n init_key resp_pk /\
                      t == ma_nsl_message3_term idα.session idα.party idα.peer resp_n resp_pk /\
                      s'_p == ma_sim_send_message3_state s_mid_p idα.session idα.party idα.peer
                                resp_n init_key)
                  ()
                  (fun resp_pk ->
                    _commute_simrecv_send3 corrupt key_directory know0 idτ idα rk_τ
                      resp_n init_key resp_pk t s s_mid s'))))
  in
  // Given t with α-NetSend, dispatch on idα.role and on send1 vs send3
  // (when Initiator) using or_elim. The knowledge equation must travel
  // with the send disjunction since alpha_send*_t carry it.
  let handle_with_t_init (t: term)
      (h_role: squash (idα.role == Initiator))
      (h_know: squash (s'.know == Seq.snoc s_mid.know t))
      (h_send: squash (
        ma_sim_send_message1_protocol_transition s_mid_p
          idα.session idα.party idα.peer t s'_p \/
        ma_sim_send_message3_protocol_transition s_mid_p
          idα.session idα.party idα.peer t s'_p))
    : Lemma (requires tau_init_prop \/ tau_recv_prop)
            (ensures the_goal) =
    FStar.Classical.or_elim
      #(ma_sim_send_message1_protocol_transition s_mid_p
          idα.session idα.party idα.peer t s'_p)
      #(ma_sim_send_message3_protocol_transition s_mid_p
          idα.session idα.party idα.peer t s'_p)
      #(fun _ -> the_goal)
      (fun h1 ->
        FStar.Classical.or_elim
          #tau_init_prop #tau_recv_prop #(fun _ -> the_goal)
          (fun ht -> handle_init_send1 t ht ())
          (fun ht -> handle_recv_send1 t ht ()))
      (fun h3 ->
        FStar.Classical.or_elim
          #tau_init_prop #tau_recv_prop #(fun _ -> the_goal)
          (fun ht -> handle_init_send3 t ht ())
          (fun ht -> handle_recv_send3 t ht ()))
  in
  let handle_with_t_resp (t: term)
      (h_role: squash (idα.role == Responder))
      (h_know: squash (s'.know == Seq.snoc s_mid.know t))
      (h_send: squash (
        ma_sim_send_message2_protocol_transition s_mid_p
          idα.session idα.party idα.peer t s'_p))
    : Lemma (requires tau_init_prop \/ tau_recv_prop)
            (ensures the_goal) =
    FStar.Classical.or_elim
      #tau_init_prop #tau_recv_prop #(fun _ -> the_goal)
      (fun ht -> handle_init_send2 t ht ())
      (fun ht -> handle_recv_send2 t ht ())
  in
  let handle_with_t (t: term)
      (h_t: squash (
        ma_ideal_protocol_transition s_mid_p
          (Protocol.Observable NetSend t idα) s'_p /\
        s'.know == Seq.snoc s_mid.know t))
    : Lemma (requires tau_init_prop \/ tau_recv_prop)
            (ensures the_goal) =
    // The protocol transition for NetSend depends on idα.role.
    match idα.role with
    | Initiator -> handle_with_t_init t () () ()
    | Responder -> handle_with_t_resp t () () ()
  in
  // Eliminate the existential `t` from the α transition, then the τ
  // disjunction.
  assert (tau_init_prop \/ tau_recv_prop);
  FStar.Classical.exists_elim the_goal #term
    #(fun t ->
        ma_ideal_protocol_transition s_mid_p
          (Protocol.Observable NetSend t idα) s'_p /\
        s'.know == Seq.snoc s_mid.know t)
    ()
    (fun t -> handle_with_t t ())
#pop-options


/// ----------------------------------------------------------------------
/// The main right-movability theorem.
///
/// Dispatches on the shape of `alpha`. Every role-distinct pair `(tau, alpha)`
/// that is NOT one of the infeasible deliver configurations (A)/(B) genuinely
/// commutes: the two transitions touch disjoint state and the swapped witness
/// `s_mid'` is reconstructed by the corresponding lemma:
///   * `alpha` is `Internal`        — `_ideal_internal_internal_commute`;
///   * `alpha` is `Observable NetSend` — `_ideal_internal_netsend_commute`;
///   * `alpha` is `Input`           — `_ideal_input_commute`;
///   * `alpha = Observable IoSend idα` (a deliver) but NOT of the (A) shape
///     (`tau = initiate`, `idα = (i, peer, party, comp role)`) nor the (B)
///     shape (`tau = recv3`, `(session_α, party_α) = (session_τ, party_τ)`) —
///     `rl_commute_initiate_deliver` / `rl_commute_simrecv_deliver_diff_party`.
/// Each lemma derives its precise label-distinctness from feasibility (or pure
/// label arithmetic).
/// (The `Observable IoSend` (A)/(B) shapes are discharged by
/// `subcase_A_infeasible` / `subcase_B_infeasible` above.)
#push-options "--z3rlimit 30 --split_queries no"
let ma_right_movable_ideal_role corrupt key_directory know0 =
  ma_label_in_same_partition_role_equiv ();
  let p = ma_ideal_system corrupt key_directory know0 in
  // ---------------------------------------------------------------------
  // The commute clause (conditioned on `inv s`).
  // ---------------------------------------------------------------------
  // `right_movable_mod_inv` only guards the commute obligation with `inv s`; it
  // does not itself assert that `inv` is inductive. Inductiveness (the init and
  // preservation hypotheses) is supplied separately to
  // `obs_bisim_up_to_partitions_implies_t_equivalence'`. This proof therefore
  // discharges only the commute body, assuming `inv s` at the pre-state.
  introduce forall (rho rho': system_label).
    ~(ma_partition_role.in_same_partition rho rho') ==>
    (forall (tau alpha: system_label)
        (s s_mid s': ideal_system_state).
      ma_partition_role.in_same_partition tau rho /\ is_internal tau /\
      ma_partition_role.in_same_partition alpha rho' /\
      ma_ideal_system_inv corrupt key_directory s /\
      p.transitions s tau s_mid /\ p.transitions s_mid alpha s' ==>
      (exists (s_mid': ideal_system_state).
        p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s'))
  with (
    introduce _ ==> _
    with _h. (
      introduce forall (tau alpha: system_label)
          (s s_mid s': ideal_system_state).
        ma_partition_role.in_same_partition tau rho /\ is_internal tau /\
        ma_partition_role.in_same_partition alpha rho' /\
        ma_ideal_system_inv corrupt key_directory s /\
        p.transitions s tau s_mid /\ p.transitions s_mid alpha s' ==>
        (exists (s_mid': ideal_system_state).
          p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s')
      with (
        introduce _ ==> _
        with _h2. (
          // Lift the role-distinctness of (rho, rho') to (tau, alpha).
          role_symm_lemma tau rho;
          role_trans_lemma rho tau alpha;
          role_trans_lemma rho alpha rho';
          // Now `~(ma_label_in_same_partition_role tau alpha)` holds. Dispatch
          // directly on the shape of `alpha`. Conditioned on
          // `ma_ideal_system_inv corrupt key_directory s` (in scope via `_h2`), the two
          // invariant-blocked deliver configurations (A)/(B) are genuinely
          // discharged below (they are infeasible: the goal holds vacuously
          // from `False`); every other role-distinct pair genuinely commutes.
          let TestedSystem.Internal idtau = tau in
          (
            match alpha with
            | TestedSystem.Observable IoSend idalpha -> (
              let s_p = TestedSystem.s2p_state s in
              let s_mid_p = TestedSystem.s2p_state s_mid in
              let s'_p = TestedSystem.s2p_state s' in
              let goal : prop =
                exists (s_mid': ideal_system_state).
                  p.transitions s alpha s_mid' /\ p.transitions s_mid' tau s' in
              // From `p.transitions s tau s_mid` (tau = Internal idtau):
              //   init_prop \/ recv_prop.
              let init_prop : prop =
                ma_ideal_initiate_protocol_transition s_p
                  idtau.session idtau.party idtau.peer idtau.role s_mid_p in
              let recv_prop : prop =
                (match idtau.role with
                 | Responder ->
                   ma_sim_receive_message3_protocol_transition s_p
                     idtau.session idtau.party idtau.peer s_mid_p
                 | Initiator -> False) in
              let handle_init (_: squash init_prop) : Lemma goal =
                if idalpha.session = idtau.session &&
                   idalpha.party = idtau.peer && idalpha.peer = idtau.party &&
                   idalpha.role = complementary_role idtau.role
                then
                  // Subcase (A): for honest parties, infeasible → goal vacuous.
                  // For corrupt parties, deliver is already enabled at s → commute.
                  if not (Set.mem idtau.party corrupt) && not (Set.mem idtau.peer corrupt)
                  then
                    subcase_A_infeasible corrupt key_directory know0 idtau idalpha s s_mid s'
                  else
                    FStar.Classical.exists_elim goal #term
                      #(fun output_t ->
                          ma_ideal_deliver_protocol_transition s_mid_p
                            idalpha.session idalpha.party idalpha.peer idalpha.role
                            output_t s'_p /\
                          s'.know == Seq.snoc s_mid.know output_t)
                      ()
                      (fun output_t ->
                        subcase_A_commute_corrupt corrupt key_directory know0
                          idtau idalpha output_t s s_mid s')
                else
                  // genuinely-commuting initiate-vs-deliver pair (NOT subcase A).
                  FStar.Classical.exists_elim goal #term
                    #(fun output_t ->
                        ma_ideal_deliver_protocol_transition s_mid_p
                          idalpha.session idalpha.party idalpha.peer idalpha.role
                          output_t s'_p /\
                        s'.know == Seq.snoc s_mid.know output_t)
                    ()
                    (fun output_t ->
                      rl_commute_initiate_deliver corrupt key_directory know0
                        idtau idalpha output_t s s_mid s')
              in
              let handle_recv (_: squash recv_prop) : Lemma goal =
                match idtau.role with
                | Initiator -> ()  // recv_prop == False: vacuous.
                | Responder ->
                  if idalpha.session = idtau.session && idalpha.party = idtau.party
                  then
                    // Same session and party: infeasible by I2 + H_resp (idα == idτ).
                    subcase_B_infeasible corrupt key_directory know0 idtau idalpha s s_mid s'
                  else
                    // genuinely-commuting recv3-vs-deliver pair, distinct
                    // (session, party).
                    FStar.Classical.exists_elim goal #priv_key
                      #(fun rk_t ->
                          ma_sim_receive_message3_enabled s_p
                            idtau.session idtau.party idtau.peer rk_t /\
                          s_mid_p == ma_sim_receive_message3_state s_p
                                       idtau.session idtau.party idtau.peer rk_t)
                      ()
                      (fun rk_t ->
                        FStar.Classical.exists_elim goal #term
                          #(fun output_t ->
                              ma_ideal_deliver_protocol_transition s_mid_p
                                idalpha.session idalpha.party idalpha.peer idalpha.role
                                output_t s'_p /\
                              s'.know == Seq.snoc s_mid.know output_t)
                          ()
                          (fun output_t ->
                            rl_commute_simrecv_deliver_diff_party corrupt key_directory know0
                              idtau idalpha rk_t output_t s s_mid s'))
              in
              FStar.Classical.or_elim #init_prop #recv_prop #(fun _ -> goal)
                handle_init handle_recv
            )
            | TestedSystem.Internal idalpha ->
              // Internal × Internal residual.
              _ideal_internal_internal_commute corrupt key_directory know0
                idtau idalpha s s_mid s'
            | TestedSystem.Observable NetSend idalpha ->
              // Internal × NetSend residual.
              _ideal_internal_netsend_commute corrupt key_directory know0
                idtau idalpha s s_mid s'
            | TestedSystem.Input d ->
              // Internal × Input residual: Input only inserts into the inputs
              // bag, so it commutes with any internal tau.
              _ideal_input_commute corrupt key_directory know0 tau d s s_mid s'
          )
        )
      )
    )
  )
#pop-options
