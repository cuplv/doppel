module MA.Types

open AencTerms

open SymbolicTypes

module Set = FStar.Set
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module List = FStar.List.Tot.Base
module ListProperties = FStar.List.Tot.Properties

/// The set of nonces syntactically present in a term. Encryption keys are not
/// terms in the asymmetric encoding, so only encrypted plaintexts are scanned.
let rec ma_term_nonces (t: term) : Set.set nonce =
  match t with
  | Nonce n -> Set.singleton n
  | Pair left right -> Set.union (ma_term_nonces left) (ma_term_nonces right)
  | Aenc plaintext _ -> ma_term_nonces plaintext
  | _ -> Set.empty

let rec ma_term_list_nonces (ts: list term) : Set.set nonce =
  match ts with
  | [] -> Set.empty
  | t :: rest -> Set.union (ma_term_nonces t) (ma_term_list_nonces rest)

/// Initial protocol states mark every nonce already present in the adversary's
/// initial knowledge as used. Later protocol steps monotonically add freshly
/// generated nonces to this set.
let ma_knowledge_nonces (know: knowledge term) : Set.set nonce =
  ma_term_list_nonces (Seq.seq_to_list know)

/// `aenc_subterm c t` holds when term `c` occurs inside `t`, reachable by
/// descending into `Pair` components and `Aenc` plaintexts — the structural
/// positions an adversary can reach by projection and decryption.  Reflexive.
let rec aenc_subterm (c: term) (t: term) : bool =
  c = t ||
  (match t with
   | Pair l r -> aenc_subterm c l || aenc_subterm c r
   | Aenc p _ -> aenc_subterm c p
   | _ -> false)

/// A term containing no `Aenc` constructor anywhere.
let rec aenc_free (t: term) : bool =
  match t with
  | Pair l r -> aenc_free l && aenc_free r
  | Aenc _ _ -> false
  | _ -> true

/// A "shallow" term: either `Aenc`-free, or an `Aenc` whose plaintext is
/// `Aenc`-free (no `Aenc` nested inside another `Aenc`'s plaintext).  Every
/// protocol-emitted knowledge term satisfies this (single-layer ciphertexts).
let shallow_aenc (t: term) : bool =
  match t with
  | Aenc p _ -> aenc_free p
  | _ -> aenc_free t

/// The nonces of a sub-term are a subset of the nonces of the enclosing term.
let rec aenc_subterm_nonces_subset (c t: term)
    : Lemma (requires aenc_subterm c t)
            (ensures Set.subset (ma_term_nonces c) (ma_term_nonces t))
            (decreases t) =
  if c = t then ()
  else match t with
    | Pair l r ->
      (if aenc_subterm c l then aenc_subterm_nonces_subset c l
       else aenc_subterm_nonces_subset c r);
      let helper (x: nonce)
          : Lemma (Set.mem x (ma_term_nonces c) ==> Set.mem x (ma_term_nonces t)) =
        Set.mem_union x (ma_term_nonces l) (ma_term_nonces r)
      in
      FStar.Classical.forall_intro helper
    | Aenc p _ -> aenc_subterm_nonces_subset c p
    | _ -> ()

/// An `Aenc`-free term has no `Aenc` sub-term.
let rec aenc_free_no_aenc_subterm (c t: term)
    : Lemma (requires aenc_free t /\ aenc_subterm c t /\ Aenc? c)
            (ensures False)
            (decreases t) =
  if c = t then ()
  else match t with
    | Pair l r ->
      if aenc_subterm c l then aenc_free_no_aenc_subterm c l
      else aenc_free_no_aenc_subterm c r
    | _ -> ()

/// In a shallow term, the only `Aenc` sub-term is the term itself.
let aenc_subterm_shallow_eq (c t: term)
    : Lemma (requires shallow_aenc t /\ aenc_subterm c t /\ Aenc? c)
            (ensures c == t) =
  if c = t then ()
  else match t with
    | Aenc p _ -> aenc_free_no_aenc_subterm c p
    | Pair l r ->
      if aenc_subterm c l then aenc_free_no_aenc_subterm c l
      else aenc_free_no_aenc_subterm c r
    | _ -> ()

let ma_set_union_empty_left (#a:eqtype) (s: Set.set a)
    : Lemma (ensures Set.equal (Set.union Set.empty s) s) =
  let helper (x: a)
      : Lemma (ensures (Set.mem x (Set.union Set.empty s) = Set.mem x s)) =
    Set.mem_union x Set.empty s;
    Set.mem_empty x
  in
  FStar.Classical.forall_intro helper;
  Set.lemma_equal_intro (Set.union Set.empty s) s

let ma_set_union_assoc (#a:eqtype) (s1 s2 s3: Set.set a)
    : Lemma
      (ensures Set.equal
        (Set.union s1 (Set.union s2 s3))
        (Set.union (Set.union s1 s2) s3)) =
  let helper (x: a)
      : Lemma
        (ensures
          Set.mem x (Set.union s1 (Set.union s2 s3)) =
          Set.mem x (Set.union (Set.union s1 s2) s3)) =
    Set.mem_union x s1 (Set.union s2 s3);
    Set.mem_union x s2 s3;
    Set.mem_union x (Set.union s1 s2) s3;
    Set.mem_union x s1 s2
  in
  FStar.Classical.forall_intro helper;
  Set.lemma_equal_intro
    (Set.union s1 (Set.union s2 s3))
    (Set.union (Set.union s1 s2) s3)

let rec ma_term_list_nonces_snoc (ts: list term) (t: term)
    : Lemma
      (ensures Set.equal
        (ma_term_list_nonces (List.snoc (ts, t)))
        (Set.union (ma_term_list_nonces ts) (ma_term_nonces t))) =
  match ts with
  | [] -> ma_set_union_empty_left (ma_term_nonces t)
  | hd :: tl ->
    ma_term_list_nonces_snoc tl t;
    ma_set_union_assoc (ma_term_nonces hd) (ma_term_list_nonces tl) (ma_term_nonces t)

let rec ma_seq_of_list_snoc (ts: list term) (t: term)
    : Lemma
      (ensures
        Seq.seq_of_list (List.snoc (ts, t)) ==
        Seq.snoc (Seq.seq_of_list ts) t) =
  match ts with
  | [] ->
    let empty_terms : list term = [] in
    Seq.lemma_seq_of_list_cons t empty_terms;
    Seq.lemma_empty (Seq.seq_of_list empty_terms);
    Seq.append_empty_r (Seq.create #term 1 t);
    Seq.append_empty_l (Seq.create #term 1 t)
  | hd :: tl ->
    ma_seq_of_list_snoc tl t;
    Seq.lemma_seq_of_list_cons hd (List.snoc (tl, t));
    Seq.lemma_seq_of_list_cons hd tl;
    Seq.append_assoc (Seq.create 1 hd) (Seq.seq_of_list tl) (Seq.create 1 t);
    Seq.lemma_cons_snoc hd (Seq.seq_of_list tl) t

let ma_seq_to_list_snoc (know: knowledge term) (t: term)
    : Lemma
      (ensures Seq.seq_to_list (Seq.snoc know t) ==
        List.snoc (Seq.seq_to_list know, t)) =
  let lhs = Seq.seq_to_list (Seq.snoc know t) in
  let rhs = List.snoc (Seq.seq_to_list know, t) in
  Seq.lemma_seq_of_seq_to_list (Seq.snoc know t);
  Seq.lemma_seq_of_seq_to_list know;
  ma_seq_of_list_snoc (Seq.seq_to_list know) t;
  assert (Seq.seq_of_list lhs == Seq.snoc know t);
  assert (Seq.seq_of_list rhs == Seq.snoc know t);
  Seq.lemma_seq_to_seq_of_list lhs;
  Seq.lemma_seq_to_seq_of_list rhs

let ma_knowledge_nonces_snoc (know: knowledge term) (t: term)
    : Lemma
      (ensures Set.equal
        (ma_knowledge_nonces (Seq.snoc know t))
        (Set.union (ma_knowledge_nonces know) (ma_term_nonces t))) =
  ma_seq_to_list_snoc know t;
  ma_term_list_nonces_snoc (Seq.seq_to_list know) t

let ma_knowledge_nonces_snoc_preserves_subset
      (know: knowledge term)
      (t: term)
      (used_nonces: Set.set nonce)
    : Lemma
      (requires
        Set.subset (ma_knowledge_nonces know) used_nonces /\
        Set.subset (ma_term_nonces t) used_nonces)
      (ensures
        Set.subset (ma_knowledge_nonces (Seq.snoc know t)) used_nonces) =
  ma_knowledge_nonces_snoc know t;
  Set.lemma_equal_elim (ma_knowledge_nonces (Seq.snoc know t))
    (Set.union (ma_knowledge_nonces know) (ma_term_nonces t));
  Set.subset_mem (ma_knowledge_nonces know) used_nonces;
  Set.subset_mem (ma_term_nonces t) used_nonces;
  let helper (n: nonce)
      : Lemma
        (ensures
          Set.mem n (ma_knowledge_nonces (Seq.snoc know t)) ==>
          Set.mem n used_nonces) =
    Set.mem_union n (ma_knowledge_nonces know) (ma_term_nonces t)
  in
  FStar.Classical.forall_intro helper;
  Set.mem_subset (ma_knowledge_nonces (Seq.snoc know t)) used_nonces

let ma_knowledge_nonces_snoc_empty_preserves_subset
      (know: knowledge term)
      (t: term)
      (used_nonces: Set.set nonce)
    : Lemma
      (requires
        Set.subset (ma_knowledge_nonces know) used_nonces /\
        Set.equal (ma_term_nonces t) Set.empty)
      (ensures
        Set.subset (ma_knowledge_nonces (Seq.snoc know t)) used_nonces) =
  ma_knowledge_nonces_snoc know t;
  Set.lemma_equal_elim (ma_knowledge_nonces (Seq.snoc know t))
    (Set.union (ma_knowledge_nonces know) (ma_term_nonces t));
  Set.lemma_equal_elim (ma_term_nonces t) Set.empty;
  Set.subset_mem (ma_knowledge_nonces know) used_nonces;
  let helper (n: nonce)
      : Lemma
        (ensures
          Set.mem n (ma_knowledge_nonces (Seq.snoc know t)) ==>
          Set.mem n used_nonces) =
    Set.mem_union n (ma_knowledge_nonces know) (ma_term_nonces t);
    Set.mem_empty n
  in
  FStar.Classical.forall_intro helper;
  Set.mem_subset (ma_knowledge_nonces (Seq.snoc know t)) used_nonces

let rec ma_term_list_nonces_index_subset
      (ts: list term)
      (i: nat {i < List.length ts})
      (t: term)
    : Lemma
      (requires List.index ts i == t)
      (ensures Set.subset (ma_term_nonces t) (ma_term_list_nonces ts)) =
  match ts with
  | [] -> ()
  | hd :: tl ->
    if i = 0 then
      (assert (t == hd);
       let helper (n: nonce)
           : Lemma
             (ensures
               Set.mem n (ma_term_nonces t) ==>
               Set.mem n (ma_term_list_nonces ts)) =
         Set.mem_union n (ma_term_nonces hd) (ma_term_list_nonces tl)
       in
       FStar.Classical.forall_intro helper;
       Set.mem_subset (ma_term_nonces t) (ma_term_list_nonces ts))
    else
      (ma_term_list_nonces_index_subset tl (i - 1) t;
       Set.subset_mem (ma_term_nonces t) (ma_term_list_nonces tl);
       let helper (n: nonce)
           : Lemma
             (ensures
               Set.mem n (ma_term_nonces t) ==>
               Set.mem n (ma_term_list_nonces ts)) =
         Set.mem_union n (ma_term_nonces hd) (ma_term_list_nonces tl)
       in
       FStar.Classical.forall_intro helper;
       Set.mem_subset (ma_term_nonces t) (ma_term_list_nonces ts))

let ma_knowledge_nonces_index
      (know: knowledge term)
      (i: nat)
      (t: term)
    : Lemma
      (requires i < Seq.length know /\
        Seq.index know i == t)
      (ensures Set.subset (ma_term_nonces t) (ma_knowledge_nonces know)) =
  SeqProps.lemma_index_is_nth know i;
  ma_term_list_nonces_index_subset (Seq.seq_to_list know) i t

(** Observable effects of the message authentication protocol. *)
type ma_effect =
  | IoSend : ma_effect
  | NetSend : ma_effect

/// Role played by an authenticating party in a session.
type role =
  | Initiator
  | Responder

let complementary_role (r: role) : role =
  match r with
  | Initiator -> Responder
  | Responder -> Initiator

/// `complementary_role` is an involution.
let complementary_role_involutive (r: role)
    : Lemma (complementary_role (complementary_role r) == r) = ()

/// Identifier carried by Protocol/TestedSystem labels. Each transition carries
/// its (session, party, peer, role) in the label, so a label fully identifies
/// which transition variant fires. The `ma_label_in_same_partition_role`
/// relation uses these fields to define the partition.
type ma_label_id = {
  session: session_id;
  party: participant_id;
  peer: participant_id;
  role: role
}

/// Tag a protocol input with its source so IO inputs and network inputs are
/// distinct in the shared input bag.
let ma_io_input_term (input_t: term) : term =
  Pair (Data (data_of_string "IoInput")) input_t

let ma_net_input_term (input_t: term) : term =
  Pair (Data (data_of_string "NetInput")) input_t

/// Untagged MA environment authentication-request payload.
let ma_auth_input_payload_term
      (session: session_id)
      (party peer: participant_id)
      (r: role)
    : term =
  match r with
  | Initiator ->
    Pair (SessionId session) (Pair (ParticipantId party) (ParticipantId peer))
  | Responder ->
    Pair (Pair (SessionId session) (ParticipantId party)) (ParticipantId peer)

/// Common MA environment input encoding. Authentication requests are always
/// IO inputs, so this constructor includes the IO tag directly.
let ma_auth_input_term
      (session: session_id)
      (party peer: participant_id)
      (r: role)
    : term =
  ma_io_input_term (ma_auth_input_payload_term session party peer r)

/// Common MA output encoding that `party` authenticated `peer` in `session`.
let ma_authenticated_term
      (session: session_id)
      (party peer: participant_id)
    : term =
  Pair
    (SessionId session)
    (Pair
      (ParticipantId party)
      (ParticipantId peer))
