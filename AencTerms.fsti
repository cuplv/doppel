(** Terms used for asymmetric encryption *)

module AencTerms



/// Type representing a session identifier

val session_id:eqtype

/// Identifiers for protocol participants. Used for NSL-style protocols where messages include sender and receiver identifiers.
val participant_id:eqtype

/// Nonces used in NSL-style protocols.
val nonce:eqtype

/// Type of data used in messages
val data:eqtype

val data_of_string : string -> data



/// Private keys
val priv_key : eqtype

/// Symbolic terms used in the protocol. Adversaries also work with these terms.
type term =
  | ParticipantId : participant_id -> term
  | SessionId : session_id -> term
  | Nonce : nonce -> term
  | Data : data -> term
  | PrivKey : priv_key -> term
  // Public keys are defined in terms of private keys so that each public key corresponds to exactly one private key.
  | PubKey : (priv: priv_key) -> term
  | Pair : term -> term -> term
  | Aenc : plaintext: term -> priv_key -> term

let rec size_of_term (t: term) : (r: nat{r > 0}) =
  match t with
  | ParticipantId _ -> 1
  | SessionId _ -> 1
  | Nonce _ -> 1
  | Data _ -> 1
  | PrivKey _ -> 1
  | PubKey _ -> 1
  | Pair l r -> size_of_term l + size_of_term r + 1
  | Aenc p k -> size_of_term p + 1
