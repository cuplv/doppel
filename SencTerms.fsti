(** Terms used for symmetric encryption *)

module SencTerms



/// Type representing a session identifier

val session_id:eqtype



/// Type of data used in messages

val data:eqtype



/// Symmetric keys

val key:eqtype



/// Symbolic terms used in the protocol. Adversaries also work with these terms.

type term =
  | Bool : bool -> term
  | SessionId : session_id -> term
  | Data : data -> term
  | Key : key -> term
  | Pair : term -> term -> term
  | Senc : plaintext: term -> key -> term
