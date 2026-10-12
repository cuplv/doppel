module AencTerms



/// Type representing a session identifier
let session_id = nat

/// Identifiers for protocol participants.
let participant_id = string

/// Nonces used in NSL-style protocols.
let nonce = nat

/// Type of data used in messages
let data = string

let data_of_string (s: string) : data = s

/// Asymmetric private keys
let priv_key = string
