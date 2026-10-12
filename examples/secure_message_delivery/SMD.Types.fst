module SMD.Types



(** Observable effects of the secure message delivery protocol. *)

type smd_effect =
  | IoSend : smd_effect
  | NetSend : smd_effect
