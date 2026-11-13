(* Examples for slash and backslash type reduction rules *)

Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import src.WordTypes.

Example slash_example : Plus ([BL 1 2] ++ [BL 0 1] ++ [BL 2 1]).
Proof.
  apply slash.
  - apply pvi. exists 1. auto.
  - apply mvi. exists 0. auto.
Qed.

Example backslash_example : Plus ([BL 2 1] ++ [BL 0 1] ++ [BL 1 2]).
Proof.
  apply backslash.
  - apply pvi. exists 1. auto.
  - apply mvi. exists 0. auto.
Qed.
