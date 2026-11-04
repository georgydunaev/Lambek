(* Examples for slash and backslash type reduction rules *)

Require Import ../01.v.

Example slash_example : Plus ([BL 1 2]++[BL 0 1]++[BL 2 1]).
Proof.
  apply slash.
  apply pvi.
  apply mvi.
Qed.

Example backslash_example : Plus ([BL 2 1]++[BL 0 1]++[BL 1 2]).
Proof.
  apply backslash.
  apply pvi.
  apply mvi.
Qed.