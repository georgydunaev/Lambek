(* Example 1: Demonstrating the use of Lambek calculus in Coq *)

(* Author: openrouter/nvidia/nemotron-3.5-lightning:free (Capability Tier 1) *)
(* Date: 2023-10-28 *)

Require Import 01.

(* Define a simple word with one literal *)
Definition simple_word := [BL 0 2].

(* Negate the simple word *)
Definition negated_word := neg simple_word.

(* Double negate the simple word *)
Definition dnegated_word := dneg simple_word.

(* Verify the Plus relation for the simple word *)
Lemma simple_word_plus : Plus simple_word.
Proof.
  apply pvi.
  exact (Nat.Even 2).
Qed.

(* Verify the Minus relation for the negated word *)
Lemma negated_word_minus : Minus negated_word.
Proof.
  apply mvi.
  exact (Nat.Odd 3).
Qed.
