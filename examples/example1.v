(* Example 1: Demonstrating the use of Lambek calculus in Coq *)

Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import src.WordTypes.

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
  exists 1.
  auto.
Qed.

(* Verify the Minus relation for the negated word *)
Lemma negated_word_minus : Minus negated_word.
Proof.
  apply mvi.
  exists 1.
  auto.
Qed.
