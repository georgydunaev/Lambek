(* Example: Demonstrating the use of Lambek calculus in Coq *)

Require Import List.
Import ListNotations.
Require Import PeanoNat.
Require Import src.WordTypes.

(* Define a word with a single literal *) 
Definition example_word := [BL 0 2].

(* Prove that the word is in the Plus relation *) 
Lemma example_plus : Plus example_word.
Proof.
  apply pvi.
  exists 1.
  auto.
Qed.

(* Define a word with a single literal *) 
Definition example_word2 := [BL 0 3].

(* Prove that the word is in the Minus relation *) 
Lemma example_minus : Minus example_word2.
Proof.
  apply mvi.
  exists 1.
  auto.
Qed.
