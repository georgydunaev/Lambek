(* Example: Demonstrating the use of Lambek calculus in Coq *)

(* Author: mistral/codestral-latest (Capability Tier 1) *)
(* Date: 2023-10-28 *)

Require Import ../01.v.

(* Define a word with a single literal *) 
Definition example_word := [BL 0 2].

(* Prove that the word is in the Plus relation *) 
Lemma example_plus : Plus example_word.
Proof.
  apply pvi.
  exact (Nat.Even 2).
Qed.

(* Define a word with a single literal *) 
Definition example_word2 := [BL 0 3].

(* Prove that the word is in the Minus relation *) 
Lemma example_minus : Minus example_word2.
Proof.
  apply mvi.
  exact (Nat.Odd 3).
Qed.
