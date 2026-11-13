(* Examples of Lambek Sequent Calculus Deductions in Coq *)

Require Import List.
Import ListNotations.
Require Import src.Lambek.

(* Variables representing linguistic types:
 * 0: np (noun phrase)
 * 1: s  (sentence)
 * 2: n  (common noun)
 *)

Definition np : Fm := Atom 0.
Definition s : Fm := Atom 1.
Definition n : Fm := Atom 2.

(* Transitive verb: (np \ s) / np *)
Definition tv : Fm := (np \ s) / np.

(* Intransitive verb: np \ s *)
Definition iv : Fm := np \ s.

(* Determiner: np / n *)
Definition det : Fm := np / n.

(* Example 1: Subject + Intransitive Verb -> Sentence (np, np \ s |- s) *)
Example ex_sentence_iv : L ([np; iv], s).
Proof.
  apply app_backslash.
Qed.

(* Example 2: Transitive Verb + Object -> Verb Phrase ((np \ s) / np, np |- np \ s) *)
Example ex_vp : L ([tv; np], iv).
Proof.
  apply app_slash.
Qed.

(* Example 3: Subject + Transitive Verb + Object -> Sentence (np, (np \ s) / np, np |- s) *)
Example ex_sentence_tv : L ([np; tv; np], s).
Proof.
  change [np; tv; np] with ([np] ++ [tv] ++ [np] ++ []).
  apply (L_Slash_L np (np \ s) s [np] [np] []).
  - apply L_Ax.
  - apply app_backslash.
Qed.

(* Example 4: Determiner + Noun -> Noun Phrase (np / n, n |- np) *)
Example ex_np_det : L ([det; n], np).
Proof.
  apply app_slash.
Qed.
