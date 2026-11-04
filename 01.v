(* Lambek calculus *)
(*
 * This file contains the Coq implementation of Lambek calculus.
 * It defines variables, literals, words, and operations for negation and double negation.
 * It also includes inductive definitions for Plus and Minus and tactics for pattern matching.
 *
 * Author: mistral/mistral-medium-latest (Capability Tier 1)
 * Date: 2023-10-28
 *)

Definition var := nat.
(* Defines a variable as a natural number. *)

Record Literal := BL {
(* Defines a literal with a variable and a natural number. *)
 p : var;
 n : nat;
}.

Definition Word := list Literal.
(* Defines a word as a list of literals. *)

Require Import Arith.
Require Import List.
Import ListNotations.

Definition neglit l := {|p:=(p l);n:=(n l)+1;|}.
(* Negates a literal by incrementing the natural number. *)

Fixpoint neg (w: Word) : Word
(* Negates a word by negating each literal and reversing the order. *)
:= match (w:Word) with
   | [] => []
   | he::ta => (neg ta)++[neglit he]
   end.

Fixpoint dneg (w: Word) : Word
(* Double negates a word by negating each literal twice. *)
:= match (w:Word) with
   | [] => []
   | he::ta => (neglit (neglit he))::(dneg ta)
   end.

Require Import src.plus.
Require Import src.minus.
  | slash : forall A B, (Plus A) -> (Minus B) -> (Plus (A++[BL 0 1]++B))
  | backslash : forall A B, (Plus A) -> (Minus B) -> (Plus (B++[BL 0 1]++A))
(* Defines the Plus relation for words. *)
 | pvi : forall v ne, (Nat.Even ne) -> Plus ([BL v ne])
 | pmp : forall A B, (Plus A) -> (Minus B) -> (Plus (A++(dneg B)))
 with 
 Minus : Word -> Prop :=
 | mvi : forall v ne, (Nat.Odd ne) -> Minus ([BL v ne])
 | mmm : forall A B, (Minus A) -> (Minus B) -> (Minus (A++B))
 | pmm : forall A B, (Plus A) -> (Minus B) -> (Minus (A++B))
.

Require Import PeanoNat.

Ltac lpat n := try (apply pvi; exists (n/2); auto with arith).

Ltac lmat n := try (apply mvi; exists (n/2); auto with arith).

Ltac lato :=
  match goal with
    | [ |- Plus [ ?y ] ] => lpat (n y)
    | [ |- Minus [ ?y ] ] => lmat (n y)
  end.

Example ex1 : Minus [(BL 0 2);(BL 0 4);(BL 0 3);(BL 0 1)].
Proof.
apply (pmm [(BL 0 2);(BL 0 4);(BL 0 3)] [(BL 0 1)]).
- apply (pmp [(BL 0 2)] [(BL 0 2);(BL 0 1)]).
  + lato.
  + apply (pmm [{| p := 0; n := 2 |}] [{| p := 0; n := 1 |}]); lato.
- lato.
Defined.

Inductive Fm :=
| Atom :> var -> Fm
| BSlash : Fm -> Fm -> Fm
.

Definition vin (x:nat) : var := x.
Coercion vin : nat >-> var.
Infix "\" := BSlash (left associativity, at level 64).
Check (0 \ 1).
Check (0 \ 1 \ 2).

Fixpoint translation (x : Fm) :=
 match x return Word with
 | Atom p => [{|p:=p;n:=1;|}]
 | ( a \ b ) => (neg (translation a))++(translation b)
 end.

Notation "'γ'" := translation.
Eval compute in γ (4 \ 3 \ 2 \ 1).  (* [2;4;3;1] Ok! *)
Eval compute in γ (7 \ 6 \ 5 \ 4 \ 3 \ 2 \ 1).

(* "L(\)" calculus *)
Definition lFm := (list Fm).
Definition etl (x:Fm) : lFm := [x].
Coercion etl : Fm >-> lFm.
Notation " x '-->' y " := (@pair lFm Fm x y) (left associativity, at level 72).
Definition myapp : lFm -> lFm -> lFm := @app Fm.
Notation " x , y " := (myapp x y) (left associativity, at level 69).
Notation "x -------------- y" := (x -> y) 
(left associativity, only parsing, at level 84).
Notation "x --------------------------------- y" := (x -> y) 
(left associativity, only parsing, at level 86).
Reserved Notation "'L(\)' '⊢' x" (left associativity, at level 78).

Section LBS.
Local Notation " x ; y " := (x -> y) (only parsing,
 left associativity, at level 87).

Inductive LBS : (list Fm)*Fm -> Prop :=
| AX : forall (A:Fm),

       L(\) ⊢ A-->A

| RI : forall (A B:Fm) (Π:list Fm),

       L(\) ⊢ A,Π-->B
       --------------
       L(\) ⊢ Π-->A\B

| LI : forall (A B C:Fm) (Φ Γ Δ:list Fm),

       L(\) ⊢ Φ-->A  ;  L(\) ⊢ Γ,B,Δ-->C
       ---------------------------------
             L(\) ⊢ Γ,Φ,A\B,Δ-->C

where "'L(\)' '⊢' x" := (LBS x)
.
Print LBS.
End LBS.

Inductive S : Word -> Prop :=
| R0 : forall p, S [(BL p 1);(BL p 2)]
| R1 : forall (𝔸 𝔹 :Word) (p:Literal), 
   (Minus 𝔸) -> (Minus 𝔹) ->
   S (𝔸 ++ 𝔹 ++ dneg([p])) -> 
   S (𝔹 ++ dneg(p :: 𝔸) )
| R2 : forall (𝔸 𝔹 ℂ 𝔻 :Word) (p:Literal), 
(Minus 𝔸) -> (Plus 𝔹) ->
(Minus ℂ) -> (Minus 𝔻) ->
   S (𝔸 ++ 𝔹 ) ->
   S (ℂ ++ 𝔻 ++ dneg([p])) -> 
   S (ℂ ++ 𝔸 ++ 𝔹 ++ 𝔻++ dneg(p::𝔸) )
.

(* 𝔸 = U+1D538 *)
(* ℂ = U+2102*)

