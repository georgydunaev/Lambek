(* Word and Literal definitions with Plus and Minus relations *)

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import PeanoNat.

Definition var := nat.

Record Literal := BL {
  p : var;
  n : nat;
}.

Definition Word := list Literal.

Definition neglit (l : Literal) : Literal :=
  {| p := p l; n := (n l) + 1 |}.

Fixpoint neg (w : Word) : Word :=
  match w with
  | [] => []
  | he :: ta => (neg ta) ++ [neglit he]
  end.

Fixpoint dneg (w : Word) : Word :=
  match w with
  | [] => []
  | he :: ta => (neglit (neglit he)) :: (dneg ta)
  end.

Inductive Plus : Word -> Prop :=
| slash : forall A B, (Plus A) -> (Minus B) -> (Plus (A ++ [BL 0 1] ++ B))
| backslash : forall A B, (Plus A) -> (Minus B) -> (Plus (B ++ [BL 0 1] ++ A))
| pvi : forall v ne, (Nat.Even ne) -> Plus ([BL v ne])
| pmp : forall A B, (Plus A) -> (Minus B) -> (Plus (A ++ (dneg B)))
with
Minus : Word -> Prop :=
| mvi : forall v ne, (Nat.Odd ne) -> Minus ([BL v ne])
| mmm : forall A B, (Minus A) -> (Minus B) -> (Minus (A ++ B))
| pmm : forall A B, (Plus A) -> (Minus B) -> (Minus (A ++ B)).
