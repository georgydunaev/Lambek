(* Lambek calculus *)

Definition var:=nat.

Record Literal := BL{
 p : var;
 n : nat;
}.

Definition Word := list Literal.

Require Import Arith.
Require Import List.
Import ListNotations.

Definition neglit l := {|p:=(p l);n:=(n l)+1;|}.

Fixpoint neg (w: Word) : Word
:= match (w:Word) with
   | [] => []
   | he::ta => (neg ta)++[neglit he]
   end.

Fixpoint dneg (w: Word) : Word
:= match (w:Word) with
   | [] => []
   | he::ta => (neglit (neglit he))::(dneg ta)
   end.

Inductive Plus : Word -> Prop :=
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
Infix "\" := BSlash (left associativity, at level 65).
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
Notation " x '-->' y " := (@pair lFm Fm x y) (left associativity, at level 66).
Definition myapp : lFm -> lFm -> lFm := @app Fm.
Notation " x , y " := (myapp x y) (left associativity, at level 65).
Notation "x ---------------- y" := (x -> y) (only parsing, at level 65).
Notation "x ------------------------------------ y" := (x -> y) (only parsing, at level 65).
Reserved Notation "'L(\)' '⊢' x" (at level 65).
Notation " x ; y " := (x -> y) (only parsing, 
left associativity, at level 66).
Inductive LBS : (list Fm)*Fm -> Prop :=
| Ax : forall (A:Fm),

       L(\) ⊢ (A-->A)

| RI : forall (A B:Fm) (Π:list Fm),

       L(\) ⊢ (A,Π-->B)
       ----------------
       L(\) ⊢ (Π-->A\B)

| LI : forall (A B C:Fm) (Φ Γ Δ:list Fm),

       L(\) ⊢ (Φ-->A) ; L(\) ⊢ (Γ,B,Δ-->C)
       ------------------------------------
              L(\) ⊢ (Δ-->A\B)

where "'L(\)' '⊢' x" := (LBS x)
.




