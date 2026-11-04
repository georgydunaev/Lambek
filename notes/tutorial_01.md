# Tutorial: Using Lambek Calculus in Coq

## Introduction
This tutorial provides a step-by-step guide on how to use the Lambek calculus implementation in Coq. The implementation includes definitions for variables, literals, words, and operations for negation and double negation. It also includes inductive definitions for `Plus` and `Minus` and tactics for pattern matching.

## Step 1: Define Variables
Variables are defined as natural numbers in the implementation. For example:

```coq
Definition var := nat.
```

## Step 2: Define Literals
Literals are defined as a record with a variable and a natural number. For example:

```coq
Record Literal := BL {
  p : var;
  n : nat;
}.
```

## Step 3: Define Words
Words are defined as a list of literals. For example:

```coq
Definition Word := list Literal.
```

## Step 4: Define Negation
Negation is defined as incrementing the natural number in a literal. For example:

```coq
Definition neglit l := {|p:=(p l);n:=(n l)+1;|}.
```

## Step 5: Define Double Negation
Double negation is defined as negating a literal twice. For example:

```coq
Fixpoint dneg (w: Word) : Word
:= match (w:Word) with
   | [] => []
   | he::ta => (neglit (neglit he))::(dneg ta)
end.
```

## Step 6: Define Plus and Minus Relations
The `Plus` and `Minus` relations are defined inductively. For example:

```coq
Inductive Plus : Word -> Prop := 
| pvi : forall v ne, (Nat.Even ne) -> Plus ([BL v ne])
| pmp : forall A B, (Plus A) -> (Minus B) -> (Plus (A++(dneg B)))
with 
Minus : Word -> Prop := 
| mvi : forall v ne, (Nat.Odd ne) -> Minus ([BL v ne])
```

## Conclusion
This tutorial has provided a step-by-step guide on how to use the Lambek calculus implementation in Coq. You can now create your own examples and proofs using the definitions and relations provided in the implementation.
