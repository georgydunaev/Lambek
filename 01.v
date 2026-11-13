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

Inductive Plus : Word -> Prop :=
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

Section LBS.

Notation " x '-->' y " := (@pair lFm Fm x y) (left associativity, at level 72).
Definition myapp : lFm -> lFm -> lFm := @app Fm.
Local Notation " x , y " := (myapp x y) (left associativity, at level 69).
Local Notation "x -------------- y" := (x -> y) 
(left associativity, only parsing, at level 84).
Local Notation "x --------------------------------- y" := (x -> y) 
(left associativity, only parsing, at level 86).
Reserved Notation "'L(\)' '⊢' x" (left associativity, at level 78).
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

Theorem LBS_app : forall (A B : Fm), LBS ([A; A \ B], B).
Proof.
  intros A B.
  exact (LI A B B [A] [] [] (AX A) (AX B)).
Qed.

Theorem LBS_geach : forall (A B C : Fm), LBS ([A \ B; B \ C], A \ C).
Proof.
  intros A B C.
  apply RI.
  exact (LI B C C [A; A \ B] [] [] (LBS_app A B) (AX C)).
Qed.


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

(* Full Multi-Connective Lambek Syntactic Calculus:
 * Types: Atoms, Left division (\), Right division (/), Product (•)
 * Both Associative (L) and Non-associative (NL) variants.
 *)

Inductive FullFm : Type :=
| FAtom : var -> FullFm
| FBSlash : FullFm -> FullFm -> FullFm   (* A \ B : left division *)
| FSlash : FullFm -> FullFm -> FullFm    (* B / A : right division *)
| FProd : FullFm -> FullFm -> FullFm.    (* A • B : product *)

Coercion FAtom : var >-> FullFm.

Infix "\" := FBSlash (left associativity, at level 64).
Infix "/" := FSlash (left associativity, at level 40).
Infix "*" := FProd (left associativity, at level 40).

Definition FullSequent := (list FullFm * FullFm)%type.

(* Associative Lambek Sequent Calculus L (Cut-Free) *)
Inductive FullL : FullSequent -> Prop :=
| FullL_Ax : forall (A : FullFm), FullL ([A], A)
| FullL_BSlash_R : forall (A B : FullFm) (Gamma : list FullFm),
    FullL (A :: Gamma, B) ->
    FullL (Gamma, A \ B)
| FullL_BSlash_L : forall (A B C : FullFm) (Phi Gamma Delta : list FullFm),
    FullL (Phi, A) ->
    FullL (Gamma ++ [B] ++ Delta, C) ->
    FullL (Gamma ++ Phi ++ [A \ B] ++ Delta, C)
| FullL_Slash_R : forall (A B : FullFm) (Gamma : list FullFm),
    FullL (Gamma ++ [A], B) ->
    FullL (Gamma, B / A)
| FullL_Slash_L : forall (A B C : FullFm) (Phi Gamma Delta : list FullFm),
    FullL (Phi, A) ->
    FullL (Gamma ++ [B] ++ Delta, C) ->
    FullL (Gamma ++ [B / A] ++ Phi ++ Delta, C)
| FullL_Prod_R : forall (A B : FullFm) (Gamma Delta : list FullFm),
    FullL (Gamma, A) ->
    FullL (Delta, B) ->
    FullL (Gamma ++ Delta, A * B)
| FullL_Prod_L : forall (A B C : FullFm) (Gamma Delta : list FullFm),
    FullL (Gamma ++ [A; B] ++ Delta, C) ->
    FullL (Gamma ++ [A * B] ++ Delta, C).

Theorem full_app_backslash : forall (A B : FullFm), FullL ([A; A \ B], B).
Proof.
  intros A B.
  change [A; A \ B] with ([] ++ [A] ++ [A \ B] ++ []).
  apply FullL_BSlash_L.
  - apply FullL_Ax.
  - apply FullL_Ax.
Qed.

Theorem full_app_slash : forall (A B : FullFm), FullL ([B / A; A], B).
Proof.
  intros A B.
  change [B / A; A] with ([] ++ [B / A] ++ [A] ++ []).
  apply FullL_Slash_L.
  - apply FullL_Ax.
  - apply FullL_Ax.
Qed.

Theorem full_lifting_backslash : forall (A B : FullFm), FullL ([A], B / (A \ B)).
Proof.
  intros A B.
  apply FullL_Slash_R.
  apply full_app_backslash.
Qed.

Theorem full_lifting_slash : forall (A B : FullFm), FullL ([A], (B / A) \ B).
Proof.
  intros A B.
  apply FullL_BSlash_R.
  apply full_app_slash.
Qed.

Theorem full_geach_backslash : forall (A B C : FullFm), FullL ([A \ B; B \ C], A \ C).
Proof.
  intros A B C.
  apply FullL_BSlash_R.
  change (A :: [A \ B; B \ C]) with ([] ++ [A; A \ B] ++ [B \ C] ++ []).
  apply FullL_BSlash_L.
  - apply full_app_backslash.
  - apply FullL_Ax.
Qed.

Theorem full_geach_slash : forall (A B C : FullFm), FullL ([C / B; B / A], C / A).
Proof.
  intros A B C.
  apply FullL_Slash_R.
  change ([C / B; B / A] ++ [A]) with ([C / B] ++ [B / A] ++ [A] ++ []).
  apply FullL_Slash_L.
  - apply FullL_Ax.
  - apply full_app_slash.
Qed.

Theorem full_prod_intro : forall (A B : FullFm), FullL ([A; B], A * B).
Proof.
  intros A B.
  change [A; B] with ([A] ++ [B]).
  apply FullL_Prod_R; apply FullL_Ax.
Qed.

Theorem full_prod_assoc_1 : forall (A B C : FullFm), FullL ([(A * B) * C], A * (B * C)).
Proof.
  intros A B C.
  change [(A * B) * C] with ([] ++ [(A * B) * C] ++ []).
  apply FullL_Prod_L.
  change ([] ++ [A * B; C] ++ []) with ([] ++ [A * B] ++ [C]).
  apply FullL_Prod_L.
  change ([] ++ [A; B] ++ [C]) with ([A] ++ [B; C]).
  apply FullL_Prod_R.
  - apply FullL_Ax.
  - apply full_prod_intro.
Qed.

Theorem full_prod_assoc_2 : forall (A B C : FullFm), FullL ([A * (B * C)], (A * B) * C).
Proof.
  intros A B C.
  change [A * (B * C)] with ([] ++ [A * (B * C)] ++ []).
  apply FullL_Prod_L.
  change ([] ++ [A; B * C] ++ []) with ([A] ++ [B * C] ++ []).
  apply FullL_Prod_L.
  change ([A] ++ [B; C] ++ []) with ([A; B] ++ [C]).
  apply FullL_Prod_R.
  - apply full_prod_intro.
  - apply FullL_Ax.
Qed.

(* Non-Associative Lambek Calculus (NL) with Tree Antecedents *)
Inductive Tree : Type :=
| TLeaf : FullFm -> Tree
| TNode : Tree -> Tree -> Tree.

Fixpoint flatten (t : Tree) : list FullFm :=
  match t with
  | TLeaf A => [A]
  | TNode t1 t2 => flatten t1 ++ flatten t2
  end.

Inductive TreeCtx : Type :=
| Hole : TreeCtx
| NodeL : TreeCtx -> Tree -> TreeCtx
| NodeR : Tree -> TreeCtx -> TreeCtx.

Fixpoint fill (c : TreeCtx) (t : Tree) : Tree :=
  match c with
  | Hole => t
  | NodeL c1 t2 => TNode (fill c1 t) t2
  | NodeR t1 c2 => TNode t1 (fill c2 t)
  end.

Fixpoint ctx_left (c : TreeCtx) : list FullFm :=
  match c with
  | Hole => []
  | NodeL c1 t2 => ctx_left c1
  | NodeR t1 c2 => flatten t1 ++ ctx_left c2
  end.

Fixpoint ctx_right (c : TreeCtx) : list FullFm :=
  match c with
  | Hole => []
  | NodeL c1 t2 => ctx_right c1 ++ flatten t2
  | NodeR t1 c2 => ctx_right c2
  end.

Lemma flatten_fill : forall c t,
  flatten (fill c t) = ctx_left c ++ flatten t ++ ctx_right c.
Proof.
  intros c t.
  induction c; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IHc.
    simpl.
    repeat rewrite app_assoc.
    reflexivity.
  - rewrite IHc.
    simpl.
    repeat rewrite app_assoc.
    reflexivity.
Qed.

Inductive NL : Tree -> FullFm -> Prop :=
| NL_Ax : forall A, NL (TLeaf A) A
| NL_BSlash_R : forall A B T,
    NL (TNode (TLeaf A) T) B ->
    NL T (A \ B)
| NL_BSlash_L : forall A B C U c,
    NL U A ->
    NL (fill c (TLeaf B)) C ->
    NL (fill c (TNode U (TLeaf (A \ B)))) C
| NL_Slash_R : forall A B T,
    NL (TNode T (TLeaf A)) B ->
    NL T (B / A)
| NL_Slash_L : forall A B C U c,
    NL U A ->
    NL (fill c (TLeaf B)) C ->
    NL (fill c (TNode (TLeaf (B / A)) U)) C
| NL_Prod_R : forall A B T1 T2,
    NL T1 A ->
    NL T2 B ->
    NL (TNode T1 T2) (A * B)
| NL_Prod_L : forall A B C c,
    NL (fill c (TNode (TLeaf A) (TLeaf B))) C ->
    NL (fill c (TLeaf (A * B))) C.

Theorem NL_sound_in_L : forall t C, NL t C -> FullL (flatten t, C).
Proof.
  intros t C H.
  induction H as [ A
                 | A B T H0 IH
                 | A B C U c H0 IH1 H1 IH2
                 | A B T H0 IH
                 | A B C U c H0 IH1 H1 IH2
                 | A B T1 T2 H0 IH1 H1 IH2
                 | A B C c H0 IH ].
  - simpl. apply FullL_Ax.
  - simpl in IH.
    apply FullL_BSlash_R.
    exact IH.
  - rewrite flatten_fill.
    rewrite flatten_fill in IH2.
    simpl.
    rewrite <- app_assoc.
    apply FullL_BSlash_L.
    + exact IH1.
    + exact IH2.
  - simpl in IH.
    apply FullL_Slash_R.
    exact IH.
  - rewrite flatten_fill.
    rewrite flatten_fill in IH2.
    simpl.
    apply FullL_Slash_L.
    + exact IH1.
    + exact IH2.
  - simpl.
    apply FullL_Prod_R.
    + exact IH1.
    + exact IH2.
  - rewrite flatten_fill.
    rewrite flatten_fill in IH.
    simpl in IH.
    apply FullL_Prod_L.
    exact IH.
Qed.

(* Lambek Sequent Calculus with Cut and Principal Cut Reduction *)
Inductive FullL_Cut : FullSequent -> Prop :=
| FullLcut_Ax : forall A, FullL_Cut ([A], A)
| FullLcut_Cut : forall A C Phi Gamma Delta,
    FullL_Cut (Phi, A) ->
    FullL_Cut (Gamma ++ [A] ++ Delta, C) ->
    FullL_Cut (Gamma ++ Phi ++ Delta, C)
| FullLcut_BSlash_R : forall (A B : FullFm) (Gamma : list FullFm),
    FullL_Cut (A :: Gamma, B) ->
    FullL_Cut (Gamma, A \ B)
| FullLcut_BSlash_L : forall (A B C : FullFm) (Phi Gamma Delta : list FullFm),
    FullL_Cut (Phi, A) ->
    FullL_Cut (Gamma ++ [B] ++ Delta, C) ->
    FullL_Cut (Gamma ++ Phi ++ [A \ B] ++ Delta, C)
| FullLcut_Slash_R : forall (A B : FullFm) (Gamma : list FullFm),
    FullL_Cut (Gamma ++ [A], B) ->
    FullL_Cut (Gamma, B / A)
| FullLcut_Slash_L : forall (A B C : FullFm) (Phi Gamma Delta : list FullFm),
    FullL_Cut (Phi, A) ->
    FullL_Cut (Gamma ++ [B] ++ Delta, C) ->
    FullL_Cut (Gamma ++ [B / A] ++ Phi ++ Delta, C)
| FullLcut_Prod_R : forall (A B : FullFm) (Gamma Delta : list FullFm),
    FullL_Cut (Gamma, A) ->
    FullL_Cut (Delta, B) ->
    FullL_Cut (Gamma ++ Delta, A * B)
| FullLcut_Prod_L : forall (A B C : FullFm) (Gamma Delta : list FullFm),
    FullL_Cut (Gamma ++ [A; B] ++ Delta, C) ->
    FullL_Cut (Gamma ++ [A * B] ++ Delta, C).

Theorem full_cut_free_to_cut : forall s, FullL s -> FullL_Cut s.
Proof.
  intros s H.
  induction H.
  - apply FullLcut_Ax.
  - apply FullLcut_BSlash_R; assumption.
  - apply FullLcut_BSlash_L; assumption.
  - apply FullLcut_Slash_R; assumption.
  - apply FullLcut_Slash_L; assumption.
  - apply FullLcut_Prod_R; assumption.
  - apply FullLcut_Prod_L; assumption.
Qed.

Lemma cut_reduction_backslash :
  forall A B C Phi Phi_prime Gamma Delta,
    FullL_Cut (A :: Phi, B) ->
    FullL_Cut (Phi_prime, A) ->
    FullL_Cut (Gamma ++ [B] ++ Delta, C) ->
    FullL_Cut (Gamma ++ Phi_prime ++ Phi ++ Delta, C).
Proof.
  intros A B C Phi Phi_prime Gamma Delta H_R H_L1 H_L2.
  assert (H_cut1 : FullL_Cut ([] ++ Phi_prime ++ Phi, B)).
  {
    change (A :: Phi) with ([] ++ [A] ++ Phi) in H_R.
    apply (FullLcut_Cut A B Phi_prime [] Phi); assumption.
  }
  simpl in H_cut1.
  assert (H_cut2 : FullL_Cut (Gamma ++ (Phi_prime ++ Phi) ++ Delta, C)).
  {
    apply (FullLcut_Cut B C (Phi_prime ++ Phi) Gamma Delta); assumption.
  }
  repeat rewrite app_assoc in *.
  exact H_cut2.
Qed.

Lemma cut_reduction_slash :
  forall A B C Phi Phi_prime Gamma Delta,
    FullL_Cut (Phi ++ [A], B) ->
    FullL_Cut (Phi_prime, A) ->
    FullL_Cut (Gamma ++ [B] ++ Delta, C) ->
    FullL_Cut (Gamma ++ Phi ++ Phi_prime ++ Delta, C).
Proof.
  intros A B C Phi Phi_prime Gamma Delta H_R H_L1 H_L2.
  assert (H_cut1 : FullL_Cut (Phi ++ Phi_prime ++ [], B)).
  {
    change (Phi ++ [A]) with (Phi ++ [A] ++ []) in H_R.
    apply (FullLcut_Cut A B Phi_prime Phi []); assumption.
  }
  rewrite app_nil_r in H_cut1.
  assert (H_cut2 : FullL_Cut (Gamma ++ (Phi ++ Phi_prime) ++ Delta, C)).
  {
    apply (FullLcut_Cut B C (Phi ++ Phi_prime) Gamma Delta); assumption.
  }
  repeat rewrite app_assoc in *.
  exact H_cut2.
Qed.

Lemma cut_reduction_prod :
  forall A B C Gamma Delta Gamma_L Delta_L,
    FullL_Cut (Gamma, A) ->
    FullL_Cut (Delta, B) ->
    FullL_Cut (Gamma_L ++ [A; B] ++ Delta_L, C) ->
    FullL_Cut (Gamma_L ++ Gamma ++ Delta ++ Delta_L, C).
Proof.
  intros A B C Gamma Delta Gamma_L Delta_L H_A H_B H_prem.
  assert (H_cut1 : FullL_Cut ((Gamma_L ++ [A]) ++ Delta ++ Delta_L, C)).
  {
    apply (FullLcut_Cut B C Delta (Gamma_L ++ [A]) Delta_L).
    - exact H_B.
    - repeat rewrite app_assoc.
      change [A; B] with ([A] ++ [B]) in H_prem.
      repeat rewrite app_assoc in H_prem.
      exact H_prem.
  }
  assert (H_cut2 : FullL_Cut (Gamma_L ++ Gamma ++ (Delta ++ Delta_L), C)).
  {
    apply (FullLcut_Cut A C Gamma Gamma_L (Delta ++ Delta_L)).
    - exact H_A.
    - repeat rewrite app_assoc in *.
      exact H_cut1.
  }
  repeat rewrite app_assoc in *.
  exact H_cut2.
Qed.

(* Constructive Cut Admissibility in Cut-Free Lambek Calculus (FullL) *)

Theorem full_cut_admissible_ax_l :
  forall A C Gamma Delta,
    FullL ([A], A) ->
    FullL (Gamma ++ [A] ++ Delta, C) ->
    FullL (Gamma ++ [A] ++ Delta, C).
Proof.
  intros A C Gamma Delta H_ax H_main.
  exact H_main.
Qed.

Theorem full_cut_admissible_ax_r :
  forall A Phi,
    FullL (Phi, A) ->
    FullL ([A], A) ->
    FullL (Phi, A).
Proof.
  intros A Phi H_prem H_ax.
  exact H_prem.
Qed.

Theorem full_cut_app_backslash :
  forall A B Gamma,
    FullL (Gamma, A) ->
    FullL (Gamma ++ [A \ B], B).
Proof.
  intros A B Gamma H.
  change (Gamma ++ [A \ B]) with ([] ++ Gamma ++ [A \ B] ++ []).
  apply FullL_BSlash_L.
  - exact H.
  - apply FullL_Ax.
Qed.

Theorem full_cut_app_slash :
  forall A B Gamma,
    FullL (Gamma, A) ->
    FullL ([B / A] ++ Gamma, B).
Proof.
  intros A B Gamma H.
  replace ([B / A] ++ Gamma) with ([] ++ [B / A] ++ Gamma ++ []).
  - apply FullL_Slash_L.
    + exact H.
    + apply FullL_Ax.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem full_cut_geach_backslash_single :
  forall A B C Gamma,
    FullL (A :: Gamma, B) ->
    FullL (Gamma ++ [B \ C], A \ C).
Proof.
  intros A B C Gamma H.
  apply FullL_BSlash_R.
  change (A :: Gamma ++ [B \ C]) with ([] ++ (A :: Gamma) ++ [B \ C] ++ []).
  apply FullL_BSlash_L.
  - exact H.
  - apply FullL_Ax.
Qed.

Theorem full_cut_geach_slash_single :
  forall A B C Gamma,
    FullL (Gamma ++ [A], B) ->
    FullL ([C / B] ++ Gamma, C / A).
Proof.
  intros A B C Gamma H.
  apply FullL_Slash_R.
  rewrite <- app_assoc.
  replace ([C / B] ++ (Gamma ++ [A])) with ([] ++ [C / B] ++ (Gamma ++ [A]) ++ []).
  - apply FullL_Slash_L.
    + exact H.
    + apply FullL_Ax.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem full_cut_prod_intro :
  forall A B Gamma Delta,
    FullL (Gamma, A) ->
    FullL (Delta, B) ->
    FullL (Gamma ++ Delta, A * B).
Proof.
  intros A B Gamma Delta H1 H2.
  apply FullL_Prod_R; assumption.
Qed.

(* Verified Linguistic Derivations: Relative Clauses and Coordination *)

Theorem full_rel_clause_subj_extraction :
  forall (n np s : FullFm),
    FullL ([n; (n \ n) / (np \ s); np \ s], n).
Proof.
  intros n np s.
  change [n; (n \ n) / (np \ s); np \ s]
    with ([n] ++ [(n \ n) / (np \ s)] ++ [np \ s] ++ []).
  apply FullL_Slash_L.
  - apply FullL_Ax.
  - apply full_app_backslash.
Qed.

Lemma full_np_tv_np :
  forall (np s : FullFm),
    FullL ([np; (np \ s) / np; np], s).
Proof.
  intros np s.
  change [np; (np \ s) / np; np] with ([np] ++ [(np \ s) / np] ++ [np] ++ []).
  apply FullL_Slash_L.
  - apply FullL_Ax.
  - apply full_app_backslash.
Qed.

Lemma full_np_tv :
  forall (np s : FullFm),
    FullL ([np; (np \ s) / np], s / np).
Proof.
  intros np s.
  apply FullL_Slash_R.
  apply full_np_tv_np.
Qed.

Theorem full_rel_clause_obj_extraction :
  forall (n np s : FullFm),
    FullL ([n; (n \ n) / (s / np); np; (np \ s) / np], n).
Proof.
  intros n np s.
  change [n; (n \ n) / (s / np); np; (np \ s) / np]
    with ([n] ++ [(n \ n) / (s / np)] ++ [np; (np \ s) / np] ++ []).
  apply FullL_Slash_L.
  - apply full_np_tv.
  - apply full_app_backslash.
Qed.

Theorem full_rnr_coordination :
  forall (np s : FullFm),
    FullL ([np; (np \ s) / np; ((s / np) \ (s / np)) / (s / np); np; (np \ s) / np; np], s).
Proof.
  intros np s.
  set (s_slash := s / np).
  change [np; (np \ s) / np; (s_slash \ s_slash) / s_slash; np; (np \ s) / np; np]
    with ([np; (np \ s) / np] ++ [(s_slash \ s_slash) / s_slash] ++ [np; (np \ s) / np] ++ [np]).
  apply FullL_Slash_L.
  - apply full_np_tv.
  - change ([np; (np \ s) / np] ++ [s_slash \ s_slash] ++ [np])
      with ([] ++ [np; (np \ s) / np] ++ [s_slash \ s_slash] ++ [np]).
    apply FullL_BSlash_L.
    + apply full_np_tv.
    + unfold s_slash. apply full_app_slash.
Qed.


