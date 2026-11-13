(* Pentus's Theorem, Gaifman-Kazimierz Translation, and AB Reductions in Lambek Calculus *)
(* Formalization of Context-Free Grammars and Categorial Proof Systems *)

Require Import List.
Import ListNotations.
Require Import src.Lambek.

(* Section 1: Context-Free Grammars in Chomsky Normal Form (CNF) *)

Definition nonterm := nat.
Definition terminal := nat.

Inductive CfgRule : Type :=
| Cfg_Bin : nonterm -> nonterm -> nonterm -> CfgRule  (* A -> B C *)
| Cfg_Term : nonterm -> terminal -> CfgRule.          (* A -> a *)

(* Derivations in Chomsky-Bar-Hillel Grammar Systems *)
Inductive cfg_derives (rules : list CfgRule) : list terminal -> nonterm -> Prop :=
| cd_term : forall (A : nonterm) (a : terminal),
    In (Cfg_Term A a) rules ->
    cfg_derives rules [a] A
| cd_bin : forall (A B C : nonterm) (w1 w2 : list terminal),
    In (Cfg_Bin A B C) rules ->
    cfg_derives rules w1 B ->
    cfg_derives rules w2 C ->
    cfg_derives rules (w1 ++ w2) A.

Record CFG : Type := mkCFG {
  cfg_rules : list CfgRule;
  cfg_start : nonterm
}.

Definition cfg_language (g : CFG) (w : list terminal) : Prop :=
  cfg_derives (cfg_rules g) w (cfg_start g).

(* Section 2: Ajdukiewicz-Bar-Hillel (AB) Derivation Trees *)

Inductive AB_Tree : Type :=
| AB_Leaf : Fm -> AB_Tree
| AB_App_R : AB_Tree -> AB_Tree -> AB_Tree   (* (B/A) A -> B *)
| AB_App_L : AB_Tree -> AB_Tree -> AB_Tree.  (* A (A\B) -> B *)

Fixpoint ab_yield (t : AB_Tree) : list Fm :=
  match t with
  | AB_Leaf A => [A]
  | AB_App_R t1 t2 => ab_yield t1 ++ ab_yield t2
  | AB_App_L t1 t2 => ab_yield t1 ++ ab_yield t2
  end.

Inductive ab_derives : AB_Tree -> Fm -> Prop :=
| abd_leaf : forall (A : Fm), ab_derives (AB_Leaf A) A
| abd_app_r : forall (t1 t2 : AB_Tree) (A B : Fm),
    ab_derives t1 (B / A) ->
    ab_derives t2 A ->
    ab_derives (AB_App_R t1 t2) B
| abd_app_l : forall (t1 t2 : AB_Tree) (A B : Fm),
    ab_derives t1 A ->
    ab_derives t2 (A \ B) ->
    ab_derives (AB_App_L t1 t2) B.

(* Relational formulation of AB reduction on sequent antecedents *)
Inductive AB_reduce : list Fm -> Fm -> Prop :=
| AB_Ax : forall (A : Fm), AB_reduce [A] A
| AB_Slash : forall (A B : Fm) (Gamma Delta : list Fm),
    AB_reduce Gamma (B / A) ->
    AB_reduce Delta A ->
    AB_reduce (Gamma ++ Delta) B
| AB_BSlash : forall (A B : Fm) (Gamma Delta : list Fm),
    AB_reduce Gamma A ->
    AB_reduce Delta (A \ B) ->
    AB_reduce (Gamma ++ Delta) B.

(* Section 3: Soundness of AB Reductions in Cut-Free Lambek Calculus L *)

Theorem ab_step_slash_sound : forall (A B : Fm), L ([B / A; A], B).
Proof.
  intros A B.
  apply app_slash.
Qed.

Theorem ab_step_backslash_sound : forall (A B : Fm), L ([A; A \ B], B).
Proof.
  intros A B.
  apply app_backslash.
Qed.

Theorem ab_lexical_slash_sound :
  forall (A B : Fm) (Delta : list Fm),
    L (Delta, A) ->
    L ([B / A] ++ Delta, B).
Proof.
  intros A B Delta H.
  apply cut_app_slash.
  exact H.
Qed.

Theorem ab_lexical_backslash_sound :
  forall (A B : Fm) (Gamma : list Fm),
    L (Gamma, A) ->
    L (Gamma ++ [A \ B], B).
Proof.
  intros A B Gamma H.
  apply cut_app_backslash.
  exact H.
Qed.

(* Soundness of Full AB Derivation Trees in Lambek Calculus with Cut *)

Theorem ab_sound_in_L_cut : forall (t : AB_Tree) (C : Fm),
  ab_derives t C -> L_Cut (ab_yield t, C).
Proof.
  intros t C H.
  induction H as [ A
                 | t1 t2 A B H1 IH1 H2 IH2
                 | t1 t2 A B H1 IH1 H2 IH2 ].
  - simpl.
    apply Lcut_Ax.
  - simpl.
    assert (H_base : L_Cut ([B / A; A], B)).
    {
      apply cut_free_to_cut.
      apply app_slash.
    }
    assert (H_cut1 : L_Cut ([B / A] ++ ab_yield t2, B)).
    {
      change [B / A; A] with ([B / A] ++ [A] ++ []) in H_base.
      assert (H_step : L_Cut ([B / A] ++ ab_yield t2 ++ [], B)).
      {
        apply (Lcut_Cut A B (ab_yield t2) [B / A] []).
        - exact IH2.
        - exact H_base.
      }
      rewrite app_nil_r in H_step.
      exact H_step.
    }
    change (ab_yield t1 ++ ab_yield t2) with ([] ++ ab_yield t1 ++ ab_yield t2).
    change ([B / A] ++ ab_yield t2) with ([] ++ [B / A] ++ ab_yield t2) in H_cut1.
    apply (Lcut_Cut (B / A) B (ab_yield t1) [] (ab_yield t2)).
    + exact IH1.
    + exact H_cut1.
  - simpl.
    assert (H_base : L_Cut ([A; A \ B], B)).
    {
      apply cut_free_to_cut.
      apply app_backslash.
    }
    assert (H_cut1 : L_Cut (ab_yield t1 ++ [A \ B], B)).
    {
      change [A; A \ B] with ([] ++ [A] ++ [A \ B]) in H_base.
      apply (Lcut_Cut A B (ab_yield t1) [] [A \ B]).
      - exact IH1.
      - exact H_base.
    }
    assert (H_step : L_Cut ((ab_yield t1) ++ (ab_yield t2) ++ [], B)).
    {
      change (ab_yield t1 ++ [A \ B]) with ((ab_yield t1) ++ [A \ B] ++ []) in H_cut1.
      apply (Lcut_Cut (A \ B) B (ab_yield t2) (ab_yield t1) []).
      - exact IH2.
      - exact H_cut1.
    }
    rewrite app_nil_r in H_step.
    exact H_step.
Qed.

Theorem AB_reduce_sound_in_L_Cut : forall (Gamma : list Fm) (C : Fm),
  AB_reduce Gamma C -> L_Cut (Gamma, C).
Proof.
  intros Gamma C H.
  induction H as [ A
                 | A B Gamma Delta H1 IH1 H2 IH2
                 | A B Gamma Delta H1 IH1 H2 IH2 ].
  - apply Lcut_Ax.
  - assert (H_base : L_Cut ([B / A; A], B)).
    {
      apply cut_free_to_cut.
      apply app_slash.
    }
    assert (H_cut1 : L_Cut ([B / A] ++ Delta, B)).
    {
      change [B / A; A] with ([B / A] ++ [A] ++ []) in H_base.
      assert (H_step : L_Cut ([B / A] ++ Delta ++ [], B)).
      {
        apply (Lcut_Cut A B Delta [B / A] []).
        - exact IH2.
        - exact H_base.
      }
      rewrite app_nil_r in H_step.
      exact H_step.
    }
    change (Gamma ++ Delta) with ([] ++ Gamma ++ Delta).
    change ([B / A] ++ Delta) with ([] ++ [B / A] ++ Delta) in H_cut1.
    apply (Lcut_Cut (B / A) B Gamma [] Delta).
    + exact IH1.
    + exact H_cut1.
  - assert (H_base : L_Cut ([A; A \ B], B)).
    {
      apply cut_free_to_cut.
      apply app_backslash.
    }
    assert (H_cut1 : L_Cut (Gamma ++ [A \ B], B)).
    {
      change [A; A \ B] with ([] ++ [A] ++ [A \ B]) in H_base.
      apply (Lcut_Cut A B Gamma [] [A \ B]).
      - exact IH1.
      - exact H_base.
    }
    assert (H_step : L_Cut (Gamma ++ Delta ++ [], B)).
    {
      change (Gamma ++ [A \ B]) with (Gamma ++ [A \ B] ++ []) in H_cut1.
      apply (Lcut_Cut (A \ B) B Delta Gamma []).
      - exact IH2.
      - exact H_cut1.
    }
    rewrite app_nil_r in H_step.
    exact H_step.
Qed.

(* Section 4: Gaifman-Kazimierz Embedding *)

Definition gk_functor_slash (A C : nonterm) : Fm :=
  (Atom A) / (Atom C).

Definition gk_functor_backslash (A B : nonterm) : Fm :=
  (Atom B) \ (Atom A).

Theorem gk_rule_slash_sound : forall (A B C : nonterm),
  L ([gk_functor_slash A C; Atom C], Atom A).
Proof.
  intros A B C.
  unfold gk_functor_slash.
  apply app_slash.
Qed.

Theorem gk_rule_backslash_sound : forall (A B C : nonterm),
  L ([Atom B; gk_functor_backslash A B], Atom A).
Proof.
  intros A B C.
  unfold gk_functor_backslash.
  apply app_backslash.
Qed.

(* Gaifman-Kazimierz Compositionality in L *)
Theorem gk_chain_sound : forall (A B C : nonterm) (Delta : list Fm),
  L (Delta, Atom C) ->
  L ([gk_functor_slash A C] ++ Delta, Atom A).
Proof.
  intros A B C Delta H.
  unfold gk_functor_slash.
  apply cut_app_slash.
  exact H.
Qed.
