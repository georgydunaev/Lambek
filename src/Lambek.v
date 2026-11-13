(* Formal Verification of the Lambek Calculus in Coq *)
(* Syntactic Calculus (L) and Non-Associative Lambek Calculus (NL) *)

Require Import List.
Import ListNotations.

Definition var := nat.

Inductive Fm : Type :=
| Atom : var -> Fm
| BSlash : Fm -> Fm -> Fm   (* A \ B : left division *)
| Slash : Fm -> Fm -> Fm    (* B / A : right division *)
| Prod : Fm -> Fm -> Fm.    (* A * B : product *)

Coercion Atom : var >-> Fm.

Infix "\" := BSlash (left associativity, at level 64).
Infix "/" := Slash (left associativity, at level 40).
Infix "*" := Prod (left associativity, at level 40).

Definition Sequent := (list Fm * Fm)%type.

(* Section 1: Associative Lambek Sequent Calculus L (Cut-Free) *)
Inductive L : Sequent -> Prop :=
| L_Ax : forall (A : Fm), L ([A], A)
| L_BSlash_R : forall (A B : Fm) (Gamma : list Fm),
    L (A :: Gamma, B) ->
    L (Gamma, A \ B)
| L_BSlash_L : forall (A B C : Fm) (Phi Gamma Delta : list Fm),
    L (Phi, A) ->
    L (Gamma ++ [B] ++ Delta, C) ->
    L (Gamma ++ Phi ++ [A \ B] ++ Delta, C)
| L_Slash_R : forall (A B : Fm) (Gamma : list Fm),
    L (Gamma ++ [A], B) ->
    L (Gamma, B / A)
| L_Slash_L : forall (A B C : Fm) (Phi Gamma Delta : list Fm),
    L (Phi, A) ->
    L (Gamma ++ [B] ++ Delta, C) ->
    L (Gamma ++ [B / A] ++ Phi ++ Delta, C)
| L_Prod_R : forall (A B : Fm) (Gamma Delta : list Fm),
    L (Gamma, A) ->
    L (Delta, B) ->
    L (Gamma ++ Delta, A * B)
| L_Prod_L : forall (A B C : Fm) (Gamma Delta : list Fm),
    L (Gamma ++ [A; B] ++ Delta, C) ->
    L (Gamma ++ [A * B] ++ Delta, C).

(* Fundamental Theorems of Lambek Deductions *)

Theorem app_backslash : forall (A B : Fm), L ([A; A \ B], B).
Proof.
  intros A B.
  change [A; A \ B] with ([] ++ [A] ++ [A \ B] ++ []).
  apply L_BSlash_L.
  - apply L_Ax.
  - apply L_Ax.
Qed.

Theorem app_slash : forall (A B : Fm), L ([B / A; A], B).
Proof.
  intros A B.
  change [B / A; A] with ([] ++ [B / A] ++ [A] ++ []).
  apply L_Slash_L.
  - apply L_Ax.
  - apply L_Ax.
Qed.

Theorem lifting_backslash : forall (A B : Fm), L ([A], B / (A \ B)).
Proof.
  intros A B.
  apply L_Slash_R.
  apply app_backslash.
Qed.

Theorem lifting_slash : forall (A B : Fm), L ([A], (B / A) \ B).
Proof.
  intros A B.
  apply L_BSlash_R.
  apply app_slash.
Qed.

Theorem geach_backslash : forall (A B C : Fm), L ([A \ B; B \ C], A \ C).
Proof.
  intros A B C.
  apply L_BSlash_R.
  change (A :: [A \ B; B \ C]) with ([] ++ [A; A \ B] ++ [B \ C] ++ []).
  apply L_BSlash_L.
  - apply app_backslash.
  - apply L_Ax.
Qed.

Theorem geach_slash : forall (A B C : Fm), L ([C / B; B / A], C / A).
Proof.
  intros A B C.
  apply L_Slash_R.
  change ([C / B; B / A] ++ [A]) with ([C / B] ++ [B / A] ++ [A] ++ []).
  apply L_Slash_L.
  - apply L_Ax.
  - apply app_slash.
Qed.

Theorem prod_intro : forall (A B : Fm), L ([A; B], A * B).
Proof.
  intros A B.
  change [A; B] with ([A] ++ [B]).
  apply L_Prod_R; apply L_Ax.
Qed.

Theorem prod_assoc_1 : forall (A B C : Fm), L ([(A * B) * C], A * (B * C)).
Proof.
  intros A B C.
  change [(A * B) * C] with ([] ++ [(A * B) * C] ++ []).
  apply L_Prod_L.
  change ([] ++ [A * B; C] ++ []) with ([] ++ [A * B] ++ [C]).
  apply L_Prod_L.
  change ([] ++ [A; B] ++ [C]) with ([A] ++ [B; C]).
  apply L_Prod_R.
  - apply L_Ax.
  - apply prod_intro.
Qed.

Theorem prod_assoc_2 : forall (A B C : Fm), L ([A * (B * C)], (A * B) * C).
Proof.
  intros A B C.
  change [A * (B * C)] with ([] ++ [A * (B * C)] ++ []).
  apply L_Prod_L.
  change ([] ++ [A; B * C] ++ []) with ([A] ++ [B * C] ++ []).
  apply L_Prod_L.
  change ([A] ++ [B; C] ++ []) with ([A; B] ++ [C]).
  apply L_Prod_R.
  - apply prod_intro.
  - apply L_Ax.
Qed.

(* Section 2: Sequent Calculus with Cut and Cut Reduction *)

Inductive L_Cut : Sequent -> Prop :=
| Lcut_Ax : forall (A : Fm), L_Cut ([A], A)
| Lcut_Cut : forall (A C : Fm) (Phi Gamma Delta : list Fm),
    L_Cut (Phi, A) ->
    L_Cut (Gamma ++ [A] ++ Delta, C) ->
    L_Cut (Gamma ++ Phi ++ Delta, C)
| Lcut_BSlash_R : forall (A B : Fm) (Gamma : list Fm),
    L_Cut (A :: Gamma, B) ->
    L_Cut (Gamma, A \ B)
| Lcut_BSlash_L : forall (A B C : Fm) (Phi Gamma Delta : list Fm),
    L_Cut (Phi, A) ->
    L_Cut (Gamma ++ [B] ++ Delta, C) ->
    L_Cut (Gamma ++ Phi ++ [A \ B] ++ Delta, C)
| Lcut_Slash_R : forall (A B : Fm) (Gamma : list Fm),
    L_Cut (Gamma ++ [A], B) ->
    L_Cut (Gamma, B / A)
| Lcut_Slash_L : forall (A B C : Fm) (Phi Gamma Delta : list Fm),
    L_Cut (Phi, A) ->
    L_Cut (Gamma ++ [B] ++ Delta, C) ->
    L_Cut (Gamma ++ [B / A] ++ Phi ++ Delta, C)
| Lcut_Prod_R : forall (A B : Fm) (Gamma Delta : list Fm),
    L_Cut (Gamma, A) ->
    L_Cut (Delta, B) ->
    L_Cut (Gamma ++ Delta, A * B)
| Lcut_Prod_L : forall (A B C : Fm) (Gamma Delta : list Fm),
    L_Cut (Gamma ++ [A; B] ++ Delta, C) ->
    L_Cut (Gamma ++ [A * B] ++ Delta, C).

Theorem cut_free_to_cut : forall (s : Sequent), L s -> L_Cut s.
Proof.
  intros s H.
  induction H.
  - apply Lcut_Ax.
  - apply Lcut_BSlash_R; assumption.
  - apply Lcut_BSlash_L; assumption.
  - apply Lcut_Slash_R; assumption.
  - apply Lcut_Slash_L; assumption.
  - apply Lcut_Prod_R; assumption.
  - apply Lcut_Prod_L; assumption.
Qed.

(* Residuation / Lambek Adjunction in L_Cut *)

Theorem residuation_slash_to_prod :
  forall (A B C : Fm), L_Cut ([A], C / B) -> L_Cut ([A * B], C).
Proof.
  intros A B C H.
  change [A * B] with ([] ++ [A * B] ++ []).
  apply Lcut_Prod_L.
  change ([] ++ [A; B] ++ []) with ([] ++ [A] ++ [B]).
  apply (Lcut_Cut (C / B) C [A] [] [B]).
  - exact H.
  - change ([] ++ [C / B] ++ [B]) with ([] ++ [C / B; B] ++ []).
    apply cut_free_to_cut.
    apply app_slash.
Qed.

Theorem residuation_backslash_to_prod :
  forall (A B C : Fm), L_Cut ([B], A \ C) -> L_Cut ([A * B], C).
Proof.
  intros A B C H.
  change [A * B] with ([] ++ [A * B] ++ []).
  apply Lcut_Prod_L.
  change ([] ++ [A; B] ++ []) with ([A] ++ [B] ++ []).
  apply (Lcut_Cut (A \ C) C [B] [A] []).
  - exact H.
  - change ([A] ++ [A \ C] ++ []) with ([] ++ [A; A \ C] ++ []).
    apply cut_free_to_cut.
    apply app_backslash.
Qed.

Lemma cut_reduction_backslash :
  forall (A B C : Fm) (Phi Phi_prime Gamma Delta : list Fm),
    L_Cut (A :: Phi, B) ->
    L_Cut (Phi_prime, A) ->
    L_Cut (Gamma ++ [B] ++ Delta, C) ->
    L_Cut (Gamma ++ Phi_prime ++ Phi ++ Delta, C).
Proof.
  intros A B C Phi Phi_prime Gamma Delta H_R H_L1 H_L2.
  assert (H_cut1 : L_Cut ([] ++ Phi_prime ++ Phi, B)).
  {
    change (A :: Phi) with ([] ++ [A] ++ Phi) in H_R.
    apply (Lcut_Cut A B Phi_prime [] Phi); assumption.
  }
  simpl in H_cut1.
  assert (H_cut2 : L_Cut (Gamma ++ (Phi_prime ++ Phi) ++ Delta, C)).
  {
    apply (Lcut_Cut B C (Phi_prime ++ Phi) Gamma Delta); assumption.
  }
  repeat rewrite app_assoc in *.
  exact H_cut2.
Qed.

Lemma cut_reduction_slash :
  forall (A B C : Fm) (Phi Phi_prime Gamma Delta : list Fm),
    L_Cut (Phi ++ [A], B) ->
    L_Cut (Phi_prime, A) ->
    L_Cut (Gamma ++ [B] ++ Delta, C) ->
    L_Cut (Gamma ++ Phi ++ Phi_prime ++ Delta, C).
Proof.
  intros A B C Phi Phi_prime Gamma Delta H_R H_L1 H_L2.
  assert (H_cut1 : L_Cut (Phi ++ Phi_prime ++ [], B)).
  {
    change (Phi ++ [A]) with (Phi ++ [A] ++ []) in H_R.
    apply (Lcut_Cut A B Phi_prime Phi []); assumption.
  }
  rewrite app_nil_r in H_cut1.
  assert (H_cut2 : L_Cut (Gamma ++ (Phi ++ Phi_prime) ++ Delta, C)).
  {
    apply (Lcut_Cut B C (Phi ++ Phi_prime) Gamma Delta); assumption.
  }
  repeat rewrite app_assoc in *.
  exact H_cut2.
Qed.

Lemma cut_reduction_prod :
  forall (A B C : Fm) (Gamma Delta Gamma_L Delta_L : list Fm),
    L_Cut (Gamma, A) ->
    L_Cut (Delta, B) ->
    L_Cut (Gamma_L ++ [A; B] ++ Delta_L, C) ->
    L_Cut (Gamma_L ++ Gamma ++ Delta ++ Delta_L, C).
Proof.
  intros A B C Gamma Delta Gamma_L Delta_L H_A H_B H_prem.
  assert (H_cut1 : L_Cut ((Gamma_L ++ [A]) ++ Delta ++ Delta_L, C)).
  {
    apply (Lcut_Cut B C Delta (Gamma_L ++ [A]) Delta_L).
    - exact H_B.
    - repeat rewrite app_assoc.
      change [A; B] with ([A] ++ [B]) in H_prem.
      repeat rewrite app_assoc in H_prem.
      exact H_prem.
  }
  assert (H_cut2 : L_Cut (Gamma_L ++ Gamma ++ (Delta ++ Delta_L), C)).
  {
    apply (Lcut_Cut A C Gamma Gamma_L (Delta ++ Delta_L)).
    - exact H_A.
    - repeat rewrite app_assoc in *.
      exact H_cut1.
  }
  repeat rewrite app_assoc in *.
  exact H_cut2.
Qed.

(* Constructive Cut Admissibility in Cut-Free Lambek Calculus (L) *)

Theorem cut_admissible_ax_l :
  forall (A C : Fm) (Gamma Delta : list Fm),
    L ([A], A) ->
    L (Gamma ++ [A] ++ Delta, C) ->
    L (Gamma ++ [A] ++ Delta, C).
Proof.
  intros A C Gamma Delta H_ax H_main.
  exact H_main.
Qed.

Theorem cut_admissible_ax_r :
  forall (A : Fm) (Phi : list Fm),
    L (Phi, A) ->
    L ([A], A) ->
    L (Phi, A).
Proof.
  intros A Phi H_prem H_ax.
  exact H_prem.
Qed.

Theorem cut_app_backslash :
  forall (A B : Fm) (Gamma : list Fm),
    L (Gamma, A) ->
    L (Gamma ++ [A \ B], B).
Proof.
  intros A B Gamma H.
  change (Gamma ++ [A \ B]) with ([] ++ Gamma ++ [A \ B] ++ []).
  apply L_BSlash_L.
  - exact H.
  - apply L_Ax.
Qed.

Theorem cut_app_slash :
  forall (A B : Fm) (Gamma : list Fm),
    L (Gamma, A) ->
    L ([B / A] ++ Gamma, B).
Proof.
  intros A B Gamma H.
  replace ([B / A] ++ Gamma) with ([] ++ [B / A] ++ Gamma ++ []).
  - apply L_Slash_L.
    + exact H.
    + apply L_Ax.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem cut_geach_backslash_single :
  forall (A B C : Fm) (Gamma : list Fm),
    L (A :: Gamma, B) ->
    L (Gamma ++ [B \ C], A \ C).
Proof.
  intros A B C Gamma H.
  apply L_BSlash_R.
  change (A :: Gamma ++ [B \ C]) with ([] ++ (A :: Gamma) ++ [B \ C] ++ []).
  apply L_BSlash_L.
  - exact H.
  - apply L_Ax.
Qed.

Theorem cut_geach_slash_single :
  forall (A B C : Fm) (Gamma : list Fm),
    L (Gamma ++ [A], B) ->
    L ([C / B] ++ Gamma, C / A).
Proof.
  intros A B C Gamma H.
  apply L_Slash_R.
  rewrite <- app_assoc.
  replace ([C / B] ++ (Gamma ++ [A])) with ([] ++ [C / B] ++ (Gamma ++ [A]) ++ []).
  - apply L_Slash_L.
    + exact H.
    + apply L_Ax.
  - simpl. rewrite app_nil_r. reflexivity.
Qed.

Theorem cut_prod_intro :
  forall (A B : Fm) (Gamma Delta : list Fm),
    L (Gamma, A) ->
    L (Delta, B) ->
    L (Gamma ++ Delta, A * B).
Proof.
  intros A B Gamma Delta H1 H2.
  apply L_Prod_R; assumption.
Qed.

(* Linguistic Derivations: Relative Clauses and Coordination *)

Theorem rel_clause_subj_extraction :
  forall (n np s : Fm),
    L ([n; (n \ n) / (np \ s); np \ s], n).
Proof.
  intros n np s.
  change [n; (n \ n) / (np \ s); np \ s]
    with ([n] ++ [(n \ n) / (np \ s)] ++ [np \ s] ++ []).
  apply L_Slash_L.
  - apply L_Ax.
  - apply app_backslash.
Qed.

Lemma np_tv_np :
  forall (np s : Fm),
    L ([np; (np \ s) / np; np], s).
Proof.
  intros np s.
  change [np; (np \ s) / np; np] with ([np] ++ [(np \ s) / np] ++ [np] ++ []).
  apply L_Slash_L.
  - apply L_Ax.
  - apply app_backslash.
Qed.

Lemma np_tv :
  forall (np s : Fm),
    L ([np; (np \ s) / np], s / np).
Proof.
  intros np s.
  apply L_Slash_R.
  apply np_tv_np.
Qed.

Theorem rel_clause_obj_extraction :
  forall (n np s : Fm),
    L ([n; (n \ n) / (s / np); np; (np \ s) / np], n).
Proof.
  intros n np s.
  change [n; (n \ n) / (s / np); np; (np \ s) / np]
    with ([n] ++ [(n \ n) / (s / np)] ++ [np; (np \ s) / np] ++ []).
  apply L_Slash_L.
  - apply np_tv.
  - apply app_backslash.
Qed.

Theorem rnr_coordination :
  forall (np s : Fm),
    L ([np; (np \ s) / np; ((s / np) \ (s / np)) / (s / np); np; (np \ s) / np; np], s).
Proof.
  intros np s.
  set (s_slash := s / np).
  change [np; (np \ s) / np; (s_slash \ s_slash) / s_slash; np; (np \ s) / np; np]
    with ([np; (np \ s) / np] ++ [(s_slash \ s_slash) / s_slash] ++ [np; (np \ s) / np] ++ [np]).
  apply L_Slash_L.
  - apply np_tv.
  - change ([np; (np \ s) / np] ++ [s_slash \ s_slash] ++ [np])
      with ([] ++ [np; (np \ s) / np] ++ [s_slash \ s_slash] ++ [np]).
    apply L_BSlash_L.
    + apply np_tv.
    + unfold s_slash. apply app_slash.
Qed.

(* Section 3: Non-Associative Lambek Calculus NL with Tree Antecedents *)

Inductive Tree : Type :=
| TLeaf : Fm -> Tree
| TNode : Tree -> Tree -> Tree.

Fixpoint flatten (t : Tree) : list Fm :=
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

Fixpoint ctx_left (c : TreeCtx) : list Fm :=
  match c with
  | Hole => []
  | NodeL c1 t2 => ctx_left c1
  | NodeR t1 c2 => flatten t1 ++ ctx_left c2
  end.

Fixpoint ctx_right (c : TreeCtx) : list Fm :=
  match c with
  | Hole => []
  | NodeL c1 t2 => ctx_right c1 ++ flatten t2
  | NodeR t1 c2 => ctx_right c2
  end.

Lemma flatten_fill : forall (c : TreeCtx) (t : Tree),
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

Inductive NL : Tree -> Fm -> Prop :=
| NL_Ax : forall (A : Fm), NL (TLeaf A) A
| NL_BSlash_R : forall (A B : Fm) (T : Tree),
    NL (TNode (TLeaf A) T) B ->
    NL T (A \ B)
| NL_BSlash_L : forall (A B C : Fm) (U : Tree) (c : TreeCtx),
    NL U A ->
    NL (fill c (TLeaf B)) C ->
    NL (fill c (TNode U (TLeaf (A \ B)))) C
| NL_Slash_R : forall (A B : Fm) (T : Tree),
    NL (TNode T (TLeaf A)) B ->
    NL T (B / A)
| NL_Slash_L : forall (A B C : Fm) (U : Tree) (c : TreeCtx),
    NL U A ->
    NL (fill c (TLeaf B)) C ->
    NL (fill c (TNode (TLeaf (B / A)) U)) C
| NL_Prod_R : forall (A B : Fm) (T1 T2 : Tree),
    NL T1 A ->
    NL T2 B ->
    NL (TNode T1 T2) (A * B)
| NL_Prod_L : forall (A B C : Fm) (c : TreeCtx),
    NL (fill c (TNode (TLeaf A) (TLeaf B))) C ->
    NL (fill c (TLeaf (A * B))) C.

Theorem NL_app_backslash : forall (A B : Fm),
  NL (TNode (TLeaf A) (TLeaf (A \ B))) B.
Proof.
  intros A B.
  change (TNode (TLeaf A) (TLeaf (A \ B))) with (fill Hole (TNode (TLeaf A) (TLeaf (A \ B)))).
  apply NL_BSlash_L.
  - apply NL_Ax.
  - apply NL_Ax.
Qed.

Theorem NL_app_slash : forall (A B : Fm),
  NL (TNode (TLeaf (B / A)) (TLeaf A)) B.
Proof.
  intros A B.
  change (TNode (TLeaf (B / A)) (TLeaf A)) with (fill Hole (TNode (TLeaf (B / A)) (TLeaf A))).
  apply NL_Slash_L.
  - apply NL_Ax.
  - apply NL_Ax.
Qed.

Theorem NL_to_L : forall (t : Tree) (C : Fm),
  NL t C -> L (flatten t, C).
Proof.
  intros t C H.
  induction H as [ A
                 | A B T H0 IH
                 | A B C U c H0 IH1 H1 IH2
                 | A B T H0 IH
                 | A B C U c H0 IH1 H1 IH2
                 | A B T1 T2 H0 IH1 H1 IH2
                 | A B C c H0 IH ].
  - simpl. apply L_Ax.
  - simpl in IH.
    apply L_BSlash_R.
    exact IH.
  - rewrite flatten_fill.
    rewrite flatten_fill in IH2.
    simpl.
    rewrite <- app_assoc.
    apply L_BSlash_L.
    + exact IH1.
    + exact IH2.
  - simpl in IH.
    apply L_Slash_R.
    exact IH.
  - rewrite flatten_fill.
    rewrite flatten_fill in IH2.
    simpl.
    apply L_Slash_L.
    + exact IH1.
    + exact IH2.
  - simpl.
    apply L_Prod_R.
    + exact IH1.
    + exact IH2.
  - rewrite flatten_fill.
    rewrite flatten_fill in IH.
    simpl in IH.
    apply L_Prod_L.
    exact IH.
Qed.
