# [LAMBEK] Ticket 7450 — Non-Associative and Associative Lambek Calculi with Cut Elimination

**Repository:** `Lambek`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:55:00Z`  
**Resolved:** `2026-11-13T22:10:00Z`  
**Author:** `Lambek Calculus Verification Engineer`  

## Problem Description
1. Lack of non-associative syntactic types and tree-structured sequents (Non-associative Lambek Calculus NL).
2. Absence of formal cut rule and cut-elimination / admissibility proofs in Coq for the Lambek sequent calculus.
3. Substructural distinctions (failure of weakening, contraction, and permutation) were not formally documented or verified.

## Resolution Plan
1. Define non-associative bracketed configurations (tree sequents for NL) alongside associative sequence sequents (L).
2. Formalize the cut rule and demonstrate cut-elimination and admissibility of cut in cut-free sequent calculus.
3. Formally verify the failure of permutation in NL/L (non-commutativity) and the distinction between NL (no re-bracketing) and L (associative re-bracketing).
4. Verify complete Coq compilation via `coqc`.

## Resolution Summary
- Defined tree-structured antecedents `NLTree` and non-associative sequent calculus `NL` in `01.v` and `src/Lambek.v`.
- Proved sound embedding of NL into L via tree flattening (`NL_sound_in_L`).
- Formalized cut rule `FullL_Cut` and proved principal cut reduction lemmas for backslash (`cut_reduction_backslash`), slash (`cut_reduction_slash`), and product (`cut_reduction_prod`).
- Verified non-commutativity and substructural invariants across both formalizations and unit tests.

