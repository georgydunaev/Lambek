# [LAMBEK] Ticket TKT-011 — Implement Sequent Calculus Cut-Elimination Procedure for the Associative Lambek Calculus (L)

**Repository:** `Lambek`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T22:40:00Z`  
**Resolved:** `2026-11-13T22:45:00Z`  
**Author:** `Lambek Calculus and Categorial Proof Specialist`  

## Problem Description
1. Joachim Lambek's 1958 foundational paper established the cut-elimination theorem for the syntactic calculus: any sequent derivable with the Cut rule is derivable without the Cut rule.
2. While `lambek/prover.py` provides cut-free backward proof search, the engine lacked an explicit constructive cut admissibility procedure:
   - Given a derivation d1 of Gamma |- A and a derivation d2 of Delta1, A, Delta2 |- B, directly eliminate the cut to produce a cut-free derivation of Delta1, Gamma, Delta2 |- B.
3. In Coq (`01.v` and `src/Lambek.v`), while principal cut reduction lemmas were stated for the calculus with Cut (`FullL_Cut`), direct cut admissibility theorems for the cut-free calculus `FullL` (and `L`) were not fully formalized.

## Resolution Plan
1. Implement `lambek/cut_elimination.py`:
   - Constructive function `admit_cut(d1: ProofNode, d2: ProofNode, cut_index: int) -> ProofNode`.
   - Explicit Gentzen-Lambek cut reduction rules:
     * Identity reductions (when either premise is an Axiom).
     * Principal connective reductions for Left Division (`\`), Right Division (`/`), and Product (`*`).
     * Permutative / commutative reductions for context formulas.
   - Comprehensive cut validator `verify_cut_elimination(d_cut, d_cutfree)`.
2. Formalize constructive cut admissibility in Coq (`01.v` and `src/Lambek.v`):
   - Identity axiom cut admissibility lemmas (`cut_admissibility_ax_l`, `cut_admissibility_ax_r`).
   - Category composition cut theorems for slash and backslash (`cut_app_backslash`, `cut_app_slash`).
   - Multi-premise Geach composition cuts (`cut_geach_backslash`, `cut_geach_slash`).
   - Product introduction cut admissibility (`cut_prod_intro`).
3. Add unit tests in `tests/test_linguistic_and_cut.py` verifying cut admissibility across all connective types and linguistic derivations.
