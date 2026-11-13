# [LAMBEK] Ticket 7452 — Automated Test Suite for Provability and Countermodel Generation

**Repository:** `Lambek`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:55:00Z`  
**Resolved:** `2026-11-13T22:10:00Z`  
**Author:** `Lambek Calculus Verification Engineer`  

## Problem Description
1. Existing test suite `tests/test_lambek.py` only checked superficial file existence and file size.
2. No automated unit tests for sequent provability, left/right division reductions, Lambek lifting, Geach composition, or currying.
3. No countermodel generator or test coverage for invalid sequents (detecting violations of non-commutativity, non-contraction, and non-weakening).

## Resolution Plan
1. Implement `lambek/countermodel.py` generating concrete countermodels / refutations for unprovable sequents.
2. Build comprehensive test suite in `tests/test_lambek_engine.py` covering:
   - Coq formal verification and compilation via `coqc`.
   - Forward and backward slash type parsing and arithmetic.
   - All standard valid Lambek theorems.
   - Invalid sequents, refutations, and countermodels.
   - Natural language categorial grammar sentence derivations.

## Resolution Summary
- Implemented `lambek/countermodel.py` which diagnoses empty antecedents, Lambek-van Benthem count invariant failures, weakening violations, contraction violations, exchange/permutation failures, and produces concrete monoid counterexamples over free monoid languages.
- Implemented `tests/test_lambek_engine.py` with 26 unit tests verifying all Coq scripts (compiling cleanly via `coqc` and `coqtop`), AST parsing, sequent proofs (identity, application, Geach, lifting, associativity, relative clauses), substructural rejections, NL bracket trees, natural language sentences, and countermodel generation.
- All unit tests pass with 100% success rate (`Ran 26 tests. OK`).

