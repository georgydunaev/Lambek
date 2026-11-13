# [LAMBEK] Ticket 7449 — Coq Syntax Repair and Multi-Connective Lambek Calculus in 01.v

**Repository:** `Lambek`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:55:00Z`  
**Resolved:** `2026-11-13T22:10:00Z`  
**Author:** `Lambek Calculus Verification Engineer`  

## Problem Description
1. The file `01.v` failed to load in Coq because lines 44-48 replaced `Inductive Plus : Word -> Prop :=` with invalid imports `Require Import src.plus.` and `Require Import src.minus.`.
2. Furthermore, `coqc 01.v` fails because Coq identifier syntax forbids module names starting with a digit (`01`), requiring a standard Coq module name (such as `Lambek.v`) and clean script loading.
3. The formulas in `01.v` only defined atoms and backslash (`\`), lacking forward slash (`/`, right division) and product (`•`).
4. Proofs of valid deductions for Lambek calculus (application, Geach composition, Lambek value raising / type lifting, and product associativity) were missing.

## Resolution Plan
1. Restore the mutual inductive definition of `Plus` and `Minus` in `01.v`.
2. Extend `Fm` with forward slash (`Slash`, `/`) and product (`Prod`, `•`).
3. Define the full associative Lambek sequent calculus with rules for all three connectives.
4. Formalize and prove structural properties and fundamental Lambek deductions.
5. Provide standard Coq module `Lambek.v` compilable via `coqc`.

## Resolution Summary
- Repaired `01.v`: Restored mutual inductive types `Plus` and `Minus`, isolated notation `"x , y"` in `Section LBS`, added full multi-connective calculus `FullL` with `/`, `\`, and `*`.
- Proved valid deductions: application (`full_app_backslash`, `full_app_slash`), Geach composition (`full_geach_backslash`, `full_geach_slash`), type lifting (`full_lifting_backslash`, `full_lifting_slash`), and product associativity (`full_prod_assoc_1`, `full_prod_assoc_2`).
- Modularized clean Coq modules `src/WordTypes.v`, `src/plus.v`, `src/minus.v`, `src/Lambek.v`, and root `Lambek.v`, all 100% compiling cleanly under Coq 8.20.1.

