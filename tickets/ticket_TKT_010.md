# [LAMBEK] Ticket TKT-010 — Mechanize Pentus's Theorem for Context-Free Grammars and Lambek Calculus in Python/Coq

**Repository:** `Lambek`  
**Status:** `OPEN`  
**Created:** `2026-11-13T22:40:00Z`  
**Author:** `Lambek Calculus and Categorial Proof Specialist`  

## Problem Description
1. Mati Pentus (1993) proved that every language recognizable by an associative Lambek calculus (L) grammar is context-free, solving Lambek's 1958 conjecture.
2. Conversely, the classical Gaifman-Kazimierz theorem (1964) showed that every context-free grammar can be converted to an equivalent categorial grammar in Ajdukiewicz-Bar-Hillel form (AB grammar), which forms a conservative fragment of L.
3. The existing `lambek` engine lacks:
   - An automated bridge translating Context-Free Grammars in Chomsky Normal Form (CNF) into equivalent Lambek categorial grammars.
   - Algorithms to verify language equivalence between CFG parsing charts and Lambek sequent derivations.
   - Formal Coq definitions for context-free grammars and their embeddings into Lambek type reductions.

## Resolution Plan
1. Implement in `lambek/pentus.py`:
   - Data structures for Context-Free Grammars (Variables, Terminals, Production Rules in Chomsky Normal Form).
   - Translation from CFG productions (A -> B C and A -> a) into Lambek categorial types using the Gaifman-Kazimierz construction.
   - Earley / CKY parser for CFGs cross-checked against Lambek backward-chaining derivations.
   - Interpolation and translation algorithms representing the syntactic concept lattices underlying Pentus's proof.
2. Formalize in Coq (`src/Pentus.v` or `src/Lambek.v`):
   - Inductive definitions of context-free languages and Chomsky-Bar-Hillel derivation systems.
   - Soundness of AB reduction within cut-free Lambek calculus L.
3. Add automated test coverage in `tests/test_pentus.py` verifying equivalence on standard formal languages (Dyck languages, palindromes, linguistic phrase structures).
