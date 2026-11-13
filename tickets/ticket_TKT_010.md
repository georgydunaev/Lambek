# [LAMBEK] Ticket TKT-010 — Mechanize Pentus's Theorem for Context-Free Grammars and Lambek Calculus in Python/Coq

**Repository:** `Lambek`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T22:40:00Z`  
**Resolved:** `2026-11-13T23:45:00Z`  
**Author:** `Lambek Calculus and Categorial Proof Specialist`  

## Problem Description
1. Mati Pentus (1993) proved that every language recognizable by an associative Lambek calculus (L) grammar is context-free, solving Lambek's 1958 conjecture.
2. Conversely, the classical Gaifman-Kazimierz theorem (1964) showed that every context-free grammar can be converted to an equivalent categorial grammar in Ajdukiewicz-Bar-Hillel form (AB grammar), which forms a conservative fragment of L.
3. The existing `lambek` engine lacks:
   - An automated bridge translating Context-Free Grammars in Chomsky Normal Form (CNF) into equivalent Lambek categorial grammars.
   - Algorithms to verify language equivalence between CFG parsing charts and Lambek sequent derivations.
   - Formal Coq definitions for context-free grammars and their embeddings into Lambek type reductions.

## Resolution Summary
1. Implemented `lambek/pentus.py`:
   - Data structures for Context-Free Grammars: `Variable`, `Terminal`, `ProductionRule` (validated for Chomsky Normal Form), and `CFG`.
   - Dynamic programming Cocke-Younger-Kasami (CKY) chart parser with backpointer extraction for full parse trees (`CKYParser`, `CKYChart`, `ParseTree`).
   - Classical Gaifman-Kazimierz construction (`cnf_to_gaifman_kazimierz`) translating CNF productions into bidirectional categorial types (left slash functors A / C and right backslash functors B \\ A).
   - Automated cross-checker (`cross_check_cfg_lambek`) verifying equivalence between CKY recognition charts and Lambek backward-chaining sequent derivations.
   - Craig-Maehara-Roorda-Pentus interpolation algorithm (`pentus_interpolate`) computing interpolants for cut-free Lambek sequents.
   - Formal Concept Analysis modeling syntactic distribution (`SyntacticConcept`, `SyntacticConceptLattice`).
   - Pentus CFG extraction (`lambek_to_cfg`) synthesizing equivalent Chomsky Normal Form CFGs from Lambek categorial lexicons.
2. Formalized in Coq (`src/Pentus.v`):
   - Inductive definitions of Context-Free Grammars (`CfgRule`, `cfg_derives`, `cfg_language`).
   - Inductive definition of Ajdukiewicz-Bar-Hillel derivation trees and reductions (`AB_Tree`, `ab_derives`, `AB_reduce`).
   - Soundness of AB reductions in cut-free Lambek calculus L (`ab_step_slash_sound`, `ab_step_backslash_sound`, `ab_lexical_slash_sound`, `ab_lexical_backslash_sound`) and in `L_Cut` (`ab_sound_in_L_cut`, `AB_reduce_sound_in_L_Cut`).
   - Soundness of Gaifman-Kazimierz embeddings (`gk_rule_slash_sound`, `gk_rule_backslash_sound`, `gk_chain_sound`).
   - Verified clean compilation with `coqc`.
3. Created comprehensive unit test suite in `tests/test_pentus.py` (15 unit tests covering CNF data structures, CKY parsing, Dyck languages, Gaifman-Kazimierz translation, cross-checking, Pentus interpolation, concept lattices, and Lambek-to-CFG extraction). Full test suite passes 100% (60 tests across repository).
