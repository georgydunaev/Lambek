# [LAMBEK] Ticket TKT-012 — Build an Interactive Derivation Tree Visualizer and Natural Language Sentence Parser in tools/lambek_prover.py

**Repository:** `Lambek`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T22:40:00Z`  
**Resolved:** `2026-11-13T22:45:00Z`  
**Author:** `Lambek Calculus and Categorial Proof Specialist`  

## Problem Description
1. Users and researchers require an interactive CLI and visualizer tool to:
   - Prove Lambek sequents from the command line with rich ASCII box formatting, Unicode sequents, and LaTeX proof-tree exports (`\infer`).
   - Parse complex natural language sentences into syntactic derivation trees.
   - Demonstrate cut elimination and cut admissibility interactively.
2. The repository lacked the `tools/lambek_prover.py` utility.
3. Natural language parsing lacked automated coverage for advanced linguistic phenomena:
   - Right node raising (e.g., "John likes and Mary loves Alice").
   - Subject and object relative clauses (e.g., "book which fell", "book which John read").
   - Medial extraction and noun phrase conjunctions.

## Resolution Plan
1. Create `tools/lambek_prover.py` featuring:
   - CLI flags: `--prove`, `--parse`, `--cut`, `--format`, `--latex`, `--lexicon`, `--interactive`.
   - Rich ASCII box-drawing derivation tree renderer.
   - LaTeX proof-tree (`bussproofs` / `ebproof` / `proof.sty`) exporter.
   - Pre-configured linguistic lexicon supporting transitive verbs, intransitive verbs, determiners, relative pronouns (subject/object extraction), and polytypic conjunctions.
2. Build unit test suite in `tests/test_linguistic_and_cut.py` asserting correct derivations and parse trees for:
   - Right node raising / transitive verb coordination.
   - Relative clauses with object extraction.
   - CLI execution and formatted output.
