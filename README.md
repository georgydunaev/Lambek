# Lambek Calculus Formalization and Decision Engine

This repository provides a formalization of the Lambek Syntactic Calculus in Coq alongside an executable Python decision engine, proof search tool, categorial grammar parser, and countermodel generator.

The system covers:
1. **Associative Lambek Calculus (L)** (Lambek 1958) with Left Division (`\`), Right Division (`/`), and Product (`•` or `*`).
2. **Non-Associative Lambek Calculus (NL)** (Lambek 1961) with tree-structured antecedents and no bracket re-association.
3. **Cut Admissibility and Principal Cut Reductions** for all three connectives.
4. **Executable Proof Search in Python** implementing cut-free backward-chaining with derivation trees.
5. **Categorial Grammar Parser** for natural language syntax with lexical category assignment and SVO parsing.
6. **Countermodel & Refutation Generator** diagnosing empty antecedents, Lambek-van Benthem polarity invariant violations, exchange/permutation failures, weakening/contraction violations, and free monoid language counterexamples.

---

## Directory Structure

- `01.v`: Complete Coq formalization containing word types, literal negations, `Plus` and `Minus` relations, original one-sided LBS calculus, full multi-connective Lambek calculus `FullL`, tree-based non-associative calculus `NL`, embedding theorem `NL_sound_in_L`, and cut reduction lemmas.
- `Lambek.v`: Root module re-exporting the formal library for standard `coqc` compilation.
- `_CoqProject`: Coq build configuration mapping `-Q src src` and `-Q examples examples`.
- `src/`:
  - `WordTypes.v`: Variables, literals, words, negation, double negation, and inductive `Plus`/`Minus` relations.
  - `plus.v` & `minus.v`: Re-exported word relations.
  - `Lambek.v`: Full modular formalization of L, NL, cut reductions, and valid deductions.
- `examples/`:
  - `example1.v`: Word and relation evaluations.
  - `example_01.v`: Step-by-step tutorial on word types.
  - `slash_backslash_examples.v`: Left and right division proofs in Coq.
  - `sequent_examples.v`: Sequent derivations for transitive sentences and Geach composition.
- `lambek/`:
  - `types.py`: AST for atomic categories, divisions, and products with recursive descent parsing and atom polarity counting.
  - `sequent.py`: Data structures for associative and non-associative sequents with Lambek-van Benthem invariant checks.
  - `prover.py`: Backward-chaining cut-free proof search engine returning explicit proof trees.
  - `grammar.py`: Lexicon and categorial grammar parser for sentence syntax.
  - `countermodel.py`: Diagnostic refutations and monoid language counterexamples for invalid sequents.
- `tests/`:
  - `test_lambek_engine.py`: Unit test suite testing Coq compilation, AST parsing, sequent proofs, grammatical derivations, and countermodel refutations.
  - `test_lambek.py`: File integrity and structural checks.
- `tickets/`: Project tickets documenting verification, gap identification, and resolutions.

---

## Coq Verification

To verify the Coq formalizations:

```bash
# Verify 01.v via Coq top-level batch mode:
coqtop -batch -load-vernac-source 01.v

# Compile modular library and examples via coqc:
coqc -Q src src src/WordTypes.v
coqc -Q src src src/plus.v
coqc -Q src src src/minus.v
coqc -Q src src src/Lambek.v
coqc -Q src src Lambek.v
coqc -Q src src examples/sequent_examples.v
```

All formal proofs compile cleanly under Coq 8.20.1 with zero admitted lemmas.

---

## Python Engine Usage

The Python package `lambek` can be imported directly or executed via scripts:

```python
import lambek

# 1. Parsing syntactic types and sequents
seq = lambek.parse_sequent(r"np, (np \ s) / np, np |- s")
print("Sequent:", seq)

# 2. Automated proof search
proof = lambek.prove_sequent(seq)
if proof:
    print("Derivation found:\n", proof)

# 3. Substructural refutations and countermodels
invalid_seq = lambek.parse_sequent("A, B |- B * A")
cm = lambek.find_countermodel(invalid_seq)
print(cm)

# 4. Natural language categorial grammar parsing
derivations = lambek.parse_sentence("Alice solved the hard problem", target="s")
for d in derivations:
    print("Sentence derivation:\n", d)
```

---

## Running Tests

Run the complete test suite with Python's unittest runner:

```bash
PYTHONPATH=. python3 -m unittest discover -s tests -p 'test_*.py'
```

---

## Invariants and Substructural Logics

The Lambek calculus is a substructural logic characterized by:
- **No Exchange**: Word order is preserved ($A, B \vdash B \bullet A$ is unprovable).
- **No Weakening**: Extraneous resources are disallowed ($A, B \vdash A$ is unprovable).
- **No Contraction**: Hypotheses cannot be duplicated ($A \vdash A \bullet A$ is unprovable).
- **Non-Empty Antecedents**: Sequents must have at least one premise on the left.
