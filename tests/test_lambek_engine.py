#!/usr/bin/env python3
"""Comprehensive test suite for Lambek Calculus Coq formalization and Python engine."""

import os
import subprocess
import unittest

from lambek.types import Atom, Slash, Backslash, Product, parse_type
from lambek.sequent import Sequent, TreeAntecedent, TreeSequent, parse_sequent
from lambek.prover import LambekProver, prove_sequent
from lambek.grammar import Lexicon, parse_sentence
from lambek.countermodel import find_countermodel, evaluate_language

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestCoqFormalization(unittest.TestCase):
    """Verify that all Coq formalizations and examples compile without errors."""

    def test_01_v_compilation(self):
        res = subprocess.run(
            ["coqtop", "-batch", "-load-vernac-source", "01.v"],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(
            res.returncode, 0,
            f"01.v failed to load in coqtop:\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}"
        )

    def test_modular_coq_modules(self):
        modules = [
            "src/WordTypes.v",
            "src/plus.v",
            "src/minus.v",
            "src/Lambek.v",
            "Lambek.v",
            "examples/example1.v",
            "examples/example_01.v",
            "examples/slash_backslash_examples.v",
            "examples/sequent_examples.v",
        ]
        for rel in modules:
            path = os.path.join(ROOT, rel)
            res = subprocess.run(
                ["coqc", "-Q", "src", "src", rel],
                cwd=ROOT,
                capture_output=True,
                text=True,
            )
            self.assertEqual(
                res.returncode, 0,
                f"{rel} failed to compile with coqc:\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}"
            )


class TestTypeAST(unittest.TestCase):
    """Test AST representation, parsing, complexity, and invariants of syntactic types."""

    def test_atoms(self):
        a = Atom("s")
        self.assertEqual(str(a), "s")
        self.assertEqual(repr(a), "Atom('s')")
        self.assertEqual(a.complexity, 0)
        self.assertEqual(a.atoms(), {"s"})
        self.assertEqual(a.count_polarity(+1), {"s": 1})
        self.assertEqual(a.count_polarity(-1), {"s": -1})

    def test_complex_types(self):
        # (np \ s) / np
        tv = Slash(Backslash(Atom("np"), Atom("s")), Atom("np"))
        self.assertEqual(str(tv), "(np \\ s) / np")
        self.assertEqual(tv.complexity, 2)
        self.assertEqual(tv.atoms(), {"np", "s"})
        # In tv with positive polarity:
        # tv = B / A where B = (np \ s), A = np
        # B counts with +1: np has -1, s has +1
        # A counts with -1: np has -1
        # Net: s has +1, np has -2
        counts = tv.count_polarity(+1)
        self.assertEqual(counts["s"], 1)
        self.assertEqual(counts["np"], -2)

    def test_type_parser(self):
        self.assertEqual(parse_type("s"), Atom("s"))
        self.assertEqual(parse_type("np \\ s"), Backslash(Atom("np"), Atom("s")))
        self.assertEqual(parse_type("(np \\ s) / np"), Slash(Backslash(Atom("np"), Atom("s")), Atom("np")))
        self.assertEqual(parse_type("A * B"), Product(Atom("A"), Atom("B")))
        self.assertEqual(parse_type("A * B * C"), Product(Product(Atom("A"), Atom("B")), Atom("C")))
        self.assertEqual(parse_type("A \\ B / C"), Slash(Backslash(Atom("A"), Atom("B")), Atom("C")))

    def test_round_trip(self):
        exprs = [
            "s",
            "np \\ s",
            "(np \\ s) / np",
            "((s / np) \\ s) / ((s / np) \\ s)",
            "(A * B) * C",
        ]
        for expr in exprs:
            ast = parse_type(expr)
            self.assertEqual(parse_type(str(ast)), ast)


class TestSequentAndProver(unittest.TestCase):
    """Test proof search and deduction rules in Associative Lambek Calculus (L)."""

    def setUp(self):
        self.prover = LambekProver()

    def test_identity(self):
        seq = parse_sequent("s |- s")
        proof = self.prover.prove(seq)
        self.assertIsNotNone(proof)
        self.assertEqual(proof.rule, "Ax")

    def test_left_application(self):
        # np, np \ s |- s
        seq = parse_sequent(r"np, np \ s |- s")
        proof = self.prover.prove(seq)
        self.assertIsNotNone(proof)

    def test_right_application(self):
        # s / np, np |- s
        seq = parse_sequent("s / np, np |- s")
        proof = self.prover.prove(seq)
        self.assertIsNotNone(proof)

    def test_transitive_sentence(self):
        # np, (np \ s) / np, np |- s
        seq = parse_sequent(r"np, (np \ s) / np, np |- s")
        proof = self.prover.prove(seq)
        self.assertIsNotNone(proof)

    def test_geach_composition(self):
        # Forward Geach: A / B, B / C |- A / C
        seq1 = parse_sequent("A / B, B / C |- A / C")
        self.assertIsNotNone(self.prover.prove(seq1))

        # Backward Geach: C \ B, B \ A |- C \ A
        seq2 = parse_sequent(r"C \ B, B \ A |- C \ A")
        self.assertIsNotNone(self.prover.prove(seq2))

    def test_type_lifting(self):
        # Forward lifting: A |- B / (A \ B)
        seq1 = parse_sequent(r"A |- B / (A \ B)")
        self.assertIsNotNone(self.prover.prove(seq1))

        # Backward lifting: A |- (B / A) \ B
        seq2 = parse_sequent(r"A |- (B / A) \ B")
        self.assertIsNotNone(self.prover.prove(seq2))

    def test_product_rules_and_associativity(self):
        # A, B |- A * B
        seq_intro = parse_sequent("A, B |- A * B")
        self.assertIsNotNone(self.prover.prove(seq_intro))

        # (A * B) * C |- A * (B * C)
        seq_assoc1 = parse_sequent("(A * B) * C |- A * (B * C)")
        self.assertIsNotNone(self.prover.prove(seq_assoc1))

        # A * (B * C) |- (A * B) * C
        seq_assoc2 = parse_sequent("A * (B * C) |- (A * B) * C")
        self.assertIsNotNone(self.prover.prove(seq_assoc2))

    def test_relative_clause(self):
        # Object relative clause: n, (n \ n) / (s / np), np, (np \ s) / np |- n
        seq = parse_sequent(r"n, (n \ n) / (s / np), np, (np \ s) / np |- n")
        proof = self.prover.prove(seq)
        self.assertIsNotNone(proof)

    def test_substructural_rejections(self):
        # Exchange failure: A, B |- B * A
        self.assertIsNone(self.prover.prove(parse_sequent("A, B |- B * A")))
        # Exchange failure in application: np \ s, np |- s
        self.assertIsNone(self.prover.prove(parse_sequent(r"np \ s, np |- s")))

        # Weakening failure: A, B |- A
        self.assertIsNone(self.prover.prove(parse_sequent("A, B |- A")))

        # Contraction failure: A |- A * A
        self.assertIsNone(self.prover.prove(parse_sequent("A |- A * A")))


class TestNonAssociativeTrees(unittest.TestCase):
    """Test Non-Associative bracketed tree antecedents for NL."""

    def test_tree_antecedent_flattening(self):
        a = Atom("A")
        b = Atom("B")
        c = Atom("C")
        # (A, (B, C))
        tree = TreeAntecedent(a, TreeAntecedent(b, c))
        self.assertEqual(str(tree), "(A, (B, C))")
        self.assertEqual(tree.leaves(), [a, b, c])

        # ((A, B), C)
        tree2 = TreeAntecedent(TreeAntecedent(a, b), c)
        self.assertEqual(str(tree2), "((A, B), C)")
        self.assertEqual(tree2.leaves(), [a, b, c])

        seq = TreeSequent(tree, Product(a, Product(b, c)))
        self.assertEqual(str(seq), "(A, (B, C)) |- A * (B * C)")


class TestCategorialGrammar(unittest.TestCase):
    """Test Lexicon and natural language sentence parsing."""

    def setUp(self):
        self.lex = Lexicon.standard_english()

    def test_valid_sentences(self):
        # "Alice solved the problem"
        derivs = self.lex.parse_sentence("Alice solved the problem", target="s")
        self.assertGreater(len(derivs), 0)

        # "Alice solved the hard problem"
        derivs2 = self.lex.parse_sentence("Alice solved the hard problem", target="s")
        self.assertGreater(len(derivs2), 0)

        # "John gave Mary the book"
        derivs3 = self.lex.parse_sentence("John gave Mary the book", target="s")
        self.assertGreater(len(derivs3), 0)

    def test_ungrammatical_rejection(self):
        # "Mary John likes" (incorrect word order for SVO English)
        derivs = self.lex.parse_sentence("Mary John likes", target="s")
        self.assertEqual(len(derivs), 0)

        # "Alice solved" (transitive verb lacking required direct object)
        derivs2 = self.lex.parse_sentence("Alice solved", target="s")
        self.assertEqual(len(derivs2), 0)


class TestCountermodels(unittest.TestCase):
    """Test countermodel diagnostics and language models on unprovable sequents."""

    def test_valid_sequent_returns_none(self):
        seq = parse_sequent(r"np, np \ s |- s")
        cm = find_countermodel(seq)
        self.assertIsNone(cm)

    def test_empty_antecedent(self):
        seq = parse_sequent("|- s")
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertEqual(cm.violation_type, "EmptyAntecedent")

    def test_count_invariant_mismatch(self):
        seq = parse_sequent("A |- B")
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertEqual(cm.violation_type, "CountInvariantViolation")

    def test_weakening_violation(self):
        seq = parse_sequent("A, B |- A")
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertEqual(cm.violation_type, "WeakeningViolation")

    def test_contraction_violation(self):
        seq = parse_sequent("A |- A * A")
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertEqual(cm.violation_type, "ContractionViolation")

    def test_exchange_violation_and_monoid_counterexample(self):
        seq = parse_sequent("A, B |- B * A")
        cm = find_countermodel(seq)
        self.assertIsNotNone(cm)
        self.assertEqual(cm.violation_type, "ExchangeViolation")
        self.assertIsNotNone(cm.counterexample_word)
        self.assertEqual(cm.counterexample_word, "[A][B]")


if __name__ == "__main__":
    unittest.main()
