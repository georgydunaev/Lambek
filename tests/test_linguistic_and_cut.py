"""Unit tests for Constructive Cut Admissibility, Linguistic Derivations, and CLI Tools.

Verifies:
- Constructive cut elimination / cut admissibility across all connectives (\\, /, •).
- Linguistic derivations for complex coordination (Right Node Raising) and relative clauses.
- LaTeX and ASCII deduction line generation.
- CLI tool tools/lambek_prover.py execution.
- Coq verification of constructive cut admissibility in 01.v and src/Lambek.v.
"""

from __future__ import annotations
import os
import sys
import unittest
import subprocess

from lambek.types import Atom, Backslash, Slash, Product, parse_type
from lambek.sequent import Sequent, parse_sequent
from lambek.prover import LambekProver, ProofNode, prove_sequent
from lambek.cut_elimination import admit_cut, CutProofNode, eliminate_all_cuts
from lambek.grammar import Lexicon, parse_sentence
from tools.lambek_prover import proof_to_latex, proof_to_deduction_lines


class TestConstructiveCutAdmissibility(unittest.TestCase):
    """Test suite for constructive cut admissibility and cut elimination."""

    def setUp(self) -> None:
        self.prover = LambekProver()

    def test_cut_admissibility_identity_left(self) -> None:
        p1 = prove_sequent("np |- np", self.prover)
        p2 = prove_sequent("np, np \\ s |- s", self.prover)
        self.assertIsNotNone(p1)
        self.assertIsNotNone(p2)
        res = admit_cut(p1, p2, cut_index=0, prover=self.prover)
        self.assertEqual(res.sequent, parse_sequent("np, np \\ s |- s"))
        self.assertNotEqual(res.rule, "Cut")

    def test_cut_admissibility_identity_right(self) -> None:
        p1 = prove_sequent("np, (np \\ s) / np, np |- s", self.prover)
        p2 = prove_sequent("s |- s", self.prover)
        self.assertIsNotNone(p1)
        self.assertIsNotNone(p2)
        res = admit_cut(p1, p2, cut_index=0, prover=self.prover)
        self.assertEqual(res.sequent, parse_sequent("np, (np \\ s) / np, np |- s"))
        self.assertNotEqual(res.rule, "Cut")

    def test_cut_admissibility_slash_composition(self) -> None:
        # Premise 1: np, (np \ s) / np |- s / np
        # Premise 2: s / np, np |- s
        # Cut formula: s / np at index 0 of premise 2
        p1 = prove_sequent("np, (np \\ s) / np |- s / np", self.prover)
        p2 = prove_sequent("s / np, np |- s", self.prover)
        self.assertIsNotNone(p1)
        self.assertIsNotNone(p2)
        res = admit_cut(p1, p2, cut_index=0, prover=self.prover)
        self.assertEqual(res.sequent, parse_sequent("np, (np \\ s) / np, np |- s"))
        self.assertNotEqual(res.rule, "Cut")

    def test_cut_admissibility_backslash_composition(self) -> None:
        # Premise 1: (np \ s) / np, np |- np \ s
        # Premise 2: np, np \ s |- s
        p1 = prove_sequent("(np \\ s) / np, np |- np \\ s", self.prover)
        p2 = prove_sequent("np, np \\ s |- s", self.prover)
        self.assertIsNotNone(p1)
        self.assertIsNotNone(p2)
        res = admit_cut(p1, p2, cut_index=1, prover=self.prover)
        self.assertEqual(res.sequent, parse_sequent("np, (np \\ s) / np, np |- s"))
        self.assertNotEqual(res.rule, "Cut")

    def test_cut_admissibility_product(self) -> None:
        # Premise 1: a, b |- a * b
        # Premise 2: a * b, (a * b) \ c |- c
        p1 = prove_sequent("a, b |- a * b", self.prover)
        p2 = prove_sequent("a * b, (a * b) \\ c |- c", self.prover)
        self.assertIsNotNone(p1)
        self.assertIsNotNone(p2)
        res = admit_cut(p1, p2, cut_index=0, prover=self.prover)
        self.assertEqual(res.sequent, parse_sequent("a, b, (a * b) \\ c |- c"))
        self.assertNotEqual(res.rule, "Cut")

    def test_cut_proof_node_elimination(self) -> None:
        p1 = prove_sequent("np |- np", self.prover)
        p2 = prove_sequent("np, np \\ s |- s", self.prover)
        assert p1 is not None and p2 is not None
        cut_node = CutProofNode(Atom("np"), 0, p1, p2)
        self.assertEqual(cut_node.rule, "Cut")
        eliminated = eliminate_all_cuts(cut_node, prover=self.prover)
        self.assertNotEqual(eliminated.rule, "Cut")
        self.assertEqual(eliminated.sequent, parse_sequent("np, np \\ s |- s"))


class TestLinguisticDerivations(unittest.TestCase):
    """Test suite for complex natural language syntax phenomena."""

    def setUp(self) -> None:
        self.lexicon = Lexicon.standard_english()

    def test_subject_relative_clause(self) -> None:
        # "book which fell" derives category n
        derivations = parse_sentence("book which fell", lexicon=self.lexicon, target="n")
        self.assertGreaterEqual(len(derivations), 1)
        d = derivations[0]
        self.assertEqual(d.target, Atom("n"))
        self.assertEqual(d.words, ["book", "which", "fell"])

    def test_object_relative_clause(self) -> None:
        # "book which John read" derives category n
        derivations = parse_sentence("book which john read", lexicon=self.lexicon, target="n")
        self.assertGreaterEqual(len(derivations), 1)
        d = derivations[0]
        self.assertEqual(d.target, Atom("n"))
        self.assertEqual(d.words, ["book", "which", "john", "read"])

    def test_right_node_raising_coordination(self) -> None:
        # "John likes and Mary loves Alice" derives category s
        derivations = parse_sentence("john likes and mary loves alice", lexicon=self.lexicon, target="s")
        self.assertGreaterEqual(len(derivations), 1)
        d = derivations[0]
        self.assertEqual(d.target, Atom("s"))
        self.assertEqual(d.words, ["john", "likes", "and", "mary", "loves", "alice"])

    def test_transitive_verb_coordination(self) -> None:
        # "John likes and loves Mary" derives category s
        derivations = parse_sentence("john likes and loves mary", lexicon=self.lexicon, target="s")
        self.assertGreaterEqual(len(derivations), 1)
        d = derivations[0]
        self.assertEqual(d.target, Atom("s"))

    def test_noun_phrase_coordination(self) -> None:
        # "John and Mary slept" derives category s
        derivations = parse_sentence("john and mary slept", lexicon=self.lexicon, target="s")
        self.assertGreaterEqual(len(derivations), 1)
        d = derivations[0]
        self.assertEqual(d.target, Atom("s"))

    def test_verb_phrase_coordination(self) -> None:
        # "John walked and smiled" derives category s
        derivations = parse_sentence("john walked and smiled", lexicon=self.lexicon, target="s")
        self.assertGreaterEqual(len(derivations), 1)
        d = derivations[0]
        self.assertEqual(d.target, Atom("s"))


class TestProverVisualizerAndCLI(unittest.TestCase):
    """Test suite for deduction tree visualizers and CLI utility."""

    def test_latex_export(self) -> None:
        p = prove_sequent("np, np \\ s |- s")
        self.assertIsNotNone(p)
        tex = proof_to_latex(p)
        self.assertIn("\\begin{prooftree}", tex)
        self.assertIn("\\end{prooftree}", tex)
        self.assertIn("\\AxiomC{np \\vdash np}", tex)
        self.assertIn("\\AxiomC{s \\vdash s}", tex)

    def test_deduction_lines_format(self) -> None:
        p = prove_sequent("np, (np \\ s) / np, np |- s")
        self.assertIsNotNone(p)
        lines = proof_to_deduction_lines(p)
        joined = "\n".join(lines)
        self.assertIn("---", joined)
        self.assertIn("[/L]", joined)
        self.assertIn("[\\L]", joined)
        self.assertIn("[Ax]", joined)

    def test_cli_prove(self) -> None:
        res = subprocess.run(
            [sys.executable, "tools/lambek_prover.py", "--prove", "np, (np \\ s) / np, np |- s"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0)
        self.assertIn("PROVED", res.stdout)

    def test_cli_parse(self) -> None:
        res = subprocess.run(
            [sys.executable, "tools/lambek_prover.py", "--parse", "john likes mary"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0)
        self.assertIn("SUCCESS", res.stdout)

    def test_cli_cut(self) -> None:
        res = subprocess.run(
            [
                sys.executable,
                "tools/lambek_prover.py",
                "--cut",
                "np, (np \\ s) / np |- s / np",
                "s / np, np |- s",
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0)
        self.assertIn("Constructive Cut Admissibility Result", res.stdout)
        self.assertIn("np, (np \\ s) / np, np |- s", res.stdout)


class TestCoqFormalVerification(unittest.TestCase):
    """Test suite compiling and verifying Coq formalizations."""

    def test_01_v_loads_cleanly(self) -> None:
        res = subprocess.run(
            ["coqtop", "-batch", "-load-vernac-source", "01.v"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(
            res.returncode,
            0,
            f"01.v failed to load in coqtop:\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}",
        )

    def test_src_lambek_v_compiles(self) -> None:
        res = subprocess.run(
            ["coqc", "-Q", "src", "src", "src/Lambek.v"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(
            res.returncode,
            0,
            f"src/Lambek.v failed to compile with coqc:\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}",
        )


if __name__ == "__main__":
    unittest.main()
