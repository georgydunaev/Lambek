"""Unit tests for Pentus's theorem, Gaifman-Kazimierz translation, and CKY-Lambek bridge."""

import unittest
from lambek.types import Atom, Slash, Backslash, parse_type
from lambek.sequent import Sequent
from lambek.prover import LambekProver
from lambek.grammar import Lexicon
from lambek.pentus import (
    Variable,
    Terminal,
    ProductionRule,
    ParseTree,
    CFG,
    CKYParser,
    cnf_to_gaifman_kazimierz,
    cross_check_cfg_lambek,
    pentus_interpolate,
    SyntacticConcept,
    SyntacticConceptLattice,
    lambek_to_cfg,
)


class TestCFGDataStructures(unittest.TestCase):
    """Test CFG nonterminals, terminals, and production rules in CNF."""

    def test_variable_and_terminal(self):
        v = Variable("NP")
        self.assertEqual(str(v), "NP")
        self.assertEqual(v.to_atom(), Atom("NP"))

        t = Terminal("John")
        self.assertEqual(str(t), "john")
        self.assertEqual(repr(t), "Terminal('john')")

        with self.assertRaises(ValueError):
            Variable("")
        with self.assertRaises(ValueError):
            Terminal("")

    def test_production_rules(self):
        r1 = ProductionRule("S", ("NP", "VP"))
        self.assertTrue(r1.is_binary)
        self.assertFalse(r1.is_terminal)
        self.assertEqual(str(r1), "S -> NP VP")

        r2 = ProductionRule("NP", "john")
        self.assertTrue(r2.is_terminal)
        self.assertFalse(r2.is_binary)
        self.assertEqual(str(r2), "NP -> john")

        with self.assertRaises(ValueError):
            ProductionRule("S", ("A", "B", "C"))

    def test_cfg_construction_and_parsing(self):
        grammar_text = """
        S -> NP VP
        VP -> V NP | slept
        NP -> Det N | john | mary
        V -> likes
        Det -> the
        N -> cat | dog
        """
        cfg = CFG.from_text(grammar_text, start="S")
        self.assertTrue(cfg.is_cnf())
        self.assertEqual(cfg.start, Variable("S"))
        self.assertIn(Variable("NP"), cfg.variables)
        self.assertIn(Terminal("cat"), cfg.terminals)
        self.assertIn(Terminal("slept"), cfg.terminals)


class TestCKYParser(unittest.TestCase):
    """Test CKY chart parser on formal and linguistic grammars."""

    def setUp(self):
        self.grammar_text = """
        S -> NP VP
        VP -> V NP | slept
        NP -> Det N | john | mary
        V -> likes | chased
        Det -> the | a
        N -> cat | dog
        """
        self.cfg = CFG.from_text(self.grammar_text, start="S")
        self.parser = CKYParser(self.cfg)

    def test_simple_sentences(self):
        self.assertTrue(self.parser.recognize(["john", "slept"]))
        self.assertTrue(self.parser.recognize(["the", "cat", "slept"]))
        self.assertTrue(self.parser.recognize(["john", "likes", "mary"]))
        self.assertTrue(self.parser.recognize(["the", "dog", "chased", "a", "cat"]))

    def test_reject_ungrammatical(self):
        self.assertFalse(self.parser.recognize(["john"]))
        self.assertFalse(self.parser.recognize(["slept", "john"]))
        self.assertFalse(self.parser.recognize(["the", "cat", "dog"]))
        self.assertFalse(self.parser.recognize(["likes", "mary"]))
        self.assertFalse(self.parser.recognize([]))

    def test_parse_tree_extraction(self):
        trees = self.parser.get_parse_trees(["john", "likes", "mary"])
        self.assertEqual(len(trees), 1)
        tree = trees[0]
        self.assertEqual(tree.symbol, Variable("S"))
        self.assertEqual(tree.yield_tokens(), ["john", "likes", "mary"])
        tree_str = tree.to_tree_string()
        self.assertIn("[S]", tree_str)
        self.assertIn("[NP -> john]", tree_str)
        self.assertIn("[V -> likes]", tree_str)

    def test_dyck_language_grammar(self):
        # Even-length balanced bracket subset in CNF:
        # S -> A B | S S
        # A -> o, B -> c (representing '(' and ')')
        dyck_text = """
        S -> A B | S S
        A -> o
        B -> c
        """
        dyck_cfg = CFG.from_text(dyck_text, start="S")
        dyck_parser = CKYParser(dyck_cfg)

        self.assertTrue(dyck_parser.recognize(["o", "c"]))
        self.assertTrue(dyck_parser.recognize(["o", "c", "o", "c"]))
        self.assertFalse(dyck_parser.recognize(["o"]))
        self.assertFalse(dyck_parser.recognize(["c", "o"]))
        self.assertFalse(dyck_parser.recognize(["o", "o", "c"]))


class TestGaifmanKazimierzTranslation(unittest.TestCase):
    """Test translation from CFG productions into Lambek categorial types."""

    def setUp(self):
        self.grammar_text = """
        S -> NP VP
        VP -> V NP | slept
        NP -> Det N | john | mary
        V -> likes
        Det -> the
        N -> cat | dog
        """
        self.cfg = CFG.from_text(self.grammar_text, start="S")
        self.lexicon = cnf_to_gaifman_kazimierz(self.cfg)
        self.prover = LambekProver(max_depth=50)

    def test_lexical_categories_assigned(self):
        # John derives NP
        john_cats = self.lexicon.get_categories("john")
        self.assertIn(Atom("NP"), john_cats)

        # 'likes' derives V. In Gaifman-Kazimierz, V has VP / NP, and VP has S, so likes can be (S / NP) / ... or VP / NP
        likes_cats = self.lexicon.get_categories("likes")
        self.assertTrue(
            any(isinstance(c, Slash) and c.right == Atom("NP") for c in likes_cats)
        )

    def test_cross_check_grammatical_sentences(self):
        # Test john likes mary
        result = cross_check_cfg_lambek(self.cfg, ["john", "likes", "mary"], self.prover)
        self.assertTrue(result["cfg_recognized"])
        self.assertTrue(result["lambek_provable"])
        self.assertTrue(result["equivalent"])

        # Test the cat slept
        result2 = cross_check_cfg_lambek(self.cfg, ["the", "cat", "slept"], self.prover)
        self.assertTrue(result2["cfg_recognized"])
        self.assertTrue(result2["lambek_provable"])
        self.assertTrue(result2["equivalent"])

    def test_cross_check_ungrammatical_sentences(self):
        result = cross_check_cfg_lambek(self.cfg, ["cat", "the", "slept"], self.prover)
        self.assertFalse(result["cfg_recognized"])
        self.assertFalse(result["lambek_provable"])
        self.assertTrue(result["equivalent"])


class TestPentusInterpolation(unittest.TestCase):
    """Test Craig-Maehara-Roorda-Pentus interpolation on Lambek sequents."""

    def setUp(self):
        self.prover = LambekProver(max_depth=50)

    def test_transitive_sentence_interpolation(self):
        # np, (np \ s) / np, np |- s
        np = Atom("np")
        s = Atom("s")
        tv = Slash(Backslash(np, s), np)
        seq = Sequent([np, tv, np], s)

        # Split at index 1: [np] vs [tv, np]
        interp1 = pentus_interpolate(seq, split_index=1, prover=self.prover)
        self.assertIsNotNone(interp1)
        self.assertTrue(self.prover.is_provable(Sequent([np], interp1)))
        self.assertTrue(self.prover.is_provable(Sequent([interp1, tv, np], s)))

        # Split at index 2: [np, tv] vs [np]
        interp2 = pentus_interpolate(seq, split_index=2, prover=self.prover)
        self.assertIsNotNone(interp2)
        self.assertTrue(self.prover.is_provable(Sequent([np, tv], interp2)))
        self.assertTrue(self.prover.is_provable(Sequent([interp2, np], s)))

    def test_determiner_noun_interpolation(self):
        # np / n, n, np \ s |- s
        np = Atom("np")
        n = Atom("n")
        s = Atom("s")
        det = Slash(np, n)
        iv = Backslash(np, s)
        seq = Sequent([det, n, iv], s)

        # Split at index 2: [det, n] vs [iv]
        interp = pentus_interpolate(seq, split_index=2, prover=self.prover)
        self.assertIsNotNone(interp)
        self.assertTrue(self.prover.is_provable(Sequent([det, n], interp)))
        self.assertTrue(self.prover.is_provable(Sequent([interp, iv], s)))

    def test_invalid_split_index_raises(self):
        seq = Sequent([Atom("a"), Atom("b")], Atom("c"))
        with self.assertRaises(ValueError):
            pentus_interpolate(seq, split_index=0)
        with self.assertRaises(ValueError):
            pentus_interpolate(seq, split_index=2)


class TestSyntacticConceptLattice(unittest.TestCase):
    """Test syntactic concept lattices modeling language distribution."""

    def test_toy_lattice(self):
        expressions = ["john", "mary", "the cat", "slept", "ran"]
        contexts = [
            (tuple(), ("slept",)),
            (tuple(), ("ran",)),
            (("john",), tuple()),
            (("mary",), tuple()),
        ]

        def membership(words):
            s = " ".join(words)
            return s in {
                "john slept",
                "mary slept",
                "the cat slept",
                "john ran",
                "mary ran",
                "the cat ran",
            }

        lattice = SyntacticConceptLattice(expressions, contexts, membership)
        self.assertGreater(len(lattice.concepts), 0)

        # Find concept containing proper names
        john_expr = ("john",)
        matching = [c for c in lattice.concepts if john_expr in c.extent]
        self.assertGreater(len(matching), 0)

        # Check lattice meet and join
        c1 = lattice.concepts[0]
        c2 = lattice.concepts[-1]
        meet_c = lattice.meet(c1, c2)
        join_c = lattice.join(c1, c2)
        self.assertTrue(meet_c <= c1)
        self.assertTrue(c1 <= join_c)


class TestLambekToCFG(unittest.TestCase):
    """Test Pentus's translation from Lambek categorial lexicon into Chomsky Normal Form CFG."""

    def test_cfg_extraction_and_parsing(self):
        lex = Lexicon()
        np = Atom("np")
        s = Atom("s")
        n = Atom("n")
        det = Slash(np, n)
        iv = Backslash(np, s)
        tv = Slash(Backslash(np, s), np)

        lex.add_entry("john", np)
        lex.add_entry("mary", np)
        lex.add_entry("cat", n)
        lex.add_entry("the", det)
        lex.add_entry("slept", iv)
        lex.add_entry("likes", tv)

        cfg = lambek_to_cfg(lex, target=s)
        self.assertTrue(cfg.is_cnf())

        parser = CKYParser(cfg)
        self.assertTrue(parser.recognize(["john", "slept"]))
        self.assertTrue(parser.recognize(["the", "cat", "slept"]))
        self.assertFalse(parser.recognize(["cat", "the"]))
        self.assertFalse(parser.recognize(["slept"]))


if __name__ == "__main__":
    unittest.main()
