"""Categorial Grammar Parser and Derivation Engine based on Lambek Calculus."""

from __future__ import annotations
import re
from typing import Dict, List, Optional, Tuple, Sequence
from lambek.types import TypeAST, Atom, Backslash, Slash, parse_type
from lambek.sequent import Sequent
from lambek.prover import LambekProver, ProofNode


class GrammarDerivation:
    """A linguistic derivation showing word-type assignments and proof tree."""

    def __init__(self, words: List[str], types: List[TypeAST], target: TypeAST, proof: ProofNode) -> None:
        self.words = words
        self.types = types
        self.target = target
        self.proof = proof

    def type_assignment_str(self) -> str:
        pairs = [f"{w}: {t}" for w, t in zip(self.words, self.types)]
        return ", ".join(pairs)

    def __str__(self) -> str:
        return f"Derivation({self.type_assignment_str()} |- {self.target})\n{self.proof}"


class Lexicon:
    """Lexicon mapping surface words to sets of Lambek syntactic types."""

    def __init__(self) -> None:
        self.entries: Dict[str, List[TypeAST]] = {}

    def add_entry(self, word: str, category: TypeAST | str) -> None:
        w = word.strip().lower()
        cat = parse_type(category) if isinstance(category, str) else category
        if w not in self.entries:
            self.entries[w] = []
        if cat not in self.entries[w]:
            self.entries[w].append(cat)

    def get_categories(self, word: str) -> List[TypeAST]:
        return self.entries.get(word.strip().lower(), [])

    @classmethod
    def standard_english(cls) -> Lexicon:
        """Create standard English linguistic lexicon."""
        lex = cls()
        # Noun phrases (proper nouns)
        for name in ("john", "mary", "alice", "bob", "georgy"):
            lex.add_entry(name, Atom("np"))

        # Common nouns
        for noun in ("cat", "dog", "mat", "problem", "theorem", "logician", "book", "sentence", "apples", "man"):
            lex.add_entry(noun, Atom("n"))

        # Determiners
        for det in ("the", "a", "an", "every", "some"):
            lex.add_entry(det, Slash(Atom("np"), Atom("n")))  # np / n

        # Adjectives
        for adj in ("small", "black", "hard", "difficult", "elegant", "interesting"):
            lex.add_entry(adj, Slash(Atom("n"), Atom("n")))  # n / n

        # Intransitive verbs: np \ s
        for iv in ("slept", "ran", "walked", "smiled", "fell"):
            lex.add_entry(iv, Backslash(Atom("np"), Atom("s")))

        # Transitive verbs: (np \ s) / np
        for tv in ("likes", "loves", "saw", "solved", "proved", "read", "chased", "wrote"):
            lex.add_entry(tv, Slash(Backslash(Atom("np"), Atom("s")), Atom("np")))

        # Ditransitive verbs: ((np \ s) / np) / np
        for dtv in ("gave", "sent", "assigned"):
            lex.add_entry(dtv, Slash(Slash(Backslash(Atom("np"), Atom("s")), Atom("np")), Atom("np")))

        # Prepositions
        for prep in ("on", "in", "with"):
            # Adnominal: (n \ n) / np
            lex.add_entry(prep, Slash(Backslash(Atom("n"), Atom("n")), Atom("np")))
            # Adverbial: ((np \ s) \ (np \ s)) / np
            lex.add_entry(
                prep,
                Slash(Backslash(Backslash(Atom("np"), Atom("s")), Backslash(Atom("np"), Atom("s"))), Atom("np")),
            )

        # Relative pronouns
        # Subject extraction: (n \ n) / (np \ s)
        for rel_subj in ("who", "which", "that"):
            lex.add_entry(
                rel_subj,
                Slash(Backslash(Atom("n"), Atom("n")), Backslash(Atom("np"), Atom("s"))),
            )
        # Object extraction: (n \ n) / (s / np)
        for rel_obj in ("whom", "which", "that"):
            lex.add_entry(
                rel_obj,
                Slash(Backslash(Atom("n"), Atom("n")), Slash(Atom("s"), Atom("np"))),
            )

        # Conjunctions (polytypic coordination)
        # Sentential coordination: (s \ s) / s
        for conj in ("and", "or", "but"):
            lex.add_entry(conj, Slash(Backslash(Atom("s"), Atom("s")), Atom("s")))

        # Noun phrase coordination: (np \ np) / np
        for conj in ("and", "or"):
            lex.add_entry(conj, Slash(Backslash(Atom("np"), Atom("np")), Atom("np")))

        # Verb phrase coordination: ((np \ s) \ (np \ s)) / (np \ s)
        vp = Backslash(Atom("np"), Atom("s"))
        for conj in ("and", "or"):
            lex.add_entry(conj, Slash(Backslash(vp, vp), vp))

        # Transitive verb coordination: (tv \ tv) / tv where tv = (np \ s) / np
        tv = Slash(Backslash(Atom("np"), Atom("s")), Atom("np"))
        for conj in ("and", "or"):
            lex.add_entry(conj, Slash(Backslash(tv, tv), tv))

        # Right Node Raising coordination: ((s / np) \ (s / np)) / (s / np)
        s_slash_np = Slash(Atom("s"), Atom("np"))
        for conj in ("and", "or"):
            lex.add_entry(conj, Slash(Backslash(s_slash_np, s_slash_np), s_slash_np))

        return lex

    def parse_sentence(
        self,
        sentence: str,
        target: TypeAST | str = Atom("s"),
        prover: Optional[LambekProver] = None,
    ) -> List[GrammarDerivation]:
        """Tokenize sentence, assign lexical categories, and search for Lambek derivations."""
        target_ast = parse_type(target) if isinstance(target, str) else target
        p = prover or LambekProver()

        tokens = [tok.lower() for tok in re.findall(r"[a-zA-Z]+", sentence)]
        if not tokens:
            return []

        # Gather lexical options
        options: List[List[TypeAST]] = []
        for tok in tokens:
            cats = self.get_categories(tok)
            if not cats:
                # Unknown word
                return []
            options.append(cats)

        # Generate cartesian product of assignments
        derivations: List[GrammarDerivation] = []

        def backtrack(idx: int, current_types: List[TypeAST]) -> None:
            if idx == len(tokens):
                seq = Sequent(current_types, target_ast)
                proof = p.prove(seq)
                if proof is not None:
                    derivations.append(GrammarDerivation(tokens, list(current_types), target_ast, proof))
                return

            for cat in options[idx]:
                current_types.append(cat)
                backtrack(idx + 1, current_types)
                current_types.pop()

        backtrack(0, [])
        return derivations


def parse_sentence(
    sentence: str,
    lexicon: Optional[Lexicon] = None,
    target: TypeAST | str = "s",
    prover: Optional[LambekProver] = None,
) -> List[GrammarDerivation]:
    """Convenience helper to parse a sentence using a Lexicon (defaults to standard English)."""
    lex = lexicon if lexicon is not None else Lexicon.standard_english()
    return lex.parse_sentence(sentence, target=target, prover=prover)

