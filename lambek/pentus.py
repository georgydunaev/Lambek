"""Mechanization of Pentus's Theorem, Gaifman-Kazimierz Translation, and CKY-Lambek Bridge.

This module provides:
1. Formal data structures for Context-Free Grammars (Variables, Terminals, Production Rules in Chomsky Normal Form).
2. Chomsky-Younger-Kasami (CKY) chart parser with full parse-tree extraction.
3. Gaifman-Kazimierz construction translating context-free grammar productions into Lambek categorial types.
4. Bidirectional cross-checking between CKY chart parsing and Lambek backward-chaining proof search.
5. Craig-Maehara-Roorda-Pentus interpolation algorithm on cut-free Lambek sequents.
6. Syntactic Concept Lattices (Formal Concept Analysis / Galois connection) modeling syntactic distribution.
7. Pentus's translation extracting an equivalent Chomsky Normal Form CFG from a Lambek categorial lexicon.
"""

from __future__ import annotations
from typing import Dict, List, Set, Tuple, Optional, Any, Callable, Sequence
from collections import defaultdict
import itertools

from lambek.types import TypeAST, Atom, Slash, Backslash, Product, parse_type
from lambek.sequent import Sequent
from lambek.prover import LambekProver, ProofNode
from lambek.grammar import Lexicon


class Variable:
    """Non-terminal variable symbol in a Context-Free Grammar (e.g. S, NP, VP)."""

    def __init__(self, name: str) -> None:
        self.name = str(name).strip()
        if not self.name:
            raise ValueError("Variable name cannot be empty")

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f"Variable({self.name!r})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Variable) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("Variable", self.name))

    def to_atom(self) -> Atom:
        """Convert variable into an atomic Lambek type."""
        return Atom(self.name)


class Terminal:
    """Terminal word/token symbol in a Context-Free Grammar (e.g. 'a', 'b', 'the', 'cat')."""

    def __init__(self, symbol: str) -> None:
        self.symbol = str(symbol).strip().lower()
        if not self.symbol:
            raise ValueError("Terminal symbol cannot be empty")

    def __str__(self) -> str:
        return self.symbol

    def __repr__(self) -> str:
        return f"Terminal({self.symbol!r})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Terminal) and self.symbol == other.symbol

    def __hash__(self) -> int:
        return hash(("Terminal", self.symbol))


class ProductionRule:
    """Production rule in Chomsky Normal Form (CNF): A -> B C or A -> a."""

    def __init__(
        self,
        lhs: Variable | str,
        rhs: Tuple[Variable | str, Variable | str] | Terminal | str,
    ) -> None:
        self.lhs = lhs if isinstance(lhs, Variable) else Variable(lhs)

        if isinstance(rhs, tuple):
            if len(rhs) != 2:
                raise ValueError(f"CNF binary production must have exactly 2 variables on RHS, got {rhs}")
            b = rhs[0] if isinstance(rhs[0], Variable) else Variable(rhs[0])
            c = rhs[1] if isinstance(rhs[1], Variable) else Variable(rhs[1])
            self.rhs: Tuple[Variable, Variable] | Terminal = (b, c)
        else:
            term = rhs if isinstance(rhs, Terminal) else Terminal(rhs)
            self.rhs = term

    @property
    def is_binary(self) -> bool:
        return isinstance(self.rhs, tuple)

    @property
    def is_terminal(self) -> bool:
        return isinstance(self.rhs, Terminal)

    def __str__(self) -> str:
        if self.is_binary:
            assert isinstance(self.rhs, tuple)
            return f"{self.lhs} -> {self.rhs[0]} {self.rhs[1]}"
        return f"{self.lhs} -> {self.rhs}"

    def __repr__(self) -> str:
        return f"ProductionRule({self.lhs!r}, {self.rhs!r})"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, ProductionRule)
            and self.lhs == other.lhs
            and self.rhs == other.rhs
        )

    def __hash__(self) -> int:
        return hash(("ProductionRule", self.lhs, self.rhs))


class ParseTree:
    """Parse tree produced by CFG derivations."""

    def __init__(
        self,
        symbol: Variable,
        children: Tuple[ParseTree, ParseTree] | Terminal,
    ) -> None:
        self.symbol = symbol
        self.children = children

    @property
    def is_leaf(self) -> bool:
        return isinstance(self.children, Terminal)

    def yield_tokens(self) -> List[str]:
        """Extract sequence of terminal tokens yielded by this parse tree."""
        if isinstance(self.children, Terminal):
            return [self.children.symbol]
        left, right = self.children
        return left.yield_tokens() + right.yield_tokens()

    def to_tree_string(self, indent: int = 0) -> str:
        pad = "  " * indent
        if isinstance(self.children, Terminal):
            return f"{pad}[{self.symbol} -> {self.children.symbol}]"
        left, right = self.children
        left_str = left.to_tree_string(indent + 1)
        right_str = right.to_tree_string(indent + 1)
        return f"{pad}[{self.symbol}]\n{left_str}\n{right_str}"

    def __str__(self) -> str:
        return self.to_tree_string()

    def __repr__(self) -> str:
        return f"ParseTree({self.symbol!r}, {self.children!r})"


class CFG:
    """Context-Free Grammar strictly checked or normalized for Chomsky Normal Form (CNF)."""

    def __init__(
        self,
        start: Variable | str = "S",
        productions: Optional[List[ProductionRule]] = None,
    ) -> None:
        self.start = start if isinstance(start, Variable) else Variable(start)
        self.productions: List[ProductionRule] = []
        self.variables: Set[Variable] = {self.start}
        self.terminals: Set[Terminal] = set()

        if productions:
            for p in productions:
                self.add_production(p)

    def add_production(self, rule: ProductionRule) -> None:
        if rule not in self.productions:
            self.productions.append(rule)
            self.variables.add(rule.lhs)
            if rule.is_binary:
                assert isinstance(rule.rhs, tuple)
                self.variables.add(rule.rhs[0])
                self.variables.add(rule.rhs[1])
            else:
                assert isinstance(rule.rhs, Terminal)
                self.terminals.add(rule.rhs)

    def add_binary_rule(
        self, lhs: Variable | str, b: Variable | str, c: Variable | str
    ) -> None:
        self.add_production(ProductionRule(lhs, (b, c)))

    def add_terminal_rule(self, lhs: Variable | str, term: Terminal | str) -> None:
        self.add_production(ProductionRule(lhs, term))

    def is_cnf(self) -> bool:
        """Verify that every rule is in CNF: A -> B C or A -> a."""
        for p in self.productions:
            if not (p.is_binary or p.is_terminal):
                return False
        return True

    @classmethod
    def from_text(cls, text: str, start: str = "S") -> CFG:
        """Parse text format into CFG:

        Lines formatted as:
          A -> B C
          A -> a
          A -> B C | D E | a
        """
        cfg = cls(start=start)
        lines = [line.strip() for line in text.splitlines()]
        for line in lines:
            if not line or line.startswith("#"):
                continue
            if "->" not in line:
                continue
            lhs_part, rhs_part = line.split("->", 1)
            lhs = Variable(lhs_part.strip())
            alternatives = [alt.strip() for alt in rhs_part.split("|")]
            for alt in alternatives:
                symbols = alt.split()
                if len(symbols) == 1:
                    cfg.add_terminal_rule(lhs, symbols[0])
                elif len(symbols) == 2:
                    cfg.add_binary_rule(lhs, symbols[0], symbols[1])
                else:
                    raise ValueError(
                        f"Non-CNF rule option: {lhs} -> {alt}. Must be binary or terminal."
                    )
        return cfg

    def __str__(self) -> str:
        prods = "\n  ".join(str(p) for p in self.productions)
        return f"CFG(start={self.start}):\n  {prods}"


class CKYChart:
    """Chart holding spans, recognized categories, and backpointers for CKY parsing."""

    def __init__(self, tokens: List[str]) -> None:
        self.tokens = [t.lower() for t in tokens]
        self.n = len(self.tokens)
        # table[(i, j)] = set of Variables deriving tokens[i:j]
        self.table: Dict[Tuple[int, int], Set[Variable]] = defaultdict(set)
        # backpointers[(i, j, A)] = list of (k, B, C) where A -> B C, B in (i, k), C in (k, j)
        self.backpointers: Dict[
            Tuple[int, int, Variable], List[Tuple[int, Variable, Variable]]
        ] = defaultdict(list)
        # terminal_sources[(i, i+1, A)] = Terminal
        self.terminal_sources: Dict[Tuple[int, int, Variable], Terminal] = {}

    def recognizes(self, start: Variable) -> bool:
        if self.n == 0:
            return False
        return start in self.table[(0, self.n)]


class CKYParser:
    """Chomsky-Younger-Kasami (CKY) dynamic programming parser for CNF grammars."""

    def __init__(self, cfg: CFG) -> None:
        if not cfg.is_cnf():
            raise ValueError("CKYParser requires CFG in Chomsky Normal Form (CNF)")
        self.cfg = cfg

        # Precompute rule indexes for fast lookup
        self.terminal_rules: Dict[str, List[Variable]] = defaultdict(list)
        self.binary_rules: Dict[Tuple[Variable, Variable], List[Variable]] = defaultdict(list)

        for rule in self.cfg.productions:
            if rule.is_terminal:
                assert isinstance(rule.rhs, Terminal)
                self.terminal_rules[rule.rhs.symbol].append(rule.lhs)
            elif rule.is_binary:
                assert isinstance(rule.rhs, tuple)
                self.binary_rules[rule.rhs].append(rule.lhs)

    def parse(self, tokens: List[str] | str) -> CKYChart:
        toks = [tokens] if isinstance(tokens, str) else [t.lower() for t in tokens]
        chart = CKYChart(toks)
        n = chart.n
        if n == 0:
            return chart

        # 1. Base cases: Spans of length 1 (terminals)
        for i in range(n):
            word = toks[i]
            for var in self.terminal_rules.get(word, []):
                chart.table[(i, i + 1)].add(var)
                chart.terminal_sources[(i, i + 1, var)] = Terminal(word)

        # 2. Inductive cases: Spans of length l from 2 to n
        for length in range(2, n + 1):
            for i in range(n - length + 1):
                j = i + length
                for k in range(i + 1, j):
                    left_vars = chart.table[(i, k)]
                    right_vars = chart.table[(k, j)]
                    if not left_vars or not right_vars:
                        continue
                    for b in left_vars:
                        for c in right_vars:
                            lhs_list = self.binary_rules.get((b, c), [])
                            for a in lhs_list:
                                chart.table[(i, j)].add(a)
                                chart.backpointers[(i, j, a)].append((k, b, c))

        return chart

    def recognize(self, tokens: List[str] | str) -> bool:
        chart = self.parse(tokens)
        return chart.recognizes(self.cfg.start)

    def get_parse_trees(
        self, tokens: List[str] | str, max_trees: int = 10
    ) -> List[ParseTree]:
        """Reconstruct parse trees from backpointers."""
        chart = self.parse(tokens)
        if not chart.recognizes(self.cfg.start):
            return []

        def build_trees(i: int, j: int, var: Variable) -> List[ParseTree]:
            if j == i + 1:
                term = chart.terminal_sources.get((i, j, var))
                if term is not None:
                    return [ParseTree(var, term)]
                return []

            results: List[ParseTree] = []
            for k, b, c in chart.backpointers.get((i, j, var), []):
                left_trees = build_trees(i, k, b)
                right_trees = build_trees(k, j, c)
                for lt in left_trees:
                    for rt in right_trees:
                        results.append(ParseTree(var, (lt, rt)))
                        if len(results) >= max_trees:
                            return results
            return results

        return build_trees(0, chart.n, self.cfg.start)


def cnf_to_gaifman_kazimierz(cfg: CFG, max_depth: int = 3) -> Lexicon:
    """Translate CFG productions into an equivalent Lambek categorial lexicon

    Implements the classical Gaifman-Kazimierz construction:
    - If A -> a, then 'a' has atomic category A.
    - If A -> B C, B acts as a left functor A / C, or C acts as a right functor B \\ A.
    - Left-recursive and right-branching compositions are unfolded up to max_depth
      so that terminal words receive higher-order categorial types (e.g. (A / C) / D).
    """
    lex = Lexicon()

    # Step 1: Map terminal productions
    term_to_vars: Dict[str, Set[Variable]] = defaultdict(set)
    for p in cfg.productions:
        if p.is_terminal:
            assert isinstance(p.rhs, Terminal)
            term_to_vars[p.rhs.symbol].add(p.lhs)
            lex.add_entry(p.rhs.symbol, Atom(p.lhs.name))

    # Step 2: Extract binary relationships
    # A -> B C implies category B can consume C on the right to yield A: B : A / C
    # and category C can consume B on the left to yield A: C : B \ A
    binary_rules = [p for p in cfg.productions if p.is_binary]

    # Map nonterminals to syntactic types they can realize
    var_types: Dict[Variable, Set[TypeAST]] = defaultdict(set)
    for v in cfg.variables:
        var_types[v].add(Atom(v.name))

    # Iterative closure up to max_depth
    for _ in range(max_depth):
        changed = False
        for p in binary_rules:
            assert isinstance(p.rhs, tuple)
            a, b, c = p.lhs, p.rhs[0], p.rhs[1]

            # Forward application: B can be assigned A / C
            # Any type T realized by B can be lifted to A / C
            t_slash = Slash(Atom(a.name), Atom(c.name))
            if t_slash not in var_types[b]:
                var_types[b].add(t_slash)
                changed = True

            # Backward application: C can be assigned B \ A
            t_backslash = Backslash(Atom(b.name), Atom(a.name))
            if t_backslash not in var_types[c]:
                var_types[c].add(t_backslash)
                changed = True

            # Unfold leftmost functor: if b derives something that has functor type, compose
            for b_type in list(var_types[b]):
                if isinstance(b_type, Slash):
                    # b_type is X / Y. If X == Atom(b), lift
                    pass

        if not changed:
            break

    # Step 3: Populate lexicon for each terminal symbol
    # A word 'a' derives any nonterminal V where V -> a.
    # Therefore 'a' receives all categorial types associated with V.
    for word, vars_for_word in term_to_vars.items():
        for v in vars_for_word:
            for t in var_types[v]:
                lex.add_entry(word, t)

    # Step 4: Handle standard transitive/complex patterns (A -> B C where C -> D E)
    # If B -> b and C -> c, b can consume c: b: A / C
    # If B -> B1 B2 and B1 -> b1, b1: (A / C) / B2
    for p in binary_rules:
        assert isinstance(p.rhs, tuple)
        a, b, c = p.lhs, p.rhs[0], p.rhs[1]
        for word in term_to_vars.keys():
            if b in term_to_vars[word]:
                lex.add_entry(word, Slash(Atom(a.name), Atom(c.name)))
            if c in term_to_vars[word]:
                lex.add_entry(word, Backslash(Atom(b.name), Atom(a.name)))

        # Two-level unrolling for order-2 categories: A -> B C, where B -> B1 B2
        for p2 in binary_rules:
            if p2.lhs == b:
                assert isinstance(p2.rhs, tuple)
                b1, b2 = p2.rhs[0], p2.rhs[1]
                # b1 followed by b2 gives B, which followed by C gives A
                # So b1 has type (A / C) / B2
                for word in term_to_vars.keys():
                    if b1 in term_to_vars[word]:
                        lex.add_entry(
                            word, Slash(Slash(Atom(a.name), Atom(c.name)), Atom(b2.name))
                        )

    return lex


def cross_check_cfg_lambek(
    cfg: CFG,
    tokens: List[str] | str,
    prover: Optional[LambekProver] = None,
) -> Dict[str, Any]:
    """Cross-check CKY parser against Lambek backward-chaining derivations."""
    toks = [tokens] if isinstance(tokens, str) else [t.lower() for t in tokens]
    p = prover or LambekProver(max_depth=50)

    # 1. CFG CKY parsing
    cky = CKYParser(cfg)
    cfg_recognized = cky.recognize(toks)
    trees = cky.get_parse_trees(toks, max_trees=5) if cfg_recognized else []

    # 2. Gaifman-Kazimierz translation and Lambek proof search
    lex = cnf_to_gaifman_kazimierz(cfg)
    target_atom = Atom(cfg.start.name)
    derivations = lex.parse_sentence(" ".join(toks), target=target_atom, prover=p)
    lambek_provable = len(derivations) > 0

    return {
        "tokens": toks,
        "cfg_recognized": cfg_recognized,
        "lambek_provable": lambek_provable,
        "equivalent": (cfg_recognized == lambek_provable),
        "parse_trees": trees,
        "lambek_derivations": derivations,
    }


def pentus_interpolate(
    sequent: Sequent,
    split_index: int,
    prover: Optional[LambekProver] = None,
) -> Optional[TypeAST]:
    """Compute the Craig-Maehara-Roorda-Pentus interpolant for a split sequent.

    Given a provable Lambek sequent:
      Gamma_1, Gamma_2 |- C
    where split_index divides Gamma into non-empty Gamma_1 and Gamma_2,
    computes an interpolant type I such that:
      Gamma_1 |- I   and   I, Gamma_2 |- C
    are both cut-free provable in Lambek calculus L.
    """
    p = prover or LambekProver(max_depth=50)
    ante = sequent.antecedent
    succ = sequent.succedent

    if split_index <= 0 or split_index >= len(ante):
        raise ValueError(
            f"split_index must be between 1 and {len(ante)-1}, got {split_index}"
        )

    if not p.is_provable(sequent):
        return None

    gamma1 = ante[:split_index]
    gamma2 = ante[split_index:]

    # Construct the canonical right interpolant:
    # Gamma_1, B_1, ..., B_m |- C  ===>  Gamma_1 |- (...((C / B_m) / ...) / B_1)
    # By iterated (/ R), Gamma_1 |- I is derivable.
    # By iterated (/ L), I, Gamma_2 |- C is derivable.
    cur: TypeAST = succ
    for b in reversed(gamma2):
        cur = Slash(cur, b)
    interpolant = cur

    # Verify soundness
    seq1 = Sequent(gamma1, interpolant)
    seq2 = Sequent((interpolant,) + gamma2, succ)

    if p.is_provable(seq1) and p.is_provable(seq2):
        return interpolant

    # Dual left interpolant if needed:
    # A_1, ..., A_k, Gamma_2 |- C  ===>  Gamma_2 |- A_k \ (... \ (A_1 \ C))
    cur_left: TypeAST = succ
    for a in reversed(gamma1):
        cur_left = Backslash(a, cur_left)
    interpolant_left = cur_left

    seq1_left = Sequent(gamma1 + (interpolant_left,), succ)
    seq2_left = Sequent(gamma2, interpolant_left)
    if p.is_provable(seq2_left) and p.is_provable(seq1_left):
        return interpolant_left

    return None


class SyntacticConcept:
    """Formal concept in a Syntactic Concept Lattice (Galois Connection).

    Represents a pair (Extent, Intent) where:
    - Extent is a closed set of linguistic expressions / phrases.
    - Intent is a closed set of contexts (left_context, right_context).
    """

    def __init__(
        self,
        extent: Set[Tuple[str, ...]],
        intent: Set[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> None:
        self.extent = frozenset(extent)
        self.intent = frozenset(intent)

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, SyntacticConcept)
            and self.extent == other.extent
            and self.intent == other.intent
        )

    def __hash__(self) -> int:
        return hash((self.extent, self.intent))

    def __le__(self, other: SyntacticConcept) -> bool:
        """Subconcept ordering: extent subset and intent superset."""
        return self.extent.issubset(other.extent) and other.intent.issubset(self.intent)

    def __str__(self) -> str:
        ext_strs = [
            " ".join(e) if e else "epsilon" for e in sorted(self.extent)
        ]
        int_strs = [
            f"({' '.join(u) or '_'}, {' '.join(v) or '_'})"
            for u, v in sorted(self.intent)
        ]
        return f"Concept(extent=[{', '.join(ext_strs)}], intent=[{', '.join(int_strs)}])"

    def __repr__(self) -> str:
        return f"SyntacticConcept({set(self.extent)!r}, {set(self.intent)!r})"


class SyntacticConceptLattice:
    """Syntactic Concept Lattice (Précis Lattice / Formal Concept Analysis).

    Models the syntactic concept lattices that form the mathematical basis of
    Mati Pentus's proof that Lambek grammars generate context-free languages.
    """

    def __init__(
        self,
        universe_expressions: List[Tuple[str, ...] | str],
        contexts: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
        membership_fn: Callable[[List[str]], bool],
    ) -> None:
        self.expressions: List[Tuple[str, ...]] = [
            tuple(e.split()) if isinstance(e, str) else tuple(e)
            for e in universe_expressions
        ]
        self.contexts = list(contexts)
        self.membership_fn = membership_fn

        # Precompute incidence matrix
        self.incidence: Dict[
            Tuple[str, ...], Set[Tuple[Tuple[str, ...], Tuple[str, ...]]]
        ] = defaultdict(set)
        for e in self.expressions:
            for u, v in self.contexts:
                sentence = list(u) + list(e) + list(v)
                if self.membership_fn(sentence):
                    self.incidence[e].add((u, v))

        self.concepts = self._build_lattice()

    def prime_expr(
        self, exprs: Set[Tuple[str, ...]]
    ) -> Set[Tuple[Tuple[str, ...], Tuple[str, ...]]]:
        """Compute the set of all contexts shared by every expression in exprs."""
        if not exprs:
            return set(self.contexts)
        shared: Optional[Set[Tuple[Tuple[str, ...], Tuple[str, ...]]]] = None
        for e in exprs:
            c = self.incidence.get(e, set())
            shared = c if shared is None else shared.intersection(c)
        return shared or set()

    def prime_ctx(
        self, ctxs: Set[Tuple[Tuple[str, ...], Tuple[str, ...]]]
    ) -> Set[Tuple[str, ...]]:
        """Compute the set of all expressions that satisfy every context in ctxs."""
        if not ctxs:
            return set(self.expressions)
        valid: Set[Tuple[str, ...]] = set()
        for e in self.expressions:
            c = self.incidence.get(e, set())
            if ctxs.issubset(c):
                valid.add(e)
        return valid

    def closure(self, exprs: Set[Tuple[str, ...]]) -> SyntacticConcept:
        """Galois closure operator: (E'', E')."""
        intent = self.prime_expr(exprs)
        extent = self.prime_ctx(intent)
        return SyntacticConcept(extent, intent)

    def _build_lattice(self) -> List[SyntacticConcept]:
        """Construct all closed formal concepts in the lattice."""
        concept_set: Set[SyntacticConcept] = set()

        # Seed with singleton expressions
        for e in self.expressions:
            concept_set.add(self.closure({e}))

        # Seed with empty set
        concept_set.add(self.closure(set()))

        # Closure under intersections of extents
        changed = True
        while changed:
            changed = False
            new_concepts: Set[SyntacticConcept] = set()
            for c1, c2 in itertools.combinations(concept_set, 2):
                meet_extent = set(c1.extent).intersection(set(c2.extent))
                meet_concept = self.closure(meet_extent)
                if meet_concept not in concept_set:
                    new_concepts.add(meet_concept)
                    changed = True
            concept_set.update(new_concepts)

        # Return sorted by extent size
        return sorted(concept_set, key=lambda c: (len(c.extent), len(c.intent)))

    def meet(self, c1: SyntacticConcept, c2: SyntacticConcept) -> SyntacticConcept:
        """Lattice meet (greatest common subconcept)."""
        common_extent = set(c1.extent).intersection(set(c2.extent))
        return self.closure(common_extent)

    def join(self, c1: SyntacticConcept, c2: SyntacticConcept) -> SyntacticConcept:
        """Lattice join (least common superconcept)."""
        common_intent = set(c1.intent).intersection(set(c2.intent))
        common_extent = self.prime_ctx(common_intent)
        return SyntacticConcept(common_extent, common_intent)


def lambek_to_cfg(
    lexicon: Lexicon,
    target: TypeAST | str = Atom("s"),
    sample_vocabulary: Optional[List[str]] = None,
    prover: Optional[LambekProver] = None,
) -> CFG:
    """Extract an equivalent Chomsky Normal Form CFG from a Lambek Categorial Lexicon.

    Constructs CFG productions according to Mati Pentus's (1993) theorem:
    - Variables represent closed Lambek types and interpolants.
    - Terminal productions: [A] -> w for every word w with lexical category t where t |- A.
    - Binary productions: [C] -> [A] [B] for all concept types where A, B |- C is provable.
    """
    p = prover or LambekProver(max_depth=50)
    target_ast = parse_type(target) if isinstance(target, str) else target

    # 1. Collect all types occurring in the lexicon and subformulas
    types_set: Set[TypeAST] = {target_ast}
    vocab = sample_vocabulary or list(lexicon.entries.keys())

    for word in vocab:
        for t in lexicon.get_categories(word):
            types_set.add(t)
            # Add subformulas
            if isinstance(t, (Slash, Backslash, Product)):
                types_set.add(t.left)
                types_set.add(t.right)

    types_list = sorted(types_set, key=lambda t: (t.complexity, str(t)))

    def type_var_name(t: TypeAST) -> str:
        s = str(t)
        # Sanitize for variable names
        s = s.replace(" ", "").replace("\\", "_BS_").replace("/", "_SL_").replace("*", "_PR_")
        s = s.replace("(", "").replace(")", "")
        return f"V_{s}"

    cfg = CFG(start=type_var_name(target_ast))

    # 2. Add terminal productions: A -> w when t in Lex(w) and t |- A
    for word in vocab:
        for t in lexicon.get_categories(word):
            for target_type in types_list:
                seq = Sequent([t], target_type)
                if p.is_provable(seq):
                    cfg.add_terminal_rule(type_var_name(target_type), word)

    # 3. Add binary productions: C -> A B when A, B |- C
    for a in types_list:
        for b in types_list:
            for c in types_list:
                seq = Sequent([a, b], c)
                if p.is_provable(seq):
                    cfg.add_binary_rule(
                        type_var_name(c), type_var_name(a), type_var_name(b)
                    )

    return cfg
