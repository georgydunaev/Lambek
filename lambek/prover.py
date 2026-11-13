"""Automated Backward-Chaining Proof Search for Lambek Sequent Calculus L and NL.

Implements Joachim Lambek's (1958) cut-free decision procedure with subformula property.
"""

from __future__ import annotations
from typing import Optional, List, Tuple
from lambek.types import TypeAST, Atom, Backslash, Slash, Product
from lambek.sequent import Sequent, TreeAntecedent, TreeSequent


class ProofNode:
    """A node in a Lambek sequent calculus derivation tree."""

    def __init__(self, rule: str, sequent: Sequent, premises: Optional[List[ProofNode]] = None) -> None:
        self.rule = rule
        self.sequent = sequent
        self.premises: List[ProofNode] = premises or []

    def __str__(self) -> str:
        return self.to_ascii_tree()

    def to_ascii_tree(self, indent: int = 0) -> str:
        prefix = "  " * indent
        lines = [f"{prefix}[{self.rule}] {self.sequent}"]
        for p in self.premises:
            lines.append(p.to_ascii_tree(indent + 1))
        return "\n".join(lines)


class LambekProver:
    """Decision procedure and proof search engine for the associative Lambek calculus (L)."""

    def __init__(self, max_depth: int = 100) -> None:
        self.max_depth = max_depth

    def prove(self, sequent: Sequent) -> Optional[ProofNode]:
        """Search for a cut-free derivation. Returns ProofNode if provable, None otherwise."""
        return self._search(sequent, depth=0)

    def is_provable(self, sequent: Sequent) -> bool:
        return self.prove(sequent) is not None

    def _search(self, seq: Sequent, depth: int) -> Optional[ProofNode]:
        if depth > self.max_depth:
            return None

        # Lambek-van Benthem count invariant filter: necessary condition
        if not seq.satisfies_count_invariant():
            return None

        ante = seq.antecedent
        succ = seq.succedent

        # Antecedents in pure Lambek calculus must be non-empty
        if len(ante) == 0:
            return None

        # 1. Axiom Rule: A |- A
        if len(ante) == 1 and ante[0] == succ:
            return ProofNode("Ax", seq, [])

        # 2. Right Introduction Rules
        # Right Division Right Introduction: (/ R)
        # Gamma, A |- B  ===>  Gamma |- B / A
        if isinstance(succ, Slash):
            prem_ante = ante + (succ.right,)
            prem_seq = Sequent(prem_ante, succ.left)
            prem_proof = self._search(prem_seq, depth + 1)
            if prem_proof is not None:
                return ProofNode("/R", seq, [prem_proof])

        # Left Division Right Introduction: (\ R)
        # A, Gamma |- B  ===>  Gamma |- A \ B
        if isinstance(succ, Backslash):
            prem_ante = (succ.left,) + ante
            prem_seq = Sequent(prem_ante, succ.right)
            prem_proof = self._search(prem_seq, depth + 1)
            if prem_proof is not None:
                return ProofNode("\\R", seq, [prem_proof])

        # Product Right Introduction: (* R)
        # Gamma |- A   Delta |- B  ===>  Gamma, Delta |- A * B
        if isinstance(succ, Product):
            for k in range(1, len(ante)):
                ante1 = ante[:k]
                ante2 = ante[k:]
                seq1 = Sequent(ante1, succ.left)
                p1 = self._search(seq1, depth + 1)
                if p1 is not None:
                    seq2 = Sequent(ante2, succ.right)
                    p2 = self._search(seq2, depth + 1)
                    if p2 is not None:
                        return ProofNode("*R", seq, [p1, p2])

        # 3. Left Introduction Rules
        for i, formula in enumerate(ante):
            # Product Left Introduction: (* L)
            # Gamma, A, B, Delta |- C  ===>  Gamma, A * B, Delta |- C
            if isinstance(formula, Product):
                new_ante = ante[:i] + (formula.left, formula.right) + ante[i + 1:]
                prem_seq = Sequent(new_ante, succ)
                p = self._search(prem_seq, depth + 1)
                if p is not None:
                    return ProofNode("*L", seq, [p])

            # Left Division Left Introduction: (\ L)
            # Delta |- A   Gamma1, B, Gamma2 |- C  ===>  Gamma1, Delta, A \ B, Gamma2 |- C
            if isinstance(formula, Backslash):
                # Delta is a non-empty slice of ante[:i] ending at i-1
                for j in range(0, i):
                    delta = ante[j:i]
                    gamma1 = ante[:j]
                    gamma2 = ante[i + 1:]
                    seq_delta = Sequent(delta, formula.left)
                    p_delta = self._search(seq_delta, depth + 1)
                    if p_delta is not None:
                        seq_main = Sequent(gamma1 + (formula.right,) + gamma2, succ)
                        p_main = self._search(seq_main, depth + 1)
                        if p_main is not None:
                            return ProofNode("\\L", seq, [p_delta, p_main])

            # Right Division Left Introduction: (/ L)
            # Delta |- A   Gamma1, B, Gamma2 |- C  ===>  Gamma1, B / A, Delta, Gamma2 |- C
            if isinstance(formula, Slash):
                # Delta is a non-empty slice of ante[i+1:] starting at i+1
                for j in range(i + 1, len(ante)):
                    delta = ante[i + 1:j + 1]
                    gamma1 = ante[:i]
                    gamma2 = ante[j + 1:]
                    seq_delta = Sequent(delta, formula.right)
                    p_delta = self._search(seq_delta, depth + 1)
                    if p_delta is not None:
                        seq_main = Sequent(gamma1 + (formula.left,) + gamma2, succ)
                        p_main = self._search(seq_main, depth + 1)
                        if p_main is not None:
                            return ProofNode("/L", seq, [p_delta, p_main])

        return None


def prove_sequent(sequent: Sequent | str, prover: Optional[LambekProver] = None) -> Optional[ProofNode]:
    """Helper function to parse and prove a sequent or string."""
    from lambek.sequent import parse_sequent
    seq = parse_sequent(sequent) if isinstance(sequent, str) else sequent
    p = prover if prover is not None else LambekProver()
    return p.prove(seq)

