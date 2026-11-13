"""Sequent representations for Associative (L) and Non-Associative (NL) Lambek Calculus."""

from __future__ import annotations
from typing import Tuple, Sequence, Dict, Any, Union, Set
from lambek.types import TypeAST, parse_type


class Sequent:
    """Associative sequent Gamma |- C where Gamma is a non-empty sequence of types."""

    def __init__(self, antecedent: Sequence[TypeAST], succedent: TypeAST) -> None:
        self.antecedent: Tuple[TypeAST, ...] = tuple(antecedent)
        self.succedent: TypeAST = succedent

    def __str__(self) -> str:
        ante_str = ", ".join(str(f) for f in self.antecedent)
        return f"{ante_str} |- {self.succedent}"

    def __repr__(self) -> str:
        return f"Sequent({self.antecedent!r}, {self.succedent!r})"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, Sequent)
            and self.antecedent == other.antecedent
            and self.succedent == other.succedent
        )

    def __hash__(self) -> int:
        return hash(("Sequent", self.antecedent, self.succedent))

    @property
    def total_complexity(self) -> int:
        return sum(f.complexity for f in self.antecedent) + self.succedent.complexity

    def count_invariant(self) -> Dict[str, int]:
        """Compute atom count net difference: sum(antecedent) - succedent.

        In any theorem of the Lambek calculus, this net balance must be zero for all atoms.
        """
        net: Dict[str, int] = {}
        for formula in self.antecedent:
            for atom, cnt in formula.count_polarity(+1).items():
                net[atom] = net.get(atom, 0) + cnt
        for atom, cnt in self.succedent.count_polarity(+1).items():
            net[atom] = net.get(atom, 0) - cnt
        return net

    def satisfies_count_invariant(self) -> bool:
        """Lambek-van Benthem count invariant check."""
        return all(v == 0 for v in self.count_invariant().values())

    def atoms(self) -> Set[str]:
        """Collect all atomic variable names in the sequent."""
        acc: Set[str] = set()
        for formula in self.antecedent:
            acc |= formula.atoms()
        acc |= self.succedent.atoms()
        return acc


# Non-associative bracketed tree structure for NL
class TreeAntecedent:
    """Bracketed configuration of formulas for NL (Lambek 1961)."""

    def __init__(self, left: Union[TypeAST, TreeAntecedent], right: Union[TypeAST, TreeAntecedent, None] = None) -> None:
        if right is None:
            # Leaf containing a single TypeAST
            if not isinstance(left, TypeAST):
                raise TypeError("Single-argument TreeAntecedent must be TypeAST")
            self.is_leaf = True
            self.leaf_value: TypeAST = left
            self.left: Any = None
            self.right: Any = None
        else:
            self.is_leaf = False
            self.leaf_value = None  # type: ignore
            self.left = left if isinstance(left, TreeAntecedent) else TreeAntecedent(left)
            self.right = right if isinstance(right, TreeAntecedent) else TreeAntecedent(right)

    def flatten(self) -> Tuple[TypeAST, ...]:
        if self.is_leaf:
            return (self.leaf_value,)
        return self.left.flatten() + self.right.flatten()

    def leaves(self) -> List[TypeAST]:
        return list(self.flatten())

    def __str__(self) -> str:
        if self.is_leaf:
            return str(self.leaf_value)
        return f"({self.left}, {self.right})"

    def __repr__(self) -> str:
        if self.is_leaf:
            return f"TreeAntecedent({self.leaf_value!r})"
        return f"TreeAntecedent({self.left!r}, {self.right!r})"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, TreeAntecedent) or self.is_leaf != other.is_leaf:
            return False
        if self.is_leaf:
            return self.leaf_value == other.leaf_value
        return self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        if self.is_leaf:
            return hash(("Leaf", self.leaf_value))
        return hash(("Node", self.left, self.right))


class TreeSequent:
    """Non-associative sequent T |- C."""

    def __init__(self, antecedent: TreeAntecedent, succedent: TypeAST) -> None:
        self.antecedent = antecedent
        self.succedent = succedent

    def to_associative(self) -> Sequent:
        return Sequent(self.antecedent.flatten(), self.succedent)

    def __str__(self) -> str:
        return f"{self.antecedent} |- {self.succedent}"

    def __repr__(self) -> str:
        return f"TreeSequent({self.antecedent!r}, {self.succedent!r})"


def parse_sequent(text: str) -> Sequent:
    """Parse string of form 'Gamma |- C' or 'Gamma ⊢ C' into a Sequent."""
    turnstile = "|-" if "|-" in text else "⊢"
    if turnstile not in text:
        raise ValueError(f"Sequent missing turnstile (|- or ⊢) in {text!r}")
    parts = text.split(turnstile, 1)
    ante_raw = parts[0].strip()
    succ_raw = parts[1].strip()

    if not succ_raw:
        raise ValueError("Missing succedent in sequent")

    succ = parse_type(succ_raw)
    if not ante_raw:
        ante = []
    else:
        # Split antecedent by commas (ignoring commas inside parentheses)
        ante_tokens = _split_commas(ante_raw)
        ante = [parse_type(tok) for tok in ante_tokens]

    return Sequent(ante, succ)


def _split_commas(text: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    depth = 0
    for ch in text:
        if ch == "(":
            depth += 1
            current.append(ch)
        elif ch == ")":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            part = "".join(current).strip()
            if part:
                parts.append(part)
            current = []
        else:
            current.append(ch)
    final = "".join(current).strip()
    if final:
        parts.append(final)
    return parts
