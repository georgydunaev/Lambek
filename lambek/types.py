r"""Syntactic types for the Lambek Calculus.

Connectives:
  - Left division: A \ B (under A gives B, requires A on the left)
  - Right division: B / A (over A gives B, requires A on the right)
  - Product: A * B or A • B (associative or non-associative combination)
"""

from __future__ import annotations
from abc import ABC, abstractmethod
from typing import Dict, Any, Set


class TypeAST(ABC):
    """Abstract base class for Lambek syntactic types."""

    @abstractmethod
    def __str__(self) -> str:
        pass

    @abstractmethod
    def __repr__(self) -> str:
        pass

    @abstractmethod
    def __eq__(self, other: Any) -> bool:
        pass

    @abstractmethod
    def __hash__(self) -> int:
        pass

    @property
    @abstractmethod
    def complexity(self) -> int:
        """Connective count / syntactic complexity."""
        pass

    def atoms(self) -> Set[str]:
        """Collect all atomic variable names occurring in this type."""
        acc: Set[str] = set()
        self._collect_atoms(acc)
        return acc

    @abstractmethod
    def _collect_atoms(self, acc: Set[str]) -> None:
        pass

    def count_polarity(self, polarity: int = 1) -> Dict[str, int]:
        """Compute atom counts weighted by sign/polarity (+1 for positive, -1 for negative)."""
        counts: Dict[str, int] = {}
        self._accumulate_counts(counts, polarity)
        return counts

    @abstractmethod
    def _accumulate_counts(self, acc: Dict[str, int], pol: int) -> None:
        pass


class Atom(TypeAST):
    """Primitive syntactic category (e.g. s, np, n)."""

    def __init__(self, name: str) -> None:
        self.name = str(name).strip()

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f"Atom({self.name!r})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Atom) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("Atom", self.name))

    @property
    def complexity(self) -> int:
        return 0

    def _accumulate_counts(self, acc: Dict[str, int], pol: int) -> None:
        acc[self.name] = acc.get(self.name, 0) + pol

    def _collect_atoms(self, acc: Set[str]) -> None:
        acc.add(self.name)


class Backslash(TypeAST):
    """Left division: A \\ B (requires A on the left to produce B)."""

    def __init__(self, left: TypeAST, right: TypeAST) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        l_str = f"({self.left})" if isinstance(self.left, (Backslash, Slash, Product)) else str(self.left)
        r_str = f"({self.right})" if isinstance(self.right, (Backslash, Slash, Product)) else str(self.right)
        return f"{l_str} \\ {r_str}"

    def __repr__(self) -> str:
        return f"Backslash({self.left!r}, {self.right!r})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Backslash) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Backslash", self.left, self.right))

    @property
    def complexity(self) -> int:
        return 1 + self.left.complexity + self.right.complexity

    def _accumulate_counts(self, acc: Dict[str, int], pol: int) -> None:
        # A \ B : left argument A has negative polarity, right argument B has positive polarity
        self.left._accumulate_counts(acc, -pol)
        self.right._accumulate_counts(acc, pol)

    def _collect_atoms(self, acc: Set[str]) -> None:
        self.left._collect_atoms(acc)
        self.right._collect_atoms(acc)


class Slash(TypeAST):
    """Right division: B / A (requires A on the right to produce B)."""

    def __init__(self, left: TypeAST, right: TypeAST) -> None:
        self.left = left    # B
        self.right = right  # A

    def __str__(self) -> str:
        l_str = f"({self.left})" if isinstance(self.left, (Backslash, Slash, Product)) else str(self.left)
        r_str = f"({self.right})" if isinstance(self.right, (Backslash, Slash, Product)) else str(self.right)
        return f"{l_str} / {r_str}"

    def __repr__(self) -> str:
        return f"Slash({self.left!r}, {self.right!r})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Slash) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Slash", self.left, self.right))

    @property
    def complexity(self) -> int:
        return 1 + self.left.complexity + self.right.complexity

    def _accumulate_counts(self, acc: Dict[str, int], pol: int) -> None:
        # B / A : left argument B has positive polarity, right argument A has negative polarity
        self.left._accumulate_counts(acc, pol)
        self.right._accumulate_counts(acc, -pol)

    def _collect_atoms(self, acc: Set[str]) -> None:
        self.left._collect_atoms(acc)
        self.right._collect_atoms(acc)


class Product(TypeAST):
    """Syntactic product: A * B or A • B."""

    def __init__(self, left: TypeAST, right: TypeAST) -> None:
        self.left = left
        self.right = right

    def __str__(self) -> str:
        l_str = f"({self.left})" if isinstance(self.left, (Backslash, Slash, Product)) else str(self.left)
        r_str = f"({self.right})" if isinstance(self.right, (Backslash, Slash, Product)) else str(self.right)
        return f"{l_str} * {r_str}"

    def __repr__(self) -> str:
        return f"Product({self.left!r}, {self.right!r})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Product) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Product", self.left, self.right))

    @property
    def complexity(self) -> int:
        return 1 + self.left.complexity + self.right.complexity

    def _accumulate_counts(self, acc: Dict[str, int], pol: int) -> None:
        self.left._accumulate_counts(acc, pol)
        self.right._accumulate_counts(acc, pol)

    def _collect_atoms(self, acc: Set[str]) -> None:
        self.left._collect_atoms(acc)
        self.right._collect_atoms(acc)


# Recursive descent parser for syntactic types
def parse_type(text: str) -> TypeAST:
    """Parse string representation into TypeAST.

    Supports:
      - atomic identifiers: np, s, n, p, q, ...
      - connectives: \\ (backslash), / (slash), * or • (product)
      - parentheses for grouping: (np \\ s) / np
    """
    tokens = _tokenize(text)
    pos = 0

    def peek() -> str:
        nonlocal pos
        return tokens[pos] if pos < len(tokens) else ""

    def consume(expected: str = "") -> str:
        nonlocal pos
        tok = peek()
        if expected and tok != expected:
            raise ValueError(f"Expected {expected!r}, got {tok!r} at token {pos} in {text!r}")
        pos += 1
        return tok

    def parse_factor() -> TypeAST:
        tok = peek()
        if tok == "(":
            consume("(")
            node = parse_expr()
            consume(")")
            return node
        elif tok.isalnum() or tok.startswith("_"):
            consume()
            return Atom(tok)
        else:
            raise ValueError(f"Unexpected token {tok!r} at position {pos} in {text!r}")

    def parse_product() -> TypeAST:
        node = parse_factor()
        while peek() in ("*", "•"):
            consume()
            right = parse_factor()
            node = Product(node, right)
        return node

    def parse_expr() -> TypeAST:
        node = parse_product()
        while peek() in ("\\", "/"):
            op = consume()
            right = parse_product()
            if op == "\\":
                node = Backslash(node, right)
            else:
                node = Slash(node, right)
        return node

    result = parse_expr()
    if pos < len(tokens):
        raise ValueError(f"Trailing tokens {tokens[pos:]} in {text!r}")
    return result


def _tokenize(text: str) -> list[str]:
    text = text.replace("•", "*")
    tokens: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c in ("(", ")", "\\", "/", "*"):
            tokens.append(c)
            i += 1
        elif c.isalnum() or c == "_":
            start = i
            while i < n and (text[i].isalnum() or text[i] == "_"):
                i += 1
            tokens.append(text[start:i])
        else:
            raise ValueError(f"Illegal character {c!r} in type expression: {text!r}")
    return tokens


# Alias for backward-compatibility and concise imports
Type = TypeAST

