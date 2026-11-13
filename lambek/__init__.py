"""
Lambek Calculus (L) and Non-associative Lambek Calculus (NL) Engine.

Provides:
- Formal AST for Lambek types (Atoms, Right Division '/', Left Division '\\', Product '*')
- Sequent representations (associative lists and non-associative bracket trees)
- Cut-free backward-chaining proof search with full derivation trees
- Categorial grammar parsing and lexicon for natural language syntax
- Substructural refutations and language-model counterexamples
"""

from .types import (
    Type,
    Atom,
    Slash,
    Backslash,
    Product,
    parse_type,
)
from .sequent import (
    Sequent,
    TreeAntecedent,
    TreeSequent,
    parse_sequent,
)
from .prover import (
    LambekProver,
    ProofNode,
    prove_sequent,
)
from .grammar import (
    Lexicon,
    GrammarDerivation,
    parse_sentence,
)
from .countermodel import (
    Countermodel,
    find_countermodel,
    evaluate_language,
)

__all__ = [
    "Type",
    "Atom",
    "Slash",
    "Backslash",
    "Product",
    "parse_type",
    "Sequent",
    "TreeAntecedent",
    "TreeSequent",
    "parse_sequent",
    "LambekProver",
    "ProofNode",
    "prove_sequent",
    "Lexicon",
    "GrammarDerivation",
    "parse_sentence",
    "Countermodel",
    "find_countermodel",
    "evaluate_language",
]
