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
from .cut_elimination import (
    admit_cut,
    CutProofNode,
    eliminate_all_cuts,
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
from .pentus import (
    Variable,
    Terminal,
    ProductionRule,
    ParseTree,
    CFG,
    CKYChart,
    CKYParser,
    cnf_to_gaifman_kazimierz,
    cross_check_cfg_lambek,
    pentus_interpolate,
    SyntacticConcept,
    SyntacticConceptLattice,
    lambek_to_cfg,
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
    "admit_cut",
    "CutProofNode",
    "eliminate_all_cuts",
    "Lexicon",
    "GrammarDerivation",
    "parse_sentence",
    "Countermodel",
    "find_countermodel",
    "evaluate_language",
    "Variable",
    "Terminal",
    "ProductionRule",
    "ParseTree",
    "CFG",
    "CKYChart",
    "CKYParser",
    "cnf_to_gaifman_kazimierz",
    "cross_check_cfg_lambek",
    "pentus_interpolate",
    "SyntacticConcept",
    "SyntacticConceptLattice",
    "lambek_to_cfg",
]
