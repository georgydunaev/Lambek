"""
Countermodel generator and refutation diagnostics for Lambek Calculus (L).

Lambek calculus (1958) is a substructural logic lacking:
- Exchange (non-commutative: order of hypotheses matters)
- Weakening (resource-sensitive: no unused hypotheses)
- Contraction (resource-sensitive: no duplicating hypotheses)
- Empty antecedent (at least one hypothesis required)

When a sequent is unprovable in L, this module diagnoses the exact failure:
1. Empty antecedent violation.
2. Lambek-van Benthem count invariant mismatch (signed atom counts).
3. Exchange/Permutation failure (multiset of atoms balance, but order is rejected).
4. Weakening failure (surplus atoms present in antecedent).
5. Contraction failure (deficit of atoms in antecedent).
6. Concrete language model counterexample over a free monoid Sigma^*.
"""

from dataclasses import dataclass
from typing import Optional, Dict, Set, List, Tuple, Any

from .types import Type, Atom, Slash, Backslash, Product
from .sequent import Sequent
from .prover import LambekProver, ProofNode


@dataclass
class Countermodel:
    """Represents a diagnostic refutation and countermodel for an unprovable sequent."""
    sequent: Sequent
    violation_type: str
    diagnosis: str
    atom_discrepancies: Dict[str, Tuple[int, int]]
    alphabet: Optional[List[str]] = None
    interpretation: Optional[Dict[str, Set[str]]] = None
    counterexample_word: Optional[str] = None

    def __str__(self) -> str:
        lines = [
            f"Countermodel for invalid sequent: {self.sequent}",
            f"Violation Type: {self.violation_type}",
            f"Diagnosis: {self.diagnosis}",
        ]
        if self.atom_discrepancies:
            lines.append("Atom Polarity Balance (Antecedent vs Succedent):")
            for atom, (ant_cnt, succ_cnt) in sorted(self.atom_discrepancies.items()):
                lines.append(f"  Atom '{atom}': antecedent={ant_cnt}, succedent={succ_cnt}")
        if self.counterexample_word is not None and self.interpretation is not None:
            lines.append(f"Monoid Counterexample: word '{self.counterexample_word}' in L(Antecedent) \\ L(Succedent)")
            lines.append("Atom Language Assignment:")
            for atom, lang in sorted(self.interpretation.items()):
                lines.append(f"  L({atom}) = {sorted(list(lang))}")
        return "\n".join(lines)


def evaluate_language(tp: Type, interp: Dict[str, Set[str]], max_word_len: int = 6) -> Set[str]:
    """
    Evaluate type denotation in a finite sublanguage of Sigma^* under interpretation interp.
    """
    if isinstance(tp, Atom):
        return set(interp.get(tp.name, set()))
    elif isinstance(tp, Product):
        left_lang = evaluate_language(tp.left, interp, max_word_len)
        right_lang = evaluate_language(tp.right, interp, max_word_len)
        res: Set[str] = set()
        for u in left_lang:
            for v in right_lang:
                w = u + v
                if len(w) <= max_word_len:
                    res.add(w)
        return res
    elif isinstance(tp, Slash):
        # B / A = { u | forall v in L(A), uv in L(B) }
        left_lang = evaluate_language(tp.left, interp, max_word_len)   # B
        right_lang = evaluate_language(tp.right, interp, max_word_len) # A
        res = set()
        # candidate words u: prefixes of words in B or empty
        candidate_words: Set[str] = {""}
        for b_word in left_lang:
            for i in range(len(b_word) + 1):
                candidate_words.add(b_word[:i])
        for u in candidate_words:
            if all((u + v) in left_lang for v in right_lang):
                res.add(u)
        return res
    elif isinstance(tp, Backslash):
        # A \ B = { v | forall u in L(A), uv in L(B) }
        left_lang = evaluate_language(tp.left, interp, max_word_len)   # A
        right_lang = evaluate_language(tp.right, interp, max_word_len) # B
        res = set()
        candidate_words = {""}
        for b_word in right_lang:
            for i in range(len(b_word) + 1):
                candidate_words.add(b_word[i:])
        for v in candidate_words:
            if all((u + v) in right_lang for u in left_lang):
                res.add(v)
        return res
    return set()


def evaluate_antecedent_language(antecedent: List[Type], interp: Dict[str, Set[str]], max_word_len: int = 6) -> Set[str]:
    """Concatenate language denotations of antecedent formulas."""
    if not antecedent:
        return {""}
    current_lang = evaluate_language(antecedent[0], interp, max_word_len)
    for tp in antecedent[1:]:
        next_lang = evaluate_language(tp, interp, max_word_len)
        prod: Set[str] = set()
        for u in current_lang:
            for v in next_lang:
                w = u + v
                if len(w) <= max_word_len:
                    prod.add(w)
        current_lang = prod
    return current_lang


def build_concrete_countermodel(sequent: Sequent) -> Tuple[List[str], Dict[str, Set[str]], Optional[str]]:
    """
    Construct a free monoid language model counterexample if possible.
    Assigns single distinct letters to atoms and searches for a word in antecedent not in succedent.
    """
    atoms = sorted(list(sequent.atoms()))
    alphabet = [f"a_{i}" for i in range(len(atoms))]
    interp: Dict[str, Set[str]] = {}
    for idx, atom_name in enumerate(atoms):
        interp[atom_name] = {f"[{atom_name}]"}

    ant_lang = evaluate_antecedent_language(sequent.antecedent, interp, max_word_len=12)
    succ_lang = evaluate_language(sequent.succedent, interp, max_word_len=12)

    diff = ant_lang - succ_lang
    counterexample_word = next(iter(diff)) if diff else None
    return alphabet, interp, counterexample_word


def find_countermodel(sequent: Sequent, prover: Optional[LambekProver] = None) -> Optional[Countermodel]:
    """
    Search for a proof. If unprovable, generate a diagnostic Countermodel.
    Returns None if the sequent is valid/provable.
    """
    p = prover if prover is not None else LambekProver()
    proof = p.prove(sequent)
    if proof is not None:
        return None

    # Check 1: Empty antecedent
    if not sequent.antecedent:
        return Countermodel(
            sequent=sequent,
            violation_type="EmptyAntecedent",
            diagnosis="Lambek calculus requires strictly non-empty antecedents (pure substructural system).",
            atom_discrepancies={},
        )

    # Check 2: Lambek-van Benthem polarity count invariant
    ant_counts: Dict[str, int] = {}
    for tp in sequent.antecedent:
        for atom, cnt in tp.count_polarity(+1).items():
            ant_counts[atom] = ant_counts.get(atom, 0) + cnt
    succ_counts = sequent.succedent.count_polarity(+1)

    all_atoms = set(ant_counts.keys()) | set(succ_counts.keys())
    discrepancies = {
        atom: (ant_counts.get(atom, 0), succ_counts.get(atom, 0))
        for atom in all_atoms
        if ant_counts.get(atom, 0) != succ_counts.get(atom, 0)
    }

    alphabet, interp, counter_word = build_concrete_countermodel(sequent)

    if discrepancies:
        surplus_atoms = [a for a, (ac, sc) in discrepancies.items() if ac > sc]
        deficit_atoms = [a for a, (ac, sc) in discrepancies.items() if ac < sc]

        if surplus_atoms and not deficit_atoms:
            v_type = "WeakeningViolation"
            diag = (
                f"Surplus resources in antecedent: {surplus_atoms}. "
                "Lambek calculus lacks the Weakening structural rule; all hypotheses must be used."
            )
        elif deficit_atoms and not surplus_atoms:
            v_type = "ContractionViolation"
            diag = (
                f"Resource deficit in antecedent: {deficit_atoms}. "
                "Lambek calculus lacks the Contraction structural rule; hypotheses cannot be duplicated."
            )
        else:
            v_type = "CountInvariantViolation"
            diag = (
                "The Lambek-van Benthem invariant fails: signed atom counts do not balance "
                f"between antecedent and succedent ({discrepancies})."
            )

        return Countermodel(
            sequent=sequent,
            violation_type=v_type,
            diagnosis=diag,
            atom_discrepancies=discrepancies,
            alphabet=alphabet,
            interpretation=interp,
            counterexample_word=counter_word,
        )

    # Check 3: Polarity counts balance, but order is rejected (Exchange / Permutation)
    return Countermodel(
        sequent=sequent,
        violation_type="ExchangeViolation",
        diagnosis=(
            "Multisets of polar atoms balance, but the derivation fails because Lambek calculus "
            "lacks the Exchange/Permutation rule. Word order and bracket associativity are strictly preserved."
        ),
        atom_discrepancies={},
        alphabet=alphabet,
        interpretation=interp,
        counterexample_word=counter_word,
    )
