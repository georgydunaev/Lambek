"""Constructive Cut Elimination and Cut Admissibility for the Lambek Calculus.

Implements Joachim Lambek's (1958) Cut Admissibility Theorem:
If Gamma |- A and Delta1, A, Delta2 |- B, then Delta1, Gamma, Delta2 |- B.

Provides:
- admit_cut(d1, d2, cut_index): Constructively eliminates cut between two derivations.
- CutProofNode: AST node for derivations with explicit Cut inferences.
- eliminate_all_cuts(tree): Recursively reduces any proof tree containing Cut nodes.
"""

from __future__ import annotations
from typing import Optional, List, Tuple
from lambek.types import TypeAST, Atom, Backslash, Slash, Product
from lambek.sequent import Sequent
from lambek.prover import ProofNode, LambekProver


class CutProofNode(ProofNode):
    """A sequent calculus node representing an explicit Cut inference.

    Premise 1: Gamma |- A
    Premise 2: Delta1, A, Delta2 |- B
    Conclusion: Delta1, Gamma, Delta2 |- B
    """

    def __init__(
        self,
        cut_formula: TypeAST,
        cut_index: int,
        left_premise: ProofNode,
        right_premise: ProofNode,
        conclusion: Optional[Sequent] = None,
    ) -> None:
        if conclusion is None:
            ante1 = left_premise.sequent.antecedent
            ante2 = right_premise.sequent.antecedent
            delta1 = ante2[:cut_index]
            delta2 = ante2[cut_index + 1 :]
            new_ante = delta1 + ante1 + delta2
            new_succ = right_premise.sequent.succedent
            conclusion = Sequent(new_ante, new_succ)

        super().__init__("Cut", conclusion, [left_premise, right_premise])
        self.cut_formula = cut_formula
        self.cut_index = cut_index


def admit_cut(
    d1: ProofNode,
    d2: ProofNode,
    cut_index: Optional[int] = None,
    prover: Optional[LambekProver] = None,
) -> ProofNode:
    """Constructively eliminate the Cut between d1 (Gamma |- A) and d2 (Delta1, A, Delta2 |- B).

    Returns a strictly cut-free ProofNode deriving Delta1, Gamma, Delta2 |- B.
    """
    gamma = d1.sequent.antecedent
    cut_formula = d1.sequent.succedent
    delta = d2.sequent.antecedent
    b = d2.sequent.succedent

    # Determine cut_index if not supplied
    if cut_index is None:
        indices = [i for i, f in enumerate(delta) if f == cut_formula]
        if not indices:
            raise ValueError(
                f"Cut formula {cut_formula} does not occur in antecedent of second premise: {d2.sequent}"
            )
        cut_index = indices[0]
    else:
        if cut_index < 0 or cut_index >= len(delta):
            raise IndexError(f"Cut index {cut_index} out of range for antecedent length {len(delta)}")
        if delta[cut_index] != cut_formula:
            raise ValueError(
                f"Formula at index {cut_index} is {delta[cut_index]}, expected {cut_formula}"
            )

    delta1 = delta[:cut_index]
    delta2 = delta[cut_index + 1 :]
    target_ante = delta1 + gamma + delta2
    target_seq = Sequent(target_ante, b)

    engine = prover if prover is not None else LambekProver()

    # Base Case 1: Identity reduction where d1 is Axiom (A |- A)
    if d1.rule == "Ax" and len(gamma) == 1 and gamma[0] == cut_formula:
        # Delta1, A, Delta2 is already proved by d2
        return d2

    # Base Case 2: Identity reduction where d2 is Axiom (A |- A)
    if d2.rule == "Ax" and len(delta) == 1 and cut_index == 0:
        # Target sequent is Gamma |- A, which is already proved by d1
        return d1

    # Principal Case 1: Right Division (/)
    # d1 ends with (/R): Gamma, A2 |- A1  ===>  Gamma |- A1 / A2
    # d2 ends with (/L) where A1 / A2 is active at cut_index:
    # Premise 1: Phi |- A2
    # Premise 2: Delta1, A1, Delta2' |- B
    if d1.rule == "/R" and isinstance(cut_formula, Slash):
        if d2.rule == "/L" and len(d2.premises) == 2:
            prem_d1 = d1.premises[0]  # Gamma, A2 |- A1
            p_phi = d2.premises[0]     # Phi |- A2
            p_main = d2.premises[1]    # Delta1, A1, Delta2' |- B
            
            # Sub-cut 1: cut p_phi (Phi |- A2) into prem_d1 at A2 (at the end of Gamma, A2)
            cut_idx_a2 = len(gamma)
            d_mid = admit_cut(p_phi, prem_d1, cut_index=cut_idx_a2, prover=engine)
            # d_mid derives Gamma, Phi |- A1

            # Sub-cut 2: cut d_mid into p_main at A1 (at index len(delta1))
            cut_idx_a1 = len(delta1)
            res = admit_cut(d_mid, p_main, cut_index=cut_idx_a1, prover=engine)
            if res.sequent == target_seq:
                return res

    # Principal Case 2: Left Division (\)
    # d1 ends with (\R): A1, Gamma |- A2  ===>  Gamma |- A1 \ A2
    # d2 ends with (\L) where A1 \ A2 is active at cut_index:
    # Premise 1: Phi |- A1
    # Premise 2: Delta1', A2, Delta2 |- B
    if d1.rule == "\\R" and isinstance(cut_formula, Backslash):
        if d2.rule == "\\L" and len(d2.premises) == 2:
            prem_d1 = d1.premises[0]  # A1, Gamma |- A2
            p_phi = d2.premises[0]     # Phi |- A1
            p_main = d2.premises[1]    # Delta1', A2, Delta2 |- B

            # Sub-cut 1: cut p_phi (Phi |- A1) into prem_d1 at A1 (at index 0)
            d_mid = admit_cut(p_phi, prem_d1, cut_index=0, prover=engine)
            # d_mid derives Phi, Gamma |- A2

            # Sub-cut 2: cut d_mid into p_main at A2
            cut_idx_a2 = len(p_main.sequent.antecedent) - len(delta2) - 1
            res = admit_cut(d_mid, p_main, cut_index=cut_idx_a2, prover=engine)
            if res.sequent == target_seq:
                return res

    # Principal Case 3: Product (*)
    # d1 ends with (*R): Gamma1 |- A1 and Gamma2 |- A2  ===>  Gamma1, Gamma2 |- A1 * A2
    # d2 ends with (*L) where A1 * A2 is split into A1, A2:
    # Premise: Delta1, A1, A2, Delta2 |- B
    if d1.rule == "*R" and isinstance(cut_formula, Product) and len(d1.premises) == 2:
        if d2.rule == "*L" and len(d2.premises) == 1:
            p1 = d1.premises[0]  # Gamma1 |- A1
            p2 = d1.premises[1]  # Gamma2 |- A2
            p_split = d2.premises[0]  # Delta1, A1, A2, Delta2 |- B

            # First cut p2 (Gamma2 |- A2) at position cut_index + 1
            d_mid = admit_cut(p2, p_split, cut_index=cut_index + 1, prover=engine)
            # Then cut p1 (Gamma1 |- A1) at position cut_index
            res = admit_cut(p1, d_mid, cut_index=cut_index, prover=engine)
            if res.sequent == target_seq:
                return res

    # Constructive Decision Engine:
    # Since cut is admissible in L and backward search is complete and terminating,
    # find the canonical cut-free proof of target_seq.
    res_direct = engine.prove(target_seq)
    if res_direct is not None:
        return res_direct

    raise ValueError(f"Target sequent {target_seq} could not be derived after cut elimination")


def eliminate_all_cuts(tree: ProofNode, prover: Optional[LambekProver] = None) -> ProofNode:
    """Recursively eliminate all Cut inferences from a derivation tree."""
    if not tree.premises:
        return tree

    reduced_premises = [eliminate_all_cuts(p, prover=prover) for p in tree.premises]

    if tree.rule == "Cut":
        if len(reduced_premises) != 2:
            raise ValueError("Cut node must have exactly 2 premises")
        p1, p2 = reduced_premises[0], reduced_premises[1]
        cut_idx = getattr(tree, "cut_index", None)
        return admit_cut(p1, p2, cut_index=cut_idx, prover=prover)

    return ProofNode(tree.rule, tree.sequent, reduced_premises)
