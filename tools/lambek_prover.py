#!/usr/bin/env python3
"""Interactive Derivation Tree Visualizer and Sentence Parser for Lambek Calculus.

CLI utility to prove sequents, parse natural language sentences, and perform
constructive cut elimination in the Associative Lambek Calculus (L).
"""

from __future__ import annotations
import sys
import os
import argparse
from typing import Optional, List

# Ensure package root is in sys.path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from lambek.types import TypeAST, parse_type
from lambek.sequent import Sequent, parse_sequent
from lambek.prover import LambekProver, ProofNode, prove_sequent
from lambek.cut_elimination import admit_cut, CutProofNode
from lambek.grammar import Lexicon, parse_sentence


def proof_to_latex(node: ProofNode) -> str:
    """Convert a ProofNode into LaTeX bussproofs code."""
    lines: List[str] = []

    def recurse(n: ProofNode) -> None:
        for p in n.premises:
            recurse(p)
        ante_str = ", ".join(str(f) for f in n.sequent.antecedent)
        succ_str = str(n.sequent.succedent)
        seq_tex = f"{ante_str} \\vdash {succ_str}"
        rule_label = n.rule.replace("\\", "\\backslash ")

        if len(n.premises) == 0:
            lines.append(f"\\AxiomC{{{seq_tex}}}")
        elif len(n.premises) == 1:
            lines.append(f"\\RightLabel{{$[{rule_label}]$}}")
            lines.append(f"\\UnaryInfC{{{seq_tex}}}")
        elif len(n.premises) == 2:
            lines.append(f"\\RightLabel{{$[{rule_label}]$}}")
            lines.append(f"\\BinaryInfC{{{seq_tex}}}")
        else:
            lines.append(f"\\RightLabel{{$[{rule_label}]$}}")
            lines.append(f"\\TrinaryInfC{{{seq_tex}}}")

    lines.append("\\begin{prooftree}")
    recurse(node)
    lines.append("\\end{prooftree}")
    return "\n".join(lines)


def proof_to_deduction_lines(node: ProofNode) -> List[str]:
    """Render a proof node in horizontal deduction inference line format."""
    seq_str = f" {node.sequent} "
    rule_str = f" [{node.rule}]"

    if not node.premises:
        w = max(len(seq_str), 10)
        bar = "-" * w + rule_str
        return [bar, seq_str.center(w)]

    premise_blocks = [proof_to_deduction_lines(p) for p in node.premises]
    # Align premise blocks side-by-side with spacing
    max_height = max(len(b) for b in premise_blocks)
    padded_blocks: List[List[str]] = []
    for b in premise_blocks:
        pad_top = max_height - len(b)
        w = max(len(line) for line in b) if b else 0
        pad_lines = [" " * w] * pad_top + b
        padded_blocks.append([line.ljust(w) for line in pad_lines])

    top_lines: List[str] = []
    for r in range(max_height):
        top_lines.append("   ".join(padded_blocks[c][r] for c in range(len(padded_blocks))))

    top_width = len(top_lines[-1]) if top_lines else len(seq_str)
    bar_width = max(top_width, len(seq_str))
    bar_line = "-" * bar_width + rule_str
    bottom_line = seq_str.center(bar_width)

    return top_lines + [bar_line, bottom_line]


def cmd_prove(sequent_str: str, latex: bool = False, horizontal: bool = False) -> int:
    try:
        seq = parse_sequent(sequent_str)
    except Exception as e:
        print(f"Error parsing sequent: {e}", file=sys.stderr)
        return 1

    prover = LambekProver()
    proof = prover.prove(seq)

    if proof is None:
        print(f"FAILED: Sequent {seq} is not provable in Lambek calculus (L).")
        return 1

    print(f"PROVED: {seq}\n")
    if latex:
        print("LaTeX Derivation (bussproofs):")
        print(proof_to_latex(proof))
    elif horizontal:
        print("Inference Line Derivation:")
        lines = proof_to_deduction_lines(proof)
        print("\n".join(lines))
    else:
        print("Tree Derivation:")
        print(proof.to_ascii_tree())

    return 0


def cmd_parse(sentence: str, target_cat: str = "s", latex: bool = False) -> int:
    lex = Lexicon.standard_english()
    derivations = parse_sentence(sentence, lexicon=lex, target=target_cat)

    if not derivations:
        print(f"FAILED: No grammatical derivation found for {sentence!r} with target {target_cat!r}.")
        return 1

    print(f"SUCCESS: Found {len(derivations)} derivation(s) for {sentence!r} |- {target_cat}\n")
    for i, d in enumerate(derivations, start=1):
        print(f"=== Derivation {i} ===")
        print(f"Word Categories: {d.type_assignment_str()}")
        if latex:
            print("\nLaTeX Derivation:")
            print(proof_to_latex(d.proof))
        else:
            print("\nInference Lines:")
            print("\n".join(proof_to_deduction_lines(d.proof)))
            print("\nTree View:")
            print(d.proof.to_ascii_tree())
        print()

    return 0


def cmd_cut(seq1_str: str, seq2_str: str, cut_index: Optional[int] = None) -> int:
    prover = LambekProver()
    try:
        s1 = parse_sequent(seq1_str)
        s2 = parse_sequent(seq2_str)
    except Exception as e:
        print(f"Error parsing sequents: {e}", file=sys.stderr)
        return 1

    p1 = prover.prove(s1)
    if p1 is None:
        print(f"Error: Premise 1 {s1} is not provable.", file=sys.stderr)
        return 1

    p2 = prover.prove(s2)
    if p2 is None:
        print(f"Error: Premise 2 {s2} is not provable.", file=sys.stderr)
        return 1

    try:
        cut_free = admit_cut(p1, p2, cut_index=cut_index, prover=prover)
    except Exception as e:
        print(f"Cut elimination error: {e}", file=sys.stderr)
        return 1

    print("Constructive Cut Admissibility Result:")
    print(f"Premise 1: {s1}")
    print(f"Premise 2: {s2}")
    print(f"Cut-Free Conclusion: {cut_free.sequent}\n")
    print("Inference Lines:")
    print("\n".join(proof_to_deduction_lines(cut_free)))
    return 0


def cmd_interactive() -> int:
    print("Lambek Calculus Interactive REPL")
    print("Commands:")
    print("  prove <sequent>      Prove a sequent (e.g., prove np, (np \\ s) / np, np |- s)")
    print("  parse <sentence>     Parse a sentence (e.g., parse john likes mary)")
    print("  cut <s1> ; <s2>      Eliminate cut between two sequents")
    print("  quit / exit          Exit REPL\n")

    while True:
        try:
            line = input("lambek> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nExiting.")
            break

        if not line or line.lower() in ("quit", "exit"):
            break

        parts = line.split(maxsplit=1)
        cmd = parts[0].lower()
        arg = parts[1].strip() if len(parts) > 1 else ""

        if cmd == "prove":
            cmd_prove(arg)
        elif cmd == "parse":
            cmd_parse(arg)
        elif cmd == "cut":
            if ";" in arg:
                s1_part, s2_part = arg.split(";", 1)
                cmd_cut(s1_part.strip(), s2_part.strip())
            else:
                print("Usage: cut <seq1> ; <seq2>")
        else:
            print(f"Unknown command: {cmd}")

    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lambek Calculus Prover, Derivation Visualizer, and Categorial Sentence Parser"
    )
    parser.add_argument("--prove", type=str, help="Prove a Lambek sequent (e.g. 'np, np \\ s |- s')")
    parser.add_argument("--parse", type=str, help="Parse a sentence into categorial derivations")
    parser.add_argument("--target", type=str, default="s", help="Target category for parsing (default: s)")
    parser.add_argument("--cut", nargs=2, metavar=("SEQ1", "SEQ2"), help="Perform cut elimination between two sequents")
    parser.add_argument("--cut-index", type=int, default=None, help="Index of cut formula in second antecedent")
    parser.add_argument("--latex", action="store_true", help="Output derivation tree in LaTeX bussproofs format")
    parser.add_argument("--horizontal", action="store_true", help="Output deduction in horizontal inference lines")
    parser.add_argument("--interactive", action="store_true", help="Launch interactive REPL mode")

    args = parser.parse_args()

    if args.interactive:
        return cmd_interactive()
    elif args.prove:
        return cmd_prove(args.prove, latex=args.latex, horizontal=args.horizontal)
    elif args.parse:
        return cmd_parse(args.parse, target_cat=args.target, latex=args.latex)
    elif args.cut:
        return cmd_cut(args.cut[0], args.cut[1], cut_index=args.cut_index)
    else:
        parser.print_help()
        return 0


if __name__ == "__main__":
    sys.exit(main())
