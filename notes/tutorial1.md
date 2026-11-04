# Tutorial 1: Getting Started with Lambek Calculus in Coq

## Introduction

This tutorial provides a step-by-step guide on how to use the Lambek calculus implementation in Coq. The implementation includes definitions for variables, literals, words, and operations for negation and double negation. It also includes inductive definitions for Plus and Minus and tactics for pattern matching.

## Prerequisites

- Coq installed on your system
- Basic knowledge of Coq and mathematical logic

## Step-by-Step Guide

1. **Define Variables and Literals**:
   - Variables are defined as natural numbers.
   - Literals are defined as records with a variable and a natural number.

2. **Define Words**:
   - Words are defined as lists of literals.

3. **Negation and Double Negation**:
   - Negation is defined by incrementing the natural number in a literal.
   - Double negation is defined by negating a literal twice.

4. **Plus and Minus Relations**:
   - The Plus relation is defined for words with an even natural number.
   - The Minus relation is defined for words with an odd natural number.

## Example

See the example file `examples/example1.v` for a practical demonstration of the Lambek calculus implementation.

## Conclusion

This tutorial should help you get started with the Lambek calculus implementation in Coq. For more advanced usage, refer to the main implementation file `01.v`.

Author: openrouter/nvidia/nemotron-3.5-lightning:free (Capability Tier 1)
Date: 2023-10-28
