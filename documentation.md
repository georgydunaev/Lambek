# Documentation: Lambek Calculus, Substructural Logics, and Categorial Grammars

## 1. Mathematical Foundations of Lambek Calculus

The Lambek calculus, introduced by Joachim Lambek in his 1958 paper *"The Mathematics of Sentence Structure"*, is a non-commutative, resource-sensitive logic designed to capture the syntactic structure of natural language.

### Syntactic Types
Let $\mathcal{A}$ be a set of primitive syntactic types (atoms, such as $s$ for sentence, $n$ for common noun, $np$ for noun phrase). The set of formulas $\mathcal{F}$ is formed inductively:
1. $p \in \mathcal{F}$ for all $p \in \mathcal{A}$.
2. If $A, B \in \mathcal{F}$, then $A \backslash B \in \mathcal{F}$ (left division: under $A$ gives $B$; an argument of type $A$ is required to its immediate left).
3. If $A, B \in \mathcal{F}$, then $B / A \in \mathcal{F}$ (right division: over $A$ gives $B$; an argument of type $A$ is required to its immediate right).
4. If $A, B \in \mathcal{F}$, then $A \bullet B \in \mathcal{F}$ (product / concatenation).

### Sequents and Substructural Properties
A sequent in the associative Lambek calculus (L) has the form:
$$A_1, \dots, A_n \vdash B \quad (n \ge 1)$$

Lambek calculus lacks the standard structural rules of Gentzen's classical and intuitionistic systems:
- **No Weakening**: Every formula in the antecedent must contribute directly to the derivation.
- **No Contraction**: A formula cannot be reused or duplicated.
- **No Exchange / Permutation**: The order of hypotheses is strictly preserved. In L, $A, B \vdash B \bullet A$ is invalid.

### Associativity vs. Non-Associativity (L vs. NL)
- **Associative Lambek Calculus (L)** (1958): Hypotheses are organized in an associative list or word. Brackets can be freely rearranged: $(A \bullet B) \bullet C \vdash A \bullet (B \bullet C)$ is provable.
- **Non-Associative Lambek Calculus (NL)** (1961): Hypotheses are structured as a binary tree. Re-bracketing is forbidden unless explicit structural modalities are added.

---

## 2. Sequent Rules for Full Associative Lambek Calculus (L)

### Identity Axiom
$$\frac{}{A \vdash A} (\text{Ax})$$

### Slash Rules (Right Division)
$$\frac{\Gamma, A \vdash B}{\Gamma \vdash B / A} (\text{R}/) \quad (\Gamma \text{ non-empty})$$

$$\frac{\Delta \vdash A \quad \Gamma_1, B, \Gamma_2 \vdash C}{\Gamma_1, B / A, \Delta, \Gamma_2 \vdash C} (\text{L}/)$$

### Backslash Rules (Left Division)
$$\frac{A, \Gamma \vdash B}{\Gamma \vdash A \backslash B} (\text{R}\backslash) \quad (\Gamma \text{ non-empty})$$

$$\frac{\Delta \vdash A \quad \Gamma_1, B, \Gamma_2 \vdash C}{\Gamma_1, \Delta, A \backslash B, \Gamma_2 \vdash C} (\text{L}\backslash)$$

### Product Rules
$$\frac{\Gamma_1 \vdash A \quad \Gamma_2 \vdash B}{\Gamma_1, \Gamma_2 \vdash A \bullet B} (\text{R}\bullet)$$

$$\frac{\Gamma_1, A, B, \Gamma_2 \vdash C}{\Gamma_1, A \bullet B, \Gamma_2 \vdash C} (\text{L}\bullet)$$

### Cut Admissibility
$$\frac{\Delta \vdash A \quad \Gamma_1, A, \Gamma_2 \vdash C}{\Gamma_1, \Delta, \Gamma_2 \vdash C} (\text{Cut})$$

In both L and NL, Gentzen's Cut Elimination Theorem holds: every theorem provable with Cut has a cut-free derivation. This yields the decidability of the calculus via finite backward-chaining proof search.

---

## 3. Algebraic and Categorical Semantics

Lambek calculus corresponds to the internal language of **residuated monoids** (or biclosed monoidal categories):
- A monoid $(M, \bullet, 1)$ equipped with a partial order $\le$.
- The product $\bullet$ is monotonic.
- Left and right adjoints (residuals) exist for product:
  $$A \bullet B \le C \iff A \le C / B \iff B \le A \backslash C$$

In category theory, this is a monoidal biclosed category where the tensor product $\otimes$ is non-symmetric and has distinct left and right internal hom functors.

---

## 4. Linguistic Categorial Grammars

In categorial grammar, words in a natural language are assigned syntactic types from $\mathcal{F}$. A sentence $w_1 \dots w_n$ is syntactically well-formed with target category $C$ (typically $s$) if there exist type assignments $A_i \in \text{Lex}(w_i)$ such that:
$$A_1, \dots, A_n \vdash C$$

### Standard Category Assignments:
- Common noun: $n$ ("problem", "mathematician", "book")
- Determiner: $np / n$ ("the", "a")
- Proper name / Noun phrase: $np$ ("Alice", "John", "Mary")
- Intransitive verb: $np \backslash s$ ("runs", "sleeps")
- Transitive verb: $(np \backslash s) / np$ ("solved", "loves", "likes")
- Ditransitive verb: $((np \backslash s) / np) / np$ ("gave")
- Adjective: $n / n$ ("hard", "interesting")
- Preposition: $(n \backslash n) / np$ or $((np \backslash s) \backslash (np \backslash s)) / np$ ("in", "with")
- Relative pronoun (object): $(n \backslash n) / (s / np)$ ("which", "that")

---

## 5. Decision Procedure and Countermodels

### Lambek-van Benthem Polarity Invariant
Let $\text{pol}(p, A)$ denote the signed count of atom $p$ in $A$, where left arguments of $\backslash$ and right arguments of $/$ flip polarity.
In any valid Lambek theorem $A_1, \dots, A_n \vdash B$:
$$\sum_{i=1}^n \text{pol}(p, A_i) = \text{pol}(p, B) \quad \text{for all atoms } p$$
Any discrepancy immediately refutes the sequent without searching derivation trees.

### Free Monoid Countermodels
For invalid sequents that satisfy the count invariant (such as $A, B \vdash B \bullet A$), a concrete language model over the free monoid $\Sigma^*$ provides an explicit counterexample: a word $w \in L(A_1)\dots L(A_n)$ such that $w \notin L(B)$.
