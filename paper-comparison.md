# Paper vs. Rocq Development: Comparison

This document compares the CSL 2025 paper *"Kleene Algebra with Commutativity Conditions Is Undecidable"* (Azevedo de Amorim et al.) with the Rocq formalization in `kacc_undec.v`.

## What the paper proves

The paper shows that the equational theory of Kleene algebra (and even pre-Kleene algebra) with commutativity conditions on atomic terms is undecidable. The proof reduces the halting problem for two-counter (Minsky) machines to equational reasoning, then uses effective inseparability to obtain undecidability. The argument has three main parts:

1. **Soundness** (Theorem 3.4): If a machine halts with output 1, a certain inequality holds in the regular language model.
2. **Completeness** (Theorem 3.5): If a machine halts with output 1, one can compute a term making the inequality valid in *all* pre-Kleene algebras (no induction axioms needed).
3. **Effective inseparability** (Theorem 3.5–3.6): The sets of machines halting with output 0 vs. 1 are effectively inseparable, so no computable decision procedure can distinguish the two cases.

## What the Rocq development covers

### Fully formalized (with complete proofs)

- **Algebraic hierarchy** (Sections 1–6 of the development): `setoid` → `monoid` → `semi_lattice` → `pre_ka`, including all mixin records, morphism classes, and concrete instances (`bool`, `count`, product monoids, `gset`). This corresponds to the paper's Section 2 definitions but is significantly more elaborate, with the hierarchy built from scratch using stdpp typeclasses rather than relying on existing Rocq algebra libraries.

- **Free KA terms** (`ka_term`): The full AST with `Unit`, `⊥`, `⊔`, `⋅`, `star`, along with the universal elimination map `ka_term_elim` and proof that `ka_term T` forms a `pre_ka`. The paper treats free terms abstractly via the functor 𝒯; the formalization provides a concrete inductive type.

- **Language semantics**: The `lang` record and interpretation `l : ka_term T → lang` with injectivity on finite terms (`l_inj_finite`). Corresponds to the paper's ℒ functor.

- **Finite automata**: `fsa` and `nfa` records with constructions for join, multiplication (`fsa_mul'`), and Kleene star (`fsa_star'`), plus the key decomposition lemma (`fsa_elem_k_decomp_gen`). The paper's Section 5 (expansion/derivatives) is partially covered here.

- **Derivatives**: Brzozowski-style `derivative` function on `ka_term (list T)` and the `repr_rel` record for representable relations (the paper's bounded-output condition from Section 5.2).

- **Counting/finiteness predicates**: `count_term`, `has_one`, `finite_state`, `pseudo_top` — auxiliary tools not explicitly named in the paper but used in the completeness argument.

- **Projection functions** `π_l`, `π_r` and the commutativity lemma `proj_com` (that left and right projections commute). This is the formal counterpart of the paper's direct sum ⊕ construction.

- **MM2 instruction encoding**: `interp` / `interp_single` / `interpret_mm2_instr` map Minsky machine instructions to KA terms using the alphabet `Σ_M = {Q_M n, a, b, c_0, c_1}`. The configuration term `C_M` and transition relation `R_M` are defined. This directly corresponds to the paper's Definition 3.3.

- **Term simplification**: `ka_simpl`, `ka_simpl_plus`, `ka_simpl_dot`, `ka_simpl_star` with correctness proofs (`ka_simplE`). Not present in the paper; an engineering convenience for the formalization.

- **Various KA lemmas**: `zero_eq_sum`, `zero_eq_prod`, `zero_neq_one`, `term_lang_equiv` (string membership ↔ term ordering), `either_empty_or_nonzero`, `finite_def'`, and many others. Some of these correspond to unnamed lemmas in the paper; others are auxiliary results needed for the formal development.

### Partially formalized (admitted or incomplete)

- **`proj_concat`** (line 3732): `t ≡ (π_l t) ⋅ (π_r t)` — admitted. This is the key decomposition lemma asserting every term equals its left projection times its right projection. The paper relies on this implicitly via the ⊕ construction.

- **`step_form`** (line 3836): The lemma that if a string pair is in the step relation of `R_M`, then the source string has a configuration form `a^n · b^m · Q_M(i)`. Admitted. Corresponds to part of the paper's soundness argument.

- **`zero_eq_prod`** (line 3226): `0 ≡ t₁ · t₂ → t₁ ≡ 0 ∨ t₂ ≡ 0` — admitted. A basic algebraic fact used throughout.

- **`zero_neq_prod`** (line 3264): The contrapositive — admitted.

- **`x_xstar__xstar_x`** and **`x_x_star`** (lines 4007, 4019): Star commutativity with its argument (`t·t✶ ≡ t✶·t`) and the right-unfold (`t✶ ≡ t✶·t`). Both admitted. The paper's pre-KA axioms only include left-unfold; these require additional reasoning.

- **`star_term_interp_empty`** (line 3579): That `[] ∈ l(t✶)` — admitted.

- **`one_star`** (line 4155): `1 ≤ x✶` — aborted with the comment "HELP! -- can't be helped".

- **Canonicalization** (lines 3854–3939): Functions `collect_L_R`, `compose_L_R`, `remove_1`, `left_assoc` are defined but `canonicalize_equiv` (proving the canonicalized term is equivalent) is commented out with incomplete proof attempts.

### Not yet formalized

- **Soundness theorem** (paper Theorem 3.4): The full statement that if a machine reaches `c_1`, the encoding inequality holds in ℒΣ̈_M. The development has `term_leq_R_M__in_lang_interp` stated but its proof is incomplete (cuts off mid-proof).

- **Completeness theorem** (paper Theorem 3.5): Computing the witness term ρ that makes the inequality valid in all pre-Kleene algebras. Not present in the formalization.

- **Effective inseparability and final undecidability** (paper Theorems 3.5–3.6): The diagonal argument constructing machine M_η and the reduction to undecidability. Not present.

- **The `diff` term in the inequality**: While `diff` is defined (line 2650), it is not yet connected to the main soundness/completeness statements.

- **Expansion lemma** (paper Section 5.1): The generalization of derivatives that avoids induction axioms. The `repr_rel` record captures the interface but the key lemma showing the transition relation satisfies it is not proved.

## Structural differences

| Aspect | Paper | Rocq development |
|--------|-------|------------------|
| **Algebraic hierarchy** | Uses standard definitions, assumes familiarity | Built from scratch with explicit mixin records and coercions; more verbose but fully self-contained |
| **Commutativity model** | Abstract "commutable sets" with a commuting relation ~ | Concrete `L`/`R` constructors on `ka_term` with `proj_com` as the commutativity axiom |
| **Direct sum ⊕** | Categorical construction on commutable sets | Modeled via product types `T * S` with `ka_term_inj1`/`ka_term_inj2` and projection morphisms |
| **Machine model** | Abstract two-counter machines with `Inc`, `If`, `Halt` | Uses `mm2_instr` from the Coq Library of Undecidability (`mm2_inc_a`, `mm2_inc_b`, `mm2_dec_a`, `mm2_dec_b`) — no explicit `Halt` instructions |
| **Proof style** | Pen-and-paper with proof sketches | Mix of ssreflect tactics (earlier, more polished sections) and vanilla Ltac (later, work-in-progress sections) |
| **KA axioms** | Left-biased pre-KA (only left-unfold for star) | Same: `PreKAMixin` has only `star_unfold : star x ≡ 1 ⊔ x · star x`. No induction axioms. |
| **Finite automata** | Mentioned briefly; main role is in expansion lemma | Extensively developed (`fsa`, `nfa`, product/star constructions, `fsa_elem_k_decomp_gen`) |

## Summary

The Rocq development has successfully formalized the foundational algebraic infrastructure and the encoding of Minsky machines as KA terms — roughly the first half of the paper's argument. The main gap is the second half: the soundness and completeness theorems connecting machine execution to term inequalities, and the final undecidability result via effective inseparability. Several intermediate lemmas in the MM2 encoding section remain admitted, and the canonicalization procedure (which may support the completeness proof) is incomplete.
