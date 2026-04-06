# Paper vs. Rocq Development: Comparison

This document compares the CSL 2025 paper [*"Kleene Algebra
with Commutativity Conditions Is Undecidable"*][paper] (Azevedo
de Amorim, Zhang, Gaboardi) with the Rocq formalization in this
repository.

## What the paper proves

The paper shows that the equational theory of Kleene algebra
(and even pre-Kleene algebra) with commutativity conditions on
atomic terms is undecidable.  The proof reduces the halting
problem for two-counter (Minsky) machines to equational
reasoning, then uses effective inseparability to obtain
undecidability.  The argument has three main parts:

1. **Soundness** (Theorem 15): If a machine halts in the zero
   state, a certain inequality holds in the regular language
   model.
2. **Completeness** (Theorem 16): If a machine halts in the
   zero state, the same inequality holds in *all* pre-Kleene
   algebras (no induction axioms needed).
3. **Effective inseparability** (Theorems 17--18): The sets of
   machines halting with output 0 vs. 1 are effectively
   inseparable, so no computable decision procedure exists.

## What the Rocq development covers

### Fully formalized

- **Algebraic hierarchy** (`algebra.v`): `setoid` → `monoid` →
  `semi_lattice`, including mixin records, morphism classes, and
  concrete instances (`bool`, product monoids, `gset`).
  Corresponds to the paper's Section 2 but is more elaborate,
  building the hierarchy from scratch on top of stdpp.

- **Free KA terms** (`pre_ka.v`): The full `ka_term` AST with
  `Unit`, `⊥`, `⊔`, `⋅`, `star`, the universal elimination map
  `ka_term_elim`, and proof that `ka_term T` forms a `pre_ka`.
  Also includes `count` and `bool` pre-KA instances.  The paper
  treats free terms abstractly; the formalization provides a
  concrete inductive type.

- **Language semantics** (`lang.v`): The `lang` record and
  interpretation `l : ka_term T → lang`, with injectivity on
  finite terms (`l_inj_finite`, Corollary 7) and the string
  membership characterization (`l_alt`, Theorem 5).

- **Finite automata** (`automata.v`): `fsa`/`nfa` records with
  join, product (`fsa_mul'`), and Kleene star (`fsa_star'`)
  constructions, plus the key decomposition lemma
  (`fsa_elem_k_decomp_gen`, Lemma 27).  Also: `ka_term_proj1`,
  `ka_term_proj2`, `ka_term_diag`, and `finite_state`.

- **Representable relations** (`repr_rel.v`): The `repr_rel`
  record (Section 5) with `next`, `residue`, and `expand_rel`
  fields.  Iteration lemmas `repr_rel_iter` (Lemma 21) and
  `repr_rel_iter_empty` (Theorem 22).  Also: padding
  infrastructure (`pad_lang`, `pad_rel`) and the final iteration
  lemma `repr_rel_iter_final`.

- **Bounded-output terms** (`bounded_output.v`): `bounded_output`
  (Definition 28), closure under join/mul/star (Lemma 30),
  `bounded_outputb` decision procedure, `prefix_free`,
  and the main construction `bounded_output_repr_rel`
  (Lemma 31) showing bounded-output finite-state terms yield
  representable relations.

- **MM2 encoding** (`mm.v`): The full encoding of two-counter
  Minsky machine instructions as KA terms over the alphabet
  `{mm_a, mm_b, mm_q q}` (Definitions 11--13).  Includes
  `config_word`, `config_set`, `encode_instr`, `mm2_R`, and
  the connection to the MM2 library's step relation.

- **Step-level soundness and completeness** (`mm.v`):
  `encoding_complete` and `encoding_sound` prove that a single
  MM2 step corresponds exactly to membership in the transition
  relation `mm2_R`.  Lifted to reflexive-transitive closure as
  `encoding_rtc_complete` and `encoding_rtc_sound`.

- **Main soundness** (`mm2_R_soundness`, Theorem 15):
  If the machine halts and `red_lb s₁ ⊑ red_ub` holds, then it
  halts in state `(0,(0,0))`.

- **Main completeness** (`mm2_R_completeness`, Theorem 16):
  If the machine reaches `(0,(0,0))`, then `red_lb s₁ ⊑ red_ub`
  holds in every pre-Kleene algebra.  The proof uses
  `repr_rel_iter_final` together with determinism
  (`mm2_step_det`) and the absence of transitions from the halt
  state (`no_step_from_halt`).

### Not yet formalized

- **Effective inseparability and undecidability** (Theorems
  17--18): The diagonal argument constructing machine M_η and the
  final reduction to undecidability are not formalized.  These
  are largely machine-independent and could reuse existing
  library results.

## Structural differences

- **Algebraic hierarchy.** The paper uses standard
  definitions; the formalization builds the hierarchy from
  scratch with mixin records and stdpp coercions.

- **Commutativity model.** The paper uses abstract commutable
  sets with a relation ~.  The formalization uses product types
  `T * S` with `ka_term_inj1`/`ka_term_inj2` and projection
  morphisms `ka_term_proj1`/`ka_term_proj2`.

- **Machine model.** The paper defines abstract two-counter
  machines.  The formalization uses `mm2_instr` from
  coq-library-undecidability.

- **Proof style.** SSReflect tactics throughout.

- **KA axioms.** Same as the paper: left-biased pre-KA with
  only left-unfold `star x ≡ 1 ⊔ x ⋅ star x`.

- **Prefix-freeness.** The paper requires prefix-freeness for
  representable relations (Lemma 31).  The formalization
  avoids this by padding languages with a sentinel `None`;
  see below.

- **Finite automata.** Sketched in the paper's expansion
  section; fully developed in the formalization (`fsa`, `nfa`,
  product/star, `fsa_elem_k_decomp_gen`).

## Padding trick

The paper's Lemma 31 requires the language `L` to be
prefix-free.  Proving prefix-freeness of the configuration
language `T` directly would require reasoning about the
distinctness of `mm_a`, `mm_b`, and `mm_q q` symbols and the
structure of configuration words.

Instead, the formalization works with *padded* languages and
relations throughout: every word is extended with a sentinel
character `None` (the original symbols are wrapped in `Some`).
The padded language `pad_lang L` is automatically prefix-free
because every word ends with the unique terminator `None`.  This
is proved once as `prefix_free_pad_lang` in `bounded_output.v`
and used via the wrapper `bounded_output_repr_rel'`, which
upgrades `bounded_output_repr_rel` (Lemma 31) to work without
any prefix-freeness hypothesis on the original language.

The soundness and completeness theorems in `mm.v` work entirely
with padded terms (`pad_rel mm2_R`, `pad_lang T`), connecting
back to the unpadded MM2 step relation via `pad_rel_nsteps_2`
and `sqsubseteq_pad_lang_1`/`sqsubseteq_pad_lang_2`.

## Summary

The formalization covers the paper's core technical content:
the algebraic infrastructure, the encoding of Minsky machines
as KA terms, and the soundness/completeness theorems connecting
machine halting to term inequalities.  All proofs are complete
— there are no admitted lemmas.  The main gap relative to the
paper is the final undecidability result via effective
inseparability (Theorems 17--18).

[paper]: https://arxiv.org/pdf/2411.15979
