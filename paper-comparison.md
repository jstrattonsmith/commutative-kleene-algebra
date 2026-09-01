# Paper vs. Rocq Development: Comparison

This document compares the CSL 2025 paper [*"Kleene Algebra
with Commutativity Conditions Is Undecidable"*][paper] (Azevedo
de Amorim, Zhang, Gaboardi) with the Rocq formalization in this
repository (plus its two sibling dependencies,
`coq-library-undecidability` and `coq-synthetic-computability --
see `CLAUDE.md` for how the three fit together).

## What the paper proves

The paper shows that the equational theory of Kleene algebra
(and even pre-Kleene algebra) with commutativity conditions on
atomic terms is undecidable. The proof reduces the halting
problem for two-counter (Minsky) machines to equational
reasoning, then uses effective inseparability to obtain
undecidability, and adapts Kuznetsov's ICTAC 2023 argument to get
Sigma^0_1-completeness. The argument has four main parts:

1. **Soundness** (Theorem 15): If a machine halts in the zero
   state, a certain inequality holds in the regular language
   model.
2. **Completeness** (Theorem 16): If a machine halts in the
   zero state, the same inequality holds in *all* pre-Kleene
   algebras (no induction axioms needed).
3. **Effective inseparability** (Theorem 17): The sets of
   machines halting with output 0 vs. 1 are effectively
   inseparable, so no computable decision procedure exists.
4. **Sigma^0_1-completeness** (Theorems 18-19): The KA-term
   inequality problem is Sigma^0_1-complete, both for a
   machine-specific alphabet and for the paper's own fixed,
   canonical two-symbol alphabet.

## What the Rocq development covers

**Everything above is fully formalized**, admit-free, with only
two axioms in the entire development (`CT_L`, Church's Thesis for
Rocq's `L` language, and `MP`, Markov's Principle -- both isolated
to `CKAUndec/KMComplete.v`, needed only for the final
Sigma^0_1-completeness step).

### Parts 1-2: the algebraic infrastructure and the encoding (`KA/`, `CKAUndec/Encoding.v`)

- **Algebraic hierarchy** (`KA/algebra.v`): `setoid` → `monoid` →
  `semi_lattice`, including mixin records, morphism classes, and
  concrete instances (`bool`, product monoids, `gset`).
  Corresponds to the paper's Section 2 but is more elaborate,
  building the hierarchy from scratch on top of stdpp.

- **Free KA terms** (`KA/pre_ka.v`): The full `ka_term` AST with
  `Unit`, `⊥`, `⊔`, `⋅`, `star`, the universal elimination map
  `ka_term_elim`, and proof that `ka_term T` forms a `pre_ka`.
  Also includes `count` and `bool` pre-KA instances. The paper
  treats free terms abstractly; the formalization provides a
  concrete inductive type.

- **Language semantics** (`KA/lang.v`): The `lang` record and
  interpretation `l : ka_term T → lang`, with injectivity on
  finite terms (`l_inj_finite`, Corollary 7) and the string
  membership characterization (`l_alt`, Theorem 5).

- **Finite automata** (`KA/automata.v`): `fsa`/`nfa` records with
  join, product (`fsa_mul'`), and Kleene star (`fsa_star'`)
  constructions, plus the key decomposition lemma
  (`fsa_elem_k_decomp_gen`, Lemma 27). Also: `ka_term_proj1`,
  `ka_term_proj2`, `ka_term_diag`, and `finite_state`.

- **Representable relations** (`KA/repr_rel.v`): The `repr_rel`
  record (Section 5) with `next`, `residue`, and `expand_rel`
  fields. Iteration lemmas `repr_rel_iter` (Lemma 21) and
  `repr_rel_iter_empty` (Theorem 22). Also: padding
  infrastructure (`pad_lang`, `pad_rel`) and the final iteration
  lemma `repr_rel_iter_final`.

- **Bounded-output terms** (`KA/bounded_output.v`): `bounded_output`
  (Definition 28), closure under join/mul/star (Lemma 30),
  `bounded_outputb` decision procedure, `prefix_free`,
  and the main construction `bounded_output_repr_rel`
  (Lemma 31) showing bounded-output finite-state terms yield
  representable relations.

- **MM2 encoding** (`CKAUndec/Encoding.v`): The full encoding of
  two-counter Minsky machine instructions as KA terms over the
  alphabet `{mm_a, mm_b, mm_q q}` (Definitions 11-13). Includes
  `config_word`, `config_set`, `encode_instr`, `mm2_R`, and
  the connection to `coq-library-undecidability`'s MM2 step
  relation (via this repo's own `MM2/` wrapper).

- **Step-level soundness and completeness** (`CKAUndec/Encoding.v`):
  `encoding_complete` and `encoding_sound` prove that a single
  MM2 step corresponds exactly to membership in the transition
  relation `mm2_R`. Lifted to reflexive-transitive closure as
  `encoding_rtc_complete` and `encoding_rtc_sound`.

- **Main soundness** (`mm2_R_soundness`, Theorem 15):
  If the machine halts and `red_lb s₁ ⊑ red_ub` holds, then it
  halts in state `(0,(0,0))`.

- **Main completeness** (`mm2_R_completeness`, Theorem 16):
  If the machine reaches `(0,(0,0))`, then `red_lb s₁ ⊑ red_ub`
  holds in every pre-Kleene algebra. The proof uses
  `repr_rel_iter_final` together with determinism
  (`mm2_step_det`) and the absence of transitions from the halt
  state (`no_step_from_halt`).

### Parts 3-4: effective inseparability and completeness (`CKAUndec/K.v`, `KMComplete.v`, `BinaryAlphabet*.v`)

- **Effective inseparability** (`CKAUndec/K.v`, Theorem 17): `K`
  (the genuine `red_lb ⊑ red_ub` KA-term-level decision problem,
  via `R_target`) is effectively inseparable from `B1_L`, in the
  unbundled sense both this paper and Kuznetsov state their own
  Theorem 17/Definition 5 in (disjointness plus a witness
  function, no enumerability required). Then upgraded
  (`CKAUndec/KEnumerable.v`) to the fully bundled notion once `K`'s
  own enumerability is shown, via a generic "finitary
  axiomatization gives r.e." argument (`KA/enumerable.v`) applied
  to the encoding's own carrier monoid.

- **Sigma^0_1-completeness** (`CKAUndec/KMComplete.v`, Theorems
  18-19 discussion): Myhill's theorem (`creative`/`m-complete`,
  reused from `coq-synthetic-computability`'s generic machinery)
  applied to `K`, then composed with the reduction
  `K ⪯ₘ KA_ineq` to get Sigma^0_1-completeness of the *actual*
  KA-term inequality relation, not just its `K`-slice. Conditional
  on `CT_L` and `MP`, each entering at one precisely identified
  point (see `KMComplete.v`'s own header comment).

- **The canonical alphabet** (`CKAUndec/BinaryAlphabet.v`,
  `BinaryAlphabetMComplete.v`, Theorem 18/19 as literally stated
  in the paper): the machine-specific alphabet result above is
  transported to the paper's own fixed, minimal two-symbol
  alphabet `{0,1}` via a binary embedding
  (`KA/BoundedOutputTransport.v`), re-running the soundness/
  completeness argument at the embedded level to get order-
  *reflection*, not just preservation -- closing with
  `KA_ineq_bin_m_complete`, needing no existential over the
  machine (a single fixed embedded carrier, matching how the
  paper itself states Theorem 18 once, not per machine).

## Structural differences

- **Algebraic hierarchy.** The paper uses standard
  definitions; the formalization builds the hierarchy from
  scratch with mixin records and stdpp coercions.

- **Commutativity model.** The paper uses abstract commutable
  sets with a relation ~. The formalization uses product types
  `T * S` with `ka_term_inj1`/`ka_term_inj2` and projection
  morphisms `ka_term_proj1`/`ka_term_proj2`.

- **Machine model.** The paper defines abstract two-counter
  machines. The formalization uses `mm2_instr` from
  `coq-library-undecidability`.

- **Proof style.** SSReflect tactics in `KA/`; plain Coq tactics
  in `MM2/`/`CKAUndec/`, matching `coq-synthetic-computability`'s
  own style at that interface.

- **KA axioms.** Same as the paper: left-biased pre-KA with
  only left-unfold `star x ≡ 1 ⊔ x ⋅ star x`.

- **Prefix-freeness.** The paper requires prefix-freeness for
  representable relations (Lemma 31). The formalization
  avoids this by padding languages with a sentinel `None`;
  see below.

- **Finite automata.** Sketched in the paper's expansion
  section; fully developed in the formalization (`fsa`, `nfa`,
  product/star, `fsa_elem_k_decomp_gen`).

- **The computability model for Theorem 17-19.** The paper's own
  proof is model-agnostic about which "every enumerable set has an
  index" numbering it uses. The formalization commits to a
  specific, concrete one throughout (Rocq's own `L` calculus, via
  `T_L`/`θ_L`), so that every step except the very last is an
  explicit, hand-built construction rather than a non-constructive
  existence claim -- `CT_L` (Church's Thesis specifically for `L`)
  is needed only at the single point where the argument must
  reason about an arbitrary, unspecified enumerable set.

## Padding trick

The paper's Lemma 31 requires the language `L` to be
prefix-free. Proving prefix-freeness of the configuration
language `T` directly would require reasoning about the
distinctness of `mm_a`, `mm_b`, and `mm_q q` symbols and the
structure of configuration words.

Instead, the formalization works with *padded* languages and
relations throughout: every word is extended with a sentinel
character `None` (the original symbols are wrapped in `Some`).
The padded language `pad_lang L` is automatically prefix-free
because every word ends with the unique terminator `None`. This
is proved once as `prefix_free_pad_lang` in `KA/bounded_output.v`
and used via the wrapper `bounded_output_repr_rel'`, which
upgrades `bounded_output_repr_rel` (Lemma 31) to work without
any prefix-freeness hypothesis on the original language.

The soundness and completeness theorems in `CKAUndec/Encoding.v`
work entirely with padded terms (`pad_rel mm2_R`, `pad_lang T`),
connecting back to the unpadded MM2 step relation via
`pad_rel_nsteps_2` and `sqsubseteq_pad_lang_1`/`sqsubseteq_pad_lang_2`.

## Summary

The formalization covers the paper's full technical content: the
algebraic infrastructure, the encoding of Minsky machines as KA
terms, the soundness/completeness theorems connecting machine
halting to term inequalities, effective inseparability, and
Sigma^0_1-completeness over both a machine-specific alphabet and
the paper's own canonical two-symbol alphabet. All proofs are
complete -- there are no admitted lemmas anywhere in the
development, and the only axioms are the two named, standard
hypotheses (`CT_L`, `MP`) the completeness result is conditional
on, isolated to a single file.

[paper]: https://arxiv.org/pdf/2411.15979
