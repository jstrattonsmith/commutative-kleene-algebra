# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository.

## Project Overview

Rocq (formerly Coq) formalization proving undecidability results for Kleene
algebras with partial commutativity of concatenation (cf. ["Kleene algebra with
commutativity conditions is undecidable" by Azevedo de Amorim et al.,
2025][KACC], ). The proof is split across seven `.v` files (~4100 lines total).
Several references here are relative to the paper.

## Build Commands

This project uses Nix flakes:

```bash
nix develop   # enter dev shell (coq-lsp, vsrocq)
nix build     # build/typecheck the full project
```

Individual files can be compiled via:

```bash
nix develop -c bash -c 'coqc -Q . kacc <file>.v'
```

The build processes all files listed in `_CoqProject`.  There are no separate
test or lint commands -- the type checker is the test suite. To check if the
code is building correctly, make sure to check the exit status -- don't just
grep for errors.

After building, make sure you always report what lemmas were left admitted.

## Dependencies

Declared in `flake.nix` via Nix overlay:
- **Rocq/Coq** (from nixpkgs)
- **stdpp** -- provides `base`, `list`, `finite`, `gmap`, `mapset`
- **coq-library-undecidability** (branch `rocq-9.0`) -- provides
  `Undecidability.MinskyMachines.MM2` for Minsky machine definitions
- **MetaRocq** (transitive via coq-library-undecidability)

## File Structure

Files are listed in dependency order (`_CoqProject`):

1. **`utils.v`** (~256 lines): Finite enumeration of gmaps, gsets, list pairs,
   and lists of bounded length.

2. **`algebra.v`** (~811 lines): Custom algebraic hierarchy built on stdpp's
   `Equiv`/`SqSubsetEq` typeclasses: `setoid` -> `monoid` (with `MonoidMixin`)
   -> `semi_lattice` (with `SemiLatticeMixin`).  Morphism classes
   (`MonoidMorphism`, `SemiLatticeMorphism`) at each level.  Concrete instances:
   `bool`, product monoids.  `MonoidGen`/`SizedMonoid` typeclasses for generator
   structures.

3. **`pre_ka.v`** (~778 lines): Pre-Kleene algebra (`PreKAMixin` adding
   star/distribution/idempotency).  `PreKAMorphism` class. `ka_term T` free KA
   term AST (`Unit`, `ka_term_bottom`, `ka_term_join`, `ka_term_mul`,
   `ka_term_star`). Key operations: `ka_term_elim`, `count_term`, `has_one`,
   `pseudo_top`. Concrete instances: `count`, `lang`.

4. **`lang.v`** (~346 lines): `lang` record (formal languages over word monoids)
   with `l : ka_term T -> lang` interpreting terms as languages. Includes
   `l_alt` (Theorem 5: string membership <-> term ordering), `l_inj_finite`
   (Corollary 7), `either_empty_or_nonzero` (Corollary 8).

5. **`automata.v`** (~927 lines): FSA/NFA definitions: `fsa` record with
   `fsa_elem`, `fsa_state`, `fsa_interp`, `fsa_initial`, `fsa_trans`,
   `fsa_trans_s`. Product (`fsa_mul'`) and star (`fsa_star'`)
   constructions. `finite_state` predicate.  Expansion lemma
   `fsa_elem_k_decomp_gen` (Lemma 27).  `ka_term_proj1`, `ka_term_proj2`,
   `ka_term_diag`.  `string_match` / `string_match_complete_sized`.

6. **`repr_rel.v`** (~332 lines): Representable relations (`repr_rel` record
   with `next`, `residue`, `expand_rel`). `diff` term. Iteration lemmas
   (`repr_rel_iter`, Lemma 21; `repr_rel_iter_empty`, Theorem 22).

7. **`bounded_output.v`** (~676 lines): Bounded-output terms (Definition
   28). Closure under join, mul, star (Lemma 30). `bounded_outputb` boolean
   check.  Prefix-free terms (Definition 32). `list_diverge` (Lemma 33). Lemma
   31 (paper version): `lemma_31_paper` restricts the expansion to
   output-bounded suffix terms. Lemma 34 (`bounded_output_repr_rel`) partially
   proved (3 admits, 1 Admitted).

   **Not yet implemented:** MM2 encoding and the full
   undecidability reduction (Definitions 11-13,
   Theorems 15-16, 18).

## Style Guidelines

Several of these guidelines are guiding principles that are not necessarily
followed consistently throughout the code, but that should be respected as much
as possible, **especially by Claude**. Many coding conventions come from
[Ssreflect][ssreflect-tutorial], but we do not follow those thoroughly because
we're using stdpp, which follows different conventions, in particular regarding
naming.

- Lines are capped at 80 characters, including in Markdown files.
- Use **ssreflect** tactics (`move=>`, `rewrite`, `apply/`, `case/`, `elim:`,
  `/=`) extensively.  Avoid `destruct`, `induction`, `exfalso`, etc.
- The `congruence` tactic is allowed.
- `Set Implicit Arguments` is active -- beware that arguments inferable from
  later ones become implicit.  Use `@lemma_name` to pass all arguments
  explicitly. Avoid using `@` as much as possible.
- Custom scope `ka_scope` with notations: `⋅` for mul, `1` for one, `∏` for
  `mul_list`, `⨆` for join_list, `x ^ n` for power.  Join (`⊔`), star, ordering
  (`⊑`), and bottom (`⊥`) use stdpp typeclasses (`Join`, `Star`, `SqSubsetEq`,
  `Bottom`) rather than custom notations.

  [KACC]: https://arxiv.org/pdf/2411.15979
  [ssreflect-tutorial]: https://inria.hal.science/inria-00407778v1/document
