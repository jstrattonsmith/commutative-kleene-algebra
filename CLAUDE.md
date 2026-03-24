# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Rocq (formerly Coq) formalization proving undecidability results for Kleene algebras with partial commutativity of concatenation. The entire proof lives in a single file: `kacc_undec.v` (~4200 lines).

## Build Commands

This project uses Nix flakes. Enter the dev environment first:

```bash
nix develop          # enter dev shell (provides coq-lsp, vsrocq-language-server)
nix build            # build/typecheck the full project
```

The Nix build invokes `coqc` on `kacc_undec.v`. There are no separate test or lint commands — the type checker is the test suite.

## Dependencies

Declared in `flake.nix` via Nix overlay:
- **Rocq/Coq** (from nixpkgs)
- **stdpp** — provides `base`, `list`, `finite`, `gmap`, `mapset`
- **coq-library-undecidability** (branch `rocq-9.0`) — provides `Undecidability.MinskyMachines.MM2` for Minsky machine definitions
- **MetaRocq** (transitive via coq-library-undecidability)

## Architecture of `kacc_undec.v`

The file builds up algebraic infrastructure from scratch, then uses it to encode Minsky machine computations:

1. **Utility sections** (lines 1–260): Finite enumeration of gmaps, gsets, list pairs, and lists of bounded length.

2. **Setoids & algebraic hierarchy** (lines 265–880): Custom algebraic hierarchy built on stdpp's `Equiv`/`SqSubsetEq` typeclasses:
   - `setoid` → `monoid` (with `MonoidMixin`) → `semi_lattice` (with `SemiLatticeMixin`) → `pre_ka` (pre-Kleene algebra, with `PreKAMixin` adding star/distribution/idempotency)
   - Each structure is a record with a `_Mixin` bundling the laws. Morphism classes (`MonoidMorphism`, `SemiLatticeMorphism`, `PreKAMorphism`) are defined at each level.
   - Concrete instances: `bool`, `count`, `lang` (formal languages), product monoids.

3. **KA terms** (lines 1106–1620): `ka_term T` is a free KA term AST (`Unit`, `⊥`, `⊔`, `⋅`, `star`). Key operations:
   - `ka_term_elim`: fold/elimination into any `pre_ka`
   - `count_term`: counts whether a term is empty/finite/infinite
   - `has_one`, `finite_state`: boolean predicates on terms
   - `pseudo_top`: absorbing element for finite alphabets

4. **Language semantics** (lines 1623–1887): `lang` record (formal languages over word monoids) with `l : ka_term T → lang` interpreting terms as languages. Includes injectivity results (`l_inj_finite`).

5. **Automata** (lines 1889–2605): FSA/NFA definitions with:
   - `fsa_elem`: interpretation of an automaton as a KA term
   - `fsa_mul'`, `fsa_star'`: product and Kleene star constructions on automata
   - `finite_state` predicate characterizing terms representable by finite automata

6. **Derivatives & representable relations** (lines 2608–2690): Brzozowski-style derivatives on `ka_term (list T)`, plus `repr_rel` for representable relations.

7. **MM2 encoding & undecidability** (lines 2696–end): The core reduction:
   - Alphabet `Σ_M` with constructors `Q_M n`, `a`, `b`, `c_0`, `c_1`
   - `interp` / `interp_single`: encode MM2 instructions as KA terms
   - `R_M`: the full encoding of an MM2 program
   - `C_M`, `c_m_form_list`: configuration terms
   - Canonicalization pass (`canonicalize`) for term normalization
   - Projection functions `π_l`, `π_r` separating left/right components, with `proj_com` proving they commute

## Proof Style

- Uses **ssreflect** tactics (`move=>`, `rewrite`, `apply/`, `case/`, `elim:`, `/=`) extensively
- Custom scope `ka_scope` with notations: `⋅` for mul, `⊔`/`+` for join, `✶` for star, `⊑`/`≤` for ordering, `⊥`/`0` for bottom, `1` for one
- `↑s` lifts a string to a KA term; `##ls` sums a list of string terms; `s ∈ t` means string membership in a term's language
