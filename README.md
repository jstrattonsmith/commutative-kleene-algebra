# Commutative Kleene Algebra

Rocq formalization of the theory of Kleene algebra with partial
commutativity of concatenation, based on the CSL 2025 paper
[*"Kleene Algebra with Commutativity Conditions Is
Undecidable"*][paper] (Azevedo de Amorim, Zhang, Gaboardi).
The development covers pre-Kleene algebras, free KA terms,
language semantics, finite automata, and representable
relations.

As an application, the development encodes two-counter Minsky
machines as pre-Kleene-algebra terms and proves soundness and
completeness of the encoding: a machine halts in the zero state
if and only if a certain inequality holds in the language model.
Combined with effective inseparability of the halting problem
(fully formalized -- see Main results below), this yields
undecidability, and in fact Sigma^0_1-completeness.

This repository is meant to sit alongside its two sibling
dependencies, `coq-library-undecidability` and
`coq-synthetic-computability`, as independent git repos under a
common parent directory -- see `CLAUDE.md` for exactly how they
fit together and why.

## File structure

The development is organized into two reusable libraries (`KA/`, `MM2/`)
plus the CKA-specific payoff (`CKAUndec/`) that combines them with a third,
external dependency (`coq-synthetic-computability`'s effective-inseparability
machinery). See [`CLAUDE.md`](CLAUDE.md) for the full file-by-file
breakdown and [`paper-comparison.md`](paper-comparison.md) for a detailed
mapping between the paper and the formalization.

- **`KA/`** -- the paper's own pre-Kleene-algebra framework: utilities,
  the algebraic hierarchy, free `ka_term` syntax, language semantics,
  finite automata, representable relations, and the binary-alphabet
  embedding.
- **`MM2/`** -- a thin Church's-Thesis-witness wrapper around
  `coq-library-undecidability`'s own MM2 (two-counter machine) simulator
  (the pure MM2 execution-model machinery itself lives upstream, in
  `coq-library-undecidability`, since it's reusable independent of this
  project).
- **`CKAUndec/`** -- the actual payoff: encodes MM2 as KA terms
  (Definitions 11-13), proves soundness/completeness (Theorems 15-16),
  and builds up effective inseparability (Theorem 17) and
  Sigma^0_1-completeness of the KA-term inequality (Theorems 18-19), both
  over the machine-specific alphabet and the paper's own canonical
  2-symbol alphabet.

## Main results

All proofs are complete -- there are no admitted lemmas anywhere in the
development. No axioms appear except two named, standard hypotheses
(`CT_L`, Church's Thesis for Rocq's `L` language; `MP`, Markov's
Principle), both isolated to `CKAUndec/KMComplete.v`, needed only for the
final Sigma^0_1-completeness step.

- **`mm2_R_soundness`** / **`mm2_R_completeness`** (`CKAUndec/Encoding.v`):
  soundness and completeness of the MM2-as-KA-terms encoding (paper
  Theorems 15-16) -- a machine reaches `(0,(0,0))` if and only if the
  encoding inequality `red_lb ⊑ red_ub` holds.
- **`CKAUndec/K.v`**: effective inseparability of the KA-term inequality
  problem (paper Theorem 17), admit- and axiom-free.
- **`CKAUndec/KMComplete.v`** / **`CKAUndec/BinaryAlphabetMComplete.v`**:
  Sigma^0_1-completeness of the KA-term inequality, both per-machine and
  over the paper's own fixed canonical alphabet (paper Theorems 18-19),
  conditional on `CT_L`/`MP`.

## Usage

Build with Nix flakes:

```bash
nix develop    # enter dev shell
nix build      # build/typecheck everything
```

Individual files:

```bash
nix develop -c bash -c 'coqc -Q . kacc <file>.v'
```

## Dependencies

Declared in `flake.nix`, pinned via `github:` inputs to a fork and a
collaborator's repo respectively -- see `CLAUDE.md`'s Dependencies section
for exactly what each provides and why they're pinned this way rather than
via a local path:

- **Rocq** (from nixpkgs)
- **stdpp** -- `base`, `list`, `finite`, `gmap`, `mapset`, `fin`
- **coq-library-undecidability** (a fork, branch `enable-L-nix-9.0`) --
  `Undecidability.MinskyMachines.MM2` and friends, Rocq's own `L` language,
  and (as of 2026-08-31) reusable MM2 simulator/compiler content originally
  developed for this project
- **coq-synthetic-computability** (a collaborator's repo) -- `T_L`/`CT_L`
  and the generic + `L`-specific effective-inseparability/reducibility-degree
  machinery the computability half of this project is built on

## License

The code contained in this repository is covered by
[`LICENSE`](./LICENSE).

[paper]: https://arxiv.org/pdf/2411.15979
