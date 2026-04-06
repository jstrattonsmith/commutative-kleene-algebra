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
(not yet formalized), this yields undecidability.

## File structure

The development is split into eight files with a linear
dependency chain (~6600 lines total):

- **`utils.v`** (284) — Finite enumeration utilities,
  `nsteps` helpers.
- **`algebra.v`** (896) — Algebraic hierarchy: setoids,
  monoids, semilattices, morphism classes.
- **`pre_ka.v`** (862) — Pre-Kleene algebras, free
  `ka_term` AST, `bool`/`count` instances.
- **`lang.v`** (402) — Language model, interpretation `l`,
  `l_alt` (Theorem 5), `l_inj_finite` (Corollary 7).
- **`automata.v`** (1062) — Finite-state automata,
  product/star constructions, expansion lemma.
- **`repr_rel.v`** (855) — Representable relations,
  `repr_rel_iter` (Lemma 21), `repr_rel_iter_empty`
  (Theorem 22), padding infrastructure.
- **`bounded_output.v`** (815) — Bounded-output terms
  (Definition 28), closure (Lemma 30),
  `bounded_output_repr_rel` (Lemma 31).
- **`mm.v`** (1419) — Minsky machine encoding
  (Definitions 11--13), soundness (Theorem 15),
  completeness (Theorem 16).

See [`paper-comparison.md`](paper-comparison.md) for a detailed
mapping between the paper and the formalization.

## Main results

All proofs are complete — there are no admitted lemmas.

- **`encoding_sound`** / **`encoding_complete`** (`mm.v`):
  A single step of a two-counter machine corresponds exactly to
  membership in the KA transition relation `mm2_R`.

- **`mm2_R_soundness`** (`mm.v`): If the machine halts and the
  encoding inequality `red_lb s₁ ⊑ red_ub` holds, then the
  machine halts in the zero state `(0,(0,0))`.

- **`mm2_R_completeness`** (`mm.v`): If the machine reaches
  `(0,(0,0))`, then the inequality `red_lb s₁ ⊑ red_ub` holds
  in every pre-Kleene algebra.

## Usage

Build with Nix flakes:

```bash
nix develop    # enter dev shell
make           # build all files
```

Individual files:

```bash
nix develop -c bash -c 'coqc -Q . kacc <file>.v'
```

## Dependencies

Declared in `flake.nix`:

- **Rocq** (from nixpkgs)
- **stdpp** — `base`, `list`, `finite`, `gmap`, `mapset`, `fin`
- **coq-library-undecidability** (branch `rocq-9.0`) — provides
  `Undecidability.MinskyMachines.MM2`

## License

The code contained in this repository is covered by
[`LICENSE`](./LICENSE).

[paper]: https://arxiv.org/pdf/2411.15979
