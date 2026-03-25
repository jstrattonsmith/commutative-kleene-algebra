# Commutative Kleene Algebra

This repository contains Rocq files formalizing results related to the undecidability of Kleene algebras with partial commutativity of the concatenation operator, based on the CSL 2025 paper *"Kleene Algebra with Commutativity Conditions Is Undecidable"* (Azevedo de Amorim, Zhang, Gaboardi).

## File Structure

The development is split into six files with a linear dependency chain:

- **`utils.v`** — Finite enumeration utilities: enumeration of gmaps, gsets, list pairs, and bounded-length lists.
- **`algebra.v`** — Algebraic hierarchy built on stdpp: setoids, monoids (lists, products), semilattices (gsets), morphism classes.
- **`pre_ka.v`** — Pre-Kleene algebras and free KA terms: `pre_ka`, `ka_term`, `PreKAMorphism`, `ka_term_elim`, `ka_term_ext` (universal property), `has_one`, `pseudo_top`. Includes `bool` and `count` instances.
- **`lang.v`** — Language semantics: `lang` (formal languages over monoids), interpretation `l : ka_term T → lang`, `l_alt`, functoriality (`lang_map`), naturality (`l_natural`).
- **`automata.v`** — Finite-state automata: `fsa`, `nfa`, product/star constructions, `fsa_elem` interpretation, `ka_term_diag_spec`, `finite_state` predicate.
- **`repr_rel.v`** — Representable relations and bounded output: `repr_rel`, `bounded_output`, closure lemmas (Lemma 30), `bounded_outputb`, `repr_rel_iter` (Lemma 21), `repr_rel_iter_empty` (Theorem 22).

## Usage

Build with Nix flakes:

```bash
nix develop    # enter dev shell
make           # build all files
```

## License

The code contained in this repository is covered by [`LICENSE`](./LICENSE).
