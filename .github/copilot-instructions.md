Project: kacc_undec (Rocq / Coq)

Rocq formalization proving undecidability results for Kleene algebras with
partial commutativity of concatenation (cf. "Kleene algebra with
commutativity conditions is undecidable", Azevedo de Amorim et al. 2025,
https://arxiv.org/pdf/2411.15979). See `../CLAUDE.md` for the authoritative,
kept-up-to-date project overview, file-by-file structure, dependencies, and
style guide -- this file is a shorter Copilot-oriented supplement, not a
replacement.

The development is **not** a single file. It's 21 files listed in dependency
order in `_CoqProject`, split into an algebraic core (`utils.v` through
`mm.v`, the paper's own pre-Kleene-algebra framework plus the MM2-as-KA-terms
encoding) and a computability argument (`EffectiveInseparability_MM2.v`
through `Theorem19_MComplete.v`, proving effective inseparability and
Sigma^0_1-completeness). All of it is admit-free; the computability argument's
final step (`Theorem19_MComplete.v`) is conditional on two named hypotheses
(`CT_L`, `MP`), nowhere else.

Quick start (dev shell)
- Use Nix flakes (there is no `shell.nix`):

```bash
nix develop
```

- Build/typecheck everything: `nix build`
- Compile one file: `nix develop -c bash -c 'coqc -Q . kacc <file>.v'`

Key components and where to look
- `mm.v`: the MM2-as-KA-terms encoding (Definitions 11-13) and the
  soundness/completeness pair (`mm2_R_completeness`/`mm2_R_soundness`,
  Theorems 15-16) everything downstream builds on.
- `Theorem17_KATerm.v` / `Theorem17_Full.v`: Theorem 17 (effective
  inseparability), the project's stated primary goal.
- `Theorem19_MComplete.v`: Sigma^0_1-completeness, conditional on `CT_L`/`MP`
  -- read its header comment for exactly why each is needed.
- `flake.nix`: Nix dev environment. Depends on `coq-library-undecidability`
  (Minsky machines, FRACTRAN, Rocq's `L` language) and a sibling project,
  `coq-synthetic-computability` (consumed as a local path flake input),
  which supplies `T_L`/`θ_L`/`CT_L` and the generic effective-inseparability
  machinery the computability half is built on.
- `notes.md`: developer TODOs, design questions and decisions.

Project-specific patterns and conventions
- Sections: many components are defined inside `Section ...` blocks.
  Definitions built inside sections close over section variables; explicit
  argument instantiation (or `@lemma_name` to force everything explicit) is
  often needed when reusing them outside the original section.
- `Set Implicit Arguments` is active project-wide (inherited transitively
  from `coq-library-undecidability`'s `mma_defs.v`/`mma_utils.v`, which never
  unset it) -- it silently makes strict/inferable arguments implicit even in
  unrelated files that merely import those transitively. If a direct term
  application throws "term X has type Y but expected (unrelated
  hypothesis's type)", prefix the application with `@` to force every
  argument explicit and positional.
- Two-tiered semantics vs syntax (algebraic core, files 1-9): the code
  distinguishes computable boolean/inductive syntactic predicates (e.g.
  `finite_state : ka_term -> bool`) from semantic equivalence under `ka_eq`.
  Prefer adding small decision functions (e.g. `count_leq`) and proving
  lemmas connecting the boolean check to `ka_eq` (`count_finiteP`,
  `count_emptyP`).
- Interpreter fold: `ka_term_elim` is the canonical fold over `ka_term`. Use
  it to build interpreters (`ka_term_map`, `count_term`); it does not
  normalize syntax.
- Style split: files 1-9 (algebraic core) use ssreflect tactics
  (`move=>`, `rewrite`, `apply/`, `case/`, `elim:`) extensively. Files 10-18
  (the computability argument) deliberately use plain Coq tactics (`intros`,
  `destruct`, `apply`) instead, since they interface directly with
  `coq-synthetic-computability`'s own plain-tactic style.

Build / proof workflow
- `nix develop` then `coqc`/`coqtop`, or an LSP-enabled editor (`coq-lsp` /
  `vsrocq-language-server`, both in the dev shell).
- `nix build` processes every file listed in `_CoqProject`, in the order
  listed there. Check the exit status, not just grep output, to confirm a
  build succeeded.
- The sibling `coq-synthetic-computability` project has its own build (a
  separate Nix derivation) that regenerates its own file list via `find`
  at build time -- adding a new file under its `theories/` needs no
  build-file patch there, unlike this project's own `_CoqProject`.
- After building, report what (if anything) was left `Admitted` --
  currently nothing is.

Debugging and common gotchas
- Section-bound definitions: if a value fails to type-check when reused
  externally, check which `Section` it was defined in and either re-import
  with explicit parameters or inline the definition.
- `Set Implicit Arguments` surprises: see above -- try `@` first before
  assuming a real type error.
- Syntax vs semantic checks (algebraic core): when determining facts like
  "term ⊑ 1", look for an existing semantic interpreter (e.g. `count_term`)
  and an associated lemma (`count_finiteP`) relating it to the semantic
  property, rather than attempting large-scale normalization.
- `red_leq`/`R_target` (computability argument) is a KA-term *safety*
  property (language containment), not a termination witness -- there is
  deliberately no "red_leq implies halts" direction in `mm.v` (that would
  make the KA-term problem decidable). Don't try to define an enumerable set
  directly via `R_target`; go through the step-indexed simulator in
  `EffectiveInseparability_MM2.v` instead, and bring `R_target` in only via
  the halts-implies-safe direction.

If unsure, ask about
- Which section boundary a helper was originally defined in.
- Whether a goal needs a computable decision or a semantic `Prop` (changes
  the recommended approach).
- Whether new work belongs in this project or in the sibling
  `coq-synthetic-computability` project -- generic/model-independent
  computability facts belong there; anything KA-term- or MM2-encoding-
  specific belongs here.
