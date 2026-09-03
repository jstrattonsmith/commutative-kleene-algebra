Project: kacc_undec (Rocq / Coq)

Rocq formalization proving undecidability results for Kleene algebras with
partial commutativity of concatenation (cf. "Kleene algebra with
commutativity conditions is undecidable", Azevedo de Amorim et al. 2025,
https://arxiv.org/pdf/2411.15979). See `../CLAUDE.md` for the authoritative,
kept-up-to-date project overview, file-by-file structure, dependencies, and
style guide -- this file is a shorter Copilot-oriented supplement, not a
replacement.

The development is organized into two reusable libraries, `KA/` (the
paper's own pre-Kleene-algebra framework) and `MM2/` (a thin
Church's-Thesis-witness wrapper around `coq-library-undecidability`'s own
MM2 simulator -- the bulk of MM2's own execution-model machinery lives
upstream there, not in this repo), plus `CKAUndec/` (the actual
MM2-as-KA-terms payoff and the effective-inseparability/completeness
argument built on it). All of it is admit-free; the completeness argument's
final step is conditional on two named hypotheses (`CT_L`, `MP`), isolated
to `CKAUndec/KMComplete.v`, nowhere else.

Quick start (dev shell)
- Use Nix flakes (there is no `shell.nix`):

```bash
nix develop
```

- Build/typecheck everything: `nix build`
- Compile one file: `nix develop -c bash -c 'coqc -Q . kacc <file>.v'`
- Fast local iteration (persists `.vo` across runs, unlike `nix build`'s
  sandbox): `nix develop -c make -j4` -- but always confirm with a real
  `nix build` before considering something verified.

Key components and where to look
- `CKAUndec/Encoding.v`: the MM2-as-KA-terms encoding (Definitions 11-13)
  and the soundness/completeness pair (`mm2_R_completeness`/
  `mm2_R_soundness`, Theorems 15-16) everything downstream builds on.
- `CKAUndec/K.v`: Theorem 17 (effective inseparability), the project's
  stated primary goal.
- `CKAUndec/KMComplete.v` / `CKAUndec/BinaryAlphabetMComplete.v`:
  Sigma^0_1-completeness, conditional on `CT_L`/`MP` -- read
  `KMComplete.v`'s header comment for exactly why each is needed.
- `flake.nix`: Nix dev environment. Depends on `coq-library-undecidability`
  (a fork, pinned via `github:`; Minsky machines, FRACTRAN, Rocq's `L`
  language, plus MM2 simulator/compiler content migrated there from this
  project) and `coq-synthetic-computability` (a collaborator's repo, also
  pinned via `github:`, not a local path -- relative `path:` inputs don't
  resolve across independent sibling git repos under Nix flakes), which
  supplies `T_L`/`θ_L`/`CT_L` and the generic effective-inseparability
  machinery the computability half is built on.
- `notes.md`: developer TODOs, design questions and decisions.

Project-specific patterns and conventions
- Sections: many components are defined inside `Section ...` blocks.
  Definitions built inside sections close over section variables; explicit
  argument instantiation (or `@lemma_name` to force everything explicit) is
  often needed when reusing them outside the original section.
- `Set Implicit Arguments` is active in some files (e.g. `CKAUndec/Encoding.v`)
  but not others -- and can leak from an imported file that sets it at its
  own top level, outside any `Section` (a plain top-level `Lemma`/
  `Definition` declared after such a `Require Import` gets its own
  arguments silently made implicit too; a `Section` `Variable` does not
  have this problem, staying explicit once the section closes regardless).
  If a direct term application throws "term X has type Y but expected
  (unrelated hypothesis's type)", suspect this before assuming a real type
  error, and try prefixing with `@` to force every argument explicit and
  positional.
- Two-tiered semantics vs syntax (`KA/`): the code distinguishes computable
  boolean/inductive syntactic predicates (e.g. `finite_state : ka_term ->
  bool`) from semantic equivalence under `ka_eq`. Prefer adding small
  decision functions (e.g. `count_leq`) and proving lemmas connecting the
  boolean check to `ka_eq` (`count_finiteP`, `count_emptyP`).
- Interpreter fold: `ka_term_elim` is the canonical fold over `ka_term`. Use
  it to build interpreters (`ka_term_map`, `count_term`); it does not
  normalize syntax.
- Style split: `KA/` uses ssreflect tactics (`move=>`, `rewrite`, `apply/`,
  `case/`, `elim:`) extensively. `MM2/` and `CKAUndec/` deliberately use
  plain Coq tactics (`intros`, `destruct`, `apply`) instead, since they
  interface directly with `coq-synthetic-computability`'s own plain-tactic
  style.

Build / proof workflow
- `nix develop` then `coqc`/`coqtop`, or an LSP-enabled editor (`coq-lsp` /
  `vsrocq-language-server`, both in the dev shell).
- `nix build` processes every file listed in `_CoqProject`, in the order
  listed there. Check the exit status, not just grep output, to confirm a
  build succeeded -- and never check it via a pipe through `tail`/`tee`
  (that reports the pipe stage's own exit code, not the build's; use
  `nix build > log 2>&1; echo "EXIT: $?"` and grep the log instead).
- The sibling `coq-synthetic-computability` project has its own build (a
  separate Nix derivation) that regenerates its own file list via `find`
  at build time -- adding a new file under its `theories/` needs no
  build-file patch there, unlike this project's own `_CoqProject`.
- After building, report what (if anything) was left `Admitted` --
  currently nothing is, anywhere in this repo or in the new content added
  to either sibling.

Debugging and common gotchas
- Section-bound definitions: if a value fails to type-check when reused
  externally, check which `Section` it was defined in and either re-import
  with explicit parameters or inline the definition.
- `Set Implicit Arguments` surprises: see above -- try `@` first before
  assuming a real type error, and check whether the flag is coming from an
  imported file rather than this one.
- Syntax vs semantic checks (`KA/`): when determining facts like
  "term ⊑ 1", look for an existing semantic interpreter (e.g. `count_term`)
  and an associated lemma (`count_finiteP`) relating it to the semantic
  property, rather than attempting large-scale normalization.
- `red_leq`/`R_target` (`CKAUndec/Encoding.v`) is a KA-term *safety*
  property, not a termination witness -- there is deliberately no
  "red_leq implies halts" direction (that would make the problem
  decidable). Don't define an enumerable set directly via `R_target`;
  go through `A0_L` (already enumerable, `coq-synthetic-computability`'s
  `L`-level construction) and `CKAUndec/Glue/TLToRTarget.v`'s
  `R_TL_R_target_connection` instead, using `R_target`'s easy
  (halts-implies-safe) direction only.
- A literal `*)` inside a Coq comment's own prose (e.g. writing "`L.*`" to
  mean "everything under the `L` namespace") closes the comment early and
  produces a confusing syntax error downstream, not at the `*)` itself.
- MetaRocq's `extract` tactic does not reliably bridge a `computableExt`-
  registered `computable` instance across a file boundary, even when the
  exact same proof works fine colocated with the function it extracts --
  if a `computable` proof fails with "could not infer any instance" for a
  function defined in another file, this is likely why; the fix is
  colocating the instance with the definition, not an import/ordering fix.

If unsure, ask about
- Which section boundary a helper was originally defined in.
- Whether a goal needs a computable decision or a semantic `Prop` (changes
  the recommended approach).
- Whether new work belongs in this project, in `coq-library-undecidability`,
  or in `coq-synthetic-computability` -- generic MM2/Minsky-machine facts
  belong in the former; generic/model-independent computability facts
  belong in the latter; anything KA-term- or MM2-as-KA-terms-encoding-
  specific belongs here.
