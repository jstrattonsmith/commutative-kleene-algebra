Project: kacc_undec (Rocq / Coq)

This repository contains a large Coq development written against the Rocq/Coq ecosystem. The main source is a single large file `kacc_undec.v` that builds Kleene-algebra/automata machinery and undecidability arguments.

Quick start (dev shell)
- Use Nix flakes or `shell.nix` to reproduce the developer environment.
- Enter the flake devshell (preferred):

```bash
nix develop
```

- Or with `shell.nix`:

```bash
nix-shell
```

Key components and where to look
- `kacc_undec.v`: the canonical large source; contains core definitions: `ka_term`, `ka_eq`, `ka_term_elim`, `count`, `count_term`, `fsa`, automata helpers, and many lemmas.
- `flake.nix` / `shell.nix`: Nix-based dev environment. Important packages: `rocq-core`, `vsrocq-language-server`, and `coq-library-undecidability` (as an input in the flake).
- `notes.md`: developer TODOs, design questions and decisions (useful context for intent and TODOs).

Project-specific patterns and conventions
- Rocq / Coq + Sections: Many components are defined inside `Section ...` blocks. Be careful: definitions built inside sections close over section variables; explicit type/argument instantiation (or inline record construction) is often needed when reusing them outside the original section.
- Two-tiered semantics vs syntax: The code frequently distinguishes computable boolean/inductive syntactic predicates (e.g. `finite_state : ka_term → bool`) from semantic equivalence under `ka_eq` (an Equiv). When modifying checks, prefer adding small decision functions (e.g. `count_leq`) and prove lemmas connecting the boolean check with semantic `ka_eq` using `count_finiteP` / `count_emptyP`.
- Interpreter fold: `ka_term_elim` is the canonical fold over `ka_term`. Use it to build interpreters (`ka_term_map`, `count_term`), but remember it does not normalize syntax.
- Small finite ADT pattern: `count` is a tiny algebraic type (CountEmpty/CountFinite/CountStarred) used as a cheap semantic classifier — search for `count_term`, `count_finiteP` for examples of turning semantic facts into decidable checks.
- Automata: `fsa` is a record with fields `fsa_state`, `fsa_elem`, `fsa_interp`, `fsa_trans`, etc. Helper construction `fsa_singleton` exists but captures its `Automata` section context — prefer constructing the record inline when used in a different section or use `@fsa_singleton` with full explicit arguments.

Build / proof workflow
- Use the Nix dev shell then your usual Coq tools: `coqc`, `coqtop`, or an LSP-enabled editor (VS Code + `vsrocq-language-server` / `vscoq`).
- There is no Makefile in the repo — rely on your editor or run `coqtop -R . MyProject -I . kacc_undec.v` style commands.

Debugging and common gotchas
- Section-bound definitions: If a value fails to type-check when reused externally, inspect where the original was defined (inside which `Section`) and either re-import with explicit parameters or inline the record/definition.
- Syntax vs semantic checks: When the code needs to determine facts like “term ≡ 1”, check for an existing semantic interpreter (e.g. `count_term`) and an associated lemma (`count_finiteP`) that relates the interpreter's result to the semantic property. Prefer adding a small `bool`-valued decision function when you must use it inside computable `Fixpoint`s.
- Program obligations: the file uses `Program Definition` for some records (e.g. `fsa_singleton`) and will generate obligations. When modifying those definitions, run proof obligations in order and re-check with `coqc` or your editor until obligations are discharged.

Examples (patterns to replicate)
- Interpreting a term to `count` (decision-friendly classifier): see `count_term` + `count_finiteP`.
- Building an FSA inline where section parameters don't match: manually construct a `fsa` record with `fsa_state := option bool` and fill `fsa_interp`, `fsa_trans`, `fsa_final`, `fsa_initial` as in the file's `fsa_singleton` definition.

Where to start when adding/changing proofs
- Open `kacc_undec.v` and locate the target lemma. Read related helper lemmas (`*_P` lemmas) nearby — these usually encode the exact bridge between a boolean decision and a semantic `ka_eq` property.
- When you need a computable check but only have a `Prop`, look for a small algebraic classifier (like `count`) and a lemma that connects it to the property. If none exists, add a tiny ADT + lemma pair rather than attempt large normalization.

If unsure, ask about
- Which section boundary the original helper was defined in (we can inline or re-export with explicit args).
- Whether the goal needs a computable decision or a semantic `Prop` (this changes the recommended approach).

Please review and tell me if you'd like this shortened, expanded with more code snippets, or tailored to a specific contributor workflow (editor/CI commands).
