# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository.

## Project Overview

Rocq (formerly Coq) formalization proving undecidability results for Kleene
algebras with partial commutativity of concatenation (cf. ["Kleene algebra with
commutativity conditions is undecidable" by Azevedo de Amorim et al.,
2025][KACC]). Several references here are relative to the paper.

This repository lives inside `mech-eff-insep/`, alongside its two sibling
dependencies as independent git repos:
- `coq-library-undecidability` (a fork, branch `enable-L-nix-9.0`) --
  Minsky-machine/FRACTRAN definitions, `L` (Rocq's own untyped lambda
  calculus, used for extraction/Church's-Thesis witnesses), and a growing
  set of genuinely reusable MM2 (two-counter machine) machinery originally
  built for this project (see MM2/ below).
- `coq-synthetic-computability` (a collaborator's repo) -- generic
  synthetic-computability theory (`T_L`/`CT_L`, effective inseparability,
  reducibility degrees), including a set of files originally built for
  this project too (see Dependencies below).

The development is organized into `MM2/` (small CKA-specific glue, plus
a `Legacy/` evaluator wrapper not on the critical path), `KA/` (the
paper's own pre-Kleene-algebra framework and binary-alphabet embedding,
independent of `MM2/`/`CKAUndec/`), and `CKAUndec/`/`CKAUndec/Glue/`
(the actual MM2-as-KA-terms payoff) -- see File Structure below for the
file-by-file breakdown of each.

This whole development depends heavily on the sibling
`coq-synthetic-computability` project (see Dependencies below) -- in
particular its `T_L`/`θ_L` step-indexed interpreter for `L` and its generic
effective-inseparability/reducibility-degree machinery.

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

The build processes all files listed in `_CoqProject`. There are no separate
test or lint commands -- the type checker is the test suite. To check if the
code is building correctly, make sure to check the exit status -- don't just
grep for errors.

`nix build` uses the git-tracked source tree: a newly created file that has
not yet been `git add`ed will not be picked up (it fails with "No rule to
make target"), even though a direct `coqc` compile of it succeeds. Stage new
files before running `nix build` to verify them.

For fast local iteration without going through the full Nix sandbox each
time (e.g. while working through a chain of compile errors), `nix develop -c
make -j4` builds incrementally in the working tree itself (persists `.vo`
files across invocations, unlike `nix build`'s ephemeral sandbox) -- but
always do a final `nix build` before considering something actually
verified; the two environments can differ (e.g. a local `.vo` cache going
stale relative to a just-updated flake input produces a spurious
"inconsistent assumptions" error that only `make clean` fixes, and `nix
build` is the only check that exercises the real dependency-fetch path).

After building, make sure you always report what lemmas were left admitted.

## Dependencies

Declared in `flake.nix` via Nix overlay, both pinned via `github:` inputs
(not local `path:` inputs -- Nix flakes cannot resolve a relative `path:`
input across independent sibling git repos, confirmed empirically; it
resolves against the referring flake's own git-fetched store copy, not the
real filesystem, with or without `--impure`):
- **Rocq/Coq** (from nixpkgs)
- **stdpp** -- provides `base`, `list`, `finite`, `gmap`, `mapset`
- **coq-library-undecidability**, pinned to
  `github:jstrattonsmith/coq-library-undecidability/enable-L-nix-9.0` (a
  fork; that branch adds a Nix-wiring fix enabling the `L/` extraction
  framework on top of an otherwise-unmodified `rocq-9.0`, plus, as of
  2026-08-31, new MM2 content originally developed in this project and
  migrated upstream since it's genuinely reusable and had zero
  Kleene-algebra content: `Undecidability.MinskyMachines.Util.{MM2_stepper,
  MM2_embed_nat,MM2_simulator}` (computable MM2 stepping, Gödel-coding,
  and a total step-indexed simulator with its L-extractability instances)
  and `Undecidability.MinskyMachines.Reductions.{FRACTRAN_computable_to_MM2_computable,
  MM2_Splice}` (FRACTRAN-to-MM2 compilation and program splicing).
  `coq-synthetic-computability`'s own flake points at the same fork+branch,
  so both projects always resolve the identical source.
- **coq-synthetic-computability**, pinned to
  `github:arthuraa/coq-synthetic-computability` (a collaborator's repo,
  not a fork of it) -- provides `T_L`/`θ_L`/`CT_L`
  (`theories/Models/CT.v`, `T_L_Uniform.v`, `T_L_Extract.v`), the generic
  and `L`-specific effective-inseparability machinery
  (`theories/ReducibilityDegrees/*.v`, `theories/Models/EffectiveInseparability_L.v`),
  `EA`/`EPF`/`SMN` (`theories/Axioms/*.v`), and, as of 2026-08-31, the
  content that used to live in this repo's own (now-deleted)
  `Computability/` directory -- zero Kleene-algebra content, genuinely
  reusable, migrated upstream: `theories/ReducibilityDegrees/EffectiveInseparabilityCore.v`
  (the unbundled effective-inseparability notion + superset-transport,
  genuinely different from -- not a duplicate of -- the already-present
  `EffectiveInseparabilityTransport.v`'s bundled version) and
  `theories/Models/{EA_L,EA_L_Myhill,T_L_Bridge}.v` (`EA_L.v` builds a
  genuine `EA` instance from `CT_L`; `EA_L_Myhill.v`, named to avoid
  colliding with the pre-existing `Basic/Myhill.v` isomorphism-theorem
  file, derives `creative`/`m-complete` from `eff_insep_shape`;
  `T_L_Bridge.v` bridges `T_L` to the `mu`-search-shaped `R_TL` and
  provides the generic `K_of`/`GenericK` "connection -> effective
  inseparability" argument this project's `CKAUndec/K.v`/
  `BinaryAlphabetMComplete.v` instantiate).
- **MetaRocq** (transitive via coq-library-undecidability)

## File Structure

Files are listed in dependency order (`_CoqProject`, which groups them into
the same sections used below with one-line comments). All files are
admit-free; no axioms appear anywhere except the two hypotheses named above
(`CT_L`, `MP`), both isolated to `CKAUndec/KMComplete.v`.

### `MM2/`: a small piece of genuinely CKA-specific glue

1. **`MM2/RtcBridge.v`** (~25 lines): `crt_to_rtc`, bridging Coq's
   `clos_refl_trans` (what the upstream MM2 facts are now stated over) to
   stdpp's `relations.rtc` (what this project's own KA-term encoding
   needs). Genuinely CKA-specific glue, not MM2-generic content -- it only
   exists because this project's own encoding happens to be built over
   stdpp's relation vocabulary.

### `MM2/Legacy/`: not on the critical path, kept for their own interest

- **`MM2/Legacy/TLUniform_MM2.v`** (~45 lines), **`MM2/Legacy/MM2_PrefixSplice.v`**
  (~265 lines): an earlier, self-contained axiom-free S-M-N-style
  construction directly at the MM2 level (predating the `T_L`-based route
  above, which superseded it for the main argument). Still compile, still
  in `_CoqProject`.
- **`MM2/Legacy/EffectiveInseparability_MM2_Race.v`** (~415 lines) and
  **`MM2/Legacy/SMN_MM2.v`** (~250 lines, `Require`s the former):
  **excluded from `_CoqProject`** (commented out, not deleted). Their
  `semidec_of_MM2_computable` needs MetaRocq's `extract` to bridge a
  `computable` instance across a file boundary, which fails.
- **`MM2/Legacy/Simulator.v`** (~150 lines): builds `Θ_MM2`, a
  `part`-valued MM2 evaluator, plus two enumerable halting sets
  (`A0_MM2`/`B1_MM2`), mirroring `coq-synthetic-computability`'s `L`-level
  construction (`Models/EffectiveInseparability_L.v`). Kept free of any
  `CKAUndec/` dependency (no `ssreflect`): `MM2_PrefixSplice.v`/
  `SMN_MM2.v` above also `Require` it and are plain-tactic-style, which
  breaks if `ssreflect` notations leak in.
- **`MM2/Legacy/SimulatorToRTarget.v`** (~120 lines): connects `Θ_MM2` to
  `CKAUndec/Encoding.v`'s `R_target` (`R_target_iff_outcome`), plus its
  embedded-alphabet analogue against `CKAUndec/BinaryAlphabet.v`'s
  `red_leq'` (`R_target_iff_outcome_binary`) -- a proven alternative to
  the `T_L`-based route `CKAUndec/Glue/TLToRTarget.v`/
  `BinaryAlphabetConnection.v` actually use. Neither lemma is referenced
  elsewhere. Kept separate from `Simulator.v` itself so that file can
  stay `ssreflect`-free.

### `KA/`: the pre-Kleene-algebra framework, groundwork for the MM2-as-KA-terms encoding, binary embedding machinery

9. **`KA/utils.v`** (~280 lines): Finite enumeration of gmaps, gsets, list
   pairs, and lists of bounded length.

10. **`KA/algebra.v`** (~900 lines): Custom algebraic hierarchy built on
    stdpp's `Equiv`/`SqSubsetEq` typeclasses: `setoid` -> `monoid` (with
    `MonoidMixin`) -> `semi_lattice` (with `SemiLatticeMixin`). Morphism
    classes (`MonoidMorphism`, `SemiLatticeMorphism`) at each level. Concrete
    instances: `bool`, `option`, `list`, product monoids/setoids.
    `MonoidGen`/`SizedMonoid` typeclasses for generator structures.

11. **`KA/pre_ka.v`** (~900 lines): Pre-Kleene algebra (`PreKAMixin` adding
    star/distribution/idempotency). `PreKAMorphism` class. `ka_term T` free KA
    term AST (`Unit`, `ka_term_bottom`, `ka_term_join`, `ka_term_mul`,
    `ka_term_star`). Key operations: `ka_term_elim`, `count_term`, `has_one`,
    `pseudo_top`. Concrete instances: `count`, `lang`.

12. **`KA/enumerable.v`** (~310 lines): Given the carrier monoid `T`'s own `≡`
    is enumerable, `ka_eq`/`⊑` on `ka_term T` is too -- via a reified,
    sound-and-complete syntactic derivation system over the 12 pre-KA axiom
    schemes (`D`, `check`/`check_sound`/`check_complete`) with computable
    proof search. This is the "finitary axiomatization gives r.e." argument
    `CKAUndec/KEnumerable.v` (below) instantiates for the MM2 encoding's own
    carrier.

13. **`KA/lang.v`** (~400 lines): `lang` record (formal languages over word
    monoids) with `l : ka_term T -> lang` interpreting terms as languages.
    Includes `l_alt` (Theorem 5: string membership <-> term ordering),
    `l_inj_finite` (Corollary 7), `either_empty_or_nonzero` (Corollary 8).

14. **`KA/automata.v`** (~1080 lines): FSA/NFA definitions: `fsa` record with
    `fsa_elem`, `fsa_state`, `fsa_interp`, `fsa_initial`, `fsa_trans`,
    `fsa_trans_s`. Product (`fsa_mul'`) and star (`fsa_star'`) constructions.
    `finite_state` predicate and its boolean analogue `finite_stateb` (+
    `finite_stateP`, `finite_stateb_join_list`). Expansion lemma
    `fsa_elem_k_decomp_gen` (Lemma 27). `ka_term_proj1`, `ka_term_proj2`,
    `ka_term_diag`. `string_match` / `string_match_complete_sized`.

15. **`KA/repr_rel.v`** (~855 lines): Representable relations (`repr_rel`
    record with `next`, `residue`, `expand_rel`). `diff` term. Iteration
    lemmas (`repr_rel_iter`, Lemma 21; `repr_rel_iter_empty`, Theorem 22).
    Also `pad_lang`/`pad_rel` and `repr_rel_iter_final` -- padding/
    termination combinators added specifically to support
    `CKAUndec/Encoding.v`'s MM2 encoding below.

16. **`KA/BinaryAlphabetTransport.v`** (~180 lines): the fixed-length
    injective character encoding shared by both binary-alphabet embedding
    routes (`finite_binary_encoding`, `Embed_pair`, `Embed_word`,
    `Embed_proj1_natural`/`Embed_proj2_natural`, all proved, axiom-free).

17. **`KA/bounded_output.v`** (~815 lines): Bounded-output terms (Definition
    28). Closure under join, mul, star (Lemma 30). `bounded_outputb` boolean
    check. Prefix-free terms (Definition 32). `list_diverge` (Lemma 33). Lemma
    31 (paper version): `lemma_31_paper` restricts the expansion to
    output-bounded suffix terms. Lemma 34 (`bounded_output_repr_rel`, plus a
    primed variant `bounded_output_repr_rel'` used by `CKAUndec/Encoding.v`)
    is fully proved, admit-free.

18. **`KA/BoundedOutputTransport.v`** (~275 lines): route 1 of the
    binary-alphabet embedding, and the one actually used downstream
    (`CKAUndec/BinaryAlphabet.v`). Reuses `KA/bounded_output.v`'s Lemma 34
    directly (already generic over any finite alphabet) by transporting its
    four hypotheses (`finite_state`, `bounded_output`, domain/codomain
    containment, `prefix_free`) through the fixed-length character encoding
    from `KA/BinaryAlphabetTransport.v`. `repr_rel_via_bounded_output` is the
    payoff theorem, fully proved, admit- and axiom-free.

### `CKAUndec/` and `CKAUndec/Glue/`: the actual MM2-as-KA-terms payoff, plus the glue wiring `MM2/`/`coq-synthetic-computability` into it

19. **`CKAUndec/Encoding.v`** (~1335 lines): encodes two-counter (MM2) Minsky
    machines as KA terms over a doubled/commutable alphabet (Definitions
    11-13): `mm_sym`, `encode_instr`, `transition_rel` (`R_M`), `config_set`
    (`C_M`). Connects to `coq-library-undecidability`'s `MM2` library via
    `translate_state`/`next_state`. `Section MM2Adapter` (parametrized by a
    program `P`, importing `coq-library-undecidability`'s
    `Util.MM2_stepper` for its single-step interpreter fragment and
    `Util.MM2_facts` for `mm2_step_det`/`mm2_stop_index_iff`) proves the
    soundness/completeness pair (paper's Theorems 15-16):
    `mm2_R_completeness` (halts-at-(0,0) implies the KA inequality
    `red_lb ⊑ red_ub`) and `mm2_R_soundness` (the converse, given the
    inequality and a halted state, the halt is exactly at (0,0)).
    `red_lb`/`red_ub`/`red_leq` are the KA-term-level objects the
    computability argument builds on. Also defines
    `R_target c y := red_leq (progOf c) (1,(y,0))`, bridging to a plain
    natural-number program code (`progOf`, from
    `coq-library-undecidability`'s `Util.MM2_simulator`) -- the KA-term
    decision problem the whole argument is ultimately about, and a
    direct consequence of `mm2_R_soundness`/`mm2_R_completeness` above.

20. **`CKAUndec/Glue/TLToRTarget.v`** (~130 lines): builds a single uniform
    MM2 program for `T_L` via `coq-library-undecidability`'s
    `Reductions.FRACTRAN_computable_to_MM2_computable`, then splices its
    divisibility-encoded output convention
    (`Reductions.MM2_Splice`'s `Psplice`) into `CKAUndec/Encoding.v`'s
    exact `(0,(0,0))`-halting convention, connecting all the way to
    `R_target` (`R_TL_R_target_connection`).

21. **`CKAUndec/K.v`** (~105 lines): closes Theorem 17. Defines `z_vec`,
    `K z := R_target c (...)` -- a genuine `red_lb ⊑ red_ub` KA-term-level
    statement -- and proves it's effectively inseparable from `B1_L` (in the
    unbundled sense both source papers state their own Theorem 17 in:
    disjointness plus a witness function, no enumerability required), via
    `coq-synthetic-computability`'s `ReducibilityDegrees.EffectiveInseparabilityCore`'s
    superset-transport lemma (Kuznetsov's Proposition 9).

22. **`CKAUndec/KEnumerable.v`** (~110 lines): shows `K` is genuinely
    enumerable, by identifying `CKAUndec/Encoding.v`'s carrier monoid (a
    product of free monoids over an `option`-padded, finite, decidable-
    equality alphabet) and applying `KA/enumerable.v`'s generic finitary-
    axiomatization argument to it. Also defines `KA_ineq`, the full
    `{(x,y) | x ⊑ y}` relation over that carrier (`K` is one fixed-rhs slice
    of it), via `ka_sqsubseteq_enumerable`.

23. **`CKAUndec/KMComplete.v`** (~135 lines): the full chain from `K`'s
    bundled effective inseparability (`eff_insep_shape_K_B1_L`, upgrading
    `CKAUndec/K.v`'s unbundled result now that enumerability is in hand)
    through Myhill's theorem (`K_creative`, `K_m_complete`, instantiating
    `coq-synthetic-computability`'s `Models.EA_L_Myhill`'s generic machinery
    at `P := K c`, conditional on `CT_L`/`MP`) to full Sigma^0_1-completeness
    of the actual KA-term inequality relation, not just its `K`-slice
    (`KA_ineq_m_complete`, composing `K_m_complete` with the reduction
    `K ⪯ₘ KA_ineq` via `red_m_transitive`).

24. **`CKAUndec/BinaryAlphabet.v`** (~390 lines): the CKA-specific wiring
    that actually closes the source paper's Theorem 18/19 (undecidability/
    completeness stated over the canonical, minimal 2-symbol alphabet
    `{0,1}`, not `mm_sym Q`) -- applies `KA/BoundedOutputTransport.v`'s
    machinery directly to `CKAUndec/Encoding.v`'s own `mm2_R`/`T`, then
    re-runs `CKAUndec/Encoding.v`'s own soundness/completeness argument
    (`mm2_R_completeness'`/`mm2_R_soundness'`) at the embedded level to get
    order-*reflection* for `red_lb`/`red_ub`, not just preservation -- having
    a `repr_rel` for the embedded term alone would not have been enough.
    `red_leq'` is the embedded analogue of `red_leq`. One documented,
    non-blocking gap remains (see the file's own comment): `red_leq'` is only
    characterized for *halting* MM2 runs, matching how `red_leq` itself is
    only ever used -- tracing to the same missing star-induction axiom
    documented in `KA/BinaryAlphabetTransport.v`'s header comment.

25. **`CKAUndec/Glue/BinaryAlphabetConnection.v`** (~120 lines): the
    binary-alphabet analogue of `CKAUndec/Glue/TLToRTarget.v` -- mirrors
    `Psplice_R_target_divides`/`_not_divides`/`R_TL_R_target_connection`,
    substituting `CKAUndec/BinaryAlphabet.v`'s `mm2_R_completeness'`/
    `mm2_R_soundness'` for the unembedded originals, closing with
    `R_TL_R_target_connection_bin`.

26. **`CKAUndec/BinaryAlphabetMComplete.v`** (~325 lines): the
    binary-alphabet analogue of `CKAUndec/KMComplete.v`, generalized over an
    abstract Prop family/carrier monoid wherever the original argument only
    used `K`/`red_leq` as an opaque interface (verified faithful to the
    original via a reflexivity-level check, `K_eq_K_of_R_target`) -- so `K`'s
    and the new `K_bin`'s properties are proven by the SAME lemmas, not two
    copies. Closes with `KA_ineq_bin_m_complete : CT_L -> MP -> m-complete
    KA_ineq_bin` -- unlike `KA_ineq_m_complete` (one instance per machine
    `c`), this needs no existential over `c`: the embedded carrier `Tm_bin`
    is a single, fixed algebra (the canonical two-symbol alphabet),
    independent of which machine is being encoded, exactly matching how the
    source paper states its own Theorem 18 once, not per machine. This is
    the final theorem closing the canonical-alphabet requirement in full.
    Its `K_of`/`GenericK`-style genericity is imported from
    `coq-synthetic-computability`'s `Models/T_L_Bridge.v` rather than
    redefined locally.

## Style Guidelines

Several of these guidelines are guiding principles that are not necessarily
followed consistently throughout the code, but that should be respected as much
as possible, **especially by Claude**. Many coding conventions come from
[Ssreflect][ssreflect-tutorial], but we do not follow those thoroughly because
we're using stdpp, which follows different conventions, in particular regarding
naming.

- Lines are capped at 80 characters, including in Markdown files.  You should
  aim to fully utilize the 80 character limit. Avoid short lines if possible.
- `KA/`-specific tactic conventions (ssreflect usage) are documented in
  `KA/CLAUDE.md`, loaded only when working under that directory.
- The `congruence` tactic is allowed.
- `Set Implicit Arguments` is active -- beware that arguments inferable from
  later ones become implicit.  Use `@lemma_name` to pass all arguments
  explicitly. Avoid using `@` as much as possible. Note this can also leak
  from an imported file that sets it at its own top level, outside any
  `Section` (confirmed while migrating `MM2/`'s content upstream: a plain
  top-level `Lemma`/`Definition` declared after `Require Import`ing such a
  file gets its own arguments silently made implicit too, unlike a
  `Section` `Variable`, which stays explicit once the section closes
  regardless) -- if a file you're editing starts producing "term has type
  X while it is expected to have type Y" errors that look like an
  off-by-N argument shift, check whether `Set Implicit Arguments` is
  actually coming from somewhere upstream of what you wrote.
- Custom scope `ka_scope` with notations: `⋅` for mul, `1` for one, `∏` for
  `mul_list`, `⨆` for join_list, `x ^ n` for power.  Join (`⊔`), star, ordering
  (`⊑`), and bottom (`⊥`) use stdpp typeclasses (`Join`, `Star`, `SqSubsetEq`,
  `Bottom`) rather than custom notations.
- A file that needs BOTH stdpp's own notations (`⊑`, `≡`, etc., which live in
  `stdpp_scope`) AND `coq-library-undecidability`'s `vec_notations` (`##` for
  vector cons, used by MMA/FRACTRAN code) cannot `Import` both -- `##` is
  declared at conflicting precedence levels in the two modules, a hard
  notation-grammar clash, not a scope-priority ambiguity. `CKAUndec/
  BinaryAlphabetMComplete.v` is the precedent: it `Require`s (never
  `Import`s) `stdpp.base`/`stdpp.decidable`/`stdpp.countable` and spells
  everything out via qualified names (`base.equiv`, `base.sqsubseteq`,
  `countable.Countable`, `decidable.bool_decide`, `fst`/`snd` instead of
  `.1`/`.2`) instead. Relatedly, ssreflect's `Generalizable Variables` will
  silently turn an unqualified, unresolvable class name used in a
  `Context `{!Foo x}` binder into a fresh, disconnected placeholder instead
  of raising "not found" -- always qualify stdpp class names
  (`countable.Countable`, not bare `Countable`) in any file that can't
  `Import` the defining module.
- A file that `Require`s (bare, not `Import`) another file for QUALIFIED
  access (e.g. `Require kacc.CKAUndec.Encoding.` to write `Encoding.mm2_R`)
  may separately need `From kacc Require Import ...` (an actual `Import`) of
  the SAME file if it also needs some of that file's names BARE (e.g. inside
  a `Notation` that must resolve unqualified) -- these are two different
  needs that can both apply to one file; see `CKAUndec/BinaryAlphabet.v` for
  an example of both being necessary simultaneously.
- A literal `*)` appearing inside a Coq block comment's own prose (e.g.
  writing "`L.*`" to mean "everything under the `L` namespace") closes the
  comment early and produces a confusing downstream syntax error, not an
  error at the actual `*)` -- write around it (e.g. "the `L/` files")
  instead.

  [KACC]: https://arxiv.org/pdf/2411.15979
  [ssreflect-tutorial]: https://inria.hal.science/inria-00407778v1/document
