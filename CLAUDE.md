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
  built for this project (see MM2_Legacy/ below).
- `coq-synthetic-computability` (a collaborator's repo) -- generic
  synthetic-computability theory (`T_L`/`CT_L`, effective inseparability,
  reducibility degrees), including a set of files originally built for
  this project too (see Dependencies below).

The development is organized into `MM2_Legacy/` (an evaluator wrapper not
on the critical path), `KA/` (the paper's own pre-Kleene-algebra framework
and binary-alphabet embedding, independent of `MM2_Legacy/`/`CKAUndec/`),
and `CKAUndec/`/`CKAUndec/Glue/` (the actual MM2-as-KA-terms payoff, plus
a small piece of CKA-specific `MM2`-facing glue, `CKAUndec/Glue/RtcBridge.v`)
-- see File Structure below for the file-by-file breakdown of each.

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
(`CT_L`, `MP`), stated as hypotheses in `CKAUndec/KMComplete.v`,
`CKAUndec/BinaryAlphabetMComplete.v` and `Universality/UnivMComplete.v`.

### `MM2_Legacy/`: not on the critical path, kept for their own interest

- **`MM2_Legacy/TLUniform_MM2.v`** (~45 lines), **`MM2_Legacy/MM2_PrefixSplice.v`**
  (~265 lines): an earlier, self-contained axiom-free S-M-N-style
  construction directly at the MM2 level (predating the `T_L`-based route
  above, which superseded it for the main argument). Still compile, still
  in `_CoqProject`.
- **`MM2_Legacy/EffectiveInseparability_MM2_Race.v`** (~415 lines) and
  **`MM2_Legacy/SMN_MM2.v`** (~250 lines, `Require`s the former):
  **excluded from `_CoqProject`** (commented out, not deleted). Their
  `semidec_of_MM2_computable` needs MetaRocq's `extract` to bridge a
  `computable` instance across a file boundary, which fails.
- **`MM2_Legacy/Simulator.v`** (~150 lines): builds `Θ_MM2`, a
  `part`-valued MM2 evaluator, plus two enumerable halting sets
  (`A0_MM2`/`B1_MM2`), mirroring `coq-synthetic-computability`'s `L`-level
  construction (`Models/EffectiveInseparability_L.v`). Kept free of any
  `CKAUndec/` dependency (no `ssreflect`): `MM2_PrefixSplice.v`/
  `SMN_MM2.v` above also `Require` it and are plain-tactic-style, which
  breaks if `ssreflect` notations leak in.
- **`MM2_Legacy/SimulatorToRTarget.v`** (~120 lines): connects `Θ_MM2` to
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

12. **`KA/rules_enumerable.v`** (~125 lines) and **`KA/preka_enumerable.v`**
    (~270 lines): the first holds generic enumerability lemmas independent
    of KA (`countable_enumerableT`, `checker_enumerable`,
    `enumerable_reduce`, and `rules_enumerable`: a predicate generated by
    a countable family of computable rules is enumerable, with derivations
    as postfix programs `list (L * nat)` run on a stack); the second
    `Require Export`s it. Given the carrier monoid `T`'s own `≡` is
    enumerable, `ka_eq`/`⊑` on `ka_term T` is too: `ka_rule` presents
    `ka_eq` as generated by rules. This is the "finitary axiomatization gives r.e." argument
    `CKAUndec/KEnumerable.v` (below) instantiates for the MM2 encoding's own
    carrier. `slice_enumerable`/`slice_enumerable_r` fix the right-/left-hand
    side of the inequality.

13. **`KA/lang.v`** (~400 lines): `lang` record (formal languages over word
    monoids) with `l : ka_term T -> lang` interpreting terms as languages.
    Includes `l_alt` (Theorem 5: string membership <-> term ordering),
    `l_inj_finite` (Corollary 7), `either_empty_or_nonzero` (Corollary 8).

14. **`KA/ka.v`** (~630 lines): Kleene algebras (`KAMixin`, Kozen's two
    star induction rules, on top of `PreKAMixin`) with basic theory
    (`ka_star_mono`, `ka_star_one`, `ka_star_comm`, and
    `ka_star_join_comm`: `(x ⊔ y)^* ≡ (1 ⊔ x x^* ⊔ y y^*) (x y)^*` when
    `x y ≡ y x`), and languages as a KA (`lang_ka`). `free_ka P` is the
    free KA over a pre-KA `P` (boxed terms over `P` modulo pre-KA laws,
    the operation table of `P` and star induction), with unit
    `free_ka_unit`, lift `free_ka_lift` and uniqueness `free_ka_ext`.
    `fka M` is the free KA over a monoid: boxed terms over `M` (`FKA`, a
    coercion that is always printed), compared by KA derivability, so
    `FKA e1 ⊑ FKA e2` reads "KA proves `e1 ⊑ e2`"; `fka_le_of_pre`
    (pre-KA inequalities hold in KA), `fka_lift`/`fka_ext`, `fka_lang`
    (soundness for languages). Over a finitely generated monoid,
    `FKA pseudo_top` is its top element (`fka_top_greatest`, `fka_top_iff`).

15. **`KA/ka_enumerable.v`** (~205 lines): the analogue of
    `KA/preka_enumerable.v` for the free KA: derivations of `free_ka_eq`
    (pre-KA laws, operation table, star induction) as the rules `fk_rule`
    of `rules_enumerable`, giving `free_ka_eq_enumerable` and
    `fka_le_slice_enumerable_r`.

16. **`KA/automata.v`** (~1080 lines): FSA/NFA definitions: `fsa` record with
    `fsa_elem`, `fsa_state`, `fsa_interp`, `fsa_initial`, `fsa_trans`,
    `fsa_trans_s`. Product (`fsa_mul'`) and star (`fsa_star'`) constructions.
    `finite_state` predicate and its boolean analogue `finite_stateb` (+
    `finite_stateP`, `finite_stateb_join_list`). Expansion lemma
    `fsa_elem_k_decomp_gen` (Lemma 27). `ka_term_proj1`, `ka_term_proj2`,
    `ka_term_diag`. `string_match` / `string_match_complete_sized`.

17. **`KA/repr_rel.v`** (~855 lines): Representable relations (`repr_rel`
    record with `next`, `residue`, `expand_rel`). `diff` term. Iteration
    lemmas (`repr_rel_iter`, Lemma 21; `repr_rel_iter_empty`, Theorem 22).
    Also `pad_lang`/`pad_rel` and `repr_rel_iter_final` -- padding/
    termination combinators added specifically to support
    `CKAUndec/Encoding.v`'s MM2 encoding below.

18. **`KA/BinaryAlphabetTransport.v`** (~180 lines): the fixed-length
    injective character encoding shared by both binary-alphabet embedding
    routes (`finite_binary_encoding`, `Embed_pair`, `Embed_word`,
    `Embed_proj1_natural`/`Embed_proj2_natural`, all proved, axiom-free).

19. **`KA/bounded_output.v`** (~815 lines): Bounded-output terms (Definition
    28). Closure under join, mul, star (Lemma 30). `bounded_outputb` boolean
    check. Prefix-free terms (Definition 32). `list_diverge` (Lemma 33). Lemma
    31 (paper version): `lemma_31_paper` restricts the expansion to
    output-bounded suffix terms. Lemma 34 (`bounded_output_repr_rel`, plus a
    primed variant `bounded_output_repr_rel'` used by `CKAUndec/Encoding.v`)
    is fully proved, admit-free.

20. **`KA/BoundedOutputTransport.v`** (~275 lines): route 1 of the
    binary-alphabet embedding, and the one actually used downstream
    (`CKAUndec/BinaryAlphabet.v`). Reuses `KA/bounded_output.v`'s Lemma 34
    directly (already generic over any finite alphabet) by transporting its
    four hypotheses (`finite_state`, `bounded_output`, domain/codomain
    containment, `prefix_free`) through the fixed-length character encoding
    from `KA/BinaryAlphabetTransport.v`. `repr_rel_via_bounded_output` is the
    payoff theorem, fully proved, admit- and axiom-free.

### `CKAUndec/` and `CKAUndec/Glue/`: the actual MM2-as-KA-terms payoff, plus the glue wiring `coq-synthetic-computability` into it

21. **`CKAUndec/Encoding.v`** (~1335 lines): encodes two-counter (MM2) Minsky
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

22. **`CKAUndec/Glue/RtcBridge.v`** (~25 lines): `crt_to_rtc`, bridging Coq's
    `clos_refl_trans` (what the upstream MM2 facts are now stated over) to
    stdpp's `relations.rtc` (what this project's own KA-term encoding
    needs). Genuinely CKA-specific glue, not MM2-generic content -- it only
    exists because this project's own encoding happens to be built over
    stdpp's relation vocabulary. Used by the next item and by
    `CKAUndec/Glue/BinaryAlphabetConnection.v` below.

23. **`CKAUndec/Glue/TLToRTarget.v`** (~155 lines): builds a single uniform
    MM2 program for `T_L` via `coq-library-undecidability`'s
    `Reductions.FRACTRAN_computable_to_MM2_computable`, then splices its
    divisibility-encoded output convention
    (`Reductions.MM2_Splice`'s `Psplice`) into `CKAUndec/Encoding.v`'s
    exact `(0,(0,0))`-halting convention. The splice argument is stated
    once, for any predicate on start states that is complete for runs
    halting at (0,(0,0)) and sound for halting runs
    (`R_TL_connection_gen`, whose witness `c` does not depend on the
    predicate, and its per-program-family form `R_TL_connection_of`).
    `R_TL_R_target_connection` instantiates it at `R_target`; so do
    `CKAUndec/Glue/BinaryAlphabetConnection.v` and
    `Universality/UnivConnection.v`.

24. **`CKAUndec/K.v`** (~105 lines): closes Theorem 17. Defines `z_vec`,
    `K z := R_target c (...)` -- a genuine `red_lb ⊑ red_ub` KA-term-level
    statement -- and proves it's effectively inseparable from `B1_L` (in the
    unbundled sense both source papers state their own Theorem 17 in:
    disjointness plus a witness function, no enumerability required), via
    `coq-synthetic-computability`'s `ReducibilityDegrees.EffectiveInseparabilityCore`'s
    superset-transport lemma (Kuznetsov's Proposition 9).

25. **`CKAUndec/KEnumerable.v`** (~110 lines): shows `K` is genuinely
    enumerable, by identifying `CKAUndec/Encoding.v`'s carrier monoid (a
    product of free monoids over an `option`-padded, finite, decidable-
    equality alphabet) and applying `KA/preka_enumerable.v`'s generic finitary-
    axiomatization argument to it. Also defines `KA_ineq`, the full
    `{(x,y) | x ⊑ y}` relation over that carrier (`K` is one fixed-rhs slice
    of it), via `ka_sqsubseteq_enumerable`.

26. **`CKAUndec/KMComplete.v`** (~135 lines): the full chain from `K`'s
    bundled effective inseparability (`eff_insep_shape_K_B1_L`, upgrading
    `CKAUndec/K.v`'s unbundled result now that enumerability is in hand)
    through Myhill's theorem (`K_creative`, conditional on `CT_L` only,
    since the separating witness is total (`eff_insep_shape_tot`); then
    `K_m_complete`, which adds `MP` for `creative_to_m_complete`;
    instantiating `coq-synthetic-computability`'s `Models.EA_L_Myhill`'s
    generic machinery at `P := K c`) to full Sigma^0_1-completeness
    of the actual KA-term inequality relation, not just its `K`-slice
    (`KA_ineq_m_complete`). The route is packaged generically over the
    Prop family `Pred` as `eff_insep_shape_K_of_B1_L` and
    `m_complete_of_K_of` (effective inseparability of `K_of Pred`, Myhill,
    then a reduction `K_of Pred ⪯ₘ P` via `red_m_transitive`), which
    `KA_ineq_m_complete`, `BinaryAlphabetMComplete.v`'s
    `KA_ineq_bin_m_complete` and the four `Universality/UnivMComplete.v`
    theorems instantiate.

27. **`CKAUndec/BinaryAlphabet.v`** (~390 lines): the CKA-specific wiring
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

28. **`CKAUndec/Glue/BinaryAlphabetConnection.v`** (~45 lines): the
    binary-alphabet analogue of `R_TL_R_target_connection`:
    `R_TL_R_target_connection_bin` instantiates `TLToRTarget.v`'s
    `R_TL_connection_gen` with `CKAUndec/BinaryAlphabet.v`'s
    `mm2_R_completeness'`/`mm2_R_soundness'`.

29. **`CKAUndec/BinaryAlphabetMComplete.v`** (~325 lines): the
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

### `Universality/`: balanced universality, a second independent MM2 encoding

Contributed separately (see [`Universality/README.md`](Universality/README.md)):
an adaptation of Xu, Zhou, Walker and Kincaid's universality construction
to pre-KA, plus full universality `Σ* ⊑ e` in KA (via `KA/ka.v`'s star
induction). Builds on `KA/` and `CKAUndec/` but nothing outside
`Universality/` depends on it. Its only change outside the directory is
that `CKAUndec/Encoding.v`'s `translate_state_spec` and `mm2_prog_spec` are
no longer `Local` (`Universality/UnivEncoding.v` reuses them). Unlike
`CKAUndec/`, every file here uses ssreflect tactics throughout.

30. **`Universality/balanced.v`** (~200 lines): the pre-KA engine behind
    `Universality/UnivEncoding.v`. Defines the additive `nat` monoid
    (`nat_add_monoid`; beware that a bare `1` in `ka_scope` at type `nat`
    elaborates to its unit, i.e. `0`) and, over `list A * nat`, the star of
    balanced letters `bal_star` (language `{(w, |w|)}`).
    `bal_univ_complete` proves `bal_star ⊑ x` without star induction by
    unfolding `bal_star` a fixed number of times: every short balanced word
    is in `l x`, and every long one has a prefix accepted by some `Pre`
    with `Pre ⋅ bal_star ⊑ x`. `bal_univ_sound` is the converse direction
    through the language model.

31. **`Universality/BalancedBinary.v`** (~350 lines): transports balanced
    universality to the fixed carrier `list bool * nat`. Letters are
    encoded by an injective fixed-length `enc` (length `k`) and weights are
    scaled by `k` (`phi (w, n) = (encw w, k * n)`, so balanced words stay
    balanced). For an upper bound `E ⊔ P ⋅ bal_star`, `bin_ub E P` adds
    detectors for an invalid block (`bad`) and for an incomplete final
    block (`partial`). `bin_complete` derives binary universality from the
    same language-level facts `bal_univ_complete` uses; `bin_sound` (and
    its language-level form `bin_sound_lang`) gives back membership of
    every balanced word over the original alphabet.

32. **`Universality/BalancedKA.v`** (~140 lines): from balanced to full
    universality in KA over `list A * nat`. `sigma_top` (`Σ*`, an instance
    of `pseudo_top`) is `star (letA ⊔ letB)`, and since the two commute,
    `ka_star_join_comm` gives `KA ⊢ Σ* ≡ bal_star ⊔ unbal`
    (`sigma_top_ka`), where `unbal` are the words with the wrong number of
    commuting letters. Hence `bal_star ⊑ x` in pre-KA gives `Σ* ⊑ x ⊔
    unbal` in KA (`ka_top_complete`), and the latter puts every balanced
    word in `l x` (`ka_top_sound`).

33. **`Universality/UnivEncoding.v`** (~1300 lines): a second, independent
    MM2 encoding, adapted from the universality construction of Xu, Zhou,
    Walker and Kincaid (arXiv:2607.09635, Section 4) to pre-KA. Over the
    carrier `list (option (mm_sym Q)) * nat`, a run is the word
    `# a^n0 q0 b^m0 # ... #`; `univ_ub` collects error detectors (wrong
    initial configuration, bad adjacent letters, wrong next state, too
    many/too few `a`s or `b`s via weighted letters, and the halt-at-zero
    factor), each padded with `bal_star`. The generic part
    (`univ_complete_gen`/`univ_sound_gen`, over any deterministic
    two-counter program on a finite state set) is instantiated in
    `Section MM2Univ` with `CKAUndec/Encoding.v`'s adapter:
    `univ_completeness` (halts at (0,0) implies `bal_star ⊑ univ_ub_mm2
    s1`) and `univ_soundness` (the converse for halting runs).
    `univ_leq`/`R_target_univ` mirror `red_leq`/`R_target`. The
    language-level halves (`univ_complete_lang`/`univ_sound_lang`) also
    feed the binary version: `univ_ub_bin` (via
    `Universality/BalancedBinary.v` and `KA/BinaryAlphabetTransport.v`'s
    one-hot `enc_onehot`),
    `univ_completeness_bin`/`univ_soundness_bin`, `R_target_univ_bin`. Full
    `Σ*` on the left (i.e. `pseudo_top`) would not work in pre-KA, see
    `Universality/balanced.v`'s header comment; it does in KA, see the next
    item.

34. **`Universality/UnivTop.v`** (~90 lines): full universality in the free
    KA. `univ_top_ub := univ_ub_mm2 ⊔ unbal` (and `univ_top_ub_bin` over
    `list bool * nat`) satisfy `univ_top_completeness`/`_soundness` with
    `FKA sigma_top ⊑ FKA _`, via `Universality/BalancedKA.v`.
    `univ_top_leq`/`R_target_univ_top` (and `_bin`) mirror
    `univ_leq`/`R_target_univ`.

35. **`Universality/UnivConnection.v`** (~50 lines): instances of
    `CKAUndec/Glue/TLToRTarget.v`'s generic `R_TL_connection_of`:
    `R_TL_R_target_univ_connection`,
    `R_TL_R_target_univ_bin_connection` and their KA counterparts
    `R_TL_R_target_univ_top(_bin)_connection`.

36. **`Universality/UnivMComplete.v`** (~200 lines): `K_univ c := K_of
    (R_target_univ c)` is enumerable, so the balanced universality problem
    `Univ c := bal_universal`, i.e. `{e | bal_star ⊑ e}`, is m-complete
    (conditional on `CT_L`/`MP`; `Univ_m_complete`). Over the fixed carrier `list
    bool * nat`, `Univ_bin_m_complete : CT_L -> MP -> m-complete Univ_bin`
    needs no existential over the machine. In the free KA, full
    universality `Univ_top c := fka_universal`, i.e. `{e | KA ⊢ Σ* ⊑ e}`,
    is m-complete too
    (`Univ_top_m_complete`, `Univ_top_bin_m_complete`; enumerability from
    `KA/ka_enumerable.v`). Each proof is one instance of
    `CKAUndec/KMComplete.v`'s `m_complete_of_K_of`, which
    combines `eff_insep_shape_K_of_B1_L`, `m_complete_of_eff_insep_shape`
    and the reduction out of `K_of`.

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
