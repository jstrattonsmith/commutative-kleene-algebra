# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository.

## Project Overview

Rocq (formerly Coq) formalization proving undecidability results for Kleene
algebras with partial commutativity of concatenation (cf. ["Kleene algebra with
commutativity conditions is undecidable" by Azevedo de Amorim et al.,
2025][KACC]). Several references here are relative to the paper.

The development is organized into four reusable libraries plus the
CKA-specific payoff that combines them:

- **`MM2/`** (~1,040 lines, 4 files): pure two-counter (MM2) Minsky-machine
  simulation, Godel-coding, and the FRACTRAN-to-MM2 compiler. Zero
  Kleene-algebra content -- reusable in any other MM2-based undecidability
  project. `MM2/Legacy/` (~975 lines, 4 files) holds an earlier,
  self-contained axiom-free S-M-N-style construction directly at the MM2
  level, predating the `T_L`-based route below (which superseded it for the
  main argument) -- not on the critical path, kept for its own interest.
- **`Computability/`** (~330 lines, 4 files): pure effective-inseparability/
  creative/m-complete theory over an abstract numbering, plus `T_L`/`CT_L`/
  `EA` bridging. Zero MM2 or KA content -- genuinely upstreamable to the
  sibling `coq-synthetic-computability` project as-is.
- **`KA/`** (~6,360 lines, 10 files): the paper's own pre-Kleene-algebra
  framework, plus a binary-alphabet embedding
  (`BinaryAlphabetTransport.v`, `BoundedOutputTransport.v`) transporting
  representable-relation facts along a fixed-length injective character
  encoding. Independent of `MM2/`/`Computability/`/`CKAUndec/` -- touches
  none of them, the most foundational library in the repo. Admit-free
  except one file (`BinaryAlphabetTransport.v`), which keeps a single
  committed `Admitted` lemma documenting a genuine dead end (needs
  star-monotonicity, which this project's pre-KA deliberately does not
  axiomatize) rather than papering over it -- see its header comment.
- **`CKAUndec/` and `CKAUndec/Glue/`** (~2,740 lines, 9 files): the actual
  payoff -- encodes MM2 as KA terms (Definitions 11-13,
  `CKAUndec/Encoding.v`), proves the soundness/completeness pair connecting
  MM2 reachability to a KA-term inequality (Theorems 15-16), and builds up
  effective inseparability (Theorem 17, admit- and axiom-free) and
  Sigma^0_1-completeness of the KA-term inequality (matching the paper's own
  closing remark that it adapted Kuznetsov's ICTAC 2023 completeness
  argument) both over the machine-specific alphabet and over the paper's own
  canonical, minimal 2-symbol alphabet
  (`CKAUndec/BinaryAlphabet.v`/`CKAUndec/BinaryAlphabetMComplete.v`, closing
  the source paper's actual Theorem 18/19 statement rather than a
  machine-specific analogue of it) -- conditional on two named, standard
  hypotheses (`CT_L`, Church's Thesis for Rocq's `L` language; `MP`, Markov's
  Principle) -- see `CKAUndec/KMComplete.v`'s header comment for exactly why
  each is needed and where. `CKAUndec/Glue/*.v` files are thin connective
  code wiring `MM2/` and `Computability/` into `CKAUndec/` (e.g. splicing an
  MM2-generic halting convention into `CKAUndec/Encoding.v`'s exact halting
  convention). Named `CKAUndec/` rather than `CKA/` to stay visually
  distinct from `KA/` in a file tree.

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

After building, make sure you always report what lemmas were left admitted.

## Dependencies

Declared in `flake.nix` via Nix overlay:
- **Rocq/Coq** (from nixpkgs)
- **stdpp** -- provides `base`, `list`, `finite`, `gmap`, `mapset`
- **coq-library-undecidability** (branch `rocq-9.0`) -- provides
  `Undecidability.MinskyMachines.MM2`/`MMA`/`FRACTRAN` for Minsky machine and
  FRACTRAN definitions, and `Undecidability.L` (Rocq's own `L` language)
- **coq-synthetic-computability** -- a sibling project, consumed as a local
  path flake input (`coq-synthetic-computability.url =
  "path:.../coq-synthetic-computability"`, see `flake.nix`) so in-progress
  edits there are picked up without committing/pushing first. Provides `T_L`/
  `θ_L`/`CT_L` (`theories/Models/CT.v`, `T_L_Uniform.v`, `T_L_Extract.v`), the
  generic and `L`-specific effective-inseparability machinery
  (`theories/ReducibilityDegrees/*.v`, `theories/Models/EffectiveInseparability_L.v`),
  and `EA`/`EPF`/`SMN` (`theories/Axioms/*.v`). Its own build (a separate
  `mkCoqDerivation`, not driven by this project's `_CoqProject`) regenerates
  its file list from `find . -name '*.v'` at build time, so new files added
  there don't need any build-file patch.
- **MetaRocq** (transitive via coq-library-undecidability)

## File Structure

Files are listed in dependency order (`_CoqProject`, which groups them into
the same sections used below with one-line comments). All files are
admit-free except one deliberately-documented `Admitted` in
`KA/BinaryAlphabetTransport.v` (see its entry below); no axioms appear
anywhere except the two hypotheses named above (`CT_L`, `MP`), both isolated
to `CKAUndec/KMComplete.v`.

### `MM2/`: pure two-counter-machine (MM2) machinery, zero KA content

1. **`MM2/Stepper.v`** (~130 lines): extracted from `CKAUndec/Encoding.v`'s own
   `Section MM2Adapter`. `mm2_atom_fun`(+spec), `mm2_instr_at_nth_error`,
   `mm2_step_fun`(+spec), `mm2_step_det`, `mm2_stop_spec` -- the single-step
   MM2 interpreter fragment, parametrized by a program `P`. Zero KA content.

2. **`MM2/Simulator.v`** (~420 lines): the step-indexed Gallina simulator for
   MM2 programs (`Θ_ours_MM2`, `mm2_iter`, `mm2_haltedAt`), Godel-coding
   (`progOf`/`codeOf`), `A0_MM2`/`B1_MM2` and their enumerability, and the
   `MetaRocq`-driven `L`-extractability instances needed to make this
   simulator usable as a Church's-Thesis witness.

3. **`MM2/FractranCompiler.v`** (~180 lines): compiles a FRACTRAN-computable
   relation to `MM2_computable`, pinning a concrete output-register
   convention (a divisibility encoding). Parametric in any FRACTRAN-computable
   `R`, not tied to `T_L` or KACC at all.

4. **`MM2/Splice.v`** (~305 lines): `FRACTRAN_computable_to_MMA2_pinned`
   re-derives the library's own FRACTRAN-to-MMA2 compilation theorem with a
   PINNED stop position (needed so code can be reliably appended right after
   a compiled program). `Section Splice` builds `Psplice`, a program that
   runs a compiled FRACTRAN program then tests/redirects on the output
   register's divisibility by `qs 1`, restated at MM2 level
   (`Psplice_mm2_divides`/`not_divides`). Entirely MM2-generic, no mention of
   KA terms or `CKAUndec/Encoding.v`'s `R_target`/`red_leq`.

### `Computability/`: generic effective-inseparability / `T_L` bridging, zero MM2/KA content

5. **`Computability/InseparabilityCore.v`** (~50 lines): the unbundled notion
   of effective inseparability (Kuznetsov's Definition 5 / Azevedo de Amorim
   et al.'s Theorem 17 statement, verbatim: disjointness plus a witness
   function, no enumerability) -- `eff_insep_core`, `eff_insep_shape_to_core`,
   and Proposition 9's superset-transport lemma `eff_insep_core_superset`,
   parametrized over an arbitrary numbering `W` and sets `A`/`B`/`A'`.

6. **`Computability/TL_Bridge.v`** (~95 lines): `theta_ours_L_iff`,
   `T_L_first_or_none`, `T_L_least_witness`, `R_TL_iff` -- bridges `T_L`
   (Rocq's own `L`-interpreter) to `A0_L`/`B1_L` (from the sibling project's
   `EffectiveInseparability_L.v`). Purely `T_L`/`A0_L`/`B1_L`-level, reused
   unchanged by both the machine-specific and binary-alphabet arguments.

7. **`Computability/EA_L.v`** (~100 lines): given `CT_L`, builds a genuine
   `EA` instance (the sibling project's abstract "this numbering enumerates
   every enumerable set" interface) directly from `T_L`, using the sibling
   project's own already-proven `SMN_for T_L` (an axiom-free S-M-N/currying
   theorem, needing nothing beyond `L`'s native closure support) plus one
   application of `CT_L` to a single paired predicate. Confirmed 100% generic
   and genuinely upstreamable to `coq-synthetic-computability` as-is (only
   relocated here within this repo, not upstreamed).

8. **`Computability/Myhill.v`** (~90 lines): `eff_insep_shape_W_iff` (the
   generic transport lemma showing `eff_insep_shape` is invariant under
   replacing `W` with a pointwise-equivalent numbering) plus
   `creative_of_eff_insep_shape`/`m_complete_of_eff_insep_shape` -- Myhill's-
   theorem-style machinery stated over an arbitrary Prop family `P`, not tied
   to `K`/`K_bin`.

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

16. **`KA/BinaryAlphabetTransport.v`** (~555 lines): route 2 of the
    binary-alphabet embedding (closing the source paper's Theorem 18, stated
    over the canonical, minimal 2-symbol alphabet `{0,1}`, not an arbitrary
    machine-specific alphabet) -- a generic algebraic transport theorem for
    `repr_rel` along a fixed-length injective character encoding
    (`Embed_pair`, `Embed_word`, `next_spec'`, all proved, axiom-free). Hits
    one genuine dead end, `dpseudo_top_mismatch_transport` (left `Admitted`,
    not axiomatized): it needs star-monotonicity
    (`Proper ((⊑) ==> (⊑)) star`), which this pre-KA deliberately does not
    provide (see its header comment for the full argument). Kept as a
    committed, self-contained artifact; superseded by
    `KA/BoundedOutputTransport.v` (route 1) for the embedding actually used
    downstream.

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

### `CKAUndec/` and `CKAUndec/Glue/`: the actual MM2-as-KA-terms payoff, plus the glue wiring `MM2/`/`Computability/` into it

19. **`CKAUndec/Encoding.v`** (~1335 lines): encodes two-counter (MM2) Minsky
    machines as KA terms over a doubled/commutable alphabet (Definitions
    11-13): `mm_sym`, `encode_instr`, `transition_rel` (`R_M`), `config_set`
    (`C_M`). Connects to `coq-library-undecidability`'s `MM2` library via
    `translate_state`/`next_state`. `Section MM2Adapter` (parametrized by a
    program `P`, and `Require`ing `MM2/Stepper.v` for its single-step
    interpreter fragment) proves the soundness/completeness pair (paper's
    Theorems 15-16): `mm2_R_completeness` (halts-at-(0,0) implies the KA
    inequality `red_lb ⊑ red_ub`) and `mm2_R_soundness` (the converse, given
    the inequality and a halted state, the halt is exactly at (0,0)).
    `red_lb`/`red_ub`/`red_leq` are the KA-term-level objects the
    computability argument builds on.

20. **`CKAUndec/Glue/MM2ToKATerm.v`** (~80 lines): bridges `MM2/Simulator.v`'s
    step-indexed evaluator (`Θ_ours_MM2`) to `CKAUndec/Encoding.v`'s own
    KA-term encoding: `red_leq`, `R_target c y := red_leq (progOf c) (1,(y,0))`
    (the KA-term-level decision problem the whole argument is ultimately
    about), and `R_target_iff_outcome`. This bridging needs no axiom -- a
    straightforward consequence of `CKAUndec/Encoding.v`'s
    `mm2_R_soundness`/`mm2_R_completeness`.

21. **`CKAUndec/Glue/TLToRTarget.v`** (~130 lines): builds a single uniform
    MM2 program for `T_L` via `MM2/FractranCompiler.v`, then splices its
    divisibility-encoded output convention (`MM2/Splice.v`'s `Psplice`) into
    `CKAUndec/Encoding.v`'s exact `(0,(0,0))`-halting convention, connecting
    all the way to `R_target` (`R_TL_R_target_connection`).

22. **`CKAUndec/K.v`** (~105 lines): closes Theorem 17. Defines `z_vec`,
    `K z := R_target c (...)` -- a genuine `red_lb ⊑ red_ub` KA-term-level
    statement -- and proves it's effectively inseparable from `B1_L` (in the
    unbundled sense both source papers state their own Theorem 17 in:
    disjointness plus a witness function, no enumerability required), via
    `Computability/InseparabilityCore.v`'s superset-transport lemma
    (Kuznetsov's Proposition 9).

23. **`CKAUndec/KEnumerable.v`** (~110 lines): shows `K` is genuinely
    enumerable, by identifying `CKAUndec/Encoding.v`'s carrier monoid (a
    product of free monoids over an `option`-padded, finite, decidable-
    equality alphabet) and applying `KA/enumerable.v`'s generic finitary-
    axiomatization argument to it. Also defines `KA_ineq`, the full
    `{(x,y) | x ⊑ y}` relation over that carrier (`K` is one fixed-rhs slice
    of it), via `ka_sqsubseteq_enumerable`.

24. **`CKAUndec/KMComplete.v`** (~135 lines): the full chain from `K`'s
    bundled effective inseparability (`eff_insep_shape_K_B1_L`, upgrading
    `CKAUndec/K.v`'s unbundled result now that enumerability is in hand)
    through Myhill's theorem (`K_creative`, `K_m_complete`, instantiating
    `Computability/Myhill.v`'s generic machinery at `P := K c`, conditional on
    `CT_L`/`MP`) to full Sigma^0_1-completeness of the actual KA-term
    inequality relation, not just its `K`-slice (`KA_ineq_m_complete`,
    composing `K_m_complete` with the reduction `K ⪯ₘ KA_ineq` via
    `red_m_transitive` -- closes a gap Arthur, the advisor, flagged after
    reviewing the proof).

25. **`CKAUndec/BinaryAlphabet.v`** (~390 lines): the CKA-specific wiring
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
    only ever used -- tracing to the same missing star-induction axiom as
    `KA/BinaryAlphabetTransport.v`'s gap.

26. **`CKAUndec/Glue/BinaryAlphabetConnection.v`** (~120 lines): the
    binary-alphabet analogue of `CKAUndec/Glue/TLToRTarget.v` -- mirrors
    `Psplice_R_target_divides`/`_not_divides`/`R_TL_R_target_connection`,
    substituting `CKAUndec/BinaryAlphabet.v`'s `mm2_R_completeness'`/
    `mm2_R_soundness'` for the unembedded originals, closing with
    `R_TL_R_target_connection_bin`.

27. **`CKAUndec/BinaryAlphabetMComplete.v`** (~325 lines): the
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
    the final theorem closing Arthur's comment 2 in full. Its own header
    comment documents a scoped decision to keep this file's `GenericK`/
    `GenericEnumerable` sections here (rather than pushing them further into
    `Computability/`, where their genericity would in principle belong)
    since doing so would also require relocating `CKAUndec/K.v`'s `z_vec`.

### `MM2/Legacy/`, not on the critical path, kept for their own interest

- **`MM2/Legacy/TLUniform_MM2.v`** (~45 lines), **`MM2/Legacy/MM2_PrefixSplice.v`**
  (~265 lines), **`MM2/Legacy/EffectiveInseparability_MM2_Race.v`**
  (~415 lines), **`MM2/Legacy/SMN_MM2.v`** (~250 lines): an earlier,
  self-contained axiom-free S-M-N-style construction directly at the MM2
  level (predating the `T_L`-based route above, which superseded it for the
  main argument). Still compiles and is still in `_CoqProject`. Three of the
  four originally carried stale `CKAUndec.Encoding`/`CKAUndec.Glue.MM2ToKATerm`
  imports left over from before the `MM2/Simulator.v` split -- confirmed
  vestigial (the files compile identically without them) and pruned when
  this group was moved here, so despite predating the `MM2/`/`CKAUndec/`
  split, all four are genuinely, purely MM2-generic.

## Style Guidelines

Several of these guidelines are guiding principles that are not necessarily
followed consistently throughout the code, but that should be respected as much
as possible, **especially by Claude**. Many coding conventions come from
[Ssreflect][ssreflect-tutorial], but we do not follow those thoroughly because
we're using stdpp, which follows different conventions, in particular regarding
naming.

- Lines are capped at 80 characters, including in Markdown files.  You should
  aim to fully utilize the 80 character limit. Avoid short lines if possible.
- Use **ssreflect** tactics (`move=>`, `rewrite`, `apply/`, `case/`, `elim:`,
  `/=`) extensively.  Avoid `destruct`, `induction`, `exfalso`, etc.  This
  applies to `KA/` (files 9-18 above). The `MM2/`, `Computability/`, and
  `CKAUndec/` files deliberately use plain Coq tactics instead (`intros`,
  `destruct`, `apply`) -- they interface directly with
  `coq-synthetic-computability`'s own plain-tactic style, and mixing
  ssreflect in at that boundary wasn't worth the friction.
- The `congruence` tactic is allowed.
- `Set Implicit Arguments` is active -- beware that arguments inferable from
  later ones become implicit.  Use `@lemma_name` to pass all arguments
  explicitly. Avoid using `@` as much as possible.
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

  [KACC]: https://arxiv.org/pdf/2411.15979
  [ssreflect-tutorial]: https://inria.hal.science/inria-00407778v1/document
