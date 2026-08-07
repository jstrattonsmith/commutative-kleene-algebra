# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository.

## Project Overview

Rocq (formerly Coq) formalization proving undecidability results for Kleene
algebras with partial commutativity of concatenation (cf. ["Kleene algebra with
commutativity conditions is undecidable" by Azevedo de Amorim et al.,
2025][KACC]). Several references here are relative to the paper.

The development has two halves. The **algebraic half** (`utils.v` through
`mm.v`, ~7,700 lines across 9 files) builds the paper's own pre-Kleene-algebra
framework and encodes two-counter (MM2) Minsky machines as KA terms
(Definitions 11-13), proving the soundness/completeness pair connecting MM2
reachability to a KA-term inequality (Theorems 15-16). This half is done and
admit-free. The **computability half** (`EffectiveInseparability_MM2.v`
through `Theorem19_MComplete.v`, ~2,000 lines across 10 files) proves
effective inseparability (Theorem 17, admit- and axiom-free) and, building on
that, Sigma^0_1-completeness (matching the paper's own closing remark that it
adapted Kuznetsov's ICTAC 2023 completeness argument), conditional on two
named, standard hypotheses (`CT_L`, Church's Thesis for Rocq's `L` language;
`MP`, Markov's Principle) -- see `Theorem19_MComplete.v`'s header comment for
exactly why each is needed and where. Plain undecidability (Theorem 18) is an
immediate corollary of Theorem 17 and isn't separately formalized.

This computability half depends heavily on the sibling
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

The build processes all files listed in `_CoqProject`.  There are no separate
test or lint commands -- the type checker is the test suite. To check if the
code is building correctly, make sure to check the exit status -- don't just
grep for errors.

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

Files are listed in dependency order (`_CoqProject`). All files below are
admit-free; only the two hypotheses named above (`CT_L`, `MP`) appear
anywhere, both isolated to `Theorem19_MComplete.v`.

### Algebraic core (the paper's own framework + MM2-as-KA-terms encoding)

1. **`utils.v`** (~280 lines): Finite enumeration of gmaps, gsets, list pairs,
   and lists of bounded length.

2. **`algebra.v`** (~900 lines): Custom algebraic hierarchy built on stdpp's
   `Equiv`/`SqSubsetEq` typeclasses: `setoid` -> `monoid` (with `MonoidMixin`)
   -> `semi_lattice` (with `SemiLatticeMixin`).  Morphism classes
   (`MonoidMorphism`, `SemiLatticeMorphism`) at each level.  Concrete instances:
   `bool`, `option`, `list`, product monoids/setoids.  `MonoidGen`/
   `SizedMonoid` typeclasses for generator structures.

3. **`pre_ka.v`** (~900 lines): Pre-Kleene algebra (`PreKAMixin` adding
   star/distribution/idempotency).  `PreKAMorphism` class. `ka_term T` free KA
   term AST (`Unit`, `ka_term_bottom`, `ka_term_join`, `ka_term_mul`,
   `ka_term_star`). Key operations: `ka_term_elim`, `count_term`, `has_one`,
   `pseudo_top`. Concrete instances: `count`, `lang`.

4. **`enumerable.v`** (~310 lines): Given the carrier monoid `T`'s own `≡` is
   enumerable, `ka_eq`/`⊑` on `ka_term T` is too -- via a reified,
   sound-and-complete syntactic derivation system over the 12 pre-KA axiom
   schemes (`D`, `check`/`check_sound`/`check_complete`) with computable
   proof search. This is the "finitary axiomatization gives r.e." argument
   `K_Enumerable.v` (below) instantiates for the MM2 encoding's own carrier.

5. **`lang.v`** (~400 lines): `lang` record (formal languages over word monoids)
   with `l : ka_term T -> lang` interpreting terms as languages. Includes
   `l_alt` (Theorem 5: string membership <-> term ordering), `l_inj_finite`
   (Corollary 7), `either_empty_or_nonzero` (Corollary 8).

6. **`automata.v`** (~1060 lines): FSA/NFA definitions: `fsa` record with
   `fsa_elem`, `fsa_state`, `fsa_interp`, `fsa_initial`, `fsa_trans`,
   `fsa_trans_s`. Product (`fsa_mul'`) and star (`fsa_star'`)
   constructions. `finite_state` predicate.  Expansion lemma
   `fsa_elem_k_decomp_gen` (Lemma 27).  `ka_term_proj1`, `ka_term_proj2`,
   `ka_term_diag`.  `string_match` / `string_match_complete_sized`.

7. **`repr_rel.v`** (~860 lines): Representable relations (`repr_rel` record
   with `next`, `residue`, `expand_rel`). `diff` term. Iteration lemmas
   (`repr_rel_iter`, Lemma 21; `repr_rel_iter_empty`, Theorem 22). Also
   `pad_lang`/`pad_rel` and `repr_rel_iter_final` -- padding/termination
   combinators added specifically to support `mm.v`'s MM2 encoding below.

8. **`bounded_output.v`** (~815 lines): Bounded-output terms (Definition
   28). Closure under join, mul, star (Lemma 30). `bounded_outputb` boolean
   check.  Prefix-free terms (Definition 32). `list_diverge` (Lemma 33). Lemma
   31 (paper version): `lemma_31_paper` restricts the expansion to
   output-bounded suffix terms. Lemma 34 (`bounded_output_repr_rel`, plus a
   primed variant `bounded_output_repr_rel'` used by `mm.v`) is fully proved,
   admit-free.

9. **`mm.v`** (~1410 lines): Encodes two-counter (MM2) Minsky machines as KA
   terms over a doubled/commutable alphabet (Definitions 11-13): `mm_sym`,
   `encode_instr`, `transition_rel` (`R_M`), `config_set` (`C_M`). Connects to
   `coq-library-undecidability`'s `MM2` library via `translate_state`/
   `next_state`. `Section MM2Adapter` (parametrized by a program `P`) proves
   the soundness/completeness pair (paper's Theorems 15-16):
   `mm2_R_completeness` (halts-at-(0,0) implies the KA inequality `red_lb ⊑
   red_ub`) and `mm2_R_soundness` (the converse, given the inequality and a
   halted state, the halt is exactly at (0,0)). `red_lb`/`red_ub`/`red_leq`
   are the KA-term-level objects the computability argument below builds on.

### Computability argument (Theorems 17-19)

10. **`EffectiveInseparability_MM2.v`** (~470 lines): step-indexed Gallina
    simulator for MM2 programs (`Θ_ours_MM2`, `mm2_iter`, `mm2_haltedAt`),
    `A0_MM2`/`B1_MM2` and their enumerability, `progOf`/`codeOf` (Gödel-coding
    programs as naturals), and `R_target c y := red_leq (progOf c) (1,(y,0))`
    -- the KA-term-level decision problem the whole argument is ultimately
    about.

11. **`FRACTRAN_computable_to_MM2_computable.v`** (~180 lines): proves
    `FRACTRAN_computable R -> MMA2_computable R -> MM2_computable R`
    (locally-defined, divisibility-encoded output conventions), and a small
    number-theoretic helper, `not_div` (if `x` doesn't divide `y`, `x^(m+1)`
    doesn't divide `x^m * y`). Only `not_div` is actually used by the main
    chain below (`TLUniform_Bridge.v` needs the same argument for its own,
    more direct re-derivation) -- the two headline compilation theorems are
    used only by the not-on-the-critical-path files at the bottom of this
    list, not by anything from `TLUniform_Bridge.v` onward. An earlier
    version of this argument routed the whole chain through the fully-
    compiled, existentially-packaged `MM2_computable` this file produces
    (via a now-removed `TLUniform_MM2.v`); that got superseded once it
    became clear the existential wrapper doesn't expose the pinned
    stop-position the splice construction below needs, and nothing was ever
    left depending on the old route.

12. **`TLUniform_Bridge.v`** (~400 lines): re-derives the FRACTRAN-to-MMA2
    compilation directly (`FRACTRAN_computable_to_MMA2_pinned`), exposing
    the concrete stop position the existential form above hides, then
    splices its divisibility-encoded output convention into `mm.v`'s exact
    `(0,(0,0))`-halting convention (`Psplice`), connecting all the way to
    `R_target` (`R_TL_R_target_connection`) for `T_L` (Rocq's own
    `L`-language interpreter, from the sibling `coq-synthetic-computability`
    project).

13. **`A0_L_Prime.v`** (~265 lines): builds `A0_L'`, a superset of `A0_L`
    (from the sibling project's `EffectiveInseparability_L.v`) that's
    disjoint from `B1_L` and enumerable, using `Θ_ours_MM2`'s own
    enumerability shape rather than `R_target` directly (`R_target`/
    `red_leq` is a safety/language-containment property, not a termination
    witness -- there's no halts-iff-red_leq direction, only halts-implies-
    red_leq, so defining a superset directly via `R_target` wouldn't obviously
    be enumerable).

14. **`Theorem17_KATerm.v`** (~140 lines): closes Theorem 17. Defines `K z :=
    R_target c (...)` -- a genuine `red_lb ⊑ red_ub` KA-term-level statement
    -- and proves it's effectively inseparable from `B1_L` (in the unbundled
    sense both source papers state their own Theorem 17 in: disjointness plus
    a witness function, no enumerability required), via one more application
    of the sibling project's superset-transport lemma (Kuznetsov's
    Proposition 9).

15. **`K_Enumerable.v`** (~95 lines): shows `K` is genuinely enumerable, by
    identifying `mm.v`'s carrier monoid (a product of free monoids over an
    `option`-padded, finite, decidable-equality alphabet) and applying
    `enumerable.v`'s generic finitary-axiomatization argument to it.

16. **`Theorem17_Full.v`** (~45 lines): upgrades Theorem 17 to the sibling
    project's fully bundled `eff_insep_shape` notion, now that `K`'s
    enumerability is in hand.

17. **`EA_L.v`** (~100 lines): given `CT_L`, builds a genuine `EA` instance
    (the sibling project's abstract "this numbering enumerates every
    enumerable set" interface) directly from `T_L`, using the sibling
    project's own already-proven `SMN_for T_L` (an axiom-free S-M-N/currying
    theorem, needing nothing beyond `L`'s native closure support) plus one
    application of `CT_L` to a single paired predicate.

18. **`Theorem19_MComplete.v`** (~55 lines): the payoff. Feeds `EA_L` into
    the sibling project's existing, unmodified `eff_insep_to_m_complete`
    (Myhill's theorem) to get `K_m_complete : CT_L -> MP -> exists c,
    m-complete (K c)` -- genuine Sigma^0_1-hardness of the actual KA-term-level
    set `K`, matching the paper's own completeness claim.

### Not on the critical path, kept for their own interest

- **`MM2_PrefixSplice.v`** (~265 lines), **`EffectiveInseparability_MM2_Race.v`**
  (~415 lines), **`SMN_MM2.v`** (~250 lines): an earlier, self-contained
  axiom-free S-M-N-style construction directly at the MM2 level (predating
  the `T_L`-based route above, which superseded it for the main argument).
  Still compiles and is still in `_CoqProject`. `EffectiveInseparability_MM2_Race.v`
  is the sole remaining consumer of `FRACTRAN_computable_to_MM2_computable.v`'s
  two headline compilation theorems (item 11 above).

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
  applies to the algebraic core (files 1-9 above). The computability-argument
  files (10-18) deliberately use plain Coq tactics instead (`intros`,
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

  [KACC]: https://arxiv.org/pdf/2411.15979
  [ssreflect-tutorial]: https://inria.hal.science/inria-00407778v1/document
