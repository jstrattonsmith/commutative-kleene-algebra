# DirectUndec: pre-KA term equality is undecidable, directly

Goal (set 2026-11-19): a direct many-one reduction from a standard halting
problem to pre-KA term equality, with no `CT_L`/`MP`, and without using
effective inseparability (explicitly, or implicitly via the `T_L` route).
Expected outcome: tedious and/or difficult, which would justify the
effective-inseparability route.

## Summary

- **Pre-KA: done, and it was not hard.** `PreKA_EQ_undec` (carrier
  `list nat * list nat`) and `PreKA_EQ_bin_undec` (the canonical binary
  carrier `Tm_bin`) both state `undecidable _` in the undecidability
  library's sense. Both are axiom-free (`Print Assumptions`: closed under
  the global context), and no coq-synthetic-computability module is loaded.
  First version: about 33 minutes and about 950 lines.
- **The second encoding (pre-KA balanced universality, `Universality/`)
  also has a direct proof.** `UNIV_undec` is axiom-free, and
  `UNIV_MP_reduction` holds under `MP`. It needs a second model,
  `TailModel.v`, about 1h20 of work.
- **The free KA (FKA): the same route provably cannot work** with this
  encoding. KA proves `red_lb ⊑ red_ub` for a non-halting machine
  (`DirectUndec/FKALoop.v`). This is where an inseparability argument is
  genuinely forced; see "Where effective inseparability earns its keep".

## Theorems

- `OmegaModel.v`: `omega_pre_ka`, the omega-token pre-KA model;
  `den_tok_le`, tokens are preserved by `⊑`.
- `NonHalting.v`: `chain_lb_not_le_chain_ub`, the generic refutation for an
  infinite chain; `red_lb_not_le_red_ub`,
  `¬ terminates P s1 → ¬ red_lb P s1 ⊑ red_ub P`; `red_leq_complete` and
  `red_leq_sound`, `red_leq` holds iff the run reaches `(0,(0,0))` (the
  converse direction as `¬ reach → ¬ red_leq`).
- `Undec.v`: `PreKA_EQ_undec : undecidable PreKA_EQ` over
  `list nat * list nat`; `PreKA_EQ_reduction`, both halves of the reduction
  from `MM2_HALTS_ON_ZERO`.
- `Undec.v`: `PreKA_EQ_MP_reduction : MP → MM2_HALTS_ON_ZERO ⪯ PreKA_EQ`,
  a genuine many-one reduction under Markov's principle alone (no `CT_L`).
- `Binary.v`: `PreKA_EQ_bin_undec : undecidable PreKA_EQ_bin` over `Tm_bin`,
  and `PreKA_EQ_bin_MP_reduction`.
- `TailModel.v`: `tlang_pre_ka`, a second model whose tokens carry finite
  tails, so infinite products do not absorb what follows; `pre_mul`,
  `pre_star`: how a run token can arise in a product or a star.
- `UnivDirect.v`: `univ_not_le_of_not_terminates`, a divergent run refutes
  `bal_star ⊑ univ_ub_mm2 P s1`; `univ_leq_complete`/`univ_leq_sound`;
  `UNIV_undec : undecidable UNIV` (balanced universality, the machine's
  alphabet part of the instance) and `UNIV_MP_reduction`.
- `FKALoop.v`: `fka_red_leq_closed`, a finite closed reachable set gives
  `FKA red_lb ⊑ FKA red_ub`; `fka_red_leq_not_terminates_fails`, the KA
  analogue of `red_lb_not_le_red_ub` is false.

## Proof idea

The reduction is the existing encoding: machine instance `(P, a, b)` maps to
the pair `(red_lb ⊔ red_ub, red_ub)`. The library's chain
`SBTM_HALT ⪯ … ⪯ MM2_HALTS_ON_ZERO` supplies the source problem.
`mm2_R_completeness` (halts at `(0,(0,0))` → `⊑`) and `mm2_R_soundness`
(halts elsewhere → `⋢`) already existed. The missing case was a divergent
run.

For a divergent run every finite prefix is covered by `red_ub`, so the
language model cannot refute `⊑`. Pre-KA, however, has only the unfolding
axiom `x* ≡ 1 ⊔ x ⋅ x*`, and no star induction. So `x*` may contain more
than `⋃ xⁿ`, and a non-standard model can tell the two terms apart:

- An element is a language together with a set of *tokens* `(t, k)`. A
  token stands for the infinite product `t ⋅ r k ⋅ r (k+1) ⋅ …`, where `r`
  is the sequence of run steps. Tokens are identified when they agree after
  finitely many more steps (`tsim`).
- Products absorb tokens on the right. `star A` additionally holds the
  token `(1, k)` whenever every `r j` with `j ≥ k` is in `A`. The unfolding
  axiom holds because `(1, k) = r k ⋅ (1, k+1)`.
- `red_lb = (1, c₀) ⋅ R*` contains the token of the run. Its two components
  agree letter by letter forever.
- Every token of `red_ub` is *bad*: it comes after an explicit mismatch, or
  it cannot exist at all. The `dpseudo_top` star's body only has one-letter
  pairs, while run steps have at least two letters per side. The
  `inj2 (pad_lang _)` part has empty left components.

Constructively, `red_leq → reaches (0,(0,0))` would need Markov's
principle. This is not a problem: the library defines
`undecidable p := decidable p → enumerable (complement SBTM_HALT)`. The two
halves `halt → eq` and `¬ halt → ¬ eq` turn a decider for `eq` into a
decider for the complement of `MM2_HALTS_ON_ZERO`, hence of `SBTM_HALT`;
`complement_SBTM_HALT_undec` finishes the proof.

## Where effective inseparability earns its keep

The pre-KA result does **not** justify effective inseparability on
difficulty grounds. The direct proof is short, and parts of it are reusable
(the omega model is generic). The arguments that remain:

1. **Star induction (FKA, and KA-based case studies like `Univ_top`).** For
   any machine whose reachable configurations form a finite, step-closed
   set avoiding bad halts, KA proves `red_lb ⊑ red_ub` by star induction
   with that set as invariant (`fka_red_leq_closed`). The two-instruction
   loop `[inc_a; dec_a 1]` is an instance. So over FKA,
   `{M | KA ⊢ red_lb_M ⊑ red_ub_M}` lies *strictly* between "halts at
   `(0,(0,0))`" and "does not halt elsewhere": it contains some divergent
   machines, and presumably not all of them. If it contained all, "never
   halts elsewhere" would be r.e. like KA provability, so "halts elsewhere"
   would be decidable. No model can refute an
   inequality KA proves, so no argument of the `NonHalting.v` kind exists.
   A reduction from halting would need a different encoding, one that
   defeats every regular inductive invariant of every divergent machine. It
   is far from clear how to build one uniformly.

   An inseparability argument needs no characterization of the middle set:
   any set sandwiched between two (effectively) inseparable sets is
   undecidable (creative, m-complete). That is exactly the situation FKA
   is in.

2. **The synthetic setting needs `CT` for the sandwich** (an informal
   argument, not formalized here). Plain recursive inseparability would
   suffice classically for undecidability of a sandwiched set. But the
   usual proof that two halting sets are inseparable builds a diagonal
   machine that runs the hypothetical separator on its own code. In
   axiom-free synthetic Coq a decider is an arbitrary Coq function, not a
   machine, so it cannot be internalized. As far as I can see this needs
   something like `CT_L`, which the `T_L` route assumes anyway. So for FKA, "some form of
   inseparability plus `CT_L`" is not a stylistic choice. It is the natural
   route once the middle set is uncharacterizable. The pre-KA route needs
   neither because there the middle set is empty.

3. **Strength of the conclusion.** The effective-inseparability route gives
   m-completeness (`Σ⁰₁`-completeness) of the inequality relation, and
   creativity, under `CT_L`/`MP`. The direct route gives `undecidable`
   axiom-free, and under `MP` alone a many-one reduction from the
   halting problem `MM2_HALTS_ON_ZERO` (`PreKA_EQ_MP_reduction`). In the
   synthetic setting, "every enumerable predicate reduces to `p`"
   (m-completeness) needs `CT` whatever the route, because it quantifies
   over arbitrary Coq enumerators. Given `CT`, halting is m-complete and
   composing with `PreKA_EQ_MP_reduction` makes `PreKA_EQ` m-complete too
   (not formalized here). So in pre-KA, effective inseparability is not
   needed even for the stronger statement.

So a fair "justification" reads: *in pre-KA a direct reduction exists and
is easy, for both encodings in this repository, because the absence of star
induction makes divergence refutable.
In the presence of star induction the natural encoding only yields a
sandwich, and inseparability is the tool that handles sandwiches.*

## Open questions

- Is there an encoding for FKA where divergence is refutable (in some
  non-*-continuous KA)? `fka_red_leq_closed` shows the encoding must at
  least defeat finite invariants, and likely all regular ones.
- The same question for KA universality (`Univ_top`, `Σ* ⊑ e`). I expect
  the `FKALoop.v` phenomenon there too (a looping machine's run words have a
  regular invariant), but did not formalize it.
- Binary-carrier versions of the universality result (`univ_ub_bin`).
  These should follow the same pattern as `Binary.v`, through
  `Universality/BalancedBinary.v`'s transport.

## Log

- **01:12** Start. Branched `direct-undec` from `main`.
- **01:12-01:24** Read `CKAUndec/Encoding.v`, `KA/pre_ka.v`, `KA/lang.v`,
  `KA/repr_rel.v`, and the undecidability library's `undecidable` and MM2
  problems. Design fixed.
- **01:24-01:31** `DirectUndec/OmegaModel.v` (~520 lines): the omega-token
  pre-KA model, generic over a monoid `M` and a sequence `r`. Compiles.
  Mostly routine; the obstacles were Program obligations, nested bullets,
  and setoid rewriting under binders (worked around with `/=`).
- **01:31-01:39** `DirectUndec/NonHalting.v` (~240 lines): for a
  non-terminating run, `red_lb P s1 ⋢ red_ub P` (`red_lb_not_le_red_ub`),
  hence `red_leq_sound`/`red_leq_complete`. Compiles, admit-free. The proof
  needed only token bookkeeping on `red_ub`.
- **01:39-01:45** `DirectUndec/Undec.v` (~190 lines): the reduction to term
  equality over the fixed carrier `list nat * list nat`, and
  `PreKA_EQ_undec : undecidable PreKA_EQ`. Axiom-free; `nix build` passes.
  **Pre-KA goal reached in about 33 minutes of wall-clock time**
  (01:12-01:45), in about 950 lines.
- **01:45-01:51** `DirectUndec/FKALoop.v` (~190 lines): KA proves
  `red_lb ⊑ red_ub` for every machine with a finite closed reachable set,
  in particular for the non-halting loop `[inc_a; dec_a 1]`. Admit- and
  axiom-free.
- **01:51-01:58** Generalized the refutation in `NonHalting.v` to any
  padded representable relation plus an infinite chain of non-empty words
  (`chain_lb_not_le_chain_ub`). New `DirectUndec/Binary.v` (~300 lines):
  the same result over the canonical binary carrier
  `Tm_bin = list (option bool) * list (option bool)`
  (`PreKA_EQ_bin_undec`), with the concrete one-hot letter encoding. The
  completeness and halting-soundness proofs are adapted from
  `CKAUndec/BinaryAlphabet.v`; that file can't be imported because it pulls
  in `CKAUndec/K.v` and coq-synthetic-computability. This also settles the
  "GENUINE OPEN GAP" recorded in `BinaryAlphabet.v`'s comment: in pre-KA a
  divergent run *refutes* `red_leq'` (the comment expected it to hold "in
  spirit"), so `red_leq'` holds exactly when the run reaches `(0,(0,0))`.
  Axiom-free; `nix build` passes.
- **01:58-02:02** This write-up, plus the `DirectUndec/` section in the
  project `CLAUDE.md`.
- **02:02-02:05** Looked at `Universality/` (see open questions: its
  left-hand side `bal_star` also prefixes the detectors, so the run token is
  absorbed and the model needs tails). Added the `MP`-only many-one
  reductions (`run_reach`/`reach_run`, `HALTS_ON_ZERO_search`).
- **02:05-02:15** `DirectUndec/TailModel.v` (~440 lines). In
  `Universality/` the left-hand side `bal_star` also prefixes the
  detectors on the right, so the omega model's absorbing tokens cannot
  separate the two sides. The new model is plain `lang` over a monoid of
  finite elements, tokens `(t, k, u)` with a finite tail, and junk. Only the
  star changes: `star' A = A* ⋅ (1 ⊔ Z A ⋅ A*)`. Everything except star
  unfolding is inherited from `KA/lang.v`, which made it simpler than
  `OmegaModel.v`.
- **02:15-02:36** `DirectUndec/UnivDirect.v` (~430 lines): the run as an
  infinite word `W`, token-freeness of all detectors (by a small tactic),
  and the refutation. It reuses `UnivEncoding.v`'s language-level soundness
  lemmas (`win_sound`, `nobad_run`, `run_parse`) on finite prefixes of `W`.
  Most time went into unification noise: section-variable arguments of
  `UnivEncoding.v` lemmas (`l_w_*` take `q0`), `/=` unfolding definitions
  that `lia` then treats as different atoms, and `1` elaborated as
  `monoid_one` vs `prod_one`. Axiom-free; `nix build` passes.

