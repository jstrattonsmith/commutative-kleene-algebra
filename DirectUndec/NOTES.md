# DirectUndec: undecidability of pre-KA term equality without effective inseparability

Goal (set 2026-11-19): a direct many-one reduction from a standard halting
problem to pre-KA term equality, with no `CT_L`/`MP`, and without using
effective inseparability (explicitly, or implicitly via the `T_L` route).

## Log

- **01:12** Start. Branched `direct-undec` from `main`.
- **01:12-01:24** Read `CKAUndec/Encoding.v`, `KA/pre_ka.v`, `KA/lang.v`,
  `KA/repr_rel.v`, and the undecidability library's `undecidable` and MM2
  problems. Design (below) fixed.
- **01:24-01:31** `DirectUndec/OmegaModel.v` (~520 lines): the omega-token
  pre-KA model, generic over a monoid `M` and a sequence `r`. Compiles.
  Mostly routine; the obstacles were Program obligations, nested bullets,
  and setoid rewriting under binders (worked around with `/=`).
- **01:31-01:39** `DirectUndec/NonHalting.v` (~240 lines): for a
  non-terminating run, `red_lb P s1 ⋢ red_ub P` (`red_lb_not_le_red_ub`),
  hence `red_leq_sound`/`red_leq_complete`. Compiles, admit-free. The proof
  needed only token bookkeeping on `red_ub`: the `dpseudo_top` star cannot
  produce run tokens (its body only contains one-letter pairs, while run
  steps have at least two letters per side), `inj2(pad_lang _)` has empty
  left components, and every token of the error term comes after an
  explicit mismatch.
- **01:39-01:45** `DirectUndec/Undec.v` (~190 lines): the reduction to term
  equality over the fixed carrier `list nat * list nat`, and
  `PreKA_EQ_undec : undecidable PreKA_EQ` (the library's notion). Also
  `PreKA_EQ_reduction`, the two halves of the reduction.
  `Print Assumptions PreKA_EQ_undec`: *Closed under the global context*
  (no axioms, no `CT_L`, no `MP`). No `coq-synthetic-computability` module is
  even loaded. `nix build` passes.

**Pre-KA goal reached in about 33 minutes of wall-clock time** (01:12-01:45),
in about 950 lines.
- **01:45-01:51** `DirectUndec/FKALoop.v` (~190 lines): why this does not
  carry over to the free KA. `fka_red_leq_closed`: if the configurations
  reachable from `s1` form a finite, step-closed set with no halting
  configuration other than `(0,(0,0))`, KA proves `red_lb ⊑ red_ub` (star
  induction with a finite invariant). `fka_red_leq_loop`: this holds for the
  two-instruction machine `[inc_a; dec_a 1]`, which never halts
  (`loop_not_terminates`). Hence `fka_red_leq_not_terminates_fails`. Admit-
  and axiom-free.
