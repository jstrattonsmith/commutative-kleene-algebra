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
