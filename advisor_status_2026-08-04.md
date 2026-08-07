# Status update: MM2 effective inseparability, and the register-packing blocker

*2026-08-04, prepared for advisor meeting*

## 1. Where this sits in the overall project

The goal is a Rocq mechanization of undecidability of pre-Kleene algebra with
commutativity conditions (Azevedo de Amorim, Zhang, Gaboardi 2025). The proof
has two halves:

- **Algebraic encoding.** Two-counter (MM2) machine instructions are encoded
  as pre-KA terms over a commutable alphabet, with a soundness/completeness
  pair connecting MM2 reachability to a pre-KA inequality. This half
  (`mm.v` and its dependencies, ~6,600 lines across 8 files) is **done and
  admit-free**, and hasn't needed to change in weeks.
- **Effective inseparability.** A machine-realized proof that MM2's halting
  problem is effectively inseparable — the computability-theoretic fact that,
  combined with the algebraic half above, yields undecidability. This is the
  active work, and the subject of this update.

## 2. Progress over the last few days

Working in the `EffectiveInseparability_MM2*.v` files (Phase 2, "take 3," the
route through Rocq's weak call-by-value λ-calculus `L`):

- **Built `R_race`**, a single relation `Vector.t nat 3 -> nat -> Prop`
  encoding the diagonal "race" between two candidate MM2 programs `i` and
  `j` on input `y` — following the same recipe
  coq-synthetic-computability's own `Models/EffectiveInseparability_L.v`
  uses for `L`, but instantiated natively at the MM2 level. Packaging it as
  *one* relation over the whole triple `(i,j,y)`, rather than one relation
  per candidate pair, matters: `MM2_computable` is a `Prop`-level
  existential, and extracting a separate witness program for infinitely
  many pairs `(i,j)` would need a choice principle we don't have or want to
  assume.
- **Proved `L_computable_closed R_race`**, then **`R_race_MM2_computable`**
  — an actual MM2 program `P_race` realizing the race for the whole family
  at once — by composing seven already-proven library steps:
  `L_computable_closed → MMA_computable → TM_computable → BSM_computable →
  MM_computable → FRACTRAN_computable → MMA2_computable → MM2_computable`.
- **Closed a genuine gap in coq-library-undecidability** to make the last
  two steps possible: the library's own `MM_to_MMA2` compiler only proves
  that *termination* transfers from FRACTRAN to MMA2/MM2, which is all its
  own MM2-undecidability proof needs. We needed the actual *output value*
  to transfer (the race must recover a real winner bit, not just "did it
  halt"). New file `FRACTRAN_computable_to_MM2_computable.v` proves the
  FRACTRAN → MMA2 → MM2 leg is output-preserving, tracked via
  `qs(1)^m`-divisibility, the same idiom `MM2_computable`'s own definition
  already uses. This is generic (not specific to the race), and a
  reasonable candidate to contribute back upstream.
- Everything through this point compiles, axiom-free, no admits (commit
  `a8022a8`).
- Separately: expanded the CPP paper draft to use the real 12-page
  SIGPLAN limit rather than an assumed 6. Per your earlier call, the
  effective-inseparability section is written up *as if* finished — ahead
  of where the mechanization actually is — flagging that here so it isn't
  mistaken for a completeness claim.

## 3. The current blocker

What's left is to turn `P_race` (the general, all-triples-at-once program)
into a concrete, standalone MM2 program `η(i,j)` for one *fixed* candidate
pair, callable exactly the way `mm.v`'s own (untouched, already-proven)
soundness/completeness theorems call machines: from the raw state
`(1,(y,0))` — `y` sitting directly, unencoded, in one register.

The problem is a **calling-convention mismatch**. `P_race`'s own convention
— inherited from `FRACTRAN_computable`'s definition, several links back in
the chain above — represents its whole input vector via **prime-power
packing**: it expects to start from register value
`ps(1) · qs(2)^i · qs(3)^j · qs(4)^y`, not `(i,j,y)` as three separate raw
numbers.

- `i` and `j` are fine: once we fix a candidate pair, `qs(2)^i · qs(3)^j` is
  just some fixed constant, splice-able in as a straight-line block of
  increment instructions.
- `y` is not fine. It only arrives at MM2 *runtime*, live, in the raw
  register `mm.v` hands us. So `η(i,j)` needs an actual MM2 program — built
  from nothing but unary increment/decrement — that computes `qs(4)^y` from
  a raw register value `y`. An honest exponentiation subroutine, with only
  two registers to work with.

## 4. Why this isn't routine (the "exponential problem")

The naive approach — "while `y > 0`: decrement `y`, multiply the
accumulator by `qs(4)`" — needs three quantities alive simultaneously: the
remaining-`y` counter, the accumulator, and a scratch register (multiplying
a register by a fixed constant in place is destructive — it drains the
source while rebuilding the destination, needing a register distinct from
both). MM2 has exactly two registers.

I've spent real effort ruling out shortcuts, from a few independent
directions:

- **Direct construction attempts** (several different packing schemes)
  were all circular in the same way: each one needs `y` already available
  in *some* exponentiated form before it can bootstrap — which is exactly
  the problem being restated, not solved.
- **Checked whether the library's own machinery ever does this at
  runtime — it doesn't.** Read `FRACTRAN_computable`'s state-encoding
  definition and `MM_computable_to_FRACTRAN_computable`'s simulation
  directly. The prime-power packing is always a Gallina-level, *proof
  statement* choice — a mathematical fact about what number a machine's
  caller must supply — never something a compiled MM/MMA/MM2 program
  computes from a raw value at runtime. Every model in
  coq-library-undecidability gets to choose its own encoding of the input
  up front; none of them ever need to convert between two
  independently-fixed calling conventions the way we do here.
- **Checked whether a generic register-reduction compiler could supply
  the missing third register "for free."** `mma3_mma2_compiler` packs 3
  logical registers into 2 physical ones via a Gödel coding, and is
  already used elsewhere in the library. But its own correctness theorem
  (`compiler_t_output_sound'`) requires the physical *starting* state to
  already satisfy the packing invariant relative to the logical one —
  that's a hypothesis of the theorem, not something it derives. Using it
  still requires `y` pre-exponentiated as input. It relocates the problem
  one level down rather than solving it.
- **A literature check corroborates this from the outside.** The standard
  "2-counter machines are Turing complete" results assume the input
  arrives *already* Gödel-encoded; they don't solve "convert a raw unary
  input into a packed encoding at runtime" either, for the same underlying
  reason the library's own reductions don't.

So: a genuine, non-routine construction, unlike essentially everything else
in this part of the project, which has gone by composing already-proven
library lemmas.

## 5. Open questions for the meeting

Two ways forward on the table:

1. **Keep constructing a genuine 2-register algorithm** for raw `y` →
   `qs(4)^y`. Would need either real cleverness I haven't found yet, or a
   larger construction (e.g. routing through a full Turing-machine-tape
   style simulation) than "one glue subroutine."
2. **Restructure the effective-inseparability argument to avoid the bridge
   entirely** — build the race/diagonal argument natively in `mm.v`'s own
   raw calling convention from the start, rather than routing through
   `FRACTRAN`'s packed convention (which tasks #26–27 already depend on)
   and then trying to bridge back to raw at the end.

Would value your read on:

- Whether you've seen the raw-input → Gödel-encoding step handled
  constructively anywhere — this feels like it might be classical/folklore
  but not written down in a form I can point to.
- Whether option 2 is worth the larger restructuring it implies, given how
  much of the already-completed chain (tasks #26–27) is built around the
  FRACTRAN-routed convention.
