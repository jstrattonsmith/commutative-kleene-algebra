# RuleEnum: inductively generated predicates are enumerable

A small Rocq development of one general fact. If a predicate `R : X -> Prop`
is the least set closed under a family of rules, it is enumerable, provided

- the rule labels `L` are enumerable, and
- each rule is a computable partial function `rule : L -> list X -> option X`
  that takes the premises to the conclusion.

```coq
Theorem rules_enumerable (R : X -> Prop) :
  enumerableT L ->
  (forall l xs x, rule l xs = Some x -> Forall R xs -> R x) ->       (* R is closed *)
  (forall S : X -> Prop,
     (forall l xs x, rule l xs = Some x -> Forall S xs -> S x) ->
     forall x, R x -> S x) ->                                         (* R is least *)
  enumerable R.
```

`rules_enumerator` is the informative version: it names the enumerator
`rules_enum eL` explicitly. A derivation is encoded as a postfix program
`list (L * nat)`. The instruction `(l, n)` pops `n` conclusions off a stack
and pushes `rule l` applied to them. The enumerator lists all programs and
keeps those that leave exactly one element on the empty stack.

## The recommended interface: `RuleSystem.v`

`rules_enumerable` takes a partial rule function, and proving it closed
means inverting that function's `match`. `RuleSystem.v` hides this. Each
label lists its premises and its conclusion:

```coq
Theorem rule_system_enumerable (R : X -> Prop) :
  enumerableT L -> enumerable Ax ->
  closed_under premises conclusion Ax R ->          (* constructor-shaped *)
  (forall S, closed_under premises conclusion Ax S -> forall x, R x -> S x) ->
  enumerable R.
```

Both obligations then have the shape of the predicate's own constructors,
and tactics handle most of them. Here is the whole proof for `le` in
`Mutual.v`:

```coq
  apply (rule_system_enumerable_noax nat_pair_eq_dec le_premises le_conclusion).
  - exact le_label_enumerableT.
  - rules_closed.                                   (* closed: automatic *)
  - intros S HS [n m]; cbn; induction 1; by_rule.   (* least: automatic *)
```

- `rules_closed` gives one goal per label, with the premises as
  hypotheses, and tries the predicate's constructors on each.
- `by_rule` tries each constructor of the label type, filling in its
  arguments by unification with the goal and the premises from the
  context.
- `by_rule_with l` names the label when its data has to be computed.
- `Ax` holds base facts known only through an enumerator. Use
  `rule_system_enumerable_noax` when there are none.
- For mutual predicates, `rule_system_enumerable_mutual` works on tagged
  judgments `A + B`. Its minimality obligation is exactly the conclusion
  of a `Combined Scheme`.

The interface needs decidable equality on judgments and a total
`conclusion`. So a label carries data that is always valid: for example
a split `G1 ++ t :: G2` instead of an index into `G` (see
`HSCEnumerable.v`, which proves the same theorem both ways).

## Applying it to an inductive predicate

Any finitary inductive predicate fits, as long as its constructors'
non-recursive arguments range over enumerable types and its side conditions
are decidable:

1. **Labels.** Make one label per constructor, carrying all of that
   constructor's non-recursive arguments (terms, substitutions, the
   conclusion's context, an index into an enumerator, ...).
2. **Rule.** `rule l xs` recomputes the expected premises from the label,
   compares them with `xs` using decidable equality (and checks any side
   condition), and returns the conclusion.
3. **Closed** is one constructor application per label.
4. **Least** is `induction` on the predicate, mapping each constructor to
   its label.

The label can carry anything that is hard to recover from the premises
(for example `psi` in `ExE` from `psi[↑]`, or `A` in `AllI` from
`map ↑ A`), so the rule never has to invert an operation.
`Closures.v` works this out for `clos_refl_trans` of an enumerable
relation.

## Files

| File | Depends on | Contents |
|---|---|---|
| `RuleEnum.v` | Rocq Stdlib | Enumerability notions; enumerators for `nat`, products, sums, lists and surjective images; projections `enumerable_inl`/`_inr`/`_sigT`; `checker_enumerable`; `enumerable_reduce`; `rules_enumerable` |
| `RuleSystem.v` | Stdlib | Schematic interface (`rule_system_enumerable`, `_noax`, `_mutual`) and the tactics `rules_closed`, `by_rule`, `by_rule_with`, `by_axiom` |
| `Mutual.v` | Stdlib | Worked examples: `le_enumerable`, and mutual `even`/`odd` via `Combined Scheme` |
| `Closures.v` | Stdlib | `clos_refl_trans_enumerable` |
| `CoRuleEnum.v` | Stdlib | The coinductive dual: the greatest set consistent with a finitely branching backward rule system `back : X -> list (list X)` is co-enumerable (`coinductive_coenumerable`, from `MP` and a pigeonhole/König hypothesis that `LLPO` provides); refutations are enumerable with no axioms (`refutable_enumerable`); worked example `diverges_coenumerable` |
| `RuleEnumStdpp.v` | stdpp | `Countable X -> enumerableT X`; `EqDecision` as a sumbool decider |
| `RuleEnumUndec.v` | coq-library-undecidability | `enumerator`/`enumerable`/`enumerableT` agree with the library's (by `reflexivity`) |
| `HSCEnumerable.v` | coq-library-undecidability (`HilbertCalculi/HSC.v` only) | Hilbert-calculus derivability is enumerable, uniformly in the axioms (`hsc_enumerable`, `HSC_PRV_enumerable`); the substitution in `hsc_var` is replaced by its finite prefix in the label; `formula_enumerableT` is the `R := fun _ => True` instance |

`RuleEnum.v`'s definitions are written out to match the [Coq Library of
Undecidability Proofs][undec] (`Synthetic/Definitions.v`) exactly, so a
result proved here is a result there by conversion.

## Building

Files import each other as `RuleEnum.<File>`. Inside
commutative-kleene-algebra (`-R . kacc`) this resolves to
`kacc.RuleEnum.<File>`. In a standalone repo, use

```
-Q . RuleEnum
RuleEnum.v
RuleSystem.v
Mutual.v
Closures.v
CoRuleEnum.v
RuleEnumStdpp.v
RuleEnumUndec.v
HSCEnumerable.v
```

and drop either adapter if you don't want its dependency.

## Candidate applications

These are inductive relations in coq-library-undecidability with
undecidability proofs but no enumerability proof (the Hilbert calculus,
previously on this list, is now done in `HSCEnumerable.v`):

- ILL/CLL/IMSELL/EILL sequent calculi
- System F and intersection-type assignment
- string rewriting and CFG `rewt` (via `Closures.v`)
- machine evaluation relations

`FOL/Deduction/FullNDFacts.v` (`enum_prv`) and `PCP/Util/PCP_facts.v`
(`enum_PCP'`) prove natural deduction and PCP derivability enumerable by
hand, with one list comprehension per rule. Each is an instance of this
theorem.

[undec]: https://github.com/uds-psl/coq-library-undecidability
