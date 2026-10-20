# Universality: a second MM2 encoding via balanced universality

This directory holds a second, independent proof that KA with commutativity
conditions is Sigma^0_1-complete. It goes through *universality* problems
instead of the general inequality `red_lb ⊑ red_ub` used in `CKAUndec/`.
The construction adapts the universality encoding of Xu, Zhou, Walker and
Kincaid ([arXiv:2607.09635][xzwk], Section 4) to pre-KA, and then lifts
it to full universality with `Σ*` on the left in KA, using the star
induction layer in `KA/ka.v`.

The work was contributed by Arthur Azevedo de Amorim (branch
`balanced-universality`), together with `KA/ka.v` and
`KA/ka_enumerable.v` (see below). It builds on `KA/` and `CKAUndec/` but
nothing outside this directory depends on it.

## Main results

All results live in `UnivMComplete.v`. Each takes `CT_L` and `MP` as
hypotheses, exactly as `CKAUndec/KMComplete.v` does, and `Print
Assumptions` is otherwise closed.

| Theorem | Problem | Setting | Carrier |
|---|---|---|---|
| `Univ_m_complete` | `bal_star ⊑ e` | pre-KA | `list (option (mm_sym Q)) * nat`, per machine |
| `Univ_bin_m_complete` | `bal_star ⊑ e` | pre-KA | `list bool * nat`, fixed |
| `Univ_top_m_complete` | `Σ* ⊑ e` | free KA | `list (option (mm_sym Q)) * nat`, per machine |
| `Univ_top_bin_m_complete` | `Σ* ⊑ e` | free KA | `list bool * nat`, fixed |

The second component of the carrier counts a letter that commutes with
everything. `bal_star` is the star of the balanced letters `([t], 1)`, with
language `{(w, |w|)}`. `Σ*` is the star of all generators.

The encoding itself is axiom-free: `univ_completeness` and
`univ_soundness` (`UnivEncoding.v`) say that an MM2 machine halts at
`(0, (0, 0))` if and only if `bal_star ⊑ univ_ub_mm2 s1`.

### Why two left-hand sides

Pre-KA has no star induction, so `Σ* ⊑ e` cannot be reached there. The
header comment of `balanced.v` explains why the reduction would make it
decidable on the instances it produces. The pre-KA results therefore use
the non-regular slice `bal_star`. With star induction, `Σ* ≡ bal_star ⊔
unbal` holds whenever the two kinds of letter commute (`BalancedKA.v`), and
that recovers full universality in KA.

## Files

The files are listed in dependency order, matching `_CoqProject`.

**Algebra**, independent of MM2:

- `balanced.v`: the additive `nat` monoid, `bal_star`, and the pre-KA
  engine `bal_univ_complete`/`bal_univ_sound`. The engine unfolds
  `bal_star` a fixed number of times instead of using star induction.
- `BalancedBinary.v`: transports balanced universality to the fixed
  carrier `list bool * nat`.
- `BalancedKA.v`: from balanced universality to full universality in KA
  (`sigma_top_ka`, `ka_top_complete`, `ka_top_sound`).

**MM2 encoding and computability**:

- `UnivEncoding.v`: the MM2 encoding (`univ_ub`, the error detectors) and
  its soundness and completeness, both generic and for MM2, over the
  machine alphabet and the binary one.
- `UnivTop.v`: the same with `Σ*` on the left, in the free KA.
- `UnivConnection.v`: wiring from `T_L` to the universality targets. It is
  the analogue of `CKAUndec/Glue/TLToRTarget.v`.
- `UnivMComplete.v`: enumerability and m-completeness. Effective
  inseparability comes from `CKAUndec/BinaryAlphabetMComplete.v`'s generic
  `eff_insep_shape_K_of_B1_L`.

The root [`CLAUDE.md`](../CLAUDE.md) (items 30-36) gives a fuller
file-by-file description.

### Supporting files in `KA/`

Two general-purpose files came with this work but live in `KA/`, because
they are library code rather than anything specific to universality
(root `CLAUDE.md` items 14-15):

- `KA/ka.v`: Kleene algebras (`KAMixin`, Kozen's star induction rules) on
  top of `KA/pre_ka.v`'s `PreKAMixin`. Also languages as a KA, the free KA
  over a pre-KA or a monoid, the KA ordering `ka_leq`, and `pseudo_top` as
  the top element.
- `KA/ka_enumerable.v`: enumerability of free-KA derivability, the
  analogue of `KA/preka_enumerable.v` (`ka_leq_slice_enumerable_r`).

The pre-KA `slice_enumerable_r` lives in `KA/preka_enumerable.v`, beside
`slice_enumerable`.

## Interface with the rest of the development

- **Imports:** from `KA/` (`utils`, `algebra`, `pre_ka`, `lang`,
  `preka_enumerable`, `ka`, `ka_enumerable`, `BinaryAlphabetTransport`),
  from `CKAUndec/` (`Encoding`, `BinaryAlphabetMComplete`,
  `Glue/RtcBridge`, `Glue/TLToRTarget`), and from `coq-synthetic-computability`/`coq-library-undecidability`.
- **One change outside this directory:** `CKAUndec/Encoding.v`'s
  `translate_state_spec` and `mm2_prog_spec` are no longer `Local`, so
  that `UnivEncoding.v` can reuse its MM2 adapter.
- **Style:** unlike `CKAUndec/`, every file here uses ssreflect tactics
  throughout, as `KA/` does.

## Building

There is no separate build step. The files are listed in the root
`_CoqProject` under the logical prefix `kacc.Universality`, so the usual
`nix build` or `nix develop -c make` at the repository root checks them.
To check a single file:

```bash
nix develop -c bash -c 'coqc -Q . kacc Universality/UnivMComplete.v'
```

[xzwk]: https://arxiv.org/abs/2607.09635
