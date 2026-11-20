# Three routes to Σ⁰₁-completeness

This compares three ways to prove that the case studies in
`commutative-kleene-algebra` (branch `direct-undec`) are m-complete
(Σ⁰₁-complete). All three are formalized. `Comparison/Routes.v` puts their
statements side by side, and its `Print Assumptions` output lists exactly the
hypotheses each one needs.

## The point

Effective inseparability (EI), or the closely related "sandwich" lemma,
gives a **portable interface**. Each case study only has to supply an
encoding of two-counter machines that is correct on *halting* runs, plus
enumerability. One generic lemma, shared by all case studies, does the
rest. The direct reduction from halting needs much more work, and that work
is **bespoke to this setting**. Divergent runs must be refuted, which takes
about 1,400 lines of custom models plus per-encoding arguments. In KA it is
impossible: KA proves the inequality for some divergent machines.

## The three routes

The sandwich is still an inseparability argument:
- it uses the concrete pair of halting sets `A0_L` (output 1) and `B1_L`
  (output 0);
- its proof (Smullyan's race) is the same diagonal construction that proves
  `A0_L` and `B1_L` effectively inseparable.

What it drops is the abstract `eff_insep` predicate and the Myhill step
(creative → m-complete).

| Route | m-completeness needs | Machine correctness needed | Where |
|---|---|---|---|
| `eff_insep` → creative → Myhill | `CT_L` + `MP` | halting runs only | `Comparison/Routes.v` (`*_EI`) |
| Sandwich between `A0_L`/`B1_L` | `CT_L` | halting runs only | `CKAUndec/`, `Universality/` |
| Direct reduction from halting | `CT_L` (undecidability needs no axioms) | divergent runs must also be refuted | `DirectUndec/` |

The `MP` in the first row is unavoidable, not a gap in the proofs.
coq-synthetic-computability proves that "enumerable and `eff_insep` from
`B1_L` → m-complete" implies `MP` (`MPFree_L.v`,
`MP_of_eff_insep_L_m_complete`). More generally, "creative → m-complete" is
equivalent to `MP` (`MPFree.v`, `creative_m_complete_iff_MP`). For plain
undecidability, the EI route needs only `CT_L`, through creativity
(`K_undecidable_EI` in `Routes.v`).

The EI and sandwich routes differ in exactly one step: how an enumerable set
`K_of Pred` becomes m-complete.
- Sandwich: `m_complete_K_of`.
- EI: `m_complete_of_eff_insep_L` applied to `eff_insep_K_of_B1_L`; this
  step needs `MP`.

Everything else is shared:
- the machine connection `Hc`;
- enumerability of `K_of Pred`;
- the reduction out of `K_of Pred`.

## What each choice costs

**Removing the EI dead ends**, i.e. going sandwich-only, would cut roughly
90–110 of about 620 lines.
- `CKAUndec/K.v` (91 lines):
  - `eff_insep_K_B1_L` (Theorem 17) and `eff_insep_partial_K_B1_L` go,
    along with most of the header.
  - `A0_L_subset_K` and `K_B1_L_disjoint` are already unused.
  - What is left is `Definition K c := K_of (R_target c)`, which could move
    into `KEnumerable.v`, so the file would disappear.
- `CKAUndec/KMComplete.v`: `K_creative` and its comment, about 25 lines.
- `CKAUndec/BinaryAlphabetMComplete.v`: `eff_insep_K_bin_B1_L`, 10 lines.
- Imports: `EA_L_Myhill` and `EffectiveInseparability_L` would no longer be
  needed. The repo would then stop exercising the library's
  `EffectiveInseparability.v`, `EA_L_Myhill.v` and `eff_insep_K_of_B1_L`.
  That matters if this repo is meant to be the library's case study.

**Keeping a parallel EI route** costs about 90 lines, all instantiation and
no duplicated proofs. In `Comparison/Routes.v` this is:
- the EI step `K_of_m_complete_EI`;
- the generic `m_complete_of_K_of_EI`;
- six short twins (`KA_ineq`, `KA_ineq_bin` and the four universality
  problems), about 8 lines each.

Before the switch to the sandwich (commit `516065d`), EI was the only route,
and `KMComplete.v` was 174 lines, against 119 now.

So the trade is about even: roughly 100 lines saved by going sandwich-only,
or about 90 added to keep both side by side. Size is not the deciding
factor; what the paper wants to show is.

## The three case studies

| Case study | EI results | Sandwich | Direct reduction |
|---|---|---|---|
| CKA encoding (`K`, `KA_ineq`) | `eff_insep_K_B1_L`, `K_creative` | yes | yes (`PreKA_EQ`) |
| CKA encoding in KA (`KA_ineq_fka`) | `Routes.v` only | yes | **provably fails** |
| Binary alphabet | `eff_insep_K_bin_B1_L` | yes | yes (`PreKA_EQ_bin`) |
| Universality, pre-KA (`Univ`, `Univ_bin`) | `Routes.v` only | yes | `Univ` only (`UNIV`) |
| Universality, KA (`Univ_top`, `_bin`) | `Routes.v` only | yes | **provably fails** (`Univ_top`) |

`Universality/` never stated `eff_insep` for its sets. It used EI only
implicitly, through the old generic lemma. Its EI twins in `Routes.v` are
new, and they cost the same few lines per theorem.

The direct route's problems are close to the others but not literally the
same. `PreKA_EQ` and `PreKA_EQ_bin` are term *equality* over one fixed
carrier, not the per-machine inequality relation `KA_ineq`. `UNIV` puts the
machine's alphabet into the instance.

This gives a clear story:
- The direct route needs divergent runs to be refuted. That takes about
  1,400 lines of models (`OmegaModel.v`, `TailModel.v`, `NonHalting.v`).
  It is impossible in KA: KA proves the inequality for some divergent
  machines, for the CKA encoding (`FKALoop.v`) and for universality
  (`FKAUnivLoop.v`: whenever the start configuration lies on a cycle).
- The sandwich only needs correctness on halting runs. It is the only route
  that reaches the KA results.
- The CKA encoding shows both on one problem. Adding Kozen's two
  star-induction axioms (pre-KA → KA) breaks the direct reduction:
  `red_leq_fka_direct_fails` in `Routes.v` says the KA inequality does not
  imply termination. The same interface still gives
  `KA_ineq_fka_m_complete_sandwich` (`CT_L`) and `KA_ineq_fka_m_complete_EI`
  (`CT_L` + `MP`). The KA version took about 160 new lines:
  `CKAUndec/FKAMComplete.v` (112), plus a language-level form of the
  encoding's soundness (`mm2_R_soundness_lang`, `KA/repr_rel.v`'s
  `repr_rel_rtc_soundness_lang`) and enumerability of the whole KA
  ordering (`KA/ka_enumerable.v`'s `fka_le_enumerable`).
- The EI predicate is a more abstract way to state the same sandwich, and
  that abstraction costs `MP` for m-completeness.

## Proof dependencies

Line counts are approximate. "SC" is coq-synthetic-computability and "LibUndec"
is coq-library-undecidability.

```
SHARED BY ALL THREE ROUTES
  KA/ framework: algebra, pre_ka, lang, repr_rel,     (~5,300)
    bounded_output, automata
  CKAUndec/Encoding.v: MM2 machines as KA terms,      (~1,365)
    correct on HALTING runs (paper Thms 15-16)
  LibUndec: MM2, FRACTRAN
  Binary-alphabet transport (KA/*Transport.v),        (~425)
    for the binary case studies
  Universality/ encodings (balanced, UnivEncoding,    (~2,100)
    BalancedBinary, BalancedKA, UnivTop)

        |                                      |
        v                                      v
EI AND SANDWICH (shared part)            DIRECT
  Enumerability of KA derivations:         Refuting DIVERGENT runs
    KA/rules_ / preka_ / ka_enumerable       (bespoke to pre-KA):
    (~590), CKAUndec/KEnumerable.v (~95)     OmegaModel.v  (~560) omega-
  Machines from L: SC T_L_Uniform,             token pre-KA model
    T_L_Extract (~445);                      NonHalting.v  (~385) chain
    CKAUndec/Glue/TLToRTarget.v (~155)         refutation, red_leq iff
    (FRACTRAN -> MM2 compile + splice;         halting
    also used by the direct route)           TailModel.v   (~440) second
  Connections per case study                   model, for universality
    (Glue/BinaryAlphabetConnection,
    UnivConnection; ~95)                     Per-encoding refutations:
  The sandwich: K_of Pred lies between         Binary.v (~340, re-proves
    A0_L and B1_L                                parts of BinaryAlphabet.v)
    (SC T_L_Bridge.v, ~120)                    UnivDirect.v (~490)
  The halting pair A0_L/B1_L and the race    Fixed-carrier encoding of
    as L code                                  letters (Undec.v, ~240)
    (SC EffectiveInseparability_L.v, ~365)   Undecidability, no axioms:
  CT_L, and EA from CT_L (SC CT.v, EA_L.v)     LibUndec SBTM -> ... ->
                                               MM2 chain
        |                                    m-completeness (CT_L):
   +----+---------------+                      SigmaComplete.v (~230):
   v                    v                      halting m-complete via
SANDWICH             EI                        EPF_L + TLToRTarget's
  SC MPFree.v:         SC Effective-           machine; halt_sound
    separator_m_       Inseparability.v           |
    complete (race)    (~325): eff_insep,         v
  SC MPFree_L.v:       superset transport      PreKA_EQ, PreKA_EQ_bin,
    m_complete_K_of    T_L_Bridge.v:             UNIV (pre-KA only;
  CKAUndec/KMComplete    eff_insep_K_of_B1_L     no KA instance,
    m_complete_of_K_of SC EA_L_Myhill.v:         see FKALoop.v)
        |                creative_of_eff_insep_L
        |              SC simple.v: Myhill,
        |                creative -> m-complete
        |                NEEDS MP
        |                  |
        v                  v
  KA_ineq, KA_ineq_fka, KA_ineq_bin, Univ, Univ_bin, Univ_top,
  Univ_top_bin (CT_L for the sandwich; CT_L + MP for EI)
```

Reading the graph:
- All three routes share the KA framework and the encoding's correctness on
  halting runs, which is the paper's core.
- **EI and the sandwich** add generic, reusable computability:
  - enumerability of KA derivations;
  - compiling `L` into MM2;
  - the halting pair `A0_L`/`B1_L`.

  The per-case-study input is a connection lemma of about 15–50 lines. Most
  of this already lives in coq-synthetic-computability.
- **The direct route** instead needs models that refute divergent runs.
  These are specific to pre-KA and to each encoding, and they do not exist
  for KA. In exchange it needs no enumerability, and it proves
  undecidability with no axioms.

## Where to look in Rocq

`Comparison/Routes.v` has every m-completeness statement in three forms:
- `*_EI`: needs `CT_L → MP → ...`;
- `*_sandwich`: needs `CT_L → ...`;
- `*_direct`: needs `CT_L → ...`, on the direct route's problems.

It also has the undecidability variants of case study 1
(`K_undecidable_EI`, `K_undecidable_sandwich`,
`PreKA_EQ_undecidable_direct`). The two generic step lemmas
(`K_of_m_complete_EI`, `K_of_m_complete_sandwich`) sit at the top of the
file. `Print Assumptions` reports every statement as closed under the global
context: no axioms, only the explicit `CT_L`/`MP` hypotheses. Everything is
admit-free.
