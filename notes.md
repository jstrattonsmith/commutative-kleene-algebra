# Questions:

- QUEST spots
- reflection?
- where next?
- how to organize the file better...should I start thinking about splitting parts up into modules?
- better way to handle lemmas like lang_interp_build_l/r? interp_build_term_l/r?
- any automated tools in Rocq for checking which lemmas are/are not used?
- I realize they are tangential and not part of the proofs, but I'm puzzled by the struggle to prove zero_eq_sum and zero_eq_prod

# 11/24/25
- how to capture that Q_M is actually finite. Q_M correspond to the program index...
- how to capture "halts on" syntax?

## 11/3/25
- funding, ethics, military
- NetKAT -> internship thoughts
- RPA & courses for the spring -> independent study?
- (effective) inseparability reference

## 10/27/25
- how to get right associativity in K_Dot and K_Plus notations?
- ex_to_term is painful, I'd like to canonicalize terms. Is there a nice way to do this? I have a plan, but have not yet implemented, but if there is a built in way, it would be nice to use this.
  - If there is not yet, I think there is a path to the term equivalence...not necessarily the shortest path of equivalences, but _a_ path at least
- how to define upper bound on size of Q_M in rocq?
  - since Q_m is finite, we need to be able to actually construct R_M right?


## 10/22/25
- why are there the extra axioms in his version?
  - TEStarL, TEStarR
- thinking ahead to spring classes:
  - Operating systems independent study?
  - category theory class
  - Go language skills class
  - haskell -> just sounds fun
  - possibly HCIN 722: Human-Computer Interaction with Mobile, Wearable, and Ubiquitous Devices

## 10/6/25
### General direction questions
- X is ITP "too small" of a venue?
- RPA preparations and sense of direction?
- advice on how to read? I'm getting caught up on what I don't know and a little stuck on how to determine what is necessary to learn vs. what is not?
- special group memberships (SIGPLAN, SIGLOG, SIGSAM)
- Balancing direction/funding with what is actually interesting?
- getting involved in conferences, volunteer/reading?
- X help with conference website...
- numerical methods algos verification?
### KACC
- In defining `ka_term` I understand having the `L` and `R` constructors...but in Def 13/Lem 14 and on, we use these interchangeably, so a term $a_r a^* b^* q_r$ is actually a concatenation of a bunch of terms because $a_r$ and $q_r$ are actually injections into $\mathcal{T}\ddot{\Sigma}$
- How to represent $Q_M$?
- are $\Sigma_M$, $C_M$, $T_M$ necessary to define? I'm not sure how to pull out the $q_r$ terms for Def. 13 without having named at least $a$, $b$, $q$/$q_i$. Are the $q$'s list positions?
- reference 10: `Introduction to Automata Theory, Languages, and Computation` is checked out of the library, does Arthur have a copy?
- (un)decidability by diagonalization?
### 810 Manuscript
- Rocq vs. Coq (even with versioning)
- authoring
- submission standards
- how not to repeat a bunch of stuff from main paper?

- - -

## 9/29/25
- what is the Σ with two dots over it?
  - it is Σ ⊕ Σ
- how to construct $\mathcal{T}X$?
- Definition 12 is giving the terms that can only commute in particular ways...right?
- in Definition 13, what is the summation doing? Is it a union?
- in Theorem 16, what is $\Sigma^*_M$?
  - $\Sigma^*_M = \cup \Sigma^n | n \in \N$
- excuse me, "folklore"
### Terms to refresh precise definitions
- computable function
- recursive enumerable

- - -

## 9/22/25
- why the `L` and `R` constructors in `term` and why the `TEMultC` constructor for `term_eq`?
- what does term_scope mean for notation?
- Paper Example 1: should I code this up?
- His code: what is `Add Parametric Relation...`
- How do you formulate that someting (i.e. a different type) can satisfy the specifications given by the `kat_eq` relation and the `kat_term` type?
- will we need ssreflect??? issues with ssreflect to get Reflexive, Symmetric, Transitive, etc.
  - attempt 1: modify flake, attempting to add dependency with opam-nix, leads to errors about files being unfindable/not in the right location
  - attempt 2: modify flake, add dependency on regular pkgs.coqPackages_8_20 (the correct version that is imported by the other opam dependencies), leads to errors about there being duplicated ocaml files, which makes sense...
  - attempt 3: use `Require Import ssreflect.` as is done [in the undecidability library](https://github.com/search?q=repo:uds-psl/coq-library-undecidability%20ssreflect&type=code), but this fails at the stage of
  - then realized maybe I don't need ssreflect, attempted to copy over the code that Arthur gave, just to test locally and it...did not work due to reliance on ssreflect