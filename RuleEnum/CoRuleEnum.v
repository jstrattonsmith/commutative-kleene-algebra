(* The coinductive dual of RuleEnum.v. A predicate that is the greatest
   set consistent with a finitely branching, computable backward rule
   system is co-enumerable: its complement is enumerable.

   The rule system is given backwards, as [back : X -> list (list X)].
   [back x] lists every way of concluding [x], each as its finite list of
   premises. [R] is consistent if each of its elements is concluded by
   some entry of [back] whose premises are again in [R], and it is the
   greatest such set if it contains every other consistent set (the
   coinduction principle).

   Membership is approximated from above by the decidable stages
   [stage n]. Dropping out at some stage is a finite refutation, so the
   refutable elements are enumerable with no axioms
   ([refutable_enumerable]). Identifying them with the complement of [R]
   needs two classical principles, taken as explicit hypotheses:

   - [pigeon (back x)]: from "for each n, some premise list survives n
     stages" conclude "some premise list survives all stages". This is
     König's lemma for the tree of backward derivations. It holds with no
     axioms when [back x] has at most one entry ([pigeon_nil],
     [pigeon_single]), and for all finite lists under [LLPO]
     ([pigeon_LLPO]).
   - [MP] (Markov's principle): to turn "[x] does not survive every stage"
     into an explicit stage where it drops out.

   Depends only on the Rocq Stdlib (and RuleEnum.v). *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
Require Import RuleEnum.RuleEnum.

(** * Classical principles *)

Definition MP : Prop :=
  forall f : nat -> bool, ~ ~ (exists n, f n = true) -> exists n, f n = true.

(** The De Morgan form of the lesser limited principle of omniscience:
    of two Σ⁰₁ statements that are not both true, one is false. *)
Definition LLPO : Prop :=
  forall f g : nat -> bool,
  ~ ((exists n, f n = true) /\ (exists n, g n = true)) ->
  (forall n, f n = false) \/ (forall n, g n = false).

(** Finite pigeonhole for decreasing families: if at every [n] some
    element of [F] passes [P _ n], then some element passes at every
    [n]. *)
Definition pigeon {A} (F : list A) : Prop :=
  forall P : A -> nat -> bool,
  (forall a n, P a (S n) = true -> P a n = true) ->
  (forall n, exists a, In a F /\ P a n = true) ->
  exists a, In a F /\ forall n, P a n = true.

Lemma pigeon_nil {A} : pigeon (@nil A).
Proof. intros P _ H; destruct (H 0) as [a [[] _]]. Qed.

Lemma pigeon_single {A} (a : A) : pigeon [a].
Proof.
  intros P _ H; exists a; split; [now left|].
  intros n; destruct (H n) as [b [[<-|[]] Hb]]; exact Hb.
Qed.

Lemma decreasing_le (P : nat -> bool) :
  (forall n, P (S n) = true -> P n = true) ->
  forall n m, n <= m -> P m = true -> P n = true.
Proof. intros HP n m Hle; induction Hle; auto. Qed.

Lemma pigeon_LLPO {A} : LLPO -> forall F : list A, pigeon F.
Proof.
  intros llpo F; induction F as [|a F IH]; [apply pigeon_nil|].
  intros P Hdec H.
  destruct (llpo (fun n => negb (P a n))
                 (fun n => negb (existsb (fun b => P b n) F)))
    as [Ha|HF]; cbn beta in *.
  - (* [a] and the rest of [F] cannot both fail eventually: at the later
       of the two stages, [H] gives a survivor among them. *)
    intros [[n Hn] [m Hm]]; apply negb_true_iff in Hn, Hm.
    destruct (H (Nat.max n m)) as [b [[<-|Hb] Hbv]].
    + rewrite (decreasing_le _ (Hdec a) n _ (Nat.le_max_l n m) Hbv) in Hn.
      discriminate.
    + enough (existsb (fun b => P b m) F = true) by congruence.
      apply existsb_exists; exists b; split; [exact Hb|].
      exact (decreasing_le _ (Hdec b) m _ (Nat.le_max_r n m) Hbv).
  - exists a; split; [now left|].
    intros n; specialize (Ha n); now apply negb_false_iff in Ha.
  - destruct (IH P Hdec) as [b [Hb Hbv]].
    + intros n; specialize (HF n); apply negb_false_iff, existsb_exists in HF.
      exact HF.
    + exists b; split; [now right | exact Hbv].
Qed.

(** * Backward rule systems *)

Section CoRules.

Context {X : Type} (back : X -> list (list X)).

(** [stage n x]: [x] survives [n] levels of backward unfolding. *)
Fixpoint stage (n : nat) (x : X) : bool :=
  match n with
  | 0 => true
  | S n => existsb (forallb (stage n)) (back x)
  end.

Lemma stage_decreasing n x : stage (S n) x = true -> stage n x = true.
Proof.
  revert x; induction n as [|n IH]; intros x Hx; [reflexivity|].
  cbn in Hx |- *; apply existsb_exists in Hx as [ps [Hin Hps]].
  apply existsb_exists; exists ps; split; [exact Hin|].
  rewrite forallb_forall in Hps |- *.
  intros y Hy; exact (IH y (Hps y Hy)).
Qed.

(** Every element of a consistent [R] survives every stage. *)
Lemma stage_sound (R : X -> Prop) :
  (forall x, R x -> exists ps, In ps (back x) /\ Forall R ps) ->
  forall n x, R x -> stage n x = true.
Proof.
  intros Hcons n; induction n as [|n IH]; intros x Hx; [reflexivity|].
  destruct (Hcons x Hx) as [ps [Hin HF]]; cbn.
  apply existsb_exists; exists ps; split; [exact Hin|].
  apply forallb_forall; intros y Hy.
  apply IH; rewrite Forall_forall in HF; auto.
Qed.

(** If [back] is pigeonhole-finite, everything that survives every stage
    is in the greatest consistent [R]: the survivors are themselves
    consistent. *)
Lemma stages_complete (R : X -> Prop) :
  (forall S : X -> Prop,
     (forall x, S x -> exists ps, In ps (back x) /\ Forall S ps) ->
     forall x, S x -> R x) ->
  (forall x, pigeon (back x)) ->
  forall x, (forall n, stage n x = true) -> R x.
Proof.
  intros Hgr Hpig; apply Hgr; intros x Hx.
  destruct (Hpig x (fun ps n => forallb (stage n) ps)) as [ps [Hin Hps]];
    cbn beta in *.
  - intros ps n; rewrite !forallb_forall; eauto using stage_decreasing.
  - intros n; specialize (Hx (S n)); cbn in Hx.
    now apply existsb_exists in Hx.
  - exists ps; split; [exact Hin|].
    apply Forall_forall; intros y Hy n.
    specialize (Hps n); rewrite forallb_forall in Hps; auto.
Qed.

(** Refutations are enumerable, with no axioms. *)
Theorem refutable_enumerable :
  enumerableT X -> enumerable (fun x => exists n, stage n x = false).
Proof.
  intros [eX HeX].
  apply (checker_enumerable
    (D := X * nat) (fun '(x, n) => if stage n x then None else Some x)).
  - exists (prod_enum eX (fun n => Some n)).
    exact (prod_enumeratorT HeX nat_enumeratorT).
  - intros [x n] x' H.
    destruct (stage n x) eqn:E; [discriminate|].
    injection H as <-; now exists n.
  - intros x [n Hn]; exists (x, n); cbn; now rewrite Hn.
Qed.

Theorem coinductive_coenumerable (R : X -> Prop) :
  MP ->
  enumerableT X ->
  (forall x, pigeon (back x)) ->
  (forall x, R x -> exists ps, In ps (back x) /\ Forall R ps) ->
  (forall S : X -> Prop,
     (forall x, S x -> exists ps, In ps (back x) /\ Forall S ps) ->
     forall x, S x -> R x) ->
  enumerable (fun x => ~ R x).
Proof.
  intros mp HX Hpig Hcons Hgr.
  destruct (refutable_enumerable HX) as [f Hf].
  exists f; intros x; split.
  - intros HnR; apply (proj1 (Hf x)); cbn beta.
    destruct (mp (fun n => negb (stage n x))) as [n Hn]; cbn beta in *.
    + intros Hno; apply HnR, (stages_complete R Hgr Hpig).
      intros n; destruct (stage n x) eqn:E; [reflexivity|].
      exfalso; apply Hno; exists n; now rewrite E.
    + exists n; now apply negb_true_iff.
  - intros [n Hn]%Hf HR.
    now rewrite (stage_sound R Hcons n x HR) in Hn.
Qed.

Corollary coinductive_coenumerable_LLPO (R : X -> Prop) :
  MP -> LLPO ->
  enumerableT X ->
  (forall x, R x -> exists ps, In ps (back x) /\ Forall R ps) ->
  (forall S : X -> Prop,
     (forall x, S x -> exists ps, In ps (back x) /\ Forall S ps) ->
     forall x, S x -> R x) ->
  enumerable (fun x => ~ R x).
Proof.
  intros mp llpo HX.
  apply (coinductive_coenumerable R mp HX).
  intros x; now apply pigeon_LLPO.
Qed.

End CoRules.

(** * Example: divergence of a deterministic step function

    [back] has at most one entry, so no pigeonhole axiom is needed. Only
    [MP] remains: "does not diverge" is "halts", and producing the
    halting time from a proof that divergence is impossible is exactly
    Markov's principle. *)

Section Divergence.

Context {X : Type} (step : X -> option X).

CoInductive diverges : X -> Prop :=
  | diverges_step x y : step x = Some y -> diverges y -> diverges x.

Definition step_back (x : X) : list (list X) :=
  match step x with
  | Some y => [[y]]
  | None => []
  end.

Theorem diverges_coenumerable :
  MP -> enumerableT X -> enumerable (fun x => ~ diverges x).
Proof.
  intros mp HX.
  apply (coinductive_coenumerable step_back diverges mp HX).
  - intros x; unfold step_back.
    destruct (step x); [apply pigeon_single | apply pigeon_nil].
  - intros x [x' y Hs Hd]; exists [y]; unfold step_back; rewrite Hs.
    split; [now left | now repeat constructor].
  - intros S HS; cofix CIH; intros x Hx.
    destruct (HS x Hx) as [ps [Hin HF]]; unfold step_back in Hin.
    destruct (step x) as [y|] eqn:E; [|destruct Hin].
    destruct Hin as [<-|[]].
    exact (diverges_step x y E (CIH y (Forall_inv HF))).
Qed.

End Divergence.
