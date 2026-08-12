(* Generic effective-inseparability machinery, extracted from
   CKAUndec.K.v. Zero MM2/KA content -- parametrized over an
   arbitrary numbering W and sets A/B/A', reusable for any effective-
   inseparability argument that wants the unbundled (no-enumerability-
   required) notion. Genuinely upstreamable to the sibling
   coq-synthetic-computability project as-is.

   The unbundled notion (Kuznetsov's Definition 5 / Azevedo de Amorim et
   al.'s Theorem 17 statement, verbatim): disjointness plus a witness
   function, no enumerability. The *library's* eff_insep_shape bundles
   `enumerable A` into its own definition (for Proposition 7's
   convenience, not because Definition 5/Theorem 17 require it); this
   file's eff_insep_core drops that requirement, and
   eff_insep_core_superset is Proposition 9 / eff_insep_shape_superset
   restated without the enumerable-A' plumbing (same proof shape as
   EffectiveInseparabilityTransport.v's eff_insep_shape_superset). *)

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.Shared.partial.

Definition eff_insep_core (W : nat -> nat -> Prop) (A B : nat -> Prop) : Prop :=
  (forall x, A x -> ~ B x) /\
  exists f : nat -> nat -> part nat,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k, hasvalue (f i j) k /\ ~ W i k /\ ~ W j k.

Lemma eff_insep_shape_to_core (W : nat -> nat -> Prop) (A B : nat -> Prop) :
  eff_insep_shape W A B -> eff_insep_core W A B.
Proof.
intros [_ [_ [Hdisj [f Hf]]]]. split; [exact Hdisj |]. exists f. exact Hf.
Qed.

Lemma eff_insep_core_superset (W : nat -> nat -> Prop) (A B A' : nat -> Prop) :
  eff_insep_core W A B ->
  (forall x, A x -> A' x) ->
  (forall x, A' x -> ~ B x) ->
  eff_insep_core W A' B.
Proof.
intros [Hdisj [f Hf]] Hsub Hdisj'.
split; [exact Hdisj' |].
exists f. intros i j Hi Hj Hij.
apply Hf.
- intros x Hx. apply Hi, Hsub, Hx.
- exact Hj.
- exact Hij.
Qed.
