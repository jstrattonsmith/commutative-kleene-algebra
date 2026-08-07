(* The bridge fact needed to redo Myhill's theorem (creative_to_m_complete)
   directly over W_L instead of an arbitrary EA instance's own numbering:
   assuming CT_L (Church's Thesis for L, already defined and equipped
   with a rich derived toolkit in coq-synthetic-computability's
   Models/CT.v -- CT_L_to_EPF_L in particular), every semi-decidable set
   has an index under W_L. Isolated in its own file so the axiom's use
   is easy to spot. *)

From Stdlib Require Import Unicode.Utf8.
Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.SemiDecidabilityFacts.
Require Import SyntheticComputability.Axioms.EPF.

Lemma CT_L_W_L_bridge :
  CT_L -> forall p : nat -> Prop, semi_decidable p -> exists c, forall x, p x <-> W_L c x.
Proof.
intros ct p [f Hf].
pose proof (CT_L_to_EPF_L ct) as epf.
pose (g := fun x : nat => mu (fun n => ret (f x n))).
destruct (epf g) as [c Hc].
exists c.
intros x.
unfold W_L.
rewrite (Hf x).
split.
- intros [n Hn].
  assert (Hgx : ter (g x)).
  { apply mu_ter. exists n. split.
    - apply ret_hasvalue'. exact Hn.
    - intros m _. eexists. apply ret_hasvalue. }
  destruct Hgx as [v Hv].
  exists v. apply (Hc x). exact Hv.
- intros [v Hv].
  apply (Hc x) in Hv.
  apply mu_hasvalue in Hv as [Htrue _].
  apply ret_hasvalue_inv in Htrue.
  exists v. exact Htrue.
Qed.
