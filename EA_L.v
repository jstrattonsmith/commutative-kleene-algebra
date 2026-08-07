(* Builds a genuine EA instance from CT_L + SMN (SMN_for T_L is already
   proven axiom-free in Models/CT.v -- L's own native closure support
   gives currying for free, no extra axiom needed there). This lets the
   EXISTING, already-proven generic machinery in
   ReducibilityDegrees/{simple,EffectiveInseparability}.v
   (productive/creative/creative_to_m_complete/eff_insep_to_m_complete)
   be reused directly, instead of re-deriving it from scratch against
   W_L. Only CT_L is assumed; SMN and the dovetailing enumerator
   construction are axiom-free. *)

From Stdlib Require Import Unicode.Utf8 Arith.
Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
Require Import SyntheticComputability.Synthetic.SemiDecidabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.Axioms.EPF.
Require Import SyntheticComputability.Axioms.CT.

(* --- 1. The dovetailing enumerator: for each program index c, list out
   the elements of W_L c by search over (x,n) pairs. Same index c works
   for both W_L and W(psi_L) -- no index translation needed. *)

Definition psi_L (c m : nat) : option nat :=
  let (x, n) := unembed m in
  match T_L c x n with
  | Some _ => Some x
  | None => None
  end.

Lemma theta_L_hasvalue_iff (c x v : nat) :
  hasvalue (θ_L c x) v <-> exists n, T_L c x n = Some v.
Proof. unfold θ_L, hasvalue. reflexivity. Qed.

Lemma W_psi_L_iff (c x : nat) : (exists m, psi_L c m = Some x) <-> W_L c x.
Proof.
unfold W_L, ter. setoid_rewrite theta_L_hasvalue_iff. split.
- intros [m Hm]. unfold psi_L in Hm.
  destruct (unembed m) as [x' n] eqn:E.
  destruct (T_L c x' n) as [v|] eqn:Ev; inversion Hm; subst.
  exists v. exists n. exact Ev.
- intros [v [n Hn]].
  exists (embed (x, n)). unfold psi_L. rewrite embedP, Hn. reflexivity.
Qed.

(* --- 2. The EA-building step, given CT_L. --- *)

Section BuildEA_L.

Hypothesis ct : CT_L.

Lemma EA_L_spec :
  forall p : nat -> nat -> Prop, penumerable p ->
    exists gamma : nat -> nat, parametric_enumerator (fun x => psi_L (gamma x)) p.
Proof.
intros p [f Hf].
pose (g := fun (xy n : nat) =>
  let (x, y) := unembed xy in
  match f x n with Some y' => Nat.eqb y' y | None => false end).
pose proof (CT_L_to_EPF_L ct) as epf.
pose (G := fun xy : nat => mu (fun n => ret (g xy n))).
destruct (epf G) as [c0 Hc0].
destruct SMN as [S HS].
exists (fun x => S c0 x).
intros x y.
rewrite (W_psi_L_iff (S c0 x) y).
unfold W_L, ter.
setoid_rewrite theta_L_hasvalue_iff.
setoid_rewrite <- (@HS c0 x y).
transitivity (ter (G (embed (x, y)))).
{ unfold G, ter.
  split.
  - intros Hxy. apply Hf in Hxy as [n Hn].
    assert (Htrue : g (embed (x,y)) n = true).
    { unfold g. rewrite embedP, Hn. apply PeanoNat.Nat.eqb_refl. }
    assert (Hgxy : ter (mu (fun n0 => ret (g (embed (x,y)) n0)))).
    { apply mu_ter. exists n. split.
      - apply ret_hasvalue'. exact Htrue.
      - intros m _. eexists. apply ret_hasvalue. }
    destruct Hgxy as [v Hv]. exists v. exact Hv.
  - intros [v Hv].
    apply mu_hasvalue in Hv as [Htrue _].
    apply ret_hasvalue_inv in Htrue.
    unfold g in Htrue. rewrite embedP in Htrue.
    destruct (f x v) as [y'|] eqn:Ef; [| discriminate].
    apply PeanoNat.Nat.eqb_eq in Htrue. subst y'.
    apply Hf. exists v. exact Ef. }
split.
- intros [v Hv]. exists v. apply theta_L_hasvalue_iff.
  apply (Hc0 (embed (x,y))). exact Hv.
- intros [v [n Hn]]. exists v. apply (Hc0 (embed (x,y))).
  apply theta_L_hasvalue_iff. exists n. exact Hn.
Qed.

Definition EA_L : EA := exist _ psi_L EA_L_spec.

End BuildEA_L.
