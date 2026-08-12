(* Bridges T_L/Theta_ours_L (Rocq's own L-interpreter, from the sibling
   coq-synthetic-computability project) to T_L_Uniform.R_TL, the
   mu-search-shaped uniform relation used throughout the CKA-specific
   binary-alphabet argument (CKA.Glue.TLToRTarget.v and beyond).

   NOTE 2026-08-14: this file used to also contain (a) an MM2/Theta_ours_MM2
   -level splice construction (Psplice_theta_divides/not_divides, A0_L',
   A0_L'_enumerable) and (b) its own CKA-specific payoff (A0_L_subset,
   A0_L'_B1_L_disjoint, A0_L_prime_exists). Both were confirmed, by a
   full-codebase dependency check, to be dead: nothing downstream ever
   consumes A0_L_prime_exists or any of the lemmas feeding only into it --
   CKA.K.v and (what was) Theorem19_BinaryAlphabet.v only ever
   used theta_ours_L_iff/R_TL_iff, i.e. exactly what's left in this file.
   Removed rather than kept as a "not on critical path" artifact, since
   unlike those (which are self-contained explorations), this dead code
   was framed as if it were part of the main argument's own scaffolding.
   The removed content is still in git history if ever needed again.

   One lemma from that removed content, mma_mm2_state_22, turned out to
   still be genuinely used (by Theorem19_BinaryAlphabet.v) -- kept here for
   now; it's MM2-generic (a fact about mma_mm2_state on a 2-vector, no KA
   or L content) and belongs in MM2/Splice.v once that split happens. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From Undecidability.MinskyMachines Require Import MM2 MMA.
From Undecidability.Shared.Libs.DLW Require Import vec.
Import vec_notations.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.Shared.partial.

Lemma mma_mm2_state_22 (i x y : nat) : mma_mm2_state (i, x ## y ## vec_nil) = (i, (x, y)).
Proof. reflexivity. Qed.

(* T_L/Theta_ours_L (Theta_ours_L's own plain hasvalue) vs R_TL (T_L_Uniform's
   mu-search over TL_bit) are ultimately just "T_L i j eventually outputs m,"
   phrased through different scaffolding -- this bridges the two, including
   finding a LEAST witness n for the mu-search side (T_L is monotonic, so
   once it outputs Some m at any n it does so at all larger n too, but the
   search specifically wants the first such n). *)

Lemma theta_ours_L_iff (c y v : nat) : Θ_ours_L c y =! v <-> exists n, T_L c y n = Some v.
Proof. unfold Θ_ours_L, θ_L, hasvalue. reflexivity. Qed.

Lemma T_L_first_or_none (c y n : nat) :
  (forall k, k <= n -> T_L c y k = None) \/
  (exists n0 v0, n0 <= n /\ T_L c y n0 = Some v0 /\ forall k, k < n0 -> T_L c y k = None).
Proof.
induction n as [| n' [IHnone | [n0 [v0 [Hn0 [Hval Hmin]]]]]].
- destruct (T_L c y 0) as [v0|] eqn:E0.
  + right. exists 0, v0. repeat split; auto; intros k Hk; lia.
  + left. intros k Hk. assert (k = 0) by lia. congruence.
- destruct (T_L c y (S n')) as [v0|] eqn:ES.
  + right. exists (S n'), v0. repeat split; auto.
    intros k Hk. apply IHnone. lia.
  + left. intros k Hk. destruct (Nat.eq_dec k (S n')) as [-> | Hne]; [exact ES |].
    apply IHnone. lia.
- right. exists n0, v0. repeat split; auto; lia.
Qed.

Lemma T_L_least_witness (c y v : nat) :
  (exists n, T_L c y n = Some v) ->
  exists n, T_L c y n = Some v /\ forall k, k < n -> T_L c y k = None.
Proof.
intros [n Hn].
destruct (T_L_first_or_none c y n) as [Hnone | [n0 [v0 [Hn0 [Hval Hmin]]]]].
- exfalso. specialize (Hnone n (le_n n)). congruence.
- exists n0. split; [| exact Hmin].
  pose proof (@monotonic_T_L c y) as Hmono.
  specialize (@Hmono n0 v0 Hval n Hn0).
  congruence.
Qed.

Lemma R_TL_iff (v : Vector.t nat 2) (m : nat) :
  T_L_Uniform.R_TL v m <->
  exists n, T_L (Vector.hd v) (Vector.hd (Vector.tl v)) n = Some m.
Proof.
unfold T_L_Uniform.R_TL.
set (i := Vector.hd v). set (j := Vector.hd (Vector.tl v)).
rewrite TL_val_iff.
split.
- intros [n [_ [_ Hn]]]. exists n. rewrite <- (@T_L'_eq i j n). exact Hn.
- intros Hex.
  destruct (@T_L_least_witness i j m Hex) as [n [Hn Hmin]].
  exists n. repeat split.
  + unfold TL_bit. rewrite (@T_L'_eq i j n), Hn. reflexivity.
  + intros k Hk. unfold TL_bit. rewrite (@T_L'_eq i j k), (Hmin k Hk). reflexivity.
  + rewrite (@T_L'_eq i j n). exact Hn.
Qed.
