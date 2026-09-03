(* An axiom-free S-M-N/currying theorem for MM2: given a program c and a
   compile-time-constant x, SMN_S c x behaves on runtime input y exactly
   like c does on the packed pair (x, y). Uses a "2-adic valuation"
   pairing pair_xy x y := 2^x * (2*y+1) - 1 rather than embed_nat's
   Cantor pairing: for fixed x it is linear in y with a compile-time
   constant coefficient, realizable via coq-library-undecidability's
   mma_mult_cst_with_zero combinator, unlike a pairing needing runtime
   squaring.

   This construction alone doesn't give a creative-set-style
   undecidability argument: that also needs a universal MM2 machine
   simulating an arbitrary program given only as runtime data, which
   MM2's own instruction set (no non-destructive register read) cannot
   supply via elementary composition. The main argument sidesteps this
   via the T_L-based route (CKAUndec/K.v, CKAUndec/KMComplete.v), whose
   universal self-interpreter comes for free from L's reduction
   semantics. Off-critical-path; excluded from _CoqProject alongside
   MM2/Legacy/EffectiveInseparability_MM2_Race.v, which it Requires
   (via raceVal_MM2). *)

From Stdlib Require Import Arith Lia.

(* --- 0. pair_xy / unpair_xy, pure Gallina, no MM2 involved yet --------- *)

Fixpoint unpair_fuel (fuel m : nat) : nat * nat :=
  match fuel with
  | 0 => (0, 0)
  | S fuel' =>
    if Nat.even m then
      match m with
      | 0 => (0, 0)
      | _ => let '(x, y) := unpair_fuel fuel' (Nat.div2 m) in (S x, y)
      end
    else (0, Nat.div2 (m - 1))
  end.

Definition pair_xy (x y : nat) : nat := 2 ^ x * (2 * y + 1) - 1.

Definition unpair_xy (z : nat) : nat * nat := unpair_fuel (S z) (S z).

Lemma pair_xy_pos x y : 1 <= 2 ^ x * (2 * y + 1).
Proof.
assert (H : 1 <= 2 ^ x) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; lia).
nia.
Qed.

Lemma unpair_fuel_spec x y fuel :
  fuel >= 2 ^ x * (2 * y + 1) ->
  unpair_fuel fuel (2 ^ x * (2 * y + 1)) = (x, y).
Proof.
induction x as [| x' IH] in y, fuel |- *; intros Hfuel.
- cbn [Nat.pow] in *.
  assert (Hm : 1 * (2 * y + 1) = 2 * y + 1) by lia.
  rewrite Hm in Hfuel |- *.
  destruct fuel as [| fuel']; [lia |].
  cbn [unpair_fuel].
  assert (Heven : Nat.even (2 * y + 1) = false).
  { rewrite Nat.even_add, Nat.even_mul. reflexivity. }
  rewrite Heven.
  f_equal. f_equal.
  replace (2 * y + 1 - 1) with (2 * y) by lia.
  rewrite Nat.div2_double. reflexivity.
- remember (2 ^ x' * (2 * y + 1)) as m' eqn:Hm'.
  assert (Hm : 2 ^ (S x') * (2 * y + 1) = 2 * m') by (cbn [Nat.pow]; lia).
  rewrite Hm in Hfuel |- *.
  assert (Hm'pos : 1 <= m') by (rewrite Hm'; apply pair_xy_pos).
  destruct fuel as [| fuel']; [lia |].
  cbn [unpair_fuel].
  assert (Heven : Nat.even (2 * m') = true).
  { rewrite Nat.even_mul. reflexivity. }
  rewrite Heven.
  destruct (2 * m') as [| m''] eqn:Em2; [lia |].
  rewrite <- Em2.
  assert (Hdiv2 : Nat.div2 (2 * m') = m') by (rewrite Nat.div2_double; reflexivity).
  rewrite Hdiv2.
  assert (Hfuel' : fuel' >= m') by lia.
  rewrite Hm' in Hfuel' |- *.
  rewrite (IH y fuel' Hfuel').
  reflexivity.
Qed.

Lemma unpair_xy_pair_xy x y : unpair_xy (pair_xy x y) = (x, y).
Proof.
unfold unpair_xy, pair_xy.
assert (Hpos := pair_xy_pos x y).
replace (S (2 ^ x * (2 * y + 1) - 1)) with (2 ^ x * (2 * y + 1)) by lia.
apply unpair_fuel_spec. lia.
Qed.

(* --- 1. The MMA2-level prefix program: A := 2^x * A + (2^x - 1), using
   only 2 registers, via coq-library-undecidability's own already-proven
   mma_mult_cst_with_zero (multiply-register-by-constant, in place, other
   register ends at 0) plus a straight-line constant increment. -------- *)

From Stdlib Require Import List.
From Undecidability.Shared.Libs.DLW Require Import pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM2 mma_defs.
From Undecidability.MinskyMachines.MMA Require Import mma_utils.

Import vec_notations.

Lemma pos0_neq_pos1 : (pos0 : pos 2) <> pos1.
Proof. discriminate. Qed.

Definition mma_prefix (x : nat) : list (mm_instr (pos 2)) :=
  mma_mult_cst_with_zero pos0 pos1 (2 * 2 ^ x) 1
  ++ mma_incs pos0 (2 ^ x - 1).

Definition prefix_len (x : nat) : nat := 8 + 2 * 2 ^ x + (2 ^ x - 1).

Lemma prefix_len_spec x : length (mma_prefix x) = prefix_len x.
Proof.
unfold mma_prefix, prefix_len.
rewrite length_app.
rewrite (mma_mult_cst_with_zero_length pos0 pos1 (2*2^x) 1).
rewrite (mma_incs_length pos0 (2^x-1)).
lia.
Qed.

Lemma mma_prefix_spec (x y : nat) :
  sss_compute (@mma_sss 2) (1, mma_prefix x)
    (1, y ## 0 ## vec_nil)
    (1 + prefix_len x, pair_xy x y ## 0 ## vec_nil).
Proof.
unfold mma_prefix.
apply sss_compute_trans with
  (st2 := (9 + 2*2^x, (2*2^x*y) ## 0 ## vec_nil)).
- apply sss_progress_compute.
  apply subcode_sss_progress with
    (P := (1, mma_mult_cst_with_zero pos0 pos1 (2*2^x) 1)); auto.
  apply (mma_mult_cst_with_zero_progress pos0_neq_pos1).
  + rew vec.
  + f_equal; first [lia | (apply vec_pos_ext; intros p; analyse pos p; rew vec)].
- apply subcode_sss_compute with
    (P := (9 + 2*2^x, mma_incs pos0 (2^x - 1))).
  + exists (mma_mult_cst_with_zero pos0 pos1 (2*2^x) 1), nil.
    split; [now rewrite app_nil_r | ].
    rewrite (mma_mult_cst_with_zero_length pos0 pos1 (2*2^x) 1). lia.
  + apply mma_incs_compute.
    unfold pair_xy.
    apply injective_projections.
    * simpl. unfold prefix_len. lia.
    * simpl. apply vec_pos_ext. intros p. analyse pos p; rew vec; simpl; nia.
Qed.

(* --- 2. Convert the MMA2 prefix to native mm2_instr, exact-value
   preserving (no packing at all): MMA2_to_MM2.v's own mma_mm2_instr/
   mma_mm2_state correspondence is a literal register-value identity, so
   this step introduces no new encoding whatsoever. --------------------- *)

From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.
From Stdlib Require Import Relations.Relation_Operators.
Import MM2Notations.

Definition mm2_prefix (x : nat) : list mm2_instr :=
  List.map mma_mm2_instr (mma_prefix x).

Lemma mm2_prefix_length x : length (mm2_prefix x) = prefix_len x.
Proof. unfold mm2_prefix. rewrite length_map. apply prefix_len_spec. Qed.

Lemma mm2_prefix_spec (x y : nat) :
  clos_refl_trans (nat * (nat * nat)) (mm2_step (mm2_prefix x))
    (1, (y, 0)) (1 + prefix_len x, (pair_xy x y, 0)).
Proof.
generalize (MMA2_to_MM2.mma_mm2_compute_equiv (mma_prefix x)
              (1, y ## 0 ## vec_nil)
              (1 + prefix_len x, pair_xy x y ## 0 ## vec_nil)).
intros [Hfwd _].
specialize (Hfwd (mma_prefix_spec x y)).
unfold mm2_prefix.
exact Hfwd.
Qed.

(* --- 3. Splice mm2_prefix in front of a shifted copy of progOf c, via
   the generic specialization interface (MM2/Legacy/MM2_PrefixSplice.v) ------------- *)

From kacc Require Import MM2.Simulator.
From kacc Require Import MM2.Legacy.MM2_PrefixSplice.

Definition SMN_S (c x : nat) : nat := specialize (mm2_prefix x) c.

Theorem SMN_MM2 (c x y v : nat) :
  (exists n, mm2_outcome_at c (pair_xy x y) n = Some v)
  <-> (exists n, mm2_outcome_at (SMN_S c x) y n = Some v).
Proof.
unfold SMN_S.
apply specialize_correct.
intros y'. rewrite mm2_prefix_length. apply mm2_prefix_spec.
Qed.


(* --- 6. Currying eta(i,j) via two SMN invocations ----------------------
   SMN_MM2 curries ONE argument per application: running c on the packed
   value pair_xy(x,y) agrees with running SMN_S(c,x) on the raw residual y.
   Applying it TWICE, nested, curries TWO arguments away from a single
   FIXED "base" program U, giving eta(i,j) := SMN_S(SMN_S(U,i),j):

     Theta_ours_MM2 U (pair_xy i (pair_xy j y))
       ~[SMN with x:=i]~  Theta_ours_MM2 (SMN_S U i) (pair_xy j y)
       ~[SMN with x:=j]~  Theta_ours_MM2 (SMN_S (SMN_S U i) j) y

   This settles the "how do i,j,y get combined into one raw MM2 register"
   question with NO exponential packing anywhere (pair_xy nested twice is
   still just two more compile-time-constant-multiply prefixes). What's
   NOT settled by this: U itself would need Theta_ours_MM2 U (pair_xy i
   (pair_xy j y)) to actually COMPUTE raceVal_MM2 i j y for arbitrary
   (runtime-supplied) i and j -- i.e. U has to decode its own input back
   into (i,j,y) AND simulate whichever programs i and j denote. That is a
   genuine MM2-native universal-simulator requirement, independent of the
   packing question this file resolves; see the eta_via_U hypothesis
   below for the precise obligation. *)

Require Import SyntheticComputability.Shared.partial.
From kacc Require Import MM2.Legacy.EffectiveInseparability_MM2_Race.

Definition eta (U i j : nat) : nat := SMN_S (SMN_S U i) j.

Lemma outcome_iff_hasvalue (c z v : nat) :
  Θ_MM2 c z =! v <-> exists n, mm2_outcome_at c z n = Some v.
Proof.
rewrite (@partial.seval_hasvalue partial.implementation.monotonic_functions).
setoid_rewrite seval_Theta_MM2.
reflexivity.
Qed.

Section EtaViaSMN.

Variable U : nat.

(* The one remaining obligation: U, run on the doubly-packed input
   pair_xy i (pair_xy j y), must compute the race between machines i and
   j on the shared diagonal input embed(y,y) -- for ALL i, j, y, not just
   compile-time-fixed ones. Building such a U (axiom-free, as an actual
   MM2 program) is exactly as hard as building a native MM2 universal
   simulator: it must, from the runtime numbers i and j alone, look up and
   run whatever programs they encode. That is NOT solved by this file. *)
Hypothesis HU : forall i j y v,
  Θ_MM2 U (pair_xy i (pair_xy j y)) =! v <-> raceVal_MM2 i j y =! v.

Theorem eta_correct (i j y v : nat) :
  Θ_MM2 (eta U i j) y =! v <-> raceVal_MM2 i j y =! v.
Proof.
rewrite <- (HU i j y v).
rewrite !outcome_iff_hasvalue.
unfold eta.
rewrite <- (SMN_MM2 (SMN_S U i) j y v).
rewrite <- (SMN_MM2 U i (pair_xy j y) v).
reflexivity.
Qed.

End EtaViaSMN.

