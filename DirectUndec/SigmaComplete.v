(* Sigma^0_1-completeness without effective inseparability.

   Under CT_L alone, the halting problem MM2_HALTS_ON_ZERO is m-complete
   (MM2_HALTS_ON_ZERO_m_complete): an enumerable q is semi-decided by a Rocq
   function, CT_L (through EPF_L) gives an L-code c0 for its partial
   search, and the T_L-simulating MM2 program of CKAUndec/Glue/TLToRTarget.v
   halts at (0,(0,0)) on input (c0, x) iff that search succeeds. This is
   the textbook proof that the halting problem is complete; it uses
   neither SMN, nor effective inseparability, nor creativity/Myhill.

   The direct reductions of Undec.v, Binary.v and UnivDirect.v then give
   m-completeness of pre-KA term equality, of its binary version and of
   balanced universality under CT_L and MP (PreKA_EQ_m_complete,
   PreKA_EQ_bin_m_complete, UNIV_m_complete). MP is used only where
   Undec.v's PreKA_EQ_MP_reduction uses it: the refutation of divergent
   runs gives "equal → ¬¬ halts", and MP turns that into "halts". The
   statements are literally the library's `m-complete p` (Axioms/EA.v).
   The route loads no file of ReducibilityDegrees/ nor EA_L/T_L_Bridge.

   The only new MM2-level fact is the converse half of the splice
   connection (halt_sound): if the spliced program halts at (0,(0,0)),
   its FRACTRAN phase halted, so R_TL is defined on the input. The
   existing R_TL_connection_gen only covered outputs m <= 1, which is all
   that the 0/1 sets A0_L/B1_L of the inseparability route ask about. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia Relations.
From Undecidability.MinskyMachines Require Import MM MM2 MMA.
Import MM2Notations.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
From Undecidability.FRACTRAN Require Import FRACTRAN fractran_utils prime_seq.
From Undecidability.FRACTRAN Require Import FRACTRAN_sss.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.
From Undecidability.MinskyMachines.MMA Require Import mma_defs fractran_mma.
From Undecidability.MinskyMachines.Reductions Require Import
  MM2_Splice MMA2_to_MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_simulator.
Require Undecidability.Synthetic.Definitions.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Shared.partial.
Require SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.reductions.

Require kacc.CKAUndec.Glue.TLToRTarget.
Require kacc.DirectUndec.Undec kacc.DirectUndec.Binary.
Require kacc.DirectUndec.UnivDirect.

(** * The spliced T_L program halts only when T_L does *)

Lemma enc_nz i k (v : Vector.t nat k) : enc i v ≠ 0.
Proof.
revert i; induction v as [|x k v IH]; intros i; simpl; [lia|].
apply Nat.neq_mul_0; split; [|apply IH].
apply Nat.pow_nonzero, prime_neq_0, (str_prime qs).
Qed.

Lemma ps1_enc_nz (v : Vector.t nat 2) : ps 1 * enc 2 v ≠ 0.
Proof. rewrite ps_1. generalize (@enc_nz 2 2 v); lia. Qed.

(* Every non-zero number is j * qs 1 ^ m with qs 1 not dividing j. *)
Lemma qs1_valuation y : y ≠ 0 → ∃ m j, y = j * qs 1 ^ m ∧ ¬ divides (qs 1) j.
Proof.
induction y as [y IH] using (well_founded_induction lt_wf); intros Hy.
destruct (divides_dec y (qs 1)) as [[k Hk]|Hnd].
- rewrite qs_1 in Hk.
  destruct (IH k) as [m [j [Hkj Hj]]]; [lia|lia|].
  exists (S m), j; split; [|exact Hj].
  rewrite Hk, Hkj, qs_1, Nat.pow_succ_r'; ring.
- exists 0, y; split; [simpl; lia|exact Hnd].
Qed.

Section Halt.

Variable Q : list (nat * nat).
Hypothesis Qreg : fractran_regular Q.
Hypothesis spec : ∀ (v : Vector.t nat 2) m, R_TL v m ↔
  ∃ j, Q /F/ ps 1 * enc 2 v ▹ j * qs 1 ^ m ∧ ¬ divides (qs 1) j.

Lemma stop_zero_nil : fractran_stop Q 0 → Q = nil.
Proof.
destruct Q as [|[p q] l]; [reflexivity|]; intros H; exfalso.
apply (H 0); constructor; lia.
Qed.

Lemma compute_nil x y : fractran_compute nil x y → y = x.
Proof.
intros [[|n] H]; simpl in H; [congruence|].
destruct H as [z [Hz _]]; inversion Hz.
Qed.

Lemma halt_complete v :
  R_TL v 1 → progOf (c_P Q) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)).
Proof.
intros [j [Hev _]] % spec.
apply eval_iff in Hev as [Hc Hs].
apply Psplice_mm2_divides with (b := j * qs 1 ^ 1).
- exact (fractran_mma_sound Qreg Hc Hs).
- exists j; now rewrite Nat.pow_1_r.
Qed.

Lemma halt_sound v :
  progOf (c_P Q) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)) → ∃ m, R_TL v m.
Proof.
intros H; rewrite progOf_c_P in H.
apply (mma_mma2_zero_reduction (Psplice Q)
         (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  in H.
assert (Hterm : sss_terminates (@mma_sss 2) (1, P0 Q)
                  (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)).
{ eapply subcode_sss_terminates; [apply P0_subcode|].
  eexists; exact H. }
apply (fractran_mma_reduction Qreg) in Hterm as [y [Hc Hs]].
assert (Hy : y ≠ 0).
{ intros ->. pose proof (stop_zero_nil Hs) as E; rewrite E in Hc.
  apply compute_nil in Hc; generalize (ps1_enc_nz (v := v)); lia. }
destruct (qs1_valuation Hy) as [m [j [Hyj Hj]]].
exists m; apply spec; exists j; split; [|exact Hj].
rewrite <- Hyj; apply eval_iff; split; assumption.
Qed.

End Halt.

(** * θ_L and R_TL, as in T_L_Bridge.v (which loads the inseparability
      files, so is not imported here) *)

Lemma T_L_first_or_none (c y n : nat) :
  (∀ k, k <= n → T_L c y k = None) ∨
  (∃ n0 v0, n0 <= n ∧ T_L c y n0 = Some v0 ∧ ∀ k, k < n0 → T_L c y k = None).
Proof.
induction n as [| n' [IHnone | [n0 [v0 [Hn0 [Hval Hmin]]]]]].
- destruct (T_L c y 0) as [v0|] eqn:E0.
  + right. exists 0, v0. repeat split; auto; intros k Hk; lia.
  + left. intros k Hk. assert (k = 0) by lia. congruence.
- destruct (T_L c y (S n')) as [v0|] eqn:ES.
  + right. exists (S n'), v0. repeat split; auto.
    intros k Hk. apply IHnone. lia.
  + left. intros k Hk.
    destruct (Nat.eq_dec k (S n')) as [-> | Hne]; [exact ES |].
    apply IHnone. lia.
- right. exists n0, v0. repeat split; auto; lia.
Qed.

Lemma theta_R_TL (c x m : nat) :
  θ_L c x =! m ↔ R_TL (c ## x ## vec_nil) m.
Proof.
unfold R_TL; simpl; rewrite TL_val_iff.
change (θ_L c x =! m) with (∃ n, T_L c x n = Some m).
split.
- intros [n Hn]; change (T_L c x n = Some m) in Hn.
  destruct (T_L_first_or_none c x n) as [Hnone|[n0 [v0 [Hn0 [Hval Hmin]]]]].
  + specialize (Hnone n (le_n n)); congruence.
  + assert (v0 = m) as ->.
    { pose proof (@monotonic_T_L c x n0 v0 Hval n Hn0); congruence. }
    exists n0; repeat split.
    * unfold TL_bit; now rewrite T_L'_eq, Hval.
    * intros k Hk; unfold TL_bit; now rewrite T_L'_eq, (Hmin k Hk).
    * now rewrite T_L'_eq.
- intros [n [_ [_ Hn]]]; exists n.
  change (T_L c x n = Some m); now rewrite <- T_L'_eq.
Qed.

(** * Halting is m-complete under CT_L *)

Notation enumerable := SyntheticComputability.Synthetic.Definitions.enumerable.

Theorem MM2_HALTS_ON_ZERO_m_complete : CT_L →
  ∀ q : nat → Prop, enumerable q → q ⪯ₘ MM2_HALTS_ON_ZERO.
Proof.
intros ct q [e He].
destruct TLToRTarget.R_TL_FRACTRAN_computable as [Q [Qreg spec]].
pose (g := fun x n => match e n with Some y => Nat.eqb y x | None => false end).
pose (G := fun x => bind (mu (fun n => ret (g x n))) (fun _ => ret 1)).
destruct (CT_L_to_EPF_L ct G) as [c0 Hc0].
exists (fun x => (progOf (c_P Q), ps 1 * enc 2 (c0 ## x ## vec_nil), 0)).
intros x.
change (q x ↔ progOf (c_P Q) // (1, (ps 1 * enc 2 (c0 ## x ## vec_nil), 0))
  ↠ (0, (0, 0))).
split.
- intros [n Hn] % He.
  apply (halt_complete Qreg spec), theta_R_TL, Hc0.
  apply bind_hasvalue.
  assert (Hmu : ter (mu (fun n => ret (g x n)))).
  { apply mu_ter; exists n; split.
    - apply ret_hasvalue'; unfold g; rewrite Hn; apply Nat.eqb_refl.
    - intros k _; eexists; apply ret_hasvalue. }
  destruct Hmu as [a Ha]; exists a; split; [exact Ha|apply ret_hasvalue].
- intros [m Hm] % (halt_sound Qreg spec).
  apply theta_R_TL, Hc0, bind_hasvalue in Hm as [a [Ha _]].
  apply mu_hasvalue in Ha as [Ha _]; apply ret_hasvalue_inv in Ha.
  unfold g in Ha; apply He; exists a.
  destruct (e a) as [y|]; [|discriminate].
  apply Nat.eqb_eq in Ha; now subst.
Qed.

(** * m-completeness of the pre-KA problems under CT_L and MP *)

Lemma red_m_of_reduces {X Y} (p : X → Prop) (r : Y → Prop) :
  Undecidability.Synthetic.Definitions.reduces p r → p ⪯ₘ r.
Proof. intros [f Hf]; exists f; exact Hf. Qed.

Theorem PreKA_EQ_m_complete : CT_L → Undec.MP →
  ∀ q : nat → Prop, enumerable q → q ⪯ₘ Undec.PreKA_EQ.
Proof.
intros ct mp q Hq.
apply (red_m_transitive MM2_HALTS_ON_ZERO).
- exact (MM2_HALTS_ON_ZERO_m_complete ct Hq).
- exact (red_m_of_reduces (Undec.PreKA_EQ_MP_reduction mp)).
Qed.

Theorem PreKA_EQ_bin_m_complete : CT_L → Undec.MP →
  ∀ q : nat → Prop, enumerable q → q ⪯ₘ Binary.PreKA_EQ_bin.
Proof.
intros ct mp q Hq.
apply (red_m_transitive MM2_HALTS_ON_ZERO).
- exact (MM2_HALTS_ON_ZERO_m_complete ct Hq).
- exact (red_m_of_reduces (Binary.PreKA_EQ_bin_MP_reduction mp)).
Qed.

Theorem UNIV_m_complete : CT_L → Undec.MP →
  ∀ q : nat → Prop, enumerable q → q ⪯ₘ UnivDirect.UNIV.
Proof.
intros ct mp q Hq.
apply (red_m_transitive MM2_HALTS_ON_ZERO).
- exact (MM2_HALTS_ON_ZERO_m_complete ct Hq).
- exact (red_m_of_reduces (UnivDirect.UNIV_MP_reduction mp)).
Qed.
