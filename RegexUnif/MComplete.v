(* KA unification is Sigma^0_1-complete (conditional on CT_L and MP, as
   everywhere else in this project).

   For a machine `P` and a start configuration `s`, `mm2_eqs P s` is
   RegexUnif/Invariant.v's invariant system for RegexUnif/MM2Deque.v's
   rules, forbidden prefixes and start word. Under any theory between
   pre-KA and language equality (`RU`), it is solvable whenever `P` runs
   from `s` to `(0, (0, 0))` (`RU_complete`, the configurations of the
   run form a finite invariant) and only if no halting run from `s` ends
   elsewhere (`RU_sound`). These are exactly the hypotheses of
   CKAUndec/Glue/TLToRTarget.v's `R_TL_connection_of`, and the rest is
   CKAUndec/KMComplete.v's `m_complete_of_K_of`, with enumerability from
   RegexUnif/Syntax.v's `unif_enumerable`.

   Final results: unification modulo KA (`KA_unif_m_complete`) and
   modulo pre-KA (`PreKA_unif_m_complete`), over the alphabet of one
   fixed machine. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From stdpp Require Import base list.
From stdpp Require countable finite relations.
From kacc Require Import KA.algebra KA.pre_ka KA.rules_enumerable.
From kacc Require Import CKAUndec.Encoding CKAUndec.Glue.TLToRTarget.
From kacc Require CKAUndec.KMComplete.
From kacc Require Import RegexUnif.Syntax RegexUnif.Invariant.
From kacc Require Import RegexUnif.MM2Deque.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_simulator.

Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.
Require Import SyntheticComputability.Synthetic.Definitions
  SyntheticComputability.Synthetic.EnumerabilityFacts
  SyntheticComputability.Synthetic.DecidabilityFacts
  SyntheticComputability.Synthetic.reductions.

Open Scope nat_scope.

Notation alph P := (option_setoid (@mm_sym_setoid (Fin.t (S (S (length P)))))).

(* `setoid_equiv` is `simpl never`, so instance search does not see that
   the alphabet's setoid equality is stdpp's `option_equiv`; by
   conversion it is. *)
Local Instance alph_leibniz (P : list mm2_instr) : LeibnizEquiv (alph P) :=
  _ : LeibnizEquiv (option (mm_sym (Fin.t (S (S (length P)))))).

Local Instance mm_sym_countable (P : list mm2_instr) :
  countable.Countable (mm_sym (Fin.t (S (S (length P))))) :=
  finite.finite_countable.

Local Instance alph_countable (P : list mm2_instr) :
  countable.Countable (alph P) :=
  _ : countable.Countable (option (mm_sym (Fin.t (S (S (length P)))))).

Section Connection.

Variable E :
  ∀ A : setoid, ka_term (list_monoid A) → ka_term (list_monoid A) → Prop.
Hypothesis E_sound : ∀ A : setoid, lang_sound (@E A).
Hypothesis E_complete : ∀ A : setoid, preka_complete (@E A).

Definition mm2_eqs (P : list mm2_instr) (s : nat * (nat * nat)) :
    list (@ueq (alph P)) :=
  inv_eqs (mm2_rules P) (mm2_bad P) (cword P s).

Definition RU (P : list mm2_instr) (s : nat * (nat * nat)) : Prop :=
  unif (@E (alph P)) (mm2_eqs P s).

Lemma RU_complete P s : relations.rtc (mm2_step P) s (0, (0, 0)) → RU P s.
Proof.
move=> Hrun.
have Hstop : mm2_stop P (0, (0, 0)) by apply/mm2_stop_index_iff; left.
have [ls [Hs [Hreach Hcl]]] := run_path Hrun Hstop.
have Hw : cword P s ∈ cword P <$> ls by apply: elem_of_list_fmap_1.
have Hclosed t t' : t ∈ cword P <$> ls → dstep (mm2_rules P) t t' →
    t' ∈ cword P <$> ls.
{ move=> /elem_of_list_fmap [z [-> Hz]] /cword_step_inv [z' [-> Hzz']].
  exact/elem_of_list_fmap_1/(Hcl z z'). }
have Havoid t b : t ∈ cword P <$> ls → b ∈ mm2_bad P → ¬ b `prefix_of` t.
{ move=> /elem_of_list_fmap [z [-> Hz]] Hb.
  case: (stop_or_active P z) => [Hzs|Hza].
  - rewrite -(rtc_stop_eq (Hreach z Hz) Hzs); exact: cword_accept_ok.
  - exact: cword_active_ok. }
exact (inv_complete (Rs := mm2_rules P) (bad := mm2_bad P) Hw Hclosed Havoid
         (@E_complete (alph P))).
Qed.

Lemma RU_sound P s1 s2 :
  relations.rtc (mm2_step P) s1 s2 → mm2_stop P s2 → RU P s1 →
  s2 = (0, (0, 0)).
Proof.
move=> Hrun Hstop HR.
have Hlift : relations.rtc (dstep (mm2_rules P)) (cword P s1) (cword P s2).
{ elim: Hrun {Hstop HR} => [x|x y z Hxy _ IH]; first exact: relations.rtc_refl.
  exact: relations.rtc_l (cword_step Hxy) IH. }
case: (decide (s2 = (0, (0, 0)))) => // Hne.
have [b [Hb Hpre]] := cword_bad Hstop Hne.
by case: (inv_sound (@E_sound (alph P)) HR Hlift Hb).
Qed.

Theorem RU_connection :
  ∃ c, ∀ (v : Vector.t nat 2) (m : nat), m ≤ 1 → T_L_Uniform.R_TL v m →
    (m = 1 ↔ RU (progOf c) (1, (ps 1 * enc 2 v, 0))).
Proof. exact: (R_TL_connection_of RU_complete RU_sound). Qed.

End Connection.

(** * m-completeness *)

Section MComplete.

Variable c : nat.

Notation Pc := (progOf c).

Variable E :
  ∀ A : setoid, ka_term (list_monoid A) → ka_term (list_monoid A) → Prop.
Hypothesis E_enum :
  enumerable (λ p : ka_term (list_monoid (alph Pc)) * _, @E _ p.1 p.2).

Definition K_unif : nat → Prop := K_of (λ n, RU E Pc (1, (n, 0))).

Definition K_to_unif (z : nat) : list (@ueq (alph Pc)) :=
  mm2_eqs Pc (1, (ps 1 * enc 2 (z_vec z), 0)).

Lemma K_to_unif_spec z : K_unif z ↔ unif (@E _) (K_to_unif z).
Proof. reflexivity. Qed.

Theorem K_unif_enumerable : enumerable K_unif.
Proof.
apply: (enumerable_reduce (f := K_to_unif) (Q := unif (@E _))).
- exact: K_to_unif_spec.
- exact: unif_enumerable E_enum.
Qed.

End MComplete.

(** Unification modulo KA, i.e. of a system of equations `Rᵢ ≡ Sᵢ`
    with KA proofs of every instance, is Sigma^0_1-complete. *)

Definition KA_unif (c : nat) : list (@ueq (alph (progOf c))) → Prop :=
  unif fka_eqv.

Theorem KA_unif_m_complete : CT_L → MP → ∃ c, m-complete (@KA_unif c).
Proof.
move=> ct mp.
have [c Hc] := RU_connection (E := @fka_eqv) (λ A, fka_eqv_sound)
                 (λ A, fka_eqv_complete).
exists c.
apply: (KMComplete.m_complete_of_K_of Hc
          (K_unif_enumerable fka_eqv_enumerable) _ ct mp).
by move=> z; apply: K_to_unif_spec.
Qed.

(** The same modulo pre-KA. *)

Definition PreKA_unif (c : nat) : list (@ueq (alph (progOf c))) → Prop :=
  unif preka_eqv.

Theorem PreKA_unif_m_complete : CT_L → MP → ∃ c, m-complete (@PreKA_unif c).
Proof.
move=> ct mp.
have [c Hc] := RU_connection (E := @preka_eqv) (λ A, preka_eqv_sound)
                 (λ A, preka_eqv_complete).
exists c.
apply: (KMComplete.m_complete_of_K_of Hc
          (K_unif_enumerable preka_eqv_enumerable) _ ct mp).
by move=> z; apply: K_to_unif_spec.
Qed.
