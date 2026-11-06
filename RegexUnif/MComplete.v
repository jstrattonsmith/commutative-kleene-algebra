(* KA unification is Sigma^0_1-complete (conditional on CT_L and MP, as
   everywhere else in this project), already for one equation in which no
   variable occurs twice on the same side (`side_linear`).

   For a machine `P` and a start configuration `s`, `mm2_eq P s` is
   RegexUnif/Invariant.v's equation `cell_eq` for RegexUnif/MM2Deque.v's
   rules, cells and start word. It is side-linear (`mm2_eq_side_linear`).
   Under any theory `E` between pre-KA and language equality (`RU`), it
   is solvable whenever `P` runs from `s` to `(0, (0, 0))`
   (`RU_complete`, the configurations of the run form a finite invariant)
   and only if no halting run from `s` ends elsewhere (`RU_sound`). These
   are exactly the hypotheses of CKAUndec/Glue/TLToRTarget.v's
   `R_TL_connection_of`, and the rest is CKAUndec/KMComplete.v's
   `m_complete_of_K_of`, with enumerability from RegexUnif/Syntax.v's
   `unif_enumerable`: if `E` is enumerable, unification modulo `E` is
   m-complete, for side-linear single equations, for all single equations
   and for systems (`unif_m_complete_of`).

   Final results: unification modulo KA (`KA_unif_m_complete`) and
   modulo pre-KA (`PreKA_unif_m_complete`), over the alphabet of one
   fixed machine. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From stdpp Require Import base list.
From stdpp Require countable finite relations.
From kacc Require Import KA.algebra KA.pre_ka KA.lang KA.ka.
From kacc Require Import KA.rules_enumerable.
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

Definition mm2_eq (P : list mm2_instr) (s : nat * (nat * nat)) :
    @ueq (alph P) :=
  cell_eq (mm2_rules P) (mm2_cells P) (cword P s).

Lemma mm2_eq_side_linear P s : side_linear (mm2_eq P s).
Proof. exact: cell_eq_side_linear (mm2_cells_nodup P). Qed.

Section Generic.

(* A theory between pre-KA and language equality, at every alphabet. *)
Variable E :
  ∀ A : setoid, ka_term (list_monoid A) → ka_term (list_monoid A) → Prop.
Hypothesis E_pre : ∀ (A : setoid) (e1 e2 : ka_term (list_monoid A)),
  e1 ≡ e2 → E e1 e2.
Hypothesis E_lang : ∀ (A : setoid) (e1 e2 : ka_term (list_monoid A)),
  E e1 e2 → l e1 ≡ l e2.
Hypothesis E_enum : ∀ P : list mm2_instr,
  enumerable (λ p : ka_term (list_monoid (alph P)) * _, @E _ p.1 p.2).

Definition RU (P : list mm2_instr) (s : nat * (nat * nat)) : Prop :=
  unif (@E (alph P)) [mm2_eq P s].

Lemma RU_complete P s : relations.rtc (mm2_step P) s (0, (0, 0)) → RU P s.
Proof.
move=> Hrun.
have Hstop : mm2_stop P (0, (0, 0)) by apply/mm2_stop_index_iff; left.
have [ls [Hs [Hreach Hcl]]] := run_path Hrun Hstop.
apply: unif_mono (@E_pre (alph P)) _.
apply: (cell_complete (L := cword P <$> ls)).
- exact: elem_of_list_fmap_1.
- move=> t t' /elem_of_list_fmap [z [-> Hz]] /cword_step_inv [z' [-> Hzz']].
  exact/elem_of_list_fmap_1/(Hcl z z').
- move=> t /elem_of_list_fmap [z [-> Hz]].
  case: (stop_or_active P z) => [Hzs|Hza].
  + rewrite -(rtc_stop_eq (Hreach z Hz) Hzs); exact: cword_cover_accept.
  + exact: cword_cover_active.
Qed.

Lemma RU_sound P s1 s2 :
  relations.rtc (mm2_step P) s1 s2 → mm2_stop P s2 → RU P s1 →
  s2 = (0, (0, 0)).
Proof.
move=> Hrun Hstop /(unif_lsolves (@E_lang (alph P))) [ρ Hsol].
have Hlift : relations.rtc (dstep (mm2_rules P)) (cword P s1) (cword P s2).
{ elim: Hrun {Hstop Hsol} => [x|x y z Hxy _ IH].
  - exact: relations.rtc_refl.
  - exact: relations.rtc_l (cword_step Hxy) IH. }
case: (decide (s2 = (0, (0, 0)))) => // Hne.
have [c [Hc Hin]] :=
  cell_sound (@rules_cells_len P) (@rules_det P) Hsol Hlift.
by case: (cword_halt_uncovered Hstop Hne Hc Hin).
Qed.

Definition K_unif (c : nat) : nat → Prop :=
  K_of (λ n, RU (progOf c) (1, (n, 0))).

Definition K_to_unif (c z : nat) : @ueq (alph (progOf c)) :=
  mm2_eq (progOf c) (1, (ps 1 * enc 2 (z_vec z), 0)).

Lemma K_unif_enumerable c : enumerable (K_unif c).
Proof.
apply: (enumerable_reduce (f := λ z, [K_to_unif c z]) (Q := unif (@E _))).
- by [].
- exact: unif_enumerable (E_enum (progOf c)).
Qed.

(* Side-linear single equations, all single equations, and systems. *)
Theorem unif_m_complete_of :
  CT_L → MP → ∃ c,
    m-complete (λ q, side_linear q ∧ unif (@E (alph (progOf c))) [q]) ∧
    m-complete (λ q, unif (@E (alph (progOf c))) [q]) ∧
    m-complete (unif (@E (alph (progOf c)))).
Proof.
move=> ct mp; have [c Hc] := R_TL_connection_of RU_complete RU_sound.
exists c; split; [|split].
- apply: (KMComplete.m_complete_of_K_of (f := K_to_unif c) Hc
            (K_unif_enumerable c) _ ct mp) => z.
  by split => [H|[]] //; split => //; exact: mm2_eq_side_linear.
- exact: (KMComplete.m_complete_of_K_of (f := K_to_unif c) Hc
            (K_unif_enumerable c) (λ z, iff_refl _) ct mp).
- exact: (KMComplete.m_complete_of_K_of (f := λ z, [K_to_unif c z]) Hc
            (K_unif_enumerable c) (λ z, iff_refl _) ct mp).
Qed.

End Generic.

(** Unification modulo KA, i.e. of a system of equations `Rᵢ ≡ Sᵢ`
    with KA proofs of every instance, is Sigma^0_1-complete, already for
    a single equation `R ≡ S` in which no variable occurs twice on the
    same side. *)

Definition KA_unif (c : nat) : list (@ueq (alph (progOf c))) → Prop :=
  unif fka_eqv.

Definition KA_unif1 (c : nat) (q : @ueq (alph (progOf c))) : Prop :=
  unif fka_eqv [q].

Theorem KA_unif_m_complete :
  CT_L → MP → ∃ c,
    m-complete (λ q, side_linear q ∧ @KA_unif1 c q) ∧
    m-complete (@KA_unif1 c) ∧ m-complete (@KA_unif c).
Proof.
apply: (unif_m_complete_of (E := @fka_eqv)) => [A e1 e2|A e1 e2|P].
- exact: fka_of_pre.
- rewrite /fka_eqv => He x; split; apply: fka_lang; by rewrite He.
- exact: fka_eqv_enumerable.
Qed.

(** The same modulo pre-KA. *)

Definition PreKA_unif (c : nat) : list (@ueq (alph (progOf c))) → Prop :=
  unif preka_eqv.

Definition PreKA_unif1 (c : nat) (q : @ueq (alph (progOf c))) : Prop :=
  unif preka_eqv [q].

Theorem PreKA_unif_m_complete :
  CT_L → MP → ∃ c,
    m-complete (λ q, side_linear q ∧ @PreKA_unif1 c q) ∧
    m-complete (@PreKA_unif1 c) ∧ m-complete (@PreKA_unif c).
Proof.
apply: (unif_m_complete_of (E := @preka_eqv)) => [A e1 e2|A e1 e2 ->|P] //.
exact: preka_eqv_enumerable.
Qed.
