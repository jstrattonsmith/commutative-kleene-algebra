(* Regular inductive invariants as KA unification problems: the core of
   the proof that KA unification is Sigma^0_1-complete.

   A two-ended Post normal system is a list of rules `((u, u'), (v, v'))`,
   each rewriting `u ++ x ++ u'` to `v ++ x ++ v'` (`dstep`). Tag systems
   are the case `u' = v = []`. Given rules `Rs`, forbidden prefixes `bad`
   and a start word `w`, `inv_eqs Rs bad w` is a system of star-free
   equations whose solutions are inductive invariants: a language `X`
   containing `w`, closed under `dstep`, and with no word starting with
   a word of `bad`. The variable `X_{p,s}` (`var p s`) stands for the
   two-sided derivative `{x | p ++ x ++ s ∈ X}`, and is pinned down by
   the derivative equations `1 ⊔ Y ≡ 1 ⊔ ⨆_c c ⋅ Y_c` (left, along each
   rule's prefix `u`) and `1 ⊔ Y ≡ 1 ⊔ ⨆_c Y_c ⋅ c` (right, along `u'`).

   - `inv_sound`: a language-level solution keeps every word reachable
     from `w` clear of `bad`.
   - `inv_complete`: a finite invariant gives a solution modulo pre-KA,
     by RegexUnif/StarFree.v.

   Every lemma about the equations goes through an `_iff` lemma stating
   what the equation says about the languages `ρ (var p s)`, so soundness
   and completeness use the same characterization. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list countable finite relations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.
From kacc Require Import RegexUnif.Syntax RegexUnif.StarFree.

Section Invariant.

Context {A : setoid} `{!LeibnizEquiv A, !EqDecision A, !Finite A}.

Local Instance A_countable : Countable A := finite_countable.

Notation W := (list_monoid A).
Notation UT := (@uterm A).
Notation UE := (@ueq A).

Implicit Types (p s u x y t : list A) (ρ : nat → lang W).

(** * Two-ended Post normal systems *)

Definition drule : Type := ((list A * list A) * (list A * list A))%type.

Definition dstep (Rs : list drule) t t' : Prop :=
  ∃ u u' v v' x, ((u, u'), (v, v')) ∈ Rs ∧
    t = u ++ x ++ u' ∧ t' = v ++ x ++ v'.

(** * Languages over words *)

Lemma in_mul (L1 L2 : lang W) x :
  (L1 ⋅ L2) x ↔ ∃ x1 x2, x = x1 ++ x2 ∧ L1 x1 ∧ L2 x2.
Proof.
split.
- by case=> x1 [x2 [/leibniz_equiv_iff -> ?]]; exists x1, x2.
- by case=> x1 [x2 [-> ?]]; exists x1, x2.
Qed.

Lemma in_one x : (1 : lang W) x ↔ x = [].
Proof. by split => [/leibniz_equiv_iff|-> /=] //; reflexivity. Qed.

Lemma in_sing y x : lang_sing y x ↔ x = y.
Proof. by split => [/leibniz_equiv_iff|-> /=] //; reflexivity. Qed.

Lemma in_join (L1 L2 : lang W) x : (L1 ⊔ L2) x ↔ L1 x ∨ L2 x.
Proof. reflexivity. Qed.

Lemma in_bot x : (⊥ : lang W) x ↔ False.
Proof. reflexivity. Qed.

(** * Building blocks of the equations *)

Definition var p s : nat := encode_nat (p, s).

Definition tone : UT := Unit [].
Definition tv p s : UT := Unit [inr (var p s)].
Definition tw (w : list A) : UT := Unit (inl <$> w).
Definition tjoin (es : list UT) : UT := foldr (λ e acc, e ⊔ acc) ⊥ es.

Lemma tjoin_cons e es : tjoin (e :: es) = e ⊔ tjoin es.
Proof. by []. Qed.

Lemma lsubst_unit ρ cs : lsubst ρ (Unit cs) = mul_list (lsym ρ) cs.
Proof. by []. Qed.

Lemma lsubst_join ρ (e1 e2 : UT) :
  lsubst ρ (e1 ⊔ e2) = lsubst ρ e1 ⊔ lsubst ρ e2.
Proof. by []. Qed.

Lemma lsubst_mul ρ (e1 e2 : UT) :
  lsubst ρ (e1 ⋅ e2) = lsubst ρ e1 ⋅ lsubst ρ e2.
Proof. by []. Qed.

Lemma lsubst_bot ρ : lsubst ρ (⊥ : UT) = ⊥.
Proof. by []. Qed.

Lemma in_tone ρ x : lsubst ρ tone x ↔ x = [].
Proof. exact: in_one. Qed.

Lemma in_tv ρ p s x : lsubst ρ (tv p s) x ↔ ρ (var p s) x.
Proof.
rewrite /tv lsubst_unit mul_list_cons in_mul; split.
- by case=> x1 [x2 [-> [H /in_one ->]]]; rewrite app_nil_r.
- move=> H; exists x, []; rewrite app_nil_r; do !split => //.
  exact/in_one.
Qed.

Lemma in_tw ρ w x : lsubst ρ (tw w) x ↔ x = w.
Proof.
rewrite /tw lsubst_unit; elim: w x => [|a w IH] x; first exact: in_one.
rewrite fmap_cons mul_list_cons in_mul; split.
- by case=> x1 [x2 [-> [/in_sing -> /IH ->]]].
- move=> ->; exists [a], w; do !split => //; [exact/in_sing | exact/IH].
Qed.

Lemma in_tjoin ρ es x :
  lsubst ρ (tjoin es) x ↔ ∃ e, e ∈ es ∧ lsubst ρ e x.
Proof.
elim: es => [|e es IH].
- by split => [|[e [/elem_of_nil]]].
- rewrite tjoin_cons lsubst_join in_join IH; split.
  + case=> [He|[e' [He' H]]]; first by exists e; split => //; left.
    by exists e'; split => //; right.
  + by case=> e' [/elem_of_cons [->|He'] H]; [left|right; exists e'].
Qed.

Lemma star_free_tjoin {X} (f : X → UT) (zs : list X) :
  (∀ z, star_free (f z)) → star_free (tjoin (f <$> zs)).
Proof. by move=> Hf; elim: zs => //= z zs IH; split. Qed.

(** * Derivative equations *)

Definition left_lhs p : UT := tone ⊔ tv p [].
Definition left_rhs p : UT :=
  tone ⊔ tjoin ((λ c, tw [c] ⋅ tv (p ++ [c]) []) <$> enum A).
Definition left_eq p : UE := (left_lhs p, left_rhs p).

Lemma left_eq_iff ρ p :
  lsubst ρ (left_lhs p) ≡ lsubst ρ (left_rhs p) ↔
  ∀ c y, ρ (var p []) (c :: y) ↔ ρ (var (p ++ [c]) []) y.
Proof.
have HL x : lsubst ρ (left_lhs p) x ↔ x = [] ∨ ρ (var p []) x
  by rewrite /left_lhs lsubst_join in_join in_tone in_tv.
have HR x : lsubst ρ (left_rhs p) x ↔
    x = [] ∨ ∃ c y, x = c :: y ∧ ρ (var (p ++ [c]) []) y.
{ rewrite /left_rhs lsubst_join in_join in_tone in_tjoin; split.
  - case=> [->|[_ [/elem_of_list_fmap [c [-> _]]]]]; first by left.
    rewrite lsubst_mul in_mul => - [x1 [x2 [-> [/in_tw -> /in_tv H]]]].
    by right; exists c, x2.
  - case=> [->|[c [y [-> H]]]]; first by left.
    right; exists (tw [c] ⋅ tv (p ++ [c]) []); split.
    + by apply/elem_of_list_fmap; exists c; split => //; apply: elem_of_enum.
    + rewrite lsubst_mul in_mul; exists [c], y; do !split => //.
      * exact/in_tw.
      * exact/in_tv. }
split.
- move=> H c y; have := H (c :: y); rewrite HL HR => Hiff; split.
  + move=> Hc; case: (proj1 Hiff (or_intror Hc)) => [//|].
    by case=> c' [y' [[<- <-] Hy]].
  + move=> Hy; case: (proj2 Hiff (or_intror (ex_intro _ c
      (ex_intro _ y (conj eq_refl Hy))))) => //.
- move=> H x; rewrite HL HR; split.
  + case=> [->|]; first by left.
    case: x => [|c y]; first by left.
    by move=> /H Hy; right; exists c, y.
  + by case=> [->|[c [y [-> /H Hy]]]]; [left|right].
Qed.

Definition right_lhs u s : UT := tone ⊔ tv u s.
Definition right_rhs u s : UT :=
  tone ⊔ tjoin ((λ c, tv u (c :: s) ⋅ tw [c]) <$> enum A).
Definition right_eq u s : UE := (right_lhs u s, right_rhs u s).

Lemma right_eq_iff ρ u s :
  lsubst ρ (right_lhs u s) ≡ lsubst ρ (right_rhs u s) ↔
  ∀ c y, ρ (var u s) (y ++ [c]) ↔ ρ (var u (c :: s)) y.
Proof.
have HL x : lsubst ρ (right_lhs u s) x ↔ x = [] ∨ ρ (var u s) x
  by rewrite /right_lhs lsubst_join in_join in_tone in_tv.
have HR x : lsubst ρ (right_rhs u s) x ↔
    x = [] ∨ ∃ c y, x = y ++ [c] ∧ ρ (var u (c :: s)) y.
{ rewrite /right_rhs lsubst_join in_join in_tone in_tjoin; split.
  - case=> [->|[_ [/elem_of_list_fmap [c [-> _]]]]]; first by left.
    rewrite lsubst_mul in_mul => - [x1 [x2 [-> [/in_tv H /in_tw ->]]]].
    by right; exists c, x1.
  - case=> [->|[c [y [-> H]]]]; first by left.
    right; exists (tv u (c :: s) ⋅ tw [c]); split.
    + by apply/elem_of_list_fmap; exists c; split => //; apply: elem_of_enum.
    + rewrite lsubst_mul in_mul; exists y, [c]; do !split => //.
      * exact/in_tv.
      * exact/in_tw. }
split.
- move=> H c y; have := H (y ++ [c]); rewrite HL HR => Hiff; split.
  + move=> Hc; case: (proj1 Hiff (or_intror Hc)).
    * by move=> /app_nil [_].
    * case=> c' [y' [Heq Hy]].
      by case: (app_inj_tail y y' c c' Heq) => -> ->.
  + move=> Hy; case: (proj2 Hiff (or_intror (ex_intro _ c
      (ex_intro _ y (conj eq_refl Hy))))) => //.
    by move=> /app_nil [_].
- move=> H x; rewrite HL HR; split.
  + case=> [->|]; first by left.
    case: (decide (x = [])) => [->|Hne]; first by left.
    case: (exists_last Hne) => y [c ->].
    by move=> /H Hy; right; exists c, y.
  + by case=> [->|[c [y [-> /H Hy]]]]; [left|right].
Qed.

(* Chains of derivative equations from `X_{p,[]}` down to `X_{p ++ u,[]}`
   (left), and from `X_{u,[]}` down to `X_{u,s}` (right). *)
Fixpoint lchain p u : list UE :=
  match u with [] => [] | c :: u => left_eq p :: lchain (p ++ [c]) u end.

Fixpoint rchain u s : list UE :=
  match s with [] => [] | c :: s => right_eq u s :: rchain u s end.

Lemma lchain_sound ρ p u :
  (∀ q, q ∈ lchain p u → lsubst ρ q.1 ≡ lsubst ρ q.2) →
  ∀ y, ρ (var p []) (u ++ y) → ρ (var (p ++ u) []) y.
Proof.
elim: u p => [|c u IH] p H y; first by rewrite app_nil_r.
move=> Hy; have /left_eq_iff Hl := H _ (elem_of_list_here _ _).
have -> : p ++ c :: u = (p ++ [c]) ++ u by rewrite -app_assoc.
apply: IH; last exact: (proj1 (Hl c (u ++ y)) Hy).
by move=> q Hq; apply: H; apply: elem_of_list_further.
Qed.

Lemma rchain_sound ρ u s :
  (∀ q, q ∈ rchain u s → lsubst ρ q.1 ≡ lsubst ρ q.2) →
  ∀ x, ρ (var u []) (x ++ s) → ρ (var u s) x.
Proof.
elim: s => [|c s IH] H x; first by rewrite app_nil_r.
move=> Hx; have /right_eq_iff Hr := H _ (elem_of_list_here _ _).
apply/(Hr c x); apply: IH.
- by move=> q Hq; apply: H; apply: elem_of_list_further.
- by rewrite -app_assoc.
Qed.

Lemma lchain_cases p u q : q ∈ lchain p u → ∃ p', q = left_eq p'.
Proof.
elim: u p => [|c u IH] p /=; first by move/elem_of_nil.
by case/elem_of_cons => [->|/IH //]; exists p.
Qed.

Lemma rchain_cases u s q : q ∈ rchain u s → ∃ s', q = right_eq u s'.
Proof.
elim: s => [|c s IH] /=; first by move/elem_of_nil.
by case/elem_of_cons => [->|/IH //]; exists s.
Qed.

(** * The invariant equations *)

Section Eqs.

Variables (Rs : list drule) (bad : list (list A)) (w : list A).

(* X is closed under every rule. *)
Definition close_lhs : UT :=
  tv [] [] ⊔ tjoin ((λ r : drule, tw r.2.1 ⋅ tv r.1.1 r.1.2 ⋅ tw r.2.2) <$> Rs).
Definition close_eq : UE := (close_lhs, tv [] []).

(* X contains w. *)
Definition start_lhs : UT := tw w ⊔ tv [] [].
Definition start_eq : UE := (start_lhs, tv [] []).

(* No word of X starts with b. *)
Definition excl_eq b : UE := (tv b [], ⊥).

Definition inv_eqs : list UE :=
  close_eq :: start_eq :: (excl_eq <$> bad) ++
  (Rs ≫= λ r, lchain [] r.1.1 ++ rchain r.1.1 r.1.2) ++
  (bad ≫= λ b, lchain [] b).

Lemma close_eq_iff ρ :
  lsubst ρ close_lhs ≡ lsubst ρ (tv [] []) ↔
  ∀ r x, r ∈ Rs → ρ (var r.1.1 r.1.2) x →
    ρ (var [] []) (r.2.1 ++ x ++ r.2.2).
Proof.
have HL t : lsubst ρ close_lhs t ↔ ρ (var [] []) t ∨
    ∃ r x, r ∈ Rs ∧ t = r.2.1 ++ x ++ r.2.2 ∧ ρ (var r.1.1 r.1.2) x.
{ rewrite /close_lhs lsubst_join in_join in_tv in_tjoin; split.
  - case=> [H|[_ [/elem_of_list_fmap [r [-> Hr]]]]]; first by left.
    rewrite !lsubst_mul in_mul.
    case=> t12 [t3 [Ht [/in_mul [t1 [t2 [Ht12 [/in_tw Ht1 /in_tv H]]]]
                        /in_tw Ht3]]].
    right; exists r, t2; do !split => //.
    by rewrite Ht Ht12 Ht1 Ht3 -app_assoc.
  - case=> [H|[r [x [Hr [-> H]]]]]; first by left.
    right; exists (tw r.2.1 ⋅ tv r.1.1 r.1.2 ⋅ tw r.2.2); split.
    + by apply/elem_of_list_fmap; exists r.
    + rewrite !lsubst_mul in_mul; exists (r.2.1 ++ x), r.2.2.
      rewrite -app_assoc; do !split => //; last exact/in_tw.
      apply/in_mul; exists r.2.1, x; do !split => //.
      * exact/in_tw.
      * exact/in_tv. }
split.
- move=> H r x Hr Hx; apply/in_tv/H/HL; right; by exists r, x.
- move=> H t; rewrite HL in_tv; split; last by left.
  by case=> // - [r [x [Hr [-> /(H r x Hr)]]]].
Qed.

Lemma start_eq_iff ρ :
  lsubst ρ start_lhs ≡ lsubst ρ (tv [] []) ↔ ρ (var [] []) w.
Proof.
have HL t : lsubst ρ start_lhs t ↔ t = w ∨ ρ (var [] []) t
  by rewrite /start_lhs lsubst_join in_join in_tw in_tv.
split.
- by move=> /(_ w); rewrite HL in_tv => - [+ _]; apply; left.
- move=> Hw t; rewrite HL in_tv; split; last by right.
  by case=> // ->.
Qed.

Lemma excl_eq_iff ρ b :
  lsubst ρ (tv b []) ≡ lsubst ρ ⊥ ↔ ∀ y, ¬ ρ (var b []) y.
Proof.
split.
- by move=> H y; move: (H y); rewrite in_tv lsubst_bot in_bot => - [+ _].
- by move=> H y; rewrite in_tv lsubst_bot in_bot; split => // /H.
Qed.

Lemma inv_eqs_cases q :
  q ∈ inv_eqs →
  q = close_eq ∨ q = start_eq ∨ (∃ b, b ∈ bad ∧ q = excl_eq b) ∨
  (∃ p, q = left_eq p) ∨ (∃ u s, q = right_eq u s).
Proof.
rewrite /inv_eqs !elem_of_cons !elem_of_app; case=> [->|[->|[|[]]]].
- by left.
- by right; left.
- by case/elem_of_list_fmap => b [-> Hb]; right; right; left; exists b.
- case/elem_of_list_bind => r [/elem_of_app [] Hq _].
  + by do 3 right; left; apply: lchain_cases Hq.
  + by case: (rchain_cases Hq) => s ->; do 4 right; exists r.1.1, s.
- case/elem_of_list_bind => b [Hq _].
  by do 3 right; left; apply: lchain_cases Hq.
Qed.

Lemma inv_eqs_star_free q :
  q ∈ inv_eqs → star_free q.1 ∧ star_free q.2.
Proof.
case/inv_eqs_cases => [->|[->|[[b [_ ->]]|[[p ->]|[u [s ->]]]]]] /=;
  do !split => //; apply: star_free_tjoin => //.
Qed.

(** * Soundness *)

Section Sound.

Variable ρ : nat → lang W.
Hypothesis Hsol : lsolves ρ inv_eqs.

Lemma in_inv_rule r q :
  r ∈ Rs → q ∈ lchain [] r.1.1 ++ rchain r.1.1 r.1.2 → q ∈ inv_eqs.
Proof.
move=> Hr Hq; rewrite /inv_eqs !elem_of_cons !elem_of_app.
by right; right; right; left; apply/elem_of_list_bind; exists r.
Qed.

Lemma in_inv_bad b q : b ∈ bad → q ∈ lchain [] b → q ∈ inv_eqs.
Proof.
move=> Hb Hq; rewrite /inv_eqs !elem_of_cons !elem_of_app.
by right; right; right; right; apply/elem_of_list_bind; exists b.
Qed.

Lemma inv_step t t' :
  dstep Rs t t' → ρ (var [] []) t → ρ (var [] []) t'.
Proof.
case=> u [u' [v [v' [x [Hr [-> ->]]]]]] Ht.
have Hx : ρ (var u u') x.
{ apply: rchain_sound.
  - move=> q Hq; apply: Hsol; apply: (in_inv_rule Hr).
    by apply/elem_of_app; right.
  - apply: (lchain_sound (p := [])) Ht => q Hq; apply: Hsol.
    by apply: (in_inv_rule Hr); apply/elem_of_app; left. }
have /close_eq_iff Hc := Hsol (elem_of_list_here _ _).
exact: (Hc _ x Hr Hx).
Qed.

Lemma inv_reach t : rtc (dstep Rs) w t → ρ (var [] []) t.
Proof.
have /start_eq_iff Hw := Hsol (elem_of_list_further _ _ _
                                 (elem_of_list_here _ _)).
move=> Ht; elim: Ht Hw => // t1 t2 t3 H12 _ IH Ht1.
by apply: IH; apply: inv_step H12 Ht1.
Qed.

Lemma inv_avoid t b : ρ (var [] []) t → b ∈ bad → ¬ b `prefix_of` t.
Proof.
move=> Ht Hb [y Hy]; move: Ht; rewrite Hy => Ht.
have Hy' := lchain_sound (p := []) (fun q Hq => Hsol (in_inv_bad Hb Hq)) Ht.
have Hin : excl_eq b ∈ inv_eqs.
{ rewrite /inv_eqs !elem_of_cons !elem_of_app.
  by right; right; left; apply/elem_of_list_fmap; exists b. }
have /excl_eq_iff Hex := Hsol Hin.
exact: Hex Hy'.
Qed.

End Sound.

Theorem inv_sound ρ :
  lsolves ρ inv_eqs →
  ∀ t, rtc (dstep Rs) w t → ∀ b, b ∈ bad → ¬ b `prefix_of` t.
Proof.
move=> Hsol t Ht b Hb.
by apply: (inv_avoid Hsol) Hb; apply: (inv_reach Hsol).
Qed.

(** * Completeness *)

Section Complete.

Variable L : list (list A).
Hypothesis Hw : w ∈ L.
Hypothesis Hclosed : ∀ t t', t ∈ L → dstep Rs t t' → t' ∈ L.
Hypothesis Havoid : ∀ t b, t ∈ L → b ∈ bad → ¬ b `prefix_of` t.

Definition maxlen : nat := list_max (length <$> L).

(* The two-sided derivative of `L`, as a list of words. *)
Definition deriv p s : list (list A) :=
  filter (λ x, p ++ x ++ s ∈ L) (enum_list_lt (S maxlen)).

Lemma elem_of_deriv p s x : x ∈ deriv p s ↔ p ++ x ++ s ∈ L.
Proof.
rewrite /deriv elem_of_list_filter elem_of_enum_list_lt; split; first by case.
move=> Ht; split => //.
have Hmax : ∀ n, n ∈ length <$> L → n ≤ maxlen.
{ rewrite -Forall_forall; exact: (proj1 (list_max_le _ _) (le_n _)). }
have := Hmax (length (p ++ x ++ s)) (elem_of_list_fmap_1 _ _ _ Ht).
rewrite /maxlen !length_app; lia.
Qed.

Definition fL (i : nat) : ka_term W :=
  match decode_nat i : option (list A * list A) with
  | Some (p, s) => ⨆ x ∈ deriv p s, Unit x
  | None => ⊥
  end.

Lemma fL_star_free i : star_free (fL i).
Proof.
rewrite /fL; case: (decode_nat i) => [[p s]|] //.
exact: star_free_join_list.
Qed.

Lemma l_fL p s x : l (fL (var p s)) x ↔ p ++ x ++ s ∈ L.
Proof.
rewrite /fL /var decode_encode_nat.
rewrite (semi_lattice_morphism_join_list (f := @l W)) elem_of_lang_join_list.
split.
- by case=> y [/elem_of_deriv Hy /in_sing ->].
- by move=> Hx; exists x; split; [exact/elem_of_deriv | exact/in_sing].
Qed.

Lemma inv_lsolves : lsolves (λ i, l (fL i)) inv_eqs.
Proof.
move=> q /inv_eqs_cases [->|[->|[[b [Hb ->]]|[[p ->]|[u [s ->]]]]]].
- apply/close_eq_iff => - [[u u'] [v v']] x Hr /=.
  rewrite !l_fL /= app_nil_r => Hx.
  by apply: Hclosed Hx _; exists u, u', v, v', x.
- by apply/start_eq_iff; rewrite l_fL /= app_nil_r.
- apply/excl_eq_iff => y; rewrite l_fL app_nil_r => Hy.
  by apply: (Havoid Hy Hb); exists y.
- apply/left_eq_iff => c y; rewrite !l_fL !app_nil_r -app_assoc.
  reflexivity.
- apply/right_eq_iff => c y; rewrite !l_fL -app_assoc.
  reflexivity.
Qed.

Theorem inv_complete : unif preka_eqv inv_eqs.
Proof.
apply: (unif_of_lsolves (f := fL)).
- exact: fL_star_free.
- exact: inv_eqs_star_free.
- exact: inv_lsolves.
Qed.

End Complete.

End Eqs.

End Invariant.
