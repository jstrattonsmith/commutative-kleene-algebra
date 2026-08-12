(* A decidable, functional stepper for coq-library-undecidability's MM2
   (two-counter machine) model: a single-instruction step function
   (mm2_atom_fun) and its program-indexed extension (mm2_step_fun),
   proved equivalent to the library's own relational mm2_atom/mm2_step,
   plus the two facts (determinism, and the halted-iff-out-of-bounds
   characterization) built directly on top.

   Extracted 2026-08-14 from mm.v's own Section MM2Adapter, where this
   fragment lived embedded among the actual KA-term encoding (mm2_R, C,
   T, red_lb/red_ub, etc.). Nothing here mentions a KA term, a
   pre-Kleene algebra, or this project's own encoding at all -- it's
   purely about the MM2 execution model, reusable by any other MM2-based
   project. mm.v now Requires this file instead of defining the
   fragment locally. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list.
From Stdlib Require Import Lia.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* mm2_atom_fun doesn't depend on a program at all -- it's the semantics
   of a single instruction, not a program-indexed step. *)

Definition mm2_atom_fun (ρ : mm2_instr) (s : mm2_state) :=
  let '(i,(a,b)) := s in
  match ρ with
  | mm2_inc_a => (1+i,(S a,b))
  | mm2_inc_b => (1+i,(a,S b))
  | mm2_dec_a j =>
    match a with
    | 0 => (1+i,(0,b))
    | S a => (j,(a,b))
    end
  | mm2_dec_b j =>
    match b with
    | 0 => (1+i,(a,0))
    | S b => (j,(a,b))
    end
  end.

Lemma mm2_atom_fun_spec ρ s1 s2 :
  mm2_atom ρ s1 s2 ↔ mm2_atom_fun ρ s1 = s2.
Proof.
split.
- by case.
- case: ρ => [||j|j].
  1,2: case: s1 => [i [a b]] /= <-; constructor.
  + case: s1 => [i [[|a] b]] /= <-; constructor.
  + case: s1 => [i [a [|b]]] /= <-; constructor.
Qed.

Arguments mm2_atom_fun_spec {_ _ _}.

Section MM2Stepper.

Variable P : list mm2_instr.
Let n := length P.

Definition mm2_step_fun s :=
  match s.1 with
  | 0 => None
  | S i => match nth_error P i with
           | Some ρ => Some (mm2_atom_fun ρ s)
           | None => None
           end
  end.

Lemma mm2_instr_at_nth_error ρ i :
  mm2_instr_at ρ (S i) P ↔ nth_error P i = Some ρ.
Proof.
split.
- case=> l [r [HP Hlen]].
  have -> : i = length l by lia.
  by rewrite HP nth_error_app2 // Nat.sub_diag.
- move=> Hnth.
  have [l [r [HP Hlen]]] :=
    nth_error_split _ _ Hnth.
  by exists l, r; split; first done; lia.
Qed.

Lemma mm2_step_fun_spec s1 s2 :
  mm2_step P s1 s2 ↔ mm2_step_fun s1 = Some s2.
Proof.
split.
- case=> ρ [Hinstr /mm2_atom_fun_spec <-].
  rewrite /mm2_step_fun /=.
  case: s1 Hinstr => [[|i] [a b]] /= Hinstr.
  { case: Hinstr => l [r [_ /=]]; lia. }
  by rewrite (iffLR (mm2_instr_at_nth_error _ _) Hinstr).
- rewrite /mm2_step_fun.
  case: s1 => [[|i] [a b]] //=.
  case Hnth: (nth_error P i) => [ρ|] //= [<-].
  exists ρ; split.
  + by apply/mm2_instr_at_nth_error.
  + by apply/mm2_atom_fun_spec.
Qed.

Arguments mm2_step_fun_spec {_ _}.

Lemma mm2_step_det s s1 s2 :
  mm2_step P s s1 → mm2_step P s s2 → s1 = s2.
Proof.
move/mm2_step_fun_spec => H1 /mm2_step_fun_spec.
by rewrite H1; case.
Qed.

Lemma mm2_stop_spec s : mm2_stop P s ↔ ¬ (0 < index s ≤ n).
Proof.
case: s=> [i [a b]]; split.
- move=> s_stop s_bounds; case e: (mm2_step_fun (i,(a,b))) => [s'|].
  + by apply: (s_stop s'); apply/mm2_step_fun_spec.
  + rewrite /mm2_step_fun /mm2_atom_fun /= in e s_bounds.
    case: i {s_stop} => [|i] in e s_bounds; first lia.
    case P_i: nth_error => [ρ|] //= in e *.
    move/nth_error_None in P_i; lia.
- move=> /= s_bounds s' /mm2_step_fun_spec.
  rewrite /mm2_step_fun /mm2_atom_fun /=.
  case: i => [|i] //= in s_bounds *.
  case P_i: nth_error => [ρ|] //.
  have: i < n by apply/nth_error_Some; congruence.
  lia.
Qed.

End MM2Stepper.

Arguments mm2_step_fun_spec {_ _ _}.
