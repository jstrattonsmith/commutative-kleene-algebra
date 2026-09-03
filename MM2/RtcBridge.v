(* Bridges Coq's Relation_Operators.clos_refl_trans (what
   coq-library-undecidability's own MM2/MMA2 reachability facts, and
   MM2_simulator.v's mm2_iter_rtc, are stated over) to stdpp's
   relations.rtc (what CKAUndec/Encoding.v's mm2_R_soundness/
   completeness, hence red_leq/R_target, are stated over) -- a standard
   equivalence of reflexive-transitive closures over the same base
   relation, not exposed as a ready-made lemma anywhere in scope.

   Genuinely CKA-specific glue, not MM2-generic content: it only exists
   because this project's own KA-term encoding is built over stdpp's
   relation vocabulary while the underlying MM2 execution model
   (upstream) uses Coq's own. Used directly by CKAUndec/Encoding.v's
   transition relation. *)

From Stdlib Require Import Relations.
From stdpp Require relations.

Lemma crt_to_rtc {A} (R : A -> A -> Prop) (x y : A) :
  clos_refl_trans _ R x y -> relations.rtc R x y.
Proof.
induction 1 as [x y Hxy | x | x y z Hxy IHxy Hyz IHyz].
- eapply relations.rtc_l; [exact Hxy | apply relations.rtc_refl].
- apply relations.rtc_refl.
- eapply relations.rtc_transitive; eassumption.
Qed.
