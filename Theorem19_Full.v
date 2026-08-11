(* Closes a gap Arthur flagged after reviewing the proof: K_m_complete
   (Theorem19_MComplete.v) only shows m-completeness of K itself, which
   is a SLICE of the actual KA-term inequality relation KA_ineq
   (K_Enumerable.v) -- fixing the right-hand side to one specific term,
   red_ub Prog, and varying only the left. The source paper's own
   Theorem 18/19 are stated over the full relation {(x,y) | x ⊑ y}, not
   over one fixed slice of it, so a theorem about K alone does not yet
   match what those theorems actually claim.

   Closing this needs no new construction: K_Enumerable.v already
   builds the reduction K_to_KA_ineq witnessing K ⪯ₘ KA_ineq (used
   there in the OPPOSITE direction, to import KA_ineq's enumerability
   INTO K). Composing K_m_complete's hardness with that same reduction,
   via red_m_transitive, transports m-completeness the other way, OUT
   of K and into KA_ineq -- immediate once you have the reduction in
   hand, since `m-complete p` (Axioms/EA.v) is pure many-one hardness
   with no enumerability side-condition on the target. *)

From Stdlib Require Import Unicode.Utf8.
From kacc Require Import Theorem19_MComplete.
From kacc Require Import K_Enumerable.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.CRM.principles.
Require Import SyntheticComputability.Synthetic.reductions.
Require Import SyntheticComputability.Axioms.EA.

Theorem KA_ineq_m_complete : CT_L -> MP -> exists c : nat, m-complete (@KA_ineq c).
Proof.
intros ct MP_assm.
destruct (K_m_complete ct MP_assm) as [c Hc].
exists c.
intros q Hq.
apply (red_m_transitive (Theorem17_KATerm.K c) (@KA_ineq c)).
- exact (Hc q Hq).
- exists (K_to_KA_ineq c). exact (K_to_KA_ineq_spec c).
Qed.
