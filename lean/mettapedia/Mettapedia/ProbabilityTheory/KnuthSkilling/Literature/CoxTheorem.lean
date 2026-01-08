import Mettapedia.ProbabilityTheory.Cox
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.FunctionalEquations

/-!
# Cox’s theorem (Dupré–Tipler / Terenin–Draper): Lean-facing hooks

This file does **not** attempt to re-prove the full Cox theorem from the PDFs. Instead it:

1. Points at the existing Cox formalization in `Mettapedia/ProbabilityTheory/Cox/`.
2. Exposes small “connector” lemmas that relate Cox’s associativity equation to the generic
   *additive regraduation* form.

Primary sources (local PDFs):
- Dupré & Tipler, “The Cox Theorem: Unknowns and Plausible Values” (arXiv:math/0611795),
  `literature/KS_codex/Dupre_Tipler_2006_Cox_Theorem.pdf`.
- Terenin & Draper, “Jaynes’ Cox theorem and the logic of plausible inference” (arXiv:1507.06597),
  `literature/KS_codex/Terenin_Draper_2017_Cox_Theorem_Jaynesian.pdf`.

The key overlap with Knuth–Skilling is the same functional-equation shape:
`Θ (op x y) = Θ x + Θ y`,
which makes commutativity an immediate corollary once such a `Θ` exists.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

open Classical

open Mettapedia.ProbabilityTheory.Cox

/-!
## Connectors: additive representation ⇒ Cox associativity

If a conjunction rule `F` is representable by addition under an order isomorphism, then the
associativity equation holds (and commutativity follows automatically).
-/

theorem cox_associativity_of_additiveOrderIsoRep {F : ℝ → ℝ → ℝ}
    (h : AdditiveOrderIsoRep ℝ F) : Cox.AssociativityEquation F := by
  intro x y z
  simpa using (AdditiveOrderIsoRep.op_assoc (α := ℝ) (op := F) h x y z)

theorem cox_comm_of_additiveOrderIsoRep {F : ℝ → ℝ → ℝ}
    (h : AdditiveOrderIsoRep ℝ F) : ∀ x y : ℝ, F x y = F y x :=
  AdditiveOrderIsoRep.op_comm (α := ℝ) (op := F) h

end Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

