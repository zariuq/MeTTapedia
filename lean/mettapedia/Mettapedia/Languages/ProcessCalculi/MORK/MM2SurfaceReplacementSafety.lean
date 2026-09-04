import Mettapedia.Languages.ProcessCalculi.MORK.MM2SurfaceProgramSafety
import Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-!
# Renderer-domain preservation for strict finite rule replacement

`replaceMatching?` is the common fail-closed presentation transformation used
by the compact-verifier refinements.  These lemmas establish its renderer
domain contract structurally: it retains each unselected row and substitutes
only the one explicitly supplied replacement row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-- The recursive replacement worker preserves renderer admission when its
input rows and its one replacement row are admitted. -/
theorem replaceMatchingLoop_programSafe
    (selected replacement : Atom) :
    ∀ rules : List Atom,
      programSafe rules = true →
      atomSafe replacement = true →
      atomVariableBudget replacement = true →
      programSafe (replaceMatchingLoop selected replacement rules).2 = true := by
  intro rules
  induction rules with
  | nil =>
      intro _ _ _
      simp [replaceMatchingLoop, programSafe, programVariableBudget]
  | cons rule rest induction =>
      intro rulesSafe replacementAtomSafe replacementBudget
      rcases (programSafe_cons_iff rule rest).mp rulesSafe with
        ⟨ruleAtomSafe, ruleBudget, restSafe⟩
      have translatedSafe := induction restSafe replacementAtomSafe replacementBudget
      rcases loop : replaceMatchingLoop selected replacement rest with
        ⟨seen, translated⟩
      have translatedSafe' : programSafe translated = true := by
        simpa [loop] using translatedSafe
      by_cases selectedRule : rule = selected
      · subst rule
        simp only [replaceMatchingLoop, loop, ↓reduceIte]
        exact (programSafe_cons_iff replacement translated).mpr
          ⟨replacementAtomSafe, replacementBudget, translatedSafe'⟩
      · simp only [replaceMatchingLoop, loop, selectedRule, ↓reduceIte]
        exact (programSafe_cons_iff rule translated).mpr
          ⟨ruleAtomSafe, ruleBudget, translatedSafe'⟩

/-- A successful fail-closed replacement inherits renderer admission from its
input inventory and its explicit replacement row. -/
theorem replaceMatching?_programSafe
    {selected replacement : Atom} {rules replaced : List Atom}
    (rulesSafe : programSafe rules = true)
    (replacementAtomSafe : atomSafe replacement = true)
    (replacementBudget : atomVariableBudget replacement = true)
    (exact : replaceMatching? selected replacement rules = some replaced) :
    programSafe replaced = true := by
  have loopSafe := replaceMatchingLoop_programSafe selected replacement rules
    rulesSafe replacementAtomSafe replacementBudget
  rcases loop : replaceMatchingLoop selected replacement rules with
    ⟨seen, translated⟩
  simp [replaceMatching?, loop] at exact
  rcases exact with ⟨_, exactRows⟩
  subst replaced
  simpa [loop] using loopSafe

section AxiomAudit

#print axioms replaceMatchingLoop_programSafe
#print axioms replaceMatching?_programSafe

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
