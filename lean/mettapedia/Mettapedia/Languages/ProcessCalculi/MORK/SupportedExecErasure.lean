import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# Supported directive erasure

These lemmas expose the small list law used by remove-before-interpret
schedulers: consuming one supported directive erases exactly its decoded
candidate and leaves every other candidate in presentation order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open WQComputable

theorem extractSupportedSourceExecFact_atom {atom : Atom}
    {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    directive.atom = atom := by
  unfold extractSupportedSourceExecFact at decoded
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at decoded
  | some raw =>
      have rawAtom : raw.atom = atom := by
        unfold extractRawExecFact at rawEq
        split at rawEq
        · exact (congrArg RawExecFact.atom (Option.some.inj rawEq)).symm
        · simp at rawEq
      simp only [rawEq] at decoded
      unfold decodeSupportedSourceExec at decoded
      cases inputEq : parseSupportedInput raw.inputExpr <;>
        simp [inputEq] at decoded
      cases templateEq : parseSupportedTemplate raw.templateExpr <;>
        simp [templateEq] at decoded
      subst directive
      exact rawAtom

/-- Decoding commutes with consuming one successfully decoded directive.
This is independent of the directive's rule body and scheduler key. -/
theorem cSupportedSourceExecFacts_erase (space : List Atom)
    (directive : SourceExecFact)
    (decoded : extractSupportedSourceExecFact directive.atom =
      some directive) :
    cSupportedSourceExecFacts (space.erase directive.atom) =
      (cSupportedSourceExecFacts space).erase directive := by
  unfold cSupportedSourceExecFacts
  induction space with
  | nil => rfl
  | cons head tail induction =>
      by_cases headEq : head = directive.atom
      · subst head
        simp [decoded]
      · have headBeq : ¬(head == directive.atom) := by
          simpa using headEq
        rw [List.erase_cons_tail headBeq]
        simp only [List.filterMap_cons]
        cases headDecoded : extractSupportedSourceExecFact head with
        | none => simp [induction]
        | some headDirective =>
            have directiveNe : headDirective ≠ directive := by
              intro equal
              subst headDirective
              exact headEq
                (extractSupportedSourceExecFact_atom headDecoded).symm
            simp [directiveNe, induction]

#print axioms extractSupportedSourceExecFact_atom
#print axioms cSupportedSourceExecFacts_erase

end Mettapedia.Languages.ProcessCalculi.MORK
