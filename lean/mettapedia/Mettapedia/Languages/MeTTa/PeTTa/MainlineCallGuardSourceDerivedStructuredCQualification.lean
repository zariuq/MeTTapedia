import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCLifecycle
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCInputs
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCResults

/-!
# Complete qualification of source-derived call-guard bodies

This module aggregates the independently checked lifecycle, input, and result
certificates.  It proves exact inventory agreement only after every body has
been compiled from its authored source occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

private theorem sourceOccurrences_eq_authoredOrder :
    sourceOccurrences =
      [ ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩
      , ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩
      , ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩
      , ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩
      , ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩ ] := by
  decide +kernel

private theorem bodyOptionAt_of_same_value
    (left right :
      Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation.SourceOccurrence)
    (same : left.val = right.val) {body : Pattern}
    (compiled : bodyOptionAt right = some body) :
    bodyOptionAt left = some body := by
  rw [Fin.ext same]
  exact compiled

/-- The source-derived compiler reproduces the qualified target inventory,
including authored order and multiplicity. -/
theorem sourceDerivedBodies?_eq_allMatchedFamilyBodies :
    sourceDerivedBodies? = some allMatchedFamilyBodies := by
  rw [sourceDerivedBodies?, sourceOccurrences_eq_authoredOrder]
  simp only [List.mapM_cons, List.mapM_nil]
  rw [ bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_finish
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_skipHead
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_skipArity
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_beginDeclaration
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_argumentsFinished
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_rawInput
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_undefinedInput
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_holeInput
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_checkedInput
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_openInput
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_undefinedResult
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_holeResult
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_atomResult
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_checkedResult
     , bodyOptionAt_of_same_value _ _ rfl bodyOptionAt_openResult ]
  rfl

/-- Any successful complete compilation has exactly fifteen target bodies. -/
theorem sourceDerivedBodies?_length
    {bodies : List Pattern} (compiled : sourceDerivedBodies? = some bodies) :
    bodies.length = 15 := by
  rw [sourceDerivedBodies?_eq_allMatchedFamilyBodies] at compiled
  have exactBodies : bodies = allMatchedFamilyBodies :=
    (Option.some.inj compiled).symm
  simpa [exactBodies] using allMatchedFamilyBodies_length

/-- Every body returned by the source-derived compiler is well sorted in the
StructuredC target language. -/
theorem sourceDerivedBodies?_target_typed
    {bodies : List Pattern} (compiled : sourceDerivedBodies? = some bodies)
    {body : Pattern} (membership : body ∈ bodies) :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] body (.base "Statements") = true := by
  rw [sourceDerivedBodies?_eq_allMatchedFamilyBodies] at compiled
  have exactBodies : bodies = allMatchedFamilyBodies :=
    (Option.some.inj compiled).symm
  rw [exactBodies] at membership
  exact allMatchedFamilyBodies_target_typed membership

/-- Successful source-derived output contains no broad semantic callback. -/
theorem sourceDerivedBodies?_avoid_broad_hooks
    {bodies : List Pattern} (compiled : sourceDerivedBodies? = some bodies) :
    bodies.any usesForbiddenBroadHook = false := by
  rw [sourceDerivedBodies?_eq_allMatchedFamilyBodies] at compiled
  have exactBodies : bodies = allMatchedFamilyBodies :=
    (Option.some.inj compiled).symm
  simpa [exactBodies] using all_matched_bodies_avoid_broad_hooks

/-- Swapping two source occurrences changes the compiled target inventory;
the compiler does not treat rule order as administrative metadata. -/
example :
    sourceDerivedBodies? ≠
      some
        [ finishBody, skipArityBody, skipHeadBody, beginDeclarationBody
        , argumentsFinishedBody, rawInputBody, undefinedInputBody, holeInputBody
        , checkedInputBody, openInputBody, undefinedResultBody, holeResultBody
        , atomResultBody, checkedResultBody, openResultBody ] := by
  rw [sourceDerivedBodies?_eq_allMatchedFamilyBodies]
  decide +kernel

#print axioms sourceDerivedBodies?_eq_allMatchedFamilyBodies
#print axioms sourceDerivedBodies?_length
#print axioms sourceDerivedBodies?_target_typed
#print axioms sourceDerivedBodies?_avoid_broad_hooks

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC
