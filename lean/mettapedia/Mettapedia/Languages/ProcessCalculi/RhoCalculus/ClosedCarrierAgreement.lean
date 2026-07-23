import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefTypingAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-!
# Exact agreement of the generic and established closed rho carriers

The generic carrier is derived from the exact `rhoCalc` declarations.  This
module proves that its process and name fibers coincide with the established
closed carrier used by `rhoRewriteSystem`; it introduces no new rho syntax or
admission policy.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefTypingAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-- For the sole reflective presentation authored by `rhoCalc`, generic
scope safety is exactly the established quotation-aware scope check. -/
theorem rho_scopeSafe_iff (pattern : Pattern) :
    ScopeSafe rhoCalc pattern ↔
      binderSafeAt "NQuote" 0 pattern = true := by
  constructor
  · intro safe
    exact safe.2 rhoReflectivePresentation (by simp [rhoCalc])
  · intro safe
    refine ⟨isWellScopedAt_of_binderSafeAt "NQuote" safe, ?_⟩
    intro presentation membership
    simp only [rhoCalc, List.mem_singleton] at membership
    subst presentation
    exact safe

private theorem emptyFreeContexts_agree :
    liftFreeSortContext FreeSortContext.empty = FreeTypeContext.empty := by
  funext name
  simp [liftFreeSortContext, FreeSortContext.empty, FreeTypeContext.empty]

/-- The generic process fiber derived from `rhoCalc` is exactly the process
fiber already used by `rhoRewriteSystem`. -/
theorem closed_process_wellSorted_iff (pattern : Pattern) :
    ClosedTermWellSorted rhoCalc rhoProc pattern ↔
      RhoClosedTermWellSorted rhoProc pattern := by
  rw [rhoClosedTermWellSorted_process_iff]
  constructor
  · rintro ⟨typed, ground, canonical, object, safe⟩
    have typed' :
        HasSort rhoCalc (liftFreeSortContext FreeSortContext.empty) []
          pattern "Proc" := by
      simpa [rhoProc, emptyFreeContexts_agree] using typed
    exact ⟨languageDefHasSort_to_procWellSorted typed' object canonical,
      (rho_scopeSafe_iff pattern).mp safe⟩
  · rintro ⟨typed, binderSafe⟩
    have generated := procWellSorted_toLanguageDefHasSort typed
    have properties := procWellSorted_object_canonical typed
    have generated' :
        HasSort rhoCalc FreeTypeContext.empty [] pattern rhoProc.1 := by
      simpa [rhoProc, emptyFreeContexts_agree, liftBoundSortContext] using
        generated
    have safe : ScopeSafe rhoCalc pattern :=
      (rho_scopeSafe_iff pattern).mpr binderSafe
    exact ⟨generated',
      ground_of_closed_sorting generated' properties.1 safe,
      properties.2, properties.1, safe⟩

/-- The generic name fiber derived from `rhoCalc` is exactly the name fiber
already used by `rhoRewriteSystem`. -/
theorem closed_name_wellSorted_iff (pattern : Pattern) :
    ClosedTermWellSorted rhoCalc rhoName pattern ↔
      RhoClosedTermWellSorted rhoName pattern := by
  rw [rhoClosedTermWellSorted_name_iff]
  constructor
  · rintro ⟨typed, ground, canonical, object, safe⟩
    have typed' :
        HasSort rhoCalc (liftFreeSortContext FreeSortContext.empty) []
          pattern "Name" := by
      simpa [rhoName, emptyFreeContexts_agree] using typed
    exact ⟨languageDefHasSort_to_nameWellSorted typed' object canonical,
      (rho_scopeSafe_iff pattern).mp safe⟩
  · rintro ⟨typed, binderSafe⟩
    have generated := nameWellSorted_toLanguageDefHasSort typed
    have properties := nameWellSorted_object_canonical typed
    have generated' :
        HasSort rhoCalc FreeTypeContext.empty [] pattern rhoName.1 := by
      simpa [rhoName, emptyFreeContexts_agree, liftBoundSortContext] using
        generated
    have safe : ScopeSafe rhoCalc pattern :=
      (rho_scopeSafe_iff pattern).mpr binderSafe
    exact ⟨generated',
      ground_of_closed_sorting generated' properties.1 safe,
      properties.2, properties.1, safe⟩

/-- Carrier equivalence for closed rho processes.  Both sides retain the
same raw pattern; only their independently derived admission witnesses are
translated. -/
def closedProcessEquiv :
    ClosedTerm rhoCalc rhoProc ≃ RhoClosedTerm rhoProc where
  toFun term := ⟨term.1, (closed_process_wellSorted_iff term.1).mp term.2⟩
  invFun term := ⟨term.1, (closed_process_wellSorted_iff term.1).mpr term.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Carrier equivalence for closed rho names. -/
def closedNameEquiv :
    ClosedTerm rhoCalc rhoName ≃ RhoClosedTerm rhoName where
  toFun term := ⟨term.1, (closed_name_wellSorted_iff term.1).mp term.2⟩
  invFun term := ⟨term.1, (closed_name_wellSorted_iff term.1).mpr term.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem closedProcessEquiv_pattern (term : ClosedTerm rhoCalc rhoProc) :
    (closedProcessEquiv term).1 = term.1 :=
  rfl

@[simp]
theorem closedNameEquiv_pattern (term : ClosedTerm rhoCalc rhoName) :
    (closedNameEquiv term).1 = term.1 :=
  rfl

/-! ## Positive and negative controls -/

/-- Positive: the existing closed nil process is admitted by the generic
carrier and transported back without changing its syntax. -/
example :
    (closedProcessEquiv.symm closedNil).1 = .apply "PZero" [] :=
  rfl

/-- Negative: a dangling top-level de Bruijn index cannot enter the generic
closed process fiber. -/
theorem top_bvar_not_closed_process :
    ¬ ClosedTermWellSorted rhoCalc rhoProc (.bvar 0) := by
  intro typed
  exact bvar_not_typed_in_empty typed.1

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
