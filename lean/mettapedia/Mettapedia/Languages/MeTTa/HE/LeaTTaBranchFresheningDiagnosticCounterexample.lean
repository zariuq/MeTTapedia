import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationSelectionConformance

/-!
# Branch-local freshening changes polymorphic failure diagnostics

The repaired argument checker includes the current private binding names in
the avoid set used for each later argument.  Two successful head branches can
therefore give the same raw tail candidate different private spellings.  A
failed tail match records that freshened candidate in `BadArgType.actual`, so
the two diagnostics are not literally equal even though their private
variable spellings are alpha-equivalent.

This file pins the representation boundary before the branch-scan
equivariance theorem is stated.  It does not prescribe whether a later repair
should report the raw candidate or whether the conformance observation should
compare private diagnostic fields up to alpha-renaming.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBranchFresheningDiagnosticCounterexample

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Selection
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaTypeConformance
open LeaTTaTypePresentationExactConformance
open LeaTTaTypePresentationSelectionConformance

private def nativeRawCandidate : Atom :=
  .expression [.symbol "P", .var "u"]

private def nativeFormalType : Atom :=
  .expression [.symbol "Q", .symbol "A"]

private def rawCandidate : Metta.Atom :=
  .expr [.sym "P", .var "u"]

private def formalType : Metta.Atom :=
  .expr [.sym "Q", .sym "A"]

private def shortFresh : Metta.Atom :=
  Metta.Minimal.freshenTypeCandidate ["x"] 1 rawCandidate

private def longFresh : Metta.Atom :=
  Metta.Minimal.freshenTypeCandidate ["longer"] 1 rawCandidate

/-- A short prior private name yields the corresponding two-hash prefix. -/
theorem short_branch_fresh_candidate :
    shortFresh = .expr [.sym "P", .var "##u#1"] := by
  simp [shortFresh, rawCandidate, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.Minimal.captureAvoidingName,
    Metta.Minimal.avoidancePrefix]
  decide

/-- A longer prior private name changes the later candidate's private prefix. -/
theorem long_branch_fresh_candidate :
    longFresh = .expr [.sym "P", .var "#######u#1"] := by
  simp [longFresh, rawCandidate, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.Minimal.captureAvoidingName,
    Metta.Minimal.avoidancePrefix]
  decide

/-- The same raw candidate is not presented by one literal atom across the
two private branch states. -/
theorem branch_fresh_candidates_not_equal : shortFresh ≠ longFresh := by
  rw [short_branch_fresh_candidate, long_branch_fresh_candidate]
  simp

/-- Although the literal atoms differ, both private candidates are injective
alpha-presentations of the same raw type. -/
theorem branch_fresh_candidates_alpha_related :
    ObservedTypeAlphaRel
      (fromLeaTTaAtom shortFresh) (fromLeaTTaAtom longFresh) := by
  have shortVariant :=
    freshenTypeCandidate_alphaVariant ["x"] 1 nativeRawCandidate
  have longVariant :=
    freshenTypeCandidate_alphaVariant ["longer"] 1 nativeRawCandidate
  refine ⟨nativeRawCandidate,
    shortVariant.toTypeVariableRenamingOf,
    longVariant.toTypeVariableRenamingOf⟩

/-- Both private presentations fail against the same structurally distinct
formal type. -/
theorem short_branch_match_fails :
    Metta.Minimal.matchType [] formalType shortFresh = none := by
  rw [short_branch_fresh_candidate]
  rfl

theorem long_branch_match_fails :
    Metta.Minimal.matchType [] formalType longFresh = none := by
  rw [long_branch_fresh_candidate]
  rfl

private def shortDiagnostic : Metta.Minimal.TypeCheckArgsError :=
  { position := 2
    expected := formalType
    actual := shortFresh }

private def longDiagnostic : Metta.Minimal.TypeCheckArgsError :=
  { position := 2
    expected := formalType
    actual := longFresh }

/-- The observable diagnostic records the branch-local fresh spelling, so a
literal-equality equivariance claim is false for polymorphic failures. -/
theorem branch_failure_diagnostics_not_equal :
    shortDiagnostic ≠ longDiagnostic := by
  intro equal
  have actualEqual := congrArg Metta.Minimal.TypeCheckArgsError.actual equal
  exact branch_fresh_candidates_not_equal (by
    simpa [shortDiagnostic, longDiagnostic] using actualEqual)

private def nativeDiagnostic : ArgumentTypeDiagnostic :=
  { position := 2
    expected := nativeFormalType
    actual := nativeRawCandidate }

/-- The field-wise diagnostic boundary relates both branch-local runtime
errors to one public diagnostic: position and expected type are literal,
while only the generated actual-type spelling is quotiented by private
alpha-renaming. -/
theorem both_branch_diagnostics_share_alpha_observation :
    ArgumentTypeDiagnosticRuntimeRel nativeDiagnostic shortDiagnostic ∧
      ArgumentTypeDiagnosticRuntimeRel nativeDiagnostic longDiagnostic := by
  have shortAlpha : ObservedTypeAlphaRel nativeRawCandidate
      (fromLeaTTaAtom shortFresh) := by
    refine ⟨nativeRawCandidate, TypeVariableRenamingOf.refl _, ?_⟩
    simpa [shortFresh, rawCandidate, nativeRawCandidate, toLeaTTaAtom] using
      (freshenTypeCandidate_alphaVariant ["x"] 1
        nativeRawCandidate).toTypeVariableRenamingOf
  have longAlpha : ObservedTypeAlphaRel nativeRawCandidate
      (fromLeaTTaAtom longFresh) := by
    refine ⟨nativeRawCandidate, TypeVariableRenamingOf.refl _, ?_⟩
    simpa [longFresh, rawCandidate, nativeRawCandidate, toLeaTTaAtom] using
      (freshenTypeCandidate_alphaVariant ["longer"] 1
        nativeRawCandidate).toTypeVariableRenamingOf
  constructor
  · exact
      { position := rfl
        expected := by
          simpa [nativeDiagnostic, shortDiagnostic, formalType,
            nativeFormalType, fromLeaTTaAtom] using
            ObservedTypeAlphaRel.refl nativeFormalType
        actual := by
          simpa [nativeDiagnostic, shortDiagnostic] using shortAlpha }
  · exact
      { position := rfl
        expected := by
          simpa [nativeDiagnostic, longDiagnostic, formalType,
            nativeFormalType, fromLeaTTaAtom] using
            ObservedTypeAlphaRel.refl nativeFormalType
        actual := by
          simpa [nativeDiagnostic, longDiagnostic] using longAlpha }

/-! ## Why successful branches also need an alpha-scoped carrier -/

private def spellingDiscriminator : String → Atom :=
  fun name => if name = "uB" then .symbol "B" else .symbol "A"

/-- Renaming a private candidate in a successful match changes the global
solution theory even when every public name is fixed.  Consequently a static
spec presentation cannot be paired with both runtime spellings by the
unscoped `TypePresentationSimulationState`; the branch boundary must retain
an exact branch-local state and compare it to the static presentation only at
the declared public scope. -/
theorem private_spelling_changes_global_solution_theory :
    ¬∀ valuation,
      TypeSubstSatisfied valuation [("t", .var "uA")] ↔
        TypeSubstSatisfied valuation [("t", .var "uB")] := by
  intro equivalent
  have := equivalent spellingDiscriminator
  simp [TypeSubstSatisfied, spellingDiscriminator, applyTypeValuation] at this

end Mettapedia.Languages.MeTTa.HE.LeaTTaBranchFresheningDiagnosticCounterexample
