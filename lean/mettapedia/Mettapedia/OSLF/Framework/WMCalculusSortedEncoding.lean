import Mettapedia.OSLF.Framework.WMCalculusEncoding
import Mettapedia.OSLF.Framework.WMCalculusContextEncoding
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Sorting the existing WM encoding by its authored signature

WM atoms are free variables in the raw representation. An encoded term is
well sorted exactly when its state and query atoms have their respective
types in the supplied free-variable context. This makes the naming condition
explicit without changing the operational encoding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusSortedEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism

def sortType : WMSort → TypeExpr
  | .state => .base "State"
  | .query => .base "Query"
  | .evidence => .base "BinaryEvidence"

/-- Precisely the leaf assignments required by the existing encoder. -/
def AtomsTyped (free : FreeTypeContext) : {s : WMSort} → WMTerm s → Prop
  | _, .state name => free name = some (sortType .state)
  | _, .query name => free name = some (sortType .query)
  | _, .revise first second => AtomsTyped free first ∧ AtomsTyped free second
  | _, .extract world query => AtomsTyped free world ∧ AtomsTyped free query
  | _, .combine first second => AtomsTyped free first ∧ AtomsTyped free second
  | _, .zero => True

theorem encodeWM_isObject {s : WMSort} (term : WMTerm s) :
    isObjectPattern (encodeWM term) = true := by
  induction term <;>
    simp_all [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero,
      isObjectPattern, isObjectPatternList]

/-- The WM encoder creates no display-name binder metadata. -/
theorem encodeWM_hasCanonicalBinderMetadata {s : WMSort} (term : WMTerm s) :
    (encodeWM term).hasCanonicalBinderMetadata = true := by
  induction term <;>
    simp_all [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]

/-- Encoded WM terms have no bound indices, at any ambient binder depth. -/
theorem encodeWM_isWellScopedAt {s : WMSort} (term : WMTerm s)
    (depth : Nat) : (encodeWM term).isWellScopedAt depth = true := by
  induction term <;>
    simp_all [encodeWM, pRevise, pExtract, pCombine, pEvidenceZero,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-- The actual authored checker accepts exactly the consistent atom typings. -/
theorem check_encodeWM_iff (lang : LanguageDef) (declared : lang.terms = coreTerms)
    {s : WMSort} (free : FreeTypeContext)
    (term : WMTerm s) :
    checkHasType lang free [] (encodeWM term) (sortType s) = true ↔
      AtomsTyped free term := by
  induction term <;>
    simp_all [encodeWM, sortType, AtomsTyped, checkHasType,
      checkArgumentsHaveTypes, coreTerms,
      reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
      pRevise, pExtract, pCombine, pEvidenceZero, parameterType?,
      usesBareCollection?, matchesParameterRepresentation?]

/-- Encoded WM terms contain no bound indices, so their sorting criterion is
independent of the surrounding binder stack. -/
theorem check_encodeWM_iff_bound (lang : LanguageDef)
    (declared : lang.terms = coreTerms) {s : WMSort}
    (free : FreeTypeContext) (bound : List TypeExpr) (term : WMTerm s) :
    checkHasType lang free bound (encodeWM term) (sortType s) = true ↔
      AtomsTyped free term := by
  induction term <;>
    simp_all [encodeWM, sortType, AtomsTyped, checkHasType,
      checkArgumentsHaveTypes, coreTerms,
      reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
      pRevise, pExtract, pCombine, pEvidenceZero, parameterType?,
      usesBareCollection?, matchesParameterRepresentation?]

/-- This is the declaration-derived sorting judgment, not a parallel type system. -/
theorem encodeWM_hasType_iff (lang : LanguageDef) (declared : lang.terms = coreTerms)
    {s : WMSort} (free : FreeTypeContext)
    (term : WMTerm s) :
    HasType lang free [] (encodeWM term) (sortType s) ↔
      AtomsTyped free term :=
  (checkHasType_eq_true_iff (encodeWM_isObject term)).symm.trans
    (check_encodeWM_iff lang declared free term)

theorem encodeWM_hasType_iff_bound (lang : LanguageDef)
    (declared : lang.terms = coreTerms) {s : WMSort}
    (free : FreeTypeContext) (bound : List TypeExpr) (term : WMTerm s) :
    HasType lang free bound (encodeWM term) (sortType s) ↔
      AtomsTyped free term :=
  (checkHasType_eq_true_iff (encodeWM_isObject term)).symm.trans
    (check_encodeWM_iff_bound lang declared free bound term)

/-- The complete native open-pattern admission criterion for a WM encoding
is exactly the sorting of its named atoms. The non-typing checks are genuine
properties of the encoder, not additional assumptions. -/
theorem encodeWM_openPatternWellSorted_iff_bound (lang : LanguageDef)
    (declared : lang.terms = coreTerms) {s : WMSort}
    (free : FreeTypeContext) (bound : List TypeExpr) (term : WMTerm s) :
    OpenPatternWellSorted lang free bound (sortType s) (encodeWM term) ↔
      AtomsTyped free term := by
  constructor
  · intro admitted
    exact (encodeWM_hasType_iff_bound lang declared free bound term).1
      admitted.1
  · intro typed
    refine ⟨(encodeWM_hasType_iff_bound lang declared free bound term).2 typed,
      encodeWM_hasCanonicalBinderMetadata term, encodeWM_isObject term, ?_⟩
    simpa only [ScopeSafeAt] using
      encodeWM_isWellScopedAt term bound.length

theorem atomsTyped_of_step {free : FreeTypeContext} {s : WMSort}
    {source target : WMTerm s} (step : WMStep source target)
    (typed : AtomsTyped free source) : AtomsTyped free target := by
  cases step <;> simp_all [AtomsTyped]

theorem atomsTyped_of_contextStep {free : FreeTypeContext} {s : WMSort}
    {source target : WMTerm s} (step : WMContextStep source target)
    (typed : AtomsTyped free source) : AtomsTyped free target := by
  induction step with
  | root step => exact atomsTyped_of_step step typed
  | revise_left | revise_right | extract_left | extract_right |
      combine_left | combine_right => simp_all [AtomsTyped]

theorem atomsTyped_of_contextStepStar {free : FreeTypeContext} {s : WMSort}
    {source target : WMTerm s} (steps : WMContextStepStar source target)
    (typed : AtomsTyped free source) : AtomsTyped free target := by
  induction steps with
  | refl => exact typed
  | tail _ step previous => exact atomsTyped_of_contextStep step previous

/-- Every reduct of a sorted encoded term remains sorted by the actual
contextual presentation, after any number of steps and at every depth. -/
theorem contextual_reduct_hasType {free : FreeTypeContext} {s : WMSort}
    (source : WMTerm s) {target : Pattern}
    (typed : HasType (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      free [] (encodeWM source) (sortType s))
    (steps : LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM source) target) :
    HasType (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      free [] target (sortType s) := by
  obtain ⟨reduct, termSteps, rfl⟩ := wmContextStepStar_complete source steps
  apply (encodeWM_hasType_iff _ rfl free reduct).2
  exact atomsTyped_of_contextStepStar termSteps
    ((encodeWM_hasType_iff _ rfl free source).1 typed)

/-- Operational adequacy recovers an encoded reduct, so the full native open
carrier, including binder metadata, object form, and scope, is preserved by
every contextual WM computation. -/
theorem contextual_reduct_openPatternWellSorted
    {free : FreeTypeContext} {s : WMSort}
    (source : WMTerm s) {target : Pattern} (bound : List TypeExpr)
    (admitted : OpenPatternWellSorted
      (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      free bound (sortType s) (encodeWM source))
    (steps : LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM source) target) :
    OpenPatternWellSorted
      (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      free bound (sortType s) target := by
  obtain ⟨reduct, termSteps, rfl⟩ := wmContextStepStar_complete source steps
  exact (encodeWM_openPatternWellSorted_iff_bound _ rfl free bound reduct).2
    (atomsTyped_of_contextStepStar termSteps
      ((encodeWM_openPatternWellSorted_iff_bound _ rfl free bound source).1
        admitted))

/-- The same name cannot serve as both input sorts of Extract in one context. -/
theorem extract_same_atom_not_sorted (free : FreeTypeContext) (name : String) :
    ¬ HasType wmCoreLanguageDef free []
      (encodeWM (.extract (.state name) (.query name))) (sortType .evidence) := by
  rw [encodeWM_hasType_iff _ rfl]
  rintro ⟨stateTyped, queryTyped⟩
  exact (by decide : (some (TypeExpr.base "State")) ≠ some (.base "Query"))
    (stateTyped.symm.trans queryTyped)

def specimenFree : FreeTypeContext :=
  fun name => if name = "world" then some (.base "State")
    else if name = "question" then some (.base "Query") else none

theorem extract_distinct_atoms_sorted :
    HasType wmCoreLanguageDef specimenFree []
      (encodeWM (.extract (.state "world") (.query "question")))
      (sortType .evidence) :=
  (encodeWM_hasType_iff _ rfl _ _).2 (by simp [AtomsTyped, specimenFree, sortType])

#print axioms encodeWM_hasType_iff
#print axioms encodeWM_hasType_iff_bound
#print axioms encodeWM_openPatternWellSorted_iff_bound
#print axioms contextual_reduct_hasType
#print axioms contextual_reduct_openPatternWellSorted
#print axioms extract_same_atom_not_sorted

end Mettapedia.OSLF.Framework.WMCalculusSortedEncoding
