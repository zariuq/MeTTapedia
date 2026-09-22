import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceReplacement

/-!
# Open-pattern admission under typed occurrence replacement

The type judgment is only one component of the native open-pattern carrier.
The existing one-hole zipper also preserves the remaining admission checks
when the replacement has the same binder-metadata, object-form, and
scope-at-every-depth profile as the selected subterm.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Pattern

private theorem canonicalList_append (before after : List Pattern) :
    hasCanonicalBinderMetadataList (before ++ after) =
      (hasCanonicalBinderMetadataList before &&
        hasCanonicalBinderMetadataList after) := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
      simp [hasCanonicalBinderMetadataList, ih, Bool.and_assoc]

private theorem objectList_append (before after : List Pattern) :
    isObjectPatternList (before ++ after) =
      (isObjectPatternList before && isObjectPatternList after) := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
      simp [isObjectPatternList, ih, Bool.and_assoc]

private theorem scopedList_append (depth : Nat) (before after : List Pattern) :
    isWellScopedListAt depth (before ++ after) =
      (isWellScopedListAt depth before &&
        isWellScopedListAt depth after) := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
      simp [isWellScopedListAt, ih, Bool.and_assoc]

/-- Equality of the three non-typing admission checks, with scope compared at
every depth so the profile remains valid after crossing binders. -/
def AdmissionProfileEquivalent (source target : Pattern) : Prop :=
  hasCanonicalBinderMetadata source = hasCanonicalBinderMetadata target ∧
    isObjectPattern source = isObjectPattern target ∧
    ∀ depth, isWellScopedAt depth source = isWellScopedAt depth target

/-- A one-hole context transports the complete non-typing admission profile.
No authored declaration is needed for this purely syntactic fact. -/
theorem OneHoleContext.admissionProfileEquivalent_fill
    (context : OneHoleContext) {source target : Pattern}
    (profile : AdmissionProfileEquivalent source target) :
    AdmissionProfileEquivalent (context.fill source) (context.fill target) := by
  obtain ⟨canonical, object, scopeEq⟩ := profile
  induction context with
  | hole => exact ⟨canonical, object, scopeEq⟩
  | apply constructor before inner after ih =>
      obtain ⟨innerCanonical, innerObject, innerScoped⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [OneHoleContext.fill, hasCanonicalBinderMetadata,
          canonicalList_append, hasCanonicalBinderMetadataList,
          innerCanonical]
      · simp [OneHoleContext.fill, isObjectPattern,
          objectList_append, isObjectPatternList, innerObject]
      · intro depth
        simp [OneHoleContext.fill, isWellScopedAt,
          scopedList_append, isWellScopedListAt, innerScoped depth]
  | lambda binder inner ih =>
      obtain ⟨innerCanonical, innerObject, innerScoped⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [OneHoleContext.fill, hasCanonicalBinderMetadata, innerCanonical]
      · simpa [OneHoleContext.fill, isObjectPattern] using innerObject
      · intro depth
        simpa [OneHoleContext.fill, isWellScopedAt] using innerScoped (depth + 1)
  | multiLambda arity binders inner ih =>
      obtain ⟨innerCanonical, innerObject, innerScoped⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [OneHoleContext.fill, hasCanonicalBinderMetadata, innerCanonical]
      · simpa [OneHoleContext.fill, isObjectPattern] using innerObject
      · intro depth
        simpa [OneHoleContext.fill, isWellScopedAt] using innerScoped (depth + arity)
  | substBody inner replacement ih =>
      obtain ⟨innerCanonical, innerObject, innerScoped⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [OneHoleContext.fill, hasCanonicalBinderMetadata, innerCanonical]
      · simp [OneHoleContext.fill, isObjectPattern]
      · intro depth
        simp [OneHoleContext.fill, isWellScopedAt, innerScoped (depth + 1)]
  | substReplacement body inner ih =>
      obtain ⟨innerCanonical, innerObject, innerScoped⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [OneHoleContext.fill, hasCanonicalBinderMetadata, innerCanonical]
      · simp [OneHoleContext.fill, isObjectPattern]
      · intro depth
        simp [OneHoleContext.fill, isWellScopedAt, innerScoped depth]
  | collection kind before inner after rest ih =>
      obtain ⟨innerCanonical, innerObject, innerScoped⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [OneHoleContext.fill, hasCanonicalBinderMetadata,
          canonicalList_append, hasCanonicalBinderMetadataList,
          innerCanonical]
      · simp [OneHoleContext.fill, isObjectPattern,
          objectList_append, isObjectPatternList, innerObject]
      · intro depth
        simp [OneHoleContext.fill, isWellScopedAt,
          scopedList_append, isWellScopedListAt, innerScoped depth]

/-- Typed occurrence replacement transports the exact native open-pattern
carrier, not merely its `HasType` component. -/
theorem TypedAt.replace_openPatternWellSorted
    {language : LanguageDef} {free : FreeTypeContext}
    {source target : Pattern} {context : OneHoleContext}
    {bound focusBound : List TypeExpr} {ambientType focusType : TypeExpr}
    (selected : TypedAt language free source context bound ambientType
      focusBound focusType)
    (admitted : OpenPatternWellSorted language free bound ambientType
      (context.fill source))
    (compatible : RepresentationCompatible source target)
    (profile : AdmissionProfileEquivalent source target)
    (replacement : HasType language free focusBound target focusType) :
    OpenPatternWellSorted language free bound ambientType
      (context.fill target) := by
  obtain ⟨_, canonical, object, scopeProof⟩ := admitted
  obtain ⟨canonicalEq, objectEq, scopedEq⟩ :=
    OneHoleContext.admissionProfileEquivalent_fill context profile
  have targetScope : ScopeSafeAt bound.length (context.fill target) := by
    unfold ScopeSafeAt at scopeProof ⊢
    rw [← scopedEq bound.length]
    exact scopeProof
  exact ⟨selected.replace compatible replacement,
    canonicalEq.symm ▸ canonical, objectEq.symm ▸ object,
    targetScope⟩

#print axioms OneHoleContext.admissionProfileEquivalent_fill
#print axioms TypedAt.replace_openPatternWellSorted

end Mettapedia.GSLT.LanguageDef.WellSorted
