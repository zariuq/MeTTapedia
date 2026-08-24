import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey
import Mettapedia.GSLT.LanguageDef.CostRegionTree

/-!
# Replay keys on one Cost elaboration fibre

Compact erasure is constant on a fixed elaboration fibre, whereas retaining
the elaboration itself is an exact replay key.  These are the canonical
negative and positive controls for information retained by Cost elaboration.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.Elaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

universe uValue

/-- Compact erasure restricted to one elaboration fibre. -/
def compactFibreKey {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort) :
    CostOpenElaboration source term →
      ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
        source.costWholeLanguage targetFree targetBound targetSort :=
  fun _ => term

/-- The proof-relevant identity key retains the elaboration itself. -/
def provenanceKey {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort} :
    CostOpenElaboration source term → CostOpenElaboration source term :=
  id

/-- On one fibre, compact erasure supports precisely the constant
observations. -/
theorem compactFibreKey_hasRealization_iff_constant
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort)
    {Value : Type uValue}
    (observation : CostOpenElaboration source term → Value) :
    ReplayKey.HasRealization (compactFibreKey term) observation ↔
      ∃ value : Value, ∀ elaboration, observation elaboration = value := by
  constructor
  · rintro ⟨realization⟩
    exact ⟨realization.run term, fun elaboration =>
      (congrFun realization.agrees elaboration)⟩
  · rintro ⟨value, constant⟩
    exact ⟨{
      run := fun _ => value
      agrees := funext constant
    }⟩

/-- With an inhabited observation codomain, fibre invariance under compact
erasure is likewise equivalent to constancy. -/
theorem compactFibreKey_supports_iff_constant
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort)
    {Value : Type uValue} [Nonempty Value]
    (observation : CostOpenElaboration source term → Value) :
    ReplayKey.Supports (compactFibreKey term) observation ↔
      ∃ value : Value, ∀ elaboration, observation elaboration = value := by
  constructor
  · intro supported
    by_cases inhabited : Nonempty (CostOpenElaboration source term)
    · rcases inhabited with ⟨seed⟩
      exact ⟨observation seed, fun elaboration => supported rfl⟩
    · exact ⟨Classical.choice inferInstance,
        fun elaboration => False.elim (inhabited ⟨elaboration⟩)⟩
  · rintro ⟨value, constant⟩ left right _
    exact (constant left).trans (constant right).symm

/-- The retained provenance key admits exact replay. -/
theorem provenanceKey_isExact
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort} :
    ReplayKey.IsExact (provenanceKey (source := source) (term := term)) :=
  ⟨{ decode := id, recovers := fun _ => rfl }⟩

/-- Every observation on an elaboration fibre is supported by the retained
provenance key. -/
theorem provenanceKey_supports
    {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort}
    {Value : Type uValue}
    (observation : CostOpenElaboration source term → Value) :
    ReplayKey.Supports
      (provenanceKey (source := source) (term := term)) observation :=
  provenanceKey_isExact.supports observation

#print axioms compactFibreKey_hasRealization_iff_constant
#print axioms compactFibreKey_supports_iff_constant
#print axioms provenanceKey_isExact

end Mettapedia.GSLT.LanguageDef.Cost.Elaboration
