import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Scope under constructor maps

A constructor map changes no binder and no variable, so a pattern and its image are well scoped, and ground, at the
same depths.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

variable (symbols : LanguageDefSymbolMap)

theorem isWellScopedAt_mapPattern (pattern : Pattern) :
    ∀ depth, (mapPattern symbols pattern).isWellScopedAt depth =
      pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [mapPattern, Pattern.isWellScopedAt]
  | hfvar name => intro depth; simp [mapPattern, Pattern.isWellScopedAt]
  | happly constructor arguments inductionHypothesis =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, Pattern.isWellScopedAt]
      induction arguments with
      | nil => rfl
      | cons argument arguments tailHypothesis =>
          simp only [List.map_cons, Pattern.isWellScopedListAt]
          rw [inductionHypothesis argument (by simp) depth,
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]
  | hlambda binder body inductionHypothesis =>
      intro depth
      simp only [mapPattern, Pattern.isWellScopedAt]
      exact inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      intro depth
      simp only [mapPattern, Pattern.isWellScopedAt]
      exact inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro depth
      simp only [mapPattern, Pattern.isWellScopedAt]
      rw [bodyHypothesis (depth + 1), replacementHypothesis depth]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, Pattern.isWellScopedAt]
      induction elements with
      | nil => rfl
      | cons element elements tailHypothesis =>
          simp only [List.map_cons, Pattern.isWellScopedListAt]
          rw [inductionHypothesis element (by simp) depth,
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]

theorem isGroundAt_mapPattern (pattern : Pattern) :
    ∀ depth, (mapPattern symbols pattern).isGroundAt depth = pattern.isGroundAt depth := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [mapPattern, Pattern.isGroundAt]
  | hfvar name => intro depth; simp [mapPattern, Pattern.isGroundAt]
  | happly constructor arguments inductionHypothesis =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, Pattern.isGroundAt]
      induction arguments with
      | nil => rfl
      | cons argument arguments tailHypothesis =>
          simp only [List.map_cons, Pattern.isGroundListAt]
          rw [inductionHypothesis argument (by simp) depth,
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]
  | hlambda binder body inductionHypothesis =>
      intro depth
      simp only [mapPattern, Pattern.isGroundAt]
      exact inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      intro depth
      simp only [mapPattern, Pattern.isGroundAt]
      exact inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro depth
      simp only [mapPattern, Pattern.isGroundAt]
      rw [bodyHypothesis (depth + 1), replacementHypothesis depth]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro depth
      simp only [mapPattern, mapPatternList_eq_map, Pattern.isGroundAt]
      congr 1
      induction elements with
      | nil => rfl
      | cons element elements tailHypothesis =>
          simp only [List.map_cons, Pattern.isGroundListAt]
          rw [inductionHypothesis element (by simp) depth,
            tailHypothesis (fun item member => inductionHypothesis item (by simp [member]))]

end Mettapedia.GSLT.LanguageDef
