import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Representation invariants of free-variable closing

Closing changes variable incidence but introduces neither pending
substitutions, collection tails, nor binder display metadata. These laws are
independent of a language's signature and complement typed closing.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem isObjectPatternList_append (first second : List Pattern) :
    isObjectPatternList (first ++ second) =
      (isObjectPatternList first && isObjectPatternList second) := by
  induction first with
  | nil => rfl
  | cons first rest ih => simp only [List.cons_append, isObjectPatternList, ih, Bool.and_assoc]

theorem hasCanonicalBinderMetadataList_append (first second : List Pattern) :
    Pattern.hasCanonicalBinderMetadataList (first ++ second) =
      (Pattern.hasCanonicalBinderMetadataList first &&
        Pattern.hasCanonicalBinderMetadataList second) := by
  induction first with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.cons_append, Pattern.hasCanonicalBinderMetadataList, ih, Bool.and_assoc]

mutual
  theorem isObjectPattern_closeFVar (pattern : Pattern) (depth : Nat) (name : String) :
      isObjectPattern (closeFVar depth name pattern) = isObjectPattern pattern := by
    cases pattern with
    | bvar => simp only [closeFVar]
    | fvar actual => simp only [closeFVar]; split <;> rfl
    | apply constructor arguments =>
        simp only [closeFVar, isObjectPattern,
          isObjectPatternList_map_closeFVar arguments depth name]
    | lambda binder body =>
        simp only [closeFVar, isObjectPattern, isObjectPattern_closeFVar body]
    | multiLambda arity binders body =>
        simp only [closeFVar, isObjectPattern, isObjectPattern_closeFVar body]
    | subst => simp only [closeFVar, isObjectPattern]
    | collection kind elements rest =>
        simp only [closeFVar, isObjectPattern,
          isObjectPatternList_map_closeFVar elements depth name]
  termination_by sizeOf pattern

  theorem isObjectPatternList_map_closeFVar
      (patterns : List Pattern) (depth : Nat) (name : String) :
      isObjectPatternList (patterns.map (closeFVar depth name)) =
        isObjectPatternList patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp only [List.map_cons, isObjectPatternList,
          isObjectPattern_closeFVar pattern depth name,
          isObjectPatternList_map_closeFVar patterns depth name]
  termination_by sizeOf patterns
end

mutual
  theorem hasCanonicalBinderMetadata_closeFVar
      (pattern : Pattern) (depth : Nat) (name : String) :
      (closeFVar depth name pattern).hasCanonicalBinderMetadata =
        pattern.hasCanonicalBinderMetadata := by
    cases pattern with
    | bvar => simp only [closeFVar]
    | fvar actual => simp only [closeFVar]; split <;> rfl
    | apply constructor arguments =>
        simp only [closeFVar, Pattern.hasCanonicalBinderMetadata,
          hasCanonicalBinderMetadataList_map_closeFVar arguments depth name]
    | lambda binder body =>
        simp only [closeFVar, Pattern.hasCanonicalBinderMetadata,
          hasCanonicalBinderMetadata_closeFVar body]
    | multiLambda arity binders body =>
        simp only [closeFVar, Pattern.hasCanonicalBinderMetadata,
          hasCanonicalBinderMetadata_closeFVar body]
    | subst body replacement =>
        simp only [closeFVar, Pattern.hasCanonicalBinderMetadata,
          hasCanonicalBinderMetadata_closeFVar body,
          hasCanonicalBinderMetadata_closeFVar replacement]
    | collection kind elements rest =>
        simp only [closeFVar, Pattern.hasCanonicalBinderMetadata,
          hasCanonicalBinderMetadataList_map_closeFVar elements depth name]
  termination_by sizeOf pattern

  theorem hasCanonicalBinderMetadataList_map_closeFVar
      (patterns : List Pattern) (depth : Nat) (name : String) :
      Pattern.hasCanonicalBinderMetadataList (patterns.map (closeFVar depth name)) =
        Pattern.hasCanonicalBinderMetadataList patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp only [List.map_cons, Pattern.hasCanonicalBinderMetadataList,
          hasCanonicalBinderMetadata_closeFVar pattern depth name,
          hasCanonicalBinderMetadataList_map_closeFVar patterns depth name]
  termination_by sizeOf patterns
end

end Mettapedia.OSLF.MeTTaIL.ClosingRepresentation
