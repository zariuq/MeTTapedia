import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryGeneratorAlignment

/-!
# Counterexample to unrestricted collapsing-pair closure

Reflective parallel canonicalization identifies permutations of a bare hash
bag.  At a genuine collection type, however, the Cost region tree is a
structural collection and its child-first normalizer deliberately preserves
element order.  Thus the generic collapsing-pair premise used by unrestricted
paired recursion is stronger than the exact rho generator theorem requires.

The witness below is fully typed and quote-safe.  It does not refute rho's
base-sort generator invariant: in an admitted rho term, a bare collection is
the parameter of a static `PPar` constructor, so the enclosing static region
must intercept it before structural collection recursion.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

private def permutationAtomType : TypeExpr :=
  .base (costBaseSortName "Name")

private def permutationFree : FreeTypeContext
  | "a" | "b" => some permutationAtomType
  | _ => none

private def permutationLeft : Pattern :=
  .collection .hashBag [.fvar "b", .fvar "a"] none

private def permutationRight : Pattern :=
  .collection .hashBag [.fvar "a", .fvar "b"] none

private theorem permutationLeft_wellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      permutationFree [] (.collection .hashBag permutationAtomType)
      permutationLeft := by
  refine ⟨⟨?_, by decide, by simp [permutationLeft,
    isObjectPattern, isObjectPatternList], by
      simp [ScopeSafeAt, permutationLeft, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]⟩, ?_⟩
  · exact .collection (.cons (.fvar (by simp [permutationFree]))
      (.cons (.fvar (by simp [permutationFree]))
        (.nil [] permutationAtomType)))
  · intro presentation membership
    simp [permutationLeft, binderSafeAt, binderSafeListAt]

private theorem permutationRight_wellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      permutationFree [] (.collection .hashBag permutationAtomType)
      permutationRight := by
  refine ⟨⟨?_, by decide, by simp [permutationRight,
    isObjectPattern, isObjectPatternList], by
      simp [ScopeSafeAt, permutationRight, Pattern.isWellScopedAt,
        Pattern.isWellScopedListAt]⟩, ?_⟩
  · exact .collection (.cons (.fvar (by simp [permutationFree]))
      (.cons (.fvar (by simp [permutationFree]))
        (.nil [] permutationAtomType)))
  · intro presentation membership
    simp [permutationRight, binderSafeAt, binderSafeListAt]

private theorem permutation_canonical :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl)
        permutationLeft =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl)
        permutationRight := by
  apply canonicalize_parallel_permutation
  exact List.Perm.swap (Pattern.fvar "a") (Pattern.fvar "b") []

private theorem normalize_fvar_tree
    {available outer : List TypeExpr} {name : String}
    (tree : CostRegionTree rhoCIGSLT permutationFree available outer (.fvar name)
      permutationAtomType) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .fvar name := by
  let view := tree.structuralRootView tree.rootIsStatic_eq_false_of_fvar
  cases view with
  | fvar lookup => simp [CostRegionTree.normalize]

private theorem normalize_permutationLeft_tree
    {available outer : List TypeExpr}
    (tree : CostRegionTree rhoCIGSLT permutationFree available outer permutationLeft
      (.collection .hashBag permutationAtomType)) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        permutationLeft := by
  let view := tree.structuralRootView
    tree.rootIsStatic_eq_false_of_collection_type
  cases view with
  | collection children =>
      cases children with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail with
              | nil =>
                  simp only [CostRegionTree.normalize,
                    CostRegionElementTrees.normalize, permutationLeft]
                  rw [normalize_fvar_tree first, normalize_fvar_tree second]

private theorem normalize_permutationRight_tree
    {available outer : List TypeExpr}
    (tree : CostRegionTree rhoCIGSLT permutationFree available outer permutationRight
      (.collection .hashBag permutationAtomType)) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        permutationRight := by
  let view := tree.structuralRootView
    tree.rootIsStatic_eq_false_of_collection_type
  cases view with
  | collection children =>
      cases children with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail with
              | nil =>
                  simp only [CostRegionTree.normalize,
                    CostRegionElementTrees.normalize, permutationRight]
                  rw [normalize_fvar_tree first, normalize_fvar_tree second]

/-- Unrestricted collapsing-pair closure is false even for rho's base-colour
reflective declaration.  The obstruction lives at a collection type, outside
the base-sort root of `CostOpenGeneratorTreeAlignable`. -/
theorem not_rhoBaseCostCanonicalCollapsingPairClosed :
    ¬ CostCanonicalCollapsingPairClosed rhoCIGSLT
      rhoHereditaryNormalizationKernel
      (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl) := by
  intro closed
  obtain ⟨paired⟩ := closed (outer := []) permutationLeft_wellSorted
    permutationRight_wellSorted permutation_canonical
    (Or.inl (Or.inr ⟨[.fvar "b", .fvar "a"], rfl⟩))
  have normalized := paired.alignment.normalize_pattern_eq
  rw [normalize_permutationLeft_tree paired.leftTree,
    normalize_permutationRight_tree paired.rightTree] at normalized
  exact (by decide : permutationLeft ≠ permutationRight) normalized

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
