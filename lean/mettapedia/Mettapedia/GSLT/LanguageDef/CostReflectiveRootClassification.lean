import Mettapedia.GSLT.LanguageDef.CostStaticRootInversion
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalRootDichotomy

/-!
# Typed classification of collapsing reflective Cost roots

Reflective canonicalization has two root-changing cases: a quote application
and a bare parallel collection.  This file connects that syntax-level
dichotomy to the proof-relevant Cost tree.

The connection uses only existing validated data.  Reflective retyping puts
the authored quote constructor in the hereditary fragment, so either static
colour maps it to a constructor with that exact static role.  A bare
collection at a base result fibre can only be represented by a static tree.
Thus no planner-order convention enters the classification.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open WellSorted
open ReflectionExtension

/-- Every collapsing root of a generated static reflective declaration is a
genuine static root in the checked Cost tree.  The returned colour is the
colour retained by the tree; bare-collection overlap is intentionally not
resolved by an enumeration preference. -/
theorem CostRegionTree.nonempty_staticRootColor_of_costStatic_collapsingRoot
    (source : CIGSLT) (declarationColor : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.reflection.1.presentations)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {pattern : Pattern} {category : String}
    (tree : CostRegionTree source targetFree available outer pattern
      (.base category))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl source declarationColor declaration)
      pattern) :
    Nonempty (Σ color,
      CostRegionTree.StaticRootColor source targetFree tree color) := by
  rcases collapsing with ⟨arguments, patternEq⟩ | ⟨elements, patternEq⟩
  · have wrapped :=
      (source.reflectivePresentationsRetypable declaration membership
        ).constructorLabels_mem_wrapped.1
    have staticDecoded :=
      decodeDeclaredCostStaticConstructor_symbols_of_wrappedLabel source
        declarationColor declaration.quoteConstructor wrapped
    obtain ⟨constructor, decoded, role⟩ :=
      exists_declaredCostConstructor_of_static_decode source declarationColor
        ((declarationColor.symbols source).constructor
          declaration.quoteConstructor)
        declaration.quoteConstructor staticDecoded
    have mappedQuote :
        (costStaticReflectivePresentationDecl source declarationColor
          declaration).quoteConstructor =
          (declarationColor.symbols source).constructor
            declaration.quoteConstructor := by
      simp [costStaticReflectivePresentationDecl_eq_map,
        mapReflectivePresentation]
    rw [mappedQuote] at patternEq
    rcases tree.nonempty_staticRootColor_of_static_application_of_eq patternEq
        rfl declarationColor constructor decoded role with ⟨root⟩
    exact ⟨⟨declarationColor, root⟩⟩
  · exact tree.nonempty_staticRootColor_of_base_collection_of_eq patternEq rfl

/-- Boolean reflection of the typed classification: a collapsing generated
reflective root cannot elaborate as a structural frame. -/
theorem CostRegionTree.rootIsStatic_of_costStatic_collapsingRoot
    (source : CIGSLT) (declarationColor : CostStaticColor)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.reflection.1.presentations)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {pattern : Pattern} {category : String}
    (tree : CostRegionTree source targetFree available outer pattern
      (.base category))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl source declarationColor declaration)
      pattern) :
    tree.rootIsStatic = true := by
  rcases tree.nonempty_staticRootColor_of_costStatic_collapsingRoot source
      declarationColor declaration membership collapsing with
    ⟨⟨color, root⟩⟩
  exact root.rootIsStatic

end Mettapedia.GSLT.LanguageDef
