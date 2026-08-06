import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain

/-!
# Root classification for rho static-to-structural canonical pairs

Canonical equality away from Quote/Drop and bare-parallel collapse preserves
the compact root.  Since a proof-relevant static rho tree retains the exact
declaration-derived root shape, that aligned case cannot turn it into a
structural tree.  Nor can the structural endpoint itself have a collapsing
root: at a base result fibre every collapsing generated rho root is static.

Thus every genuinely asymmetric static-to-structural canonical pair is
oriented by a collapsing root on the static endpoint.  This is the exact
syntax-level entry point for the semantic-atom terminal.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- If the left rho Cost tree is static and the right tree is structural,
canonical equality must collapse at the left root. -/
theorem rhoCollapsingRoot_of_static_structural_canonical_eq
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (color : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftStatic : left.rootIsStatic = true)
    (rightStructural : right.rootIsStatic = false)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  rcases canonicalize_eq_root_cases declaration canonical with
      leftCollapsing | rightCollapsing | aligned
  · exact leftCollapsing
  · obtain ⟨category, typeEq⟩ :=
      left.type_eq_base_of_rootIsStatic leftStatic
    subst type
    have rightStatic :=
      right.rootIsStatic_of_costStatic_collapsingRoot rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        (by exact List.mem_cons_self) rightCollapsing
    rw [rightStatic] at rightStructural
    contradiction
  · have rightStatic :=
      left.rootIsStatic_of_canonicalRootAligned right leftStatic aligned
    rw [rightStatic] at rightStructural
    contradiction

/-- Symmetric orientation of
`rhoCollapsingRoot_of_static_structural_canonical_eq`. -/
theorem rhoCollapsingRoot_of_structural_static_canonical_eq
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (color : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftStructural : left.rootIsStatic = false)
    (rightStatic : right.rootIsStatic = true)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern :=
  rhoCollapsingRoot_of_static_structural_canonical_eq color right left
    rightStatic leftStructural canonical.symm

/-- Exhaustive proof-relevant root classification of a canonical rho pair
for which at least one endpoint has a static-root shape.  The asymmetric
constructors retain the oriented collapsing-root proof needed by the
semantic-atom terminals. -/
inductive RhoCanonicalStaticPairRootCase
    (color : CostStaticColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type) : Type where
  | bothStatic
      (leftStatic : left.rootIsStatic = true)
      (rightStatic : right.rootIsStatic = true) :
      RhoCanonicalStaticPairRootCase color left right
  | leftCollapsing
      (leftStatic : left.rootIsStatic = true)
      (rightStructural : right.rootIsStatic = false)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern) :
      RhoCanonicalStaticPairRootCase color left right
  | rightCollapsing
      (leftStructural : left.rootIsStatic = false)
      (rightStatic : right.rootIsStatic = true)
      (collapsing : CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
      RhoCanonicalStaticPairRootCase color left right

/-- Canonical equality plus one declaration-derived static shape constructs
the exhaustive root case directly.  No pair-normalization bridge is assumed
or hidden in this classifier. -/
theorem nonempty_rhoCanonicalStaticPairRootCase
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (color : CostStaticColor)
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (staticShape : CostStaticRootShape rhoCIGSLT leftPattern type ∨
      CostStaticRootShape rhoCIGSLT rightPattern type) :
    Nonempty (RhoCanonicalStaticPairRootCase color left right) := by
  rcases staticShape with leftShape | rightShape
  · have leftStatic := leftShape.rootIsStatic left
    cases rightStatic : right.rootIsStatic with
    | false =>
        exact ⟨.leftCollapsing leftStatic rightStatic
          (rhoCollapsingRoot_of_static_structural_canonical_eq color left
            right leftStatic rightStatic canonical)⟩
    | true => exact ⟨.bothStatic leftStatic rightStatic⟩
  · have rightStatic := rightShape.rootIsStatic right
    cases leftStatic : left.rootIsStatic with
    | false =>
        exact ⟨.rightCollapsing leftStatic rightStatic
          (rhoCollapsingRoot_of_structural_static_canonical_eq color left
            right leftStatic rightStatic canonical)⟩
    | true => exact ⟨.bothStatic leftStatic rightStatic⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
