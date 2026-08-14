import Mettapedia.GSLT.LanguageDef.CostGeneratorHereditaryAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratedOccurrenceAbsorption

/-!
# Exact rho generator alignment from local static closures

Every generated rho Cost edge retains one proof-relevant authored occurrence
and one exact base-or-wrapped reflective declaration that absorbs it.  The
reachable paired elaborator handles all rigid constructors, binders, and
recursive children while proving that a genuine structural collection fibre
cannot occur.  Consequently the repaired universal alignment reduces to one
declaration-local obligation for each colour: selected static-region closure.

This module performs that assembly without choosing a second occurrence,
erasing provenance, or assuming the final executor equality.  Concrete rho
restoration theorems must still discharge that local closure premise.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Local static and collapsing-root closures are sufficient for alignment.

This older boundary theorem is retained because the collection-type
counterexample targets its collapsing premise.  That premise is false for rho
on arbitrary types, so the repaired route below does not use this theorem. -/
theorem rhoCostOpenGeneratorTreeAlignable_of_pairClosures
    (staticClosed : ∀ color,
      CostCanonicalStaticPairClosed rhoCIGSLT
        rhoHereditaryNormalizationKernel
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl))
    (collapsingClosed : ∀ color,
      CostCanonicalCollapsingPairClosed rhoCIGSLT
        rhoHereditaryNormalizationKernel
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)) :
    CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel := by
  intro targetFree targetBound targetSort left right generator
  obtain ⟨occurrence⟩ := nonempty_rhoCostTypedGeneratorOccurrence generator
  let absorption := occurrence.absorption
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    absorption.color rhoReflectivePresentation.toReflectivePresentationDecl
  have representatives :
      canonicalize declaration left.1 = canonicalize declaration right.1 := by
    dsimp only [declaration]
    rw [← absorption.declaration_eq]
    exact absorption.contextualRepresentatives
  obtain ⟨paired⟩ := CostCanonicalPairElaboration.nonempty_of_canonical
    declaration (staticClosed absorption.color)
      (collapsingClosed absorption.color) left.2 right.2 representatives
  exact ⟨
    { occurrence := occurrence.witness
      erasesTo := occurrence.erasesTo
      leftElaboration := ⟨paired.leftTree⟩
      rightElaboration := ⟨paired.rightTree⟩
      treeAlignment := paired.alignment }⟩

/-- Static restoration closure in both generated rho colours is sufficient
for hereditary alignment of every typed generated Cost edge.

The recursive type-domain proof eliminates the false unrestricted
collapsing-pair obligation: every root-changing canonical form reachable from
a rho language sort is base-typed and closes through the ordinary static
restoration theorem. -/
theorem rhoCostOpenGeneratorTreeAlignable_of_staticClosures
    (staticClosed : ∀ color,
      CostCanonicalStaticPairClosedInDomain rhoCanonicalRecursiveTypeDomain
        rhoHereditaryNormalizationKernel
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)) :
    CostOpenGeneratorTreeAlignable rhoCIGSLT
      rhoHereditaryNormalizationKernel := by
  intro targetFree targetBound targetSort left right generator
  obtain ⟨occurrence⟩ := nonempty_rhoCostTypedGeneratorOccurrence generator
  let absorption := occurrence.absorption
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    absorption.color rhoReflectivePresentation.toReflectivePresentationDecl
  have representatives :
      canonicalize declaration left.1 = canonicalize declaration right.1 := by
    dsimp only [declaration]
    rw [← absorption.declaration_eq]
    exact absorption.contextualRepresentatives
  obtain ⟨paired⟩ :=
    CostCanonicalPairElaboration.nonempty_of_canonical_inDomain
      (outer := []) rhoCanonicalRecursiveTypeDomain absorption.color
      rhoReflectivePresentation.toReflectivePresentationDecl
      (by exact List.mem_cons_self) (staticClosed absorption.color)
      left.2 right.2 representatives rfl
  exact ⟨
    { occurrence := occurrence.witness
      erasesTo := occurrence.erasesTo
      leftElaboration := ⟨paired.leftTree⟩
      rightElaboration := ⟨paired.rightTree⟩
      treeAlignment := paired.alignment }⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
