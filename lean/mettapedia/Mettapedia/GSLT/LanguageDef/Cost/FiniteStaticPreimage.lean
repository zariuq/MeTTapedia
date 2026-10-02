import Mettapedia.GSLT.LanguageDef.Cost.FiniteDeclarationInventory

/-!
# Authored static preimages for finite Cost profiles

The existing finite declaration inventory determines the exact source row of
any generated static constructor. Parameter representation and transported
collection units remain part of the certificate. The constructed preimage
uses the actual nonprincipal inventory; principal continuation retyping is
kept outside static regions. This is the declaration prerequisite for
migrating the existing retained planner, not another region compiler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax StructuralMorphism
namespace ContinuationDecorationProfile
variable {theory : IGSLT} {cut : InteractionCutPresentation theory}

/-- The complete static row image, including algebra references in the same
constructor namespace. It records no normalization or closure assumption. -/
structure StaticConstructorPreimage (profile : ContinuationDecorationProfile cut)
    (color : CostStaticColor) (constructor : profile.DeclaredCostConstructor) where
  sourceConstructor : DeclaredConstructor theory.presentation.presentation
  wrapped : sourceConstructor ∈ profile.constructorClosure
  labelMap : (profile.materializeDeclaredCostConstructor constructor).label =
    (color.symbolsOf theory).constructor sourceConstructor.1.label
  categoryMap : (profile.materializeDeclaredCostConstructor constructor).category =
    (color.symbolsOf theory).sort sourceConstructor.1.category
  parametersMap : (profile.materializeDeclaredCostConstructor constructor).params =
    sourceConstructor.1.params.map (mapTermParam (color.symbolsOf theory))
  algebraMap : (profile.materializeDeclaredCostConstructor constructor).algebra? =
    sourceConstructor.1.algebra?.map
      (StructuralMorphism.mapCollectionAlgebra (color.symbolsOf theory).constructor)

/-- Authored label uniqueness makes the complete preimage certificate unique. -/
@[ext] theorem StaticConstructorPreimage.ext
    {profile : ContinuationDecorationProfile cut} {color : CostStaticColor}
    {constructor : profile.DeclaredCostConstructor}
    (left right : profile.StaticConstructorPreimage color constructor) : left = right := by
  have same : left.sourceConstructor = right.sourceConstructor := by
    apply ContinuationRetypingPlan.authoredConstructorLabel_injective
      theory.presentation.presentation
    exact CostStaticColor.symbolsOf_constructor_injective theory color
      (left.labelMap.symm.trans right.labelMap)
  cases left
  cases right
  cases same
  rfl

instance {profile : ContinuationDecorationProfile cut} {color : CostStaticColor}
    {constructor : profile.DeclaredCostConstructor} :
    Subsingleton (profile.StaticConstructorPreimage color constructor) :=
  ⟨StaticConstructorPreimage.ext⟩

/-- The exact nonprincipal inventory constructs every selected static
preimage. Additional continuation slots remain on principal boundary rows. -/
def staticConstructorPreimage
    (programAdditional : List (ContinuationDecorationSlot cut.program))
    (environmentAdditional : List (ContinuationDecorationSlot cut.environment))
    (color : CostStaticColor)
    (constructor : (withNonprincipalInventory programAdditional environmentAdditional).DeclaredCostConstructor)
    (role : (withNonprincipalInventory programAdditional environmentAdditional).declaredCostConstructorRole
      constructor = .static color) :
    (withNonprincipalInventory programAdditional environmentAdditional).StaticConstructorPreimage
      color constructor := by
  rcases constructor with ⟨generated, declared⟩
  cases generated with
  | base authored =>
    cases color with
    | base =>
      refine ⟨authored,
        (declaredCostConstructorRole_base_static_iff programAdditional environmentAdditional authored).mp role,
        rfl, rfl, ?_, rfl⟩
      exact static_base_params programAdditional environmentAdditional authored role
    | wrapped =>
      simp only [declaredCostConstructorRole] at role
      split at role <;> cases role
  | wrapped authored =>
    cases color with
    | base => cases role
    | wrapped =>
      refine ⟨authored, declared, rfl, ?_, ?_, rfl⟩
      · simp [materializeDeclaredCostConstructor, costWrappedConstructor,
          CostStaticColor.symbolsOf, costWrappedStaticSymbols]
      · simp [materializeDeclaredCostConstructor, costWrappedConstructor,
          CostStaticColor.symbolsOf]
  | apparatus kind => cases role

/-- Bare collection representation is determined by the parameter profile;
its omitted surface constructor label introduces no second row authority. -/
theorem StaticConstructorPreimage.usesBareCollection_iff
    {profile : ContinuationDecorationProfile cut} {color : CostStaticColor}
    {constructor : profile.DeclaredCostConstructor}
    (preimage : profile.StaticConstructorPreimage color constructor) :
    WellSorted.UsesBareCollection (profile.materializeDeclaredCostConstructor constructor) ↔
      WellSorted.UsesBareCollection preimage.sourceConstructor.1 := by
  have same : WellSorted.UsesBareCollection (profile.materializeDeclaredCostConstructor constructor) ↔
      WellSorted.UsesBareCollection (mapGrammarRule (color.symbolsOf theory)
        preimage.sourceConstructor.1) := by
    simp only [WellSorted.UsesBareCollection, preimage.parametersMap, mapGrammarRule]
  exact same.trans (WellSorted.usesBareCollection_mapGrammarRule_iff _ _)

end ContinuationDecorationProfile
end Mettapedia.GSLT.LanguageDef
