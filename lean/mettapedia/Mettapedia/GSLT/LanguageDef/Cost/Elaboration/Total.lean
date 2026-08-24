import Mettapedia.GSLT.LanguageDef.CostElaborationDisplayed
import Mettapedia.GSLT.LanguageDef.CostElaborationTreeReindexLaws
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# The lawful one-step Cost elaboration total category

`CostElaborationTotal` retains a checked region tree over an arbitrary
continued authority.  This module restricts its base to
`CostElaborationBase`, whose objects carry a selected lawful Cost normalizer
and whose arrows preserve the decomposition decisions needed for exact
reindexing.

The resulting total category keeps proof-relevant elaborations while its
projection exposes the already-defined compact one-step Cost functor.  Its
structural fibre transport gives strongly cocartesian lifts.  No closure under
a second Cost step is asserted.
-/

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A lawful one-step Cost authority together with one checked elaboration in
its exact indexed fibre. -/
structure Cost.Elaboration.Total where
  base : CostElaborationBase
  fiber : CostElaborationFiber base.toLayer.source.toCIGSLT

namespace Cost.Elaboration.Total

/-- The computationally complete, proof-erased decoration of the retained
elaboration. -/
def decoration (object : Cost.Elaboration.Total) :
    CostTreeDecoration object.base.toLayer.source.toCIGSLT :=
  object.fiber.2.decoration

/-- A total arrow is a conservative Cost one-step arrow that transports the
complete retained decoration exactly. -/
structure Morphism (source target : Cost.Elaboration.Total) where
  base : source.base ⟶ target.base
  decoration_natural :
    source.decoration.map base.underlying.underlying.underlying =
      target.decoration

namespace Morphism

/-- Total arrows are determined by their base arrow; decoration naturality is
a proposition. -/
@[ext]
theorem ext {source target : Cost.Elaboration.Total}
    {first second : Morphism source target}
    (base : first.base = second.base) : first = second := by
  cases first
  cases second
  cases base
  rfl

/-- Identity transports a retained decoration without changing it. -/
def id (source : Cost.Elaboration.Total) : Morphism source source where
  base := CostElaborationBase.Morphism.id source.base
  decoration_natural := CostTreeDecoration.map_id _ _

/-- Composition follows strict composition of complete decoration maps. -/
def comp {first second third : Cost.Elaboration.Total}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  base := CostElaborationBase.Morphism.comp left.base right.base
  decoration_natural := by
    calc
      first.decoration.map
          (CIGSLT.Morphism.comp left.base.underlying.underlying.underlying
            right.base.underlying.underlying.underlying) =
          (first.decoration.map
            left.base.underlying.underlying.underlying).map
              right.base.underlying.underlying.underlying :=
        CostTreeDecoration.map_comp
          left.base.underlying.underlying.underlying
          right.base.underlying.underlying.underlying first.decoration
      _ = second.decoration.map
            right.base.underlying.underlying.underlying :=
        congrArg
          (CostTreeDecoration.map
            right.base.underlying.underlying.underlying)
          left.decoration_natural
      _ = third.decoration := right.decoration_natural

end Morphism

/-- The total category of checked elaborations over the conservative lawful
Cost one-step base. -/
instance : CategoryTheory.Category Cost.Elaboration.Total where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    exact CategoryTheory.Category.id_comp morphism.base
  comp_id morphism := by
    apply Morphism.ext
    exact CategoryTheory.Category.comp_id morphism.base
  assoc first second third := by
    apply Morphism.ext
    exact CategoryTheory.Category.assoc first.base second.base third.base

/-- Forget the retained fibre while keeping the selected normalizer, Cost
laws, and conservative arrow. -/
def projection :
    CategoryTheory.Functor Cost.Elaboration.Total CostElaborationBase where
  obj object := object.base
  map morphism := morphism.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Compact one-step Cost is the projection of the lawful total category to
its base followed by the existing one-step Cost functor. -/
def compact :
    CategoryTheory.Functor Cost.Elaboration.Total OrderedCIGSLT :=
  projection.comp CostElaborationBase.compact

/-- Forget the selected normalizer and its laws while retaining the same
checked elaboration and exact decoration transport. -/
def forgetToStructural :
    CategoryTheory.Functor Cost.Elaboration.Total CostElaborationTotal where
  obj object :=
    { base := object.base.toLayer.source.toCIGSLT
      fiber := object.fiber }
  map morphism :=
    { base := morphism.base.underlying.underlying.underlying
      decoration_natural := morphism.decoration_natural }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Push one retained Cost fibre along a conservative lawful cost layer arrow.
This is structural transport of the existing tree, not recompilation in the
target authority. -/
def transportFiber {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    CostElaborationFiber target.toLayer.source.toCIGSLT :=
  mapCostElaborationFiber
    morphism.underlying.underlying.underlying
    (Cost.Layer.Hom.CompactMapLaws.preservesGeneratedReflectiveScope
      morphism.underlying.compactMapLaws)
    morphism.reindexLaws fiber

/-- The transported total object over the codomain of a conservative cost layer
arrow. -/
def transportObject {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    Cost.Elaboration.Total :=
  ⟨target, transportFiber morphism fiber⟩

/-- Every conservative lawful cost layer arrow has a chosen displayed lift from
each retained source fibre.  Its factorization property is proved below. -/
def transportLift {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    Morphism ⟨source, fiber⟩ (transportObject morphism fiber) where
  base := morphism
  decoration_natural :=
    (mapCostElaborationFiber_decoration
      morphism.underlying.underlying.underlying
      (Cost.Layer.Hom.CompactMapLaws.preservesGeneratedReflectiveScope
        morphism.underlying.compactMapLaws)
      morphism.reindexLaws fiber).symm

/-- The chosen structural lift lies over exactly the requested base arrow. -/
@[simp]
theorem projection_map_transportLift
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    projection.map (transportLift morphism fiber) = morphism :=
  rfl

/-- Factor an arbitrary total arrow through the chosen structural transport
whenever its base arrow factors through the selected Cost one-step arrow.

This is the existence half of the cocartesian universal property.  The proof
uses strict composition of complete decorations; it does not compare or erase
the proof terms retained by the two fibres. -/
def transportFactor
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT)
    (destination : Cost.Elaboration.Total)
    (composite : Morphism ⟨source, fiber⟩ destination)
    (next : target ⟶ destination.base)
    (baseFactorization : CostElaborationBase.Morphism.comp morphism next =
      composite.base) :
    Morphism (transportObject morphism fiber) destination where
  base := next
  decoration_natural := by
    have underlyingFactorization :
        CIGSLT.Morphism.comp
            morphism.underlying.underlying.underlying
            next.underlying.underlying.underlying =
          composite.base.underlying.underlying.underlying :=
      congrArg
        (fun base => base.underlying.underlying.underlying)
        baseFactorization
    have transportedDecoration :
        (transportObject morphism fiber).decoration =
          fiber.2.decoration.map
            morphism.underlying.underlying.underlying := by
      simpa [transportObject, transportFiber, decoration] using
        (mapCostElaborationFiber_decoration
          morphism.underlying.underlying.underlying
          (Cost.Layer.Hom.CompactMapLaws.preservesGeneratedReflectiveScope
            morphism.underlying.compactMapLaws)
          morphism.reindexLaws fiber)
    calc
      (transportObject morphism fiber).decoration.map
          next.underlying.underlying.underlying =
          (fiber.2.decoration.map
            morphism.underlying.underlying.underlying).map
              next.underlying.underlying.underlying := by
        exact congrArg
          (fun current => current.map
            next.underlying.underlying.underlying)
          transportedDecoration
      _ = fiber.2.decoration.map
          (CIGSLT.Morphism.comp
            morphism.underlying.underlying.underlying
            next.underlying.underlying.underlying) :=
        (CostTreeDecoration.map_comp
          morphism.underlying.underlying.underlying
          next.underlying.underlying.underlying fiber.2.decoration).symm
      _ = fiber.2.decoration.map
          composite.base.underlying.underlying.underlying :=
        congrArg (fun current => fiber.2.decoration.map current)
          underlyingFactorization
      _ = destination.decoration := composite.decoration_natural

/-- The chosen transport followed by its factor is the original total arrow.
This is equality of total arrows, not merely equality after projection. -/
theorem transportLift_comp_transportFactor
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT)
    (destination : Cost.Elaboration.Total)
    (composite : Morphism ⟨source, fiber⟩ destination)
    (next : target ⟶ destination.base)
    (baseFactorization : CostElaborationBase.Morphism.comp morphism next =
      composite.base) :
    Morphism.comp (transportLift morphism fiber)
        (transportFactor morphism fiber destination composite next
          baseFactorization) =
      composite := by
  apply Morphism.ext
  exact baseFactorization

/-- The factor through a chosen structural transport is unique over its
specified base arrow.  Together with `transportLift_comp_transportFactor`,
this is the full cocartesian-style factorization law for the chosen lift. -/
theorem transportFactor_unique
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT)
    (destination : Cost.Elaboration.Total)
    (composite : Morphism ⟨source, fiber⟩ destination)
    (next : target ⟶ destination.base)
    (baseFactorization : CostElaborationBase.Morphism.comp morphism next =
      composite.base)
    (candidate : Morphism (transportObject morphism fiber) destination)
    (candidateBase : candidate.base = next) :
    candidate = transportFactor morphism fiber destination composite next
      baseFactorization := by
  apply Morphism.ext
  exact candidateBase

/-- Structural reindexing is the strongly cocartesian lift of a conservative
lawful Cost one-step arrow.  This packages the factorization and uniqueness
theorems above in Mathlib's standard fibre-category interface. -/
instance transportLift_isStronglyCocartesian
    {source target : CostElaborationBase}
    (morphism : source ⟶ target)
    (fiber : CostElaborationFiber source.toLayer.source.toCIGSLT) :
    projection.IsStronglyCocartesian morphism
      (transportLift morphism fiber) := by
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · let lift := transportLift morphism fiber
    have mapped : projection.IsHomLift (projection.map lift) lift :=
      CategoryTheory.IsHomLift.map projection lift
    have projected : projection.map lift = morphism :=
      projection_map_transportLift morphism fiber
    exact Eq.mp
      (congrArg (fun base => projection.IsHomLift base lift) projected) mapped
  · intro destination next composite compositeLift
    have baseFactorization :
        CostElaborationBase.Morphism.comp morphism next = composite.base := by
      change CostElaborationBase.Morphism.comp morphism next =
        projection.map composite
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift
        _ _ _ _ projection (⟨source, fiber⟩ : Cost.Elaboration.Total)
        destination (CostElaborationBase.Morphism.comp morphism next)
        composite compositeLift
    let factor := @transportFactor source target morphism fiber destination
      composite next baseFactorization
    have factorLift : projection.IsHomLift next factor := by
      have mapped : projection.IsHomLift (projection.map factor) factor :=
        CategoryTheory.IsHomLift.map projection factor
      have projected : projection.map factor = next := rfl
      exact Eq.mp
        (congrArg (fun base => projection.IsHomLift base factor) projected)
        mapped
    use factor
    refine ⟨⟨factorLift,
      transportLift_comp_transportFactor morphism fiber destination composite
        next baseFactorization⟩, ?_⟩
    intro candidate properties
    have candidateBase : candidate.base = next := by
      change projection.map candidate = next
      exact (@CategoryTheory.IsHomLift.eq_of_isHomLift
        _ _ _ _ projection (transportObject morphism fiber) destination next
        candidate properties.1).symm
    exact transportFactor_unique morphism fiber destination composite next
      baseFactorization candidate candidateBase

/-- Equal retained decorations over one lawful base object support the identity
lift, even if their proof terms differ. -/
def identityLiftOfDecorationEq
    (base : CostElaborationBase)
    (sourceFiber targetFiber :
      CostElaborationFiber base.toLayer.source.toCIGSLT)
    (equalDecoration : sourceFiber.2.decoration =
      targetFiber.2.decoration) :
    Morphism ⟨base, sourceFiber⟩ ⟨base, targetFiber⟩ where
  base := CostElaborationBase.Morphism.id base
  decoration_natural := by
    change sourceFiber.2.decoration.map
        (CIGSLT.Morphism.id base.toLayer.source.toCIGSLT) =
      targetFiber.2.decoration
    exact (CostTreeDecoration.map_id _ _).trans equalDecoration

/-- Negative canary: an identity base arrow cannot identify two distinct
computational decorations. -/
theorem noIdentityLiftOfDecorationNe
    (base : CostElaborationBase)
    (sourceFiber targetFiber :
      CostElaborationFiber base.toLayer.source.toCIGSLT)
    (differentDecoration : sourceFiber.2.decoration ≠
      targetFiber.2.decoration) :
    ¬ ∃ morphism : Morphism ⟨base, sourceFiber⟩ ⟨base, targetFiber⟩,
      morphism.base = CostElaborationBase.Morphism.id base := by
  rintro ⟨morphism, baseIdentity⟩
  have natural := morphism.decoration_natural
  rw [baseIdentity] at natural
  change sourceFiber.2.decoration.map
      (CIGSLT.Morphism.id base.toLayer.source.toCIGSLT) =
    targetFiber.2.decoration at natural
  rw [CostTreeDecoration.map_id] at natural
  exact differentDecoration natural

end Cost.Elaboration.Total

end Mettapedia.GSLT.LanguageDef
