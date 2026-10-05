import Mettapedia.TypeTheory.ContextualCollectionGenerators

/-!
# External host-Choice Collection comparison

Host Choice supplies actual enumerations of every future proof-small
fibre, and one covering receipt for every enumeration code. These populate
the already constructed Collection generators. Their contextual maps,
small collected fibres and covering comparison are inherited from the
constructive construction.

This proves the full covering-square statement for the precise
pointwise-surjective cover and fixed-bound receipt-small map predicates,
without asserting that selected witnesses form natural sections. The
dependency on host Choice is explicit. No internal native Choice law,
unrestricted original-bound material presentation, or foundational default
is selected by this comparison module.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualCollection

open CategoryTheory ContextualWitnessCover ContextualImageFactorization ContextualCoherentSmallMaps
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {X : D ⥤ Type v} {A : D ⥤ Type w} {Y : D ⥤ Type z}
variable (operation : NaturalHom X A) (cover : NaturalHom Y X)

noncomputable def futureEnumerations (small : SmallFibres operation) (point : D)
    (parameter : A.obj point) : ContextualEnumerationCovers.FutureEnumerations operation point parameter :=
  fun future => Classical.choice (small future.1 (A.map future.2 parameter))

noncomputable def selectedWitness (covered : Cover cover) (point : D) (argument : X.obj point) :
    Fibre cover point argument :=
  ⟨Classical.choose (covered point argument), Classical.choose_spec (covered point argument)⟩

noncomputable def generator (small : SmallFibres operation) (covered : Cover cover)
    (point : D) (parameter : A.obj point) : ContextualCollectionGenerators.Generator operation cover where
  point := point
  parameter := parameter
  enumerations := futureEnumerations operation small point parameter
  witnessCarrier _ _ := PUnit.{u + 1}
  witness future code _ := selectedWitness cover covered future.1
    (((futureEnumerations operation small point parameter) future).value code).val
  inhabited _ _ := ⟨PUnit.unit⟩

theorem generators_exist (small : SmallFibres operation) (covered : Cover cover) :
    ∀ point (parameter : A.obj point),
      ∃ receipt : ContextualCollectionGenerators.Generator operation cover,
        receipt.point = point ∧ HEq receipt.parameter parameter :=
  fun point parameter => ⟨generator operation cover small covered point parameter, rfl, HEq.rfl⟩

theorem parameter_cover (small : SmallFibres operation) (covered : Cover cover) :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) :=
  ContextualCollectionGenerators.parameterMap_cover operation cover
    (generators_exist operation cover small covered)

/-- The actual diagram is built by free source/terminal arrows. Choice is
used to populate its generator object, not to assert the desired square. -/
theorem collection (small : SmallFibres operation) (covered : Cover cover) :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
      Cover (ContextualCollectionGenerators.comparison operation cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
      (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation cover).comp
          (ContextualCollectionGenerators.parameterMap operation cover) :=
  ContextualCollectionGenerators.full_diagram operation cover
    (generators_exist operation cover small covered)

/-- At the common successor ambient bound, both constructed objects remain
in the same type-valued functor category, while the collected fibre codes
are in the original context universe. -/
theorem collection_in_successor_category {X A Y : D ⥤ Type (u + 1)}
    (operation : NaturalHom X A) (cover : NaturalHom Y X)
    (small : SmallFibres operation) (covered : Cover cover) :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
      Cover (ContextualCollectionGenerators.comparison operation cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
      (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation cover).comp
          (ContextualCollectionGenerators.parameterMap operation cover) :=
  collection operation cover small covered

end Mettapedia.TypeTheory.HostChoiceContextualCollection
