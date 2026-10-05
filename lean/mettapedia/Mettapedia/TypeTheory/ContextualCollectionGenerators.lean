import Mettapedia.TypeTheory.ContextualBoundedCollection

/-!
# Collection diagrams from retained future receipts

A generator retains actual small enumerations of all future small-map
fibres and a nonempty small covering-receipt family for every code. Its free
contextual arrows form the parameter object. The collected object retains
the witness's source future, terminal arrow and original receipt code.
Transport acts on that terminal arrow, so the chosen receipts need not be
a natural section.

The covering square, quasi-pullback comparison and coherent small fibres
are constructed without selecting any generator. Only parameter-cover
surjectivity requires generators to exist. An optional external-host
comparison populates these generators from pointwise proof-smallness and
covering existence; this module does not use that comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCollectionGenerators

open CategoryTheory ContextualWitnessCover ContextualImageFactorization ContextualCoherentSmallMaps
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {X : D ⥤ Type v} {A : D ⥤ Type w} {Y : D ⥤ Type z}
variable (operation : NaturalHom X A) (cover : NaturalHom Y X)

structure Generator where
  point : D
  parameter : A.obj point
  enumerations : ContextualEnumerationCovers.FutureEnumerations operation point parameter
  witnessCarrier : ∀ (future : Future.Objects point), (enumerations future).Carrier → Type u
  witness : ∀ (future : Future.Objects point) (code : (enumerations future).Carrier),
    witnessCarrier future code → Fibre cover future.1 ((enumerations future).value code).val
  inhabited : ∀ (future : Future.Objects point) (code : (enumerations future).Carrier),
    Nonempty (witnessCarrier future code)

def prefixEnumeration (generator : Generator operation cover) {point : D}
    (arrival : generator.point ⟶ point) (future : Future.Objects point) :
    Enumeration.{u, v} (Fibre operation future.1 (A.map future.2 (A.map arrival generator.parameter))) where
  Carrier := (generator.enumerations ⟨future.1, arrival ≫ future.2⟩).Carrier
  value code := ⟨(generator.enumerations ⟨future.1, arrival ≫ future.2⟩).value code |>.val,
    ((generator.enumerations ⟨future.1, arrival ≫ future.2⟩).value code).property.trans
      (A.map_comp_apply arrival future.2 generator.parameter)⟩
  covered receipt := by
    obtain ⟨code, represents⟩ := (generator.enumerations ⟨future.1, arrival ≫ future.2⟩).covered
      (⟨receipt.val, receipt.property.trans (A.map_comp_apply arrival future.2 generator.parameter).symm⟩ :
        Fibre operation future.1 (A.map (arrival ≫ future.2) generator.parameter))
    refine ⟨code, ?_⟩
    apply Subtype.ext
    exact congrArg (fun receipt : Fibre operation future.1
      (A.map (arrival ≫ future.2) generator.parameter) => receipt.val) represents

/-- The complete future bounds restrict by actual arrow prefixing. This
construction retains both receipt codes and their full cover readings. -/
def restrictGenerator (generator : Generator operation cover) {point : D}
    (arrival : generator.point ⟶ point) : Generator operation cover where
  point := point
  parameter := A.map arrival generator.parameter
  enumerations := prefixEnumeration operation cover generator arrival
  witnessCarrier future code := generator.witnessCarrier ⟨future.1, arrival ≫ future.2⟩ code
  witness future code := generator.witness ⟨future.1, arrival ≫ future.2⟩ code
  inhabited future code := generator.inhabited ⟨future.1, arrival ≫ future.2⟩ code

abbrev ParameterAt (point : D) := Σ generator : Generator operation cover, generator.point ⟶ point

def parameters : D ⥤ Type (max (u + 1) v w z) where
  obj := ParameterAt operation cover
  map step := TypeCat.ofHom fun receipt => ⟨receipt.1, receipt.2 ≫ step⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.comp_id receipt.2)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg (Sigma.mk receipt.1) (Category.assoc receipt.2 earlier later).symm

def parameterMap : NaturalHom (parameters operation cover) A where
  app _ receipt := A.map receipt.2 receipt.1.parameter
  naturality step receipt := (A.map_comp_apply receipt.2 step receipt.1.parameter).symm

theorem parameterMap_cover
    (existence : ∀ point (parameter : A.obj point),
      ∃ generator : Generator operation cover, generator.point = point ∧
        HEq generator.parameter parameter) : Cover (parameterMap operation cover) := by
  intro point parameter
  obtain ⟨generator, same, values⟩ := existence point parameter
  cases same
  exact ⟨⟨generator, 𝟙 generator.point⟩,
    (A.map_id_apply generator.point generator.parameter).trans (eq_of_heq values)⟩

theorem parameterMap_cover_iff : Cover (parameterMap operation cover) ↔
    ∀ point (parameter : A.obj point),
      ∃ generator : Generator operation cover, generator.point = point ∧ HEq generator.parameter parameter := by
  constructor
  · intro covered point parameter
    obtain ⟨⟨generator, arrival⟩, same⟩ := covered point parameter
    exact ⟨restrictGenerator operation cover generator arrival, rfl, heq_of_eq same⟩
  · exact parameterMap_cover operation cover

abbrev CollectedAt (point : D) :=
  Σ generator : Generator operation cover,
    Σ future : Future.Objects generator.point,
      (future.1 ⟶ point) ×
        (Σ code : (generator.enumerations future).Carrier, generator.witnessCarrier future code)

def collected : D ⥤ Type (max (u + 1) v w z) where
  obj := CollectedAt operation cover
  map step := TypeCat.ofHom fun receipt => ⟨receipt.1, receipt.2.1, receipt.2.2.1 ≫ step, receipt.2.2.2⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨generator, future, tail, code⟩
    exact congrArg (fun arrow => (⟨generator, future, arrow, code⟩ : CollectedAt operation cover _))
      (Category.comp_id tail)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨generator, future, tail, code⟩
    exact congrArg (fun arrow => (⟨generator, future, arrow, code⟩ : CollectedAt operation cover _))
      (Category.assoc tail earlier later).symm

def collectedMap : NaturalHom (collected operation cover) (parameters operation cover) where
  app _ receipt := ⟨receipt.1, receipt.2.1.2 ≫ receipt.2.2.1⟩
  naturality _ receipt := congrArg (Sigma.mk receipt.1) (Category.assoc _ _ _)

def top : NaturalHom (collected operation cover) Y where
  app _ receipt := Y.map receipt.2.2.1
    (receipt.1.witness receipt.2.1 receipt.2.2.2.1 receipt.2.2.2.2).val
  naturality step receipt := (Y.map_comp_apply receipt.2.2.1 step
    (receipt.1.witness receipt.2.1 receipt.2.2.2.1 receipt.2.2.2.2).val).symm

theorem collection_square : (top operation cover).comp (cover.comp operation) =
    (collectedMap operation cover).comp (parameterMap operation cover) := by
  apply NaturalHom.ext
  rintro point ⟨generator, future, tail, code, witness⟩
  change operation.app point (cover.app point (Y.map tail (generator.witness future code witness).val)) =
    A.map (future.2 ≫ tail) generator.parameter
  exact (congrArg (operation.app point) ((cover.naturality tail _).symm.trans
    (congrArg (X.map tail) (generator.witness future code witness).property))).trans
    ((operation.naturality tail _).symm.trans
      ((congrArg (A.map tail) ((generator.enumerations future).value code).property).trans
        (A.map_comp_apply future.2 tail generator.parameter).symm))

abbrev Branch (point : D) (parameter : ParameterAt operation cover point) : Type u :=
  Σ future : Future.Objects parameter.1.point,
    Σ _tail : {arrow : future.1 ⟶ point // future.2 ≫ arrow = parameter.2},
      (Σ code : (parameter.1.enumerations future).Carrier, parameter.1.witnessCarrier future code)

def branchDecoder (point : D) (parameter : ParameterAt operation cover point) :
    Branch operation cover point parameter ≃ Fibre (collectedMap operation cover) point parameter where
  toFun branch := ⟨⟨parameter.1, branch.1, branch.2.1.val, branch.2.2⟩,
    congrArg (Sigma.mk parameter.1) branch.2.1.property⟩
  invFun := by
    rcases parameter with ⟨generator, arrival⟩
    rintro ⟨⟨other, future, tail, code⟩, same⟩
    change (⟨other, future.2 ≫ tail⟩ : ParameterAt operation cover point) = ⟨generator, arrival⟩ at same
    have generators : other = generator := congrArg Sigma.fst same
    subst other
    exact ⟨future, ⟨tail, eq_of_heq (Sigma.mk.inj_iff.mp same).2⟩, code⟩
  left_inv := by
    rcases parameter with ⟨generator, arrival⟩
    rintro ⟨future, ⟨tail, follows⟩, code⟩
    rfl
  right_inv := by
    rcases parameter with ⟨generator, arrival⟩
    rintro ⟨⟨other, future, tail, code⟩, same⟩
    change (⟨other, future.2 ≫ tail⟩ : ParameterAt operation cover point) = ⟨generator, arrival⟩ at same
    have generators : other = generator := congrArg Sigma.fst same
    subst other
    rfl

def collectedData : Data (collectedMap operation cover) :=
  ofEquivs (collectedMap operation cover) (fun point => Branch operation cover point.1 point.2)
    (fun point => branchDecoder operation cover point.1 point.2)

theorem collectedMap_small : SmallFibres (collectedMap operation cover) :=
  (collectedData operation cover).smallFibres

def comparison : NaturalHom (collected operation cover)
    (pullback operation (parameterMap operation cover)) :=
  pullbackPair operation (parameterMap operation cover)
    ((top operation cover).comp cover) (collectedMap operation cover) (collection_square operation cover)

theorem comparison_cover : Cover (comparison operation cover) := by
  intro point receipt
  rcases receipt with ⟨⟨argument, ⟨generator, arrival⟩⟩, same⟩
  let future : Future.Objects generator.point := ⟨point, arrival⟩
  obtain ⟨code, represents⟩ := (generator.enumerations future).covered
    (⟨argument, same⟩ : Fibre operation point (A.map arrival generator.parameter))
  obtain ⟨witness⟩ := generator.inhabited future code
  refine ⟨⟨generator, future, 𝟙 point, code, witness⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change cover.app point (Y.map (𝟙 point) (generator.witness future code witness).val) = argument
    exact (congrArg (cover.app point) (Y.map_id_apply point _)).trans
      ((generator.witness future code witness).property.trans (congrArg Subtype.val represents))
  · exact congrArg (Sigma.mk generator) (Category.comp_id arrival)

theorem full_diagram
    (existence : ∀ point (parameter : A.obj point),
      ∃ generator : Generator operation cover, generator.point = point ∧ HEq generator.parameter parameter) :
    Cover (parameterMap operation cover) ∧ Cover (comparison operation cover) ∧
      SmallFibres (collectedMap operation cover) ∧
      (top operation cover).comp (cover.comp operation) =
        (collectedMap operation cover).comp (parameterMap operation cover) :=
  ⟨parameterMap_cover operation cover existence, comparison_cover operation cover,
    collectedMap_small operation cover, collection_square operation cover⟩

section CoherentCovers

variable (model : Data operation) (coverModel : Data cover) (covered : Cover cover)

def coherentGenerator (point : D) (parameter : A.obj point) : Generator operation cover where
  point := point
  parameter := parameter
  enumerations := model.futureEnumerations point parameter
  witnessCarrier future code := coverModel.family.obj
    ⟨future.1, ((model.enumeration future.1 (A.map future.2 parameter)).value code).val⟩
  witness future code := coverModel.decoder
    ⟨future.1, ((model.enumeration future.1 (A.map future.2 parameter)).value code).val⟩
  inhabited future code := by
    obtain ⟨witness, represents⟩ := covered future.1
      ((model.enumeration future.1 (A.map future.2 parameter)).value code).val
    exact ⟨(coverModel.decoder _).symm ⟨witness, represents⟩⟩

include model coverModel covered in
theorem coherent_generator_exists : ∀ point (parameter : A.obj point),
    ∃ generator : Generator operation cover, generator.point = point ∧ HEq generator.parameter parameter :=
  fun point parameter => ⟨coherentGenerator operation cover model coverModel covered point parameter, rfl, HEq.rfl⟩

include model coverModel covered in
theorem coherent_collection : Cover (parameterMap operation cover) ∧ Cover (comparison operation cover) ∧
    SmallFibres (collectedMap operation cover) ∧
    (top operation cover).comp (cover.comp operation) =
      (collectedMap operation cover).comp (parameterMap operation cover) :=
  full_diagram operation cover (coherent_generator_exists operation cover model coverModel covered)

end CoherentCovers

section BoundedWitnesses

variable (model : Data operation) (witnesses : X.Elements ⥤ Type u)
variable (reading : NaturalHom (ContextualSmallFamilyUniverse.total witnesses) Y)
variable (total : ContextualBoundedCollection.BoundedTotal cover witnesses reading)

def boundedGenerator (point : D) (parameter : A.obj point) : Generator operation cover where
  point := point
  parameter := parameter
  enumerations := model.futureEnumerations point parameter
  witnessCarrier future code :=
    (ContextualBoundedCollection.goodWitnesses cover witnesses reading).obj
      ⟨future.1, ((model.enumeration future.1 (A.map future.2 parameter)).value code).val⟩
  witness future code witness :=
    ⟨reading.app future.1
      ⟨((model.enumeration future.1 (A.map future.2 parameter)).value code).val, witness.val⟩,
      witness.property⟩
  inhabited future code := by
    obtain ⟨witness, valid⟩ := total future.1
      ((model.enumeration future.1 (A.map future.2 parameter)).value code).val
    exact ⟨⟨witness, valid⟩⟩

include model witnesses reading total in
theorem bounded_generator_exists : ∀ point (parameter : A.obj point),
    ∃ generator : Generator operation cover, generator.point = point ∧ HEq generator.parameter parameter :=
  fun point parameter => ⟨boundedGenerator operation cover model witnesses reading total point parameter, rfl, HEq.rfl⟩

end BoundedWitnesses

end Mettapedia.TypeTheory.ContextualCollectionGenerators
