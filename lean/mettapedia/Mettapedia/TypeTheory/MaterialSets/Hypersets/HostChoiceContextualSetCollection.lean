import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowers
import Mettapedia.TypeTheory.HostChoiceContextualCollection

/-!
# Internal Collection from the constructed contextual covering diagram

A total stable relation is interpreted over every actual future of its
parameter and input set. Its member domain has an original-bound small
projection. The actual contextual Collection diagram provides a covering
parameter family and a small family of witness rows. Their material values
are assembled by the inverse final structure.

External host Choice populates the diagram's generators. It does not provide
a natural witness function on the original parameter family. Set values stay
at the successor bound; collected witness receipts remain at the original
context bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollection

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory

universe u v
variable {D : Type u} [Category.{u} D]
variable (parameters : D ⥤ Type v)
variable (test : CoveredFuturePowerClassifier.StablePredicate
  (CoveredFuturePowerClassifier.product parameters (CoveredFuturePowerClassifier.product (sets (D := D)) sets)))

def Total (point : D) (parameter : parameters.obj point) (parent : sets.obj point) : Prop :=
  ∀ (target : D) (arrow : point ⟶ target) (child : sets.obj target),
    Member target child (sets.map arrow parent) →
      ∃ witness : sets.obj target,
        test.holds ⟨target, (parameters.map arrow parameter, (child, witness))⟩

theorem total_transport {point target : D} (arrow : point ⟶ target)
    {parameter : parameters.obj point} {parent : sets.obj point}
    (total : Total parameters test point parameter parent) :
    Total parameters test target (parameters.map arrow parameter) (sets.map arrow parent) := by
  intro later tail child belongs
  have parentEq := congrArg (fun map => map parent) (sets.map_comp arrow tail)
  obtain ⟨witness, witnessLaw⟩ := total later (arrow ≫ tail) child
    ((congrArg (Member later child) parentEq).symm ▸ belongs)
  refine ⟨witness, ?_⟩
  have parameterEq := congrArg (fun map => map parameter) (parameters.map_comp arrow tail)
  exact (congrArg (fun value => test.holds ⟨later, (value, (child, witness))⟩) parameterEq) ▸ witnessLaw

def inputs : D ⥤ Type (max v (u+1)) where
  obj point := {value : parameters.obj point × sets.obj point // Total parameters test point value.1 value.2}
  map step := TypeCat.ofHom fun value => ⟨(parameters.map step value.val.1, sets.map step value.val.2),
    total_transport parameters test step value.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact Prod.ext (congrArg (fun map => map value.val.1) (parameters.map_id point))
      (congrArg (fun map => map value.val.2) (sets.map_id point))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact Prod.ext (congrArg (fun map => map value.val.1) (parameters.map_comp earlier later))
      (congrArg (fun map => map value.val.2) (sets.map_comp earlier later))

def memberDomain : D ⥤ Type (max v (u+1)) where
  obj point := {value : (inputs parameters test).obj point × sets.obj point //
    Member point value.2 value.1.val.2}
  map step := TypeCat.ofHom fun value =>
    ⟨((inputs parameters test).map step value.val.1, sets.map step value.val.2),
      member_transport step value.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact Prod.ext (congrArg (fun map => map value.val.1) ((inputs parameters test).map_id point))
      (congrArg (fun map => map value.val.2) (sets.map_id point))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact Prod.ext (congrArg (fun map => map value.val.1) ((inputs parameters test).map_comp earlier later))
      (congrArg (fun map => map value.val.2) (sets.map_comp earlier later))

def memberProjection : NaturalHom (memberDomain parameters test) (inputs parameters test) where
  app _ value := value.val.1
  naturality _ _ := rfl

theorem memberProjection_small : ContextualImageFactorization.SmallFibres (memberProjection parameters test) := by
  intro point input
  obtain ⟨enumeration⟩ := (unfold.app point input.val.2).property
  refine ⟨{
    Carrier := enumeration.Carrier ⟨point, 𝟙 point⟩
    value := fun code => ⟨⟨(input, enumeration.value ⟨point, 𝟙 point⟩ code),
      (enumeration.covered ⟨point, 𝟙 point⟩ _).mpr ⟨code, rfl⟩⟩, rfl⟩
    covered := ?_ }⟩
  intro receipt
  have parentEq : receipt.val.val.1.val.2 = input.val.2 :=
    congrArg (fun value => value.val.2) receipt.property
  have belongs : Member point receipt.val.val.2 input.val.2 :=
    (congrArg (Member point receipt.val.val.2) parentEq) ▸ receipt.val.property
  obtain ⟨code, same⟩ := (enumeration.covered ⟨point, 𝟙 point⟩ _).mp belongs
  refine ⟨code, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext receipt.property.symm same

def witnesses : D ⥤ Type (max v (u+1)) where
  obj point := {value : (memberDomain parameters test).obj point × sets.obj point //
    test.holds ⟨point, (value.1.val.1.val.1, (value.1.val.2, value.2))⟩}
  map step := TypeCat.ofHom fun value =>
    ⟨((memberDomain parameters test).map step value.val.1, sets.map step value.val.2),
      test.closed (CategoryOfElements.homMk _ _ step rfl) value.property⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact Prod.ext (congrArg (fun map => map value.val.1) ((memberDomain parameters test).map_id point))
      (congrArg (fun map => map value.val.2) (sets.map_id point))
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact Prod.ext (congrArg (fun map => map value.val.1) ((memberDomain parameters test).map_comp earlier later))
      (congrArg (fun map => map value.val.2) (sets.map_comp earlier later))

def witnessCover : NaturalHom (witnesses parameters test) (memberDomain parameters test) where
  app _ value := value.val.1
  naturality _ _ := rfl

def witnessValue : NaturalHom (witnesses parameters test) (sets (D := D)) where
  app _ value := value.val.2
  naturality _ _ := rfl

theorem witnessCover_covered : ContextualCoherentSmallMaps.Cover (witnessCover parameters test) := by
  intro point value
  have total := value.val.1.property
  obtain ⟨witness, law⟩ := total point (𝟙 point) value.val.2
    ((congrArg (fun map => Member point value.val.2 (map value.val.1.val.2)) (sets.map_id point)).symm ▸
      value.property)
  have parameterId := congrArg (fun map => map value.val.1.val.1) (parameters.map_id point)
  refine ⟨⟨(value, witness), ?_⟩, rfl⟩
  exact (congrArg (fun parameter => test.holds ⟨point, (parameter, (value.val.2, witness))⟩)
    parameterId) ▸ law

abbrev collectingParameters := ContextualCollectionGenerators.parameters
  (memberProjection parameters test) (witnessCover parameters test)

abbrev collectedRows := ContextualCollectionGenerators.collected
  (memberProjection parameters test) (witnessCover parameters test)

abbrev collectedProjection := ContextualCollectionGenerators.collectedMap
  (memberProjection parameters test) (witnessCover parameters test)

abbrev parameterMap := ContextualCollectionGenerators.parameterMap
  (memberProjection parameters test) (witnessCover parameters test)

abbrev rowWitness := ContextualCollectionGenerators.top
  (memberProjection parameters test) (witnessCover parameters test)

def collectedValue : NaturalHom (collectedRows parameters test) (sets (D := D)) :=
  (rowWitness parameters test).comp (witnessValue parameters test)

theorem collectingParameter_cover : ContextualCoherentSmallMaps.Cover (parameterMap parameters test) :=
  HostChoiceContextualCollection.parameter_cover (memberProjection parameters test) (witnessCover parameters test)
    (memberProjection_small parameters test) (witnessCover_covered parameters test)

theorem row_square : (rowWitness parameters test).comp
    ((witnessCover parameters test).comp (memberProjection parameters test)) =
      (collectedProjection parameters test).comp (parameterMap parameters test) :=
  ContextualCollectionGenerators.collection_square _ _

def rowPredicate : CoveredFuturePowerClassifier.StablePredicate
    (CoveredFuturePowerClassifier.product (collectingParameters parameters test) (sets (D := D))) where
  holds value := ∃ row : (collectedRows parameters test).obj value.1,
    (collectedProjection parameters test).app value.1 row = value.2.1 ∧
      (collectedValue parameters test).app value.1 row = value.2.2
  closed {first second} move available := by
    obtain ⟨row, parameterEq, valueEq⟩ := available
    refine ⟨(collectedRows parameters test).map move.1 row, ?_, ?_⟩
    · exact ((collectedProjection parameters test).naturality move.1 row).symm.trans
        ((congrArg ((collectingParameters parameters test).map move.1) parameterEq).trans
          (congrArg Prod.fst move.2))
    · exact ((collectedValue parameters test).naturality move.1 row).symm.trans
        ((congrArg (sets.map move.1) valueEq).trans (congrArg Prod.snd move.2))

def rowReceipts (point : D) (input : (collectingParameters parameters test).obj point) :
    ContextualImageFactorization.Enumeration.{u, max v (u+1)}
      (ContextualImageFactorization.Fibre (collectedProjection parameters test) point input) :=
  (ContextualCollectionGenerators.collectedData (memberProjection parameters test)
    (witnessCover parameters test)).enumeration point input

def rowEnumeration (point : D) (input : (collectingParameters parameters test).obj point) :
    CoveredFuturePowerClassifier.RelationEnumeration (collectingParameters parameters test) sets
      (rowPredicate parameters test) point input where
  Carrier future := (rowReceipts parameters test future.1
    ((collectingParameters parameters test).map future.2 input)).Carrier
  value future code := (collectedValue parameters test).app future.1
    ((rowReceipts parameters test future.1
      ((collectingParameters parameters test).map future.2 input)).value code).val
  covered future child := by
    constructor
    · rintro ⟨row, parameterEq, valueEq⟩
      let receipt : ContextualImageFactorization.Fibre (collectedProjection parameters test) future.1
          ((collectingParameters parameters test).map future.2 input) := ⟨row, parameterEq⟩
      obtain ⟨code, same⟩ := (rowReceipts parameters test future.1
        ((collectingParameters parameters test).map future.2 input)).covered receipt
      exact ⟨code, (congrArg (fun decoded : ContextualImageFactorization.Fibre
          (collectedProjection parameters test) future.1
          ((collectingParameters parameters test).map future.2 input) =>
        (collectedValue parameters test).app future.1 decoded.val) same).trans valueEq⟩
    · rintro ⟨code, valueEq⟩
      let receipt := (rowReceipts parameters test future.1
        ((collectingParameters parameters test).map future.2 input)).value code
      exact ⟨receipt.val, receipt.property, valueEq⟩

def rowRelation : CoveredFuturePowerClassifier.CoveredRelation
    (collectingParameters parameters test) (sets (D := D)) where
  predicate := rowPredicate parameters test
  covered point input := ⟨rowEnumeration parameters test point input⟩

noncomputable def collectingSet : NaturalHom (collectingParameters parameters test) (sets (D := D)) :=
  (CoveredFuturePowerClassifier.classifier (collectingParameters parameters test) sets
    (rowRelation parameters test)).comp assemble

theorem collectingSet_members (point : D) (input : (collectingParameters parameters test).obj point)
    (child : sets.obj point) :
    Member point child ((collectingSet parameters test).app point input) ↔
      ∃ row : (collectedRows parameters test).obj point,
        (collectedProjection parameters test).app point row = input ∧
          (collectedValue parameters test).app point row = child := by
  change (unfold.app point (assemble.app point
    ((CoveredFuturePowerClassifier.classifier (collectingParameters parameters test) sets
      (rowRelation parameters test)).app point input))).val.holds _ ↔ _
  have returns := unfold_assemble point
    ((CoveredFuturePowerClassifier.classifier (collectingParameters parameters test) sets
      (rowRelation parameters test)).app point input)
  have result := CoveredFuturePowerClassifier.classifier_future
    (collectingParameters parameters test) sets (rowRelation parameters test) point input
      (current sets point child)
  change ((CoveredFuturePowerClassifier.classifier (collectingParameters parameters test) sets
    (rowRelation parameters test)).app point input).val.holds (current sets point child) ↔
      (rowRelation parameters test).predicate.holds
        ⟨point, ((collectingParameters parameters test).map (𝟙 point) input, child)⟩ at result
  rw [(collectingParameters parameters test).map_id] at result
  exact (iff_of_eq (congrArg (fun power : Power sets point => power.val.holds (current sets point child)) returns)).trans result

theorem collectingSet_covers (point : D) (input : (collectingParameters parameters test).obj point)
    (child : sets.obj point)
    (belongs : Member point child ((parameterMap parameters test).app point input).val.2) :
    ∃ witness : sets.obj point,
      Member point witness ((collectingSet parameters test).app point input) ∧
        test.holds ⟨point, (((parameterMap parameters test).app point input).val.1, (child, witness))⟩ := by
  let original : (memberDomain parameters test).obj point :=
    ⟨((parameterMap parameters test).app point input, child), belongs⟩
  let receipt : (ContextualImageFactorization.pullback (memberProjection parameters test)
      (parameterMap parameters test)).obj point := ⟨(original, input), rfl⟩
  obtain ⟨row, same⟩ := ContextualCollectionGenerators.comparison_cover
    (memberProjection parameters test) (witnessCover parameters test) point receipt
  have sourceEq : (witnessCover parameters test).app point ((rowWitness parameters test).app point row) = original :=
    congrArg (fun value => value.val.1) same
  have parameterEq : (collectedProjection parameters test).app point row = input :=
    congrArg (fun value => value.val.2) same
  refine ⟨(collectedValue parameters test).app point row,
    (collectingSet_members parameters test point input _).mpr ⟨row, parameterEq, rfl⟩, ?_⟩
  exact (congrArg (fun value : (memberDomain parameters test).obj point =>
    test.holds ⟨point, (value.val.1.val.1, (value.val.2, (collectedValue parameters test).app point row))⟩)
      sourceEq) ▸ ((rowWitness parameters test).app point row).property

theorem collectingSet_contains (point : D) (input : (collectingParameters parameters test).obj point)
    (witness : sets.obj point)
    (belongs : Member point witness ((collectingSet parameters test).app point input)) :
    ∃ child : sets.obj point,
      Member point child ((parameterMap parameters test).app point input).val.2 ∧
        test.holds ⟨point, (((parameterMap parameters test).app point input).val.1, (child, witness))⟩ := by
  obtain ⟨row, parameterEq, valueEq⟩ := (collectingSet_members parameters test point input witness).mp belongs
  let original := (witnessCover parameters test).app point ((rowWitness parameters test).app point row)
  have inputEq : original.val.1 = (parameterMap parameters test).app point input :=
    (congrArg (fun operation : NaturalHom (collectedRows parameters test) (inputs parameters test) =>
      operation.app point row) (row_square parameters test)).trans
        (congrArg ((parameterMap parameters test).app point) parameterEq)
  refine ⟨original.val.2, ?_, ?_⟩
  · exact (congrArg (fun value : (inputs parameters test).obj point =>
      Member point original.val.2 value.val.2) inputEq) ▸ original.property
  · have originalLaw := ((rowWitness parameters test).app point row).property
    exact (congrArg₂ (fun parameter value => test.holds ⟨point, (parameter, (original.val.2, value))⟩)
      (congrArg (fun value : (inputs parameters test).obj point => value.val.1) inputEq) valueEq) ▸ originalLaw

theorem collectingSet_strong (point : D) (input : (collectingParameters parameters test).obj point) :
    (∀ child : sets.obj point,
      Member point child ((parameterMap parameters test).app point input).val.2 →
        ∃ witness : sets.obj point,
          Member point witness ((collectingSet parameters test).app point input) ∧
            test.holds ⟨point, (((parameterMap parameters test).app point input).val.1, (child, witness))⟩) ∧
    (∀ witness : sets.obj point,
      Member point witness ((collectingSet parameters test).app point input) →
        ∃ child : sets.obj point,
          Member point child ((parameterMap parameters test).app point input).val.2 ∧
            test.holds ⟨point, (((parameterMap parameters test).app point input).val.1, (child, witness))⟩) :=
  ⟨collectingSet_covers parameters test point input, collectingSet_contains parameters test point input⟩

/-- The chosen covering receipt is eliminated only inside this existential
statement. Every actual future uses the collector's proved natural transport. -/
theorem internal_strongCollection (point : D) (parameter : parameters.obj point) (parent : sets.obj point)
    (total : Total parameters test point parameter parent) :
    ∃ collection : sets.obj point,
      ∀ (target : D) (arrow : point ⟶ target),
        (∀ child : sets.obj target, Member target child (sets.map arrow parent) →
          ∃ witness : sets.obj target, Member target witness (sets.map arrow collection) ∧
            test.holds ⟨target, (parameters.map arrow parameter, (child, witness))⟩) ∧
        (∀ witness : sets.obj target, Member target witness (sets.map arrow collection) →
          ∃ child : sets.obj target, Member target child (sets.map arrow parent) ∧
            test.holds ⟨target, (parameters.map arrow parameter, (child, witness))⟩) := by
  let original : (inputs parameters test).obj point := ⟨(parameter, parent), total⟩
  obtain ⟨input, same⟩ := collectingParameter_cover parameters test point original
  refine ⟨(collectingSet parameters test).app point input, ?_⟩
  intro target arrow
  have clauses := collectingSet_strong parameters test target ((collectingParameters parameters test).map arrow input)
  have inputEq : (parameterMap parameters test).app target ((collectingParameters parameters test).map arrow input) =
      (inputs parameters test).map arrow original :=
    ((parameterMap parameters test).naturality arrow input).symm.trans
      (congrArg ((inputs parameters test).map arrow) same)
  rw [inputEq] at clauses
  rw [← (collectingSet parameters test).naturality arrow input] at clauses
  exact clauses

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollection
