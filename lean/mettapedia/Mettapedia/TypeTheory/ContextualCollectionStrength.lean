import Mettapedia.TypeTheory.ContextualCollectionGenerators

/-!
# Collection, small witness covers, and selected witnesses

The one-parameter test of a covering Collection square is equivalent to a
small multivalued cover of all requested witnesses. The construction keeps
every receipt in that cover. A selected witness for each original index is
a stronger input, and supplies such a square by a separate construction.

For contextual maps with originally small sources the literal fibre types
give coherent small data without selection. These data instantiate the
constructed contextual Collection diagram over arbitrary wider parameters.
This result concerns its stated cover and size classes; it is not a
full-power finality assertion for the originally small family category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCollectionStrength

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps

universe u v w

/-- A small set of witnesses covers every requested original index. -/
def SmallWitnessCollection : Prop :=
  ∀ (I : Type u) (W : I → Type (max u v)), (∀ index, Nonempty (W index)) →
    ∃ (Receipt : Type u) (index : Receipt → I) (_witness : ∀ receipt, W (index receipt)),
      Function.Surjective index

/-- The input data select a witness at every original index. -/
def WitnessSelection : Prop :=
  ∀ (I : Type u) (W : I → Type (max u v)), (∀ index, Nonempty (W index)) →
    Nonempty (∀ index, W index)

/-- A small collecting image of a surjection is not an inverse to it. -/
def SmallCollectingImage {I : Type u} {Y : Type v} (read : Y → I) : Prop :=
  ∃ (Receipt : Type u) (value : Receipt → Y), Function.Surjective (read ∘ value)

/-- The type-valued Collection principle tests every cover of an originally
small index type, while retaining a possibly wider witness type. -/
def TypeCollection : Prop :=
  ∀ (I : Type u) (Y : Type (max u v)) (read : Y → I), Function.Surjective read →
    SmallCollectingImage read

theorem typeCollection_iff_smallWitnessCollection :
    TypeCollection.{u, v} ↔ SmallWitnessCollection.{u, v} := by
  constructor
  · intro collection I W inhabited
    let read : (Σ index, W index) → I := Sigma.fst
    have onto : Function.Surjective read := by
      intro index
      obtain ⟨witness⟩ := inhabited index
      exact ⟨⟨index, witness⟩, rfl⟩
    obtain ⟨Receipt, value, covered⟩ := collection I (Σ index, W index) read onto
    exact ⟨Receipt, fun receipt => (value receipt).1, fun receipt => (value receipt).2, covered⟩
  · intro collection I Y read covered
    let W : I → Type (max u v) := fun index => {witness : Y // read witness = index}
    have inhabited : ∀ index, Nonempty (W index) := by
      intro index
      obtain ⟨witness, represents⟩ := covered index
      exact ⟨⟨witness, represents⟩⟩
    obtain ⟨Receipt, index, witness, onto⟩ := collection I W inhabited
    refine ⟨Receipt, fun receipt => (witness receipt).val, ?_⟩
    intro original
    obtain ⟨receipt, represents⟩ := onto original
    exact ⟨receipt, (witness receipt).property.trans represents⟩

/-- Selecting one witness at each original index yields a multivalued
collecting cover. The reverse selection is not part of this theorem. -/
theorem witnessSelection_implies_smallWitnessCollection
    (selection : WitnessSelection.{u, v}) : SmallWitnessCollection.{u, v} := by
  intro I W inhabited
  obtain ⟨witness⟩ := selection I W inhabited
  exact ⟨I, id, witness, fun index => ⟨index, rfl⟩⟩

/-- A covering Collection square for the map `I → 1`. Its collected map
has actual small fibre covers, and its comparison covers every pair of a
parameter and an original index. -/
structure CollectionSquare {I : Type u} {Y : Type v} (read : Y → I) where
  Parameter : Type (max u v)
  Collected : Type (max u v)
  projection : Collected → Parameter
  row : Collected → Y
  parameterCover : Nonempty Parameter
  small : ∀ parameter, Nonempty (Enumeration.{u, max u v}
    {receipt : Collected // projection receipt = parameter})
  comparisonCover : ∀ parameter index,
    ∃ receipt, projection receipt = parameter ∧ read (row receipt) = index

/-- A square supplies a small collecting image by taking one of its
covered parameters inside this proposition. No parameter is selected as data. -/
theorem collectingImage_of_square {I : Type u} {Y : Type v} (read : Y → I)
    (square : CollectionSquare read) : SmallCollectingImage read := by
  obtain ⟨parameter⟩ := square.parameterCover
  obtain ⟨enumeration⟩ := square.small parameter
  refine ⟨enumeration.Carrier, fun receipt => square.row (enumeration.value receipt).val, ?_⟩
  intro index
  obtain ⟨receipt, over, represents⟩ := square.comparisonCover parameter index
  obtain ⟨code, same⟩ := enumeration.covered ⟨receipt, over⟩
  exact ⟨code, (congrArg
    (fun value : {receipt : square.Collected // square.projection receipt = parameter} =>
      read (square.row value.val)) same).trans represents⟩

/-- A small collecting image constructs the square: its receipt carrier is
raised only to lie in the fixed ambient type universe. -/
def squareOfCollectingImage {I : Type u} {Y : Type v} (read : Y → I)
    (Receipt : Type u) (value : Receipt → Y)
    (covered : Function.Surjective (read ∘ value)) : CollectionSquare read where
  Parameter := PUnit.{max u v + 1}
  Collected := ULift.{v, u} Receipt
  projection _ := PUnit.unit
  row receipt := value receipt.down
  parameterCover := ⟨PUnit.unit⟩
  small parameter := by
    cases parameter
    exact ⟨{
      Carrier := Receipt
      value := fun receipt => ⟨ULift.up receipt, rfl⟩
      covered := fun receipt => ⟨receipt.val.down, Subtype.ext (by cases receipt.val; rfl)⟩ }⟩
  comparisonCover parameter index := by
    cases parameter
    obtain ⟨receipt, represents⟩ := covered index
    exact ⟨ULift.up receipt, rfl, represents⟩

theorem nonempty_square_iff_collectingImage {I : Type u} {Y : Type v} (read : Y → I) :
    Nonempty (CollectionSquare read) ↔ SmallCollectingImage read := by
  constructor
  · rintro ⟨square⟩
    exact collectingImage_of_square read square
  · rintro ⟨Receipt, value, covered⟩
    exact ⟨squareOfCollectingImage read Receipt value covered⟩

/-- Full covering squares already imply multivalued witness Collection in
this one-parameter test. The conclusion contains no original-index selector. -/
theorem coveringSquares_iff_smallWitnessCollection :
    (∀ (I : Type u) (Y : Type (max u v)) (read : Y → I), Function.Surjective read →
      Nonempty (CollectionSquare read)) ↔ SmallWitnessCollection.{u, v} := by
  rw [← typeCollection_iff_smallWitnessCollection]
  constructor
  · intro squares I Y read covered
    exact (nonempty_square_iff_collectingImage read).mp (squares I Y read covered)
  · intro collection I Y read covered
    exact (nonempty_square_iff_collectingImage read).mpr (collection I Y read covered)

/-- Small authored witness carriers construct Collection directly. Every
inhabited small receipt is kept; no witness is selected for each index. -/
def boundedWitnessSquare {I : Type u} {Y : Type v} (read : Y → I)
    (Carrier : I → Type u) (value : (index : I) → Carrier index → Y)
    (correct : ∀ index receipt, read (value index receipt) = index)
    (inhabited : ∀ index, Nonempty (Carrier index)) : CollectionSquare read :=
  squareOfCollectingImage read (Σ index, Carrier index) (fun receipt => value receipt.1 receipt.2)
    (fun index => by
      obtain ⟨receipt⟩ := inhabited index
      exact ⟨⟨index, receipt⟩, correct index receipt⟩)

section Contextual

variable {D : Type u} [Category.{u} D]
variable {X : D ⥤ Type u} {A : D ⥤ Type v}

/-- The literal fibres of an originally small source are uniformly small.
Their actual contextual maps are constructed by the inverse fibre decoder. -/
def originalSmallData (operation : NaturalHom X A) : Data operation :=
  ofEquivs operation (fun point => Fibre operation point.1 point.2)
    (fun _ => Equiv.refl _)

theorem originalSmallData_restrict (operation : NaturalHom X A)
    {first second : A.Elements} (step : first ⟶ second)
    (receipt : Fibre operation first.1 first.2) :
    (originalSmallData operation).family.map step receipt = fibreMap operation step receipt := rfl

/-- With originally small sources on both sides, the complete contextual
Collection diagram is constructed over arbitrary wider parameters. -/
theorem originalSmall_collection {Y : D ⥤ Type u} (operation : NaturalHom X A)
    (cover : NaturalHom Y X) (covered : Cover cover) :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
    Cover (ContextualCollectionGenerators.comparison operation cover) ∧
    SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
    (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
      (ContextualCollectionGenerators.collectedMap operation cover).comp
        (ContextualCollectionGenerators.parameterMap operation cover) :=
  ContextualCollectionGenerators.coherent_collection operation cover
    (originalSmallData operation) (originalSmallData cover) covered

end Contextual

end Mettapedia.TypeTheory.ContextualCollectionStrength
