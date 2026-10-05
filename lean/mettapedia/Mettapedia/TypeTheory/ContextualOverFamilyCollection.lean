import Mettapedia.TypeTheory.ContextualCollectionStrength
import Mettapedia.TypeTheory.ContextualSmallFamilyComprehension

/-!
# Constructive Collection for authored families over wider parameters

An authored map over the same parameter family has an actual small fibre
carrier: the source's native terms at the target parameter satisfying its
image equation. The parameter square and equality elimination construct
both inverse fibre maps. Thus these covers have coherent small data even
when their total source and target objects inhabit a wider universe.

These concrete decoders instantiate the full contextual Collection square.
Only surjectivity of the authored cover is propositional. No original
parameter representative or witness is selected. Arbitrary wider covers
outside this interpreted family class retain the separate Collection
strength obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualOverFamilyCollection

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps ContextualSmallFamilyUniverse

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (source target : base.Elements ⥤ Type u)
variable (operation : NaturalHom (total source) (total target))
variable (over : operation.comp (projection target) = projection source)

include over in
theorem source_parameter (point : D) (parameter : base.obj point) (term : source.obj ⟨point, parameter⟩) :
    (operation.app point ⟨parameter, term⟩).1 = parameter :=
  congrArg (fun map : NaturalHom (total source) base => map.app point ⟨parameter, term⟩) over

/-- A literal native source term is retained; the wider parameter is supplied
by the target value and is not encoded or recovered from material labels. -/
def Receipt (point : (total target).Elements) : Type u :=
  {term : source.obj ⟨point.1, point.2.1⟩ // operation.app point.1 ⟨point.2.1, term⟩ = point.2}

def fibreForward (point : (total target).Elements) (receipt : Receipt source target operation point) :
    Fibre operation point.1 point.2 := ⟨⟨point.2.1, receipt.val⟩, receipt.property⟩

def fibreBackward (point : (total target).Elements) (receipt : Fibre operation point.1 point.2) :
    Receipt source target operation point := by
  rcases point with ⟨point, parameter, term⟩
  rcases receipt with ⟨⟨originalParameter, originalTerm⟩, same⟩
  have parameterLaw : originalParameter = parameter :=
    (source_parameter source target operation over point originalParameter originalTerm).symm.trans
      (congrArg Sigma.fst same)
  cases parameterLaw
  exact ⟨originalTerm, same⟩

theorem fibreBackward_forward (point : (total target).Elements) (receipt : Receipt source target operation point) :
    fibreBackward source target operation over point (fibreForward source target operation point receipt) = receipt := by
  rcases point with ⟨point, parameter, term⟩
  rcases receipt with ⟨receipt, same⟩
  rfl

theorem fibreForward_backward (point : (total target).Elements) (receipt : Fibre operation point.1 point.2) :
    fibreForward source target operation point (fibreBackward source target operation over point receipt) = receipt := by
  rcases point with ⟨point, parameter, term⟩
  rcases receipt with ⟨⟨originalParameter, originalTerm⟩, same⟩
  have parameterLaw : originalParameter = parameter :=
    (source_parameter source target operation over point originalParameter originalTerm).symm.trans
      (congrArg Sigma.fst same)
  cases parameterLaw
  exact Subtype.ext rfl

/-- The inverses follow from the actual parameter square. Pointwise
surjectivity and a selected inverse are not input fields. -/
def fibreEquiv (point : (total target).Elements) :
    Receipt source target operation point ≃ Fibre operation point.1 point.2 where
  toFun := fibreForward source target operation point
  invFun := fibreBackward source target operation over point
  left_inv := fibreBackward_forward source target operation over point
  right_inv := fibreForward_backward source target operation over point

def data : Data operation :=
  ofEquivs operation (Receipt source target operation) (fibreEquiv source target operation over)

theorem data_restrict_source {first second : (total target).Elements} (step : first ⟶ second)
    (receipt : (data source target operation over).family.obj first) :
    ((data source target operation over).decoder second
      ((data source target operation over).family.map step receipt)).val =
      (total source).map step.1 (((data source target operation over).decoder first receipt).val) :=
  (congrArg Subtype.val ((data source target operation over).naturality step receipt)).symm

include over in
theorem smallFibres : SmallFibres operation := (data source target operation over).smallFibres

def futureEnumerations (point : D) (value : (total target).obj point) :
    ContextualEnumerationCovers.FutureEnumerations operation point value :=
  (data source target operation over).futureEnumerations point value

variable (covered : Cover operation)

/-- Every cover between these authored displayed families constructs an
actual Collection diagram over the arbitrary wider base. -/
def generator (point : D) (parameter : base.obj point) :
    ContextualCollectionGenerators.Generator (projection target) operation :=
  ContextualCollectionGenerators.coherentGenerator (projection target) operation
    (projectionData target) (data source target operation over) covered point parameter

include over covered in
theorem full_collection :
    Cover (ContextualCollectionGenerators.parameterMap (projection target) operation) ∧
      Cover (ContextualCollectionGenerators.comparison (projection target) operation) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap (projection target) operation) ∧
      (ContextualCollectionGenerators.top (projection target) operation).comp (operation.comp (projection target)) =
        (ContextualCollectionGenerators.collectedMap (projection target) operation).comp
          (ContextualCollectionGenerators.parameterMap (projection target) operation) :=
  ContextualCollectionGenerators.coherent_collection (projection target) operation
    (projectionData target) (data source target operation over) covered

theorem generator_parameter (point : D) (parameter : base.obj point) :
    (generator source target operation over covered point parameter).parameter = parameter := rfl

end Mettapedia.TypeTheory.ContextualOverFamilyCollection
