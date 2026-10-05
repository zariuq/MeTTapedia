import Mettapedia.TypeTheory.HostChoiceContextualSmallMapRepresentation
import Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier
import Mettapedia.TypeTheory.HostChoiceContextualCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Extensive

/-!
# Fixed-successor presheaf small-map conditions with external host choice

The objects are arbitrary type-valued presheaves at the fixed successor
bound over a small context category. Small maps have original-bound fibre
receipt covers. Composition, pullback, diagonals, covered quotients and
copairing satisfy the exact small-map conditions. The cover predicate is
identified with categorical epimorphisms, not with natural splittings.

The identity/composition and classification factories priced by external
host choice are kept distinct from the internal presheaf logic. In particular,
the indexed natural number object and its recursion laws are constructed,
while Collection uses the independently constructed covering diagram.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualSmallMapModel

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps
open Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier
open Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFunctor

universe u v w z
variable {D : Type u} [Category.{u} D]

abbrev Ambient (D : Type u) [Category.{u} D] := FamilyObject.{u, u + 1} D

theorem small_identity (A : D ⥤ Type v) : SmallFibres (ContextualSmallMapConstructions.identity A) :=
  ContextualSmallMapConstructions.identity_smallFibres A

theorem small_composition {X : D ⥤ Type v} {A : D ⥤ Type w} {B : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom A B)
    (inner : SmallFibres first) (outer : SmallFibres second) : SmallFibres (first.comp second) :=
  HostChoiceContextualSmallMaps.smallFibres_compose first second inner outer

theorem small_pullback {X : D ⥤ Type v} {A : D ⥤ Type w} {B : D ⥤ Type z}
    (operation : NaturalHom X A) (change : NaturalHom B A) (small : SmallFibres operation) :
    SmallFibres (pullbackSecond operation change) := smallFibres_pullback operation change small

/-- Reflection through a covering parameter change uses a receipt only
inside the fibre's existential proof, not as a global chosen inverse. -/
theorem small_pullback_reflect {X : D ⥤ Type v} {A : D ⥤ Type w} {B : D ⥤ Type z}
    (operation : NaturalHom X A) (change : NaturalHom B A) (covered : Cover change)
    (small : SmallFibres (pullbackSecond operation change)) : SmallFibres operation := by
  intro point value
  obtain ⟨parameter, represents⟩ := covered point value
  obtain ⟨enumeration⟩ := small point parameter
  refine ⟨{ Carrier := enumeration.Carrier
            value := fun code => ⟨(enumeration.value code).val.val.1,
              (enumeration.value code).val.property.trans
                ((congrArg (change.app point) (enumeration.value code).property).trans represents)⟩
            covered := ?_ }⟩
  intro receipt
  let original : Fibre (pullbackSecond operation change) point parameter :=
    ⟨⟨(receipt.val, parameter), receipt.property.trans represents.symm⟩, rfl⟩
  obtain ⟨code, same⟩ := enumeration.covered original
  exact ⟨code, Subtype.ext (congrArg (fun value : Fibre (pullbackSecond operation change) point parameter =>
    value.val.val.1) same)⟩

noncomputable def coherentCoveredDescent {X : D ⥤ Type v} {A : D ⥤ Type w} {B : D ⥤ Type z}
    (cover : NaturalHom X A) (remaining : NaturalHom A B) (covered : Cover cover)
    (model : Data (cover.comp remaining)) : Data remaining :=
  HostChoiceContextualSmallMapRepresentation.selectedModel remaining
    (smallFibres_covered_quotient (cover.comp remaining) cover remaining rfl covered model.smallFibres)

noncomputable def coherentParameterDescent {X : D ⥤ Type v} {A : D ⥤ Type w} {B : D ⥤ Type z}
    (operation : NaturalHom X A) (change : NaturalHom B A) (covered : Cover change)
    (model : Data (pullbackSecond operation change)) : Data operation :=
  HostChoiceContextualSmallMapRepresentation.selectedModel operation
    (small_pullback_reflect operation change covered model.smallFibres)

def diagonal (A : D ⥤ Type v) : NaturalHom A (product A A) where
  app _ value := (value, value)
  naturality _ _ := rfl

def diagonalEnumeration (A : D ⥤ Type v) (point : D) (pair : (product A A).obj point) :
    Enumeration.{u, v} (Fibre (diagonal A) point pair) where
  Carrier := {receipt : PUnit.{u + 1} // pair.1 = pair.2}
  value code := ⟨pair.1, Prod.ext rfl code.property⟩
  covered receipt := by
    have left : receipt.val = pair.1 := congrArg Prod.fst receipt.property
    have right : receipt.val = pair.2 := congrArg Prod.snd receipt.property
    exact ⟨⟨PUnit.unit, left.symm.trans right⟩, Subtype.ext left.symm⟩

theorem small_diagonal (A : D ⥤ Type v) : SmallFibres (diagonal A) :=
  fun point pair => ⟨diagonalEnumeration A point pair⟩

theorem small_covered_quotient {X : D ⥤ Type v} {A : D ⥤ Type w} {B : D ⥤ Type z}
    (cover : NaturalHom X A) (remaining : NaturalHom A B) (covered : Cover cover)
    (small : SmallFibres (cover.comp remaining)) : SmallFibres remaining :=
  smallFibres_covered_quotient (cover.comp remaining) cover remaining rfl covered small

def copairing {X : D ⥤ Type v} {Y : D ⥤ Type w} {A : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom Y A) :
    NaturalHom (ContextualSmallMapConstructions.coproduct X Y) A where
  app point value := Sum.elim (first.app point) (second.app point) value
  naturality step value := by
    cases value with
    | inl value => exact first.naturality step value
    | inr value => exact second.naturality step value

def copairingEnumeration {X : D ⥤ Type v} {Y : D ⥤ Type w} {A : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom Y A) (point : D) (value : A.obj point)
    (left : Enumeration.{u, v} (Fibre first point value))
    (right : Enumeration.{u, w} (Fibre second point value)) :
    Enumeration.{u, max v w} (Fibre (copairing first second) point value) where
  Carrier := Sum left.Carrier right.Carrier
  value code := match code with
    | .inl code => ⟨Sum.inl (left.value code).val, (left.value code).property⟩
    | .inr code => ⟨Sum.inr (right.value code).val, (right.value code).property⟩
  covered := by
    rintro ⟨argument, same⟩
    cases argument with
    | inl argument =>
        obtain ⟨code, law⟩ := left.covered ⟨argument, same⟩
        exact ⟨Sum.inl code, Subtype.ext (congrArg Sum.inl (congrArg Subtype.val law))⟩
    | inr argument =>
        obtain ⟨code, law⟩ := right.covered ⟨argument, same⟩
        exact ⟨Sum.inr code, Subtype.ext (congrArg Sum.inr (congrArg Subtype.val law))⟩

theorem small_copairing {X : D ⥤ Type v} {Y : D ⥤ Type w} {A : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom Y A)
    (left : SmallFibres first) (right : SmallFibres second) : SmallFibres (copairing first second) := by
  intro point value
  obtain ⟨leftEnumeration⟩ := left point value
  obtain ⟨rightEnumeration⟩ := right point value
  exact ⟨copairingEnumeration first second point value leftEnumeration rightEnumeration⟩

theorem copairing_left {X : D ⥤ Type v} {Y : D ⥤ Type w} {A : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom Y A) :
    (ContextualSmallMapConstructions.leftInclusion X Y).comp (copairing first second) = first := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem copairing_right {X : D ⥤ Type v} {Y : D ⥤ Type w} {A : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom Y A) :
    (ContextualSmallMapConstructions.rightInclusion X Y).comp (copairing first second) = second := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem copairing_unique {X : D ⥤ Type v} {Y : D ⥤ Type w} {A : D ⥤ Type z}
    (first : NaturalHom X A) (second : NaturalHom Y A)
    (other : NaturalHom (ContextualSmallMapConstructions.coproduct X Y) A)
    (left : (ContextualSmallMapConstructions.leftInclusion X Y).comp other = first)
    (right : (ContextualSmallMapConstructions.rightInclusion X Y).comp other = second) :
    other = copairing first second := by
  apply NaturalHom.ext
  intro point value
  cases value with
  | inl value => exact congrArg (fun map : NaturalHom X A => map.app point value) left
  | inr value => exact congrArg (fun map : NaturalHom Y A => map.app point value) right

theorem natTrans_epi_iff_cover {X A : D ⥤ Type v} (operation : NaturalHom X A) :
    @Epi (D ⥤ Type v) _ X A operation.toNatTrans ↔ Cover operation := by
  rw [NatTrans.epi_iff_epi_app]
  exact forall_congr' fun point => CategoryTheory.epi_iff_surjective _

theorem ambient_epi_iff_cover {X A : Ambient D} (operation : X ⟶ A) :
    Epi operation ↔ Cover operation := by
  constructor
  · intro epi
    have converted : @Epi (D ⥤ Type (u + 1)) _ X.interpretation A.interpretation
        operation.toNatTrans := by
      refine ⟨?_⟩
      intro target first second same
      have law : operation.comp (NaturalHom.ofNatTrans first) =
          operation.comp (NaturalHom.ofNatTrans second) := by
        apply NaturalHom.ext
        intro point value
        exact congrArg (fun map : X.interpretation ⟶ target => map.app point value) same
      have result : (NaturalHom.ofNatTrans first : A ⟶ (⟨target⟩ : Ambient D)) =
          NaturalHom.ofNatTrans second := (cancel_epi operation).mp law
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro value
      exact congrArg (fun map : NaturalHom A.interpretation target => map.app point value) result
    exact (natTrans_epi_iff_cover operation).mp converted
  · intro covered
    exact ⟨fun first second same => cover_right_cancel operation covered first second same⟩

theorem small_epi_descent {X A B : Ambient D} (cover : X ⟶ A) (remaining : A ⟶ B)
    (epi : Epi cover) (small : SmallFibres (cover.comp remaining)) : SmallFibres remaining :=
  small_covered_quotient cover remaining ((ambient_epi_iff_cover cover).mp epi) small

def terminal : D ⥤ Type (u + 1) where
  obj _ := PUnit.{u + 2}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def naturalNumbers : D ⥤ Type (u + 1) where
  obj _ := ULift.{u + 1} Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def naturalNumbersProjection : NaturalHom (naturalNumbers (D := D)) terminal where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def naturalNumbersEnumeration (point : D) (value : (terminal (D := D)).obj point) :
    Enumeration.{u, u + 1} (Fibre naturalNumbersProjection point value) where
  Carrier := ULift.{u} Nat
  value code := ⟨ULift.up code.down, by
    change (PUnit.unit : PUnit.{u + 2}) = value
    exact Subsingleton.elim _ _⟩
  covered receipt := ⟨ULift.up receipt.val.down, Subtype.ext rfl⟩

theorem naturalNumbers_small : SmallFibres (naturalNumbersProjection (D := D)) :=
  fun point value => ⟨naturalNumbersEnumeration point value⟩

def zero : NaturalHom (terminal (D := D)) naturalNumbers where
  app _ _ := ULift.up 0
  naturality _ _ := rfl

def successor : NaturalHom (naturalNumbers (D := D)) naturalNumbers where
  app _ number := ULift.up number.down.succ
  naturality _ _ := rfl

def parameterZero (P : D ⥤ Type v) : NaturalHom P (product P naturalNumbers) where
  app _ value := (value, ULift.up 0)
  naturality _ _ := rfl

def parameterSuccessor (P : D ⥤ Type v) :
    NaturalHom (product P naturalNumbers) (product P naturalNumbers) where
  app _ value := (value.1, ULift.up value.2.down.succ)
  naturality _ _ := rfl

def iterateValue {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y)
    (point : D) (parameter : P.obj point) : Nat → Y.obj point
  | 0 => initial.app point parameter
  | number + 1 => step.app point (parameter, iterateValue initial step point parameter number)

def iterate {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y) :
    NaturalHom (product P naturalNumbers) Y where
  app point value := iterateValue initial step point value.1 value.2.down
  naturality {first second} arrow value := by
    rcases value with ⟨parameter, ⟨number⟩⟩
    change Y.map arrow (iterateValue initial step first parameter number) =
      iterateValue initial step second (P.map arrow parameter) number
    induction number with
    | zero => exact initial.naturality arrow parameter
    | succ number hypothesis =>
        change Y.map arrow (step.app first (parameter, iterateValue initial step first parameter number)) = _
        exact (step.naturality arrow (parameter, iterateValue initial step first parameter number)).trans
          (congrArg (fun result => step.app second (P.map arrow parameter, result)) hypothesis)

def iterationPair {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (operation : NaturalHom (product P naturalNumbers) Y) :
    NaturalHom (product P naturalNumbers) (product P Y) :=
  pair P Y (firstProjection P naturalNumbers) operation

theorem iterate_zero {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y) :
    (parameterZero P).comp (iterate initial step) = initial := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem iterate_successor {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y) :
    (parameterSuccessor P).comp (iterate initial step) =
      (iterationPair (iterate initial step)).comp step := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem iterate_unique {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y)
    (other : NaturalHom (product P naturalNumbers) Y)
    (zeroLaw : (parameterZero P).comp other = initial)
    (successorLaw : (parameterSuccessor P).comp other = (iterationPair other).comp step) :
    other = iterate initial step := by
  apply NaturalHom.ext
  rintro point ⟨parameter, ⟨number⟩⟩
  change other.app point (parameter, ULift.up number) = iterateValue initial step point parameter number
  induction number with
  | zero => exact congrArg (fun map : NaturalHom P Y => map.app point parameter) zeroLaw
  | succ number hypothesis =>
      exact (congrArg (fun map : NaturalHom (product P naturalNumbers) Y =>
        map.app point (parameter, ULift.up number)) successorLaw).trans
          (congrArg (fun result => step.app point (parameter, result)) hypothesis)

theorem indexed_naturalNumber_universal {P : D ⥤ Type v} {Y : D ⥤ Type w}
    (initial : NaturalHom P Y) (step : NaturalHom (product P Y) Y) :
    ∃! operation : NaturalHom (product P naturalNumbers) Y,
      (parameterZero P).comp operation = initial ∧
        (parameterSuccessor P).comp operation = (iterationPair operation).comp step :=
  ⟨iterate initial step, ⟨iterate_zero initial step, iterate_successor initial step⟩,
    fun other laws => iterate_unique initial step other laws.1 laws.2⟩

end Mettapedia.TypeTheory.HostChoiceContextualSmallMapModel
