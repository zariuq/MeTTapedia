import Mettapedia.TypeTheory.ContextualImageFactorization

/-!
# Effective quotient projections remain effective after pullback

Dependent quotient elimination constructs the value of a descended natural
map at a requested target argument. It uses that argument's actual quotient
class, not a selected occurrence. The compatibility proof identifies all
possible receipts of that argument. The resulting factor has exact beta
and uniqueness laws, so pointwise surjectivity is not the only evidence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualQuotientPullback

open CategoryTheory ContextualWitnessCover ContextualKernelQuotients ContextualImageFactorization

universe u v w z t
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} (operation : NaturalHom A B)
variable {Z : D ⥤ Type z} (change : NaturalHom Z (quotient operation))

abbrev source := pullback (projection operation) change
abbrev onto := pullbackSecond (projection operation) change

private theorem evidenceFunction_heq {Q : Type v} {X : Type z} {Y : Type t}
    (reading : X → Q) {first second : Q} (same : first = second)
    (left : ∀ value, first = reading value → Y) (right : ∀ value, second = reading value → Y)
    (pointwise : ∀ value available other, left value available = right value other) : HEq left right := by
  cases same
  apply heq_of_eq
  funext value available
  exact pointwise value available available

private theorem evidenceApplication_eq {Q : Type v} {X : Type z} {Y : Type t}
    (reading : X → Q) (function : ∀ point value, point = reading value → Y)
    {first second : Q} (same : first = second) (value : X)
    (available : first = reading value) (other : second = reading value) :
    function first value available = function second value other := by
  cases same
  rfl

variable {Y : D ⥤ Type t} (other : NaturalHom (source operation change) Y)
variable (compatible : Respects (onto operation change) other)

def classFunction (point : D) (value : (quotient operation).obj point) :
    ∀ argument : Z.obj point, value = change.app point argument → Y.obj point :=
  Quotient.hrecOn'
    (φ := fun quotientValue : Quotient (kernel operation point) =>
      ∀ argument : Z.obj point, quotientValue = change.app point argument → Y.obj point) value
    (fun receipt argument available => other.app point ⟨(receipt, argument), available⟩)
    (fun first second same => evidenceFunction_heq (change.app point)
      (Quotient.sound (s := kernel operation point) same) _ _
      (fun argument available otherAvailable => compatible point
        (first := ⟨(first, argument), available⟩) (second := ⟨(second, argument), otherAvailable⟩) rfl))

def value (point : D) (argument : Z.obj point) : Y.obj point :=
  classFunction operation change other compatible point (change.app point argument) argument rfl

theorem value_beta (point : D) (receipt : (source operation change).obj point) :
    value operation change other compatible point receipt.val.2 = other.app point receipt := by
  have transported := evidenceApplication_eq (change.app point)
    (classFunction operation change other compatible point) receipt.property receipt.val.2 receipt.property rfl
  exact transported.symm.trans (show classFunction operation change other compatible point
    ((projection operation).app point receipt.val.1) receipt.val.2 receipt.property = other.app point receipt from rfl)

def descend : NaturalHom Z Y where
  app := value operation change other compatible
  naturality {first second} step argument := by
    obtain ⟨receipt, same⟩ := pullback_surjective (projection operation) change
      (projection_surjective operation) first argument
    have before := value_beta operation change other compatible first receipt
    have after := value_beta operation change other compatible second ((source operation change).map step receipt)
    change value operation change other compatible second (Z.map step receipt.val.2) =
      other.app second ((source operation change).map step receipt) at after
    have result := (congrArg (Y.map step) before).trans
      ((other.naturality step receipt).trans after.symm)
    exact same ▸ result

theorem descend_beta (point : D) (receipt : (source operation change).obj point) :
    (descend operation change other compatible).app point ((onto operation change).app point receipt) =
      other.app point receipt := value_beta operation change other compatible point receipt

theorem factorization : (onto operation change).comp (descend operation change other compatible) = other := by
  apply NaturalHom.ext
  exact descend_beta operation change other compatible

theorem uniqueness (candidate : NaturalHom Z Y)
    (factors : (onto operation change).comp candidate = other) :
    candidate = descend operation change other compatible := by
  apply NaturalHom.ext
  intro point argument
  obtain ⟨receipt, same⟩ := pullback_surjective (projection operation) change
    (projection_surjective operation) point argument
  have square := congrArg (fun map : NaturalHom (source operation change) Y => map.app point receipt) factors
  exact same ▸ square.trans (descend_beta operation change other compatible point receipt).symm

theorem effective_universal
    (equalized : (kernelFirst (onto operation change)).comp other =
      (kernelSecond (onto operation change)).comp other) :
    ∃! factor : NaturalHom Z Y, (onto operation change).comp factor = other := by
  let respects := (kernelPair_compatibility_iff (onto operation change) other).mp equalized
  refine ⟨descend operation change other respects, factorization operation change other respects, ?_⟩
  intro candidate factors
  exact uniqueness operation change other respects candidate factors

end Mettapedia.TypeTheory.ContextualQuotientPullback
