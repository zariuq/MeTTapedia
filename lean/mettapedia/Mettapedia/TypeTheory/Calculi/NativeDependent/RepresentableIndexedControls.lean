import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedTerms
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Types.Basic

/-!
# Complete bounded witnesses and an empty indexed fibre

A supplied natural-number index retains its independently supplied element
of Fin (n + 1). Different bounded witnesses over one index remain distinct.
A separate successor map has no witness over zero and a witness over twelve.
These are native dependent calculations, without compiled numeral execution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.Controls

open _root_.CategoryTheory Opposite

noncomputable section

abbrev Base := AsSmall.{0} (Type)
abbrev unitObject : Base := ⟨PUnit⟩
abbrev naturalObject : Base := ⟨Nat⟩
abbrev boundedObject : Base := ⟨Σ n : Nat, Fin (n + 1)⟩

def projection : boundedObject ⟶ naturalObject := ⟨↾Sigma.fst⟩
def indexed : ArrowSymbol Base := ⟨boundedObject, naturalObject, projection⟩

def point (n : Nat) : unitObject ⟶ naturalObject := ⟨↾fun _ => n⟩
def valuePoint (n : Nat) (witness : Fin (n + 1)) : unitObject ⟶ boundedObject :=
  ⟨↾fun _ => ⟨n, witness⟩⟩

def argument (n : Nat) : (objectScope naturalObject).1.obj (op unitObject) :=
  (objectNameInverse naturalObject).app (op unitObject) (point n)

def value (n : Nat) (witness : Fin (n + 1)) :
    (fibreMeaning indexed).decoded.obj ⟨op unitObject, argument n⟩ :=
  encode indexed (op unitObject) (argument n) (valuePoint n witness) rfl

theorem complete_bounded_readout (n : Nat) (witness : Fin (n + 1)) :
    (decode indexed (op unitObject) (argument n) (value n witness)).val.down PUnit.unit =
      ⟨n, witness⟩ := rfl

theorem witness_is_retained (n : Nat) (witness : Fin (n + 1)) :
    ((decode indexed (op unitObject) (argument n) (value n witness)).val.down PUnit.unit).2 =
      witness := rfl

theorem distinct_witnesses_are_distinct (n : Nat) {first second : Fin (n + 1)}
    (different : first ≠ second) : value n first ≠ value n second := by
  intro same
  have read := congrArg (fun supplied =>
    ((decode indexed (op unitObject) (argument n) supplied).val.down PUnit.unit).2.val) same
  exact different (Fin.ext read)

theorem one_and_two_remain_distinct : value 3 ⟨1, by decide⟩ ≠ value 3 ⟨2, by decide⟩ :=
  distinct_witnesses_are_distinct 3 (by decide)

def independently_generated_type :
    Derivation (signature Base) (.type (objectContext naturalObject) (fibreType indexed (.var 0))) :=
  genericFibreFormed indexed

theorem generated_type_has_the_actual_indexed_meaning :
    (model Base).evaluateType (objectScope naturalObject) (fibreType indexed (.var 0)) =
      some (fibreMeaning indexed) := generic_fibre_read indexed

theorem generated_forget_has_the_actual_value_meaning :
    (model Base).evaluateTerm (fibreScope indexed) (genericForget indexed) =
      some ⟨forgetType indexed, forgetValue indexed⟩ := generic_forget_read indexed

theorem the_generated_forget_retains_the_bounded_pair (n : Nat) (witness : Fin (n + 1)) :
    ((forgetValue indexed).val ⟨op unitObject, ⟨argument n, value n witness⟩⟩).down PUnit.unit =
      ⟨n, witness⟩ := rfl

def successor : naturalObject ⟶ naturalObject := ⟨↾Nat.succ⟩
def successorIndexed : ArrowSymbol Base := ⟨naturalObject, naturalObject, successor⟩

theorem zero_fibre_is_empty :
    IsEmpty ((fibreMeaning successorIndexed).decoded.obj ⟨op unitObject, argument 0⟩) := by
  refine ⟨fun supplied => ?_⟩
  have indexed := (decode successorIndexed (op unitObject) (argument 0) supplied).property
  have read := congrArg (fun arrow : unitObject ⟶ naturalObject => arrow.down PUnit.unit) indexed
  exact Nat.succ_ne_zero _ read

def twelveValue :
    (fibreMeaning successorIndexed).decoded.obj ⟨op unitObject, argument 12⟩ :=
  encode successorIndexed (op unitObject) (argument 12) (point 11) rfl

theorem twelve_fibre_is_inhabited :
    Nonempty ((fibreMeaning successorIndexed).decoded.obj ⟨op unitObject, argument 12⟩) :=
  ⟨twelveValue⟩

theorem the_same_native_indexed_type_has_distinct_fibres :
    (fibreMeaning successorIndexed).decoded.obj ⟨op unitObject, argument 0⟩ ≠
      (fibreMeaning successorIndexed).decoded.obj ⟨op unitObject, argument 12⟩ := by
  intro same
  exact zero_fibre_is_empty.false (same.symm ▸ twelveValue)

theorem twelve_retains_its_original_eleven :
    (show Nat from (decode successorIndexed (op unitObject) (argument 12) twelveValue).val.down
      PUnit.unit) = 11 := rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.Controls
