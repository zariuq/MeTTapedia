import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.NativeSubstitution

/-!
# Executable checking and scope controls

These are observations of the constructed checking procedure, with no supplied
proof trees. Both dependent binders and the number recursor are exercised. A
false observation means this fuel-bounded test found no derivation; separate
model theorems distinguish genuine ill-typedness where stated.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ExecutableCheckingControls

open TypedEquality.Normalization
open Mettapedia.TypeTheory.UniverseLevel

abbrev level : LevelExpr Nat := .const 0
abbrev rules := TowerNumbersModel.rules level

def num {n : Nat} : Tm Tower.Head n := .const TowerNumbersModel.num

def zero {n : Nat} : Tm Tower.Head n := .const TowerNumbersModel.zero

def succ {n : Nat} (term : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.const TowerNumbersModel.succ) term

def sort {n : Nat} (index : Nat) : Tm Tower.Head n := .head (.sort (.const index))

def numeral {n : Nat} : Nat → Tm Tower.Head n
  | 0 => zero
  | value+1 => succ (numeral value)

def test {n : Nat} (context : Ctx Tower.Head n) (term type : Tm Tower.Head n) : Bool :=
  ExecutableTowerNumbers.accepts level 80 context term type

def packType : Tm Tower.Head 0 := .pi num (.sigma num (.id num (.var 1) (.var 0)))

def pack : Tm Tower.Head 0 := .lam (.pair (.var 0) (.refl (.var 0)))

def wrongPack : Tm Tower.Head 0 := .lam (.pair (.var 0) (.refl (succ (.var 0))))

def polymorphicIdType : Tm Tower.Head 0 := .pi (sort 0) (.pi (.var 0) (.var 1))

def polymorphicId : Tm Tower.Head 0 := .lam (.lam (.var 0))

def copiedByRecursor (value : Nat) : Tm Tower.Head 0 :=
  recApp TowerNumbersModel.numRec
    [.lam num, zero, .lam (.lam (succ (.var 0)))] (numeral value)

theorem dependent_pack_accepted : test .nil pack packType = true := by decide +kernel

theorem wrong_dependent_endpoint_rejected : test .nil wrongPack packType = false := by decide +kernel

theorem polymorphic_identity_accepted : test .nil polymorphicId polymorphicIdType = true := by
  decide +kernel

theorem self_universe_rejected : test .nil (sort 0) (sort 0) = false := by decide +kernel

theorem cumulative_universe_accepted : test .nil (sort 0) (sort 3) = true := by decide +kernel

theorem malformed_context_rejected : test (.snoc .nil zero) (.var 0) zero = false := by
  decide +kernel

theorem malformed_expected_type_rejected : test .nil zero zero = false := by decide +kernel

theorem ignored_well_typed_argument_accepted :
    test .nil (.app (.lam (zero : Tm Tower.Head 1)) (sort 0)) num = true := by
  decide +kernel

/-- The argument above is well-typed at its own higher universe. In contrast,
ignoring an argument does not justify accepting an undeclared argument. -/
theorem ignored_undeclared_argument_rejected :
    test .nil (.app (.lam (zero : Tm Tower.Head 1)) (.const `missing)) num = false := by
  decide +kernel

theorem id_endpoint_type_rejected :
    test .nil (.refl zero) (.id num zero (sort 0)) = false := by decide +kernel

theorem distinct_number_endpoints_rejected :
    test .nil (.refl zero) (.id num zero (succ zero)) = false := by decide +kernel

theorem recursor_accepted : test .nil (copiedByRecursor 3) num = true := by decide +kernel

theorem recursor_computes :
    ExecutableReduction.normalizeTerm rules (ExecutableTowerNumbers.root level) 40
      (copiedByRecursor 3) = some (numeral 3) := by decide +kernel

theorem nested_root_computes :
    ExecutableReduction.normalizeTerm rules (ExecutableTowerNumbers.root level) 40
      (.pair (copiedByRecursor 2) (.refl (copiedByRecursor 1))) =
      some (.pair (numeral 2) (.refl (numeral 1))) := by decide +kernel

theorem exhausted_is_unestablished :
    ExecutableTowerNumbers.accepts level 0 .nil zero num = false := by decide +kernel

/-- A successful observation has an actual typing derivation. -/
theorem dependent_pack_typed : TypedEquality.Typed rules .nil pack packType :=
  ExecutableTowerNumbers.accepts_sound level dependent_pack_accepted

/-- This negative boundary is a theorem of the normalization model, beyond a
finite search refusal. -/
theorem distinct_number_endpoints_not_equal :
    ¬ TypedEquality.Equal rules .nil zero (succ zero) num :=
  TowerNumbers.zero_ne_succ .nil

end ExecutableCheckingControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
