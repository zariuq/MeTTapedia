import Mettapedia.Languages.Micromath.Kernel

/-!
# Static Micromath controls in a nontrivial Boolean model

The two projections have different meanings. Two consistent seed equations
permit a genuine new substitution consequence. A second control shows why
the shared-input check matters: four individually valid equations would
yield a false equation if the differing input were silently identified.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Micromath.KernelControls

def boolAssignment : Assignment Bool
  | 0 => fun a _ => a
  | 1 => fun _ b => b
  | 2 => Bool.and
  | 4 => Bool.and
  | 5 => fun a _ => a
  | 6 => fun _ b => b
  | 7 => Bool.and
  | _ => Bool.xor

theorem bool_projects : Projects boolAssignment := ⟨fun _ _ => rfl,fun _ _ => rfl⟩

def projectionCollapse : Claim := ⟨0,1,0,1⟩
theorem projection_collapse_false : ¬ Holds boolAssignment projectionCollapse := by
  intro claimed
  exact Bool.noConfusion (claimed false true)

theorem projection_collapse_not_derivable : ¬ Derives ∅ projectionCollapse := by
  intro proof
  exact projection_collapse_false (derives_sound boolAssignment bool_projects (fun _ member => False.elim member) proof)

theorem future_names_are_allowed : Derives ∅ (projectionFirst 7000 9000) := .projectionFirst 7000 9000

def main : Claim := ⟨4,2,0,1⟩
def left : Claim := projectionFirst 5 6
def right : Claim := projectionSecond 5 6
def packed : Claim := ⟨7,4,5,6⟩
def transferred : Claim := ⟨7,2,5,6⟩
def axioms : Set Claim := fun claim => claim = main ∨ claim = packed

theorem source_seeds_hold : ∀ claim ∈ axioms, Holds boolAssignment claim := by
  intro claim member
  rcases member with rfl | rfl
  · intro a b; cases a <;> cases b <;> rfl
  · intro a b; cases a <;> cases b <;> rfl

theorem forward_substitution : substitute1? main left right packed = some transferred := by decide +kernel
theorem reverse_substitution : substitute2? main left right transferred = some packed := by decide +kernel

theorem transferred_is_new : transferred ∉ axioms := by
  change ¬ (transferred = main ∨ transferred = packed)
  decide +kernel
theorem transferred_derives : Derives axioms transferred :=
  .substitute1 (.assumption (Or.inl rfl)) (.projectionFirst 5 6) (.projectionSecond 5 6)
    (.assumption (Or.inr rfl)) forward_substitution

theorem transferred_holds : Holds boolAssignment transferred :=
  derives_sound boolAssignment bool_projects source_seeds_hold transferred_derives

theorem substituted_reverse_derives : Derives axioms packed :=
  .substitute2 (.assumption (Or.inl rfl)) (.projectionFirst 5 6) (.projectionSecond 5 6)
    transferred_derives reverse_substitution

theorem wrong_left_function_refused : substitute1? main {left with f := 3} right packed = none := by decide +kernel
theorem differing_inputs_refused : substitute1? main left {right with x := 8} packed = none := by decide +kernel
theorem wrong_forward_result_function_refused : substitute1? main left right transferred = none := by decide +kernel
theorem wrong_reverse_result_function_refused : substitute2? main left right packed = none := by decide +kernel
theorem wrong_reverse_result_argument_refused : substitute2? main left right {transferred with x := 6} = none := by decide +kernel

def diagonalAnd : Claim := ⟨0,2,0,0⟩
def firstIdentity : Claim := ⟨0,0,0,0⟩
def differentFirstInput : Claim := ⟨1,0,1,0⟩
def falseMixedAnd : Claim := ⟨0,2,0,1⟩

theorem diagonal_and_holds : Holds boolAssignment diagonalAnd := by
  intro a b; cases a <;> cases b <;> rfl
theorem first_identity_holds : Holds boolAssignment firstIdentity := by
  intro a b; cases a <;> cases b <;> rfl
theorem different_first_input_holds : Holds boolAssignment differentFirstInput := by
  intro a b; cases a <;> cases b <;> rfl
theorem mixed_and_false : ¬ Holds boolAssignment falseMixedAnd := by
  intro claimed
  exact Bool.noConfusion (claimed true false)

theorem shared_input_separator :
    Holds boolAssignment diagonalAnd ∧ Holds boolAssignment firstIdentity ∧
    Holds boolAssignment differentFirstInput ∧
    ¬ Holds boolAssignment falseMixedAnd ∧
    substitute1? diagonalAnd firstIdentity differentFirstInput firstIdentity = none :=
  ⟨diagonal_and_holds,first_identity_holds,different_first_input_holds,mixed_and_false,by decide +kernel⟩

#print axioms projection_collapse_not_derivable
#print axioms source_seeds_hold
#print axioms transferred_derives
#print axioms shared_input_separator
end Mettapedia.Languages.Micromath.KernelControls
