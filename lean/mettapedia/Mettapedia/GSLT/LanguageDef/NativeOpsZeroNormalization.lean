import Mettapedia.GSLT.LanguageDef.NativeOpsTargetValues

/-!
# Typed scalar initializer normalization

C prints a scalar default as 0 or false, whereas the operational IR can
retain a generic typed-zero initializer. The rewrite below changes only that
pure initializer and preserves every result in both directions. Pointer,
array and record zeros retain their respective types and constructors.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR

def canonicalPure : PureOperation → PureOperation
  | .zero .word => .word 0
  | .zero .byte => .byte 0
  | .zero .bool => .bool false
  | operation => operation

theorem canonical_pure_exact {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) (operation : PureOperation) (value : TargetValue) :
    TargetPureEval interface frame state (canonicalPure operation) value ↔
      TargetPureEval interface frame state operation value := by
  cases operation <;> try exact Iff.rfl
  case zero type =>
    cases type <;> try exact Iff.rfl
    case word =>
      constructor
      · intro computed; cases computed; exact .zero .unsignedWord
      · intro initialized; cases initialized with
        | zero initialized => cases initialized; exact .word 0
    case byte =>
      constructor
      · intro computed; cases computed; exact .zero .unsignedByte
      · intro initialized; cases initialized with
        | zero initialized => cases initialized; exact .byte 0
    case bool =>
      constructor
      · intro computed; cases computed; exact .zero .boolean
      · intro initialized; cases initialized with
        | zero initialized => cases initialized; exact .bool false

mutual
  def canonicalCode (code : List Instruction) : List Instruction := match code with
    | [] => []
    | first :: rest => canonicalInstruction first :: canonicalCode rest
  termination_by sizeOf code
  decreasing_by all_goals simp_wf; all_goals omega

  def canonicalInstruction (instruction : Instruction) : Instruction := match instruction with
    | .temporary identity type operation => .temporary identity type (canonicalPure operation)
    | .forWord counter bound body => .forWord counter bound (canonicalCode body)
    | .branch condition yes no => .branch condition (canonicalCode yes) (canonicalCode no)
    | .switch selector arms otherwise => .switch selector (canonicalArms arms) (canonicalCode otherwise)
    | .scope body => .scope (canonicalCode body)
    | instruction => instruction
  termination_by sizeOf instruction
  decreasing_by all_goals simp_wf; all_goals omega

  def canonicalArms (arms : List (BitVec 64 × List Instruction)) : List (BitVec 64 × List Instruction) := match arms with
    | [] => []
    | (selector, body) :: rest => (selector, canonicalCode body) :: canonicalArms rest
  termination_by sizeOf arms
  decreasing_by all_goals simp_wf; all_goals omega
end

def canonicalFunction (function : NativeIR.Function) : NativeIR.Function :=
  { function with body := canonicalCode function.body }

theorem null_pointer_initializer_keeps_type (element : NativeType) :
    canonicalPure (.zero (.ref element)) = .zero (.ref element) := rfl

theorem empty_array_initializer_keeps_type (element : NativeType) :
    canonicalPure (.zero (.array element)) = .zero (.array element) := rfl

theorem record_initializer_keeps_layout (name : String) :
    canonicalPure (.zero (.named name)) = .zero (.named name) := rfl

theorem word_default_is_not_byte (interface : Interface) (frame : TargetFrame)
    {World : Type} (state : TargetState World) :
    ¬ TargetPureEval interface frame state (canonicalPure (.zero .word)) (.byte 0) := by
  intro computed
  cases computed

end Mettapedia.GSLT.LanguageDef.NativeOps
