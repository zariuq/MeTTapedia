import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization
import Mettapedia.GSLT.LanguageDef.NativeOpsLowering

/-!
# Checked agreement of native instruction trees

The C normalizer and authored-source lowerer produce independently computed
instruction trees. The structural checker retains all operands, guards,
scopes, branches, calls, stores and temporary identities. Its acceptance
requires two successful translations; two refusals do not constitute agreement.
Execution preservation and reflection are separate semantic obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

open NativeIR

mutual
  def sameInstruction : Instruction → Instruction → Bool
    | .temporary i t op, .temporary j u oq => decide (i = j ∧ t = u ∧ op = oq)
    | .assign p a, .assign q b => decide (p = q ∧ a = b)
    | .helper p op, .helper q oq => decide (p = q ∧ op = oq)
    | .call p f args, .call q g others => decide (p = q ∧ f = g ∧ args = others)
    | .checkContextExists, .checkContextExists => true
    | .checkContext, .checkContext => true
    | .checkedNumericGuard op a, .checkedNumericGuard oq b => decide (op = oq ∧ a = b)
    | .declareLocal n t a, .declareLocal m u b => decide (n = m ∧ t = u ∧ a = b)
    | .write a b, .write c d => decide (a = c ∧ b = d)
    | .writeElement a b c, .writeElement d e f => decide (a = d ∧ b = e ∧ c = f)
    | .forWord i n body, .forWord j m other => decide (i = j ∧ n = m) && sameCode body other
    | .branch c yes no, .branch d otherYes otherNo =>
        decide (c = d) && sameCode yes otherYes && sameCode no otherNo
    | .switch a cases rest, .switch b others otherwise =>
        decide (a = b) && sameCases cases others && sameCode rest otherwise
    | .scope body, .scope other => sameCode body other
    | .label l, .label m => decide (l = m)
    | .jump l, .jump m => decide (l = m)
    | .return a, .return b => decide (a = b)
    | _, _ => false
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega

  def sameCode : List Instruction → List Instruction → Bool
    | [], [] => true
    | first :: rest, other :: others => sameInstruction first other && sameCode rest others
    | _, _ => false
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega

  def sameCases : List (BitVec 64 × List Instruction) → List (BitVec 64 × List Instruction) → Bool
    | [], [] => true
    | (key, body) :: rest, (otherKey, otherBody) :: others =>
        decide (key = otherKey) && sameCode body otherBody && sameCases rest others
    | _, _ => false
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  theorem sameInstruction_iff : (left right : Instruction) →
      (sameInstruction left right = true ↔ left = right)
    | .temporary i t op, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.temporary.injEq]
    | .assign p a, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.assign.injEq]
    | .helper p op, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.helper.injEq]
    | .call p f args, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.call.injEq]
    | .checkContextExists, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq]
    | .checkContext, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq]
    | .checkedNumericGuard op a, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.checkedNumericGuard.injEq]
    | .declareLocal n t a, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.declareLocal.injEq]
    | .write a b, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.write.injEq]
    | .writeElement a b c, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.writeElement.injEq]
    | .forWord i bound body, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Bool.and_eq_true, Instruction.forWord.injEq, sameCode_iff body, and_assoc]
    | .branch condition yes no, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Bool.and_eq_true, Instruction.branch.injEq, sameCode_iff yes, sameCode_iff no, and_assoc]
    | .switch selector arms otherwise, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Bool.and_eq_true, Instruction.switch.injEq, sameCases_iff arms, sameCode_iff otherwise, and_assoc]
    | .scope body, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, Instruction.scope.injEq, sameCode_iff body]
    | .label label, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.label.injEq]
    | .jump label, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.jump.injEq]
    | .return value, right => by
        cases right <;> simp only [sameInstruction, reduceCtorEq, decide_eq_true_eq, Instruction.return.injEq]
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega

  theorem sameCode_iff : (left right : List Instruction) →
      (sameCode left right = true ↔ left = right)
    | [], [] => by simp only [sameCode]
    | [], _ :: _ => by simp only [sameCode, reduceCtorEq]
    | _ :: _, [] => by simp only [sameCode, reduceCtorEq]
    | first :: rest, other :: others => by
        simp only [sameCode, Bool.and_eq_true, List.cons.injEq,
          sameInstruction_iff first other, sameCode_iff rest others]
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega

  theorem sameCases_iff : (left right : List (BitVec 64 × List Instruction)) →
      (sameCases left right = true ↔ left = right)
    | [], [] => by simp only [sameCases]
    | [], _ :: _ => by simp only [sameCases, reduceCtorEq]
    | _ :: _, [] => by simp only [sameCases, reduceCtorEq]
    | (key, body) :: rest, (otherKey, otherBody) :: others => by
        simp only [sameCases, Bool.and_eq_true, decide_eq_true_eq, List.cons.injEq,
          Prod.mk.injEq, sameCode_iff body otherBody, sameCases_iff rest others, and_assoc]
  termination_by left _ => sizeOf left
  decreasing_by all_goals simp_wf; all_goals omega

end

def sameFunction (left right : NativeIR.Function) : Bool :=
  decide (left.header = right.header) && sameCode left.body right.body &&
    decide (left.temporaryCount = right.temporaryCount)

theorem sameFunction_iff (left right : NativeIR.Function) :
    sameFunction left right = true ↔ left = right := by
  cases left
  cases right
  simp only [sameFunction, Bool.and_eq_true, decide_eq_true_eq, sameCode_iff,
    NativeIR.Function.mk.injEq, and_assoc]

def successfulFunctionAgreement : Option NativeIR.Function → Option NativeIR.Function → Bool
  | some left, some right => sameFunction left right
  | _, _ => false

theorem successfulFunctionAgreement_iff (left right : Option NativeIR.Function) :
    successfulFunctionAgreement left right = true ↔
      ∃ function, left = some function ∧ right = some function := by
  cases left <;> cases right <;>
    simp only [successfulFunctionAgreement, sameFunction_iff, reduceCtorEq,
      false_and, and_false, exists_false, Option.some.injEq]
  rename_i first second
  constructor
  · intro same
    exact ⟨first, rfl, same.symm⟩
  · rintro ⟨function, rfl, rfl⟩
    rfl

def bodyAgreement (representation : Representation) (native : CFunction)
    (source : NativeOps.Function) : Bool :=
  successfulFunctionAgreement (normalizeFunction? representation native)
    (NativeLowering.function? representation.interface source)

theorem bodyAgreement_iff (representation : Representation) (native : CFunction)
    (source : NativeOps.Function) :
    bodyAgreement representation native source = true ↔
      ∃ function, normalizeFunction? representation native = some function ∧
        NativeLowering.function? representation.interface source = some function :=
  successfulFunctionAgreement_iff _ _

/-- Matching nested control preserves the guard, temporary and return. -/
theorem matching_nested_control :
    sameCode [.scope [.checkedNumericGuard .div (.word 7), .return (.word 3)]]
      [.scope [.checkedNumericGuard .div (.word 7), .return (.word 3)]] = true := by
  decide +kernel

/-- Dropping a refusal guard cannot pass body agreement. -/
theorem missing_guard_refused :
    sameCode [.scope [.checkedNumericGuard .div (.word 7), .return (.word 3)]]
      [.scope [.return (.word 3)]] = false := by
  decide +kernel

theorem changed_switch_multiplicity_refused :
    sameCode [.switch (.word 0) [(0, [.return (.word 1)])] []]
      [.switch (.word 0) [(0, [.return (.word 1)]), (0, [.return (.word 1)])] []] = false := by
  decide +kernel

theorem both_translations_refused : successfulFunctionAgreement none none = false := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
