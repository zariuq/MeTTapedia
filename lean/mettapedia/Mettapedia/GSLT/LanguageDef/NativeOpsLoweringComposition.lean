import Mettapedia.GSLT.LanguageDef.NativeOpsLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsRunComposition

/-!
# Control boundaries of authored native expressions

Successful expression, address and argument lowering produces no outward
label transfer. These syntactic facts connect the actual lowering definitions
to finite target-run composition, including short-circuit branches and array
initialization loops. They do not replace expression or function adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction)
open NativeLowering (Expression Arguments)

theorem jump_free_append (first second : List Instruction) :
    jumpFreeCode (first ++ second) = (jumpFreeCode first && jumpFreeCode second) := by
  induction first with
  | nil => simp only [List.nil_append, jumpFreeCode, Bool.true_and]
  | cons head tail ih =>
      simp only [List.cons_append, jumpFreeCode, ih, Bool.and_assoc]

theorem pure_temporary_jump_free (supply : NativeIR.Supply) (type : NativeType)
    (operation : NativeIR.PureOperation) :
    jumpFreeCode (NativeLowering.pureTemporary supply type operation).code = true := by
  simp only [NativeLowering.pureTemporary, jumpFreeCode, jumpFreeInstruction, Bool.true_and]

theorem reference_checks_jump_free (value : NativeIR.Atom) :
    jumpFreeCode (NativeLowering.checkReference value) = true := by
  simp only [NativeLowering.checkReference, jumpFreeCode, jumpFreeInstruction, Bool.true_and]

theorem numeric_guard_jump_free (operation : Binary) (right : NativeIR.Atom) :
    jumpFreeCode (NativeLowering.numericGuard operation right) = true := by
  cases operation with
  | word operation => cases operation <;> simp only [NativeLowering.numericGuard, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
  | compare operation => simp only [NativeLowering.numericGuard, jumpFreeCode]
  | and => simp only [NativeLowering.numericGuard, jumpFreeCode]
  | or => simp only [NativeLowering.numericGuard, jumpFreeCode]

local macro "finish_leaf_lowering" compiled:ident : tactic => `(tactic| (
  rcases Option.bind_eq_some_iff.mp $compiled with ⟨type, inferred, lowered⟩
  cases Option.some.inj lowered
  simp only [NativeLowering.pureTemporary, jumpFreeCode, jumpFreeInstruction, Bool.true_and]))

mutual
  theorem expression_lowering_jump_free (interface : Interface) (scope : Scope)
      (expression : Expr) (supply : NativeIR.Supply) (output : Expression)
      (compiled : NativeLowering.expression? interface scope expression supply = some output) :
      jumpFreeCode output.code = true := by
    cases expression with
    | word value => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | byte value => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | bool value => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | «variable» name => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | zero type => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | null type => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | new type => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | newArray element count =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨countOutput, countCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope count supply countOutput countCompiled,
          pure_temporary_jump_free, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
    | field base name =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨baseType, baseInferred, compiled⟩
        cases baseType with
        | named record =>
            rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨index, layout, compiled⟩
            cases Option.some.inj compiled
            simp only [NativeLowering.prependCode, jump_free_append,
              expression_lowering_jump_free interface scope base supply baseOutput baseCompiled,
              pure_temporary_jump_free, Bool.true_and]
        | ref element =>
            cases element with
            | named record =>
                rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
                cases Option.some.inj compiled
                simp only [NativeLowering.prependCode, jump_free_append,
                  location_lowering_jump_free interface scope (.field base name) supply locationOutput located,
                  pure_temporary_jump_free, Bool.true_and]
            | _ => cases compiled
        | _ => cases compiled
    | index array index =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          location_lowering_jump_free interface scope (.index array index) supply locationOutput located,
          pure_temporary_jump_free, Bool.true_and]
    | load reference =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          location_lowering_jump_free interface scope (.load reference) supply locationOutput located,
          pure_temporary_jump_free, Bool.true_and]
    | address location =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          location_lowering_jump_free interface scope location supply locationOutput located,
          pure_temporary_jump_free, Bool.true_and]
    | length array =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          expression_lowering_jump_free interface scope array supply arrayOutput arrayCompiled,
          pure_temporary_jump_free, Bool.true_and]
    | slice array start count =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨startOutput, startCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨countOutput, countCompiled, compiled⟩
        cases type with
        | array element =>
            cases Option.some.inj compiled
            simp only [jump_free_append,
              expression_lowering_jump_free interface scope array supply arrayOutput arrayCompiled,
              expression_lowering_jump_free interface scope start arrayOutput.supply startOutput startCompiled,
              expression_lowering_jump_free interface scope count startOutput.supply countOutput countCompiled,
              pure_temporary_jump_free, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
        | _ => cases compiled
    | call name arguments =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨argumentOutput, argumentsCompiled, compiled⟩
        repeat' (first | dsimp only at compiled | split at compiled)
        all_goals cases Option.some.inj compiled
        all_goals simp only [jump_free_append,
            arguments_lowering_jump_free interface scope arguments supply argumentOutput argumentsCompiled,
            jumpFreeCode, jumpFreeInstruction, Bool.true_and]
    | unary operation operand =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨operandOutput, operandCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          expression_lowering_jump_free interface scope operand supply operandOutput operandCompiled,
          pure_temporary_jump_free, Bool.true_and]
    | binary operation left right =>
        cases operation with
        | and | or =>
            rw [NativeLowering.expression?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨leftOutput, leftCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨rightOutput, rightCompiled, compiled⟩
            cases Option.some.inj compiled
            simp only [jump_free_append,
              expression_lowering_jump_free interface scope left supply leftOutput leftCompiled,
              pure_temporary_jump_free, jumpFreeCode, jumpFreeInstruction,
              expression_lowering_jump_free interface scope right
                (NativeLowering.pureTemporary leftOutput.supply type (.copy leftOutput.result)).supply
                rightOutput rightCompiled, Bool.true_and]
        | word operation | compare operation =>
            rw [NativeLowering.expression?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨leftOutput, leftCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨rightOutput, rightCompiled, compiled⟩
            cases Option.some.inj compiled
            simp only [NativeLowering.prependCode, jump_free_append,
              expression_lowering_jump_free interface scope left supply leftOutput leftCompiled,
              expression_lowering_jump_free interface scope right leftOutput.supply rightOutput rightCompiled,
              numeric_guard_jump_free, pure_temporary_jump_free, Bool.true_and]
  termination_by 2 * sizeOf expression + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem location_lowering_jump_free (interface : Interface) (scope : Scope)
      (location : Expr) (supply : NativeIR.Supply) (output : Expression)
      (compiled : NativeLowering.location? interface scope location supply = some output) :
      jumpFreeCode output.code = true := by
    cases location with
    | «variable» name => rw [NativeLowering.location?] at compiled; finish_leaf_lowering compiled
    | field base name =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨baseType, baseInferred, compiled⟩
        cases baseType with
        | named record =>
            rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨index, layout, compiled⟩
            cases Option.some.inj compiled
            simp only [NativeLowering.prependCode, jump_free_append,
              location_lowering_jump_free interface scope base supply baseOutput baseCompiled,
              pure_temporary_jump_free, Bool.true_and]
        | ref element =>
            cases element with
            | named record =>
                rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
                rcases Option.bind_eq_some_iff.mp compiled with ⟨index, layout, compiled⟩
                cases Option.some.inj compiled
                simp only [NativeLowering.prependCode, jump_free_append,
                  expression_lowering_jump_free interface scope base supply baseOutput baseCompiled,
                  reference_checks_jump_free, pure_temporary_jump_free, Bool.true_and]
            | _ => cases compiled
        | _ => cases compiled
    | index array index =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨indexOutput, indexCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope array supply arrayOutput arrayCompiled,
          expression_lowering_jump_free interface scope index arrayOutput.supply indexOutput indexCompiled,
          jumpFreeCode, jumpFreeInstruction, Bool.true_and]
    | load reference =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨referenceOutput, referenceCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope reference supply referenceOutput referenceCompiled,
          reference_checks_jump_free, Bool.true_and]
    | _ =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        cases compiled
  termination_by 2 * sizeOf location
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem arguments_lowering_jump_free (interface : Interface) (scope : Scope)
      (arguments : List Expr) (supply : NativeIR.Supply) (output : Arguments)
      (compiled : NativeLowering.arguments? interface scope arguments supply = some output) :
      jumpFreeCode output.code = true := by
    cases arguments with
    | nil =>
        rw [NativeLowering.arguments?] at compiled
        cases Option.some.inj compiled
        simp only [jumpFreeCode]
    | cons first rest =>
        rw [NativeLowering.arguments?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨firstOutput, firstCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨restOutput, restCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope first supply firstOutput firstCompiled,
          arguments_lowering_jump_free interface scope rest firstOutput.supply restOutput restCompiled,
          Bool.true_and]
  termination_by 2 * sizeOf arguments
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

end Mettapedia.GSLT.LanguageDef.NativeOps
