import Mettapedia.GSLT.LanguageDef.NativeOpsLoweringComposition

/-!
# Supply and visible-label boundaries of actual expression lowering

These front-end laws cover every successfully lowered expression, location and
ordered argument list. They use no runtime typing, heap, call or execution
premise. A unit-valued call may consume no private identifier; its supply is
still monotone. Statement execution adequacy remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Label Supply)
open NativeLowering (Expression Arguments)

def TopLabelFree (code : List Instruction) : Prop :=
  ∀ label, Instruction.label label ∉ code

theorem top_label_free_nil : TopLabelFree [] := by
  intro label member
  cases member

theorem top_label_free_append {first second : List Instruction}
    (left : TopLabelFree first) (right : TopLabelFree second) : TopLabelFree (first ++ second) := by
  intro label member
  rcases List.mem_append.mp member with before | after
  · exact left label before
  · exact right label after

theorem top_label_free_singleton (instruction : Instruction)
    (notLabel : ∀ label, Instruction.label label ≠ instruction) : TopLabelFree [instruction] := by
  intro label member
  exact notLabel label (List.mem_singleton.mp member)

theorem pure_temporary_label_free (supply : Supply) (type : NativeType)
    (operation : NativeIR.PureOperation) :
    TopLabelFree (NativeLowering.pureTemporary supply type operation).code :=
  top_label_free_singleton _ (fun _ impossible => by cases impossible)

theorem reference_checks_label_free (atom : NativeIR.Atom) :
    TopLabelFree (NativeLowering.checkReference atom) := by
  intro label member
  simp only [NativeLowering.checkReference, List.mem_cons, List.mem_nil_iff, reduceCtorEq,
    false_or] at member

theorem numeric_guard_label_free (operation : Binary) (right : NativeIR.Atom) :
    TopLabelFree (NativeLowering.numericGuard operation right) := by
  cases operation with
  | and | or | compare _ => exact top_label_free_nil
  | word operation =>
      cases operation <;> intro label member
      all_goals simp only [NativeLowering.numericGuard, List.mem_cons, List.mem_nil_iff,
        reduceCtorEq, false_or] at member

structure LoweringBoundary (before after : Supply) (code : List Instruction) : Prop where
  monotone : before.next ≤ after.next
  labelFree : TopLabelFree code

theorem lowering_boundary_empty (supply : Supply) : LoweringBoundary supply supply [] :=
  ⟨Nat.le_refl _, top_label_free_nil⟩

theorem lowering_boundary_pure (supply : Supply) (type : NativeType)
    (operation : NativeIR.PureOperation) :
    LoweringBoundary supply (NativeLowering.pureTemporary supply type operation).supply
      (NativeLowering.pureTemporary supply type operation).code :=
  ⟨(NativeIR.fresh_strict supply).le, pure_temporary_label_free supply type operation⟩

theorem lowering_boundary_append {first middle last : Supply} {left right : List Instruction}
    (before : LoweringBoundary first middle left) (after : LoweringBoundary middle last right) :
    LoweringBoundary first last (left ++ right) :=
  ⟨before.monotone.trans after.monotone, top_label_free_append before.labelFree after.labelFree⟩

theorem lowering_boundary_suffix {before after : Supply} {code suffix : List Instruction}
    (prefixBoundary : LoweringBoundary before after code) (noLabel : TopLabelFree suffix) :
    LoweringBoundary before after (code ++ suffix) :=
  ⟨prefixBoundary.monotone, top_label_free_append prefixBoundary.labelFree noLabel⟩

theorem lowering_boundary_prepend_pure {before : Supply} {child : Expression}
    (boundary : LoweringBoundary before child.supply child.code)
    (type : NativeType) (operation : NativeIR.PureOperation) :
    LoweringBoundary before (NativeLowering.prependCode child.code
      (NativeLowering.pureTemporary child.supply type operation)).supply
      (NativeLowering.prependCode child.code
        (NativeLowering.pureTemporary child.supply type operation)).code :=
  lowering_boundary_append boundary (lowering_boundary_pure child.supply type operation)

local macro "boundary_leaf" hypothesis:ident : tactic => `(tactic|
  (rcases Option.bind_eq_some_iff.mp $hypothesis with ⟨type, _, compiled⟩
   cases Option.some.inj compiled
   first
   | exact lowering_boundary_pure _ _ _
   | refine ⟨(NativeIR.fresh_strict _).le, ?_⟩
     intro label member
     simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member))

mutual
  theorem expression_lowering_boundary (interface : Interface) (scope : Scope)
      (expression : Expr) (supply : Supply) (output : Expression)
      (compiled : NativeLowering.expression? interface scope expression supply = some output) :
      LoweringBoundary supply output.supply output.code := by
    cases expression with
    | word value => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | byte value => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | bool value => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | «variable» name => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | zero type => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | null type => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | new element => rw [NativeLowering.expression?] at compiled; boundary_leaf compiled
    | newArray element count =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨countOutput, countCompiled, compiled⟩
        cases Option.some.inj compiled
        have child := expression_lowering_boundary interface scope count supply countOutput countCompiled
        refine ⟨child.monotone.trans
          ((NativeIR.fresh_strict countOutput.supply).le.trans
            (NativeIR.fresh_strict (NativeIR.fresh countOutput.supply).2).le), ?_⟩
        apply top_label_free_append
        · exact top_label_free_append child.labelFree (pure_temporary_label_free _ _ _)
        · intro label member
          simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member
    | field base name =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨baseType, _, compiled⟩
        cases baseType with
        | named record =>
            rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨index, _, compiled⟩
            cases Option.some.inj compiled
            exact lowering_boundary_prepend_pure
              (expression_lowering_boundary interface scope base supply baseOutput baseCompiled) _ _
        | ref element =>
            cases element with
            | named record =>
                rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
                cases Option.some.inj compiled
                exact lowering_boundary_prepend_pure
                  (location_lowering_boundary interface scope (.field base name) supply locationOutput located) _ _
            | _ => cases compiled
        | _ => cases compiled
    | index array index =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_prepend_pure
          (location_lowering_boundary interface scope (.index array index) supply locationOutput located) _ _
    | load reference =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_prepend_pure
          (location_lowering_boundary interface scope (.load reference) supply locationOutput located) _ _
    | address location =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_prepend_pure
          (location_lowering_boundary interface scope location supply locationOutput located) _ _
    | length array =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_prepend_pure
          (expression_lowering_boundary interface scope array supply arrayOutput arrayCompiled) _ _
    | slice array start count =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨startOutput, startCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨countOutput, countCompiled, compiled⟩
        cases type with
        | array element =>
            cases Option.some.inj compiled
            have first := expression_lowering_boundary interface scope array supply arrayOutput arrayCompiled
            have second := expression_lowering_boundary interface scope start arrayOutput.supply startOutput startCompiled
            have third := expression_lowering_boundary interface scope count startOutput.supply countOutput countCompiled
            refine lowering_boundary_suffix
              (lowering_boundary_append (lowering_boundary_append (lowering_boundary_append first second) third)
                (lowering_boundary_pure _ _ _)) ?_
            intro label member
            simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member
        | _ => cases compiled
    | call name arguments =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨argumentOutput, argumentsCompiled, compiled⟩
        have child := arguments_lowering_boundary interface scope arguments supply argumentOutput argumentsCompiled
        repeat' (first | dsimp only at compiled | split at compiled)
        all_goals cases Option.some.inj compiled
        all_goals refine ⟨?_, ?_⟩
        all_goals first
          | exact child.monotone
          | exact child.monotone.trans (NativeIR.fresh_strict argumentOutput.supply).le
          | apply top_label_free_append child.labelFree
            intro label member
            simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member
    | unary operation operand =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨operandOutput, operandCompiled, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_prepend_pure
          (expression_lowering_boundary interface scope operand supply operandOutput operandCompiled) _ _
    | binary operation left right =>
        cases operation with
        | and | or =>
            rw [NativeLowering.expression?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨leftOutput, leftCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨rightOutput, rightCompiled, compiled⟩
            cases Option.some.inj compiled
            have first := expression_lowering_boundary interface scope left supply leftOutput leftCompiled
            have second := expression_lowering_boundary interface scope right
              (NativeLowering.pureTemporary leftOutput.supply type (.copy leftOutput.result)).supply
              rightOutput rightCompiled
            refine ⟨first.monotone.trans
              ((NativeIR.fresh_strict leftOutput.supply).le.trans second.monotone), ?_⟩
            exact top_label_free_append
              (top_label_free_append first.labelFree (pure_temporary_label_free _ _ _))
              (top_label_free_singleton _ (fun _ impossible => by cases impossible))
        | word operation | compare operation =>
            rw [NativeLowering.expression?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨leftOutput, leftCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨rightOutput, rightCompiled, compiled⟩
            cases Option.some.inj compiled
            have first := expression_lowering_boundary interface scope left supply leftOutput leftCompiled
            have second := expression_lowering_boundary interface scope right leftOutput.supply rightOutput rightCompiled
            refine lowering_boundary_append ?_ (lowering_boundary_pure _ _ _)
            exact lowering_boundary_suffix (lowering_boundary_append first second) (numeric_guard_label_free _ _)
  termination_by 2 * sizeOf expression + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem location_lowering_boundary (interface : Interface) (scope : Scope)
      (location : Expr) (supply : Supply) (output : Expression)
      (compiled : NativeLowering.location? interface scope location supply = some output) :
      LoweringBoundary supply output.supply output.code := by
    cases location with
    | «variable» name =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_empty supply
    | field base name =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨baseType, _, compiled⟩
        cases baseType with
        | named record =>
            rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨index, _, compiled⟩
            cases Option.some.inj compiled
            exact lowering_boundary_prepend_pure
              (location_lowering_boundary interface scope base supply baseOutput baseCompiled) _ _
        | ref element =>
            cases element with
            | named record =>
                rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
                rcases Option.bind_eq_some_iff.mp compiled with ⟨index, _, compiled⟩
                cases Option.some.inj compiled
                refine lowering_boundary_append ?_ (lowering_boundary_pure _ _ _)
                exact lowering_boundary_suffix
                  (expression_lowering_boundary interface scope base supply baseOutput baseCompiled)
                  (reference_checks_label_free _)
            | _ => cases compiled
        | _ => cases compiled
    | index array index =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨indexOutput, indexCompiled, compiled⟩
        cases Option.some.inj compiled
        have first := expression_lowering_boundary interface scope array supply arrayOutput arrayCompiled
        have second := expression_lowering_boundary interface scope index arrayOutput.supply indexOutput indexCompiled
        refine ⟨first.monotone.trans (second.monotone.trans (NativeIR.fresh_strict indexOutput.supply).le), ?_⟩
        apply top_label_free_append (top_label_free_append first.labelFree second.labelFree)
        intro label member
        simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member
    | load reference =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨referenceOutput, referenceCompiled, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_suffix
          (expression_lowering_boundary interface scope reference supply referenceOutput referenceCompiled)
          (reference_checks_label_free _)
    | _ =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        cases compiled
  termination_by 2 * sizeOf location
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem arguments_lowering_boundary (interface : Interface) (scope : Scope)
      (arguments : List Expr) (supply : Supply) (output : Arguments)
      (compiled : NativeLowering.arguments? interface scope arguments supply = some output) :
      LoweringBoundary supply output.supply output.code := by
    cases arguments with
    | nil =>
        rw [NativeLowering.arguments?] at compiled
        cases Option.some.inj compiled
        exact lowering_boundary_empty supply
    | cons first rest =>
        rw [NativeLowering.arguments?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨firstOutput, firstCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨restOutput, restCompiled, compiled⟩
        cases Option.some.inj compiled
        exact lowering_boundary_append
          (expression_lowering_boundary interface scope first supply firstOutput firstCompiled)
          (arguments_lowering_boundary interface scope rest firstOutput.supply restOutput restCompiled)
  termination_by 2 * sizeOf arguments
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

end Mettapedia.GSLT.LanguageDef.NativeOps
