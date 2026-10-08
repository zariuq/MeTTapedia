import Mettapedia.GSLT.LanguageDef.NativeOpsGuardedExpressionCorrespondence
import Mettapedia.GSLT.LanguageDef.NativeOpsInstructionComposition

/-!
# Authored boolean branch lowering and private-frame profiles

The actual compiler copies the left operand, branches on that copy, and
assigns the right operand only in the selected arm. Scope closure retains the
outer copy and removes arm-local temporaries. These laws describe that exact
fragment and the private-map invariant needed at its boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom Condition)
open NativeLowering (Expression)

/-- Typed zero/null testing executes through the ordinary pure target
operation. An outer pointer tag establishes nullness, not pointee liveness. -/
theorem scalar_condition_evaluates {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {value : TargetValue}
    (tagged : TargetOuterTag atom.type value)
    (read : TargetAtomEval interface frame state atom value)
    {operation : NativeIR.PureOperation}
    (admitted : NativeLowering.scalarConditionOperation? atom = some operation) :
    ∃ test, targetScalarCondition value = some test ∧
      TargetPureEval interface frame state operation (.bool test) := by
  generalize typeEq : atom.type = type at tagged
  cases tagged with
  | unit => simp [NativeLowering.scalarConditionOperation?, typeEq] at admitted
  | record => simp [NativeLowering.scalarConditionOperation?, typeEq] at admitted
  | array => simp [NativeLowering.scalarConditionOperation?, typeEq] at admitted
  | bool value =>
      simp only [NativeLowering.scalarConditionOperation?, typeEq, Option.some.injEq] at admitted
      cases admitted
      exact ⟨value, rfl, .copy read⟩
  | word value =>
      simp only [NativeLowering.scalarConditionOperation?, typeEq, Option.some.injEq] at admitted
      cases admitted
      refine ⟨decide (value.toNat ≠ 0), rfl, .binary read (.zero .unsignedWord) ?_⟩
      have testEq : (!(value == (0 : BitVec 64))) = decide (value.toNat ≠ 0) := by
        apply Bool.eq_iff_iff.mpr
        simp [BitVec.toNat_eq]
      change some (TargetValue.bool (!(value == (0 : BitVec 64)))) =
        some (TargetValue.bool (decide (value.toNat ≠ 0)))
      exact congrArg (fun test => some (TargetValue.bool test)) testEq
  | byte value =>
      simp only [NativeLowering.scalarConditionOperation?, typeEq, Option.some.injEq] at admitted
      cases admitted
      refine ⟨decide (value.toNat ≠ 0), rfl, .binary read (.zero .unsignedByte) ?_⟩
      have testEq : (!(NativeWord64.targetToWord value == NativeWord64.targetToWord 0)) =
          decide (value.toNat ≠ 0) := by
        apply Bool.eq_iff_iff.mpr
        simp [NativeWord64.targetToWord, BitVec.toNat_eq,
          BitVec.toNat_setWidth_of_le (by decide +kernel : 8 ≤ 64)]
      change some (TargetValue.bool (!(NativeWord64.targetToWord value == NativeWord64.targetToWord 0))) =
        some (TargetValue.bool (decide (value.toNat ≠ 0)))
      exact congrArg (fun test => some (TargetValue.bool test)) testEq
  | reference element address =>
      simp only [NativeLowering.scalarConditionOperation?, typeEq, Option.some.injEq] at admitted
      cases admitted
      refine ⟨address.isSome, rfl, .binary read (.zero (.nullPointer element)) ?_⟩
      cases address <;> rfl

theorem scalar_condition_exact {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {value result : TargetValue}
    (tagged : TargetOuterTag atom.type value)
    (read : TargetAtomEval interface frame state atom value)
    {operation : NativeIR.PureOperation}
    (admitted : NativeLowering.scalarConditionOperation? atom = some operation) :
    TargetPureEval interface frame state operation result ↔
      ∃ test, targetScalarCondition value = some test ∧ result = .bool test := by
  obtain ⟨test, meaning, computed⟩ := scalar_condition_evaluates tagged read admitted
  constructor
  · intro ran
    exact ⟨test, meaning, target_pure_unique ran computed⟩
  · rintro ⟨other, same, resultEq⟩
    cases Option.some.inj (meaning.symm.trans same)
    cases resultEq
    exact computed

/-- The target condition is compared with the independently defined source
scalar value, in both directions and with no additional possible result. -/
theorem scalar_condition_source_exact {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom}
    {value : SourceValue} {result : TargetValue}
    (tagged : SourceOuterTag atom.type value)
    (read : TargetAtomEval interface frame state atom (encodeValue value))
    {operation : NativeIR.PureOperation}
    (admitted : NativeLowering.scalarConditionOperation? atom = some operation) :
    TargetPureEval interface frame state operation result ↔
      ∃ test, sourceScalarCondition value = some test ∧ result = .bool test := by
  rw [← scalar_condition_correspondence]
  exact scalar_condition_exact (outer_tag_preservation tagged) read admitted

/-- A condition temporary retains the complete external state, memory,
fault and accounting record; only its fresh private binding is installed. -/
theorem scalar_condition_run_source_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {frame : TargetFrame} {state : TargetState World} {atom : Atom} {value : SourceValue}
    (tagged : SourceOuterTag atom.type value)
    (read : TargetAtomEval interface frame state atom (encodeValue value))
    {operation : NativeIR.PureOperation}
    (admitted : NativeLowering.scalarConditionOperation? atom = some operation)
    {test : Bool} (meaning : sourceScalarCondition value = some test)
    {identity : Nat} (unused : frame.temporaryNames.contains identity = false)
    (root : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.temporary identity .bool operation] frame state out ↔
      out = ⟨.normal, targetDeclareTemporary frame identity (.bool test), state⟩ := by
  have computed := (scalar_condition_source_exact tagged read admitted).mpr
    ⟨test, meaning, rfl⟩
  exact target_run_temporary_exact unused computed root out

theorem scalar_condition_boolean_path {input : Expression}
    (typed : input.result.type = .bool) : NativeLowering.scalarCondition? input = some input := by
  simp only [NativeLowering.scalarCondition?, typed]

theorem source_short_circuit_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (continueValue : Bool) (left right : Expr) (before : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary (shortCircuitBinary continueValue) left right) before out ↔
      (∃ after, SourceExprEval interface heap calls frame left before ⟨.ok (.bool (!continueValue)), after⟩ ∧
        out = ⟨.ok (.bool (!continueValue)), after⟩) ∨
      (∃ middle, SourceExprEval interface heap calls frame left before ⟨.ok (.bool continueValue), middle⟩ ∧
        SourceExprEval interface heap calls frame right middle out) ∨
      (∃ fault after, SourceExprEval interface heap calls frame left before ⟨.error fault, after⟩ ∧
        out = ⟨.error fault, after⟩) := by
  cases continueValue
  · exact source_or_exact left right before out
  · exact source_and_exact left right before out

theorem source_short_circuit_skip {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (continueValue : Bool) {left right : Expr} {before after : SourceState World}
    (ran : SourceExprEval interface heap calls frame left before ⟨.ok (.bool (!continueValue)), after⟩) :
    SourceExprEval interface heap calls frame (.binary (shortCircuitBinary continueValue) left right) before
      ⟨.ok (.bool (!continueValue)), after⟩ :=
  (source_short_circuit_exact continueValue left right before _).mpr (.inl ⟨after, ran, rfl⟩)

theorem source_short_circuit_taken {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (continueValue : Bool) {left right : Expr} {before middle : SourceState World} {out : SourceOutcome World}
    (first : SourceExprEval interface heap calls frame left before ⟨.ok (.bool continueValue), middle⟩)
    (second : SourceExprEval interface heap calls frame right middle out) :
    SourceExprEval interface heap calls frame (.binary (shortCircuitBinary continueValue) left right) before out :=
  (source_short_circuit_exact continueValue left right before out).mpr (.inr (.inl ⟨middle, first, second⟩))

theorem source_short_circuit_left_fault {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (continueValue : Bool) {left right : Expr} {before after : SourceState World} {fault : NativeWord64.Fault}
    (ran : SourceExprEval interface heap calls frame left before ⟨.error fault, after⟩) :
    SourceExprEval interface heap calls frame (.binary (shortCircuitBinary continueValue) left right) before
      ⟨.error fault, after⟩ :=
  (source_short_circuit_exact continueValue left right before _).mpr (.inr (.inr ⟨fault, after, ran, rfl⟩))

theorem short_circuit_inferred {interface : Interface} {scope : Scope}
    (continueValue : Bool) {left right : Expr} {type : NativeType}
    (inferred : inferExpr interface scope (.binary (shortCircuitBinary continueValue) left right) = some type) :
    type = .bool ∧ inferExpr interface scope left = some .bool ∧
      inferExpr interface scope right = some .bool := by
  obtain ⟨input, first, second, typing⟩ := guarded_binary_inferred inferred
  cases continueValue <;> cases input <;>
    simp only [shortCircuitBinary, Bool.false_eq_true, if_false, if_true, binaryType, reduceCtorEq] at typing
  all_goals cases typing; exact ⟨rfl, first, second⟩

theorem short_circuit_lowering_exact {interface : Interface} {scope : Scope}
    (continueValue : Bool) {left right : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope
      (.binary (shortCircuitBinary continueValue) left right) supply = some output) :
    ∃ first second,
      inferExpr interface scope left = some .bool ∧ inferExpr interface scope right = some .bool ∧
      NativeLowering.expression? interface scope left supply = some first ∧
      NativeLowering.expression? interface scope right
        (NativeLowering.pureTemporary first.supply .bool (.copy first.result)).supply = some second ∧
      output = shortCircuitOutput continueValue first second := by
  cases continueValue <;>
    simp only [shortCircuitBinary, Bool.false_eq_true, if_false, if_true] at compiled
  all_goals rw [NativeLowering.expression?] at compiled
  all_goals
    dsimp only at compiled
    rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
    rcases Option.bind_eq_some_iff.mp compiled with ⟨first, firstCompiled, compiled⟩
    rcases Option.bind_eq_some_iff.mp compiled with ⟨second, secondCompiled, compiled⟩
    have types : type = .bool ∧ inferExpr interface scope left = some .bool ∧
        inferExpr interface scope right = some .bool := by
      first
      | exact short_circuit_inferred false inferred
      | exact short_circuit_inferred true inferred
    cases types.1
    refine ⟨first, second, types.2.1, types.2.2, firstCompiled, secondCompiled, ?_⟩
    exact (Option.some.inj compiled).symm

/-- The recursive family adds boolean branch constructors to proved guarded children. -/
inductive SourceShortCircuitExpression : Expr → Prop where
  | guarded {expression : Expr} (child : SourceGuardedExpression expression) :
      SourceShortCircuitExpression expression
  | connect (continueValue : Bool) {left right : Expr}
      (first : SourceShortCircuitExpression left) (second : SourceShortCircuitExpression right) :
      SourceShortCircuitExpression (.binary (shortCircuitBinary continueValue) left right)

theorem short_circuit_lowering_bounds {interface : Interface} {scope : Scope} {expression : Expr}
    (supported : SourceShortCircuitExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    supply.next < output.supply.next ∧ atomWithin output.supply.next output.result := by
  induction supported generalizing supply output with
  | guarded child =>
      exact ⟨(guarded_lowering_bounds child compiled).1, guarded_result_atom_within child compiled⟩
  | connect continueValue first second firstIH secondIH =>
      obtain ⟨left, right, _, _, leftCompiled, rightCompiled, same⟩ :=
        short_circuit_lowering_exact continueValue compiled
      subst output
      have leftBounds := firstIH leftCompiled
      have rightBounds := secondIH rightCompiled
      have copied : left.supply.next <
          (NativeLowering.pureTemporary left.supply .bool (.copy left.result)).supply.next :=
        NativeIR.fresh_strict left.supply
      refine ⟨leftBounds.1.trans (copied.trans rightBounds.1), ?_⟩
      exact Nat.le_of_lt rightBounds.1

theorem target_empty_frame_scoped (storage : Nat) : TemporariesScoped (targetEmptyFrame storage) :=
  fun _ _ => rfl

theorem target_declare_local_scoped {World : Type} {frame : TargetFrame}
    (hscope : TemporariesScoped frame) (state : TargetState World)
    (name : String) (type : NativeType) (value : TargetValue) :
    TemporariesScoped (targetDeclareLocal frame state name type value).1 := hscope

theorem target_bind_parameters_scoped {World : Type} (parameters : List Parameter)
    (values : List TargetValue) {frame : TargetFrame} {state : TargetState World}
    (hscope : TemporariesScoped frame) {after : TargetFrame} {post : TargetState World}
    (bound : targetBindParameters parameters values frame state = some (after, post)) :
    TemporariesScoped after := by
  induction parameters generalizing values frame state after post with
  | nil =>
      cases values <;> simp only [targetBindParameters, reduceCtorEq, Option.some.injEq] at bound
      cases bound
      exact hscope
  | cons parameter rest ih =>
      cases values with
      | nil => cases bound
      | cons value tail =>
          exact ih tail (target_declare_local_scoped hscope state parameter.name parameter.type value) bound

theorem target_close_block_scoped {World : Type} (marker : TargetFrame)
    (out : TargetBlockOutcome World) : TemporariesScoped (targetCloseBlock marker out).frame := by
  intro identity absent
  change marker.temporaryNames.contains identity = false at absent
  simp only [targetCloseBlock, targetLeaveScope, absent, Bool.false_eq_true, if_false]

theorem target_close_block_state_no_locals {World : Type} {marker : TargetFrame}
    {out : TargetBlockOutcome World} (same : out.frame.nextLocal = marker.nextLocal) :
    (targetCloseBlock marker out).state = out.state := by
  simp only [targetCloseBlock, targetLeaveScope, same, targetDropLocals_empty]

theorem close_block_preserves_temporary_read {World : Type} {interface : Interface}
    {marker : TargetFrame} {out : TargetBlockOutcome World} {identity : Nat} {type : NativeType}
    {value : TargetValue} (live : marker.temporaryNames.contains identity = true)
    (read : TargetAtomEval interface out.frame out.state (.temporary identity type) value) :
    TargetAtomEval interface (targetCloseBlock marker out).frame (targetCloseBlock marker out).state
      (.temporary identity type) value := by
  cases read with
  | temporary selected _ =>
      exact .temporary (by simpa only [targetCloseBlock, targetLeaveScope, live, if_true] using selected) live

theorem close_block_temporary_protection {World : Type} {lower : Nat} {marker current : TargetFrame}
    (hscope : TemporariesScoped marker) (protection : TemporaryProtection lower marker current)
    (state : TargetState World) :
    TemporaryProtection lower marker (targetLeaveScope marker current state).1 := by
  refine ⟨protection.storage, protection.nextLocal, rfl, fun _ _ => rfl, ?_⟩
  intro identity inside
  by_cases live : marker.temporaryNames.contains identity = true
  · simp only [targetLeaveScope, live, if_true]
    exact protection.values identity inside
  · have absent := Bool.eq_false_iff.mpr live
    simp only [targetLeaveScope, if_neg live]
    exact (hscope identity absent).symm

theorem close_block_temporary_bound {World : Type} {marker : TargetFrame} {bound : Nat}
    (bounded : TemporaryNamesBound marker bound) (out : TargetBlockOutcome World) :
    TemporaryNamesBound (targetCloseBlock marker out).frame bound := bounded

theorem fresh_guarded_run_scoped {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {lower upper : Nat} (fresh : FreshGuardedCode lower upper code)
    {frame : TargetFrame} {state : TargetState World} (hscope : TemporariesScoped frame)
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root code frame state out) : TemporariesScoped out.frame := by
  induction code generalizing frame state with
  | nil => cases ran; exact hscope
  | cons instruction rest ih =>
      have head := fresh instruction (by simp only [List.mem_cons, true_or])
      have tail : FreshGuardedCode lower upper rest := fun item member => fresh item (List.mem_cons_of_mem _ member)
      rcases head with ⟨identity, type, operation, same, _, _⟩ | ⟨operation, right, same⟩
      · subst instruction
        cases ran with
        | next first remaining =>
            cases first with
            | temporary _ _ => exact ih tail (declared_temporaries_completeNames hscope _ _) remaining
        | «return» first | resume first _ _ | escape first _ => cases first
      · subst instruction
        cases ran with
        | next first remaining =>
            cases first with
            | numericClear _ _ => exact ih tail hscope remaining
        | «return» first => cases first; exact hscope
        | resume first _ _ | escape first _ => cases first

theorem guarded_expression_run_scoped {World : Type} {interface : Interface} {scope : Scope}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root : List Instruction} {expression : Expr} (guarded : SourceGuardedExpression expression)
    {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    {frame : TargetFrame} {state : TargetState World} (hscope : TemporariesScoped frame)
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root output.code frame state out) : TemporariesScoped out.frame :=
  fresh_guarded_run_scoped (guarded_lowering_bounds guarded compiled).2.1 hscope ran

end Mettapedia.GSLT.LanguageDef.NativeOps
