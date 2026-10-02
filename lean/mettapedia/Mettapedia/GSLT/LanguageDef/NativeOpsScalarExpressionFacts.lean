import Mettapedia.GSLT.LanguageDef.NativeOpsExpressionLeaves
import Mettapedia.GSLT.LanguageDef.NativeOpsLoweringComposition

/-!
# Structural bounds of recursive scalar expression lowering

This fragment contains admitted leaves, unary operations, comparisons and
unsigned operations without a numeric refusal guard. Every emitted instruction
is an ordinary private temporary declaration. The original runtime state is
preserved even when it already carries a fault; observing a recursive source
expression additionally requires the source's first-fault discipline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeLowering (Expression)

/-- Binary operations whose actual emission has no numeric guard. -/
inductive UncheckedScalarBinary : Binary → Prop where
  | add : UncheckedScalarBinary (.word .add)
  | sub : UncheckedScalarBinary (.word .sub)
  | mul : UncheckedScalarBinary (.word .mul)
  | band : UncheckedScalarBinary (.word .band)
  | bor : UncheckedScalarBinary (.word .bor)
  | bxor : UncheckedScalarBinary (.word .bxor)
  | compare (operation : NativeWord64.Comparison) : UncheckedScalarBinary (.compare operation)

inductive SourceScalarExpression : Expr → Prop where
  | leaf {expression : Expr} (leaf : SourceLeaf expression) : SourceScalarExpression expression
  | unary (operation : Unary) {operand : Expr} (child : SourceScalarExpression operand) :
      SourceScalarExpression (.unary operation operand)
  | binary {operation : Binary} (unchecked : UncheckedScalarBinary operation)
      {left right : Expr} (first : SourceScalarExpression left)
      (second : SourceScalarExpression right) : SourceScalarExpression (.binary operation left right)

theorem unchecked_scalar_not_and {operation : Binary}
    (unchecked : UncheckedScalarBinary operation) : operation ≠ .and := by
  cases unchecked <;> intro impossible <;> cases impossible

theorem unchecked_scalar_not_or {operation : Binary}
    (unchecked : UncheckedScalarBinary operation) : operation ≠ .or := by
  cases unchecked <;> intro impossible <;> cases impossible

theorem unchecked_scalar_numeric_guard {operation : Binary}
    (unchecked : UncheckedScalarBinary operation) (right : Atom) :
    NativeLowering.numericGuard operation right = [] := by
  cases unchecked <;> rfl

theorem scalar_leaf_lowering_exact {interface : Interface} {scope : Scope}
    {expression : Expr} (leaf : SourceLeaf expression) {supply : NativeIR.Supply}
    {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    ∃ type operation, output = NativeLowering.pureTemporary supply type operation := by
  cases leaf <;> rw [NativeLowering.expression?] at compiled
  all_goals
    rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, lowered⟩
    cases Option.some.inj lowered
    exact ⟨_, _, rfl⟩

theorem scalar_unary_lowering_exact {interface : Interface} {scope : Scope}
    {operation : Unary} {operand : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.unary operation operand) supply = some output) :
    ∃ type child, inferExpr interface scope (.unary operation operand) = some type ∧
      NativeLowering.expression? interface scope operand supply = some child ∧
      output = NativeLowering.prependCode child.code
        (NativeLowering.pureTemporary child.supply type (.unary operation child.result)) := by
  rw [NativeLowering.expression?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨child, childCompiled, compiled⟩
  exact ⟨type, child, inferred, childCompiled, (Option.some.inj compiled).symm⟩

theorem scalar_binary_lowering_exact {interface : Interface} {scope : Scope}
    {operation : Binary} (unchecked : UncheckedScalarBinary operation)
    {left right : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.binary operation left right) supply = some output) :
    ∃ type first second, inferExpr interface scope (.binary operation left right) = some type ∧
      NativeLowering.expression? interface scope left supply = some first ∧
      NativeLowering.expression? interface scope right first.supply = some second ∧
      output = NativeLowering.prependCode (first.code ++ second.code)
        (NativeLowering.pureTemporary second.supply type (.binary operation first.result second.result)) := by
  cases unchecked <;> rw [NativeLowering.expression?] at compiled
  all_goals
    rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
    rcases Option.bind_eq_some_iff.mp compiled with ⟨first, firstCompiled, compiled⟩
    rcases Option.bind_eq_some_iff.mp compiled with ⟨second, secondCompiled, compiled⟩
    refine ⟨type, first, second, inferred, firstCompiled, secondCompiled, ?_⟩
    simpa only [NativeLowering.numericGuard, List.append_nil] using (Option.some.inj compiled).symm

/-- The actual fragment has only declarations strictly above the old supply. -/
def FreshPureCode (lower upper : Nat) (code : List Instruction) : Prop :=
  ∀ instruction ∈ code, ∃ identity type operation,
    instruction = .temporary identity type operation ∧ lower < identity ∧ identity ≤ upper

theorem fresh_pure_code_nil (lower upper : Nat) : FreshPureCode lower upper [] := by
  intro instruction member; cases member

theorem fresh_pure_code_weaken {lower upper smaller larger : Nat} {code : List Instruction}
    (lowerBound : smaller ≤ lower) (upperBound : upper ≤ larger)
    (fresh : FreshPureCode lower upper code) : FreshPureCode smaller larger code := by
  intro instruction member
  rcases fresh instruction member with ⟨identity, type, operation, same, above, within⟩
  exact ⟨identity, type, operation, same, lowerBound.trans_lt above, within.trans upperBound⟩

theorem fresh_pure_code_append {lower upper : Nat} {first second : List Instruction}
    (left : FreshPureCode lower upper first) (right : FreshPureCode lower upper second) :
    FreshPureCode lower upper (first ++ second) := by
  intro instruction member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact left instruction inFirst
  · exact right instruction inSecond

theorem fresh_pure_code_temporary {lower upper identity : Nat}
    (type : NativeType) (operation : NativeIR.PureOperation)
    (above : lower < identity) (within : identity ≤ upper) :
    FreshPureCode lower upper [.temporary identity type operation] := by
  intro instruction member
  cases List.mem_singleton.mp member
  exact ⟨identity, type, operation, rfl, above, within⟩

theorem scalar_lowering_bounds {interface : Interface} {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    supply.next < output.supply.next ∧ FreshPureCode supply.next output.supply.next output.code ∧
      ∃ type, output.result = .temporary output.supply.next type := by
  induction scalar generalizing supply output with
  | leaf leaf =>
      obtain ⟨type, operation, same⟩ := scalar_leaf_lowering_exact leaf compiled
      subst output
      refine ⟨NativeIR.fresh_strict supply, ?_, type, rfl⟩
      exact fresh_pure_code_temporary type operation (NativeIR.fresh_strict supply) (Nat.le_refl _)
  | unary operation child ih =>
      obtain ⟨type, childOutput, _, childCompiled, same⟩ := scalar_unary_lowering_exact compiled
      subst output
      rcases ih childCompiled with ⟨advanced, fresh, _⟩
      change supply.next < (NativeIR.fresh childOutput.supply).2.next ∧ _
      have next := NativeIR.fresh_strict childOutput.supply
      refine ⟨advanced.trans next, ?_, type, rfl⟩
      apply fresh_pure_code_append
      · exact fresh_pure_code_weaken (Nat.le_refl _) (Nat.le_of_lt next) fresh
      · exact fresh_pure_code_temporary type (.unary operation childOutput.result)
          (advanced.trans next) (Nat.le_refl _)
  | binary unchecked first second firstIH secondIH =>
      obtain ⟨type, firstOutput, secondOutput, _, firstCompiled, secondCompiled, same⟩ :=
        scalar_binary_lowering_exact unchecked compiled
      subst output
      rcases firstIH firstCompiled with ⟨firstAdvanced, firstFresh, _⟩
      rcases secondIH secondCompiled with ⟨secondAdvanced, secondFresh, _⟩
      have next := NativeIR.fresh_strict secondOutput.supply
      refine ⟨firstAdvanced.trans (secondAdvanced.trans next), ?_, type, rfl⟩
      apply fresh_pure_code_append
      · apply fresh_pure_code_append
        · exact fresh_pure_code_weaken (Nat.le_refl _) (Nat.le_of_lt (secondAdvanced.trans next)) firstFresh
        · exact fresh_pure_code_weaken (Nat.le_of_lt firstAdvanced) (Nat.le_of_lt next) secondFresh
      · exact fresh_pure_code_temporary type _
          (firstAdvanced.trans (secondAdvanced.trans next)) (Nat.le_refl _)

theorem scalar_result_atom_within {interface : Interface} {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    atomWithin output.supply.next output.result := by
  obtain ⟨_, _, type, same⟩ := scalar_lowering_bounds scalar compiled
  rw [same]
  exact Nat.le_refl _

/-- Raw runs of this fragment cannot change context, heap or external state. -/
theorem fresh_pure_run_shape {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {lower upper : Nat} (fresh : FreshPureCode lower upper code)
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (bounded : TemporaryNamesBound frame upper)
    (ran : TargetRun interface heap calls result root code frame state out) :
    out.flow = .normal ∧ out.state = state ∧
      TemporaryProtection lower frame out.frame ∧ TemporaryNamesBound out.frame upper := by
  induction code generalizing frame state with
  | nil =>
      cases ran
      exact ⟨rfl, rfl, temporary_protection_refl lower frame, bounded⟩
  | cons instruction rest ih =>
      obtain ⟨identity, type, operation, same, above, within⟩ := fresh instruction (by simp)
      subst instruction
      have tailFresh : FreshPureCode lower upper rest := fun item member => fresh item (by simp [member])
      cases ran with
      | next first tail =>
          cases first with
          | temporary unused computed =>
              rename_i value
              have nextBounded := declared_temporary_bound bounded (Nat.le_refl _) within value
              rcases ih tailFresh nextBounded tail with ⟨normal, unchanged, protection, finalBounded⟩
              exact ⟨normal, unchanged,
                temporary_protection_trans (declare_temporary_protects frame _ above) protection,
                finalBounded⟩
      | «return» first | resume first _ _ | escape first _ => cases first

theorem scalar_target_run_shape {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root : List Instruction} {scope : Scope} {expression : Expr}
    (scalar : SourceScalarExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (bounded : TemporaryNamesBound frame supply.next)
    (ran : TargetRun interface heap calls result root output.code frame state out) :
    out.flow = .normal ∧ out.state = state ∧
      TemporaryProtection supply.next frame out.frame ∧ TemporaryNamesBound out.frame output.supply.next := by
  rcases scalar_lowering_bounds scalar compiled with ⟨advanced, fresh, _⟩
  have wider : TemporaryNamesBound frame output.supply.next :=
    fun identity live => (bounded identity live).trans (Nat.le_of_lt advanced)
  exact fresh_pure_run_shape fresh wider ran

end Mettapedia.GSLT.LanguageDef.NativeOps
