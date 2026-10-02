import Mettapedia.GSLT.LanguageDef.NativeOpsScalarProfiles
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarExpressionLowering

/-!
# Recursive scalar lowering with explicit numeric guards

All unsigned word operations and comparisons are included. Boolean
short-circuit operators, memory reads and calls have separate composition
obligations. Actual guards may return the enclosing function's typed zero;
successful paths retain a fresh private result temporary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom)
open NativeLowering (Expression)

inductive GuardedScalarBinary : Binary → Prop where
  | word (operation : NativeWord64.WordOp) : GuardedScalarBinary (.word operation)
  | compare (operation : NativeWord64.Comparison) : GuardedScalarBinary (.compare operation)

inductive SourceGuardedExpression : Expr → Prop where
  | leaf {expression : Expr} (leaf : SourceLeaf expression) : SourceGuardedExpression expression
  | unary (operation : Unary) {operand : Expr} (child : SourceGuardedExpression operand) :
      SourceGuardedExpression (.unary operation operand)
  | binary {operation : Binary} (scalar : GuardedScalarBinary operation)
      {left right : Expr} (first : SourceGuardedExpression left)
      (second : SourceGuardedExpression right) : SourceGuardedExpression (.binary operation left right)

theorem guarded_scalar_not_and {operation : Binary} (scalar : GuardedScalarBinary operation) :
    operation ≠ .and := by cases scalar <;> intro impossible <;> cases impossible

theorem guarded_scalar_not_or {operation : Binary} (scalar : GuardedScalarBinary operation) :
    operation ≠ .or := by cases scalar <;> intro impossible <;> cases impossible

theorem guarded_scalar_operands {operation : Binary} (scalar : GuardedScalarBinary operation)
    (left right : Expr) : sourceStrictOperands? (.binary operation left right) = some [left, right] := by
  cases scalar <;> rfl

theorem unchecked_expression_is_guarded {expression : Expr} (scalar : SourceScalarExpression expression) :
    SourceGuardedExpression expression := by
  induction scalar with
  | leaf leaf => exact .leaf leaf
  | unary operation child ih => exact .unary operation ih
  | binary unchecked first second firstIH secondIH =>
      cases unchecked <;> exact .binary (by constructor) firstIH secondIH

theorem guarded_binary_lowering_exact {interface : Interface} {scope : Scope}
    {operation : Binary} (scalar : GuardedScalarBinary operation)
    {left right : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.binary operation left right) supply = some output) :
    ∃ type first second, inferExpr interface scope (.binary operation left right) = some type ∧
      NativeLowering.expression? interface scope left supply = some first ∧
      NativeLowering.expression? interface scope right first.supply = some second ∧
      output = NativeLowering.prependCode
        (first.code ++ second.code ++ NativeLowering.numericGuard operation second.result)
        (NativeLowering.pureTemporary second.supply type (.binary operation first.result second.result)) := by
  cases scalar <;> rw [NativeLowering.expression?] at compiled
  all_goals
    rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
    rcases Option.bind_eq_some_iff.mp compiled with ⟨first, firstCompiled, compiled⟩
    rcases Option.bind_eq_some_iff.mp compiled with ⟨second, secondCompiled, compiled⟩
    exact ⟨type, first, second, inferred, firstCompiled, secondCompiled, (Option.some.inj compiled).symm⟩

theorem guarded_unary_inferred {interface : Interface} {scope : Scope}
    {operation : Unary} {operand : Expr} {type : NativeType}
    (inferred : inferExpr interface scope (.unary operation operand) = some type) :
    ∃ input, inferExpr interface scope operand = some input ∧ unaryType operation input = some type := by
  rw [inferExpr] at inferred
  exact Option.bind_eq_some_iff.mp inferred

theorem guarded_binary_inferred {interface : Interface} {scope : Scope}
    {operation : Binary} {left right : Expr} {type : NativeType}
    (inferred : inferExpr interface scope (.binary operation left right) = some type) :
    ∃ input, inferExpr interface scope left = some input ∧
      inferExpr interface scope right = some input ∧ binaryType operation input = some type := by
  rw [inferExpr] at inferred
  rcases Option.bind_eq_some_iff.mp inferred with ⟨leftType, first, inferred⟩
  rcases Option.bind_eq_some_iff.mp inferred with ⟨rightType, second, inferred⟩
  split at inferred
  · rename_i same
    cases same
    exact ⟨_, first, second, inferred⟩
  · cases inferred

/-- The emitted fragment declares private temporaries and tests numeric guards. -/
def FreshGuardedCode (lower upper : Nat) (code : List Instruction) : Prop :=
  ∀ instruction ∈ code,
    (∃ identity type operation, instruction = .temporary identity type operation ∧
      lower < identity ∧ identity ≤ upper) ∨
    (∃ operation right, instruction = .checkedNumericGuard operation right)

theorem fresh_guarded_code_weaken {lower upper smaller larger : Nat} {code : List Instruction}
    (low : smaller ≤ lower) (high : upper ≤ larger) (fresh : FreshGuardedCode lower upper code) :
    FreshGuardedCode smaller larger code := by
  intro instruction member
  rcases fresh instruction member with ⟨identity, type, operation, same, above, within⟩ | guard
  · exact .inl ⟨identity, type, operation, same, low.trans_lt above, within.trans high⟩
  · exact .inr guard

theorem fresh_guarded_code_append {lower upper : Nat} {first second : List Instruction}
    (left : FreshGuardedCode lower upper first) (right : FreshGuardedCode lower upper second) :
    FreshGuardedCode lower upper (first ++ second) := by
  intro instruction member
  rcases List.mem_append.mp member with member | member
  · exact left instruction member
  · exact right instruction member

theorem fresh_guarded_code_of_pure {lower upper : Nat} {code : List Instruction}
    (fresh : FreshPureCode lower upper code) : FreshGuardedCode lower upper code :=
  fun instruction member => .inl (fresh instruction member)

theorem numeric_guard_has_no_temporary (operation : Binary) (right : Atom) (lower upper : Nat) :
    FreshGuardedCode lower upper (NativeLowering.numericGuard operation right) := by
  intro instruction member
  cases operation with
  | word operation =>
      cases operation <;> simp only [NativeLowering.numericGuard, List.not_mem_nil] at member
      all_goals cases List.mem_singleton.mp member; exact .inr ⟨_, _, rfl⟩
  | compare comparison => cases member
  | and => cases member
  | or => cases member

theorem guarded_lowering_bounds {interface : Interface} {scope : Scope} {expression : Expr}
    (guarded : SourceGuardedExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    supply.next < output.supply.next ∧ FreshGuardedCode supply.next output.supply.next output.code ∧
      ∃ type, output.result = .temporary output.supply.next type := by
  induction guarded generalizing supply output with
  | leaf leaf =>
      obtain ⟨type, operation, same⟩ := scalar_leaf_lowering_exact leaf compiled
      subst output
      exact ⟨NativeIR.fresh_strict supply,
        fresh_guarded_code_of_pure (fresh_pure_code_temporary type operation
          (NativeIR.fresh_strict supply) (Nat.le_refl _)), type, rfl⟩
  | unary operation child ih =>
      obtain ⟨type, childOutput, _, childCompiled, same⟩ := scalar_unary_lowering_exact compiled
      subst output
      rcases ih childCompiled with ⟨advanced, fresh, _⟩
      have next := NativeIR.fresh_strict childOutput.supply
      refine ⟨advanced.trans next, ?_, type, rfl⟩
      exact fresh_guarded_code_append
        (fresh_guarded_code_weaken (Nat.le_refl _) (Nat.le_of_lt next) fresh)
        (fresh_guarded_code_of_pure (fresh_pure_code_temporary type (.unary operation childOutput.result)
          (advanced.trans next) (Nat.le_refl _)))
  | binary scalar first second firstIH secondIH =>
      obtain ⟨type, firstOutput, secondOutput, _, firstCompiled, secondCompiled, same⟩ :=
        guarded_binary_lowering_exact scalar compiled
      subst output
      rcases firstIH firstCompiled with ⟨firstAdvanced, firstFresh, _⟩
      rcases secondIH secondCompiled with ⟨secondAdvanced, secondFresh, _⟩
      have next := NativeIR.fresh_strict secondOutput.supply
      refine ⟨firstAdvanced.trans (secondAdvanced.trans next), ?_, type, rfl⟩
      apply fresh_guarded_code_append
      · apply fresh_guarded_code_append
        · apply fresh_guarded_code_append
          · exact fresh_guarded_code_weaken (Nat.le_refl _)
              (Nat.le_of_lt (secondAdvanced.trans next)) firstFresh
          · exact fresh_guarded_code_weaken (Nat.le_of_lt firstAdvanced) (Nat.le_of_lt next) secondFresh
        · exact numeric_guard_has_no_temporary _ _ _ _
      · exact fresh_guarded_code_of_pure (fresh_pure_code_temporary type
          (.binary _ firstOutput.result secondOutput.result)
          (firstAdvanced.trans (secondAdvanced.trans next)) (Nat.le_refl _))

theorem guarded_result_atom_within {interface : Interface} {scope : Scope} {expression : Expr}
    (guarded : SourceGuardedExpression expression) {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) :
    atomWithin output.supply.next output.result := by
  obtain ⟨_, _, type, same⟩ := guarded_lowering_bounds guarded compiled
  rw [same]
  exact Nat.le_refl _

theorem guarded_temporary_bound_mono {frame : TargetFrame} {lower upper : Nat}
    (bounded : TemporaryNamesBound frame lower) (increase : lower ≤ upper) :
    TemporaryNamesBound frame upper :=
  fun identity live => Nat.le_trans (bounded identity live) increase

end Mettapedia.GSLT.LanguageDef.NativeOps
