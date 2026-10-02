import Mettapedia.GSLT.LanguageDef.NativeOpsLocalControlProfiles

/-!
# Actual statement lowering and continuation boundaries

These laws expose the existing lowerer, including location-before-value order
and the complete while label/scope suffix. They do not execute a replacement
loop machine. The following execution proofs use the emitted continuation
and the existing TargetRun label lookup.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Atom Supply LoopLabels Label)
open NativeLowering (Expression Block)

mutual
  /-- The concrete structured local family uses the existing expression
      implementation; allocation, release and function calls are separate. -/
  inductive SourceLocalControlStatement : Statement → Prop where
    | declare (name : String) (type : NativeType) {value : Expr}
        (supported : SourceShortCircuitExpression value) :
        SourceLocalControlStatement (.declare name type value)
    | set (name : String) {value : Expr} (supported : SourceShortCircuitExpression value) :
        SourceLocalControlStatement (.set (.variable name) value)
    | branch {condition : Expr} {yes no : List Statement}
        (tested : SourceShortCircuitExpression condition)
        (whenTrue : SourceLocalControlBlock yes) (whenFalse : SourceLocalControlBlock no) :
        SourceLocalControlStatement (.branch condition yes no)
    | while {condition : Expr} {body : List Statement}
        (tested : SourceShortCircuitExpression condition) (iteration : SourceLocalControlBlock body) :
        SourceLocalControlStatement (.while condition body)
    | break : SourceLocalControlStatement .break
    | continue : SourceLocalControlStatement .continue
    | effect {value : Expr} (supported : SourceShortCircuitExpression value) :
        SourceLocalControlStatement (.effect value)
    | returnUnit : SourceLocalControlStatement (.return none)
    | returnValue {value : Expr} (supported : SourceShortCircuitExpression value) :
        SourceLocalControlStatement (.return (some value))
    | block {body : List Statement} (supported : SourceLocalControlBlock body) :
        SourceLocalControlStatement (.block body)

  inductive SourceLocalControlBlock : List Statement → Prop where
    | nil : SourceLocalControlBlock []
    | cons {first : Statement} {rest : List Statement}
        (head : SourceLocalControlStatement first) (tail : SourceLocalControlBlock rest) :
        SourceLocalControlBlock (first :: rest)
end

def LoopLabelsWithin (bound : Nat) (loops : List LoopLabels) : Prop :=
  ∀ active ∈ loops, active.entry.identity ≤ bound ∧ active.exit.identity ≤ bound

theorem loop_labels_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
    {loops : List LoopLabels} (bounded : LoopLabelsWithin lower loops) : LoopLabelsWithin upper loops :=
  fun active member => ⟨(bounded active member).1.trans inside, (bounded active member).2.trans inside⟩

theorem declaration_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {name : String} {type : NativeType} {initializer : Expr}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.declare name type initializer)
      supply = some output) :
    ∃ nextScope value,
      checkStatement interface result loops.length scope (.declare name type initializer) = some nextScope ∧
      NativeLowering.expression? interface scope initializer supply = some value ∧
      output = ⟨value.code ++ [.declareLocal name type value.result], nextScope, value.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨value, lowered, compiled⟩
  exact ⟨nextScope, value, checked, lowered, (Option.some.inj compiled).symm⟩

theorem declaration_checked_type {interface : Interface} {result : NativeType} {loops : Nat}
    {scope nextScope : Scope} {name : String} {type : NativeType} {initializer : Expr}
    (checked : checkStatement interface result loops scope (.declare name type initializer) = some nextScope) :
    inferExpr interface scope initializer = some type ∧ nextScope = (name, type) :: scope := by
  rw [checkStatement] at checked
  split at checked
  · cases checked
  · rcases Option.bind_eq_some_iff.mp checked with ⟨actual, inferred, checked⟩
    split at checked
    · rename_i same
      cases same
      exact ⟨inferred, (Option.some.inj checked).symm⟩
    · cases checked

theorem set_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {location value : Expr}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.set location value)
      supply = some output) :
    ∃ nextScope place replacement,
      checkStatement interface result loops.length scope (.set location value) = some nextScope ∧
      NativeLowering.location? interface scope location supply = some place ∧
      NativeLowering.expression? interface scope value place.supply = some replacement ∧
      output = ⟨place.code ++ replacement.code ++ [.write place.result replacement.result],
        nextScope, replacement.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨place, located, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨replacement, lowered, compiled⟩
  exact ⟨nextScope, place, replacement, checked, located, lowered, (Option.some.inj compiled).symm⟩

theorem set_checked_types {interface : Interface} {result : NativeType} {loops : Nat}
    {scope nextScope : Scope} {location value : Expr}
    (checked : checkStatement interface result loops scope (.set location value) = some nextScope) :
    ∃ type, inferLocation interface scope location = some type ∧
      inferExpr interface scope value = some type ∧ nextScope = scope := by
  rw [checkStatement] at checked
  rcases Option.bind_eq_some_iff.mp checked with ⟨locationType, located, checked⟩
  rcases Option.bind_eq_some_iff.mp checked with ⟨valueType, inferred, checked⟩
  split at checked
  · rename_i same
    cases same
    exact ⟨locationType, located, inferred, (Option.some.inj checked).symm⟩
  · cases checked

theorem local_set_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {name : String} {value : Expr}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.set (.variable name) value)
      supply = some output) :
    ∃ type replacement,
      lookupVariable scope name = some type ∧ inferExpr interface scope value = some type ∧
      NativeLowering.expression? interface scope value supply = some replacement ∧
      output = ⟨replacement.code ++ [.write (.localAddress name type) replacement.result],
        scope, replacement.supply⟩ := by
  obtain ⟨nextScope, place, replacement, checked, located, lowered, same⟩ := set_lowering_exact compiled
  obtain ⟨type, lookup, inferred, scopeSame⟩ := set_checked_types checked
  simp only [inferLocation] at lookup
  have placeSame : place = ⟨[], .localAddress name type, supply⟩ := by
    simpa only [NativeLowering.location?, inferLocation, lookup, bind, Option.bind_some,
      Option.some.injEq] using located.symm
  subst place
  subst nextScope
  exact ⟨type, replacement, lookup, inferred, lowered, by simpa only [List.nil_append] using same⟩

theorem branch_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {condition : Expr} {whenTrue whenFalse : List Statement}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.branch condition whenTrue whenFalse)
      supply = some output) :
    ∃ nextScope test yes no,
      checkStatement interface result loops.length scope (.branch condition whenTrue whenFalse) = some nextScope ∧
      NativeLowering.expression? interface scope condition supply = some test ∧
      NativeLowering.block? interface result loops scope whenTrue test.supply = some yes ∧
      NativeLowering.block? interface result loops scope whenFalse yes.supply = some no ∧
      output = ⟨test.code ++ [.branch (.value test.result) yes.code no.code], nextScope, no.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨test, lowered, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨yes, yesLowered, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨no, noLowered, compiled⟩
  exact ⟨nextScope, test, yes, no, checked, lowered, yesLowered, noLowered,
    (Option.some.inj compiled).symm⟩

def freshLoopLabels (supply : Supply) : LoopLabels :=
  ⟨⟨.entry, (NativeIR.fresh supply).1⟩, ⟨.exit, (NativeIR.fresh (NativeIR.fresh supply).2).1⟩⟩

theorem while_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {condition : Expr} {body : List Statement}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.while condition body)
      supply = some output) :
    ∃ nextScope test iteration,
      checkStatement interface result loops.length scope (.while condition body) = some nextScope ∧
      NativeLowering.expression? interface scope condition (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test ∧
      NativeLowering.block? interface result (freshLoopLabels supply :: loops) scope body test.supply = some iteration ∧
      output = ⟨[.label (freshLoopLabels supply).entry,
        .scope (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry]), .label (freshLoopLabels supply).exit],
        nextScope, iteration.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨test, lowered, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨iteration, bodyLowered, compiled⟩
  exact ⟨nextScope, test, iteration, checked, lowered, bodyLowered, (Option.some.inj compiled).symm⟩

theorem effect_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {expression : Expr} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.effect expression) supply = some output) :
    ∃ nextScope value, checkStatement interface result loops.length scope (.effect expression) = some nextScope ∧
      NativeLowering.expression? interface scope expression supply = some value ∧
      output = ⟨value.code, nextScope, value.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨value, lowered, compiled⟩
  exact ⟨nextScope, value, checked, lowered, (Option.some.inj compiled).symm⟩

theorem return_value_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {expression : Expr} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.return (some expression)) supply = some output) :
    ∃ nextScope value, checkStatement interface result loops.length scope (.return (some expression)) = some nextScope ∧
      NativeLowering.expression? interface scope expression supply = some value ∧
      output = ⟨value.code ++ [.return value.result], nextScope, value.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨value, lowered, compiled⟩
  exact ⟨nextScope, value, checked, lowered, (Option.some.inj compiled).symm⟩

theorem block_statement_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {body : List Statement} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.block body) supply = some output) :
    ∃ nextScope value, checkStatement interface result loops.length scope (.block body) = some nextScope ∧
      NativeLowering.block? interface result loops scope body supply = some value ∧
      output = ⟨[.scope value.code], nextScope, value.supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨value, lowered, compiled⟩
  exact ⟨nextScope, value, checked, lowered, (Option.some.inj compiled).symm⟩

theorem block_cons_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {first : Statement} {rest : List Statement}
    {supply : Supply} {output : Block}
    (compiled : NativeLowering.block? interface result loops scope (first :: rest) supply = some output) :
    ∃ head tail, NativeLowering.statement? interface result loops scope first supply = some head ∧
      NativeLowering.block? interface result loops head.scope rest head.supply = some tail ∧
      output = ⟨head.code ++ tail.code, tail.scope, tail.supply⟩ := by
  rw [NativeLowering.block?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨head, lowered, compiled⟩
  rcases Option.bind_eq_some_iff.mp compiled with ⟨tail, tailLowered, compiled⟩
  exact ⟨head, tail, lowered, tailLowered, (Option.some.inj compiled).symm⟩

theorem break_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope .break supply = some output) :
    ∃ active outer, loops = active :: outer ∧ output = ⟨[.jump active.exit], scope, supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  cases loops with
  | nil => cases compiled
  | cons active outer =>
      have scopeSame : nextScope = scope := by
        simpa only [checkStatement, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, if_false, Option.some.injEq] using checked.symm
      subst nextScope
      exact ⟨active, outer, rfl, (Option.some.inj compiled).symm⟩

theorem continue_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope .continue supply = some output) :
    ∃ active outer, loops = active :: outer ∧ output = ⟨[.jump active.entry], scope, supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  cases loops with
  | nil => cases compiled
  | cons active outer =>
      have scopeSame : nextScope = scope := by
        simpa only [checkStatement, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, if_false, Option.some.injEq] using checked.symm
      subst nextScope
      exact ⟨active, outer, rfl, (Option.some.inj compiled).symm⟩

theorem return_unit_lowering_exact {interface : Interface} {result : NativeType}
    {loops : List LoopLabels} {scope : Scope} {supply : Supply} {output : Block}
    (compiled : NativeLowering.statement? interface result loops scope (.return none) supply = some output) :
    result = .unit ∧ output = ⟨[.return .unit], scope, supply⟩ := by
  rw [NativeLowering.statement?] at compiled
  rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, checked, compiled⟩
  rw [checkStatement] at checked
  split at checked
  · rename_i resultSame
    cases resultSame
    cases Option.some.inj checked
    exact ⟨rfl, (Option.some.inj compiled).symm⟩
  · cases checked

theorem fresh_loop_labels_above_supply (supply : Supply) :
    supply.next < (freshLoopLabels supply).entry.identity ∧
      (freshLoopLabels supply).entry.identity < (freshLoopLabels supply).exit.identity := by
  exact ⟨NativeIR.fresh_strict supply, NativeIR.fresh_strict (NativeIR.fresh supply).2⟩

theorem loop_root_after_entry (supply : Supply) (iteration continuation : List Instruction) :
    targetAfterLabel? ([.label (freshLoopLabels supply).entry, .scope iteration,
      .label (freshLoopLabels supply).exit] ++ continuation) (freshLoopLabels supply).entry =
      some (.scope iteration :: .label (freshLoopLabels supply).exit :: continuation) := by
  simp only [List.cons_append, List.nil_append, targetAfterLabel?, if_true]

theorem loop_root_after_exit (supply : Supply) (iteration continuation : List Instruction) :
    targetAfterLabel? ([.label (freshLoopLabels supply).entry, .scope iteration,
      .label (freshLoopLabels supply).exit] ++ continuation) (freshLoopLabels supply).exit = some continuation := by
  simp only [List.cons_append, List.nil_append, targetAfterLabel?, freshLoopLabels,
    if_true]
  rfl

end Mettapedia.GSLT.LanguageDef.NativeOps
