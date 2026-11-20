import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitution

/-!
# Actual binder-equation steps of the substitution helper

Each step below supplies an instantiation of a member of the fixed finite
program. The transition relation is the existing `ProgramBinders.Rewrites`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open RuleBuilder Templates

abbrev Step : MClosed → MClosed → Prop := ProgramBinders.Rewrites rules.get
abbrev Runs : MClosed → MClosed → Prop := Relation.ReflTransGen Step

theorem of_answer {equation : Equation} {before after : MClosed}
    (inside : equation ∈ rules) (answered : ProgramBinders.Answers equation before after) : Step before after := by
  obtain ⟨index, same⟩ := List.mem_iff_get.mp inside
  refine ⟨index, ?_⟩
  rw [same]
  exact answered

theorem schema_step {n : Nat} {left right : Template n}
    (inside : RuleBuilder.equation left right ∈ rules) (environment : Fin n → MClosed) :
    Step (materialize environment left) (materialize environment right) :=
  of_answer inside (instantiated_answer left right environment)

attribute [local simp] act ret mapTerm visit ns nz rawVar nilEnv consEnv tupleHead
attribute [local simp] activeC returnC mapC visitC liftC bottom shiftC substituteZeroC substituteEnvironmentC
attribute [local simp] shiftOp zeroOp environmentOp shiftIndexC addIndexC zeroIndexC
attribute [local simp] lookupC liftEnvironmentC
attribute [local simp] oneFrame twoFirstFrame twoLastFrame threeFirstFrame threeSecondFrame threeLastFrame
attribute [local simp] RuleBuilder.materialize_tuple

theorem enter_shift (amount cutoff : Nat) (term continuation : MClosed) :
    Step (shiftC amount cutoff term continuation) (mapC (shiftOp amount cutoff) term (bottom continuation)) := by
  have step := schema_step (n := 4) (by change enterShift ∈ rules; simp [rules])
    [encodeNat amount, encodeNat cutoff, term, continuation].get
  simpa using step

theorem enter_zero (argument body : NativeSyntax.Raw Tower.Head) (depth : Nat) (continuation : MClosed) :
    Step (substituteZeroC (quoteRaw argument) depth (quoteRaw body) continuation)
      (mapC (zeroOp argument depth) (quoteRaw body) (bottom continuation)) := by
  have step := schema_step (n := 4) (by change enterZero ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat depth, quoteRaw body, continuation].get
  simpa using step

theorem enter_environment (environment : List (NativeSyntax.Raw Tower.Head)) (body continuation : MClosed) :
    Step (substituteEnvironmentC (encodeRawEnv environment) body continuation)
      (mapC (environmentOp environment) body (bottom continuation)) := by
  have step := schema_step (n := 3) (by change enterEnvironment ∈ rules; simp [rules])
    [encodeRawEnv environment, body, continuation].get
  simpa using step

theorem leave_bottom (value continuation : MClosed) :
    Step (returnC value (bottom continuation)) (resumeC value continuation) := by
  have step := schema_step (n := 2) (by change leave ∈ rules; simp [rules]) [value, continuation].get
  simpa [resumeC] using step

theorem map_constant (operation : MClosed) (name : DeclName) (continuation : MClosed) :
    Step (mapC operation (quoteRaw (.const name)) continuation)
      (returnC (quoteRaw (.const name)) continuation) := by
  have step := schema_step (n := 3) (by change mapConstant ∈ rules; simp [rules])
    [operation, encodeName name, continuation].get
  simpa [quoteRaw] using step

theorem map_head (operation : MClosed) (head : Tower.Head) (continuation : MClosed) :
    Step (mapC operation (quoteRaw (.head head)) continuation)
      (returnC (quoteRaw (.head head)) continuation) := by
  have step := schema_step (n := 3) (by change mapHead ∈ rules; simp [rules])
    [operation, encodeHead head, continuation].get
  simpa [quoteRaw] using step

theorem map_variable (operation : MClosed) (index : Nat) (continuation : MClosed) :
    Step (mapC operation (quoteRaw (.var index)) continuation)
      (activeC "hd-helper-variable" [operation, encodeNat index, continuation]) := by
  have step := schema_step (n := 3) (by change mapVariable ∈ rules; simp [rules])
    [operation, encodeNat index, continuation].get
  simpa [quoteRaw] using step

theorem map_unary {tag : String} {binds : Bool} (inside : mapUnary tag binds ∈ rules)
    (operation child continuation : MClosed) :
    Step (mapC operation (nodeC tag [child]) continuation)
      (visitC binds operation child (oneFrame tag continuation)) := by
  have step := schema_step (n := 3) (by change mapUnary tag binds ∈ rules; exact inside)
    [operation, child, continuation].get
  simpa using step

theorem map_binary {tag : String} {firstBinds secondBinds : Bool}
    (inside : mapBinary tag firstBinds secondBinds ∈ rules) (operation first second continuation : MClosed) :
    Step (mapC operation (nodeC tag [first, second]) continuation)
      (visitC firstBinds operation first (twoFirstFrame tag operation secondBinds second continuation)) := by
  have step := schema_step (n := 4) (by change mapBinary tag firstBinds secondBinds ∈ rules; exact inside)
    [operation, first, second, continuation].get
  simpa using step

theorem map_ternary {tag : String} {firstBinds secondBinds thirdBinds : Bool}
    (inside : mapTernary tag firstBinds secondBinds thirdBinds ∈ rules)
    (operation first second third continuation : MClosed) :
    Step (mapC operation (nodeC tag [first, second, third]) continuation)
      (visitC firstBinds operation first
        (threeFirstFrame tag operation secondBinds second thirdBinds third continuation)) := by
  have step := schema_step (n := 5)
    (by change mapTernary tag firstBinds secondBinds thirdBinds ∈ rules; exact inside)
    [operation, first, second, third, continuation].get
  simpa using step

theorem visit_free (operation term continuation : MClosed) :
    Step (visitC false operation term continuation) (mapC operation term continuation) := by
  have step := schema_step (n := 3) (by change visitFree ∈ rules; simp [rules])
    [operation, term, continuation].get
  simpa using step

theorem visit_bound (operation term continuation : MClosed) :
    Step (visitC true operation term continuation)
      (liftC operation (nodeC "hd-helper-after-lift" [term, continuation])) := by
  have step := schema_step (n := 3) (by change visitBound ∈ rules; simp [rules])
    [operation, term, continuation].get
  simpa using step

theorem after_lift (operation term continuation : MClosed) :
    Step (returnC operation (nodeC "hd-helper-after-lift" [term, continuation]))
      (mapC operation term continuation) := by
  have step := schema_step (n := 3) (by change afterLift ∈ rules; simp [rules])
    [operation, term, continuation].get
  simpa using step

theorem return_one (value : MClosed) (tag : String) (continuation : MClosed) :
    Step (returnC value (oneFrame tag continuation)) (returnC (nodeC tag [value]) continuation) := by
  have step := schema_step (n := 3) (by change returnOne ∈ rules; simp [rules])
    [value, csym tag, continuation].get
  simpa [nodeC] using step

theorem return_two_first (value : MClosed) (tag : String) (operation : MClosed)
    (binds : Bool) (second continuation : MClosed) :
    Step (returnC value (twoFirstFrame tag operation binds second continuation))
      (visitC binds operation second (twoLastFrame tag value continuation)) := by
  have step := schema_step (n := 6) (by change returnTwoFirst ∈ rules; simp [rules])
    [value, csym tag, operation, boundFlag binds, second, continuation].get
  simpa using step

theorem return_two_last (value : MClosed) (tag : String) (first continuation : MClosed) :
    Step (returnC value (twoLastFrame tag first continuation))
      (returnC (nodeC tag [first, value]) continuation) := by
  have step := schema_step (n := 4) (by change returnTwoLast ∈ rules; simp [rules])
    [value, csym tag, first, continuation].get
  simpa [nodeC] using step

theorem return_three_first (value : MClosed) (tag : String) (operation : MClosed)
    (secondBinds : Bool) (second : MClosed) (thirdBinds : Bool) (third continuation : MClosed) :
    Step (returnC value (threeFirstFrame tag operation secondBinds second thirdBinds third continuation))
      (visitC secondBinds operation second (threeSecondFrame tag value operation thirdBinds third continuation)) := by
  have step := schema_step (n := 8) (by change returnThreeFirst ∈ rules; simp [rules])
    [value, csym tag, operation, boundFlag secondBinds, second, boundFlag thirdBinds, third, continuation].get
  simpa using step

theorem return_three_second (value : MClosed) (tag : String) (first operation : MClosed)
    (binds : Bool) (third continuation : MClosed) :
    Step (returnC value (threeSecondFrame tag first operation binds third continuation))
      (visitC binds operation third (threeLastFrame tag first value continuation)) := by
  have step := schema_step (n := 7) (by change returnThreeSecond ∈ rules; simp [rules])
    [value, csym tag, first, operation, boundFlag binds, third, continuation].get
  simpa using step

theorem return_three_last (value : MClosed) (tag : String) (first second continuation : MClosed) :
    Step (returnC value (threeLastFrame tag first second continuation))
      (returnC (nodeC tag [first, second, value]) continuation) := by
  have step := schema_step (n := 5) (by change returnThreeLast ∈ rules; simp [rules])
    [value, csym tag, first, second, continuation].get
  simpa [nodeC] using step

theorem lift_shift (amount cutoff : Nat) (continuation : MClosed) :
    Step (liftC (shiftOp amount cutoff) continuation) (returnC (shiftOp amount (cutoff + 1)) continuation) := by
  have step := schema_step (n := 3) (by change liftShift ∈ rules; simp [rules])
    [encodeNat amount, encodeNat cutoff, continuation].get
  simpa using step

theorem lift_zero (argument : NativeSyntax.Raw Tower.Head) (depth : Nat) (continuation : MClosed) :
    Step (liftC (zeroOp argument depth) continuation) (returnC (zeroOp argument (depth + 1)) continuation) := by
  have step := schema_step (n := 3) (by change liftZero ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat depth, continuation].get
  simpa using step

theorem shift_variable (amount cutoff index : Nat) (continuation : MClosed) :
    Step (activeC "hd-helper-variable" [shiftOp amount cutoff, encodeNat index, continuation])
      (shiftIndexC amount cutoff index index continuation) := by
  have step := schema_step (n := 4) (by change shiftVariable ∈ rules; simp [rules])
    [encodeNat amount, encodeNat cutoff, encodeNat index, continuation].get
  simpa using step

theorem shift_index_cutoff (amount remaining original : Nat) (continuation : MClosed) :
    Step (shiftIndexC amount 0 remaining original continuation) (addIndexC amount original continuation) := by
  have step := schema_step (n := 4) (by change shiftIndexAtCutoff ∈ rules; simp [rules])
    [encodeNat amount, encodeNat remaining, encodeNat original, continuation].get
  simpa using step

theorem shift_index_below (amount cutoff original : Nat) (continuation : MClosed) :
    Step (shiftIndexC amount (cutoff + 1) 0 original continuation)
      (returnC (quoteRaw (.var original)) continuation) := by
  have step := schema_step (n := 4) (by change shiftIndexBelow ∈ rules; simp [rules])
    [encodeNat amount, encodeNat cutoff, encodeNat original, continuation].get
  simpa [quoteRaw] using step

theorem shift_index_next (amount cutoff index original : Nat) (continuation : MClosed) :
    Step (shiftIndexC amount (cutoff + 1) (index + 1) original continuation)
      (shiftIndexC amount cutoff index original continuation) := by
  have step := schema_step (n := 5) (by change shiftIndexNext ∈ rules; simp [rules])
    [encodeNat amount, encodeNat cutoff, encodeNat index, encodeNat original, continuation].get
  simpa using step

theorem add_index_zero (index : Nat) (continuation : MClosed) :
    Step (addIndexC 0 index continuation) (returnC (quoteRaw (.var index)) continuation) := by
  have step := schema_step (n := 2) (by change addIndexZero ∈ rules; simp [rules]) [encodeNat index, continuation].get
  simpa [quoteRaw] using step

theorem add_index_next (amount index : Nat) (continuation : MClosed) :
    Step (addIndexC (amount + 1) index continuation) (addIndexC amount (index + 1) continuation) := by
  have step := schema_step (n := 3) (by change addIndexNext ∈ rules; simp [rules])
    [encodeNat amount, encodeNat index, continuation].get
  simpa using step

theorem zero_variable (argument : NativeSyntax.Raw Tower.Head) (depth index : Nat) (continuation : MClosed) :
    Step (activeC "hd-helper-variable" [zeroOp argument depth, encodeNat index, continuation])
      (zeroIndexC argument depth index depth index continuation) := by
  have step := schema_step (n := 4) (by change zeroVariable ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat depth, encodeNat index, continuation].get
  simpa using step

theorem zero_index_equal (argument : NativeSyntax.Raw Tower.Head) (depth original : Nat) (continuation : MClosed) :
    Step (zeroIndexC argument 0 0 depth original continuation)
      (mapC (shiftOp depth 0) (quoteRaw argument) continuation) := by
  have step := schema_step (n := 4) (by change zeroIndexEqual ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat depth, encodeNat original, continuation].get
  simpa using step

theorem zero_index_above (argument : NativeSyntax.Raw Tower.Head) (index depth predecessor : Nat)
    (continuation : MClosed) :
    Step (zeroIndexC argument 0 (index + 1) depth (predecessor + 1) continuation)
      (returnC (quoteRaw (.var predecessor)) continuation) := by
  have step := schema_step (n := 5) (by change zeroIndexAbove ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat index, encodeNat depth, encodeNat predecessor, continuation].get
  simpa [quoteRaw] using step

theorem zero_index_below (argument : NativeSyntax.Raw Tower.Head) (remaining depth original : Nat)
    (continuation : MClosed) :
    Step (zeroIndexC argument (remaining + 1) 0 depth original continuation)
      (returnC (quoteRaw (.var original)) continuation) := by
  have step := schema_step (n := 5) (by change zeroIndexBelow ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat remaining, encodeNat depth, encodeNat original, continuation].get
  simpa [quoteRaw] using step

theorem zero_index_next (argument : NativeSyntax.Raw Tower.Head) (remaining index depth original : Nat)
    (continuation : MClosed) :
    Step (zeroIndexC argument (remaining + 1) (index + 1) depth original continuation)
      (zeroIndexC argument remaining index depth original continuation) := by
  have step := schema_step (n := 6) (by change zeroIndexNext ∈ rules; simp [rules])
    [quoteRaw argument, encodeNat remaining, encodeNat index, encodeNat depth, encodeNat original, continuation].get
  simpa using step

theorem lift_environment (environment : List (NativeSyntax.Raw Tower.Head)) (continuation : MClosed) :
    Step (liftC (environmentOp environment) continuation)
      (liftEnvironmentC environment (nodeC "hd-helper-env-op-frame" [continuation])) := by
  have step := schema_step (n := 2) (by change liftEnvironment ∈ rules; simp [rules])
    [encodeRawEnv environment, continuation].get
  simpa using step

theorem environment_operation (environment : List (NativeSyntax.Raw Tower.Head)) (continuation : MClosed) :
    Step (returnC (encodeRawEnv environment) (nodeC "hd-helper-env-op-frame" [continuation]))
      (returnC (environmentOp (.var 0 :: environment)) continuation) := by
  have step := schema_step (n := 2) (by change environmentOperation ∈ rules; simp [rules])
    [encodeRawEnv environment, continuation].get
  simpa [encodeRawEnv, quoteRaw] using step

theorem environment_variable (environment : List (NativeSyntax.Raw Tower.Head)) (index : Nat)
    (continuation : MClosed) :
    Step (activeC "hd-helper-variable" [environmentOp environment, encodeNat index, continuation])
      (lookupC environment index continuation) := by
  have step := schema_step (n := 3) (by change environmentVariable ∈ rules; simp [rules])
    [encodeRawEnv environment, encodeNat index, continuation].get
  simpa using step

theorem lookup_empty (index : Nat) (continuation : MClosed) :
    Step (lookupC [] index continuation) (returnC (quoteRaw (.const .anonymous)) continuation) := by
  have step := schema_step (n := 2) (by change lookupEmpty ∈ rules; simp [rules])
    [encodeNat index, continuation].get
  simpa [encodeRawEnv] using step

theorem lookup_zero (first : NativeSyntax.Raw Tower.Head) (rest : List (NativeSyntax.Raw Tower.Head))
    (continuation : MClosed) :
    Step (lookupC (first :: rest) 0 continuation) (returnC (quoteRaw first) continuation) := by
  have step := schema_step (n := 3) (by change lookupZero ∈ rules; simp [rules])
    [quoteRaw first, encodeRawEnv rest, continuation].get
  simpa [encodeRawEnv] using step

theorem lookup_next (first : NativeSyntax.Raw Tower.Head) (rest : List (NativeSyntax.Raw Tower.Head))
    (index : Nat) (continuation : MClosed) :
    Step (lookupC (first :: rest) (index + 1) continuation) (lookupC rest index continuation) := by
  have step := schema_step (n := 4) (by change lookupNext ∈ rules; simp [rules])
    [quoteRaw first, encodeRawEnv rest, encodeNat index, continuation].get
  simpa [encodeRawEnv] using step

theorem lift_environment_empty (continuation : MClosed) :
    Step (liftEnvironmentC [] continuation) (returnC (encodeRawEnv []) continuation) := by
  have step := schema_step (n := 1) (by change liftEnvironmentEmpty ∈ rules; simp [rules]) [continuation].get
  simpa [encodeRawEnv] using step

theorem lift_environment_next (first : NativeSyntax.Raw Tower.Head) (rest : List (NativeSyntax.Raw Tower.Head))
    (continuation : MClosed) :
    Step (liftEnvironmentC (first :: rest) continuation)
      (mapC (shiftOp 1 0) (quoteRaw first) (nodeC "hd-helper-env-head" [encodeRawEnv rest, continuation])) := by
  have step := schema_step (n := 3) (by change liftEnvironmentNext ∈ rules; simp [rules])
    [quoteRaw first, encodeRawEnv rest, continuation].get
  simpa [encodeRawEnv] using step

theorem lift_environment_head (value : NativeSyntax.Raw Tower.Head) (rest : List (NativeSyntax.Raw Tower.Head))
    (continuation : MClosed) :
    Step (returnC (quoteRaw value) (nodeC "hd-helper-env-head" [encodeRawEnv rest, continuation]))
      (liftEnvironmentC rest (nodeC "hd-helper-env-tail" [quoteRaw value, continuation])) := by
  have step := schema_step (n := 3) (by change liftEnvironmentHead ∈ rules; simp [rules])
    [quoteRaw value, encodeRawEnv rest, continuation].get
  simpa using step

theorem lift_environment_tail (rest : List (NativeSyntax.Raw Tower.Head)) (value : NativeSyntax.Raw Tower.Head)
    (continuation : MClosed) :
    Step (returnC (encodeRawEnv rest) (nodeC "hd-helper-env-tail" [quoteRaw value, continuation]))
      (returnC (encodeRawEnv (value :: rest)) continuation) := by
  have step := schema_step (n := 3) (by change liftEnvironmentTail ∈ rules; simp [rules])
    [encodeRawEnv rest, quoteRaw value, continuation].get
  simpa [encodeRawEnv] using step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
