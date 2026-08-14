import Mettapedia.GSLT.LanguageDef.CompiledPlanFiniteSupportCompilation
import Mettapedia.GSLT.LanguageDef.EpochStampedSlotCompilation

/-!
# Epoch-stamped dense slots for compiled plans

A locally supported compiled plan declares a finite dense variable inventory
for every rule.  The maximum inventory width therefore allocates one
query-local slot buffer, and every rule-local variable reference can be
compiled to `Fin width`.  This is the static certificate needed by the generic
epoch-stamped buffer realization: attempts reuse one allocation and select a
fresh logical view without clearing the complete width.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanEpochSlotCompilation

open CompiledPlanLowering
open CompiledPlanFiniteSupportCompilation
open CompiledPlanAdmission
open EpochStampedSlotCompilation

/-- Query-local width used by the physical compiled runtime. -/
def maximumVariableCount : TypedProgram -> Nat
  | [] => 0
  | rule :: rules =>
      max rule.variableCount.toNat (maximumVariableCount rules)

theorem variableCount_le_maximumVariableCount_of_mem
    {source : TypedProgram} {rule : TypedRule} (member : rule ∈ source) :
    rule.variableCount.toNat ≤ maximumVariableCount source := by
  induction source with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [List.mem_cons] at member
      rcases member with same | member
      · subst rule
        exact Nat.le_max_left _ _
      · exact le_trans (inductionHypothesis member)
          (Nat.le_max_right _ _)

/-- Lower an unchecked natural slot to the finite query-local carrier. -/
def compileSlot? (width slot : Nat) : Option (Fin width) :=
  if bounded : slot < width then some ⟨slot, bounded⟩ else none

def compileSlots? (width : Nat) : List Nat -> Option (List (Fin width))
  | [] => some []
  | slot :: slots => do
      let compiled <- compileSlot? width slot
      let tail <- compileSlots? width slots
      some (compiled :: tail)

theorem compileSlot?_success
    {width slot : Nat} {compiled : Fin width}
    (success : compileSlot? width slot = some compiled) :
    compiled.val = slot := by
  unfold compileSlot? at success
  split at success
  · exact (congrArg Fin.val (Option.some.inj success)).symm
  · simp at success

theorem compileSlots?_values
    {width : Nat} {source : List Nat} {compiled : List (Fin width)}
    (success : compileSlots? width source = some compiled) :
    compiled.map Fin.val = source := by
  induction source generalizing compiled with
  | nil =>
      simp [compileSlots?] at success
      subst compiled
      rfl
  | cons slot slots inductionHypothesis =>
      simp only [compileSlots?, Option.bind_eq_bind] at success
      cases slotResult : compileSlot? width slot with
      | none => simp [slotResult] at success
      | some compiledSlot =>
          cases tailResult : compileSlots? width slots with
          | none => simp [slotResult, tailResult] at success
          | some compiledTail =>
              simp [slotResult, tailResult] at success
              subst compiled
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨compileSlot?_success slotResult,
                inductionHypothesis tailResult⟩

theorem compileSlots?_complete_of_all_lt
    (width : Nat) (source : List Nat)
    (bounded : source.all (fun slot => slot < width) = true) :
    ∃ compiled, compileSlots? width source = some compiled := by
  induction source with
  | nil => exact ⟨[], rfl⟩
  | cons slot slots inductionHypothesis =>
      simp only [List.all_cons, Bool.and_eq_true] at bounded
      obtain ⟨compiledTail, tailSuccess⟩ :=
        inductionHypothesis bounded.2
      have slotBound : slot < width := of_decide_eq_true bounded.1
      let compiledSlot : Fin width := ⟨slot, slotBound⟩
      refine ⟨compiledSlot :: compiledTail, ?_⟩
      simp [compileSlots?, compileSlot?, slotBound, compiledSlot, tailSuccess]

/-- Compile the source-ordered variable observations of one rule into the
query-local finite carrier.  Repeated observations remain repeated. -/
def compileRuleSlots? (width : Nat) (rule : TypedRule) :
    Option (List (Fin width)) :=
  compileSlots? width (ruleUsedVariables rule)

theorem ruleUsedVariables_all_lt_of_locallySupported
    (rule : TypedRule) (supported : rule.locallySupported = true) :
    (ruleUsedVariables rule).all
        (fun slot => slot < rule.variableCount.toNat) = true := by
  have packed :=
    packedDenseVariables_of_rule_locallySupported rule supported
  have dense := (packedDenseVariables_eq_true_iff
    rule.variableCount.toNat (ruleUsedVariables rule)).1 packed
  unfold denseVariables at dense
  rw [Bool.and_eq_true] at dense
  exact dense.1

theorem compileRuleSlots?_complete_of_program
    (source : TypedProgram) (rule : TypedRule)
    (supported : source.locallySupported = true) (member : rule ∈ source) :
    ∃ compiled,
      compileRuleSlots? (maximumVariableCount source) rule = some compiled := by
  have rulesSupported : source.all TypedRule.locallySupported = true := by
    simp [TypedProgram.locallySupported] at supported
    aesop
  have ruleSupported := (List.all_eq_true.mp rulesSupported) rule member
  have localBound :=
    ruleUsedVariables_all_lt_of_locallySupported rule ruleSupported
  have globalBound : (ruleUsedVariables rule).all
      (fun slot => slot < maximumVariableCount source) = true := by
    apply List.all_eq_true.mpr
    intro slot slotMember
    apply decide_eq_true
    exact lt_of_lt_of_le
      (of_decide_eq_true
        ((List.all_eq_true.mp localBound) slot slotMember))
      (variableCount_le_maximumVariableCount_of_mem member)
  exact compileSlots?_complete_of_all_lt
    (maximumVariableCount source) (ruleUsedVariables rule) globalBound

/-- Successful finite lowering preserves the exact source-ordered slot list. -/
theorem compileRuleSlots?_values
    {width : Nat} {rule : TypedRule} {compiled : List (Fin width)}
    (success : compileRuleSlots? width rule = some compiled) :
    compiled.map Fin.val = ruleUsedVariables rule :=
  compileSlots?_values success

/-- Once the generated finite width supplies a transaction and a fresh-epoch
certificate, stamped execution is exactly fresh-buffer execution. -/
theorem epochExecution_exact [DecidableEq (Fin width)]
    (admitted : AdmittedEpochTransaction width Value) :
    snapshotStamped admitted.epoch
        (runStamped admitted.epoch admitted.buffer admitted.transaction) =
      ReusableSlotBufferCompilation.snapshot
        (ReusableSlotBufferCompilation.runFresh admitted.transaction) :=
  snapshotStamped_run_eq_fresh admitted

/-! ## Independent witnesses and rejection boundaries -/

private def parserActionRule : TypedRule :=
  { name := [1]
    head := .application [2]
      (.cons (.variable 0) (.cons (.variable 1) .nil))
    body := []
    variableCount := 2 }

private def relationalProofRule : TypedRule :=
  { name := [3]
    head := .application [4]
      (.cons (.variable 1) (.cons (.variable 0) .nil))
    body := [.application [5] (.cons (.variable 1) .nil)]
    variableCount := 2 }

private def independentProgram : TypedProgram :=
  [parserActionRule, relationalProofRule]

/-- Parser/action registers and relational proof binders share one width. -/
example : maximumVariableCount independentProgram = 2 := by
  decide

/-- Repeated and reordered rule observations compile without losing their
source order. -/
example : ∃ compiled,
    compileRuleSlots? 2 relationalProofRule = some compiled ∧
      compiled.map Fin.val = [1, 0, 1] := by
  refine ⟨[⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩], ?_, rfl⟩
  decide

/-- A slot outside the generated finite inventory fails closed. -/
example : compileSlots? 2 [0, 2] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanEpochSlotCompilation
