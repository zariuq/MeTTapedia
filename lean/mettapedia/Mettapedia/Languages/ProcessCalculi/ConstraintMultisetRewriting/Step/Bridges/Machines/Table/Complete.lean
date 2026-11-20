import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Replay

/-!
# Stopped and exhausted table executions reach actual machine states

These are instances of target-table replay, starting at the compiler's
actual initialized state. A stopped replay reaches a state with no admitted
firing of the program. Exhaustion spends exactly the supplied event budget
and retains an endpoint that still admits a firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program

open NamesOnTheStep (Expr)
open Turing.ToPartrec
open RuleSyntax.Presentation.Schematic (schematicStep)
open RuleSyntax.Machines (rootRules ReadsBag rowState_reads)
open RuleSyntax.Machines.PartialRecursive (program eNormal)

theorem stopped_actual {budget : Nat} {code : Code} {input : List Nat} {final : Expr}
    (stopped : drive schemas budget (eNormal code .halt input) = .stopped final) :
    ∃ run : PartialRecursive.native.Run (PartialRecursive.start code input),
      run.word.length ≤ budget ∧ ReadsBag run.last {final} ∧
        ∀ firing, ¬ PartialRecursive.native.Admits (s := run.last) firing := by
  have result := stopped_has_run schemas closed (rowState_reads (eNormal code .halt input)) stopped
  have same : rootRules schemas = program := RuleSyntax.Machines.PartialRecursive.program_eq_rootRules.symm
  have transported (rules : List RuleSyntax.Presentation.Schematic.SRule) (equal : rootRules schemas = rules) :
      ∃ run : (schematicStep Nat rules).toStep.Run (PartialRecursive.start code input),
        run.word.length ≤ budget ∧ ReadsBag run.last {final} ∧
          ∀ firing, ¬ (schematicStep Nat rules).Admits (s := run.last) firing := by
    subst rules
    exact result
  exact transported program same

theorem exhausted_actual {budget : Nat} {code : Code} {input : List Nat} {final : Expr}
    (exhausted : drive schemas budget (eNormal code .halt input) = .exhausted final) :
    ∃ run : PartialRecursive.native.Run (PartialRecursive.start code input),
      run.word.length = budget ∧ ReadsBag run.last {final} ∧
        ∃ firing, PartialRecursive.native.Admits (s := run.last) firing := by
  have result := exhausted_has_run schemas closed (rowState_reads (eNormal code .halt input)) exhausted
  have same : rootRules schemas = program := RuleSyntax.Machines.PartialRecursive.program_eq_rootRules.symm
  have transported (rules : List RuleSyntax.Presentation.Schematic.SRule) (equal : rootRules schemas = rules) :
      ∃ run : (schematicStep Nat rules).toStep.Run (PartialRecursive.start code input),
        run.word.length = budget ∧ ReadsBag run.last {final} ∧
          ∃ firing, (schematicStep Nat rules).Admits (s := run.last) firing := by
    subst rules
    exact result
  exact transported program same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program.stopped_actual
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program.exhausted_actual
