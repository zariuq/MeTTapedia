import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram

/-!
# Retained authored-equation operations

The optional equation source extends the rule and matcher helpers with distinct
heads. Equations remain declarations in their own list: forward and reverse
matching do not modify the directed rewrite list. The source quotation fixes
the executed bodies; adequacy of its reader remains the named source boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecutionProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval
open Effects (State)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_equation_execution.metta"
    sha256 "f4fdedea53d95c28e2bd64076df1dee640dcc75bf1bd52ac1208d8122a2ccfd6"

def program : Program := RuleExecutionProgram.program.append source.program

def equations (head : String) : List Equation :=
  program.equations.filter (fun equation => equation.head == head)

def retainedHead (head : String) : Bool :=
  head != "eval" && !(head.startsWith "gslt:equation:")

private theorem retained_bodies_within :
    RuleExecutionProgram.program.equations.all (fun equation =>
      !retainedHead equation.head || codeWithin retainedHead equation.body) = true := by
  decide +kernel

theorem retained_program_closed : ProgramClosed retainedHead RuleExecutionProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp retained_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

private theorem extension_equations_fresh :
    source.program.equations.all (fun equation => !retainedHead equation.head) = true := by
  decide +kernel

private theorem extension_declarations_fresh :
    source.program.declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
          !retainedHead head
      | _ => true) = true := by
  decide +kernel

theorem retained_program_agreement :
    ProgramAgreementOn retainedHead RuleExecutionProgram.program program := by
  exact appended_program_agreement_of_checks _ _ _ extension_equations_fresh
    extension_declarations_fresh (fun _ _ => rfl)

/-- Existing rule-helper executions retain their answers, stores and I/O after
loading the independently authored equation source. -/
theorem retained_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (checked : PureReturns RuleExecutionProgram.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement retained_program_closed retained_program_agreement
    ⟨supported, rfl⟩ checked

theorem no_initializers : source.program.initializers = [] := by decide +kernel

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by decide +kernel

#print axioms retained_program_agreement
#print axioms retained_captured_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.EquationExecutionProgram
