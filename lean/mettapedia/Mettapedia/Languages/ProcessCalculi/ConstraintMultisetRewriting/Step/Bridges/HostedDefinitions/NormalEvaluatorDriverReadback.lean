import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorGrounding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorMachineView

/-!
# All live evaluator clauses and their literal driver payloads

Header comparisons range over the actual enlarged equation list. Live
matches against determined calls recover the driver's held payload from an
actual constraint model. No conversion or native evaluation premise is used
as a source matching test.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorDriverReadback

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalEvaluatorGrounding (DriverEntry callAt callCode clause)

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

theorem matched_head (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (determined : Determines K call code)
    (equation : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) (tag : String)
    (head : literalHead equation.lhs = some tag)
    (live : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) equation.lhs, call)])) :
    closedHead code = some tag := by
  obtain ⟨X, target, assignment, solved⟩ := live
  obtain ⟨old, added⟩ := (models_append assignment _ _).mp solved
  have matched := (models_singleton assignment _).mp added
  have left := literalHead_instantiate assignment
    (literalHead_instantiate (copyAt (BinderCore.keys built.rules) scope) head)
  have same := congrArg literalHead matched
  rw [left, determined.2 target assignment old, literalHead_include] at same
  exact same.symm

theorem evaluate_clause (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (determined : Determines K call (callCode .evaluate code))
    {equation : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : equation ∈ (NormalProgram.program built D).equations)
    (live : Solvable (callBranch D scope K call [] [] equation).store) :
    equation = clause built D .evaluate := by
  rcases (NormalProgramFormation.equation_mem_iff built D equation).mp member with original | probe | scanner | driver
  · have same := matched_head built D scope K call _ determined equation activeTag
      (NormalProgramFormation.original_lhs_head built D original) live
    change some NormalProgram.evaluateTag = some activeTag at same
    exact ((by decide +kernel : NormalProgram.evaluateTag ≠ activeTag) (Option.some.inj same)).elim
  · have same := matched_head built D scope K call _ determined equation NormalProbe.probeTag
      (NormalProgramFormation.probe_lhs_head built D probe) live
    change some NormalProgram.evaluateTag = some NormalProbe.probeTag at same
    exact ((by decide +kernel : NormalProgram.evaluateTag ≠ NormalProbe.probeTag) (Option.some.inj same)).elim
  · have same := matched_head built D scope K call _ determined equation NormalScanner.scanTag
      (NormalProgramFormation.scanner_lhs_head built D scanner) live
    change some NormalProgram.evaluateTag = some NormalScanner.scanTag at same
    exact ((by decide +kernel : NormalProgram.evaluateTag ≠ NormalScanner.scanTag) (Option.some.inj same)).elim
  · simp only [NormalProgram.driver, List.mem_cons, List.not_mem_nil, or_false] at driver
    rcases driver with rfl | rfl
    · rfl
    · have same := matched_head built D scope K call _ determined _ activeTag rfl live
      change some NormalProgram.evaluateTag = some activeTag at same
      exact ((by decide +kernel : NormalProgram.evaluateTag ≠ activeTag) (Option.some.inj same)).elim

theorem active_clause (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (determined : Determines K call code) (head : closedHead code = some activeTag)
    {equation : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : equation ∈ (NormalProgram.program built D).equations)
    (live : Solvable (callBranch D scope K call [] [] equation).store) :
    equation ∈ (BinderCore.program built.rules).equations ∨ equation = clause built D .resume := by
  rcases (NormalProgramFormation.equation_mem_iff built D equation).mp member with original | probe | scanner | driver
  · exact .inl original
  · have same := matched_head built D scope K call code determined equation NormalProbe.probeTag
      (NormalProgramFormation.probe_lhs_head built D probe) live
    rw [head] at same
    exact ((by decide +kernel : activeTag ≠ NormalProbe.probeTag) (Option.some.inj same)).elim
  · have same := matched_head built D scope K call code determined equation NormalScanner.scanTag
      (NormalProgramFormation.scanner_lhs_head built D scanner) live
    rw [head] at same
    exact ((by decide +kernel : activeTag ≠ NormalScanner.scanTag) (Option.some.inj same)).elim
  · simp only [NormalProgram.driver, List.mem_cons, List.not_mem_nil, or_false] at driver
    rcases driver with rfl | rfl
    · have same := matched_head built D scope K call code determined _ NormalProgram.evaluateTag rfl live
      rw [head] at same
      exact ((by decide +kernel : activeTag ≠ NormalProgram.evaluateTag) (Option.some.inj same)).elim
    · exact .inr rfl

theorem matching_driver_payload (entry : DriverEntry) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (determined : Determines K call code)
    (live : Solvable (NormalEvaluatorGrounding.matchStore built entry scope K call)) :
    ∃ payload, callCode entry payload = code := by
  obtain ⟨X, target, assignment, solved⟩ := live
  let grounded : Assignment (fam (BinderCore.keys built.rules)) (ProgramBinders.ground MSig) :=
    Assignment.compose (ProgramBinders.close target) assignment
  have modelsGround : Models grounded (NormalEvaluatorGrounding.matchStore built entry scope K call) := by
    intro equation inside
    simp only [grounded, Assignment.instantiate_compose]
    exact congrArg (instantiate (ProgramBinders.close target)) (solved equation inside)
  obtain ⟨old, added⟩ := (models_append grounded _ _).mp modelsGround
  have matched := (models_singleton grounded _).mp added
  let field := instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built 0)
  obtain ⟨payload, encoded⟩ := ProgramBinders.holeFree (instantiate grounded field)
  have same : callAt entry (instantiate grounded field) =
      Rigid.includeTerm (ProgramBinders.ground MSig) code := by
    rw [NormalEvaluatorGrounding.instantiate_callAt, NormalEvaluatorGrounding.instantiate_callAt] at matched
    exact matched.trans (determined.2 _ grounded old)
  rw [encoded, ← NormalEvaluatorGrounding.include_callAt] at same
  exact ⟨payload, Rigid.include_injective _ _ _ same⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorDriverReadback

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorDriverReadback.matching_driver_payload
