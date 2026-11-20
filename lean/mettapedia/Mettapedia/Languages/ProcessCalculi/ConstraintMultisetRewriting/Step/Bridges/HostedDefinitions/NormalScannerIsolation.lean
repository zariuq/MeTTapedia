import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgramFormation

/-!
# Every live scanner-call clause belongs to the actual scanner table

Literal heads exclude the original evaluator, probes and normal-evaluation
driver. This is coverage of every live copied clause, not an existence claim
for one selected alternative. Native-constructor identification is proved
separately from the incoming term's encoded shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerIsolation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing

theorem constructor_tag_injective : Function.Injective NormalScanner.Constructor.tag := by
  intro first second same
  cases first <;> cases second <;> simp_all [NormalScanner.Constructor.tag]

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

theorem matched_heads (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty)
    (leftTag rightTag : String) (left : literalHead clause.lhs = some leftTag)
    (right : literalHead call = some rightTag)
    (matched : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs, call)])) :
    leftTag = rightTag := by
  obtain ⟨X, target, assignment, solved⟩ := matched
  have same := (models_singleton assignment _).mp ((models_append assignment _ _).mp solved).2
  have first := literalHead_instantiate assignment
    (literalHead_instantiate (copyAt (BinderCore.keys built.rules) scope) left)
  have second := literalHead_instantiate assignment right
  have tags := congrArg literalHead same
  rw [first, second] at tags
  exact Option.some.inj tags

theorem matched_is_scanner (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations)
    (matched : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs,
      NormalScanner.scanAt datum)])) : clause ∈ NormalScanner.equations built D := by
  rcases (NormalProgramFormation.equation_mem_iff built D clause).mp member with original | probe | scanner | driver
  · have same := matched_heads built D scope K _ clause activeTag NormalScanner.scanTag
      (NormalProgramFormation.original_lhs_head built D original) rfl matched
    exact ((by decide +kernel : activeTag ≠ NormalScanner.scanTag) same).elim
  · have same := matched_heads built D scope K _ clause NormalProbe.probeTag NormalScanner.scanTag
      (NormalProgramFormation.probe_lhs_head built D probe) rfl matched
    exact ((by decide +kernel : NormalProbe.probeTag ≠ NormalScanner.scanTag) same).elim
  · exact scanner
  · rcases NormalProgramFormation.driver_lhs_heads built D driver with evaluate | active
    · have same := matched_heads built D scope K _ clause NormalProgram.evaluateTag NormalScanner.scanTag
        evaluate rfl matched
      exact ((by decide +kernel : NormalProgram.evaluateTag ≠ NormalScanner.scanTag) same).elim
    · have same := matched_heads built D scope K _ clause activeTag NormalScanner.scanTag active rfl matched
      exact ((by decide +kernel : activeTag ≠ NormalScanner.scanTag) same).elim

theorem live_callBranch_clause (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations)
    (live : Solvable (callBranch D scope K (NormalScanner.scanAt datum) frames pending clause).store) :
    ∃ kind, clause = NormalScanner.equation built D kind := by
  have scanner := matched_is_scanner built D scope K datum member live
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp scanner
  exact ⟨kind, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerIsolation

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerIsolation.live_callBranch_clause
