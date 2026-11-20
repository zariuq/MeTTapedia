import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgramFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalRootMatching

/-!
# Actual probe calls are isolated in the assembled source program

Solvability of a copied pattern against a wrapped call identifies an actual
probe clause. Original, scanner and driver clauses have incompatible literal
heads. The equation store is retained throughout this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramIsolation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

theorem matched_head (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) (tag : String)
    (head : literalHead clause.lhs = some tag)
    (matched : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs,
      NormalProbe.wrap call)])) : tag = NormalProbe.probeTag := by
  obtain ⟨X, target, assignment, solved⟩ := matched
  have equation := (models_singleton assignment _).mp ((models_append assignment _ _).mp solved).2
  have left := literalHead_instantiate assignment
    (literalHead_instantiate (copyAt (BinderCore.keys built.rules) scope) head)
  have right := literalHead_instantiate assignment
    (show literalHead (NormalProbe.wrap call) = some NormalProbe.probeTag from rfl)
  have heads := congrArg literalHead equation
  rw [left, right] at heads
  exact Option.some.inj heads

theorem matched_is_probe (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations)
    (matched : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs,
      NormalProbe.wrap call)])) : clause ∈ NormalProgram.probes built D := by
  rcases (NormalProgramFormation.equation_mem_iff built D clause).mp member with
    original | probe | scanner | driver
  · have same := matched_head built D scope K call clause activeTag
      (NormalProgramFormation.original_lhs_head built D original) matched
    exact ((by decide +kernel : activeTag ≠ NormalProbe.probeTag) same).elim
  · exact probe
  · have same := matched_head built D scope K call clause NormalScanner.scanTag
      (NormalProgramFormation.scanner_lhs_head built D scanner) matched
    exact ((by decide +kernel : NormalScanner.scanTag ≠ NormalProbe.probeTag) same).elim
  · rcases NormalProgramFormation.driver_lhs_heads built D driver with evaluate | active
    · have same := matched_head built D scope K call clause NormalProgram.evaluateTag evaluate matched
      exact ((by decide +kernel : NormalProgram.evaluateTag ≠ NormalProbe.probeTag) same).elim
    · have same := matched_head built D scope K call clause activeTag active matched
      exact ((by decide +kernel : activeTag ≠ NormalProbe.probeTag) same).elim

theorem probe_admission_iff (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) :
    (∃ clause ∈ (NormalProgram.program built D).equations,
      Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs,
        NormalProbe.wrap call)])) ↔ NormalRootMatching.Enabled built D scope K call := by
  constructor
  · rintro ⟨clause, member, matched⟩
    exact ⟨clause, matched_is_probe built D scope K call member matched, matched⟩
  · rintro ⟨clause, member, matched⟩
    exact ⟨clause, (NormalProgramFormation.equation_mem_iff built D clause).mpr
      (.inr (.inl member)), matched⟩

theorem no_probe_matches (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (disabled : ¬ NormalRootMatching.Enabled built D scope K call) :
    ∀ clause ∈ (NormalProgram.program built D).equations,
      ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) clause.lhs,
        NormalProbe.wrap call)]) := by
  intro clause member matched
  exact disabled ((probe_admission_iff built D scope K call).mp ⟨clause, member, matched⟩)

theorem live_callBranch_reply (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations)
    (live : Solvable (callBranch D scope K (NormalProbe.wrap call) frames pending clause).store) :
    (callBranch D scope K (NormalProbe.wrap call) frames pending clause).focus =
      .eval (.ret (NormalProbe.marker (fam (BinderCore.keys built.rules)))) := by
  have probe := matched_is_probe built D scope K call member live
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp probe
  rfl

theorem callBranch_frames (scope : Nat) (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) :
    (callBranch D scope K call frames pending clause).frames = frames ∧
      (callBranch D scope K call frames pending clause).pending = pending := ⟨rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramIsolation

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramIsolation.probe_admission_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramIsolation.live_callBranch_reply
