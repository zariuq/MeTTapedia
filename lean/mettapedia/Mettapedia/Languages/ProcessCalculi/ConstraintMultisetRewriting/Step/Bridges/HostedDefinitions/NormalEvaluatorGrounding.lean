import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalGroundingCompiled

/-!
# Ground fields of the actual normal evaluator driver and original rows

The two driver entries are views of the assembled source program's clauses.
Fresh admission uses the reached source scoping invariant and grafting. The
original row output law uses the dependency licence proved for the actual
compiled list, including its substitution helpers and generated native rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorGrounding

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

inductive DriverEntry where
  | evaluate
  | resume

def callAt {X : Type} {target : X → MetaArity MSig} (entry : DriverEntry)
    (datum : Term (signature MSig target) [] ()) : Term (signature MSig target) [] () :=
  match entry with
  | .evaluate => NormalProgram.evaluateAt datum
  | .resume => NormalProgram.resumeAt datum

def callCode (entry : DriverEntry) (code : MClosed) : MClosed :=
  match entry with
  | .evaluate => nodeC NormalProgram.evaluateTag [code]
  | .resume => resumeC code (nodeC NormalProgram.nextTag [])

def fieldPath : DriverEntry → List Nat
  | .evaluate => [1]
  | .resume => [1, 1]

theorem field_path {X : Type} {target : X → MetaArity MSig} (entry : DriverEntry)
    (datum : Term (signature MSig target) [] ()) :
    LiteralPaths.part (callAt entry datum) (fieldPath entry) = some datum := by
  cases datum <;> cases entry <;> rfl

theorem instantiate_callAt {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) (entry : DriverEntry)
    (datum : Term (signature MSig source) [] ()) :
    instantiate assignment (callAt entry datum) = callAt entry (instantiate assignment datum) := by
  cases entry <;>
    simp only [callAt, NormalProgram.evaluateAt, NormalProgram.resumeAt, NormalProgram.nextAt,
      NormalScanner.instantiate_nodeAt, List.map_cons, List.map_nil]

theorem include_callAt {X : Type} (target : X → MetaArity MSig) (entry : DriverEntry) (code : MClosed) :
    Rigid.includeTerm target (callCode entry code) = callAt entry (Rigid.includeTerm target code) := by
  cases entry <;>
    simp only [callCode, callAt, resumeC, activeC, NormalProgram.evaluateAt,
      NormalProgram.resumeAt, NormalProgram.nextAt, NormalScanner.include_nodeAt,
      List.map_cons, List.map_nil]

variable {dev : Definitions.Development} (built : Compiled dev)

def bodyAt {Ty : Type} (entry : DriverEntry) (datum : Data (BinderCore.keys built.rules) [] ()) :
    Comp (BinderCore.keys built.rules) [] () Ty :=
  match entry with
  | .evaluate => .choice
      (.let_ (NormalScanner.site built 1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
        (.apply (NormalScanner.scanAt datum)) (.ret (NormalProgram.doneAt datum)))
      (.apply (NormalProgram.seekAt datum))
  | .resume => .apply (NormalProgram.evaluateAt datum)

def clause (D : Discipline MSig [] ()) (entry : DriverEntry) :
    SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty :=
  ⟨NormalScanner.site built 0, callAt entry (NormalScanner.datum built 0),
    bodyAt built entry (NormalScanner.datum built 0)⟩

theorem clause_mem (D : Discipline MSig [] ()) (entry : DriverEntry) :
    clause built D entry ∈ (NormalProgram.program built D).equations := by
  apply NormalProgramFormation.driver_mem built D
  cases entry
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem instantiate_bodyAt {Ty : Type}
    (assignment : Assignment (fam (BinderCore.keys built.rules)) (fam (BinderCore.keys built.rules)))
    (entry : DriverEntry) (datum : Data (BinderCore.keys built.rules) [] ()) :
    (bodyAt built (Ty := Ty) entry datum).inst assignment = bodyAt built entry (instantiate assignment datum) := by
  cases entry <;>
    simp only [bodyAt, Comp.inst, Comp.mapData, NormalScanner.instantiate_marker,
      NormalScanner.instantiate_scanAt, NormalProgram.doneAt, NormalProgram.seekAt,
      NormalProgram.evaluateAt, NormalProgram.nextAt, NormalScanner.instantiate_nodeAt,
      List.map_cons, List.map_nil]

def matchStore (entry : DriverEntry) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) : List (Constraint (BinderCore.keys built.rules) [] ()) :=
  K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope)
    (callAt entry (NormalScanner.datum built 0)), call)]

theorem match_live (entry : DriverEntry) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (storeBelow : Hosting.StoreBelow scope K) (callBelow : Hosting.DependsBelow scope call)
    (determined : Determines K call (callCode entry code)) :
    Solvable (matchStore built entry scope K call) := by
  obtain ⟨X, target, assignment, solved⟩ := determined.1
  apply (Hosting.solvable_copy_iff (callAt entry (NormalScanner.datum built 0)) storeBelow callBelow).mpr
  refine ⟨X, target, assignment, NormalScannerGrounding.field_assignment built target (fun _ => code), solved, ?_⟩
  rw [instantiate_callAt, NormalScannerGrounding.read_datum,
    determined.2 target assignment solved, include_callAt]

theorem copied_field_determines (entry : DriverEntry) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (determined : Determines K call (callCode entry code))
    (live : Solvable (matchStore built entry scope K call)) :
    Determines (matchStore built entry scope K call)
      (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built 0)) code := by
  refine ⟨live, ?_⟩
  intro X target assignment solved
  obtain ⟨old, added⟩ := (models_append assignment _ _).mp solved
  have same := (models_singleton assignment _).mp added
  have aligned := same.trans (determined.2 target assignment old)
  have leftPath := LiteralPaths.part_instantiate assignment
    (LiteralPaths.part_instantiate (copyAt (BinderCore.keys built.rules) scope)
      (field_path entry (NormalScanner.datum built 0)))
  have rightPath : LiteralPaths.part (Rigid.includeTerm target (callCode entry code))
      (fieldPath entry) = some (Rigid.includeTerm target code) := by
    rw [include_callAt]
    exact field_path entry _
  have parts := congrArg (fun term => LiteralPaths.part term (fieldPath entry)) aligned
  rw [leftPath, rightPath] at parts
  exact Option.some.inj parts

theorem callBranch_shape (D : Discipline MSig [] ()) (entry : DriverEntry) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)) :
    callBranch D scope K call frames pending (clause built D entry) =
      ⟨matchStore built entry scope K call,
        .eval (bodyAt built entry
          (instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built 0))),
        frames, pending⟩ := by
  change (⟨matchStore built entry scope K call,
    .eval ((bodyAt built entry (NormalScanner.datum built 0)).inst (copyAt (BinderCore.keys built.rules) scope)),
    frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) = _
  rw [instantiate_bodyAt]

theorem determines_callAt (entry : DriverEntry)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()} {code : MClosed}
    (determined : Determines K datum code) : Determines K (callAt entry datum) (callCode entry code) := by
  refine ⟨determined.1, ?_⟩
  intro X target assignment solved
  rw [instantiate_callAt, determined.2 target assignment solved, include_callAt]

theorem include_seekAt {X : Type} (target : X → MetaArity MSig) (code : MClosed) :
    Rigid.includeTerm target (seekC code emptyContext (nodeC NormalProgram.nextTag [])) =
      NormalProgram.seekAt (Rigid.includeTerm target code) := by
  simp only [seekC, activeC, emptyContext, NormalProgram.seekAt, NormalProgram.nextAt,
    NormalScanner.include_nodeAt, List.map_cons, List.map_nil]

theorem determines_seekAt {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()} {code : MClosed}
    (determined : Determines K datum code) :
    Determines K (NormalProgram.seekAt datum) (seekC code emptyContext (nodeC NormalProgram.nextTag [])) := by
  refine ⟨determined.1, ?_⟩
  intro X target assignment solved
  simp only [NormalProgram.seekAt, NormalProgram.nextAt, NormalScanner.instantiate_nodeAt,
    List.map_cons, List.map_nil]
  rw [determined.2 target assignment solved]
  exact (include_seekAt target code).symm

theorem original_match_live (index : Fin built.rules.length) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (before after : MClosed)
    (storeBelow : Hosting.StoreBelow scope K) (callBelow : Hosting.DependsBelow scope datum)
    (determined : Determines K datum before)
    (answered : ProgramBinders.Answers (built.rules.get index) before after) :
    Solvable (K ++ [(instantiate (BinderCore.stamp built.rules scope index) (built.rules.get index).lhs, datum)]) := by
  obtain ⟨environment, matched, _⟩ := answered
  obtain ⟨X, target, assignment, solved⟩ := determined.1
  have leftReads : instantiate (NormalProbeFreshness.equationAssignment built target index environment)
      (BinderCore.embedEquation built.rules (Ty := Unit) index).lhs = Rigid.includeTerm target before :=
    (NormalProbeFreshness.read_embedded built target index environment (built.rules.get index).lhs).trans
      (((built.rules.get index).reads_in_frame environment (built.rules.get index).lhs before target).mp matched)
  have live := (Hosting.solvable_copy_iff (BinderCore.embedEquation built.rules (Ty := Unit) index).lhs
    storeBelow callBelow).mpr
      ⟨X, target, assignment, NormalProbeFreshness.equationAssignment built target index environment,
        solved, leftReads.trans (determined.2 target assignment solved).symm⟩
  simpa only [BinderCore.embedEquation, BinderCore.copy_embed] using live

theorem original_output_determines (index : Fin built.rules.length) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) (before after : MClosed)
    (determined : Determines K datum before)
    (answered : ProgramBinders.Answers (built.rules.get index) before after)
    (live : Solvable
      (K ++ [(instantiate (BinderCore.stamp built.rules scope index) (built.rules.get index).lhs, datum)])) :
    Determines (K ++ [(instantiate (BinderCore.stamp built.rules scope index) (built.rules.get index).lhs, datum)])
      (instantiate (BinderCore.stamp built.rules scope index) (built.rules.get index).rhs) after := by
  obtain ⟨environment, matched, rhsRead⟩ := answered
  refine ⟨live, ?_⟩
  intro X target assignment solved
  obtain ⟨old, added⟩ := (models_append assignment _ _).mp solved
  have same := (models_singleton assignment _).mp added
  let atRule : Assignment (built.rules.get index).arity target := fun hole => assignment ⟨[scope], ⟨index, hole⟩⟩
  have leftGround : instantiate atRule (built.rules.get index).lhs = Rigid.includeTerm target before :=
    (BinderCore.instantiate_stamp built.rules assignment scope index (built.rules.get index).lhs).symm.trans
      (same.trans (determined.2 target assignment old))
  have expectedLeft : instantiate ((built.rules.get index).assign environment target) (built.rules.get index).lhs =
      Rigid.includeTerm target before :=
    ((built.rules.get index).reads_in_frame environment (built.rules.get index).lhs before target).mp matched
  have sameRight := NormalGroundingCompiled.grounded built _ (List.get_mem built.rules index)
    target atRule environment (leftGround.trans expectedLeft.symm)
  rw [BinderCore.instantiate_stamp]
  exact sameRight.trans
    (((built.rules.get index).reads_in_frame environment (built.rules.get index).rhs after target).mp rhsRead)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorGrounding

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorGrounding.original_output_determines
