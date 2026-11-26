import Mettapedia.Languages.MeTTa.SpaceTheory.HECompiledFrontier
import Mettapedia.Languages.MeTTa.SpaceTheory.EquationalLookupProtection

/-!
# Relocating HE frontiers under equation-aware entry

The equivalence class of the request and the eligible work at each
representative are separate observations. An unchanged class can
be read at the compiled snapshot; a certified alignment can relocate
matching work. Where either proof is unavailable, that observation
comes from the live space. The ordinary continuation is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HECompiledEquationalFrontier

open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.Contracts.OccurrenceObservers (Demand)
open Mettapedia.GSLT.Contracts.OccurrenceExecution (completed readCompleted reports ofTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
open HEInvocationEntry (Input Mode)
open HENativeOnTransform (Presentation)
open EvaluationObservations (heEquationalView heEmit)

variable {Context World : Type}

abbrev ClassPlans (env : WorldEnvironment Context World) (snapshot : World → Context → Space) :=
  (world : World) → (scope : Context) → (query : Atom) →
  Option (PLift (EquationalLookupProtection.SameClass
    (snapshot world scope).atoms (env.view world scope).atoms query))

def classRead (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : ClassPlans env snapshot) (world : World) (scope : Context) (query representative : Atom) : Prop :=
  match plans world scope query with
  | none => AtomEquations.Equivalent (env.view world scope).atoms query representative
  | some _ => AtomEquations.Equivalent (snapshot world scope).atoms query representative

theorem class_read_exact (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : ClassPlans env snapshot) (world : World) (scope : Context) (query representative : Atom) :
    classRead env snapshot plans world scope query representative ↔
      AtomEquations.Equivalent (env.view world scope).atoms query representative := by
  unfold classRead
  cases plans world scope query with
  | none => rfl
  | some justified => exact justified.down representative

def capture (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : HECompiledFrontier.Plans env snapshot) (world : World) (scope : Context)
    (input : Input) (expected representative : Atom) (work : List EquationWork) : Prop :=
  ¬IsErrorRel representative ∧ NonGroundedCallRel env.dispatch representative ∧
    HECompiledFrontier.selectedFrontier env snapshot plans world scope
      {input with value := Entry.Value.ofAtom representative} (.typed expected) work ∧ work ≠ []

theorem capture_exact (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : HECompiledFrontier.Plans env snapshot) (world : World) (scope : Context)
    (input : Input) (expected representative : Atom) (work : List EquationWork) :
    capture env snapshot plans world scope input expected representative work ↔
      HEEquationEntry.select (env.view world scope) env.dispatch expected input.live input.frame representative work := by
  simp [capture, HEEquationEntry.select, HECompiledFrontier.selected_frontier_exact, Mode.protect, Mode.expected,
    Entry.Value.erase_ofAtom]

def operations (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (classes : ClassPlans env snapshot)
    (frontiers : HECompiledFrontier.Plans env snapshot) (policy : Policy) : Relations :=
  fun name args reply =>
    if name < 27 then HECompiledFrontier.operations code env snapshot frontiers policy name args reply
    else match name with
      | 27 => HEEquationalExecution.equivalentAtFrom code (classRead env snapshot classes) args reply
      | 28 => HEEquationalExecution.selectedAtFrom code (capture env snapshot frontiers) args reply
      | _ => False

theorem operations_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (classes : ClassPlans env snapshot)
    (frontiers : HECompiledFrontier.Plans env snapshot) (policy : Policy) :
    operations code env snapshot classes frontiers policy = HEEquationalExecution.operations code env policy := by
  have classEq : classRead env snapshot classes =
      (fun world scope => AtomEquations.Equivalent (env.view world scope).atoms) := by
    funext world scope query representative
    exact propext (class_read_exact env snapshot classes world scope query representative)
  have captureEq : capture env snapshot frontiers = (fun world scope input expected =>
      HEEquationEntry.select (env.view world scope) env.dispatch expected input.live input.frame) := by
    funext world scope input expected representative work
    exact propext (capture_exact env snapshot frontiers world scope input expected representative work)
  funext name args reply
  simp only [operations, HEEquationalExecution.operations, HECompiledFrontier.operations_exact, classEq, captureEq,
    HEEquationalExecution.equivalentAt, HEEquationalExecution.selectedAt]
  rfl

def theory (O : Type) [DecidableEq O] (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (classes : ClassPlans env snapshot)
    (frontiers : HECompiledFrontier.Plans env snapshot) (policy : Policy) : GSLT :=
  programSystem O (specialized rows (relationGraph (operations code env snapshot classes frontiers policy))
    {rule | rule ∈ HEEquationalExecution.rules})

theorem theory_exact (O : Type) [DecidableEq O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (snapshot : World → Context → Space) (classes : ClassPlans env snapshot)
    (frontiers : HECompiledFrontier.Plans env snapshot) (policy : Policy) :
    theory O code env snapshot classes frontiers policy = HEEquationalExecution.theory O code env policy := by
  unfold theory
  rw [operations_exact]
  rfl

theorem compiled_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (classes : ClassPlans env snapshot)
    (frontiers : HECompiledFrontier.Plans env snapshot) (policy : Policy)
    {source : HEEquationalExecution.State Context World} {start : SState O}
    (shown : HEEquationalExecution.Shows code source start)
    (demand : Demand) (answer : Mettapedia.GSLT.Contracts.OccurrenceObservers.Result Result demand) :
    reports (completed (sys := HEEquationalExecution.source env policy) heEquationalView
      (·.finished = true) heEmit source) demand answer ↔
    reports (readCompleted (sys := theory O code env snapshot classes frontiers policy)
      (ofTerm (HEEquationalExecution.Shows code) heEquationalView)
      (·.finished = true) heEmit start) demand answer := by
  let observe (ops : Relations) :=
    reports (readCompleted (sys := programSystem O
      (specialized rows (relationGraph ops) {rule | rule ∈ HEEquationalExecution.rules}))
      (ofTerm (HEEquationalExecution.Shows code) heEquationalView)
      (·.finished = true) heEmit start) demand answer
  change _ ↔ observe (operations code env snapshot classes frontiers policy)
  rw [operations_exact]
  exact EvaluationObservations.he_equational_reports_iff env policy code shown demand answer

end Mettapedia.Languages.MeTTa.SpaceTheory.HECompiledEquationalFrontier
