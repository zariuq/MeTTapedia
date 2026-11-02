import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProtectedProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability

/-!
# Real request-system traces propagate proof-relevant open derivations

The trace evidence below retains exactly the selected witnesses of existing
native firings. Its ordinary projection is the established authority-system
run. Its logical projection records all protected occurrence positions and
source rule applications. Concatenating real traces substitutes the first
proof environment into the second; no quotient or equivalence of raw runs
is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (judgment)
open InferenceSchemaKernel (Space Value)
open InferenceRequestExecution (Occurrence label location payload system)
open InferenceSelectedFirings
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

/-- Project an actual selected firing, retaining its computed source
origin. Only the protected space is projected to an ordered context. -/
noncomputable def projectFiring {actor : Bool}
    {before after : Configuration Value Occurrence}
    (firing : SelectedFiring definition actor before after) (prior : Board before) :
    Σ next : Board after, prior.context definition ⟶ next.context definition := by
  classical
  cases actor with
  | false =>
      let origin := Classical.choice firing.client_origin
      exact ⟨origin.board prior, origin.arrow prior⟩
  | true =>
      let origin := Classical.choice firing.kernel_origin
      exact ⟨origin.board prior, origin.arrow prior⟩

/-- Occurrence-addressed evidence of the existing run, with the same
physical configurations and actor sequence. This is execution evidence,
not a separate transition relation or proof-search interpreter. -/
inductive SelectedRun (definition : ValidatedCalculusLanguageDef) :
    Configuration Value Occurrence → List Bool → Configuration Value Occurrence → Type
  | nil (state : Configuration Value Occurrence) : SelectedRun definition state [] state
  | cons {before middle after : Configuration Value Occurrence}
      {actor : Bool} {actors : List Bool}
      (firing : SelectedFiring definition actor before middle)
      (rest : SelectedRun definition middle actors after) :
      SelectedRun definition before (actor :: actors) after

namespace SelectedRun

variable {before middle after : Configuration Value Occurrence}
  {actors firstActors secondActors : List Bool}

theorem ordinary : {before after : Configuration Value Occurrence} → {actors : List Bool} →
    SelectedRun definition before actors after →
      (system definition).Run payload before actors after
  | _, _, _, .nil state => .nil state
  | _, _, _, .cons firing rest => .cons firing.ordinary rest.ordinary

/-- Every actual run admits a selected trace; no scheduling, derivability
or guard-success hypothesis is added. -/
theorem of_run (run : (system definition).Run payload before actors after) :
    Nonempty (SelectedRun definition before actors after) := by
  induction run with
  | nil state => exact ⟨.nil state⟩
  | cons stepped _ earlier =>
      obtain ⟨firing⟩ := SelectedFiring.of_step stepped
      obtain ⟨rest⟩ := earlier
      exact ⟨.cons firing rest⟩

def append : {before middle after : Configuration Value Occurrence} →
    {firstActors secondActors : List Bool} →
    SelectedRun definition before firstActors middle →
    SelectedRun definition middle secondActors after →
      SelectedRun definition before (firstActors ++ secondActors) after
  | _, _, _, _, _, .nil _, second => second
  | _, _, _, _, _, .cons firing rest, second => .cons firing (rest.append second)

/-- The logical projection is built solely by retaining prior assumptions
and appending actual activated rule nodes along the selected native trace. -/
noncomputable def project : {before after : Configuration Value Occurrence} →
    {actors : List Bool} → SelectedRun definition before actors after →
    (prior : Board before) →
      Σ next : Board after, prior.context definition ⟶ next.context definition
  | _, _, _, .nil _, prior => ⟨prior, 𝟙 (prior.context definition)⟩
  | _, _, _, .cons firing rest, prior =>
      let head := projectFiring firing prior
      let tail := rest.project head.1
      ⟨tail.1, head.2 ≫ tail.2⟩

/-- Real trace concatenation is proof substitution, including the exact
ordered terminal board. This is the cut law for the physical projection. -/
theorem project_append (first : SelectedRun definition before firstActors middle)
    (second : SelectedRun definition middle secondActors after) (prior : Board before) :
    (first.append second).project prior =
      let firstProjection := first.project prior
      let secondProjection := second.project firstProjection.1
      ⟨secondProjection.1, firstProjection.2 ≫ secondProjection.2⟩ := by
  induction first with
  | nil => simp only [append, project, Category.id_comp]
  | cons firing rest earlier =>
      simp only [append, project]
      rw [earlier]
      simp only [Category.assoc]

/-- A physical row's exact source judgment acquires an actual open
derivation over the initial protected occurrence context. -/
noncomputable def derive (trace : SelectedRun definition before actors after)
    (prior : Board before) (occurrence : Occurrence)
    (present : occurrence ∈ after.present) (protectedHere : location occurrence = .judgments)
    (goal : Pattern) (readback : label occurrence = (.judgments, judgment goal)) :
    OpenDerivation definition prior.judgments goal := by
  let projected := trace.project prior
  let index := projected.1.position occurrence present protectedHere
  have actual := projected.1.at_readback index
  rw [projected.1.position_occurrence occurrence present protectedHere] at actual
  have same : projected.1.judgmentAt index = goal :=
    InferenceSchemaActivation.judgment_injective (congrArg Prod.snd (actual.symm.trans readback))
  exact (same ▸ projected.1.assumption definition index).bind projected.2

/-- Published observations also determine their open derivation, since all
projected source judgments are fixed under future assignment. -/
noncomputable def deriveObserved (trace : SelectedRun definition before actors after)
    (prior : Board before) (occurrence : Occurrence)
    (present : occurrence ∈ after.present) (protectedHere : location occurrence = .judgments)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (goal : Pattern)
    (observed : InferenceSchemaActivation.action.apply assignment (payload occurrence) = judgment goal) :
    OpenDerivation definition prior.judgments goal := by
  let projected := trace.project prior
  let index := projected.1.position occurrence present protectedHere
  have actual := projected.1.at_readback index
  rw [projected.1.position_occurrence occurrence present protectedHere] at actual
  have contents : payload occurrence = judgment (projected.1.judgmentAt index) := congrArg Prod.snd actual
  have equality := observed
  rw [contents, InferenceSchemaActivation.judgment_fixed _ (projected.1.at_scoped index) assignment] at equality
  have same := InferenceSchemaActivation.judgment_injective equality
  apply trace.derive prior occurrence present protectedHere goal
  exact actual.trans (congrArg (fun pattern => (Space.judgments, judgment pattern)) same)

end SelectedRun

/-- Source derivation production follows the actual selected run and can
use arbitrary initial protected judgments as ordered assumptions. -/
theorem actual_run_has_open_derivation
    {before after : Configuration Value Occurrence} {actors : List Bool}
    (run : (system definition).Run payload before actors after) (prior : Board before)
    (occurrence : Occurrence) (present : occurrence ∈ after.present)
    (protectedHere : location occurrence = .judgments) (goal : Pattern)
    (readback : label occurrence = (.judgments, judgment goal)) :
    Nonempty (OpenDerivation definition prior.judgments goal) := by
  obtain ⟨trace⟩ := SelectedRun.of_run run
  exact ⟨trace.derive prior occurrence present protectedHere goal readback⟩

/-- Reachability from the actual empty store yields a closed source
derivation by closing the proof-relevant projected run. -/
theorem reaches_has_closed_derivation (goal : Pattern)
    (reached : InferenceKernelReachability.Reaches definition goal) :
    Nonempty (InferenceChecker.Derivation definition goal) := by
  obtain ⟨after, actors, run, assignment, _, occurrence, present, protectedHere, observed⟩ := reached
  obtain ⟨trace⟩ := SelectedRun.of_run run
  let prior := Board.empty InferenceKernelReachability.initial rfl
  exact ⟨(trace.deriveObserved prior occurrence present protectedHere assignment goal observed).close⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying
