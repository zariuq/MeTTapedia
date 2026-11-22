import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.DependentFibre

/-!
# Solver outcomes at the typed publication boundary

The actual dependent worklist returns solved, refuted, stuck and budget
outcomes. Only a solved residual earns a principal application. Stuck and
budget outcomes retain their certified update, including all residual
solutions. They are not interpreted as absent answers or admitted firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull ContextualDependentUpdate

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- Uniform publication along the original solutions is exactly uniform
publication along the residual solutions, with the original output reindexed.
No empty-residual or principal-answer assumption is needed. -/
theorem Code.uniform_iff_update {Γ : Context rules} (output : Code Γ)
    {information : EquationStore (TotalTerm Γ)} (update : Update levels information) :
    output.Uniform levels information ↔
      (output.reindex update.answer).Uniform levels update.remaining := by
  have exact := update.entails_iff (fun _ substitution => output.At substitution)
    (fun _ first second agree => output.at_agree levels agree)
  change (∀ target substitution, (frames levels).Models substitution information → _) ↔ _ at exact
  simpa only [Code.Uniform, Code.at_reindex_iff, Frames.Entails] using exact

variable {levels} {O : Type} {state : State rules O}

inductive Suspension where
  | stuck
  | budget
  | declined
  deriving DecidableEq

/-- This is a resolution result, before resource admission and commitment. -/
inductive Resolution (schema : Schema levels O state.frame) (pick : Pick schema) : Type where
  | ready (target : Context rules) (answer : target ⟶ schema.helpers.frame)
      (principal : (frames levels).Principal (schema.compile pick).information answer)
  | refuted (absent : ¬ (frames levels).Solvable (schema.compile pick).information)
  | suspended (reason : Suspension) (update : Update levels (schema.compile pick).information)

namespace Schema

variable (schema : Schema levels O state.frame) (pick : Pick schema)

/-- Translate the driver's actual certificate, preserving its outcome class. -/
def resolveOutcome : ContextualDependentWorklist.Outcome levels (schema.compile pick).information →
    Resolution schema pick
  | .solved update finished => .ready update.target update.answer (update.completed finished)
  | .refuted absent => .refuted absent
  | .stuck update => .suspended .stuck update
  | .cutoff update => .suspended .budget update

def resolve (solver : ContextualDependentWorklist.Solver levels) (fuel : Nat) : Resolution schema pick :=
  schema.resolveOutcome pick (ContextualDependentWorklist.run solver (schema.compile pick).information fuel)

theorem solved_application (update : Update levels (schema.compile pick).information)
    (finished : update.remaining = []) :
    schema.resolveOutcome pick (.solved update finished) =
      .ready update.target update.answer (update.completed finished) := rfl

theorem cutoff_preserves_update (update : Update levels (schema.compile pick).information) :
    schema.resolveOutcome pick (.cutoff update) = .suspended .budget update := rfl

theorem stuck_preserves_update (update : Update levels (schema.compile pick).information) :
    schema.resolveOutcome pick (.stuck update) = .suspended .stuck update := rfl

theorem refuted_excludes_source (absent : ¬ (frames levels).Solvable (schema.compile pick).information) :
    ¬ schema.Admits pick := by
  intro admitted
  obtain ⟨target, baseMap, args, models⟩ := admitted.2.2.1
  exact absent ⟨target, schema.helpers.instantiate baseMap args,
    (schema.erase.compile_information_iff pick baseMap args).mpr models⟩

/-- Every pending update keeps exactly the original solution family up to
the actual typed agreement relation; it does not merely keep one answer. -/
theorem residual_exact (update : Update levels (schema.compile pick).information) :
    UnificationWithLevels.Exact (frames levels) (schema.compile pick).information
      update.answer update.remaining :=
  UnificationWithLevels.DependentFibre.update_exact update

theorem residual_publication_iff (update : Update levels (schema.compile pick).information) :
    (∀ output ∈ schema.outputs, output.Uniform levels (schema.compile pick).information) ↔
      ∀ output ∈ schema.outputs, (output.reindex update.answer).Uniform levels update.remaining := by
  constructor
  · intro uniform output member
    exact (output.uniform_iff_update levels update).mp (uniform output member)
  · intro uniform output member
    exact (output.uniform_iff_update levels update).mpr (uniform output member)

end Schema

namespace Resolution

variable {schema : Schema levels O state.frame} {pick : Pick schema}

def application? : Resolution schema pick → Option (Application levels O state)
  | .ready target answer principal => some ⟨schema, pick, target, answer, .principal principal⟩
  | .refuted _ => none
  | .suspended _ _ => none

theorem suspended_has_no_application (reason : Suspension)
    (update : Update levels (schema.compile pick).information) :
    (Resolution.suspended reason update).application? = none := rfl

/-- A solver's refutation cannot be silently turned into a source transition. -/
theorem refutation_excludes_source (absent : ¬ (frames levels).Solvable (schema.compile pick).information) :
    (Resolution.refuted absent).application? = none ∧ ¬ schema.Admits pick :=
  ⟨rfl, schema.refuted_excludes_source pick absent⟩

end Resolution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Code.uniform_iff_update
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Schema.residual_publication_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Schema.refuted_excludes_source
