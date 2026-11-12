import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentProgramSchemas

/-!
# Source schemas with retained output typings

The source declaration records retained value typings or typed templates
with their original environments. Matching uses explicit telescope arguments. Publication is
licensed at every matching solution. A certified principal answer reduces
exactly these declared-type checks to checks at that answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) (O : Type)

structure Schema (Γ : Context rules) where
  helpers : Helpers Γ
  takes : List (TotalTerm helpers.frame)
  reads : List (TotalTerm helpers.frame)
  outputs : List (Code helpers.frame)
  tells : EquationStore (TotalTerm helpers.frame)
  guards : EquationStore (TotalTerm helpers.frame)
  queries : List (Query levels O helpers.frame)

variable {levels O}

abbrev Schema.erase {Γ : Context rules} (schema : Schema levels O Γ) : DependentProgram.Schema levels O Γ where
  helpers := schema.helpers
  takes := schema.takes
  reads := schema.reads
  makes := schema.outputs.map Code.raw
  tells := schema.tells
  guards := schema.guards
  queries := schema.queries

abbrev Pick {Γ : Context rules} (schema : Schema levels O Γ) := DependentProgram.Pick schema.erase

namespace Schema

variable {state : State rules O} (schema : Schema levels O state.frame) (pick : Pick schema)

abbrev compile := schema.erase.compile (s := state) pick

def SelectionShape : Prop :=
  pick.1.taken.Nodup ∧ pick.1.fresh.Nodup ∧
    schema.takes.length = pick.1.taken.length ∧ schema.reads.length = pick.1.read.length

/-- Source meaning over actual matching arguments: every selected output
certificate holds at every model, without existential retyping of erased code. -/
def Admits : Prop :=
  schema.SelectionShape pick ∧ schema.erase.Present pick ∧
    (∃ (target : Context rules) (baseMap : target ⟶ state.frame)
      (args : schema.helpers.Arguments baseMap), schema.erase.ModelsAt pick baseMap args) ∧
    (∀ (target : Context rules) (baseMap : target ⟶ state.frame)
      (args : schema.helpers.Arguments baseMap), schema.erase.ModelsAt pick baseMap args →
        schema.erase.GuardsAt baseMap args) ∧
    ∀ (target : Context rules) (baseMap : target ⟶ state.frame)
      (args : schema.helpers.Arguments baseMap), schema.erase.ModelsAt pick baseMap args →
        ∀ output ∈ schema.outputs, output.At (schema.helpers.instantiate baseMap args)

theorem output_models_iff :
    (∀ (target : Context rules) (baseMap : target ⟶ state.frame)
      (args : schema.helpers.Arguments baseMap), schema.erase.ModelsAt pick baseMap args →
        ∀ output ∈ schema.outputs, output.At (schema.helpers.instantiate baseMap args)) ↔
      ∀ output ∈ schema.outputs, output.Uniform levels (schema.compile pick).information := by
  constructor
  · intro licensed output member target substitution solved
    let decoded := schema.helpers.openingEquiv target substitution
    have sourceModels := (schema.erase.compile_information_iff pick decoded.1 decoded.2).mp
      (show (frames levels).Models (schema.helpers.instantiate decoded.1 decoded.2)
        (schema.compile pick).information from by rwa [schema.helpers.instantiate_opening])
    have result := licensed target decoded.1 decoded.2 sourceModels output member
    rwa [schema.helpers.instantiate_opening] at result
  · intro licensed target baseMap args sourceModels output member
    exact licensed output member target (schema.helpers.instantiate baseMap args)
      ((schema.erase.compile_information_iff pick baseMap args).mpr sourceModels)

/-- Checks at the concrete answer, combined with the actual firing's
resource enabling and guards. The answer certificate is supplied separately. -/
def NativeChecks [DecidableEq O] {target : Context rules} (answer : target ⟶ schema.helpers.frame) : Prop :=
  schema.SelectionShape pick ∧
    MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) state.present
      ((schema.compile pick).selection.commit (T := Unit)) ∧
    (frames levels).Solvable (schema.compile pick).information ∧
    (frames levels).Entails (schema.compile pick).information
      (fun _ substitution => (schema.compile pick).Holds substitution) ∧
    ∀ output ∈ schema.outputs, output.At answer

theorem native_checks_iff [DecidableEq O] {target : Context rules}
    {answer : target ⟶ schema.helpers.frame}
    (principal : (frames levels).Principal (schema.compile pick).information answer) :
    schema.NativeChecks pick answer ↔ schema.Admits pick := by
  have outputs : (∀ output ∈ schema.outputs, output.At answer) ↔
      ∀ output ∈ schema.outputs, output.Uniform levels (schema.compile pick).information := by
    constructor
    · intro checked output member
      exact (output.uniform_iff_at_principal levels principal).mpr (checked output member)
    · intro checked output member
      exact (output.uniform_iff_at_principal levels principal).mp (checked output member)
  unfold NativeChecks Admits
  rw [DependentFull.enabled_iff, schema.erase.compile_made pick,
    schema.helpers.solvable_iff_arguments levels,
    schema.helpers.entails_iff_arguments levels, outputs, ← schema.output_models_iff pick]
  simp_rw [schema.erase.compile_information_iff]
  rfl

end Schema

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Schema.native_checks_iff
