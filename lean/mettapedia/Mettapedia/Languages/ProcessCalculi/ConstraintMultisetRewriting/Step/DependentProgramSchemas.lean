import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentSchemaArguments

/-!
# Dependent rule schemas and occurrence selections

A schema declares its fresh typed helpers and term patterns. A separate
choice selects the taken/read occurrences and assigns fresh identities to
made rows. Validation checks the output arity before zipping identities
with the schema's outputs, so a truncated zip cannot admit a malformed
choice. The target is the existing dependent full firing.

The source matching relation below evaluates explicit typed arguments and
old rows in their supplied environment. It does not define matching by the
target firing's admission predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) (O : Type)

/-- Patterns and typed helper declarations, independent of the choice of occurrences. -/
structure Schema (Γ : Context rules) where
  helpers : Helpers Γ
  takes : List (TotalTerm helpers.frame)
  reads : List (TotalTerm helpers.frame)
  makes : List (Make helpers.frame)
  tells : EquationStore (TotalTerm helpers.frame)
  guards : EquationStore (TotalTerm helpers.frame)
  queries : List (Query levels O helpers.frame)

structure Choice where
  taken : List O
  read : List O
  fresh : List O

variable {levels O}

/-- An output identity for each output row, before any firing is constructed. -/
abbrev Pick {Γ : Context rules} (schema : Schema levels O Γ) :=
  {choice : Choice O // choice.fresh.length = schema.makes.length}

def validateChoice {Γ : Context rules} (schema : Schema levels O Γ) (choice : Choice O) :
    Option (Pick schema) :=
  if valid : choice.fresh.length = schema.makes.length then some ⟨choice, valid⟩ else none

theorem validateChoice_none_iff {Γ : Context rules} (schema : Schema levels O Γ)
    (choice : Choice O) : validateChoice schema choice = none ↔
      choice.fresh.length ≠ schema.makes.length := by
  simp [validateChoice]

namespace Schema

variable {s : State rules O} (schema : Schema levels O s.frame) (pick : Pick schema)

abbrev compile : Firing levels s where
  helpers := schema.helpers
  taken := pick.1.taken
  read := pick.1.read
  takes := schema.takes
  reads := schema.reads
  makes := pick.1.fresh.zip schema.makes
  tells := schema.tells
  guards := schema.guards
  queries := schema.queries

theorem compile_made : (schema.compile pick).made = pick.1.fresh := by
  exact List.map_fst_zip (Nat.le_of_eq pick.2)

theorem compile_make_rows : ((schema.compile pick).makes.map Prod.snd) = schema.makes := by
  exact List.map_snd_zip (Nat.le_of_eq pick.2.symm)

def Shapes : Prop :=
  pick.1.taken.Nodup ∧ pick.1.fresh.Nodup ∧
    schema.takes.length = pick.1.taken.length ∧
    schema.reads.length = pick.1.read.length ∧
    ∀ made ∈ schema.makes, made.WellTyped

theorem compile_shapes_iff : (schema.compile pick).Shapes ↔ schema.Shapes pick := by
  have typed : (∀ made ∈ (schema.compile pick).makes, made.2.WellTyped) ↔
      ∀ made ∈ schema.makes, made.WellTyped := by
    rw [← schema.compile_make_rows pick]
    simp only [List.forall_mem_map]
  unfold Firing.Shapes Shapes
  rw [schema.compile_made pick, typed]

/-- Every matched row is compared with its interpretation under the supplied
old environment, after the schema pattern is instantiated by the typed tuple. -/
def MatchesAt {Δ : Context rules} (baseMap : Δ ⟶ s.frame)
    (args : schema.helpers.Arguments baseMap)
    (patterns : List (TotalTerm schema.helpers.frame)) (selected : List O) : Prop :=
  ∀ pattern occurrence, (pattern, occurrence) ∈ patterns.zip selected →
    (frames levels).E (pattern.reindex (schema.helpers.instantiate baseMap args))
      ((s.label occurrence).reindex baseMap)

def ModelsAt {Δ : Context rules} (baseMap : Δ ⟶ s.frame)
    (args : schema.helpers.Arguments baseMap) : Prop :=
  (frames levels).Models baseMap s.knowledge ∧
    schema.MatchesAt baseMap args schema.takes pick.1.taken ∧
    schema.MatchesAt baseMap args schema.reads pick.1.read ∧
    (frames levels).Models (schema.helpers.instantiate baseMap args) schema.tells

theorem compile_matching_iff {Δ : Context rules} (baseMap : Δ ⟶ s.frame)
    (args : schema.helpers.Arguments baseMap)
    (patterns : List (TotalTerm schema.helpers.frame)) (selected : List O) :
    (frames levels).Models (schema.helpers.instantiate baseMap args)
        ((schema.compile pick).matching patterns selected) ↔
      schema.MatchesAt baseMap args patterns selected := by
  constructor
  · intro solved pattern occurrence member
    have matched := solved (pattern, (schema.compile pick).row occurrence)
      (List.mem_map.mpr ⟨(pattern, occurrence), member, rfl⟩)
    change (frames levels).E
      (pattern.reindex (schema.helpers.instantiate baseMap args))
      (((s.label occurrence).reindex schema.helpers.weaken).reindex
        (schema.helpers.instantiate baseMap args)) at matched
    rwa [schema.helpers.instantiate_old_value] at matched
  · intro matchedRows equation member
    obtain ⟨⟨pattern, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
    change (frames levels).E
      (pattern.reindex (schema.helpers.instantiate baseMap args))
      (((s.label occurrence).reindex schema.helpers.weaken).reindex
        (schema.helpers.instantiate baseMap args))
    rw [schema.helpers.instantiate_old_value]
    exact matchedRows pattern occurrence present

/-- The compiled constraint store has exactly the independently stated
argument/row matching models. -/
theorem compile_information_iff {Δ : Context rules} (baseMap : Δ ⟶ s.frame)
    (args : schema.helpers.Arguments baseMap) :
    (frames levels).Models (schema.helpers.instantiate baseMap args)
        (schema.compile pick).information ↔
      schema.ModelsAt pick baseMap args := by
  simp only [Firing.information, Frames.models_append]
  rw [schema.helpers.instantiate_old_models,
    schema.compile_matching_iff, schema.compile_matching_iff]
  simp only [ModelsAt, and_assoc]

def GuardsAt {Δ : Context rules} (baseMap : Δ ⟶ s.frame)
    (args : schema.helpers.Arguments baseMap) : Prop :=
  (frames levels).Models (schema.helpers.instantiate baseMap args) schema.guards ∧
    ∀ query ∈ schema.queries,
      query.Holds s.present (fun occurrence => (s.label occurrence).reindex schema.helpers.weaken)
        (schema.helpers.instantiate baseMap args)

def Present : Prop :=
  (∀ occurrence ∈ pick.1.taken, occurrence ∈ s.present) ∧
    (∀ occurrence ∈ pick.1.read, occurrence ∈ s.present) ∧
    (∀ occurrence ∈ pick.1.taken, occurrence ∉ pick.1.read) ∧
    ∀ occurrence ∈ pick.1.fresh, occurrence ∉ s.present

/-- Source admission: well-formed outputs and selections, actual row
availability, a satisfying typed argument tuple, and guards at every such tuple. -/
def Admits : Prop :=
  schema.Shapes pick ∧ schema.Present pick ∧
    (∃ (Δ : Context rules) (baseMap : Δ ⟶ s.frame) (args : schema.helpers.Arguments baseMap),
      schema.ModelsAt pick baseMap args) ∧
    ∀ (Δ : Context rules) (baseMap : Δ ⟶ s.frame) (args : schema.helpers.Arguments baseMap),
      schema.ModelsAt pick baseMap args → schema.GuardsAt baseMap args

theorem compile_admits_iff [DecidableEq O] :
    (schema.compile pick).Admits ↔ schema.Admits pick := by
  unfold Firing.Admits
  rw [schema.compile_shapes_iff, DependentFull.enabled_iff]
  rw [schema.helpers.solvable_iff_arguments levels,
    schema.helpers.entails_iff_arguments levels]
  simp_rw [schema.compile_information_iff]
  rw [schema.compile_made pick]
  rfl

/-- The source constraint store, written directly from the schema and selected rows. -/
def information : EquationStore (TotalTerm schema.helpers.frame) :=
  (frames levels).applyStore schema.helpers.weaken s.knowledge ++
    ((schema.takes.zip pick.1.taken).map fun pair =>
      (pair.1, (s.label pair.2).reindex schema.helpers.weaken)) ++
    ((schema.reads.zip pick.1.read).map fun pair =>
      (pair.1, (s.label pair.2).reindex schema.helpers.weaken)) ++ schema.tells

theorem compile_information : (schema.compile pick).information = schema.information pick := rfl

/-- The source publication preserves all old labels through weakening and
replaces exactly the declared output identities by their checked terms. -/
def publish [DecidableEq O] (shapes : schema.Shapes pick) : State rules O where
  frame := schema.helpers.frame
  knowledge := schema.information pick
  present := (s.present \ pick.1.taken.toFinset) ∪ pick.1.fresh.toFinset
  label := DependentFull.relabel
    (fun occurrence => (s.label occurrence).reindex schema.helpers.weaken)
    (pick.1.fresh.zip schema.makes)
    (fun made member => shapes.2.2.2.2 made.2 (List.of_mem_zip member).2)

theorem compile_result [DecidableEq O] (admitted : schema.Admits pick) :
    (schema.compile pick).after ((schema.compile_admits_iff pick).mpr admitted) =
      schema.publish pick admitted.1 := by
  unfold Firing.after publish
  congr 1
  change (s.present \ pick.1.taken.toFinset) ∪ (schema.compile pick).made.toFinset = _
  rw [schema.compile_made pick]

end Schema

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentProgram
