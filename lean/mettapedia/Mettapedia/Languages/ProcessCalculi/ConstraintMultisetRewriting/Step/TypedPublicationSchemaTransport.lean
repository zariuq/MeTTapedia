import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationQueryTransport

/-!
# Transport of actual typed source schemas

A replacement helper telescope is compared with the original by a genuine
contextual isomorphism over the old-state comparison. Source patterns, typed
code with its retained environments, constraints, queries and occurrence
choices are all transported. Matching models and guard answers are proved
equivalent at corresponding solutions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type}

namespace SchemaTransport

variable {Γ Δ : Context rules} (schema : Schema levels O Γ)
  (helpers : Helpers Δ) (comparison : helpers.frame ≅ schema.helpers.frame)

abbrev carry : Schema levels O Δ where
  helpers := helpers
  takes := schema.takes.map (fun row => row.reindex comparison.hom)
  reads := schema.reads.map (fun row => row.reindex comparison.hom)
  outputs := schema.outputs.map (fun code => code.reindex comparison.hom)
  tells := (frames levels).applyStore comparison.hom schema.tells
  guards := (frames levels).applyStore comparison.hom schema.guards
  queries := schema.queries.map (QueryTransport.carry comparison)

def choice (pick : Pick schema) : Pick (carry schema helpers comparison) :=
  ⟨pick.val, by simpa only [Schema.erase, carry, List.length_map] using pick.property⟩

variable {schema helpers comparison}

theorem outputs {target : Context rules} (answer : target ⟶ schema.helpers.frame) :
    (∀ code ∈ (carry schema helpers comparison).outputs, code.At (answer ≫ comparison.inv)) ↔
      ∀ code ∈ schema.outputs, code.At answer := by
  change (∀ code ∈ schema.outputs.map (fun code => code.reindex comparison.hom),
    code.At (answer ≫ comparison.inv)) ↔ _
  simp only [List.forall_mem_map, Code.at_reindex_iff, Category.assoc,
    comparison.inv_hom_id, Category.comp_id]

variable {source target : State rules O}
  (schema : Schema levels O source.frame) (pick : Pick schema)
  (stateIso : PlainIso levels source target) (helpers : Helpers target.frame)
  (comparison : helpers.frame ≅ schema.helpers.frame)
  (commuting : comparison.hom ≫ schema.helpers.weaken = helpers.weaken ≫ stateIso.frame.hom)

theorem shapes :
    (carry schema helpers comparison).SelectionShape (state := target) (choice schema helpers comparison pick) ↔
      schema.SelectionShape (state := source) pick := by
  simp only [Schema.SelectionShape, choice, carry, List.length_map]

include stateIso commuting

theorem row (occurrence : O) :
    ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).row occurrence =
      ((schema.compile (state := source) pick).row occurrence).reindex comparison.hom := by
  change (target.label occurrence).reindex helpers.weaken =
    ((source.label occurrence).reindex schema.helpers.weaken).reindex comparison.hom
  rw [stateIso.label]
  change ((source.label occurrence).reindex stateIso.frame.hom).reindex helpers.weaken =
    ((source.label occurrence).reindex schema.helpers.weaken).reindex comparison.hom
  rw [← ContextualDependentEta.reindex_comp, ← ContextualDependentEta.reindex_comp, commuting]

theorem matching (patterns : List (TotalTerm schema.helpers.frame)) (selected : List O) :
    ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).matching
        (patterns.map (fun term => term.reindex comparison.hom)) selected =
      (frames levels).applyStore comparison.hom ((schema.compile pick).matching patterns selected) := by
  simp only [Firing.matching, List.zip_map_left, List.map_map, Frames.applyStore,
    Function.comp_def, Prod.map, id_eq]
  apply List.map_congr_left
  intro pair member
  exact congrArg (Prod.mk (pair.1.reindex comparison.hom))
    (row schema pick stateIso helpers comparison commuting pair.2)

theorem information_models {observer : Context rules} (solution : observer ⟶ helpers.frame) :
    (frames levels).Models solution
        ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).information ↔
      (frames levels).Models (solution ≫ comparison.hom) (schema.compile pick).information := by
  have knowledge : (frames levels).Models (solution ≫ helpers.weaken) target.knowledge ↔
      (frames levels).Models ((solution ≫ comparison.hom) ≫ schema.helpers.weaken) source.knowledge := by
    have same := (stateIso.knowledge observer (solution ≫ helpers.weaken)).symm
    rw [Frames.models_applyStore] at same
    change _ ↔ (frames levels).Models ((solution ≫ helpers.weaken) ≫ stateIso.frame.hom) source.knowledge at same
    simpa only [Category.assoc, commuting] using same
  change (frames levels).Models solution
    ((frames levels).applyStore helpers.weaken target.knowledge ++
      ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).matching
        (schema.takes.map (fun term => term.reindex comparison.hom)) pick.val.taken ++
      ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).matching
        (schema.reads.map (fun term => term.reindex comparison.hom)) pick.val.read ++
      (frames levels).applyStore comparison.hom schema.tells) ↔ _
  rw [matching schema pick stateIso helpers comparison commuting,
    matching schema pick stateIso helpers comparison commuting]
  simp only [Firing.information, Frames.models_append, Frames.models_applyStore]
  exact and_congr (and_congr (and_congr knowledge Iff.rfl) Iff.rfl) Iff.rfl

theorem guards {observer : Context rules} (solution : observer ⟶ helpers.frame) :
    ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).Holds solution ↔
      (schema.compile pick).Holds (solution ≫ comparison.hom) := by
  have rows := funext (row schema pick stateIso helpers comparison commuting)
  change ((frames levels).Models solution ((frames levels).applyStore comparison.hom schema.guards) ∧
    ∀ query ∈ schema.queries.map (QueryTransport.carry comparison), query.Holds target.present
      ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).row solution) ↔ _
  rw [rows, ← stateIso.present]
  simp only [Frames.models_applyStore, List.forall_mem_map, QueryTransport.holds_carried]
  rfl

end SchemaTransport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SchemaTransport.information_models
