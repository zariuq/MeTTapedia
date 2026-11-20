import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSchemaTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSolverTransport

/-!
# Certified source applications across helper presentations

The transported application retains occurrence choices and the solver's
target frame. Principal certificates remain principal; exact residual
certificates retain their original residual equations. Admission is compared
using the actual source and native publication judgments.
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
  {source target : State rules O}

namespace SchemaTransport

variable (schema : Schema levels O source.frame) (pick : Pick schema)
  (stateIso : PlainIso levels source target) (helpers : Helpers target.frame)
  (comparison : helpers.frame ≅ schema.helpers.frame)
  (commuting : comparison.hom ≫ schema.helpers.weaken = helpers.weaken ≫ stateIso.frame.hom)

include stateIso commuting

theorem information_equivalent :
    (frames levels).Equivalent
      ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).information
      ((frames levels).applyStore comparison.hom (schema.compile pick).information) := by
  intro observer solution
  exact (information_models schema pick stateIso helpers comparison commuting solution).trans
    (Frames.models_applyStore (X := frames levels) comparison.hom solution (schema.compile pick).information).symm

theorem solvable :
    (frames levels).Solvable
      ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).information ↔
      (frames levels).Solvable (schema.compile pick).information := by
  constructor
  · rintro ⟨observer, solution, solved⟩
    exact ⟨observer, solution ≫ comparison.hom,
      (information_models schema pick stateIso helpers comparison commuting solution).mp solved⟩
  · rintro ⟨observer, solution, solved⟩
    refine ⟨observer, solution ≫ comparison.inv,
      (information_models schema pick stateIso helpers comparison commuting _).mpr ?_⟩
    simpa only [Category.assoc, comparison.inv_hom_id, Category.comp_id] using solved

theorem entails_guards :
    (frames levels).Entails
      ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).information
      (fun _ solution => ((carry schema helpers comparison).compile (state := target)
        (choice schema helpers comparison pick)).Holds solution) ↔
      (frames levels).Entails (schema.compile pick).information
        (fun _ solution => (schema.compile pick).Holds solution) := by
  constructor
  · intro valid observer solution solved
    have moved := valid observer (solution ≫ comparison.inv)
      ((information_models schema pick stateIso helpers comparison commuting _).mpr
        (by simpa only [Category.assoc, comparison.inv_hom_id, Category.comp_id] using solved))
    have held := (guards schema pick stateIso helpers comparison commuting _).mp moved
    simpa only [Category.assoc, comparison.inv_hom_id, Category.comp_id] using held
  · intro valid observer solution solved
    exact (guards schema pick stateIso helpers comparison commuting solution).mpr
      (valid observer (solution ≫ comparison.hom)
        ((information_models schema pick stateIso helpers comparison commuting solution).mp solved))

omit stateIso commuting in
theorem selection :
    ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).selection =
      (schema.compile pick).selection := by
  change (⟨pick.val.taken, pick.val.read, _⟩ : Selection O) = ⟨pick.val.taken, pick.val.read, _⟩
  rw [(carry schema helpers comparison).erase.compile_made, schema.erase.compile_made]
  rfl

theorem checks [DecidableEq O] {answerFrame : Context rules} (answer : answerFrame ⟶ schema.helpers.frame) :
    (carry schema helpers comparison).NativeChecks (state := target)
        (choice schema helpers comparison pick) (answer ≫ comparison.inv) ↔ schema.NativeChecks pick answer := by
  unfold Schema.NativeChecks
  rw [shapes schema pick helpers comparison, selection schema pick helpers comparison,
    ← stateIso.present, solvable schema pick stateIso helpers comparison commuting,
    entails_guards schema pick stateIso helpers comparison commuting, outputs answer]

def basis {answerFrame : Context rules} {answer : answerFrame ⟶ schema.helpers.frame}
    (certificate : Basis levels O schema pick answer) :
    Basis levels O (carry schema helpers comparison) (state := target)
      (choice schema helpers comparison pick) (answer ≫ comparison.inv) := by
  cases certificate with
  | principal original =>
      have carried := SolverTransport.principal comparison original
      have same := information_equivalent schema pick stateIso helpers comparison commuting
      exact .principal
        ⟨(same _ _).mpr carried.sound,
          fun observer solution solved => carried.factors observer solution ((same _ _).mp solved)⟩
  | residual update licensed =>
      exact .residual ((SolverTransport.residual comparison update).rephrase
        (information_equivalent schema pick stateIso helpers comparison commuting))
        ((outputs update.answer).mpr licensed)

theorem residual_kept (update : ContextualDependentUpdate.Update levels (schema.compile pick).information)
    (licensed : ∀ output ∈ schema.outputs, output.At update.answer) :
    (basis schema pick stateIso helpers comparison commuting (.residual update licensed)).knowledge =
      update.remaining := rfl

theorem knowledge_equivalent {answerFrame : Context rules} {answer : answerFrame ⟶ schema.helpers.frame}
    (certificate : Basis levels O schema pick answer) :
    (frames levels).Equivalent
      (basis schema pick stateIso helpers comparison commuting certificate).knowledge certificate.knowledge := by
  cases certificate with
  | principal original =>
      intro observer further
      change (frames levels).Models further ((frames levels).applyStore (answer ≫ comparison.inv)
        ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).information) ↔
        (frames levels).Models further ((frames levels).applyStore answer (schema.compile pick).information)
      rw [Frames.models_applyStore, Frames.models_applyStore]
      change (frames levels).Models (further ≫ (answer ≫ comparison.inv))
        ((carry schema helpers comparison).compile (state := target) (choice schema helpers comparison pick)).information ↔
        (frames levels).Models (further ≫ answer) (schema.compile pick).information
      have same := information_models schema pick stateIso helpers comparison commuting (further ≫ (answer ≫ comparison.inv))
      simpa only [Category.assoc, comparison.inv_hom_id, Category.comp_id] using same
  | residual update licensed => exact fun _ _ => Iff.rfl

end SchemaTransport

namespace ApplicationTransport

variable (application : Application levels O source) (stateIso : PlainIso levels source target)
  (helpers : Helpers target.frame) (comparison : helpers.frame ≅ application.schema.helpers.frame)
  (commuting : comparison.hom ≫ application.schema.helpers.weaken = helpers.weaken ≫ stateIso.frame.hom)

def carry : Application levels O target where
  schema := SchemaTransport.carry application.schema helpers comparison
  pick := SchemaTransport.choice application.schema helpers comparison application.pick
  target := application.target
  answer := application.answer ≫ comparison.inv
  basis := SchemaTransport.basis application.schema application.pick stateIso helpers comparison commuting application.basis

theorem source_admits [DecidableEq O] :
    (carry application stateIso helpers comparison commuting).schema.Admits
        (carry application stateIso helpers comparison commuting).pick ↔
      application.schema.Admits application.pick :=
  (carry application stateIso helpers comparison commuting).basis.native_checks_iff.symm.trans
    ((SchemaTransport.checks application.schema application.pick stateIso helpers comparison commuting application.answer).trans
      application.basis.native_checks_iff)

theorem native_admits [DecidableEq O] :
    (realizationStep levels O).Admits (carry application stateIso helpers comparison commuting) ↔
      (realizationStep levels O).Admits application :=
  (realization_admits_iff _).trans
    ((source_admits application stateIso helpers comparison commuting).trans (realization_admits_iff _).symm)

theorem refinement_square :
    (carry application stateIso helpers comparison commuting).answer ≫ helpers.weaken ≫ stateIso.frame.hom =
      application.answer ≫ application.schema.helpers.weaken := by
  change (application.answer ≫ comparison.inv) ≫ helpers.weaken ≫ stateIso.frame.hom = _
  rw [Category.assoc, ← commuting, ← Category.assoc comparison.inv,
    comparison.inv_hom_id, Category.id_comp]

end ApplicationTransport

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ApplicationTransport.source_admits
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SchemaTransport.residual_kept
