import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationResultTransport

/-!
# Recertifying the result frame of an actual source application

A contextual comparison of the published result supplies an invertible map
of answer frames and equivalent result knowledge. The recertified exact
update uses the requested target knowledge literally, retaining its residual
constraints. Its source schema and selected occurrences are unchanged.
This does not invert a solver refinement or claim a new principal answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TargetChange

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]
  {source target : State rules O}
  (original : Application levels O source) (admitted : original.schema.Admits original.pick)
  (comparison : PlainIso levels (original.sourceResult admitted) target)

def answer : target.frame ⟶ original.schema.helpers.frame := comparison.frame.hom ≫ original.answer

def update : ContextualDependentUpdate.Update levels original.compile.information where
  target := target.frame
  answer := answer original admitted comparison
  remaining := target.knowledge
  sound := by
    intro observer further solved
    have transported := (comparison.knowledge observer further).mpr solved
    have before := (Frames.models_applyStore (X := frames levels) comparison.frame.hom further original.basis.knowledge).mp transported
    have originalModels := original.basis.sound (further ≫ comparison.frame.hom) before
    change (frames levels).Models (further ≫ (comparison.frame.hom ≫ original.answer)) original.compile.information
    exact Eq.mp (congrArg (fun map : observer ⟶ original.schema.helpers.frame =>
      (frames levels).Models map original.compile.information) (Category.assoc further comparison.frame.hom original.answer))
      originalModels
  complete := by
    intro observer solution solved
    obtain ⟨further, remaining, agree⟩ := original.basis.covers solution solved
    refine ⟨further ≫ comparison.frame.inv, ?_, ?_⟩
    · apply (comparison.knowledge observer (further ≫ comparison.frame.inv)).mp
      apply (Frames.models_applyStore (X := frames levels) comparison.frame.hom
        (further ≫ comparison.frame.inv) original.basis.knowledge).mpr
      change (frames levels).Models ((further ≫ comparison.frame.inv) ≫ comparison.frame.hom) original.basis.knowledge
      have cancels : (further ≫ comparison.frame.inv) ≫ comparison.frame.hom = further :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun map => further ≫ map) comparison.frame.inv_hom_id).trans (Category.comp_id _))
      exact Eq.mpr (congrArg (fun map : observer ⟶ original.target =>
        (frames levels).Models map original.basis.knowledge) cancels) remaining
    · intro term
      have old := agree term
      change (frames levels).E (term.reindex solution) (term.reindex (further ≫ original.answer)) at old
      change (frames levels).E (term.reindex solution)
        (term.reindex ((further ≫ comparison.frame.inv) ≫ (comparison.frame.hom ≫ original.answer)))
      have cancels : (further ≫ comparison.frame.inv) ≫ (comparison.frame.hom ≫ original.answer) =
          further ≫ original.answer :=
        (Category.assoc _ _ _).trans
          (congrArg (fun map => further ≫ map) (comparison.frame.inv_hom_id_assoc original.answer))
      exact Eq.mpr (congrArg (fun map : observer ⟶ original.schema.helpers.frame =>
        (frames levels).E (term.reindex solution) (term.reindex map)) cancels) old

theorem outputs : ∀ code ∈ original.schema.outputs, code.At (answer original admitted comparison) :=
  fun code member => code.at_precompose (original.source_licenses admitted code member) comparison.frame.hom

def application : Application levels O source where
  schema := original.schema
  pick := original.pick
  target := target.frame
  answer := answer original admitted comparison
  basis := .residual (update original admitted comparison) (outputs original admitted comparison)

theorem source_admitted :
    (application original admitted comparison).schema.Admits (application original admitted comparison).pick := admitted

theorem native_admitted : (realizationStep levels O).Admits (application original admitted comparison) :=
  (realization_admits_iff _).mpr (source_admitted original admitted comparison)

theorem exact_residual : (application original admitted comparison).basis.knowledge = target.knowledge := rfl

theorem old_schema : (application original admitted comparison).schema = original.schema := rfl

theorem old_occurrences : (application original admitted comparison).pick.val = original.pick.val := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TargetChange

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TargetChange.update
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.TargetChange.native_admitted
