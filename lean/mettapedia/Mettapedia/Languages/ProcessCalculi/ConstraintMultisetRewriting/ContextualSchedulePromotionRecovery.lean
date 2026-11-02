import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathModelRestriction

/-!
# Actual contextual paths recover guard-retaining schedule data

Recovery extracts the original rule, selected ports, output labels and
computed solver receipt. Its certificate stores those data and an independently
compiled question list, never the input path. Conversely, accepted data build
the original path. Both directions retain the entire endpoint inventory and
the selected occurrence/fuel lists; no final-state-only quotient is taken.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualInteractionFactors

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

namespace Prepared

variable {before after : Endpoint locals O Γ sort}

def ofFiring (edge : Firing locals before after) : Prepared locals before where
  rule := edge.rule
  ruleCovered := edge.ruleCovered
  selection := edge.selection
  outputs := edge.outputs
  formation := ⟨edge.admitted.take_length, edge.admitted.read_length, edge.admitted.outputs⟩
  resources := (resources_iff edge.outputs edge.selection before.inventory.configuration.present).mpr
    ⟨edge.admitted.take_distinct, edge.admitted.output_distinct, edge.admitted.occurrences⟩
  fuel := edge.fuel
  update := edge.update
  computed := edge.computed
  finished := edge.empty

theorem target_ofFiring (edge : Firing locals before after) :
    (ofFiring edge).target = after := edge.destination.symm

theorem checked_ofFiring (edge : Firing locals before after) :
    Checked locals (ofFiring edge).questions := by
  intro question member
  obtain ⟨check, present, rfl⟩ := List.mem_map.mp member
  exact edge.admitted.checks check present

end Prepared

namespace Certificate

variable {source target other : Endpoint locals O Γ sort}

def castTarget (certificate : Certificate locals source target) (same : target = other) :
    Certificate locals source other := same ▸ certificate

@[simp] theorem questions_castTarget (certificate : Certificate locals source target) (same : target = other) :
    (certificate.castTarget same).questions = certificate.questions := by
  cases same
  rfl

@[simp] theorem selections_castTarget (certificate : Certificate locals source target) (same : target = other) :
    (certificate.castTarget same).selections = certificate.selections := by
  cases same
  rfl

@[simp] theorem fuels_castTarget (certificate : Certificate locals source target) (same : target = other) :
    (certificate.castTarget same).fuels = certificate.fuels := by
  cases same
  rfl

/-- Every actual path supplies independently inspectable data and every
original guard at its own prefix. The input path is not a certificate field. -/
theorem recover (path : Quiver.Path source target) :
    ∃ certificate : Certificate locals source target,
      Checked locals certificate.questions ∧
      certificate.selections = ContextualExecution.selections path ∧
      certificate.fuels = ContextualExecution.fuels path := by
  induction path with
  | nil => exact ⟨.nil source, by simp [Checked, questions], rfl, rfl⟩
  | cons past edge earlier =>
      obtain ⟨certificate, checked, selected, spent⟩ := earlier
      let prepared := Prepared.ofFiring edge
      let completed := (Certificate.snoc certificate prepared).castTarget (Prepared.target_ofFiring edge)
      refine ⟨completed, ?_, ?_, ?_⟩
      · change Checked locals ((Certificate.snoc certificate prepared).castTarget _).questions
        rw [questions_castTarget]
        exact (checked_append_iff locals _ _).mpr ⟨checked, Prepared.checked_ofFiring edge⟩
      · change ((Certificate.snoc certificate prepared).castTarget _).selections = _
        rw [selections_castTarget, selections, selected]
        rfl
      · change ((Certificate.snoc certificate prepared).castTarget _).fuels = _
        rw [fuels_castTarget, fuels, spent]
        rfl

/-- Existence is equivalent at the original full typed endpoint, not merely
at its visible answer or final occurrence set. -/
theorem actual_path_iff_checked_certificate :
    Nonempty (Quiver.Path source target) ↔
      ∃ certificate : Certificate locals source target, Checked locals certificate.questions := by
  constructor
  · rintro ⟨path⟩
    obtain ⟨certificate, checked, _selected, _spent⟩ := recover path
    exact ⟨certificate, checked⟩
  · rintro ⟨certificate, checked⟩
    exact ⟨certificate.realize checked⟩

theorem final_models_restrict_to_original_equations
    (certificate : Certificate locals source target) (checked : Checked locals certificate.questions)
    {Future : Type} {future : Future → MetaArity S} (candidate : Assignment target.declarations future)
    (models : ContextualFrameUnifier.Models candidate target.inventory.configuration.equations) :
    ContextualFrameUnifier.Models
      (Assignment.compose candidate (ContextualExecution.pathAssignment (certificate.realize checked)))
      source.inventory.configuration.equations :=
  ContextualExecution.models_restrict_to_prefix (certificate.realize checked) candidate models

end Certificate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
