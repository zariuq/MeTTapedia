import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces

/-! # General steps beyond the literal-store construction profile

Deduplicating genuine equations is exact by meaning and changes the store's
syntax. Adding a genuine consistent constraint is a strict refinement.
Both are ordinary steps. Restriction changes permission without deleting
the preparation or changing its effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ProfileControls

open AdmissionObservationCover.Controls (frame World)
open PreparedStep.Controls (bit no)
open EffectStoreControls (duplicated extra)

noncomputable def normalize : Step frame Nat (EquationStore (World → Bool)) (fun _ => Unit) :=
  Step.guarded (EffectCore.deduplicate frame ()) (fun _ _ _ => True)

instance normalization_exact : normalize.Exact := ⟨EffectCore.deduplicate_exact frame ()⟩

theorem normalization_prepared : normalize.Prepares (s := duplicated) () := by
  classical
  exact
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), (fun _ _ => false), by
      intro e h
      change e ∈ duplicated at h
      simp [duplicated] at h
      subst e
      rfl⟩⟩

theorem normalization_admitted : normalize.Admits (s := duplicated) () :=
  ⟨normalization_prepared, fun _ _ _ => trivial⟩

theorem normalization_result :
    normalize.result (s := duplicated) () normalization_admitted = [(bit, no)] := by
  classical
  simp [normalize, Step.result, Step.guarded, Step.ofEffect, EffectCore.deduplicate,
    EffectCore.storeAction, duplicated, List.eraseDups_cons]

theorem normalization_not_literal : ¬normalize.LiteralKnowledge := by
  classical
  intro literal
  apply EffectStoreControls.normalization_changes_syntax
  calc
    _ = frame.applyStore (frame.id ()) duplicated :=
      literal.knowledge (s := duplicated) () normalization_prepared
    _ = duplicated := Frames.applyStore_id _

noncomputable def normalizedRun : normalize.Run duplicated :=
  .cons () normalization_admitted (.nil _)

theorem normalization_run_changes_store : normalizedRun.last ≠ duplicated := by
  exact EffectStoreControls.normalization_changes_syntax

theorem normalization_covers : SettlementCoverage.CoversSettlement normalize := by
  apply SettlementCoverage.covers_of_retracts
  intro _ _ _
  exact ⟨frame.id (), fun _ => rfl⟩

def strict : Step frame Nat (EquationStore (World → Bool)) (fun _ => Unit) :=
  Step.guarded (EffectCore.tell frame () extra) (fun _ _ _ => True)

theorem strict_admitted : strict.Admits (s := []) () :=
  ⟨EffectStoreControls.tell_prepared, fun _ _ _ => trivial⟩

theorem strict_not_exact : ¬strict.Exact := fun exactness =>
  EffectStoreControls.tell_not_exact exactness.exactness

theorem strict_result_consistent :
    frame.Solvable (a := ()) (strict.knowledge (strict.result (s := []) () strict_admitted)) :=
  EffectStoreControls.tell_result_solvable

/-- Even an everywhere-refusing policy retains the candidate's prepared effect. -/
noncomputable def denied : Step frame Nat (EquationStore (World → Bool)) (fun _ => Unit) :=
  Spaces.restrict normalize (fun _ => False)

theorem refused_but_prepared : denied.Prepares (s := duplicated) () ∧
    ¬denied.Admits (s := duplicated) () :=
  ⟨normalization_prepared, fun admitted => admitted.2⟩

theorem refused_effect_unchanged :
    denied.preparedResult (s := duplicated) () refused_but_prepared.1 =
      normalize.preparedResult (s := duplicated) () normalization_prepared := rfl

theorem no_refused_success_event : ¬Nonempty (denied.effectCore.Event denied.eventAdmission
    duplicated [(bit, no)]) := by
  rintro ⟨event⟩
  exact event.permitted.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ProfileControls
