import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedStep

/-! # Store normalization and strict refinement as prepared effects

These are knowledge-only effects: occurrences are unchanged. Deduplication
really changes the store representation while preserving every solution;
telling additional equations can strictly reduce the solution family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH

namespace EffectCore

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (a : Obj)

abbrev storeAction (update : EquationStore (Tm a) → EquationStore (Tm a))
    (reflects : ∀ (store : EquationStore (Tm a)) {b : Obj} (σ : Hom a b),
      X.Models σ (update store) → X.Models σ store) :
    EffectCore X Nat (EquationStore (Tm a)) (fun _ => Unit) where
  frame _ := a
  knowledge s := s
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := a
  extension _ := X.id a
  information {s} _ := s
  information_refines _ := by
    intro b σ solved
    exact (Frames.models_congr (fun t => Frames.act_comp_id σ t) _).mp solved
  Shapes _ := ([] : List Nat).Nodup
  preparedResult {s} _ _ := update s
  present_preparedResult _ _ := by ext o; simp [fire, Selection.commit]
  preparedSettle _ _ := X.id a
  result_refines {s} _ _ := by
    intro b σ solved
    exact (Frames.models_congr (fun t => Frames.act_comp_id σ t) _).mp (reflects s σ solved)

noncomputable abbrev deduplicate :
    EffectCore X Nat (EquationStore (Tm a)) (fun _ => Unit) := by
  classical
  exact storeAction X a List.eraseDups (fun store _ σ solved e member =>
    solved e (List.mem_eraseDups.mpr member))

theorem deduplicate_exact : (deduplicate X a).ExactKnowledge := by
  classical
  intro s f p b σ solved e member
  have back : X.Models σ s :=
    (Frames.models_congr (fun t => (Frames.act_comp_id σ t).symm) s).mp solved
  exact back e (List.mem_eraseDups.mp member)

abbrev tell (extra : EquationStore (Tm a)) :
    EffectCore X Nat (EquationStore (Tm a)) (fun _ => Unit) :=
  storeAction X a (· ++ extra) (fun _ _ _ solved e member =>
    solved e (List.mem_append_left extra member))

end EffectCore

namespace EffectStoreControls

open AdmissionObservationCover.Controls (World frame)
open PreparedStep.Controls (bit no)

def duplicated : EquationStore (World → Bool) := [(bit, no), (bit, no)]

theorem normalization_changes_syntax :
    (EffectCore.deduplicate frame ()).knowledge
      ((EffectCore.deduplicate frame ()).preparedResult (s := duplicated) ()
        ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
          ⟨(), (fun _ _ => false), by intro e he; simp [duplicated] at he; subst e; rfl⟩⟩) ≠
      duplicated := by
  classical
  simp [duplicated, List.eraseDups_cons]

def extra : EquationStore (World → Bool) := [(bit, no)]

theorem tell_prepared : (EffectCore.tell frame () extra).Prepares (s := []) () :=
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), id, Frames.models_nil _⟩⟩

/-- A consistent strictly stronger result is allowed, but it is not exact. -/
theorem tell_not_exact : ¬ (EffectCore.tell frame () extra).ExactKnowledge := by
  intro exactness
  have wrong := exactness (s := []) () tell_prepared (b := ()) id (Frames.models_nil _)
  have equality := wrong (bit, no) (List.mem_singleton_self _)
  have point := congrFun equality (fun _ => true)
  cases point

theorem tell_result_solvable :
    frame.Solvable (a := ())
      ((EffectCore.tell frame () extra).knowledge
        ((EffectCore.tell frame () extra).preparedResult (s := []) () tell_prepared)) := by
  refine ⟨(), (fun _ _ => false), ?_⟩
  intro e he
  have same : e = (bit, no) := List.mem_singleton.mp he
  subst e
  rfl

/-- Dropping a necessary equation does not satisfy the local refinement obligation. -/
theorem cannot_forget_constraint :
    ¬ (∀ σ : World → World, frame.Models (a := ()) (b := ()) σ [] →
      frame.Models (a := ()) (b := ()) σ extra) := by
  intro forgotten
  have equality := forgotten id (Frames.models_nil _) (bit, no) (List.mem_singleton_self _)
  have point := congrFun equality (fun _ => true)
  cases point

end EffectStoreControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
