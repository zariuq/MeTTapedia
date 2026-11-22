import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSaturation

/-!
# Fixed answers, actual progress, and a stopping saturation policy

The closure law allows an infinite initial reading set. Finite closure is a
sufficient, not necessary, condition for a fixed stage. A growing protected
round allocates a genuinely new occurrence. At a fixed reading set, the
selected saturation policy adds no further physical firing.

This does not declare the underlying occurrence-bag machine terminal: it may
still admit duplicate-producing applications, observable through counts or
history rather than the reading-set observer used here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (consequence)
open StepWeb.KernelRounds

universe uOcc uValue uInstance

theorem stage_eq_finiteProofs_iff_fixed {G : Type uValue} {I : Type uInstance} [DecidableEq G]
    (rules : I → SetStoreClosure.Instance G) (seed : Set G) (n : Nat) :
    stage rules seed n = finiteProofs rules seed ↔
      immediate rules (stage rules seed n) = stage rules seed n := by
  constructor
  · intro complete
    rw [complete]
    apply Set.Subset.antisymm
    · rintro value (old | ⟨i, enabled, made⟩)
      · exact old
      · exact finiteProofs_closed rules seed i enabled made
    · exact immediate_extensive rules _
  · intro fixed
    have allStages : ∀ k, stage rules seed k ⊆ stage rules seed n := by
      intro k
      induction k with
      | zero => exact seed_subset_stage rules seed n
      | succ k ih =>
        intro value member
        rw [← fixed]
        rcases member with old | ⟨i, enabled, made⟩
        · exact Or.inl (ih old)
        · exact Or.inr ⟨i, fun premise inside => ih (enabled premise inside), made⟩
    apply Set.Subset.antisymm
    · intro value member
      exact ⟨n, member⟩
    · rintro value ⟨k, member⟩
      exact allStages k member

variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

def Saturated (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig) : Prop :=
  immediate (consequence judgmentTag arrowTag) (storeReadings s caller) = storeReadings s caller

theorem ProtectedRun.new_occurrence_of_reading_growth {caller : Subst rowSig}
    (execution : ProtectedRun judgmentTag arrowTag s caller)
    (growth : storeReadings execution.run.last execution.source ≠ storeReadings s caller) :
    ∃ o ∈ execution.run.last.present, o ∉ s.present := by
  classical
  by_contra none
  apply growth
  apply Set.Subset.antisymm
  · rintro value ⟨o, present, reading⟩
    have old : o ∈ s.present := by
      by_contra absent
      exact none ⟨o, present, absent⟩
    exact ⟨o, old, (execution.retained_reading_iff o old value).mp reading⟩
  · exact execution.readings_mono

theorem application_run_append_nil (run : (machine judgmentTag arrowTag O).Run s) :
    run.append (.nil run.last) = run := by
  induction run with
  | nil initial => rfl
  | cons f admitted rest ih => exact congrArg (Interface.Step.Run.cons f admitted) ih

variable [Infinite O]

theorem protectedRound_progress (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (growth : ¬ Saturated judgmentTag arrowTag s caller) :
    ∃ o ∈ (protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag) s caller known).run.last.present,
      o ∉ s.present := by
  apply ProtectedRun.new_occurrence_of_reading_growth
  rw [protectedRound_exact]
  exact growth

theorem saturationPrefix_saturated_iff (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (n : Nat) :
    Saturated judgmentTag arrowTag (saturationPrefix judgmentTag arrowTag s caller known n).run.last
        (saturationPrefix judgmentTag arrowTag s caller known n).source ↔
      storeReadings (saturationPrefix judgmentTag arrowTag s caller known n).run.last
          (saturationPrefix judgmentTag arrowTag s caller known n).source =
        saturationReadings judgmentTag arrowTag s caller known := by
  rw [Saturated, saturationPrefix_exact, saturationReadings_eq_finiteProofs]
  exact (stage_eq_finiteProofs_iff_fixed _ _ n).symm

theorem saturationPrefix_stops_run (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (n : Nat)
    (fixed : Saturated judgmentTag arrowTag (saturationPrefix judgmentTag arrowTag s caller known n).run.last
      (saturationPrefix judgmentTag arrowTag s caller known n).source) :
    (saturationPrefix judgmentTag arrowTag s caller known (n + 1)).run =
      (saturationPrefix judgmentTag arrowTag s caller known n).run := by
  change ((saturationPrefix judgmentTag arrowTag s caller known n).run.append
    (protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag)
      (saturationPrefix judgmentTag arrowTag s caller known n).run.last
      (saturationPrefix judgmentTag arrowTag s caller known n).source
      (saturationPrefix judgmentTag arrowTag s caller known n).known).run) = _
  rw [protectedRound_closed _ _ _ fixed]
  exact application_run_append_nil _

theorem saturationPrefix_stops_source (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (n : Nat)
    (fixed : Saturated judgmentTag arrowTag (saturationPrefix judgmentTag arrowTag s caller known n).run.last
      (saturationPrefix judgmentTag arrowTag s caller known n).source) :
    (saturationPrefix judgmentTag arrowTag s caller known (n + 1)).source =
      (saturationPrefix judgmentTag arrowTag s caller known n).source := by
  change (protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag)
    (saturationPrefix judgmentTag arrowTag s caller known n).run.last
    (saturationPrefix judgmentTag arrowTag s caller known n).source
    (saturationPrefix judgmentTag arrowTag s caller known n).known).source = _
  rw [protectedRound_closed _ _ _ fixed]
  rfl

theorem finite_saturation_has_fixed_prefix (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (finite : (saturationReadings judgmentTag arrowTag s caller known).Finite) :
    ∃ n, Saturated judgmentTag arrowTag (saturationPrefix judgmentTag arrowTag s caller known n).run.last
      (saturationPrefix judgmentTag arrowTag s caller known n).source := by
  classical
  obtain ⟨n, bounded⟩ := finite_premises_have_a_stage (consequence judgmentTag arrowTag)
    (storeReadings s caller) finite.toFinset (fun value member => by
      rw [← saturationReadings_eq_finiteProofs]
      exact finite.mem_toFinset.mp member)
  refine ⟨n, (saturationPrefix_saturated_iff s caller known n).mpr ?_⟩
  apply Set.Subset.antisymm
  · intro value member
    exact ⟨n, member⟩
  · intro value member
    rw [saturationPrefix_exact]
    exact bounded value (finite.mem_toFinset.mpr member)

#print axioms stage_eq_finiteProofs_iff_fixed
#print axioms ProtectedRun.new_occurrence_of_reading_growth
#print axioms protectedRound_progress
#print axioms saturationPrefix_saturated_iff
#print axioms saturationPrefix_stops_run
#print axioms saturationPrefix_stops_source
#print axioms finite_saturation_has_fixed_prefix

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
