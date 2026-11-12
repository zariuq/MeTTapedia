import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationConservativity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentSchemaQueryControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.SetExtensionality

/-!
# Publication does not erase guard or equality boundaries

The actual dependent absence controls retain their verdicts. Counting uses
the complete present region; adding a matching occurrence changes admission.
Extensional evidence is retained as evidence and does not become a new
definitional equation of the intensional frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.GuardControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls

abbrev absenceSchema := DependentProgram.QueryControls.absenceSchema
abbrev absencePick := DependentProgram.QueryControls.absencePick

theorem absence_outputs_typed : ∀ made ∈ absenceSchema.makes, made.WellTyped := by
  intro made member
  cases member

def absenceApplication (knowledge : EquationStore (TotalTerm triple)) :
    Application setting.levels Nat (queryState knowledge) :=
  FrameTyped.application absenceSchema absence_outputs_typed absencePick

theorem unknown_type_still_refuses_absence :
    ¬ (realizationStep setting.levels Nat).Admits (absenceApplication []) := by
  intro admitted
  exact DependentProgram.QueryControls.unknown_type_refuses_absence
    ((FrameTyped.admits_iff (state := queryState []) absenceSchema absence_outputs_typed absencePick).mp admitted)

theorem function_type_still_admits_absence :
    (realizationStep setting.levels Nat).Admits (absenceApplication [(xUniverse, arrowUniverse)]) :=
  (FrameTyped.admits_iff (state := queryState [(xUniverse, arrowUniverse)]) absenceSchema absence_outputs_typed absencePick).mpr
    DependentProgram.QueryControls.function_type_admits_absence

def countedRow : TotalTerm point := ⟨groundType point, ⟨.var 0, Derivable.var 0⟩⟩

def countedState (present : Finset Nat) : State Tower.rules Nat := ⟨point, [], present, fun _ => countedRow⟩

def countSchema (number : Nat) : DependentProgram.Schema setting.levels Nat point where
  helpers := .nil _
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.count setting.levels Nat countedRow number]

def countPick (number : Nat) : DependentProgram.Pick (countSchema number) := ⟨⟨[], [], []⟩, rfl⟩

theorem count_outputs_typed (number : Nat) : ∀ made ∈ (countSchema number).makes, made.WellTyped := by
  intro made member
  cases member

def countApplication (present : Finset Nat) (number : Nat) :
    Application setting.levels Nat (countedState present) :=
  FrameTyped.application (countSchema number) (count_outputs_typed number) (countPick number)

theorem complete_count_iff (present : Finset Nat) (number : Nat) {target : Context Tower.rules}
    (substitution : target ⟶ point) :
    (Query.count setting.levels Nat countedRow number).Holds present (fun _ => countedRow) substitution ↔
      present.card = number := by
  constructor
  · rintro ⟨seen, covers, counted⟩
    have full : seen = present := by
      apply Finset.ext
      intro occurrence
      rw [covers]
      exact and_iff_left (((frames setting.levels).equivalence target).refl _)
    exact full ▸ counted
  · intro counted
    exact ⟨present, fun _ => (and_iff_left (((frames setting.levels).equivalence target).refl _)).symm,
      counted⟩

theorem count_admits_iff (present : Finset Nat) (number : Nat) :
    (realizationStep setting.levels Nat).Admits (countApplication present number) ↔ present.card = number := by
  constructor
  · intro admitted
    have holds := admitted.2.2.2 point (𝟙 point) (Frames.models_nil _)
    exact (complete_count_iff present number (𝟙 point)).mp
      (holds.2 _ (List.mem_singleton_self _))
  · intro counted
    refine ⟨⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl⟩, (fun _ member => nomatch member)⟩,
      ?_, ⟨point, 𝟙 point, Frames.models_nil _⟩, ?_⟩
    · apply (DependentFull.enabled_iff (countApplication present number).compile).mpr
      exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member),
        (fun _ member => nomatch member), (fun _ member => nomatch member)⟩
    · intro target substitution _
      refine ⟨Frames.models_nil _, ?_⟩
      intro query member
      obtain rfl := List.mem_singleton.mp member
      exact (complete_count_iff present number substitution).mpr counted

theorem matching_extension_changes_count :
    (realizationStep setting.levels Nat).Admits (countApplication {1} 1) ∧
      ¬ (realizationStep setting.levels Nat).Admits (countApplication {1, 2} 1) := by
  constructor
  · exact (count_admits_iff {1} 1).mpr (by decide)
  · intro admitted
    have impossible := (count_admits_iff {1, 2} 1).mp admitted
    contradiction

open ProgrammingOnTheStep.SetExtensionality

def extensionalitySchema : DependentProgram.Schema setting.levels Nat evidenceState.frame where
  helpers := extensionalityFiring.helpers
  takes := extensionalityFiring.takes
  reads := extensionalityFiring.reads
  makes := []
  tells := extensionalityFiring.tells
  guards := []
  queries := []

def extensionalityPick : DependentProgram.Pick extensionalitySchema := ⟨⟨[], [0, 1], []⟩, rfl⟩

theorem extensionality_outputs_typed : ∀ made ∈ extensionalitySchema.makes, made.WellTyped := by
  intro made member
  cases member

def extensionalityApplication : Application setting.levels Nat evidenceState :=
  FrameTyped.application extensionalitySchema extensionality_outputs_typed extensionalityPick

theorem extensional_evidence_is_not_conversion :
    ¬ (realizationStep setting.levels Nat).Admits extensionalityApplication := by
  intro admitted
  have source := (FrameTyped.admits_iff extensionalitySchema extensionality_outputs_typed extensionalityPick).mp admitted
  exact extensionality_refused ((extensionalitySchema.compile_admits_iff extensionalityPick).mpr source)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.GuardControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.GuardControls.count_admits_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.GuardControls.extensional_evidence_is_not_conversion
