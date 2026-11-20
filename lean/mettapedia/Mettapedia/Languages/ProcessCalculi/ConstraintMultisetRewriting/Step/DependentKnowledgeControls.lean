import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeDiamond
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunControls

/-!
# Genuine strengthening and inconsistent additions

The path/point publication diamond remains valid after learning X = Ground.
That equation is not already solved by the original identity interpretation.
Symbolic models extend through the actual helper pullbacks. An inconsistent
addition, in contrast, disables an originally admitted native firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {Γ : Context rules}

/-- The observing context is extended by the pulled-back helpers. This
preserves symbolic solvability and does not assert closed inhabitation. -/
theorem helpers_keep_solvability (helpers : Helpers Γ) (added : EquationStore (TotalTerm Γ))
    (solvable : (frames levels).Solvable added) :
    (frames levels).Solvable ((frames levels).applyStore helpers.weaken added) := by
  obtain ⟨observer, solution, solved⟩ := solvable
  refine ⟨(helpers.reindex solution).frame, Helpers.lift solution helpers,
    (Frames.models_applyStore (X := frames levels) helpers.weaken (Helpers.lift solution helpers) added).mpr ?_⟩
  change (frames levels).Models (Helpers.lift solution helpers ≫ helpers.weaken) added
  rw [Helpers.lift_weaken]
  exact Frames.models_comp (X := frames levels) solved (helpers.reindex solution).weaken

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls TelescopeControls KnowledgeChange

def variableType : TotalTerm base := ⟨smallUniverse base, ⟨.var 0, Derivable.var 0⟩⟩
def groundCode : TotalTerm base := ⟨smallUniverse base, ⟨ground, ground_typed _⟩⟩
def learned : EquationStore (TotalTerm base) := [(variableType, groundCode)]

def groundAssignment : point ⟶ base := pair (toEmpty point) ⟨ground, ground_typed _⟩

theorem learned_solvable : (frames setting.levels).Solvable learned := by
  refine ⟨point, groundAssignment, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change (frames setting.levels).E (variableType.reindex groundAssignment) (groundCode.reindex groundAssignment)
  have same : variableType.reindex groundAssignment = groundCode.reindex groundAssignment :=
    totalTerm_ext (TypeOver.ext rfl rfl) rfl
  rw [same]
  exact ((frames setting.levels).equivalence _).refl _

theorem genuinely_new_constraint : ¬ (frames setting.levels).Models (𝟙 base) learned := by
  intro models
  have equality := (models (variableType, groundCode) (List.mem_singleton_self _)).2
  change Equal Tower.rules base.raw (.var 0) ground (.head (.sort Tower.zero)) at equality
  have typeEquality : TypeEq Tower.rules base.raw (.var 0) ground := ⟨_, .sort _, equality⟩
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 0 : Tower.Tm 1) := .var 0
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) typeEquality base.formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

theorem final_consistent : FinalConsistent DependentRun.Controls.diamond.forward learned := by
  have first := helpers_keep_solvability (levels := setting.levels) pathHelpers learned learned_solvable
  have second := helpers_keep_solvability (levels := setting.levels) (pointHelpers.reindex pathHelpers.weaken)
    ((frames setting.levels).applyStore pathHelpers.weaken learned) first
  change (frames setting.levels).Solvable
    ((frames setting.levels).applyStore (pointHelpers.reindex pathHelpers.weaken).weaken
      ((frames setting.levels).applyStore pathHelpers.weaken learned) ++
        ([] : EquationStore (TotalTerm (pointHelpers.reindex pathHelpers.weaken).frame)))
  simpa only [List.append_nil] using second

theorem both_orders_licensed :
    RunConsistent DependentRun.Controls.diamond.forward learned ∧
      RunConsistent DependentRun.Controls.diamond.backward learned :=
  DependentRun.Controls.diamond.consistency_both learned final_consistent

noncomputable def strengthened_swap := DependentRun.Controls.diamond.strengthenedCell learned final_consistent

theorem helper_map_retained :
    (DependentRun.Controls.diamond.strengthened learned final_consistent).close.frame.hom =
      exchange pointHelpers pathHelpers := rfl

def idle : HelperFiring setting.levels Nat emptyState := ⟨.nil _, ⟨[], [], [], [], [], [], [], []⟩⟩

theorem idle_admitted : (helperStep setting.levels Nat).Admits idle := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => False.elim (List.not_mem_nil member)⟩,
    (enabled_iff _).mpr ?_, ⟨_, 𝟙 _, Frames.models_nil _⟩, ?_⟩
  · exact ⟨fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member)⟩
  · exact fun _ _ _ => ⟨fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member)⟩

theorem inconsistent_addition_refuses :
    ¬ (helperStep setting.levels Nat).Admits (KnowledgeChange.firing ContextualDependentWorklist.Controls.clash idle) := by
  intro admitted
  have solved := (KnowledgeChange.admits_iff _ idle idle_admitted).mp admitted
  have unchanged : pushed idle ContextualDependentWorklist.Controls.clash = ContextualDependentWorklist.Controls.clash :=
    Frames.applyStore_id (X := frames setting.levels) _
  change (frames setting.levels).Solvable (pushed idle ContextualDependentWorklist.Controls.clash ++ []) at solved
  rw [unchanged, List.append_nil] at solved
  exact ContextualDependentWorklist.Controls.clash_refuted solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeControls.both_orders_licensed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeControls.inconsistent_addition_refuses
