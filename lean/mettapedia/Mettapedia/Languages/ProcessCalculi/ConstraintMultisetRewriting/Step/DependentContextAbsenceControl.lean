import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextPlacement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# A native absence check invalidated by an added occurrence

The firing consumes and creates nothing. It is admitted in the empty store,
but adding one matching row refutes its actual natural absence query. Thus
resource disjointness alone cannot license its contextual placement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextAbsenceControl

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull.Controls ContextPlacement

def absentQuery : NaturalQuery setting.levels Nat base := NaturalQuery.predicate setting.levels Nat .none (baseState.label 0)

def checker : HelperFiring setting.levels Nat baseState :=
  ⟨.nil _, ⟨[], [], [], [], [], [], [], [absentQuery]⟩⟩

theorem admitted : (helperStep setting.levels Nat).Admits checker := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => False.elim (List.not_mem_nil member)⟩,
    (enabled_iff _).mpr ?_, ⟨_, 𝟙 _, Frames.models_nil _⟩, ?_⟩
  · exact ⟨fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member),
      fun _ member => False.elim (List.not_mem_nil member)⟩
  · intro observer solution solved
    refine ⟨Frames.models_nil _, ?_⟩
    intro query member
    obtain rfl := List.mem_singleton.mp member
    apply (NaturalQuery.predicate_holds_iff _ _ _ _ _).mpr
    apply (Query.predicate_holds_iff _ _ _ _ _).mpr
    intro occurrence inside
    exact False.elim (Finset.notMem_empty _ inside)

theorem added_row_refuses : ¬ (helperStep setting.levels Nat).Admits (firing {1} checker) := by
  intro accepted
  have holds := (accepted.2.2.2 base (𝟙 base) (Frames.models_nil _)).2 absentQuery.toQuery (List.mem_singleton_self _)
  have absent := (Query.predicate_holds_iff _ _ _ _ _).mp
    ((NaturalQuery.predicate_holds_iff _ _ _ _ _).mp holds)
  have missing := absent 1 (by decide)
  apply missing
  have row : (firing {1} checker).toFiring.row 1 = baseState.label 0 :=
    (frames setting.levels).act_id _
  rw [row]
  exact ((frames setting.levels).equivalence _).refl _

theorem resource_disjointness_is_insufficient :
    Disjoint checker.toFiring.taken.toFinset ({1} : Finset Nat) ∧
      Disjoint checker.toFiring.made.toFinset ({1} : Finset Nat) ∧ ¬ Safe {1} checker := by
  refine ⟨by decide, by decide, ?_⟩
  intro safe
  exact added_row_refuses (ContextPlacement.admits {1} checker admitted safe.fresh safe.queries)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextAbsenceControl

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextAbsenceControl.added_row_refuses
