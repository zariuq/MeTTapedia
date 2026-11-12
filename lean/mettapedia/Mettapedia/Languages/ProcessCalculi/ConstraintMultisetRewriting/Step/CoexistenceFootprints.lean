import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence

/-!
# Exact resource conditions for framing

Growing the occurrence store preserves the positive inputs. Preparation then
requires freshness against the context and the actual query checks. To leave
the context unchanged, consumption must also avoid its identities. Read/read
overlap is unrestricted by these conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uR

open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire fire_union_frame)

namespace Coexistence.Footprints

variable {O : Type uOcc} {R : Type uR} [DecidableEq O]

theorem enabled_union_iff (label : O → R) (store context : Finset O) (commit : Commit O R)
    (enabled : Enabled label store commit) :
    Enabled label (store ∪ context) commit ↔ Disjoint commit.made context ∧
      ∀ query ∈ commit.queries, query.Holds label (store ∪ context) := by
  constructor
  · intro combined
    exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_right combined.fresh,
      combined.queries_hold⟩
  · rintro ⟨fresh, queries⟩
    exact ⟨enabled.taken_subset.trans Finset.subset_union_left,
      enabled.kept_subset.trans Finset.subset_union_left, enabled.apart,
      Finset.disjoint_union_right.mpr ⟨enabled.fresh, fresh⟩, queries⟩

theorem selection_enabled_union_iff (store context : Finset O) (selection : Selection O)
    (enabled : Enabled (fun _ : O => ()) store (selection.commit (T := Unit))) :
    Enabled (fun _ : O => ()) (store ∪ context) (selection.commit (T := Unit)) ↔
      Disjoint selection.made.toFinset context := by
  rw [enabled_union_iff _ _ _ _ enabled]
  simp [Selection.commit]

theorem fire_preserves_context_iff (label : O → R) (store context : Finset O)
    (commit : Commit O R) (enabled : Enabled label store commit) :
    fire (store ∪ context) commit = fire store commit ∪ context ↔
      Disjoint commit.taken context := by
  constructor
  · intro unchanged
    apply Finset.disjoint_left.mpr
    intro occurrence taken inContext
    have member : occurrence ∈ fire (store ∪ context) commit := by
      rw [unchanged]
      exact Finset.mem_union_right _ inContext
    rcases mem_fire.mp member with ⟨_, notTaken⟩ | made
    · exact notTaken taken
    · exact Finset.disjoint_left.mp enabled.fresh made (enabled.taken_subset taken)
  · intro apart
    exact fire_union_frame apart

end Coexistence.Footprints

namespace EffectCore

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (effect : EffectCore X O State Firing)

theorem prepared_context_enabled_iff {state : State} (firing : Firing state)
    (prepared : effect.Prepares firing) (context : Finset O) :
    Enabled (fun _ : O => ()) (effect.present state ∪ context)
        ((effect.selection firing).commit (T := Unit)) ↔
      Disjoint (effect.selection firing).made.toFinset context :=
  Coexistence.Footprints.selection_enabled_union_iff _ _ _ prepared.2.1

end EffectCore
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
