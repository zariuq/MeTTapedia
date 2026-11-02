import Mettapedia.GSLT.Parsing.ClassAwareGroundedChart
import Mettapedia.GSLT.Parsing.ClassAwareChartIndex

/-! Hash-indexed root reachability with exact agreement to the existing Horn
closure. Saturation and root pruning remain distinct operations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartPruning

open ClassAwarePackedForest ClassAwareGroundedChart ClassAwareNativeForestQualification
open ClassAwareParserPackCorrespondence ParserProfileSemantics

def expand (source : Forest) (seen : List NodeKey) : List NodeKey :=
  let index : Std.HashSet NodeKey := .ofList seen
  Mettapedia.Util.LinearHash.eraseDupsFast (seen ++ source.families.flatMap fun family =>
    if index.contains family.parent then familyChildNodes family else [])

theorem expand_exact (source : Forest) (seen : List NodeKey) :
    expand source seen = (seen ++ source.families.flatMap fun family =>
      if family.parent ∈ seen then familyChildNodes family else []).eraseDups := by
  simp [expand, Mettapedia.Util.LinearHash.eraseDupsFast_eq]

theorem mem_expand (source : Forest) (seen : List NodeKey) (key : NodeKey) :
    key ∈ expand source seen ↔ key ∈ seen ∨
      ∃ family ∈ source.families, family.parent ∈ seen ∧ key ∈ familyChildNodes family := by
  simp [expand, Mettapedia.Util.LinearHash.eraseDupsFast_eq, List.mem_flatMap]

def Closed (source : Forest) (seen : List NodeKey) : Prop :=
  ∀ family ∈ source.families, family.parent ∈ seen →
    ∀ key ∈ familyChildNodes family, key ∈ seen

theorem expand_contains (source : Forest) (seen : List NodeKey) : seen ⊆ expand source seen :=
  fun _ member => (mem_expand _ _ _).mpr (Or.inl member)

theorem fixed_closed {source : Forest} {seen : List NodeKey} (fixed : expand source seen = seen) :
    Closed source seen := by
  intro family member parent key child
  rw [← fixed]
  exact (mem_expand _ _ _).mpr (Or.inr ⟨family, member, parent, child⟩)

theorem expand_sound {source : Forest} {seen : List NodeKey}
    (sound : ∀ key ∈ seen, key ∈ reachableNodes source) :
    ∀ key ∈ expand source seen, key ∈ reachableNodes source := by
  intro key member
  rcases (mem_expand _ _ _).mp member with old | ⟨family, present, parent, child⟩
  · exact sound key old
  · exact child_mem_reachableNodes present (sound family.parent parent) child

def finish? (source : Forest) : Nat → List NodeKey → Option (List NodeKey)
  | 0, _ => none
  | rounds + 1, seen =>
    let next := expand source seen
    if next == seen then some seen else finish? source rounds next

theorem finish?_closed {source : Forest} (rounds : Nat) (seed found : List NodeKey)
    (finished : finish? source rounds seed = some found) : seed ⊆ found ∧ Closed source found := by
  induction rounds generalizing seed with
  | zero => cases finished
  | succ rounds ih =>
    simp only [finish?] at finished
    split at finished
    · rename_i fixed
      cases Option.some.inj finished
      exact ⟨fun _ member => member, fixed_closed (by simpa only [beq_iff_eq] using fixed)⟩
    · obtain ⟨contains, closed⟩ := ih _ finished
      exact ⟨fun _ member => contains (expand_contains _ _ member), closed⟩

theorem finish?_sound {source : Forest} (rounds : Nat) (seed found : List NodeKey)
    (sound : ∀ key ∈ seed, key ∈ reachableNodes source)
    (finished : finish? source rounds seed = some found) :
    ∀ key ∈ found, key ∈ reachableNodes source := by
  induction rounds generalizing seed with
  | zero => cases finished
  | succ rounds ih =>
    simp only [finish?] at finished
    split at finished
    · cases Option.some.inj finished
      exact sound
    · exact ih _ (expand_sound sound) finished

theorem closed_covers_reachable {source : Forest} {seen : List NodeKey}
    (roots : source.roots ⊆ seen) (closed : Closed source seen) :
    ∀ key ∈ reachableNodes source, key ∈ seen := by
  intro key member
  have derived := (FiniteHornSaturation.saturateFast_iff_derivable
    (reachabilityProgram source) source.roots.toFinset key).mp member
  apply List.mem_toFinset.mp
  apply Mettapedia.Logic.LP.derivable_subset_of_closed
    (reachabilityProgram source) source.roots.toFinset seen.toFinset ?_ ?_ key derived
  · intro root rootMember
    exact List.mem_toFinset.mpr (roots (List.mem_toFinset.mp rootMember))
  · intro rule member premises
    simp only [reachabilityProgram, List.mem_toFinset, List.mem_flatMap, List.mem_map] at member
    obtain ⟨family, familyMember, child, childMember, rfl⟩ := member
    apply List.mem_toFinset.mpr
    apply closed family familyMember
    · exact List.mem_toFinset.mp (premises (by simp [reachabilityRule]))
    · exact childMember

def budget (source : Forest) : Nat :=
  source.roots.length + source.families.length +
    (source.families.flatMap familyChildNodes).length + 1

def prune? (source : Forest) : Option Forest :=
  (finish? source (budget source) source.roots).map fun seen =>
    let index : Std.HashSet NodeKey := .ofList seen
    { source with families := source.families.filter (fun family => index.contains family.parent) }

theorem prune?_exact {source result : Forest} (pruned : prune? source = some result) :
    result = rootReachableForest source := by
  obtain ⟨seen, finished, resultEq⟩ := Option.map_eq_some_iff.mp pruned
  obtain ⟨roots, closed⟩ := finish?_closed _ _ _ finished
  have sound := finish?_sound _ _ _ (fun _ member => root_mem_reachableNodes member) finished
  have complete := closed_covers_reachable roots closed
  rw [← resultEq]
  unfold rootReachableForest
  dsimp only
  apply congrArg (Forest.mk source.roots)
  apply List.filter_congr
  intro family member
  apply Bool.eq_iff_iff.mpr
  simp only [Std.HashSet.contains_iff_mem, Std.HashSet.mem_ofList, List.contains_iff_mem, decide_eq_true_eq]
  exact ⟨sound family.parent, complete family.parent⟩

theorem prune?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {source result : Forest}
    (complete : RootParserComplete source profile plan input)
    (pruned : prune? source = some result) : RootParserComplete result profile plan input := by
  rw [prune?_exact pruned]
  exact rootReachable_complete complete

end Mettapedia.GSLT.Parsing.ClassAwareChartPruning
