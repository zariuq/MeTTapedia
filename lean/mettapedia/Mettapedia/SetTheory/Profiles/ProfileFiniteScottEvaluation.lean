import Mettapedia.SetTheory.Profiles.ProfileFiniteScottCoherence

/-!
# Stable-stage evaluation of finite canonical graph observations

Equality, membership, and first authored member origins can be evaluated at
any checked stable quotient stage. The comparison theorems connect those
observations to the complete cardinal-bounded construction. The raw counting
refinement can likewise stop at a verified fixed table. These are computational
comparisons within the constructed finite model.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileFiniteScottEvaluation

open Mettapedia.SetTheory.Profiles
open ProfileFiniteScottReadout ProfileFiniteScottCollapse
open ConstructiveFinite
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open UnfoldingIdentityComparison

universe u

theorem canonical_before_stopped (graph : FiniteGraph.{u}) (count : Nat)
    (bound : count ≤ size (α := graph.Node))
    (unchanged : (graph.iterate count).stopped) (first second : graph.Node) :
    graph.canonicalProjection first = graph.canonicalProjection second ↔
      graph.iterateProjection count first = graph.iterateProjection count second := by
  obtain ⟨later, same⟩ := Nat.exists_eq_add_of_le bound
  change graph.iterateProjection (size (α := graph.Node)) first =
    graph.iterateProjection (size (α := graph.Node)) second ↔ _
  rw [same]
  exact ProfileFiniteScottCoherence.FiniteGraph.projection_after_stopped_kernel
    graph count unchanged later first second

theorem equivalent_before_stopped (graph : FiniteGraph.{u}) (count : Nat)
    (bound : count ≤ size (α := graph.Node))
    (unchanged : (graph.iterate count).stopped) (first second : graph.Node) :
    graph.canonicalEquivalent first second = true ↔
      graph.iterateProjection count first = graph.iterateProjection count second :=
  (graph.canonicalEquivalent_kernel first second).trans
    (canonical_before_stopped graph count bound unchanged first second)

theorem member_before_stopped (graph : FiniteGraph.{u}) (count : Nat)
    (bound : count ≤ size (α := graph.Node))
    (unchanged : (graph.iterate count).stopped) (member set : graph.Node) :
    graph.canonicalMember (graph.canonicalProjection member) (graph.canonicalProjection set) ↔
      (graph.iterate count).edge (graph.iterateProjection count set)
        (graph.iterateProjection count member) := by
  change graph.canonicalGraph.edge (graph.canonicalProjection set)
    (graph.canonicalProjection member) ↔ _
  rw [graph.canonicalProjection_edge, graph.iterateProjection_edge]
  constructor
  · rintro ⟨child, available, same⟩
    exact ⟨child, available,
      (canonical_before_stopped graph count bound unchanged child member).mp same⟩
  · rintro ⟨child, available, same⟩
    exact ⟨child, available,
      (canonical_before_stopped graph count bound unchanged child member).mpr same⟩

theorem selectFresh_kernel {α β γ : Type u}
    [DecidableEq β] [DecidableEq γ] (first : α → β) (second : α → γ)
    (kernel : ∀ left right, first left = first right ↔ second left = second right)
    (seen entries : List α) :
    selectFresh first (seen.map first) entries = selectFresh second (seen.map second) entries := by
  induction entries generalizing seen with
  | nil => rfl
  | cons head tail previous =>
    have same : first head ∈ seen.map first ↔ second head ∈ seen.map second := by
      simp only [List.mem_map]
      constructor
      · rintro ⟨value, present, paired⟩
        exact ⟨value, present, (kernel value head).mp paired⟩
      · rintro ⟨value, present, paired⟩
        exact ⟨value, present, (kernel value head).mpr paired⟩
    by_cases present : first head ∈ seen.map first
    · have secondPresent := same.mp present
      simp only [selectFresh, if_pos present, if_pos secondPresent]
      exact previous seen
    · have secondMissing : second head ∉ seen.map second := fun proof => present (same.mpr proof)
      simp only [selectFresh, if_neg present, if_neg secondMissing]
      exact congrArg (List.cons head) (previous (head :: seen))

theorem members_before_stopped (presentation : ProfileGraphReadout.Presentations.Checked) (count : Nat)
    (bound : count ≤ size (α := (Presentations.graph presentation).Node))
    (unchanged : ((Presentations.graph presentation).iterate count).stopped) :
    Presentations.members presentation =
      (selectFresh ((Presentations.graph presentation).iterateProjection count) []
        (Presentations.sourceChildren presentation)).map Fin.val := by
  unfold Presentations.members Presentations.selectedChildren
  have same := selectFresh_kernel (Presentations.graph presentation).canonicalProjection
    ((Presentations.graph presentation).iterateProjection count)
    (canonical_before_stopped (Presentations.graph presentation) count bound unchanged) []
    (Presentations.sourceChildren presentation)
  exact congrArg (List.map Fin.val) same

theorem rounds_after_fixed {α β : Type u} [Enumeration α] [Enumeration β]
    [DecidableEq α] [DecidableEq β] (left : α → α → Prop) (right : β → β → Prop)
    [DecidableRel left] [DecidableRel right] (count : Nat)
    (fixed : refine left right (rounds left right count) = rounds left right count)
    (later : Nat) : rounds left right (count + later) = rounds left right count := by
  induction later with
  | zero => rfl
  | succ later previous =>
    change refine left right (rounds left right (count + later)) = _
    exact (congrArg (refine left right) previous).trans fixed

theorem stable_at_fixed {α β : Type u} [Enumeration α] [Enumeration β]
    [DecidableEq α] [DecidableEq β] (left : α → α → Prop) (right : β → β → Prop)
    [DecidableRel left] [DecidableRel right] (count : Nat)
    (bound : count ≤ size (α := α) * size (α := β))
    (fixed : refine left right (rounds left right count) = rounds left right count) :
    stable left right = rounds left right count := by
  obtain ⟨later, same⟩ := Nat.exists_eq_add_of_le bound
  unfold stable
  rw [same]
  exact rounds_after_fixed left right count fixed later

/-- Stable quotient steps are actual graph isomorphisms, preserving full
unfolding occurrences at each projected root. -/
def unfolding_after_stopped (graph : FiniteGraph.{u}) (count : Nat)
    (unchanged : (graph.iterate count).stopped) (first : graph.Node) :
    (later : Nat) → PresentationIso
      (unfold (graph.iterate count).edge (graph.iterateProjection count first))
      (unfold (graph.iterate (count + later)).edge (graph.iterateProjection (count + later) first))
  | 0 => PresentationIso.refl _
  | later + 1 =>
      (unfolding_after_stopped graph count unchanged first later).trans
        (FiniteGraph.unfoldingEquivIso (graph.iterate (count + later)).edge
          (graph.iterate (count + later)).quotient.edge
          ((graph.iterate (count + later)).quotientEquiv
            (ProfileFiniteScottCoherence.FiniteGraph.stopped_after graph count unchanged later))
          ((graph.iterate (count + later)).quotientEquiv_edge
            (ProfileFiniteScottCoherence.FiniteGraph.stopped_after graph count unchanged later))
          (graph.iterateProjection (count + later) first))

def unfolding_before_stopped (graph : FiniteGraph.{u}) (count : Nat)
    (bound : count ≤ size (α := graph.Node))
    (unchanged : (graph.iterate count).stopped) (first : graph.Node) :
    PresentationIso
      (unfold (graph.iterate count).edge (graph.iterateProjection count first))
      (unfold graph.canonicalGraph.edge (graph.canonicalProjection first)) := by
  change PresentationIso _
    (unfold (graph.iterate (size (α := graph.Node))).edge
      (graph.iterateProjection (size (α := graph.Node)) first))
  have same : count + (size (α := graph.Node) - count) = size (α := graph.Node) :=
    Nat.add_sub_of_le bound
  rw [← same]
  exact unfolding_after_stopped graph count unchanged first _

def stageEqual (left right : FiniteGraph.{u}) (leftCount rightCount : Nat)
    (first : left.Node) (second : right.Node) : Bool :=
  rawUnfoldingEquivalent (left.iterate leftCount).edge (right.iterate rightCount).edge
    (left.iterateProjection leftCount first) (right.iterateProjection rightCount second)

def inverseEdges (source target : FiniteGraph.{u}) (nodes : source.Node ≃ target.Node) : Prop :=
  ∀ first second, source.edge (nodes.symm first) (nodes.symm second) ↔ target.edge first second

instance inverseEdgesDecidable (source target : FiniteGraph.{u})
    (nodes : source.Node ≃ target.Node) : Decidable (inverseEdges source target nodes) := by
  unfold inverseEdges
  infer_instance

theorem forwardEdges_of_inverse (source target : FiniteGraph.{u})
    (nodes : source.Node ≃ target.Node) (verified : inverseEdges source target nodes) :
    ∀ first second, source.edge first second ↔ target.edge (nodes first) (nodes second) := by
  intro first second
  simpa only [Equiv.symm_apply_apply] using verified (nodes first) (nodes second)

theorem rawEquivalent_iso (left right flatLeft flatRight : FiniteGraph.{u})
    (leftNodes : left.Node ≃ flatLeft.Node) (rightNodes : right.Node ≃ flatRight.Node)
    (leftEdges : inverseEdges left flatLeft leftNodes)
    (rightEdges : inverseEdges right flatRight rightNodes) (first : left.Node) (second : right.Node) :
    rawUnfoldingEquivalent left.edge right.edge first second =
      rawUnfoldingEquivalent flatLeft.edge flatRight.edge (leftNodes first) (rightNodes second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [rawUnfoldingEquivalent_eq_true]
  let firstIso := FiniteGraph.unfoldingEquivIso left.edge flatLeft.edge leftNodes
    (forwardEdges_of_inverse left flatLeft leftNodes leftEdges) first
  let secondIso := FiniteGraph.unfoldingEquivIso right.edge flatRight.edge rightNodes
    (forwardEdges_of_inverse right flatRight rightNodes rightEdges) second
  exact ⟨fun ⟨iso⟩ => ⟨firstIso.symm.trans (iso.trans secondIso)⟩,
    fun ⟨iso⟩ => ⟨firstIso.trans (iso.trans secondIso.symm)⟩⟩

/-- Rank changes the finite carrier representation, preserving its authored
enumeration order. The cardinal equation is checked independently. -/
def finiteRank (graph : FiniteGraph.{0}) (count : Nat)
    (same : size (α := graph.Node) = count) : graph.Node ≃ Fin count :=
  positionEquiv.symm.trans (finCongr same)

theorem stageEqual_correct (left right : FiniteGraph.{u}) (leftCount rightCount : Nat)
    (leftBound : leftCount ≤ size (α := left.Node))
    (rightBound : rightCount ≤ size (α := right.Node))
    (leftStopped : (left.iterate leftCount).stopped)
    (rightStopped : (right.iterate rightCount).stopped)
    (first : left.Node) (second : right.Node) :
    stageEqual left right leftCount rightCount first second =
      FiniteGraph.normalizedEqual left right first second := by
  apply Bool.eq_iff_iff.mpr
  rw [stageEqual, rawUnfoldingEquivalent_eq_true,
    ProfileFiniteScottCoherence.FiniteGraph.normalizedEqual_unfolding_kernel]
  let firstIso := unfolding_before_stopped left leftCount leftBound leftStopped first
  let secondIso := unfolding_before_stopped right rightCount rightBound rightStopped second
  exact ⟨fun ⟨isomorphism⟩ => ⟨firstIso.symm.trans (isomorphism.trans secondIso)⟩,
    fun ⟨isomorphism⟩ => ⟨firstIso.trans (isomorphism.trans secondIso.symm)⟩⟩

def stageMember (left right : FiniteGraph.{u}) (leftCount rightCount : Nat)
    (member : left.Node) (set : right.Node) : Bool :=
  decide (∃ child, right.edge set child ∧
    stageEqual left right leftCount rightCount member child = true)

theorem stageMember_correct (left right : FiniteGraph.{u}) (leftCount rightCount : Nat)
    (leftBound : leftCount ≤ size (α := left.Node))
    (rightBound : rightCount ≤ size (α := right.Node))
    (leftStopped : (left.iterate leftCount).stopped)
    (rightStopped : (right.iterate rightCount).stopped)
    (member : left.Node) (set : right.Node) :
    stageMember left right leftCount rightCount member set =
      FiniteGraph.normalizedMember left right member set := by
  apply Bool.eq_iff_iff.mpr
  rw [stageMember, decide_eq_true_eq, FiniteGraph.normalizedMember_eq_true]
  simp only [stageEqual_correct left right leftCount rightCount leftBound rightBound
    leftStopped rightStopped, FiniteGraph.normalizedEqual]

namespace Presentations

open ProfileGraphReadout.Presentations
open ProfileFiniteScottCollapse.Presentations

def CheckedStage (presentation : Checked) (count : Nat) : Prop :=
  count ≤ size (α := (graph presentation).Node) ∧ ((graph presentation).iterate count).stopped

instance checkedStageDecidable (presentation : Checked) (count : Nat) :
    Decidable (CheckedStage presentation count) := inferInstanceAs (Decidable (_ ∧ _))

theorem cardinal_stage (presentation : Checked) :
    CheckedStage presentation (size (α := (graph presentation).Node)) :=
  ⟨Nat.le_refl _, FiniteGraph.iterate_stops _⟩

def stageEqual (first second : Checked) (firstCount secondCount : Nat) : Bool :=
  ProfileFiniteScottEvaluation.stageEqual (graph first) (graph second) firstCount secondCount
    (root first) (root second)

def stageMember (element set : Checked) (elementCount setCount : Nat) : Bool :=
  ProfileFiniteScottEvaluation.stageMember (graph element) (graph set) elementCount setCount
    (root element) (root set)

def stageMembers (presentation : Checked) (count : Nat) : List Nat :=
  (selectFresh ((graph presentation).iterateProjection count) [] (sourceChildren presentation)).map Fin.val

theorem stageMember_sourceChildren (element set : Checked) (elementCount setCount : Nat) :
    stageMember element set elementCount setCount =
      (sourceChildren set).any (fun child =>
        ProfileFiniteScottEvaluation.stageEqual (graph element) (graph set) elementCount setCount
          (root element) child) := by
  apply Bool.eq_iff_iff.mpr
  simp only [stageMember, ProfileFiniteScottEvaluation.stageMember, decide_eq_true_eq,
    List.any_eq_true]
  constructor
  · rintro ⟨child, available, same⟩
    exact ⟨child, (mem_sourceChildren set child).mpr available, same⟩
  · rintro ⟨child, available, same⟩
    exact ⟨child, (mem_sourceChildren set child).mp available, same⟩

theorem any_cons_values {α : Type u} (predicate : α → Bool) (head : α) (tail : List α)
    (headValue tailValue : Bool) (headChecked : predicate head = headValue)
    (tailChecked : tail.any predicate = tailValue) :
    (head :: tail).any predicate = (headValue || tailValue) := by
  rw [List.any_cons, headChecked, tailChecked]

theorem stageEqual_correct (first second : Checked) (firstCount secondCount : Nat)
    (firstBound : firstCount ≤ size (α := (graph first).Node))
    (secondBound : secondCount ≤ size (α := (graph second).Node))
    (firstStopped : ((graph first).iterate firstCount).stopped)
    (secondStopped : ((graph second).iterate secondCount).stopped) :
    stageEqual first second firstCount secondCount = ProfileFiniteScottCollapse.Presentations.equal first second :=
  ProfileFiniteScottEvaluation.stageEqual_correct _ _ _ _ firstBound secondBound firstStopped secondStopped _ _

theorem stageMember_correct (element set : Checked) (elementCount setCount : Nat)
    (elementBound : elementCount ≤ size (α := (graph element).Node))
    (setBound : setCount ≤ size (α := (graph set).Node))
    (elementStopped : ((graph element).iterate elementCount).stopped)
    (setStopped : ((graph set).iterate setCount).stopped) :
    stageMember element set elementCount setCount = ProfileFiniteScottCollapse.Presentations.member element set :=
  ProfileFiniteScottEvaluation.stageMember_correct _ _ _ _ elementBound setBound elementStopped setStopped _ _

theorem stageMembers_correct (presentation : Checked) (count : Nat)
    (bound : count ≤ size (α := (graph presentation).Node))
    (unchanged : ((graph presentation).iterate count).stopped) :
    stageMembers presentation count = ProfileFiniteScottCollapse.Presentations.members presentation :=
  (members_before_stopped presentation count bound unchanged).symm

end Presentations

end Mettapedia.SetTheory.Profiles.ProfileFiniteScottEvaluation
