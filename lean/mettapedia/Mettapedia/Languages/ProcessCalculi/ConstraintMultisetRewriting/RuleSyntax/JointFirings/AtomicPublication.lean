import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AllAtOnce
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Tensor
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OccurrenceCorePlacement

/-!
# A separation by atomic publication of occurrences

Public observation reads a fixed subset of target occurrence identities.
Each source occurrence has its own public target identity. Administrative
steps may rearrange hidden data around a visible commit. The two public
cuts of that commit must represent the two source cuts.

This strengthens operational completeness for an observer that can count
new physical publications. A finite one-match program cannot implement
the all-token transition under that contract. A generated ground tensor
does realize the transition for each concrete bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AtomicPublication

open AnnotatedRuns (firstOrder)
open Examples (Tm X E consume)
open EveryControls (tokens tokensAt takeAt consume_ground)
open AllAtOnce (spendAll spendAll_every spendAll_made_rows)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (action)

section Atomic

variable {T S O : Type*} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T) (rules : Set (RuleInstance T))
  (isPublic : O → Bool) (row : ℕ ↪ O)

def observe (state : Configuration T O) : Finset O := state.present.filter fun o => isPublic o = true

/-- A publication exposes the same rows at both cuts as the source step.
The target may prepare its visible firing and continue afterwards at any
states with these public observations. -/
structure OccurrenceAtomic (encode : State Tm ℕ → Configuration T O) : Prop where
  readback : ∀ s, observe isPublic (encode s) = s.present.map row
  complete : ∀ (s : State Tm ℕ) (bag : Bag ℕ E tokens s.frame),
    bag.members ≠ [] → bag.Admits X s →
    ∃ (before : Configuration T O) (fire : AnnotatedRuns.Firing T S O)
      (admitted : (firstOrder A label).Admits (s := before) fire),
      fire.rule ∈ rules ∧ observe isPublic before = observe isPublic (encode s) ∧
      observe isPublic ((firstOrder A label).result fire admitted) =
        observe isPublic (encode (bag.result X s))

private theorem observed_growth (before after : Configuration T O) :
    ((observe isPublic after) \ (observe isPublic before)).card ≤ (after.present \ before.present).card := by
  apply Finset.card_le_card
  intro o member
  obtain ⟨inAfter, outside⟩ := Finset.mem_sdiff.mp member
  obtain ⟨inAfter, visible⟩ := Finset.mem_filter.mp inAfter
  exact Finset.mem_sdiff.mpr ⟨inAfter, fun present => outside (Finset.mem_filter.mpr ⟨present, visible⟩)⟩

/-- There is no such encoding through bounded-arity target rules, even
without further constraints on the map or the choice of preparation. -/
theorem no_bounded_atomic_encoding (bound : ℕ)
    (bounded : ∀ rule ∈ rules, rule.produce.length ≤ bound) :
    ¬ ∃ encode, OccurrenceAtomic A label rules isPublic row encode := by
  rintro ⟨encode, valid⟩
  let n := bound + 1
  let entry := tokensAt (Finset.range n)
  let bag := spendAll n
  have members : bag.members ≠ [] := by
    simp [bag, spendAll, bagOf, n]
  obtain ⟨before, fire, admitted, member, entryRead, resultRead⟩ :=
    valid.complete entry bag members (spendAll_every n).admits
  have observed : ((observe isPublic ((firstOrder A label).result fire admitted)) \
      (observe isPublic before)).card = n := by
    rw [resultRead, entryRead, valid.readback, valid.readback, ← Finset.map_sdiff, Finset.card_map]
    exact spendAll_made_rows n
  have limit := (observed_growth isPublic before ((firstOrder A label).result fire admitted)).trans
    ((OccurrenceCorePlacement.added_card_le A label fire admitted).trans (bounded _ member))
  rw [observed] at limit
  omega

end Atomic

/-- On a concrete token group the ground tensor is a real one-match firing
with the same rows and labels. Its arity is generated from the group. -/
theorem token_tensor (n : ℕ) :
    let entry := tokensAt (Finset.range n)
    let members := (List.range n).map fun o => takeAt o (n + o)
    let fire := tensorFiring action members
    fire.Admits X entry ∧
      (fire.result X entry).present = ((spendAll n).result X entry).present ∧
      (fire.result X entry).label = ((spendAll n).result X entry).label := by
  dsimp only
  let members := (List.range n).map fun o => takeAt o (n + o)
  have ground : ∀ m ∈ members, GroundRule action m.rule := by
    intro m inside
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp inside
    exact consume_ground
  have split : Split members := by
    intro m inside
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp inside
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨(admits_iff_tensor ground split _).mp (spendAll_every n).admits,
    (result_tensor ground split _).1, (result_tensor ground split _).2.1⟩

#print axioms no_bounded_atomic_encoding
#print axioms token_tensor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AtomicPublication
