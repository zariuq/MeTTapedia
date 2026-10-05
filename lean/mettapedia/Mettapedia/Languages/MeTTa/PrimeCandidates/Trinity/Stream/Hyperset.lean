import Mettapedia.TypeTheory.MaterialSets.Hypersets.Streams
import Mettapedia.GSLT.Dynamics.DemandAgreement

/-!
# What a hyperset keeps of a running program

A hyperset keeps the branching of a program and forgets a duplicated edge and the length of a
cycle.

* Branching is kept. `x·(y + z)` and `x·y + x·z` have the same words and, when `y` and `z`
  are read differently, two hypersets (`branching_kept`, from `late_early_part`).
* Multiplicity is forgotten. A point with two edges to an empty child and a point with one
  such edge picture the same hyperset, and the number of edges differs
  (`multiplicity_forgotten`). The bags of those answers differ. Two copies of one answer
  differ as bags and agree as sets (`twoEqualAnswers_bagsDiffer_setsAgree`).
* The length of a cycle is forgotten. With one label, the two-node cycle and the one-node
  loop are one hyperset, while the cycle returns after two steps and the loop after one
  (`shape_forgotten`). Read at `Ω`, both are `Ω` (`shape_forgotten_omega`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open AccessiblePointedGraph
open HSet
open Mettapedia.GSLT.Dynamics.DemandAgreement

universe u

/-- **Branching is kept.** The same words, and two hypersets when the two branches are read
differently. -/
theorem branching_kept {β : Type u} {ℓ : β → HSet.{u}} (hℓ : Function.Injective ℓ)
    {x y z : β} (hyz : y ≠ z) :
    {w | Trace (lateRel x y z) .start w} = {w | Trace (earlyRel x y z) .start w} ∧
      decorateLabelled (lateRel x y z) ℓ .start ≠
        decorateLabelled (earlyRel x y z) ℓ .start :=
  late_early_part hℓ hyz

/-- One answer, as a bag. -/
def oneEdgeBag : Multiset Unit :=
  {()}

/-- The same answer written twice, as a bag. -/
def twoEdgeBag : Multiset Unit :=
  {()} + {()}

/-- **A duplicated edge is forgotten by the hyperset and kept by the bag.** `twoChildren` and
`oneChild empty` picture `{∅}` (`picture_twoChildren`, `picture_oneChild_empty`) and have
different numbers of edges (`occurrenceCount_twoChildren_ne`). The bags of one answer and of
two copies differ. Two copies of an answer `a` differ as the curriculum's bags and agree as
sets. -/
theorem multiplicity_forgotten {α : Type} [DecidableEq α] (a : α) :
    picture twoChildren.{u} = picture (oneChild AccessiblePointedGraph.empty.{u}) ∧
      occurrenceCount twoChildren.{u} ≠
        occurrenceCount (oneChild AccessiblePointedGraph.empty.{u}) ∧
      oneEdgeBag ≠ twoEdgeBag ∧
      sharedPair (Multiset.replicate 2 a) ≠ resampledPair (Multiset.replicate 2 a) ∧
      (sharedPair (Multiset.replicate 2 a)).toFinset =
        (resampledPair (Multiset.replicate 2 a)).toFinset := by
  refine ⟨picture_twoChildren.trans picture_oneChild_empty.symm, occurrenceCount_twoChildren_ne,
      ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg Multiset.card h
    simp [oneEdgeBag, twoEdgeBag, Multiset.card_singleton] at hc
  · exact (twoEqualAnswers_bagsDiffer_setsAgree a).2.2.1
  · obtain ⟨_, _, _, hl, hr⟩ := twoEqualAnswers_bagsDiffer_setsAgree a
    exact hl.trans hr.symm

/-- **The length of a cycle is forgotten.** One label makes the two-node cycle the one-node
loop. The cycle returns to its start after two steps and not after one; the loop returns
after one. -/
theorem shape_forgotten (b : HSet.{u}) :
    alternating b b (⟨true⟩ : ULift.{u} Bool) = repeatStream b ∧
      (∀ a : ULift.{u} Bool, deterministic_alternateRel.node a 1 ≠ a ∧
          deterministic_alternateRel.node a 2 = a) ∧
        ∀ a : PUnit.{u + 1}, deterministic_repeatRel.node a 1 = a :=
  alternating_cycle_length_forgotten b

/-- **At `Ω`, the cycle and the loop are `Ω`.** -/
theorem shape_forgotten_omega :
    alternating quineAtom.{u} quineAtom.{u} (⟨true⟩ : ULift.{u} Bool) = quineAtom.{u} ∧
      repeatStream quineAtom.{u} = quineAtom.{u} :=
  ⟨(shape_forgotten quineAtom.{u}).1.trans
      ((repeatStream_eq_quineAtom_iff quineAtom.{u}).mpr rfl),
    (repeatStream_eq_quineAtom_iff quineAtom.{u}).mpr rfl⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream
