import Mettapedia.Languages.TransitionSystem.Extension
import Mettapedia.Languages.TransitionSystem.Runs

/-!
# A morphism of theories that does not preserve trace equivalence

A morphism preserves what every probe finds bisimilar.  It need not preserve
what a probe finds trace equivalent.

The smaller table has two states, `L` and `R`, that run for the same lengths
and are not bisimilar: `L` moves to `A`, which then chooses between a state
that moves and one that does not; `R` chooses at once.  The larger table adds
a run of three moves out of `A`.  Its inclusion is a morphism: `A` is the
only state of the smaller table with a successor that moves and one that
does not, so whatever a probe relates to `A` is `A`.  In the larger table `L`
runs for four steps and `R` for three.

So the two terms have the same traces in the source and different traces in
the target, along a map that preserves bisimilarity for every probe.  The
map preserves transitions and does not reflect them; a map that does both
preserves trace equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.Languages.TransitionSystem

/-- The smaller table. -/
def small : Table where
  states := ["L", "R", "A", "A1", "A2", "B", "B2", "C"]
  moves :=
    [("LA", "L", "A"), ("AB", "A", "B"), ("AC", "A", "C"), ("BC", "B", "C"),
      ("RA1", "R", "A1"), ("RA2", "R", "A2"), ("A1B2", "A1", "B2"), ("A2C", "A2", "C"),
      ("B2C", "B2", "C")]

/-- The larger table: three more states and a run of three moves out of
`A`. -/
def large : Table where
  states := small.states ++ ["T1", "T2", "T3"]
  moves := small.moves ++ [("AT1", "A", "T1"), ("T1T2", "T1", "T2"), ("T2T3", "T2", "T3")]

theorem small_wellFormed : small.WellFormed := by decide

theorem large_wellFormed : large.WellFormed := by decide

/-- The larger table extends the smaller one at `A`. -/
theorem extension : Table.PivotExtension small large "A" :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- How long each state of the smaller table runs. -/
def smallHeight : String → ℕ
  | "L" => 3
  | "R" => 3
  | "A" => 2
  | "A1" => 2
  | "A2" => 1
  | "B" => 1
  | "B2" => 1
  | _ => 0

/-- How long each state of the larger table runs. -/
def largeHeight : String → ℕ
  | "L" => 4
  | "R" => 3
  | "A" => 3
  | "A1" => 2
  | "A2" => 1
  | "B" => 1
  | "B2" => 1
  | "T1" => 2
  | "T2" => 1
  | _ => 0

theorem small_height : small.Height smallHeight := ⟨by decide, by decide⟩

theorem large_height : large.Height largeHeight := ⟨by decide, by decide⟩

/-- The interface of closed states. -/
def proc : Interface := ⟨.base "Proc", []⟩

/-- The state that chooses after its first move. -/
def early : Term small.language proc :=
  Table.stateTerm (interface := proc) rfl (by decide : "L" ∈ small.states)

/-- The state that chooses with its first move. -/
def late : Term small.language proc :=
  Table.stateTerm (interface := proc) rfl (by decide : "R" ∈ small.states)

/-- **In the smaller table the two states have the same traces.** -/
theorem early_late_traceEquivalent :
    (Table.theory small_wellFormed).reductionProbe.TraceEquivalent (index := proc) early late :=
  Table.traceEquivalent_of_height_eq small_wellFormed small_height (leftLabel := "L")
    (rightLabel := "R") rfl rfl (by decide)

/-- **The inclusion is a morphism of theories.** -/
def lengthen :
    ContextMorphism (Table.theory small_wellFormed) (Table.theory large_wellFormed) :=
  Table.inclusionMorphism small_wellFormed large_wellFormed extension

/-- The image of every hole acts as the identity. -/
theorem lengthen_identity (origin : Interface)
    (term : (Table.theory large_wellFormed).Term (lengthen.interface origin)) :
    (Table.theory large_wellFormed).apply
      (lengthen.context ((Table.theory small_wellFormed).identity origin)) term = term :=
  apply_map_identity base (Table.inclusion small_wellFormed large_wellFormed extension) origin
    term

/-- **In the larger table their images have different traces**: the image of
the first runs for four steps and the image of the second does not. -/
theorem images_not_traceEquivalent :
    ¬ (lengthen.push (Table.theory small_wellFormed).reductionProbe).TraceEquivalent
      (index := proc) (lengthen.term early) (lengthen.term late) := by
  intro equivalent
  have traces := equivalent
    (lengthen.toContextMap.pushPath (Table.theory small_wellFormed).reductionProbe
      ((Table.theory small_wellFormed).reductionPath proc 4))
  have leftRuns := ContextMap.hasTrace_push_reductionPath_iff lengthen.toContextMap
    lengthen_identity (origin := proc) 4 (lengthen.term early)
  have rightRuns := ContextMap.hasTrace_push_reductionPath_iff lengthen.toContextMap
    lengthen_identity (origin := proc) 4 (lengthen.term late)
  have leftHeight := Table.runsFor_iff large_wellFormed large_height 4 (lengthen.term early)
    (label := "L") (Table.inclusionMap_term_val small_wellFormed large_wellFormed extension early)
  have rightHeight := Table.runsFor_iff large_wellFormed large_height 4 (lengthen.term late)
    (label := "R") (Table.inclusionMap_term_val small_wellFormed large_wellFormed extension late)
  have impossible : 4 ≤ largeHeight "L" ↔ 4 ≤ largeHeight "R" :=
    leftHeight.symm.trans ((leftRuns.symm.trans (traces.trans rightRuns)).trans rightHeight)
  revert impossible
  decide

/-- **The morphism does not preserve trace equivalence.** -/
theorem lengthen_not_preservesTraces : ¬ lengthen.toContextMap.PreservesTraces :=
  fun preserves => images_not_traceEquivalent
    (preserves (Table.theory small_wellFormed).reductionProbe early_late_traceEquivalent)

/-- The morphism preserves transitions. -/
theorem lengthen_preservesTransitions : lengthen.toContextMap.PreservesTransitions :=
  Table.inclusionMap_preservesTransitions small_wellFormed large_wellFormed extension

/-- It does not reflect them: a map that preserves and reflects transitions
preserves trace equivalence. -/
theorem lengthen_not_reflectsTransitions : ¬ lengthen.toContextMap.ReflectsTransitions :=
  fun reflects => lengthen_not_preservesTraces
    (lengthen.toContextMap.preservesTraces_of_transitions lengthen_preservesTransitions reflects)

/-- The inclusion reflects static equivalence: adding states and moves
identifies no previously distinct state terms. -/
theorem lengthen_reflectsEquations : lengthen.toContextMap.ReflectsEquations := by
  intro origin first second equivalent
  have same := (termSetoid_iff_eq base large.language large.isEquationFree _ _).mp equivalent
  have raw := congrArg Subtype.val same
  have left := Table.inclusionMap_term_val small_wellFormed large_wellFormed extension first
  have right := Table.inclusionMap_term_val small_wellFormed large_wellFormed extension second
  have preimage : first = second := Subtype.ext (left.symm.trans (raw.trans right))
  rw [preimage]
  exact Relation.EqvGen.refl _

/-- Faithful contexts and forward transition transport still permit added
behavior: backward transition lifting is an independent obligation. -/
theorem lengthen_faithful : lengthen.toContextMap.Faithful :=
  lengthen.toContextMap.faithful_of_reflectsEquations lengthen_reflectsEquations

/-- The extension is a faithful morphism but is not hosting. -/
theorem lengthen_not_hosting : ¬ lengthen.toContextMap.Hosting :=
  fun hosting => lengthen_not_reflectsTransitions hosting.reflects

/-- **A morphism of theories need not preserve trace equivalence.** -/
theorem morphism_need_not_preserve_traces :
    ∃ (source target : ContextTheory.{0}) (morphism : ContextMorphism source target),
      morphism.toContextMap.PreservesTransitions ∧ ¬ morphism.toContextMap.PreservesTraces :=
  ⟨_, _, lengthen, lengthen_preservesTransitions, lengthen_not_preservesTraces⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun
