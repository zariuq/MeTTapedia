import Mettapedia.TypeTheory.KnowledgeUnsolved

/-!
# The frame's conversion and truth at every solution

A frame with knowledge about a variable can be read in two ways. The frame's own conversion is
the congruence closure of what it was told. The other reading takes the frame to stand for the
instantiations of the variable that satisfy the knowledge, and asks what holds at all of them
(`HoldsAtSolutions`). The second reading is the one a logic of sets gives: a hypothesis restricts
the values of a variable, and everything true of the restricted values follows.

* `holdsAtSolutions_of_convertibleKnowing`: the frame's conversion is sound for the second
  reading. What the frame converts is convertible at every solution.
* `definition_complete`: for a frame whose knowledge is one definition the two readings agree.
* `Controls.frame_is_weaker_than_its_solutions`: in general the frame's conversion is strictly
  weaker. Told `succ n ≐ succ 0`, with no declared step, every solution is `0`, so `Vec n` is
  `Vec 0` at every solution, and the frame does not convert them.

So the frame's conversion is a syntactic part of the entailment that the reading by sets has in
full. It is the part that needs no search.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeAtSolutions

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.KnowledgeSolvedForm
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Two terms are convertible at every instantiation of the variable `k` that satisfies the
store. -/
def HoldsAtSolutions (rules : Expr Base Const → Expr Base Const → Prop) (k : Nat)
    (K : EquationStore (Expr Base Const)) (A B : Expr Base Const) : Prop :=
  ∀ solution : Expr Base Const,
    (∀ equation ∈ K,
      Convertible rules (substAt k solution equation.1) (substAt k solution equation.2)) →
      Convertible rules (substAt k solution A) (substAt k solution B)

/-- **The frame's conversion is sound at every solution.** -/
theorem holdsAtSolutions_of_convertibleKnowing
    {rules : Expr Base Const → Expr Base Const → Prop} (substStable : SubstitutionStable rules)
    (shiftStable : ShiftStable rules) (k : Nat) {K : EquationStore (Expr Base Const)}
    {A B : Expr Base Const} (converted : ConvertibleKnowing rules K A B) :
    HoldsAtSolutions rules k K A B := by
  intro solution solves
  refine convertible_of_knowing shiftStable ?_
    (convertibleKnowing_subst substStable k solution converted)
  intro equation member
  obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
  exact solves original inStore

/-- **For a definition the two readings agree**: the frame converts exactly what is convertible
at every solution. -/
theorem definition_complete {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules) (k : Nat)
    (defined : Expr Base Const) {A B : Expr Base Const} :
    ConvertibleKnowing rules [(bvar k, shiftN (k + 1) defined)] A B ↔
      HoldsAtSolutions rules k [(bvar k, shiftN (k + 1) defined)] A B :=
  ⟨holdsAtSolutions_of_convertibleKnowing substStable shiftStable k, fun holds =>
    (solved_conversion_iff substStable shiftStable k defined).mpr
      (holds defined (definition_solves k defined))⟩

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeUnsolved.Controls

/-- Every solution of `succ n ≐ succ 0` is `0`, so `Vec n` is `Vec 0` at every solution. -/
theorem successors_hold_at_solutions :
    HoldsAtSolutions (fun _ _ => False) 0 knowsSuccessors (vec (bvar 0)) (vec zeroE) := by
  intro solution solves
  have same : succE solution = succE zeroE :=
    convertible_none_iff.mp
      (solves (succE (bvar 0), succE zeroE) (List.mem_singleton_self _))
  obtain ⟨_, rfl⟩ := Expr.app.inj same
  exact Relation.EqvGen.refl _

/-- **The frame's conversion is strictly weaker than truth at every solution.** -/
theorem frame_is_weaker_than_its_solutions :
    HoldsAtSolutions (fun _ _ => False) 0 knowsSuccessors (vec (bvar 0)) (vec zeroE) ∧
      ¬ ConvertibleKnowing (fun _ _ => False) knowsSuccessors (vec (bvar 0)) (vec zeroE) :=
  ⟨successors_hold_at_solutions, successors_do_not_decompose⟩

end Controls

/-! ## Axiom audit -/

#print axioms holdsAtSolutions_of_convertibleKnowing
#print axioms definition_complete
#print axioms Controls.successors_hold_at_solutions
#print axioms Controls.frame_is_weaker_than_its_solutions

end Mettapedia.TypeTheory.KnowledgeAtSolutions
