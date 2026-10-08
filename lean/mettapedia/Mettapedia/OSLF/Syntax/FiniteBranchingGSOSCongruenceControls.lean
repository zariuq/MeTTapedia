import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSCongruence
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSControls

/-!
# Distinct choice contexts and a stopped-state separator

A proper relation between the supplied natural-number states matches both
successor directions. The actual free lifting then relates distinct leaves
and their repeated occurrences in nested choice contexts. An independent
syntax fold distinguishes the complete terms, while stopped and enabled
terms fail even the action-availability consequence of bisimilarity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Bisimulation.CongruenceControls

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.FiniteBranching.GSOSControls
open IndexedPolynomial

abbrev indexedLaw := lawEquiv signature actions law
abbrev liftedInputs := IndexedGSOS.Operational.liftObject indexedLaw inputs

def highRelation : Relation inputs inputs := fun _ _ value other =>
  10 ≤ value ∧ 10 ≤ other

theorem high_relation_admitted : Admitted inputs inputs highRelation := by
  intro base sort value other held action
  change 10 ≤ (value : Nat) ∧ 10 ≤ (other : Nat) at held
  rcases held with ⟨leftHigh, rightHigh⟩
  by_cases seven : action = 7
  · subst action
    change FinitePowerset.Related (fun value other : Nat => 10 ≤ value ∧ 10 ≤ other)
      {value + 1, 31} {other + 1, 31}
    constructor
    · intro next member
      have high : 10 ≤ next := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at member
        rcases member with rfl | rfl
        · exact leftHigh.trans (Nat.le_succ value)
        · decide
      exact ⟨other + 1, by simp, high, rightHigh.trans (Nat.le_succ other)⟩
    · intro next member
      have high : 10 ≤ next := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at member
        rcases member with rfl | rfl
        · exact rightHigh.trans (Nat.le_succ other)
        · decide
      exact ⟨value + 1, by simp, leftHigh.trans (Nat.le_succ value), high⟩
  · change FinitePowerset.Related (fun value other : Nat => 10 ≤ value ∧ 10 ≤ other)
      (if action = 7 then {value + 1, 31} else ∅)
      (if action = 7 then {other + 1, 31} else ∅)
    simp [seven, FinitePowerset.Related]

theorem original_relation_is_proper : ¬ highRelation PUnit.unit () 0 20 := by
  change ¬ (10 ≤ (0 : Nat) ∧ 10 ≤ (20 : Nat))
  omega

def originalPair : Pairs inputs inputs highRelation PUnit.unit () :=
  ⟨(10, 20), by change 10 ≤ (10 : Nat) ∧ 10 ≤ (20 : Nat); omega⟩

theorem distinct_leaves_related :
    Bisimilar liftedInputs liftedInputs PUnit.unit () (pure 10) (pure 20) := by
  exact bisimilar_of_span
    (IndexedGSOS.Operational.liftMap indexedLaw
      (firstMorphism inputs inputs highRelation high_relation_admitted))
    (IndexedGSOS.Operational.liftMap indexedLaw
      (secondMorphism inputs inputs highRelation high_relation_admitted))
    PUnit.unit () (Free.pure signature.polynomial originalPair)

def relatedHole : ContextPairs indexedLaw inputs PUnit.unit () :=
  ⟨(pure 10, pure 20), distinct_leaves_related⟩

def nestedContext : signature.Term (ContextPairs indexedLaw inputs) () :=
  choose (choose (pure relatedHole) stopped) (pure relatedHole)

def firstTerm : signature.Term naturals () :=
  choose (choose (pure 10) stopped) (pure 10)

def secondTerm : signature.Term naturals () :=
  choose (choose (pure 20) stopped) (pure 20)

theorem actual_nested_context_congruence :
    Bisimilar liftedInputs liftedInputs PUnit.unit () firstTerm secondTerm := by
  have inner : Bisimilar liftedInputs liftedInputs PUnit.unit ()
      (choose (pureNat 10) stopped) (choose (pureNat 20) stopped) := by
    exact constructor_congruent indexedLaw inputs PUnit.unit () Operator.choose
      (fun position => if position then stopped else pureNat 10)
      (fun position => if position then stopped else pureNat 20)
      (by
        intro position
        cases position
        · exact distinct_leaves_related
        · exact bisimilar_refl liftedInputs PUnit.unit () stopped)
  exact constructor_congruent indexedLaw inputs PUnit.unit () Operator.choose
    (fun position => if position then pureNat 10 else choose (pureNat 10) stopped)
    (fun position => if position then pureNat 20 else choose (pureNat 20) stopped)
    (by
      intro position
      cases position
      · exact inner
      · exact distinct_leaves_related)

def syntaxAlgebra : signature.polynomial.Algebra naturals where
  act := fun _ _ layer => match layer with
    | ⟨.stopped, _⟩ => 0
    | ⟨.choose, children⟩ => children false + children true

def syntaxReadout : signature.Term naturals () → Nat :=
  Free.fold signature.polynomial (fun _ _ value => value) syntaxAlgebra PUnit.unit ()

theorem full_related_terms_are_distinct : firstTerm ≠ secondTerm := by
  intro same
  have reading := congrArg syntaxReadout same
  change (20 : Nat) = 40 at reading
  omega

theorem stopped_is_not_bisimilar_to_enabled :
    ¬ Bisimilar liftedInputs liftedInputs PUnit.unit () stopped (pure 10) := by
  classical
  intro related
  have empty : liftedInputs.str PUnit.unit () stopped 7 = ∅ :=
    actual_stopped_successors 7
  have disabled := (bisimilar_availability (left := liftedInputs) (right := liftedInputs)
    PUnit.unit () (value := stopped) (other := pure 10) related 7).mp empty
  have impossible : ({pureNat 11, pureNat 31} : Finset (signature.Term naturals ())) = ∅ :=
    (actual_pure_successors 10).symm.trans disabled
  have reading := congrArg (fun successors : Finset (signature.Term naturals ()) =>
    pureNat 11 ∈ successors) impossible
  simp at reading

end Mettapedia.OSLF.FiniteBranching.Bisimulation.CongruenceControls
