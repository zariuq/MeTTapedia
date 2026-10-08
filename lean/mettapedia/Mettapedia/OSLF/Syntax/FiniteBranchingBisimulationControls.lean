import Mettapedia.OSLF.Syntax.FiniteBranchingBehaviourControls
import Mettapedia.OSLF.Syntax.FiniteBranchingBisimulation

/-!
# Many-to-one labelled bisimulation controls

The left state offers two actual successors at action seven, while its
right partner offers one. All pairs in the declared relation match these
behaviors, and the constructed relation coalgebra retains both successor
pairs. Replacing the partner by a stopped state invalidates the same
relation's transition condition.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Bisimulation.Controls

open _root_.CategoryTheory Mettapedia.CategoryTheory
open Mettapedia.OSLF.FiniteBranching.Controls

abbrev leftObject : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str := fun _ _ => ↾(fun _ => twoBranches)

abbrev rightObject : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str := fun _ _ => ↾(fun _ action => if action = 7 then {0} else ∅)

def related : Relation leftObject rightObject := fun _ _ _ other => other = 0

theorem admitted : Admitted leftObject rightObject related := by
  intro base sort value other relation action
  change other = 0 at relation
  subst other
  by_cases same : action = 7
  · subst action
    change FinitePowerset.Related (fun _ other : Nat => other = 0) {11, 21} {0}
    constructor
    · intro next _
      exact ⟨0, by simp, rfl⟩
    · intro next member
      have zero : next = 0 := by simpa using member
      subst next
      exact ⟨11, by simp, rfl⟩
  · change FinitePowerset.Related (fun _ other : Nat => other = 0)
      (twoBranches action) (if action = 7 then {0} else ∅)
    simp [twoBranches, same, FinitePowerset.Related]

def initial : Pairs leftObject rightObject related PUnit.unit () := ⟨(5, 0), rfl⟩
def firstPair : Pairs leftObject rightObject related PUnit.unit () := ⟨(11, 0), rfl⟩
def secondPair : Pairs leftObject rightObject related PUnit.unit () := ⟨(21, 0), rfl⟩

theorem full_relation_successors :
    (relationCoalgebra leftObject rightObject related).str PUnit.unit () initial 7 =
      ({firstPair, secondPair} : Finset (Pairs leftObject rightObject related PUnit.unit ())) := by
  classical
  change successors leftObject rightObject related PUnit.unit () initial 7 = _
  ext pair
  rcases pair with ⟨⟨value, other⟩, held⟩
  change other = 0 at held
  subst other
  change (⟨(value, 0), rfl⟩ : Pairs leftObject rightObject related PUnit.unit ()) ∈
      FinitePowersetRelation.matching (related PUnit.unit ()) (twoBranches 7) {0} ↔ _
  simp [FinitePowersetRelation.mem_matching, twoBranches, firstPair, secondPair,
    Subtype.ext_iff]

theorem actual_projection_readouts :
    (firstMorphism leftObject rightObject related admitted).f PUnit.unit () initial = 5 ∧
      (secondMorphism leftObject rightObject related admitted).f PUnit.unit () initial = 0 :=
  ⟨rfl, rfl⟩

theorem source_pair_and_both_successors_are_distinct :
    initial ≠ firstPair ∧ firstPair ≠ secondPair := by
  constructor <;> intro same
  · have impossible : (5 : Nat) = 11 := congrArg (fun pair => pair.val.1) same
    exact (by decide : (5 : Nat) ≠ 11) impossible
  · have impossible : (11 : Nat) = 21 := congrArg (fun pair => pair.val.1) same
    exact (by decide : (11 : Nat) ≠ 21) impossible

abbrev stoppedObject : Endofunctor.Coalgebra (behaviourFunctor signature actions) where
  V := naturals
  str := fun _ _ => ↾(fun _ _ => ∅)

def stoppedRelation : Relation leftObject stoppedObject := fun _ _ _ other => other = 0

theorem present_relation_does_not_supply_bisimulation :
    ¬ Admitted leftObject stoppedObject stoppedRelation := by
  intro accepts
  have matching := (accepts PUnit.unit () 5 0 rfl 7).1 11
    (by change 11 ∈ twoBranches 7; simp [twoBranches])
  obtain ⟨_, impossible, _⟩ := matching
  change _ ∈ (∅ : Finset Nat) at impossible
  exact Finset.notMem_empty _ impossible

end Mettapedia.OSLF.FiniteBranching.Bisimulation.Controls
