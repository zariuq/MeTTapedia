import Mettapedia.CategoryTheory.FiniteActionTreeCofree
import Mettapedia.CategoryTheory.FinitePowersetWeakPullback
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSCongruence

/-!
# Final finite-branching semantics and its independent bisimulation kernel

Uncoloured unordered action trees form an actual final coalgebra. Their
complete successor sets determine two-sided matching of original states.
Conversely, an independently admitted relation supplies a full pair
coalgebra whose two projections have the same final readout. This earns
kernel equality at arbitrary action alphabets and transfers the proved
free-context congruence to complete final observations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalSemantics

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

abbrev terminalColours : S.Families := fun _ _ => PUnit.{u + 1}

def finalObject : Endofunctor.Coalgebra (behaviourFunctor S Actions) where
  V := fun _ sort => FiniteActionTree.Tree (Actions sort) PUnit.{u + 1}
  str _ _ := ↾FiniteActionTree.Tree.step

def observe (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    object ⟶ finalObject S Actions where
  f base sort := ↾(FiniteActionTree.Tree.coiterate (object.str base sort)
    (fun _ => PUnit.unit))
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro state
    funext action
    exact (FiniteActionTree.Tree.step_coiterate (object.str base sort)
      (fun _ => PUnit.unit) state action).symm

theorem observe_unique (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (mapping : object ⟶ finalObject S Actions) : mapping = observe S Actions object := by
  apply Endofunctor.Coalgebra.ext
  funext base sort
  apply ConcreteCategory.hom_ext
  apply FiniteActionTree.Tree.coiterate_unique (object.str base sort)
    (fun _ => PUnit.unit) (mapping.f base sort) (fun _ => Subsingleton.elim _ _)
  intro state action
  exact (congrArg (fun arrow => arrow base sort state action) mapping.h).symm

def isFinal : Limits.IsTerminal (finalObject S Actions) :=
  Limits.IsTerminal.ofUniqueHom (observe S Actions) (observe_unique S Actions)

theorem observe_natural {first second : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (mapping : first ⟶ second) :
    mapping ≫ observe S Actions second = observe S Actions first :=
  observe_unique S Actions first _

theorem observe_readout (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) :
    (observe S Actions object).f base sort state =
      FiniteActionTree.Tree.coiterate (object.str base sort) (fun _ => PUnit.unit) state := rfl

theorem observe_step (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort)
    (action : Actions sort) :
    FiniteActionTree.Tree.step ((observe S Actions object).f base sort state) action =
      FinitePowerset.map ((observe S Actions object).f base sort)
        (object.str base sort state action) :=
  (congrArg (fun arrow => arrow base sort state action) (observe S Actions object).h).symm

def Kernel (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Bisimulation.Relation left right := fun base sort state other =>
  (observe S Actions left).f base sort state = (observe S Actions right).f base sort other

/-- Equal complete images earn every original successor match in both directions. -/
theorem kernel_admitted (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Bisimulation.Admitted left right (Kernel S Actions left right) := by
  intro base sort state other same action
  apply (FinitePowersetWeakPullback.related_iff_matching
    ((observe S Actions left).f base sort) ((observe S Actions right).f base sort)
    (left.str base sort state action) (right.str base sort other action)).2
  have observations := congrArg (fun tree => FiniteActionTree.Tree.step tree action) same
  rw [observe_step, observe_step] at observations
  exact observations

/-- The carrier retains the complete original pair, even when its images coincide. -/
def kernelCoalgebra (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Endofunctor.Coalgebra (behaviourFunctor S Actions) :=
  Bisimulation.relationCoalgebra left right (Kernel S Actions left right)

def kernelFirst (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    kernelCoalgebra S Actions left right ⟶ left :=
  Bisimulation.firstMorphism left right (Kernel S Actions left right)
    (kernel_admitted S Actions left right)

def kernelSecond (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    kernelCoalgebra S Actions left right ⟶ right :=
  Bisimulation.secondMorphism left right (Kernel S Actions left right)
    (kernel_admitted S Actions left right)

/-- Finality identifies the two projections of an actual relation coalgebra. -/
theorem observe_of_admitted
    {left right : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (relation : Bisimulation.Relation left right)
    (admitted : Bisimulation.Admitted left right relation)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    {state : left.V base sort} {other : right.V base sort}
    (held : relation base sort state other) :
    (observe S Actions left).f base sort state = (observe S Actions right).f base sort other := by
  let pair : Bisimulation.Pairs left right relation base sort := ⟨(state, other), held⟩
  have first := congrArg (fun arrow => arrow.f base sort pair)
    (observe_natural S Actions (Bisimulation.firstMorphism left right relation admitted))
  have second := congrArg (fun arrow => arrow.f base sort pair)
    (observe_natural S Actions (Bisimulation.secondMorphism left right relation admitted))
  exact first.trans second.symm

/-- No finality or congruence premise is assumed of the independently defined relation. -/
theorem kernel_iff_bisimilar
    (left right : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : left.V base sort)
    (other : right.V base sort) :
    (observe S Actions left).f base sort state = (observe S Actions right).f base sort other ↔
      Bisimulation.Bisimilar left right base sort state other := by
  constructor
  · intro same
    exact ⟨Kernel S Actions left right, kernel_admitted S Actions left right, same⟩
  · rintro ⟨relation, admitted, held⟩
    exact observe_of_admitted S Actions relation admitted base sort held

variable {S Actions} (law : IndexedGSOS.Law S.polynomial (behaviourFunctor S Actions))

theorem context_kernel_congruent
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (context : S.polynomial.Free (Bisimulation.ContextPairs law object) base sort) :
    (observe S Actions (IndexedGSOS.Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.bind S.polynomial (fun _ _ pair => pair.val.1) base sort context) =
      (observe S Actions (IndexedGSOS.Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.bind S.polynomial (fun _ _ pair => pair.val.2) base sort context) :=
  (kernel_iff_bisimilar S Actions _ _ base sort _ _).2
    (Bisimulation.context_related law object base sort context)

theorem constructor_kernel_congruent
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (operator : S.Operator sort)
    (first second : (position : S.Position operator) →
      (IndexedGSOS.Operational.liftObject law object).V base (S.argument operator position))
    (agreement : ∀ position,
      (observe S Actions (IndexedGSOS.Operational.liftObject law object)).f base _ (first position) =
        (observe S Actions (IndexedGSOS.Operational.liftObject law object)).f base _ (second position)) :
    (observe S Actions (IndexedGSOS.Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.node S.polynomial operator first) =
      (observe S Actions (IndexedGSOS.Operational.liftObject law object)).f base sort
        (IndexedPolynomial.Free.node S.polynomial operator second) := by
  apply (kernel_iff_bisimilar S Actions _ _ base sort _ _).2
  apply Bisimulation.constructor_congruent law object base sort operator first second
  intro position
  exact (kernel_iff_bisimilar S Actions _ _ base _ _ _).1 (agreement position)

end Mettapedia.OSLF.FiniteBranching.FinalSemantics
