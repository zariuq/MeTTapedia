import Mettapedia.OSLF.Syntax.FiniteBranchingBisimilarity

/-!
# Complete first-order context congruence for finite branching

Bisimilarity is the union of all independently admitted two-sided labelled
relations. Its complete pair carrier carries the constructed relation
coalgebra. Lifting both projections through the actual free GSOS monad and
then flattening by its coalgebra-compatible multiplication proves congruence
for every free term context. No final or cofree coalgebra is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Bisimulation

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open IndexedPolynomial

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

variable (law : IndexedGSOS.Law S.polynomial (behaviourFunctor S Actions))

abbrev ContextPairs (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    S.Families :=
  Pairs (IndexedGSOS.Operational.liftObject law object)
    (IndexedGSOS.Operational.liftObject law object)
    (Bisimilar (IndexedGSOS.Operational.liftObject law object)
      (IndexedGSOS.Operational.liftObject law object))

def contextFirst (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    IndexedGSOS.Operational.liftObject law
        (relationCoalgebra (IndexedGSOS.Operational.liftObject law object)
          (IndexedGSOS.Operational.liftObject law object) (Bisimilar _ _)) ⟶
      IndexedGSOS.Operational.liftObject law object :=
  IndexedGSOS.Operational.liftMap law
    (firstMorphism _ _ (Bisimilar _ _) (bisimilar_admitted _ _)) ≫
      (IndexedGSOS.Operational.liftMultiplication law).app object

def contextSecond (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    IndexedGSOS.Operational.liftObject law
        (relationCoalgebra (IndexedGSOS.Operational.liftObject law object)
          (IndexedGSOS.Operational.liftObject law object) (Bisimilar _ _)) ⟶
      IndexedGSOS.Operational.liftObject law object :=
  IndexedGSOS.Operational.liftMap law
    (secondMorphism _ _ (Bisimilar _ _) (bisimilar_admitted _ _)) ≫
      (IndexedGSOS.Operational.liftMultiplication law).app object

/-- Every constructor occurrence in a free context preserves bisimilarity. -/
theorem context_related
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (context : S.polynomial.Free (ContextPairs law object) base sort) :
    Bisimilar (IndexedGSOS.Operational.liftObject law object)
      (IndexedGSOS.Operational.liftObject law object) base sort
      (Free.bind S.polynomial (fun _ _ pair => pair.val.1) base sort context)
      (Free.bind S.polynomial (fun _ _ pair => pair.val.2) base sort context) := by
  have complete := bisimilar_of_span (contextFirst law object)
    (contextSecond law object) base sort context
  have firstReadout : (contextFirst law object).f base sort context =
      Free.bind S.polynomial (fun _ _ pair => pair.val.1) base sort context := by
    change Free.join S.polynomial
      (Free.map S.polynomial (fun _ _ pair => pair.val.1) base sort context) = _
    unfold Free.join Free.map
    rw [Free.bind_assoc]
    rfl
  have secondReadout : (contextSecond law object).f base sort context =
      Free.bind S.polynomial (fun _ _ pair => pair.val.2) base sort context := by
    change Free.join S.polynomial
      (Free.map S.polynomial (fun _ _ pair => pair.val.2) base sort context) = _
    unfold Free.join Free.map
    rw [Free.bind_assoc]
    rfl
  rw [firstReadout, secondReadout] at complete
  exact complete

theorem constructor_congruent
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (operator : S.Operator sort)
    (first second : (position : S.Position operator) →
      (IndexedGSOS.Operational.liftObject law object).V base (S.argument operator position))
    (related : ∀ position,
      Bisimilar (IndexedGSOS.Operational.liftObject law object)
        (IndexedGSOS.Operational.liftObject law object) base (S.argument operator position)
        (first position) (second position)) :
    Bisimilar (IndexedGSOS.Operational.liftObject law object)
      (IndexedGSOS.Operational.liftObject law object) base sort
      (Free.node S.polynomial operator first) (Free.node S.polynomial operator second) := by
  let context : S.polynomial.Free (ContextPairs law object) base sort :=
    Free.node S.polynomial operator (fun position =>
      Free.pure S.polynomial ⟨(first position, second position), related position⟩)
  exact context_related law object base sort context

end Mettapedia.OSLF.FiniteBranching.Bisimulation
