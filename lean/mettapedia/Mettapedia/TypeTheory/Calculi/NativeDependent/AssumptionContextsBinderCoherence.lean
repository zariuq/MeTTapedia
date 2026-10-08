import Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContextsSubstitution

/-!
# Substitution under the two dependent pair binders

Frame substitution changes the ambient proof context while preserving its
object tuple. The independently constructed one-binder and two-binder lifts
commute with actual dependent pair packing. This comparison is derived
from the native comprehension maps and family base-change equalities.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open Mettapedia.TypeTheory.DisplayedPresheafSliceSigma

universe u w
variable {C : Type u} [Category.{u} C] (D : Cᵒᵖ ⥤ Type u)
variable {P Q : Cᵒᵖ ⥤ Type u} {n : Nat}

def objectLiftMap (change : P ⟶ Q) :
    totalSpace (ObjectInterpretation.objectFamily D P) ⟶
      totalSpace (ObjectInterpretation.objectFamily D Q) :=
  totalReindexMap change (ObjectInterpretation.objectFamily D Q)

theorem objectTuple_comp (change : P ⟶ Q) (targetTuple : Q ⟶ ObjectInterpretation.context D n) :
    objectTuple D (change ≫ targetTuple) = objectLiftMap D change ≫ objectTuple D targetTuple := by
  ext world value
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem tupleSigmaComparison (sourceTuple : P ⟶ ObjectInterpretation.context D n)
    (body : DisplayedFamily.{u,u,u,u} (ObjectInterpretation.context D (n + 1))) :
    reindexDisplayed sourceTuple
        (sigmaDisplayed (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n)) body) =
      sigmaDisplayed (ObjectInterpretation.objectFamily D P)
        (reindexDisplayed (objectTuple D sourceTuple) body) := by
  rw [sigmaDisplayed_reindex]
  congr 1

noncomputable def tuplePairIso (sourceTuple : P ⟶ ObjectInterpretation.context D n)
    (body : DisplayedFamily.{u,u,u,u} (ObjectInterpretation.context D (n + 1))) :
    totalSpace (reindexDisplayed sourceTuple
        (sigmaDisplayed (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n)) body)) ≅
      totalSpace (reindexDisplayed (objectTuple D sourceTuple) body) :=
  eqToIso (congrArg totalSpace (tupleSigmaComparison D sourceTuple body)) ≪≫
    sigmaTotalIso (ObjectInterpretation.objectFamily D P) (reindexDisplayed (objectTuple D sourceTuple) body)

set_option backward.isDefEq.respectTransparency false in
theorem tuplePack_value (sourceTuple : P ⟶ ObjectInterpretation.context D n)
    (body : DisplayedFamily.{u,u,u,u} (ObjectInterpretation.context D (n + 1)))
    (world : Cᵒᵖ) (base : P.obj world) (argument : D.obj world)
    (witness : body.obj ⟨world, ⟨sourceTuple.app world base, argument⟩⟩) :
    (tuplePairIso D sourceTuple body).inv.app world ⟨⟨base, argument⟩, witness⟩ =
      ⟨base, ⟨argument, witness⟩⟩ := by
  exact eq_of_heq (totalCast_value _ _ (tupleSigmaComparison D sourceTuple body).symm
    world ⟨base, ⟨argument, witness⟩⟩)

theorem tupleBodyComparison (change : P ⟶ Q)
    (sourceTuple : P ⟶ ObjectInterpretation.context D n) (targetTuple : Q ⟶ ObjectInterpretation.context D n)
    (same : change ≫ targetTuple = sourceTuple)
    (body : DisplayedFamily.{u,u,u,u} (ObjectInterpretation.context D (n + 1))) :
    reindexDisplayed (objectTuple D sourceTuple) body =
      reindexDisplayed (objectLiftMap D change) (reindexDisplayed (objectTuple D targetTuple) body) := by
  rw [← same, objectTuple_comp, reindexDisplayed_comp]

theorem tupleSumComparison (change : P ⟶ Q)
    (sourceTuple : P ⟶ ObjectInterpretation.context D n) (targetTuple : Q ⟶ ObjectInterpretation.context D n)
    (same : change ≫ targetTuple = sourceTuple)
    (body : DisplayedFamily.{u,u,u,u} (ObjectInterpretation.context D (n + 1))) :
    reindexDisplayed sourceTuple
        (sigmaDisplayed (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n)) body) =
      reindexDisplayed change (reindexDisplayed targetTuple
        (sigmaDisplayed (ObjectInterpretation.objectFamily D (ObjectInterpretation.context D n)) body)) := by
  rw [← same, reindexDisplayed_comp]

set_option backward.isDefEq.respectTransparency false in
theorem tuplePack_square (change : P ⟶ Q)
    (sourceTuple : P ⟶ ObjectInterpretation.context D n) (targetTuple : Q ⟶ ObjectInterpretation.context D n)
    (same : change ≫ targetTuple = sourceTuple)
    (body : DisplayedFamily.{u,u,u,u} (ObjectInterpretation.context D (n + 1))) :
    (tuplePairIso D sourceTuple body).inv ≫
        liftAlong change _ _ (tupleSumComparison D change sourceTuple targetTuple same body) =
      liftAlong (objectLiftMap D change) _ _
          (tupleBodyComparison D change sourceTuple targetTuple same body) ≫
        (tuplePairIso D targetTuple body).inv := by
  subst sourceTuple
  ext world point
  rcases point with ⟨⟨base, argument⟩, witness⟩
  have earlier := tuplePack_value D (change ≫ targetTuple) body world base argument witness
  have lifted := liftAlong_apply (objectLiftMap D change)
    (reindexDisplayed (objectTuple D (change ≫ targetTuple)) body)
    (reindexDisplayed (objectTuple D targetTuple) body)
    (tupleBodyComparison D change (change ≫ targetTuple) targetTuple rfl body)
    ⟨world, ⟨base, argument⟩⟩ witness
  change (liftAlong change _ _ (tupleSumComparison D change (change ≫ targetTuple) targetTuple rfl body)).app world
      ((tuplePairIso D (change ≫ targetTuple) body).inv.app world ⟨⟨base, argument⟩, witness⟩) =
    (tuplePairIso D targetTuple body).inv.app world
      ((liftAlong (objectLiftMap D change) _ _ (tupleBodyComparison D change (change ≫ targetTuple) targetTuple rfl body)).app world ⟨⟨base, argument⟩, witness⟩)
  rw [earlier, lifted]
  exact (tuplePack_value D targetTuple body world (change.app world base) argument witness).symm

variable {Constant Predicate : Type u}
variable (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u,u,u,u} D)
variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (PresheafInterpretation.family D constants predicates formula).sections)

set_option backward.isDefEq.respectTransparency false in
/-- The actual syntactic frame lifts commute with packing both dependent
binders. No future-arrow or substitution law is supplied as a model field. -/
theorem pack_frame_square {source target : Scope Constant Predicate n}
    (change : FrameSubstitution Declaration source target) (body : Formula Constant Predicate (n + 1)) :
    (pairIso D constants predicates source body).inv ≫
        (frame D constants predicates declarations (.proofLift change (.sigma body))).map =
      (frame D constants predicates declarations (.proofLift (.objectLift change) body)).map ≫
        (pairIso D constants predicates target body).inv := by
  exact tuplePack_square D (frame D constants predicates declarations change).map
    (tuple D constants predicates source) (tuple D constants predicates target)
    (frame D constants predicates declarations change).tuple_eq
    (PresheafInterpretation.family D constants predicates body)

end Mettapedia.TypeTheory.Calculi.NativeDependent.AssumptionContexts.Interpretation
