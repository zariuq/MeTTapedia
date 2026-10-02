import Mettapedia.CategoryTheory.FiniteOperationTheory
import Mettapedia.GSLT.Dynamics.ResumptionCategory

/-!
# Operation theories of weighted resumption handlers

The free computation monad and its ordered writer/list handler instantiate
the same finite-arity operation theory. Handling preserves substitution,
projections and tupling. A multiplicative coefficient homomorphism supplies
a second handler; its square commutes for every operation with free variables.

This construction describes the algebraic substitution boundary. It does
not identify parallel execution with cartesian copying, nor identify a
non-additive readout with a change of coefficient algebra.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ResumptionOperationTheory

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.FiniteOperationTheory
open ResumptionAlgebra

variable (Operation : Type) (Response : Operation → Type)

abbrev FreeTheory := Theory (Computation Operation Response)

variable {Operation Response}
variable {V W : Type} [Monoid V] [Monoid W]

abbrev WeightedTheory (V : Type) [Monoid V] := Theory (WriterT V List)

def handler
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V) :
    FreeTheory Operation Response ⥤ WeightedTheory V :=
  handlerFunctor (ResumptionCategory.handle responses)
    (ResumptionCategory.handle_pure responses) (ResumptionCategory.handle_bind responses)

theorem handler_substitution
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {n m k : FreeTheory Operation Response} (first : n ⟶ m) (second : m ⟶ k) :
    (handler responses).map (first ≫ second) =
      (handler responses).map first ≫ (handler responses).map second :=
  (handler responses).map_comp first second

theorem handler_firstProjection
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    (n m : Nat) :
    (handler responses).map (firstProjection n m) = firstProjection (M := WriterT V List) n m :=
  handler_preserves_firstProjection _ _ _ _ _

theorem handler_secondProjection
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    (n m : Nat) :
    (handler responses).map (secondProjection n m) = secondProjection (M := WriterT V List) n m :=
  handler_preserves_secondProjection _ _ _ _ _

theorem handler_tuple
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {n : FreeTheory Operation Response} {m k : Nat}
    (first : n ⟶ object (Computation Operation Response) m)
    (second : n ⟶ object (Computation Operation Response) k) :
    (handler responses).map (tuple first second) =
      tuple ((handler responses).map first) ((handler responses).map second) :=
  handler_preserves_tuple _ _ _ _ _

def coefficientHandler (hom : V →* W) {Answer : Type}
    (computation : WriterT V List Answer) : WriterT W List Answer :=
  WriterT.mk (WeightedResumption.mapCoefficients hom computation.run)

theorem coefficientHandler_pure (hom : V →* W) {Answer : Type} (answer : Answer) :
    coefficientHandler hom (pure answer) = (pure answer : WriterT W List Answer) := by
  apply WriterT.ext
  change [(answer, hom 1)] = [(answer, 1)]
  rw [hom.map_one]

theorem coefficientHandler_bind (hom : V →* W) {Answer Other : Type}
    (computation : WriterT V List Answer) (next : Answer → WriterT V List Other) :
    coefficientHandler hom (computation >>= next) =
      (coefficientHandler hom computation >>= fun answer => coefficientHandler hom (next answer)) := by
  apply WriterT.ext
  exact WeightedResumption.mapCoefficients_sequence hom hom.map_mul _ _

def changeOfBase (hom : V →* W) : WeightedTheory V ⥤ WeightedTheory W :=
  handlerFunctor (coefficientHandler hom)
    (coefficientHandler_pure hom) (coefficientHandler_bind hom)

/-- The square compares independently computed coefficient interpretations,
including open operations, not only completed closed answers. -/
theorem changeOfBase_commutes (hom : V →* W)
    (responses : (operation : Operation) → WeightedResumption.Contributions (Response operation) V)
    {n m : FreeTheory Operation Response} (operation : n ⟶ m) (index : Fin m) :
    (terms ((handler responses ⋙ changeOfBase hom).map operation) index).run =
      (terms ((handler (fun request =>
        WeightedResumption.mapCoefficients hom (responses request))).map operation) index).run :=
  ResumptionCategory.handle_changeOfBase hom responses (terms operation index)

end Mettapedia.GSLT.Dynamics.ResumptionOperationTheory
