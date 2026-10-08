import Mettapedia.OSLF.Syntax.FiniteBranchingBehaviour
import Mettapedia.TypeTheory.IndexedGSOSCoalgebraMonad

/-!
# Operational lifting for labelwise finite GSOS behavior

The independently defined finite-behavior law has exactly the source and
target functors of the indexed polynomial GSOS law. This comparison lets
the source-retaining free fold construct its operational coalgebra and the
actual lifted free monad. Every action has a complete finite successor set;
neither finiteness of the action carrier nor total finite support is needed.

Substitution and relabeling require the actual variable-coalgebra square.
Direct images may identify successors. No recovery of branch occurrences,
cofree adjunction, equation descent or interactive congruence is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

/-- Both independently defined functors pair a source with its complete
labelwise behavior and map both coordinates by the supplied family arrow. -/
theorem sourceBehaviourFunctor_eq_indexed :
    sourceBehaviourFunctor S Actions =
      IndexedGSOS.sourceBehaviourFunctor (behaviourFunctor S Actions) := rfl

/-- The canonical comparison preserves every component of the supplied law.
Its definitional character concerns the two presentations of the same law,
not the operational lifting subsequently derived from it. -/
def lawEquiv : Law S Actions ≃
    IndexedGSOS.Law S.polynomial (behaviourFunctor S Actions) where
  toFun law := law
  invFun law := law
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem lawEquiv_app (law : Law S Actions) (X : S.Families)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (layer : S.polynomial.Extension ((sourceBehaviourFunctor S Actions).obj X) base sort) :
    (lawEquiv S Actions law).app X base sort layer = law.app X base sort layer := rfl

abbrev VariableCoalgebra (X : S.Families) := X ⟶ (behaviourFunctor S Actions).obj X

namespace Operational

variable {S Actions} (law : Law S Actions)

/-- The actual free fold computes a complete source term beside its finite
successor sets; it uses the checked arbitrary-behavior constructor action. -/
def evaluate {X : S.Families} (inputs : VariableCoalgebra S Actions X) :=
  IndexedGSOS.Operational.evaluate (lawEquiv S Actions law) inputs

theorem evaluate_source {X : S.Families} (inputs : VariableCoalgebra S Actions X)
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free X base sort) :
    (evaluate law inputs base sort term).1 = term :=
  IndexedGSOS.Operational.evaluate_source (lawEquiv S Actions law) inputs base sort term

def coalgebra {X : S.Families} (inputs : VariableCoalgebra S Actions X) :
    VariableCoalgebra S Actions (S.polynomial.Free X) :=
  IndexedGSOS.Operational.coalgebra (lawEquiv S Actions law) inputs

@[simp]
theorem coalgebra_pure {X : S.Families} (inputs : VariableCoalgebra S Actions X)
    {base : PUnit.{u + 1}} {sort : S.Srt} (value : X base sort) (action : Actions sort) :
    coalgebra law inputs base sort (IndexedPolynomial.Free.pure S.polynomial value) action =
      Mettapedia.CategoryTheory.FinitePowerset.map
        (IndexedPolynomial.Free.pure S.polynomial) (inputs base sort value action) := rfl

/-- Each complete constructor conclusion is flattened by the actual free
monad multiplication, with all child sources and successor sets supplied. -/
theorem coalgebra_node {X : S.Families} (inputs : VariableCoalgebra S Actions X)
    {base : PUnit.{u + 1}} {sort : S.Srt} (operator : S.Operator sort)
    (children : ∀ position, S.polynomial.Free X base (S.argument operator position))
    (action : Actions sort) :
    coalgebra law inputs base sort
        (IndexedPolynomial.Free.node S.polynomial operator children) action =
      Mettapedia.CategoryTheory.FinitePowerset.map
        (IndexedPolynomial.Free.join S.polynomial)
        (law.app (S.polynomial.Free X) base sort
          ⟨operator, fun position =>
            (children position, coalgebra law inputs base _ (children position))⟩ action) :=
  congrArg (fun behavior => behavior action)
    (IndexedGSOS.Operational.coalgebra_node (lawEquiv S Actions law) inputs operator children)

/-- A supplied typed substitution that respects variable behavior respects
the complete operational behavior of every free term. -/
theorem coalgebra_bind {X Y : S.Families}
    (first : VariableCoalgebra S Actions X) (second : VariableCoalgebra S Actions Y)
    (fill : X ⟶ S.polynomial.Free Y)
    (respects : ∀ base sort value action,
      coalgebra law second base sort (fill base sort value) action =
        Mettapedia.CategoryTheory.FinitePowerset.map (fill base sort)
          (first base sort value action))
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free X base sort)
    (action : Actions sort) :
    coalgebra law second base sort
        (IndexedGSOS.Operational.bindMap fill base sort term) action =
      Mettapedia.CategoryTheory.FinitePowerset.map
        (IndexedGSOS.Operational.bindMap fill base sort) (coalgebra law first base sort term action) :=
  congrArg (fun behavior => behavior action)
    (IndexedGSOS.Operational.coalgebra_bind (lawEquiv S Actions law) first second fill
      (fun base sort value => funext (respects base sort value)) base sort term)

theorem coalgebra_rename {X Y : S.Families}
    (first : VariableCoalgebra S Actions X) (second : VariableCoalgebra S Actions Y)
    (mapping : X ⟶ Y)
    (respects : ∀ base sort value action,
      second base sort (mapping base sort value) action =
        Mettapedia.CategoryTheory.FinitePowerset.map (mapping base sort)
          (first base sort value action))
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free X base sort)
    (action : Actions sort) :
    coalgebra law second base sort (S.termMonad.map mapping base sort term) action =
      Mettapedia.CategoryTheory.FinitePowerset.map (S.termMonad.map mapping base sort)
        (coalgebra law first base sort term action) :=
  congrArg (fun behavior => behavior action)
    (IndexedGSOS.Operational.coalgebra_rename (lawEquiv S Actions law) first second mapping
      (fun base sort value => funext (respects base sort value)) base sort term)

theorem coalgebra_join {X : S.Families} (inputs : VariableCoalgebra S Actions X)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (S.polynomial.Free X) base sort) (action : Actions sort) :
    coalgebra law inputs base sort (IndexedPolynomial.Free.join S.polynomial term) action =
      Mettapedia.CategoryTheory.FinitePowerset.map
        (IndexedPolynomial.Free.join S.polynomial)
        (coalgebra law (coalgebra law inputs) base sort term action) :=
  congrArg (fun behavior => behavior action)
    (IndexedGSOS.Operational.coalgebra_join (lawEquiv S Actions law) inputs base sort term)

/-- The actual categorical free monad lifted to finite-behavior coalgebras.
Its carrier, unit and multiplication come from the original free adjunction;
their coalgebra squares are proved by the operational fold. -/
def liftedMonad : Monad (Endofunctor.Coalgebra (behaviourFunctor S Actions)) :=
  IndexedGSOS.Operational.liftedMonad (lawEquiv S Actions law)

theorem lifted_coalgebra_readout
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (term : S.polynomial.Free object.V base sort)
    (action : Actions sort) :
    ((liftedMonad law).obj object).str base sort term action =
      coalgebra law object.str base sort term action := rfl

theorem lifted_unit_readout (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (value : object.V base sort) :
    ((liftedMonad law).η.app object).f base sort value =
      IndexedPolynomial.Free.pure S.polynomial value := rfl

theorem lifted_map_readout {first second : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (mapping : first ⟶ second) (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free first.V base sort) :
    ((liftedMonad law).map mapping).f base sort term =
      S.termMonad.map mapping.f base sort term := rfl

theorem lifted_multiplication_readout
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (S.polynomial.Free object.V) base sort) :
    ((liftedMonad law).μ.app object).f base sort term =
      IndexedPolynomial.Free.join S.polynomial term := rfl

end Operational
end Mettapedia.OSLF.FiniteBranching
