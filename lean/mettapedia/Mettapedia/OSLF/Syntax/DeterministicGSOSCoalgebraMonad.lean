import Mettapedia.OSLF.Syntax.DeterministicGSOSOperational

/-!
# The actual free monad lifted to deterministic coalgebras

The operational constructor fold equips every free carrier with complete
behavior. Its relabeling, unit and multiplication are genuine coalgebra
morphisms. Their categorical monad laws follow from the original free
monad while their coalgebra compatibility is earned from the natural law.
No cofree-history comonad or lookahead law is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.Operational

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u} (law : Law S Actions)

/-- The actual operational coalgebra carried by the original free terms. -/
noncomputable def liftObject (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    Endofunctor.Coalgebra (behaviourFunctor S Actions) where
  V := S.polynomial.Free object.V
  str := coalgebra law object.str

/-- Free relabeling respects operational behavior by the earned naturality theorem. -/
noncomputable def liftMap
    {first second : Endofunctor.Coalgebra (behaviourFunctor S Actions)}
    (mapping : first ⟶ second) : liftObject law first ⟶ liftObject law second where
  f := S.termMonad.map mapping.f
  h := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro term
    have respectsInputs : ∀ base sort value,
        second.str base sort (mapping.f base sort value) =
          fun action => (first.str base sort value action).map (mapping.f base sort) := by
      intro base sort value
      have exactMap := congrArg (fun map => map base sort value) mapping.h
      exact exactMap.symm
    exact (coalgebra_rename law first.str second.str mapping.f respectsInputs base sort term).symm

/-- The genuine lifted free-term functor on deterministic transition coalgebras. -/
noncomputable def liftFunctor :
    Endofunctor.Coalgebra (behaviourFunctor S Actions) ⥤
      Endofunctor.Coalgebra (behaviourFunctor S Actions) where
  obj := liftObject law
  map := liftMap law
  map_id object := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.map_id object.V
  map_comp earlier later := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.map_comp earlier.f later.f

/-- The original free-monad unit is a real operational coalgebra morphism. -/
noncomputable def liftUnit :
    𝟭 (Endofunctor.Coalgebra (behaviourFunctor S Actions)) ⟶ liftFunctor law where
  app object :=
    { f := S.termMonad.η.app object.V
      h := by
        funext base sort
        apply ConcreteCategory.hom_ext
        intro value
        funext action
        exact (coalgebra_pure law object.str value action).symm }
  naturality {first second} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.η.naturality mapping.f

/-- The original flattening multiplication is a real operational coalgebra morphism. -/
noncomputable def liftMultiplication : liftFunctor law ⋙ liftFunctor law ⟶ liftFunctor law where
  app object :=
    { f := S.termMonad.μ.app object.V
      h := by
        funext base sort
        apply ConcreteCategory.hom_ext
        intro term
        exact (coalgebra_join law object.str base sort term).symm }
  naturality {first second} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.μ.naturality mapping.f

/-- The original free monad, equipped with its earned operational lifting. -/
noncomputable def liftedMonad : Monad (Endofunctor.Coalgebra (behaviourFunctor S Actions)) where
  toFunctor := liftFunctor law
  η := liftUnit law
  μ := liftMultiplication law
  assoc object := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.assoc object.V
  left_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.left_unit object.V
  right_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact S.termMonad.right_unit object.V

/-- Forgetting the lifted carrier recovers the existing free-monad carrier exactly. -/
theorem lifted_carrier (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    ((liftedMonad law).obj object).V = S.termMonad.obj object.V := rfl

/-- The monad unit retains the complete supplied variable. -/
theorem lifted_unit_readout (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (value : object.V base sort) :
    ((liftedMonad law).η.app object).f base sort value =
      IndexedPolynomial.Free.pure S.polynomial value := rfl

/-- The monad multiplication retains the actual flattened constructor term. -/
theorem lifted_multiplication_readout (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (S.polynomial.Free object.V) base sort) :
    ((liftedMonad law).μ.app object).f base sort term =
      IndexedPolynomial.Free.join S.polynomial term := rfl

end Mettapedia.OSLF.DeterministicGSOS.Operational
