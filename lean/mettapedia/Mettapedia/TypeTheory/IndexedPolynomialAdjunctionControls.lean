import Mettapedia.TypeTheory.IndexedPolynomialAdjunction
import Mettapedia.TypeTheory.IndexedPolynomialInterpretationControls

/-!
# Free-algebra adjunction on genuine indexed method plans

The example polynomial has a method whose result index is two greater than its
typed child. Multiplication substitutes an entire method plan into that child;
the counit reconstructs both method steps. Different input evidence remains
distinguishable, and erasing the method increments is not an algebra morphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.FreeAdjunction.Controls

open CategoryTheory InterpretationControls

/-- The existing evidence reconstruction, packaged in the categorical algebra. -/
def resultAlgebra : Endofunctor.Algebra proofMethods.endofunctor where
  a := Result
  str := fun base index => ↾(proofResult.act base index)

/-- One method still waiting for a whole plan at its typed child. -/
def nestedPlan (input : Fin 3) : proofMethods.Free (proofMethods.Free Result) () 6 :=
  Free.node proofMethods (.advanceTwo 4)
    (fun _ => Free.pure proofMethods (examplePlan input))

/-- Monad multiplication retains the outer method and substitutes the inner one. -/
theorem multiplication_preserves_both_methods (input : Fin 3) :
    (monad proofMethods).μ.app Result () 6 (nestedPlan input) =
      Free.node proofMethods (.advanceTwo 4) (fun _ => examplePlan input) := rfl

/-- The unit is the outstanding evidence hole, not a synthetic method node. -/
theorem unit_is_typed_hole (input : Fin 3) :
    (monad proofMethods).η.app Result () 2 input = Free.pure proofMethods input := rfl

theorem counit_reconstructs_nested_methods (input : Fin 3) :
    ((adjunction proofMethods).counit.app resultAlgebra).f () 6
      ((monad proofMethods).μ.app Result () 6 (nestedPlan input)) =
      input.succ.succ.succ.succ := rfl

theorem reconstruction_depends_on_input :
    ((adjunction proofMethods).counit.app resultAlgebra).f () 6
      ((monad proofMethods).μ.app Result () 6 (nestedPlan 0)) ≠
    ((adjunction proofMethods).counit.app resultAlgebra).f () 6
      ((monad proofMethods).μ.app Result () 6 (nestedPlan 1)) := by
  intro same
  have values := congrArg Fin.val same
  change 4 = 5 at values
  contradiction

/-- Replacing reconstruction by a constant is well typed but does not satisfy
the actual algebra-morphism square. -/
def constantEvidence : (freeAlgebra proofMethods Result).a ⟶ resultAlgebra.a :=
  fun _ _ => ↾(fun _ => 0)

theorem constant_evidence_not_algebra_morphism :
    ¬ (proofMethods.endofunctor.map constantEvidence ≫ resultAlgebra.str =
      (freeAlgebra proofMethods Result).str ≫ constantEvidence) := by
  intro commutes
  have atMethod := congrArg
    (fun arrow => arrow () 4
      ⟨ProofMethod.advanceTwo 2, fun _ => Free.pure proofMethods (0 : Fin 3)⟩)
    commutes
  have values := congrArg Fin.val atMethod
  change 2 = 0 at values
  contradiction

/-- The hom equivalence's inverse reconstructs the real method, rather than
only returning its hole or forgetting its index transition. -/
theorem hom_equivalence_reconstructs_method (input : Fin 3) :
    ((homEquiv proofMethods Result resultAlgebra).symm (𝟙 Result)).f () 4
      (examplePlan input) = input.succ.succ := rfl

end Mettapedia.TypeTheory.IndexedPolynomial.FreeAdjunction.Controls
