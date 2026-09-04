import Mettapedia.UniversalAlgebra.ConsequenceEquivalence
import Mettapedia.UniversalAlgebra.FreeModel

/-!
# Invariance of free models under consequence equivalence

Finite equation systems remain occurrence-bearing data.  When two systems
generate the same equational consequence relation, however, their free term
models are canonically isomorphic by homomorphisms that preserve every
canonical variable generator.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u

variable {S : Signature.{u}}

namespace EquationSystem.SameConsequences

variable {left right : EquationSystem S}
    (equivalent : left.SameConsequences right)

/-- The canonical homomorphism from the left free model to the right free
model. -/
noncomputable def freeModelHom :
    Model.Hom (TermQuotient.model left) (TermQuotient.model right) :=
  TermQuotient.lift left (TermQuotient.model right)
    ((Model.satisfies_iff_of_sameConsequences equivalent
      (TermQuotient.model right)).mpr
        (TermQuotient.model_satisfies right))
    (fun index => TermQuotient.classOf right (.var index))

/-- The inverse-direction canonical homomorphism. -/
noncomputable def freeModelInv :
    Model.Hom (TermQuotient.model right) (TermQuotient.model left) :=
  TermQuotient.lift right (TermQuotient.model left)
    ((Model.satisfies_iff_of_sameConsequences equivalent
      (TermQuotient.model left)).mp
        (TermQuotient.model_satisfies left))
    (fun index => TermQuotient.classOf left (.var index))

/-- The canonical homomorphism carries every displayed term class to the class
of the same term in the equivalent system. -/
@[simp] theorem freeModelHom_classOf (term : Term S) :
    freeModelHom equivalent (TermQuotient.classOf left term) =
      TermQuotient.classOf right term := by
  rw [freeModelHom, TermQuotient.lift_classOf,
    TermQuotient.evaluate_canonical]

/-- The inverse homomorphism likewise preserves displayed term classes. -/
@[simp] theorem freeModelInv_classOf (term : Term S) :
    freeModelInv equivalent (TermQuotient.classOf right term) =
      TermQuotient.classOf left term := by
  rw [freeModelInv, TermQuotient.lift_classOf,
    TermQuotient.evaluate_canonical]

/-- Consequence-equivalent systems have canonically isomorphic free term
models.  The isomorphism fixes every variable generator by construction. -/
noncomputable def freeModelIso :
    Model.Iso (TermQuotient.model left) (TermQuotient.model right) where
  hom := freeModelHom equivalent
  inv := freeModelInv equivalent
  hom_inv_id := by
    intro value
    induction value using Quotient.inductionOn with
    | _ term =>
        change freeModelInv equivalent
            (freeModelHom equivalent (TermQuotient.classOf left term)) =
          TermQuotient.classOf left term
        rw [freeModelHom_classOf, freeModelInv_classOf]
  inv_hom_id := by
    intro value
    induction value using Quotient.inductionOn with
    | _ term =>
        change freeModelHom equivalent
            (freeModelInv equivalent (TermQuotient.classOf right term)) =
          TermQuotient.classOf right term
        rw [freeModelInv_classOf, freeModelHom_classOf]

/-- Explicit generator-preservation canary for the invariant isomorphism. -/
theorem freeModelIso_preserves_variable (index : Nat) :
    (freeModelIso equivalent).hom (TermQuotient.classOf left (.var index)) =
      TermQuotient.classOf right (.var index) :=
  freeModelHom_classOf equivalent (.var index)

end EquationSystem.SameConsequences

end Mettapedia.UniversalAlgebra
