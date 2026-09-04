import Mathlib.Logic.Equiv.Basic
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# Dependent right adjoints between categories with families

A dependent right adjoint has an ordinary functorial action `L` on context
categories, but its right action is indexed: a type over `L Gamma` is sent to
a type over `Gamma`, and terms are related by a natural equivalence.

This is the CwF formulation used by modal dependent type theory.  It is
strictly weaker than an ordinary right adjoint on context categories and does
not require an arbitrary type over `Gamma` to arise from the right action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfDependentRightAdjoint

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-- A dependent right adjoint from `domain` to `codomain`.

`leftContext` and `leftSub` form the context functor `L`.  `rightType` is the
dependent right action on types over `L Gamma`, and `termEquiv` is its
fibrewise adjunction law. -/
structure DependentRightAdjoint
    (domain codomain : Cwf.{u, v, w, w'}) where
  leftContext : domain.Ctx -> codomain.Ctx
  leftSub : {first last : domain.Ctx} -> domain.Sub first last ->
    codomain.Sub (leftContext first) (leftContext last)
  leftSub_id : forall context,
    leftSub (domain.idS context) = codomain.idS (leftContext context)
  leftSub_comp : forall {first middle last : domain.Ctx}
    (later : domain.Sub middle last) (earlier : domain.Sub first middle),
    leftSub (domain.compS later earlier) =
      codomain.compS (leftSub later) (leftSub earlier)
  rightType : (context : domain.Ctx) ->
    codomain.Ty (leftContext context) -> domain.Ty context
  rightType_natural : forall {first last : domain.Ctx}
    (type : codomain.Ty (leftContext last))
    (substitution : domain.Sub first last),
    rightType first (codomain.tySub type (leftSub substitution)) =
      domain.tySub (rightType last type) substitution
  termEquiv : forall (context : domain.Ctx)
    (type : codomain.Ty (leftContext context)),
    (codomain.Tm (leftContext context) type) ≃
      (domain.Tm context (rightType context type))
  termEquiv_natural : forall {first last : domain.Ctx}
    (type : codomain.Ty (leftContext last))
    (term : codomain.Tm (leftContext last) type)
    (substitution : domain.Sub first last),
    HEq
      ((termEquiv first
        (codomain.tySub type (leftSub substitution)))
          (codomain.tmSub term (leftSub substitution)))
      (domain.tmSub ((termEquiv last type) term) substitution)

/-- A dependent right adjoint between full CwFs with chosen terminal
contexts.  The DRA context functor need not preserve the chosen terminal
object; no such extra condition occurs in the standard definition. -/
structure DependentRightAdjointWithTerminal
    (domain codomain : CwfWithTerminal.{u, v, w, w'}) where
  toDra : DependentRightAdjoint domain.toCwf codomain.toCwf

namespace DependentRightAdjoint

/-- Every CwF has the identity dependent right adjoint. -/
def identity (cwf : Cwf.{u, v, w, w'}) :
    DependentRightAdjoint cwf cwf where
  leftContext context := context
  leftSub substitution := substitution
  leftSub_id _ := rfl
  leftSub_comp _ _ := rfl
  rightType _ type := type
  rightType_natural _ _ := rfl
  termEquiv _ _ := Equiv.refl _
  termEquiv_natural _ _ _ := HEq.rfl

@[simp]
theorem identity_leftContext (cwf : Cwf.{u, v, w, w'})
    (context : cwf.Ctx) :
    (identity cwf).leftContext context = context :=
  rfl

@[simp]
theorem identity_rightType (cwf : Cwf.{u, v, w, w'})
    (context : cwf.Ctx) (type : cwf.Ty context) :
    (identity cwf).rightType context type = type :=
  rfl

#print axioms identity
#print axioms identity_leftContext
#print axioms identity_rightType

end DependentRightAdjoint

namespace DependentRightAdjointWithTerminal

/-- The identity DRA on a full CwF. -/
def identity (cwf : CwfWithTerminal.{u, v, w, w'}) :
    DependentRightAdjointWithTerminal cwf cwf where
  toDra := DependentRightAdjoint.identity cwf.toCwf

#print axioms identity

end DependentRightAdjointWithTerminal

end Mettapedia.TypeTheory.CwfDependentRightAdjoint
