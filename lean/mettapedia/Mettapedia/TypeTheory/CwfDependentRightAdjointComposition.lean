import Mettapedia.TypeTheory.CwfDependentRightAdjoint

/-!
# Composition of dependent right adjoints

Dependent right adjoints are closed under composition.  Context functors
compose covariantly, while the dependent right actions on types and terms
compose in the opposite order.  The naturality proof is the corresponding
pasting of the two heterogeneous term-naturality squares.

This construction is the algebra needed to speak about a composite modal
route between CwFs rather than merely listing adjacent modalities.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfDependentRightAdjoint

open Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

namespace DependentRightAdjoint

/-- A dependent term equivalence respects simultaneous equality of its
input type and heterogeneous equality of its input term.  Keeping this
transport step separate makes composition a pasting of two naturality
squares instead of relying on elaborator-chosen dependent casts. -/
private theorem termEquiv_congr
    {domain codomain : Cwf.{u, v, w, w'}}
    (dra : DependentRightAdjoint domain codomain)
    (context : domain.Ctx)
    {leftType rightType : codomain.Ty (dra.leftContext context)}
    (sameType : leftType = rightType)
    {leftTerm : codomain.Tm (dra.leftContext context) leftType}
    {rightTerm : codomain.Tm (dra.leftContext context) rightType}
    (sameTerm : HEq leftTerm rightTerm) :
    HEq
      (dra.termEquiv context leftType leftTerm)
      (dra.termEquiv context rightType rightTerm) := by
  subst rightType
  have termsEqual : leftTerm = rightTerm := eq_of_heq sameTerm
  subst rightTerm
  exact HEq.rfl

/-- Compose dependent right adjoints in context-execution order. -/
def comp {first middle last : Cwf.{u, v, w, w'}}
    (earlier : DependentRightAdjoint first middle)
    (later : DependentRightAdjoint middle last) :
    DependentRightAdjoint first last where
  leftContext context := later.leftContext (earlier.leftContext context)
  leftSub substitution := later.leftSub (earlier.leftSub substitution)
  leftSub_id context := by
    rw [earlier.leftSub_id, later.leftSub_id]
  leftSub_comp laterSub earlierSub := by
    rw [earlier.leftSub_comp, later.leftSub_comp]
  rightType context type :=
    earlier.rightType context
      (later.rightType (earlier.leftContext context) type)
  rightType_natural := by
    intro firstContext lastContext type substitution
    rw [later.rightType_natural type (earlier.leftSub substitution)]
    exact earlier.rightType_natural
      (later.rightType (earlier.leftContext lastContext) type) substitution
  termEquiv context type :=
    (later.termEquiv (earlier.leftContext context) type).trans
      (earlier.termEquiv context
        (later.rightType (earlier.leftContext context) type))
  termEquiv_natural := by
    intro firstContext lastContext type term substitution
    change HEq
      ((earlier.termEquiv firstContext _)
        ((later.termEquiv (earlier.leftContext firstContext) _)
          (last.tmSub term
            (later.leftSub (earlier.leftSub substitution)))))
      (first.tmSub
        ((earlier.termEquiv lastContext _)
          ((later.termEquiv (earlier.leftContext lastContext) type) term))
        substitution)
    have laterTypeNatural := later.rightType_natural type
      (earlier.leftSub substitution)
    have laterNatural := later.termEquiv_natural type term
      (earlier.leftSub substitution)
    have liftedLaterNatural := termEquiv_congr earlier
      firstContext laterTypeNatural laterNatural
    exact liftedLaterNatural.trans (earlier.termEquiv_natural
      (later.rightType (earlier.leftContext lastContext) type)
      ((later.termEquiv (earlier.leftContext lastContext) type) term)
      substitution)

@[simp]
theorem comp_leftContext {first middle last : Cwf.{u, v, w, w'}}
    (earlier : DependentRightAdjoint first middle)
    (later : DependentRightAdjoint middle last) (context : first.Ctx) :
    (comp earlier later).leftContext context =
      later.leftContext (earlier.leftContext context) :=
  rfl

@[simp]
theorem comp_leftSub {first middle last : Cwf.{u, v, w, w'}}
    (earlier : DependentRightAdjoint first middle)
    (later : DependentRightAdjoint middle last)
    {source target : first.Ctx} (substitution : first.Sub source target) :
    (comp earlier later).leftSub substitution =
      later.leftSub (earlier.leftSub substitution) :=
  rfl

@[simp]
theorem comp_rightType {first middle last : Cwf.{u, v, w, w'}}
    (earlier : DependentRightAdjoint first middle)
    (later : DependentRightAdjoint middle last)
    (context : first.Ctx)
    (type : last.Ty (later.leftContext (earlier.leftContext context))) :
    (comp earlier later).rightType context type =
      earlier.rightType context
        (later.rightType (earlier.leftContext context) type) :=
  rfl

/-- The composite term equivalence acts by the later transposition followed
by the earlier one. -/
theorem comp_termEquiv_apply {first middle last : Cwf.{u, v, w, w'}}
    (earlier : DependentRightAdjoint first middle)
    (later : DependentRightAdjoint middle last)
    (context : first.Ctx)
    (type : last.Ty (later.leftContext (earlier.leftContext context)))
    (term : last.Tm
      (later.leftContext (earlier.leftContext context)) type) :
    (comp earlier later).termEquiv context type term =
      earlier.termEquiv context
        (later.rightType (earlier.leftContext context) type)
        (later.termEquiv (earlier.leftContext context) type term) :=
  rfl

end DependentRightAdjoint

namespace DependentRightAdjointWithTerminal

/-- Composition does not require either context functor to preserve the
chosen terminal object. -/
def comp {first middle last : CwfWithTerminal.{u, v, w, w'}}
    (earlier : DependentRightAdjointWithTerminal first middle)
    (later : DependentRightAdjointWithTerminal middle last) :
    DependentRightAdjointWithTerminal first last where
  toDra := DependentRightAdjoint.comp earlier.toDra later.toDra

end DependentRightAdjointWithTerminal

#print axioms DependentRightAdjoint.comp
#print axioms DependentRightAdjoint.comp_leftContext
#print axioms DependentRightAdjoint.comp_rightType
#print axioms DependentRightAdjoint.comp_termEquiv_apply
#print axioms DependentRightAdjointWithTerminal.comp

end Mettapedia.TypeTheory.CwfDependentRightAdjoint
