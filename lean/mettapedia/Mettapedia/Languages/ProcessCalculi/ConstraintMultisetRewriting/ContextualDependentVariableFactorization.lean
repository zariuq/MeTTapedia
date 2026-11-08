import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCommonSelection

/-!
# Computed factorization of typed variable inclusions

Finite lookup computes the factor of a variable map through an inclusion.
Injectivity gives uniqueness and reflection of declaration compatibility;
the factor is itself a typed inclusion when the original map is injective.
No inhabitant is assigned to a variable outside the image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentVariableFactorization

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentScopeConsequence

def factor {n k m : Nat} (outer : Ren k m) (inner : Ren n m)
    (inside : ∀ index, ∃ prior, outer prior = inner index) : Ren n k :=
  fun index => (ContextualDependentInversion.lookup outer (inner index)).get
    ((commonMask_iff outer inner index).mpr (inside index))

theorem factor_image {n k m : Nat} (outer : Ren k m) (inner : Ren n m)
    (inside : ∀ index, ∃ prior, outer prior = inner index) (index : Fin n) :
    outer (factor outer inner inside index) = inner index := by
  apply ContextualDependentInversion.lookup_sound outer
  exact (Option.some_get _).symm

theorem factor_unique {n k m : Nat} (outer : Ren k m) (inner : Ren n m)
    (inside : ∀ index, ∃ prior, outer prior = inner index) (injective : Function.Injective outer)
    (other : Ren n k) (image : ∀ index, outer (other index) = inner index) :
    other = factor outer inner inside := by
  funext index
  exact injective ((image index).trans (factor_image outer inner inside index).symm)

theorem factor_injective {n k m : Nat} (outer : Ren k m) (inner : Ren n m)
    (inside : ∀ index, ∃ prior, outer prior = inner index) (injective : Function.Injective inner) :
    Function.Injective (factor outer inner inside) := by
  intro first second same
  apply injective
  rw [← factor_image outer inner inside first, ← factor_image outer inner inside second, same]

theorem rename_injective {Head : Type} {n m : Nat} (rho : Ren n m) (injective : Function.Injective rho) :
    Function.Injective (Presentation.rename (Head := Head) rho) := by
  intro first second same
  have one := ContextualDependentInversion.invert_rename first rho _
    (ContextualDependentInversion.lookup_exact rho injective)
  have two := ContextualDependentInversion.invert_rename second rho _
    (ContextualDependentInversion.lookup_exact rho injective)
  rw [same] at one
  exact Option.some.inj (one.symm.trans two)

theorem factor_compatible {Head : Type} {n k m : Nat} {source : Ctx Head n} {middle : Ctx Head k}
    {ambient : Ctx Head m} (outer : Ren k m) (inner : Ren n m)
    (inside : ∀ index, ∃ prior, outer prior = inner index) (injective : Function.Injective outer)
    (outerCompatible : CtxRen middle ambient outer) (innerCompatible : CtxRen source ambient inner) :
    CtxRen source middle (factor outer inner inside) := by
  intro index
  apply rename_injective outer injective
  calc
    Presentation.rename outer (Ctx.lookup middle (factor outer inner inside index))
        = Ctx.lookup ambient (outer (factor outer inner inside index)) := (outerCompatible _).symm
    _ = Ctx.lookup ambient (inner index) := congrArg (Ctx.lookup ambient) (factor_image outer inner inside index)
    _ = Presentation.rename inner (Ctx.lookup source index) := innerCompatible index
    _ = Presentation.rename outer (Presentation.rename (factor outer inner inside) (Ctx.lookup source index)) := by
      rw [rename_comp]
      apply congrArg (fun rho => Presentation.rename rho (Ctx.lookup source index))
      funext position
      exact (factor_image outer inner inside position).symm

variable {Head : Type} {rules : Rules Head}

def inclusion {source middle ambient : Context rules} (outer : Inclusion middle ambient) (inner : Inclusion source ambient)
    (inside : ∀ index, ∃ prior, outer.forward prior = inner.forward index)
    (outerCompatible : CtxRen middle.raw ambient.raw outer.forward)
    (innerCompatible : CtxRen source.raw ambient.raw inner.forward) : Inclusion source middle where
  forward := factor outer.forward inner.forward inside
  injective := factor_injective outer.forward inner.forward inside inner.injective
  typed := by
    intro index
    change Typed rules middle.raw (.var (factor outer.forward inner.forward inside index))
      (subst (renSub (factor outer.forward inner.forward inside)) (Ctx.lookup source.raw index))
    rw [subst_renSub, ← factor_compatible outer.forward inner.forward inside outer.injective outerCompatible innerCompatible index]
    exact .var _

end ContextualDependentVariableFactorization
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
