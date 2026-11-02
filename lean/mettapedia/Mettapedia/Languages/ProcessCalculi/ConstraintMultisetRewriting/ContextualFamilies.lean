import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# Contextual substitution in the shared equation core

The declaration family is arbitrary, so fresh identities can be allocated
without imposing a finite bound on programs. Its images, argument spines and
object binders are the common intrinsically scoped binding terms. Both sides
of equations use this same action; object variables remain rigid.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies

open Mettapedia.OSLF.Binding hiding instantiate
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} (declaration : V → MetaArity S)

def action (context : Ctx S) (sort : S.Srt) :
    SubstitutionAction (Term (signature S declaration) context sort)
      (Assignment declaration declaration) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun assignment term => ContextualFamily.instantiate assignment term
  identity := generator declaration
  compose := fun outer inner identity => instantiate outer (inner identity)
  apply_identity := instantiate_identity
  apply_compose := fun outer inner term => (instantiate_comp inner outer term).symm
  preserves := by
    intro assignment first second same
    exact congrArg (fun term : Term (signature S declaration) context sort =>
      ContextualFamily.instantiate assignment term) same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies
