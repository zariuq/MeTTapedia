import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore
import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Contextual assignments use the existing intrinsic binding syntax

Each metavariable has its own declared parameter context and result sort.
Its image may contain other metavariables. Instantiation uses the existing
`instInto` operation and its proved substitution algebra; object variables
remain rigid, while equations can refine metavariables on both sides.

This profile describes one finite prepared metavariable frame, of arbitrary
size. It does not limit the variable supply of the general calculus or supply
a higher-order unification algorithm. Frame extension and the common raw-ABT
representation are separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrame

open Mettapedia.OSLF.Binding

variable (signature : Signature) (metas : List (MetaArity signature))

abbrev Assignment := (i : Fin metas.length) →
  Term (withMetas signature metas) (metas.get i).1 (metas.get i).2

/-- This is the existing contextual substitution operation, acting on the
existing term carrier. Scope and sort restrictions are intrinsic to its type. -/
def action (context : Ctx signature) (sort : signature.Srt) :
    SubstitutionAction (Term (withMetas signature metas) context sort) (Assignment signature metas) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun body term => instInto body term
  identity := metaVar
  compose := fun outer inner i => instInto outer (inner i)
  apply_identity := instInto_metaVar_id
  apply_compose := fun outer inner term => (instInto_instInto inner outer term).symm
  preserves := fun body {_ _} same => congrArg (instInto body) same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrame
