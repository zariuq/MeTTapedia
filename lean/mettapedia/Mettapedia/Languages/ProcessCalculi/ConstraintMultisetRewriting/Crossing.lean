import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedVariables
import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Existing crossing sets select fresh or captured variable identities

The scope policy is the existing `TemplateScope.crossOwn` with lexical-fresh
default ownership. Its output is translated into the local/shared variable
coordinates used by first-order rule freshening. This translation changes
identities before solving equations; it does not change the unifier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Crossing

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.TemplateScope (crossOwn)

universe u v

variable {Name : Type*} [DecidableEq Name]

def classify (crossing : Option (List Name)) (used : List Name) (name : Name) : Name ⊕ Name :=
  if name ∈ crossOwn crossing used used then .inl name else .inr name

def nameAt (scope : Nat) (crossing : Option (List Name)) (used : List Name)
    (name : Name) : ScopedVar Name ⊕ Name :=
  ScopedVariables.variableAt scope (classify crossing used name)

theorem plain_pattern_is_fresh (scope : Nat) (used : List Name) (name : Name)
    (member : name ∈ used) : nameAt scope none used name = .inl (ScopedVar.at scope name) := by
  simp [nameAt, classify, member, ScopedVariables.variableAt]

theorem crossed_name_is_shared (scope : Nat) (crossing used : List Name) (name : Name)
    (crossed : name ∈ crossing) : nameAt scope (some crossing) used name = .inr name := by
  simp [nameAt, classify, crossOwn, crossed, ScopedVariables.variableAt]

theorem uncrossed_pattern_is_fresh (scope : Nat) (crossing used : List Name) (name : Name)
    (usedHere : name ∈ used) (uncrossed : name ∉ crossing) :
    nameAt scope (some crossing) used name = .inl (ScopedVar.at scope name) := by
  simp [nameAt, classify, crossOwn, usedHere, uncrossed, ScopedVariables.variableAt]

/-- A source name is resolved into the existing LP syntax with new variable
coordinates. This is not an evaluator for a `let` or a call. -/
def termAt {signature : LPSignature.{u, u, v, u}} [DecidableEq signature.vars]
    (scope : Nat) (crossing : Option (List signature.vars))
    (used : List signature.vars) (term : Term signature) :
    Term (signature.withVars (ScopedVar signature.vars ⊕ signature.vars)) :=
  term.renameVars (nameAt scope crossing used)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Crossing
