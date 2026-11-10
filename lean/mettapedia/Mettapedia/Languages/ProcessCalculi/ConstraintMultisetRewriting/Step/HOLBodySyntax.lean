import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLModelsBody
import Mettapedia.Logic.HOL.Syntax.NamedElaboration

/-! # Named construction of independent typed HOL definition bodies

The existing named elaborator supplies binding and type checking. Constants
carry their full source symbols; Boolean operators remain calls to the source
definitions. This is an authoring aid for expected bodies, not an additional
source parser or a definition-admission rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLBodySyntax

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open StandardTheoryInterpretation.Interpretation

private def atomicEquality : DecidableEq AtomicTy := fun first second =>
  if same : Ty.same first.val second.val = true then
    .isTrue (Subtype.ext ((Ty.same_eq_true_iff _ _).mp same))
  else .isFalse (fun equal => same ((Ty.same_eq_true_iff _ _).mpr (congrArg Subtype.val equal)))

local instance : DecidableEq AtomicTy := atomicEquality

abbrev Syntax := HOL.NamedElaboration.NamedTerm AtomicTy String (Sigma Symbol)

def signature : HOL.NamedElaboration.Signature (Sigma Symbol) Symbol := fun symbol => some symbol

def checkClosed (expected : HOL.Ty AtomicTy) (term : Syntax) : Option (HOL.ClosedTerm Symbol expected) :=
  (HOL.NamedElaboration.check signature .nil term expected).toOption

def varTerm (name : String) : Syntax := .variable name
def constant {type : HOL.Ty AtomicTy} (symbol : Symbol type) : Syntax := .constant ⟨type, symbol⟩
def apps (function : Syntax) (arguments : List Syntax) : Syntax := arguments.foldl (fun f a => .app f a) function
def lambdas (binders : List (String × HOL.Ty AtomicTy)) (body : Syntax) : Syntax :=
  binders.foldr (fun binder body => .lam binder.1 binder.2 body) body
def conjunction (first second : Syntax) : Syntax := apps (constant Symbols.conjunction) [first, second]
def implication (first second : Syntax) : Syntax := apps (constant Symbols.implication) [first, second]
def all (name : String) (type : HOL.Ty AtomicTy) (body : Syntax) : Syntax :=
  .app (constant (Symbols.universal type)) (.lam name type body)
def existsTerm (name : String) (type : HOL.Ty AtomicTy) (body : Syntax) : Syntax :=
  .app (constant (Symbols.existential type)) (.lam name type body)

namespace Controls

theorem scoped_identity :
    (checkClosed (.arr HOLModelsBody.termType HOLModelsBody.termType)
      (.lam "x" HOLModelsBody.termType (varTerm "x"))).isSome = true := by
  decide +kernel

theorem escaped_variable_refused :
    checkClosed HOLModelsBody.termType (varTerm "x") = none := by
  decide +kernel

theorem mismatched_argument_refused :
    checkClosed .prop (.app (constant Symbols.conjunction)
      (.lam "x" HOLModelsBody.termType (varTerm "x"))) = none := by
  decide +kernel

end Controls

#print axioms Controls.scoped_identity
#print axioms Controls.escaped_variable_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLBodySyntax
