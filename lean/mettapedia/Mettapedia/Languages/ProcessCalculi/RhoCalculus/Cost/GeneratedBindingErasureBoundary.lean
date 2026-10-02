import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedCollectionEquationModel
import Mettapedia.GSLT.LanguageDef.BindingSignatureValuation

/-!
# Intrinsic type information omitted by generated raw erasure

The existing structural lambda and substitution representation omits their
domain annotations in raw Patterns. Two well-typed terms in the actual
generated rho signature can therefore have the same context, result sort and
raw erasure while retaining different substitution domains. Their replacement
functions ignore their input. The counterexample concerns intrinsic syntax
equality, not inequality of their evaluated programs.

A semantic readout may respect the erasure without reconstructing all this
intrinsic type data. Such a readout needs semantic compatibility, rather than
an injectivity claim about the entire erased syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedBindingErasureBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily
open GeneratedCollectionEquationModel

abbrev processSort : TypeExpr := .base (costBaseSortName "Proc")
abbrev nameSort : TypeExpr := .base (costBaseSortName "Name")

def zero (Γ : List TypeExpr) : Term (signatureOf language) Γ processSort :=
  nullary (unitRule .base) (unit_member .base) rfl

def constantFunction (domain : TypeExpr) :
    Term (signatureOf language) [] (.arrow domain processSort) :=
  .op (.lambda domain processSort) (.cons (zero [domain]) .nil)

def discardedFunction (domain : TypeExpr) : Term (signatureOf language) [] processSort :=
  .op (.subst (.arrow domain processSort) processSort)
    (.cons (zero [.arrow domain processSort]) (.cons (constantFunction domain) .nil))

def substitutionDomain (term : Term (signatureOf language) [] processSort) : Option TypeExpr :=
  match term with
  | .var position => nomatch position
  | .op (.subst domain _) _ => some domain
  | .op _ _ => none

/-- These are distinct intrinsic operators even at the same closed result
fibre; the actual raw constructor omits their respective domain types. -/
theorem discardedFunctions_distinct :
    discardedFunction processSort ≠ discardedFunction nameSort := by
  intro same
  have domains := congrArg substitutionDomain same
  change some (TypeExpr.arrow processSort processSort) =
    some (TypeExpr.arrow nameSort processSort) at domains
  cases domains

theorem discardedFunctions_same_erasure :
    erase (discardedFunction processSort) = erase (discardedFunction nameSort) := by
  simp only [discardedFunction, constantFunction, erase]
  rw [show erase (zero [.arrow processSort processSort]) = .apply (unitName .base) [] by
        exact erase_nullary _ _ _,
    show erase (zero [processSort]) = .apply (unitName .base) [] by
        exact erase_nullary _ _ _,
    show erase (zero [.arrow nameSort processSort]) = .apply (unitName .base) [] by
        exact erase_nullary _ _ _,
    show erase (zero [nameSort]) = .apply (unitName .base) [] by
        exact erase_nullary _ _ _]

/-- Raw erasure cannot recover the full intrinsic syntax of this actual
generated signature, even after fixing context and result sort. -/
theorem closed_process_erasure_not_injective :
    ¬ Function.Injective (erase (language := language) (bound := []) (type := processSort)) := by
  intro injective
  exact discardedFunctions_distinct (injective discardedFunctions_same_erasure)

def closedAssignment {base : String → Type} :
    (sort : TypeExpr) → Var [] sort → Valuation.Value base sort :=
  fun _ position => nomatch position

/-- In the independently defined function-valued interpreter, the discarded
replacement has no influence. This holds for arbitrary constructor meanings,
without collapsing the program carrier to a singleton. -/
theorem discardedFunction_value {base : String → Type}
    (constructors : Valuation.Constructors language base) (domain : TypeExpr) :
    Valuation.read constructors (Valuation.interpret constructors (discardedFunction domain))
        closedAssignment =
      Valuation.read constructors (Valuation.interpret constructors (zero []))
        closedAssignment := rfl

/-- Semantic agreement coexists with the checked failure of syntax recovery. -/
theorem discardedFunctions_same_value {base : String → Type}
    (constructors : Valuation.Constructors language base) :
    Valuation.read constructors (Valuation.interpret constructors (discardedFunction processSort))
        closedAssignment =
      Valuation.read constructors (Valuation.interpret constructors (discardedFunction nameSort))
        closedAssignment :=
  (discardedFunction_value constructors processSort).trans
    (discardedFunction_value constructors nameSort).symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.GeneratedBindingErasureBoundary
