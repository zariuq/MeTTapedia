import Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics
import Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity

/-!
# Binder resolution for semantic FOF

The official TPTP abstract syntax preserves source variable spellings.  This
module gives the next semantic refinement: a small named first-order syntax
and a capture-avoiding partial translation to the de Bruijn representation
used by `TptpFofNormalizationSemantics`.

The resolver always chooses the nearest enclosing binder.  Free variables in
a closed FOF formula are rejected.  This module does not parse the official
grammar-shaped AST; that preceding elaboration remains a separate,
source-preserving transformation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution

open LO FirstOrder
open TptpFofNormalizationSemantics
open TptpFofSymbolIdentity

/-! ## Named semantic source -/

inductive NamedTerm where
  | variable (name : String)
  | function (head : FunctionHead) (arguments : List NamedTerm)

inductive NamedFormula where
  | verum
  | falsum
  | predicate (head : PredicateHead) (arguments : List NamedTerm)
  | equal (left right : NamedTerm)
  | not (body : NamedFormula)
  | and (left right : NamedFormula)
  | or (left right : NamedFormula)
  | iff (left right : NamedFormula)
  | implies (left right : NamedFormula)
  | reverseImplies (left right : NamedFormula)
  | xor (left right : NamedFormula)
  | nor (left right : NamedFormula)
  | nand (left right : NamedFormula)
  | all (binder : String) (body : NamedFormula)
  | ex (binder : String) (body : NamedFormula)

/-! ## Nearest-binder lookup -/

def lookupBinder? (name : String) :
    (environment : List String) -> Option (Fin environment.length)
  | [] => none
  | binder :: environment =>
      if name = binder then
        some 0
      else
        (lookupBinder? name environment).map Fin.succ

theorem lookupBinder?_head (name : String) (environment : List String) :
    lookupBinder? name (name :: environment) = some 0 := by
  simp [lookupBinder?]

theorem lookupBinder?_tail {name binder : String}
    (different : name ≠ binder) (environment : List String) :
    lookupBinder? name (binder :: environment) =
      (lookupBinder? name environment).map Fin.succ := by
  simp [lookupBinder?, different]

/-! ## Capture-avoiding resolution -/

def resolveTerm? (environment : List String) :
    NamedTerm -> Option (Term environment.length)
  | .variable name =>
      (lookupBinder? name environment).map Semiterm.bvar
  | .function head arguments => do
      let resolved <- arguments.mapM (resolveTerm? environment)
      pure <| .func
        ({ name := head.lexeme, kind := head.kind } :
          FunctionSymbol resolved.length)
        (fun index => resolved.get index)

def resolveFormula? (environment : List String) :
    NamedFormula -> Option (Formula environment.length)
  | .verum => some .verum
  | .falsum => some .falsum
  | .predicate head arguments => do
      let resolved <- arguments.mapM (resolveTerm? environment)
      pure <| .predicate
        ({ name := head.lexeme, kind := head.kind } :
          PredicateSymbol resolved.length)
        (fun index => resolved.get index)
  | .equal left right => do
      pure <| .equal
        (← resolveTerm? environment left)
        (← resolveTerm? environment right)
  | .not body => Formula.not <$> resolveFormula? environment body
  | .and left right => do
      pure <| .and
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .or left right => do
      pure <| .or
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .iff left right => do
      pure <| .iff
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .implies left right => do
      pure <| .implies
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .reverseImplies left right => do
      pure <| .reverseImplies
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .xor left right => do
      pure <| .xor
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .nor left right => do
      pure <| .nor
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .nand left right => do
      pure <| .nand
        (← resolveFormula? environment left)
        (← resolveFormula? environment right)
  | .all binder body =>
      Formula.all <$> resolveFormula? (binder :: environment) body
  | .ex binder body =>
      Formula.ex <$> resolveFormula? (binder :: environment) body

def resolveClosedFormula? : NamedFormula -> Option (Formula 0) :=
  resolveFormula? []

/-! ## Exact positive and negative controls -/

namespace Canary

def shadowingSource : NamedFormula :=
  .all "X" <| .and
    (.equal (.variable "X") (.variable "X"))
    (.ex "X" (.equal (.variable "X") (.variable "X")))

def shadowingTarget : Formula 0 :=
  .all <| .and
    (.equal (.bvar 0) (.bvar 0))
    (.ex (.equal (.bvar 0) (.bvar 0)))

theorem shadowing_resolves_to_nearest_binder :
    resolveClosedFormula? shadowingSource = some shadowingTarget := by
  simp [resolveClosedFormula?, shadowingSource, shadowingTarget,
    resolveFormula?, resolveTerm?, lookupBinder?]

def twoBinderSource : NamedFormula :=
  .all "X" <| .ex "Y" <|
    .equal (.variable "X") (.variable "Y")

def twoBinderTarget : Formula 0 :=
  .all <| .ex <| .equal (.bvar 1) (.bvar 0)

theorem distinct_binders_have_distinct_indices :
    resolveClosedFormula? twoBinderSource = some twoBinderTarget := by
  simp [resolveClosedFormula?, twoBinderSource, twoBinderTarget,
    resolveFormula?, resolveTerm?, lookupBinder?]

theorem free_variable_is_rejected :
    resolveClosedFormula? (.equal (.variable "X") (.variable "X")) = none := by
  simp [resolveClosedFormula?, resolveFormula?, resolveTerm?, lookupBinder?]

end Canary

#print axioms lookupBinder?_head
#print axioms Canary.shadowing_resolves_to_nearest_binder
#print axioms Canary.distinct_binders_have_distinct_indices
#print axioms Canary.free_variable_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution
