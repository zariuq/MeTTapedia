import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectPrograms

/-!
# The first specimen of the trinity curriculum: lists, their append, and its theorem

The source, written once:

    data num  : zero | suc num
    data list : nil  | cons num list

    append nil ys         = ys
    append (cons a as) ys = cons a (append as ys)

    theorem: for every list l, append l nil = l

`NumExpr` and `ListExpr` are the closed expressions of this source. The three faces read
them: the operational face runs them by the two equations, the intensional face types their
terms (`ListExpr.toTerm`) in the package of the program, and the extensional face reads them
as sets. Each face lives in its own module beside this one; this module fixes only the
expressions, their terms, and the steps the two equations allow (`ListExpr.Step`).

Positive example: `one ++ two` is an expression whose term is the application of `append`.
Negative example: a value has no `append` in it, and `one ++ two` is not a value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open CodeModel

/-- A closed number: a numeral. -/
inductive NumExpr where
  | zero
  | suc (n : NumExpr)
  deriving DecidableEq, Repr

/-- A closed list expression of the source. -/
inductive ListExpr where
  | nil
  | cons (head : NumExpr) (tail : ListExpr)
  | append (left right : ListExpr)
  deriving DecidableEq, Repr

/-- The term of a numeral. -/
def NumExpr.toTerm : NumExpr → CTm Tower.Head 0
  | .zero => czero
  | .suc n => csuc n.toTerm

/-- The term of a list expression, in the package of the program. -/
def ListExpr.toTerm : ListExpr → CTm Tower.Head 0
  | .nil => cnil
  | .cons head tail => ccons head.toTerm tail.toTerm
  | .append left right => cappend left.toTerm right.toTerm

/-- A value: a list expression built from `nil` and `cons` only. -/
def ListExpr.IsValue : ListExpr → Prop
  | .nil => True
  | .cons _ tail => tail.IsValue
  | .append _ _ => False

/-- **One step of the source**: an instance of one of the two equations, anywhere in a list
expression. The equations are part of the source, so every face reads the same steps. -/
inductive ListExpr.Step : ListExpr → ListExpr → Prop
  | appendNil (right : ListExpr) : Step (.append .nil right) right
  | appendCons (head : NumExpr) (tail right : ListExpr) :
      Step (.append (.cons head tail) right) (.cons head (.append tail right))
  | consTail {head : NumExpr} {tail tail' : ListExpr} :
      Step tail tail' → Step (.cons head tail) (.cons head tail')
  | appendLeft {left left' right : ListExpr} :
      Step left left' → Step (.append left right) (.append left' right)
  | appendRight {left right right' : ListExpr} :
      Step right right' → Step (.append left right) (.append left right')

/-- The list of one number. -/
abbrev one : ListExpr := .cons .zero .nil

/-- The list of another number. -/
abbrev two : ListExpr := .cons (.suc .zero) .nil

/-- Positive example: the term of `one ++ two` is the application of `append`. -/
example : (ListExpr.append one two).toTerm = cappend one.toTerm two.toTerm := rfl

/-- Positive example: `one` is a value. -/
example : one.IsValue := trivial

/-- Negative example: `one ++ two` is not a value. -/
example : ¬ (ListExpr.append one two).IsValue := fun impossible => impossible

/-- Positive example: `one ++ two` takes a step by the second equation. -/
example : ListExpr.Step (.append one two) (.cons .zero (.append .nil two)) :=
  .appendCons .zero .nil two

/-- Negative example: the empty list takes no step. -/
example (target : ListExpr) : ¬ ListExpr.Step .nil target := fun step => nomatch step

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append
