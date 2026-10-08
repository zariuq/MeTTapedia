import Mettapedia.OSLF.Syntax.BindingClosedPresentation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperationReadout
import Mettapedia.Languages.LambdaCalculus.NamePassingPresentation

/-!
# Independent ordinary constructor expressions in the source guest

Values and terms are separate declared objects. Empty-binder arguments are
formed by currying the second projection. A complete one-value body is
applied to the first coordinate of the padded binder context. The five
expressions then supply precisely the ordered binding-operator arguments.
No continuation object or operational target is used in their construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedConstructorExpressions

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

universe k

abbrev binding := NamePassing.Presentation.signature
abbrev signature := ClosedPresentation.signature.{k} binding
abbrev Guest := Object signature.{k}
def names : Guest.{k} := ClosedPresentation.sortObject binding .nm
def terms : Guest.{k} := ClosedPresentation.sortObject binding .tm
def bodies : Guest.{k} := exponentialObject names terms

def plain (sort : NamePassing.Presentation.Srt) : RawHom
    (ClosedPresentation.sortObject.{k} binding sort)
    (ClosedPresentation.powerObject binding [] sort) :=
  RawHom.curry (RawHom.second (terminal signature) (ClosedPresentation.sortObject binding sort))

def bound : RawHom bodies.{k} (ClosedPresentation.powerObject binding [.nm] .tm) :=
  RawHom.curry (Interpretation.RawHom.applyFunction
    (RawHom.second (product names (terminal signature)) bodies)
    (RawHom.compose (RawHom.first (product names (terminal signature)) bodies)
      (RawHom.first names (terminal signature))))

def reference : RawHom names.{k} terms :=
  RawHom.compose (RawHom.pair (plain .nm) (RawHom.toTerminal names))
    (ClosedPresentation.operator binding .reference)

def abstraction : RawHom bodies.{k} terms :=
  RawHom.compose (RawHom.pair bound (RawHom.toTerminal bodies))
    (ClosedPresentation.operator binding .abstraction)

def application : RawHom (product terms.{k} names) terms :=
  RawHom.compose
    (RawHom.pair (RawHom.compose (RawHom.first terms names) (plain .tm))
      (RawHom.pair (RawHom.compose (RawHom.second terms names) (plain .nm))
        (RawHom.toTerminal (product terms names))))
    (ClosedPresentation.operator binding .application)

def definition : RawHom (product terms.{k} bodies) terms :=
  RawHom.compose
    (RawHom.pair (RawHom.compose (RawHom.first terms bodies) (plain .tm))
      (RawHom.pair (RawHom.compose (RawHom.second terms bodies) bound)
        (RawHom.toTerminal (product terms bodies))))
    (ClosedPresentation.operator binding .definition)

def carrier : RawHom (product names.{k} (product terms terms)) terms :=
  RawHom.compose
    (RawHom.pair (RawHom.compose (RawHom.first names (product terms terms)) (plain .nm))
      (RawHom.pair
        (RawHom.compose (RawHom.compose (RawHom.second names (product terms terms))
          (RawHom.first terms terms)) (plain .tm))
        (RawHom.pair
          (RawHom.compose (RawHom.compose (RawHom.second names (product terms terms))
            (RawHom.second terms terms)) (plain .tm))
          (RawHom.toTerminal (product names (product terms terms))))))
    (ClosedPresentation.operator binding .carrier)

def domain : NamePassing.Presentation.Operator .tm → Guest.{k}
  | .reference => names
  | .abstraction => bodies
  | .application => product terms names
  | .definition => product terms bodies
  | .carrier => product names (product terms terms)

def expression : (operator : NamePassing.Presentation.Operator .tm) → RawHom (domain.{k} operator) terms
  | .reference => reference
  | .abstraction => abstraction
  | .application => application
  | .definition => definition
  | .carrier => carrier

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedConstructorExpressions
