import Mettapedia.OSLF.Syntax.BindingClosedPresentation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperations

/-!
# Independently admitted open binding terms in the free closed presentation

The encoder constructs raw products, projections and annotated abstractions.
An arbitrary binder list is joined to the ambient context by a recursively
constructed ordered product arrow. Every supplied variable position remains
explicit; equal sorts do not allow newly bound variables to be exchanged.

Nullary operators and unbound arguments use their actual terminal and
function headers. They are not assigned dummy values or erased premises.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory (RawHom)

universe v

variable (binding : Mettapedia.OSLF.Binding.Signature)

def projection : {context : Ctx binding} → {sort : binding.Srt} →
    Var context sort → RawHom (contextObject.{v} binding context) (sortObject binding sort)
  | sort :: context, _, .zero => RawHom.first (sortObject binding sort) (contextObject binding context)
  | old :: context, _, .succ position =>
      RawHom.compose (RawHom.second (sortObject binding old) (contextObject binding context))
        (projection position)

def contextAppend : (before after : Ctx binding) →
    RawHom (GeneratedCategory.product (contextObject.{v} binding before) (contextObject binding after))
      (contextObject binding (before ++ after))
  | [], after => RawHom.second _ (contextObject binding after)
  | sort :: before, after =>
      RawHom.pair
        (RawHom.compose (RawHom.first _ (contextObject binding after))
          (RawHom.first (sortObject binding sort) (contextObject binding before)))
        (RawHom.compose
          (RawHom.pair
            (RawHom.compose (RawHom.first _ (contextObject binding after))
              (RawHom.second (sortObject binding sort) (contextObject binding before)))
            (RawHom.second _ (contextObject binding after)))
          (contextAppend before after))

def bindBody {context binders : Ctx binding} {sort : binding.Srt}
    (body : RawHom (contextObject.{v} binding (binders ++ context)) (sortObject binding sort)) :
    RawHom (contextObject binding context) (powerObject binding binders sort) :=
  RawHom.curry (RawHom.compose (contextAppend binding binders context) body)

mutual

def encode : {context : Ctx binding} → {sort : binding.Srt} → Term binding context sort →
    RawHom (contextObject.{v} binding context) (sortObject binding sort)
  | _, _, .var position => projection binding position
  | _, _, .op operation arguments =>
      RawHom.compose (encodeArgs arguments) (operator binding operation)

def encodeArgs : {context : Ctx binding} → {arities : List (Ctx binding × binding.Srt)} →
    Args binding arities context → RawHom (contextObject.{v} binding context) (familyObject binding arities)
  | context, _, .nil => RawHom.toTerminal (contextObject binding context)
  | _, _, .cons body rest => RawHom.pair (bindBody binding (encode body)) (encodeArgs rest)

end

def termArrow {context : Ctx binding} {sort : binding.Srt} (term : Term binding context sort) :
    contextObject.{v} binding context ⟶ sortObject binding sort :=
  GeneratedCategory.classOf (encode binding term)

end Mettapedia.OSLF.Binding.ClosedPresentation
