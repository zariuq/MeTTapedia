import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorClassifying
import Mettapedia.Languages.LambdaCalculus.NamePassingPresentation

/-!
# Open name-passing trees in the generated closed constructor category

Every mixed reference/term context is interpreted by its actual ordered
product. Variables retain their supplied positions. A reference binder is
encoded by categorical abstraction after exchanging the context and new
reference; the stored value of a definition remains outside that binder.

The independently typed raw arrow retains all products, projections and
abstraction annotations. It gives a quotient arrow only after its genuine
generated admission tree has been constructed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorSyntax

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open Mettapedia.OSLF.Binding
open NamePassingConstructorClassifying

open Mettapedia.Languages.LambdaCalculus

universe v

def sortObject : NamePassing.Presentation.Srt → GeneratedCategory.Object signature.{v}
  | .nm => nameObject
  | .tm => termObject

def contextObject : Ctx NamePassing.Presentation.signature → GeneratedCategory.Object signature.{v}
  | [] => GeneratedCategory.terminal signature
  | sort :: context => GeneratedCategory.product (sortObject sort) (contextObject context)

def compose {first middle last : GeneratedCategory.Object signature.{v}}
    (before : GeneratedCategory.RawHom first middle) (after : GeneratedCategory.RawHom middle last) : GeneratedCategory.RawHom first last :=
  ⟨.compose before.code after.code, ⟨.compose before.admitted.some after.admitted.some⟩⟩

def pair {source left right : GeneratedCategory.Object signature.{v}}
    (first : GeneratedCategory.RawHom source left) (second : GeneratedCategory.RawHom source right) :
    GeneratedCategory.RawHom source (GeneratedCategory.product left right) :=
  ⟨.pair first.code second.code, ⟨.pair first.admitted.some second.admitted.some⟩⟩

def first (left right : GeneratedCategory.Object signature.{v}) : GeneratedCategory.RawHom (GeneratedCategory.product left right) left :=
  ⟨.first left.code right.code, ⟨.first left.formed.some right.formed.some⟩⟩

def second (left right : GeneratedCategory.Object signature.{v}) : GeneratedCategory.RawHom (GeneratedCategory.product left right) right :=
  ⟨.second left.code right.code, ⟨.second left.formed.some right.formed.some⟩⟩

def exchange (left right : GeneratedCategory.Object signature.{v}) :
    GeneratedCategory.RawHom (GeneratedCategory.product left right) (GeneratedCategory.product right left) :=
  pair (second left right) (first left right)

def abstract {context argument result : GeneratedCategory.Object signature.{v}}
    (body : GeneratedCategory.RawHom (GeneratedCategory.product context argument) result) :
    GeneratedCategory.RawHom context (GeneratedCategory.exponentialObject argument result) :=
  ⟨.curry context.code argument.code result.code body.code,
    ⟨.curry context.formed.some argument.formed.some result.formed.some body.admitted.some⟩⟩

def projection : {context : Ctx NamePassing.Presentation.signature} → {sort : NamePassing.Presentation.Srt} →
    Var context sort → GeneratedCategory.RawHom (contextObject.{v} context) (sortObject sort)
  | _ :: context, _, .zero => first _ (contextObject context)
  | old :: context, _, .succ position =>
      compose (second (sortObject old) (contextObject context)) (projection position)

def name {context : Ctx NamePassing.Presentation.signature} (term : NamePassing.Presentation.Name context) :
    GeneratedCategory.RawHom (contextObject.{v} context) nameObject :=
  projection (NamePassing.Presentation.nameVariable term)

def bindReference {context : Ctx NamePassing.Presentation.signature}
    (body : GeneratedCategory.RawHom (contextObject.{v} (.nm :: context)) termObject) :
    GeneratedCategory.RawHom (contextObject context) (GeneratedCategory.exponentialObject nameObject termObject) :=
  abstract (compose (exchange (contextObject context) nameObject) body)

def encode : {context : Ctx NamePassing.Presentation.signature} → NamePassing.Presentation.Program context →
    GeneratedCategory.RawHom (contextObject.{v} context) termObject
  | _, .var position => projection position
  | _, .op .reference (.cons reference .nil) =>
      compose (name reference) (constructorArrow .reference)
  | _, .op .abstraction (.cons body .nil) =>
      compose (bindReference (encode body)) (constructorArrow .abstraction)
  | _, .op .application (.cons function (.cons argument .nil)) =>
      compose (pair (encode function) (name argument)) (constructorArrow .application)
  | _, .op .definition (.cons value (.cons body .nil)) =>
      compose (pair (encode value) (bindReference (encode body))) (constructorArrow .definition)
  | _, .op .carrier (.cons reference (.cons value (.cons body .nil))) =>
      compose (pair (name reference) (pair (encode value) (encode body))) (constructorArrow .carrier)
termination_by _ term => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

def arrow {context : Ctx NamePassing.Presentation.signature} (term : NamePassing.Presentation.Program context) :
    contextObject.{v} context ⟶ termObject := GeneratedCategory.classOf (encode term)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorSyntax
