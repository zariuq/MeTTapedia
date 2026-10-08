import Mettapedia.OSLF.Syntax.BindingClosedTerms

/-!
# Independently typed equation-schema expressions

Schema metavariables are projections from the product of their actual
function objects. Application evaluates that function on the complete
ordered dependency tuple. Ordinary variables have a separate supplied
environment. Entering a binding argument extends that environment and
restages the complete metavariable tuple.

All expressions are constructed in the original binding constructor
presentation. Metavariables are not adjoined as unconstrained primitive
operators, and the encoder does not consult a semantic model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.SchemaExpressions

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory (RawHom Object product exponentialObject)

universe v

variable (binding : Mettapedia.OSLF.Binding.Signature)

abbrev Environment (stage : Object (signature.{v} binding)) (context : Ctx binding) :=
  (sort : binding.Srt) → Var context sort → RawHom stage (sortObject binding sort)

def extendEnvironment {stage : Object (signature.{v} binding)} :
    (binders : Ctx binding) → {context : Ctx binding} →
      Environment binding stage context →
        Environment binding (product (contextObject binding binders) stage) (binders ++ context)
  | [], _, environment => fun sort position =>
      RawHom.compose (RawHom.second _ _) (environment sort position)
  | head :: binders, _, environment => fun sort position => match position with
    | .zero => RawHom.compose (RawHom.first _ _)
        (RawHom.first (sortObject binding head) (contextObject binding binders))
    | .succ old => RawHom.compose
        (RawHom.pair
          (RawHom.compose (RawHom.first _ _)
            (RawHom.second (sortObject binding head) (contextObject binding binders)))
          (RawHom.second _ _))
        (extendEnvironment binders environment sort old)

def familyProjection : (arities : List (MetaArity binding)) → (index : Fin arities.length) →
    RawHom (familyObject.{v} binding arities)
      (powerObject binding (arities.get index).1 (arities.get index).2)
  | arity :: rest, ⟨0, _⟩ =>
      RawHom.first (powerObject binding arity.1 arity.2) (familyObject binding rest)
  | arity :: rest, ⟨n + 1, bound⟩ =>
      RawHom.compose (RawHom.second (powerObject binding arity.1 arity.2) (familyObject binding rest))
        (familyProjection rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

def evaluation (argument result : Object (signature.{v} binding)) :
    RawHom (product (exponentialObject argument result) argument) result :=
  ⟨.evaluation argument.code result.code,
    ⟨.evaluation argument.formed.some result.formed.some⟩⟩

def applyFunction {stage argument result : Object (signature.{v} binding)}
    (function : RawHom stage (exponentialObject argument result))
    (value : RawHom stage argument) : RawHom stage result :=
  RawHom.compose (RawHom.pair function value) (evaluation binding argument result)

variable {metavariables : List (MetaArity binding)}

mutual

def encode {stage : Object (signature.{v} binding)}
    (metas : RawHom stage (familyObject binding metavariables)) :
    {context : Ctx binding} → {sort : binding.Srt} →
    Environment binding stage context → Term (withMetas binding metavariables) context sort →
      RawHom stage (sortObject binding sort)
  | _, _, environment, .var position => environment _ position
  | _, _, environment, .op (Sum.inl operation) arguments =>
      RawHom.compose (encodeArgs metas environment arguments) (operator binding operation)
  | _, _, environment, .op (Sum.inr (.mk index)) arguments =>
      applyFunction binding
        (argument := contextObject binding (metavariables.get index).1)
        (result := sortObject binding (metavariables.get index).2)
        (RawHom.compose metas (familyProjection binding metavariables index))
        (encodeMetaArgs metas (metavariables.get index).1 environment arguments)
termination_by _ _ _ term => 2 * termSize term
decreasing_by all_goals simp only [termSize]; omega

def encodeArgs {stage : Object (signature.{v} binding)}
    (metas : RawHom stage (familyObject binding metavariables)) :
    {context : Ctx binding} → {arities : List (MetaArity binding)} →
    Environment binding stage context → Args (withMetas binding metavariables) arities context →
      RawHom stage (familyObject binding arities)
  | _, _, _, .nil => RawHom.toTerminal _
  | _, _, environment, .cons (bs := binders) body rest =>
      RawHom.pair
        (RawHom.curry (encode
          (RawHom.compose (RawHom.second (contextObject binding binders) _) metas)
          (extendEnvironment binding binders environment) body))
        (encodeArgs metas environment rest)
termination_by _ _ _ arguments => 2 * argsSize arguments + 1
decreasing_by all_goals simp only [argsSize]; have := termSize_pos body; omega

def encodeMetaArgs {stage : Object (signature.{v} binding)}
    (metas : RawHom stage (familyObject binding metavariables)) :
    (dependencies : Ctx binding) → {context : Ctx binding} →
    Environment binding stage context →
      Args (withMetas binding metavariables) (dependencies.map (fun sort => ([], sort))) context →
        RawHom stage (contextObject binding dependencies)
  | [], _, _, .nil => RawHom.toTerminal _
  | _ :: dependencies, _, environment, .cons head rest =>
      RawHom.pair (encode metas environment head)
        (encodeMetaArgs metas dependencies environment rest)
termination_by _ _ _ arguments => 2 * argsSize arguments + 1
decreasing_by all_goals simp only [argsSize]; have := termSize_pos head; omega

end

def genericStage (metavariables : List (MetaArity binding)) (context : Ctx binding) :
    Object (signature.{v} binding) :=
  product (contextObject binding context) (familyObject binding metavariables)

def genericMetas (metavariables : List (MetaArity binding)) (context : Ctx binding) :
    RawHom (genericStage.{v} binding metavariables context) (familyObject binding metavariables) :=
  RawHom.second _ _

def genericEnvironment (metavariables : List (MetaArity binding)) (context : Ctx binding) :
    Environment binding (genericStage.{v} binding metavariables context) context :=
  fun _ position => RawHom.compose (RawHom.first _ _) (projection binding position)

def expression {context : Ctx binding} {sort : binding.Srt}
    (term : Term (withMetas binding metavariables) context sort) :
    RawHom (genericStage.{v} binding metavariables context) (sortObject binding sort) :=
  encode binding (genericMetas binding metavariables context)
    (genericEnvironment binding metavariables context) term

end Mettapedia.OSLF.Binding.ClosedPresentation.SchemaExpressions
