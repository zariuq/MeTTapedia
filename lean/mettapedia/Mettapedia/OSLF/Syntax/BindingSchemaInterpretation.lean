import Mettapedia.OSLF.Syntax.BindingEquationalModels

/-!
# Raw interpretation of binding equation schemas

Schema folds and their syntactic comparisons depend only on a binding clone.
They are independent of generated equation closure and its quotient.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationInterpretation

open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution
open Mettapedia.OSLF.Binding.BindingEquationalModels

universe u

variable {S : Signature} {M : List (MetaArity S)}

mutual

/-- Interpret an equation schema in a binding-clone model. -/
def interpretSchema (A : BindingCloneAlgebra.Algebra.{u} S)
    (valuation : MetaValuation A M) :
    {Γ : Ctx S} → {sort : S.Srt} →
      Term (withMetas S M) Γ sort → A.substitution.Carrier Γ sort
  | _, _, .var v => A.substitution.injectVar v
  | _, _, .op (Sum.inl op) args =>
      A.operation op (interpretSchemaArgs A valuation args)
  | _, _, .op (Sum.inr (.mk k)) args =>
      applyMeta A (valuation k) (interpretSchemaArgs A valuation args)

/-- Interpret every argument at exactly the context opened by its binder
list. The result is the base signature's semantic argument family. -/
def interpretSchemaArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    (valuation : MetaValuation A M) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args (withMetas S M) arity Γ →
      FamilyArgs S A.substitution.Carrier arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (interpretSchema A valuation head)
        (interpretSchemaArgs A valuation tail)

end


mutual

/-- Interpreting a schema with syntactic metavariable bodies agrees with
first instantiating that authored schema and then folding the resulting base
term into the semantic model. -/
theorem interpretSchema_instantiate
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (body : (k : Fin M.length) → Term S (M.get k).1 (M.get k).2) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (term : Term (withMetas S M) Γ sort),
      interpretSchema A (fun k => interpret A (body k)) term =
        interpret A (instantiate body term)
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl op) args => by
      change A.operation op
          (interpretSchemaArgs A (fun k => interpret A (body k)) args) =
        A.operation op (interpretArgs A (instantiateArgs body args))
      exact congrArg (A.operation op)
        (interpretSchemaArgs_instantiate A body args)
  | _, _, .op (Sum.inr (.mk k)) args => by
      change A.substitution.substitute
          (argsEnvironment A
            (interpretSchemaArgs A (fun k => interpret A (body k)) args))
          (interpret A (body k)) =
        interpret A (bind (argsToSub (instantiateArgs body args)) (body k))
      rw [interpret_bind]
      congr 1
      funext sort x
      exact interpretSchemaArgs_metaEnvironment A body args sort x
termination_by _ _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize]
  all_goals omega

/-- The argument-vector comparison holds at every operator arity and every
binder-extended context. -/
theorem interpretSchemaArgs_instantiate
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (body : (k : Fin M.length) → Term S (M.get k).1 (M.get k).2) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S M) arity Γ),
      interpretSchemaArgs A (fun k => interpret A (body k)) args =
        interpretArgs A (instantiateArgs body args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg₂ FamilyArgs.cons
        (interpretSchema_instantiate A body head)
        (interpretSchemaArgs_instantiate A body tail)
termination_by _ _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

/-- A metavariable's interpreted argument environment agrees pointwise
with the syntactic argument substitution after schema instantiation. -/
theorem interpretSchemaArgs_metaEnvironment
    (A : BindingCloneAlgebra.Algebra.{u} S)
    (body : (k : Fin M.length) → Term S (M.get k).1 (M.get k).2) :
    ∀ {bs : List S.Srt} {Γ : Ctx S}
      (args : Args (withMetas S M)
        (bs.map (fun b => ([], b))) Γ)
      (sort : S.Srt) (x : Var bs sort),
      argsEnvironment A
        (interpretSchemaArgs A (fun k => interpret A (body k)) args)
        sort x =
      interpret A (argsToSub (instantiateArgs body args) sort x)
  | [], _, .nil, _, x => nomatch x
  | _ :: _, _, .cons head _tail, _, .zero => by
      exact interpretSchema_instantiate A body head
  | _ :: _, _, .cons _head tail, sort, .succ old =>
      interpretSchemaArgs_metaEnvironment A body tail sort old
termination_by _ _ args _ _ => 2 * argsSize args + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos _head; omega

end

end Mettapedia.OSLF.Binding.BindingEquationInterpretation
