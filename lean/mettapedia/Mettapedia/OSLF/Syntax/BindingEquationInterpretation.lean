import Mettapedia.OSLF.Syntax.BindingEquationalModels
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Interpreting authored binding equation schemas

The equation schema signature has the base operators and explicitly declared
metavariables. Its interpretation sends each metavariable occurrence to
semantic substitution of the corresponding value in its dependency context.
The argument fold preserves the binder contexts on every base operator.
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

/-- An equation model satisfies every authored schema under every semantic
metavariable valuation and every semantic environment for its ordinary
variables. -/
def Satisfies (A : BindingCloneAlgebra.Algebra.{u} S)
    (E : List (EqAxiom S M)) : Prop :=
  ∀ (i : Fin E.length) (valuation : MetaValuation A M)
    {Γ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier (E.get i).ctx Γ),
    A.substitution.substitute env
      (interpretSchema A valuation (E.get i).lhs) =
    A.substitution.substitute env
      (interpretSchema A valuation (E.get i).rhs)

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

mutual

/-- Every semantic equation model identifies all pairs in the generated
syntactic congruence, including instances beneath binders. -/
theorem interpret_eqClosure
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      {left right : Term S Γ sort}, EqClosure E left right →
      interpret A left = interpret A right
  | _, _, _, _, .ax i body close => by
      rw [interpret_bind, interpret_bind]
      rw [← interpretSchema_instantiate A body (E.get i).lhs,
        ← interpretSchema_instantiate A body (E.get i).rhs]
      exact satisfies i (fun k => interpret A (body k))
        (fun s v => interpret A (close s v))
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (interpret_eqClosure A satisfies h).symm
  | _, _, _, _, .trans h h' =>
      (interpret_eqClosure A satisfies h).trans
        (interpret_eqClosure A satisfies h')
  | _, _, _, _, .cong op argsEq => by
      change A.operation op (interpretArgs A _) =
        A.operation op (interpretArgs A _)
      exact congrArg (A.operation op)
        (interpretArgs_eqArgs A satisfies argsEq)

/-- The congruence induction follows every argument into the binder context
declared for that argument. -/
theorem interpretArgs_eqArgs
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {left right : Args S arity Γ}, EqArgs E left right →
      interpretArgs A left = interpretArgs A right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons headEq tailEq =>
      congrArg₂ FamilyArgs.cons
        (interpret_eqClosure A satisfies headEq)
        (interpretArgs_eqArgs A satisfies tailEq)

end

/-- A model of the authored equations receives a well-defined
interpretation from every context-and-sort fibre of the existing syntactic
equation quotient. -/
def interpretQuotient
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    {Γ : Ctx S} {sort : S.Srt} :
    TermQ E Γ sort → A.substitution.Carrier Γ sort :=
  Quotient.lift (interpret A)
    (fun _ _ h => interpret_eqClosure A satisfies h)

theorem interpretQuotient_mk
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    interpretQuotient A satisfies (Quotient.mk _ term) =
      interpret A term := rfl

/-- The quotient interpretation commutes with the repository's quotient
substitution by a syntactic environment. -/
theorem interpretQuotient_bindQ
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (sigma : Sub S Γ Δ) (q : TermQ E Γ sort) :
    interpretQuotient A satisfies (bindQ (E := E) sigma q) =
      A.substitution.substitute
        (fun s v => interpret A (sigma s v))
        (interpretQuotient A satisfies q) := by
  induction q using Quotient.inductionOn with
  | _ term => exact interpret_bind A sigma term

/-- Any family of maps out of the quotient that agrees with the term fold on
representatives agrees with this factorization everywhere. -/
theorem interpretQuotient_unique
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    {Γ : Ctx S} {sort : S.Srt}
    (map : TermQ E Γ sort → A.substitution.Carrier Γ sort)
    (onTerms : ∀ term : Term S Γ sort,
      map (Quotient.mk _ term) = interpret A term) :
    map = interpretQuotient A satisfies := by
  funext q
  induction q using Quotient.inductionOn with
  | _ term => exact onTerms term

end Mettapedia.OSLF.Binding.BindingEquationInterpretation
