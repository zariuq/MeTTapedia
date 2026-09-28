import Mettapedia.OSLF.Syntax.BindingEquationInterpretation

/-!
# Naturality of authored binding schemas

An equation or rule schema may apply a metavariable to terms in its declared
dependency context. Interpreting that application uses semantic simultaneous
substitution. This file proves that binding-clone morphisms preserve the whole
interpretation, including arguments beneath operator binders and an ordinary
closing substitution. It supplies the endpoint law needed by operational
rule actions over equation models.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationInterpretation

open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingEquationalModels

universe u v w

variable {S : Signature} {M : List (MetaArity S)}

/-- Map a semantic metavariable assignment along a binding-clone morphism. -/
def mapMetaValuation {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (valuation : MetaValuation A M) :
    MetaValuation B M :=
  fun k => h.raw.map (valuation k)

/-- Identity model interpretation leaves every declared metavariable body
unchanged, including its dependency context. -/
theorem mapMetaValuation_id (A : BindingCloneAlgebra.Algebra.{u} S)
    (valuation : MetaValuation A M) :
    mapMetaValuation (FreeBindingClone.Hom.id A) valuation = valuation := rfl

/-- Transporting semantic metavariables through two model maps agrees with
transporting through their composite. -/
theorem mapMetaValuation_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    {C : BindingCloneAlgebra.Algebra.{w} S}
    (f : FreeBindingClone.Hom A B) (g : FreeBindingClone.Hom B C)
    (valuation : MetaValuation A M) :
    mapMetaValuation (FreeBindingClone.Hom.comp f g) valuation =
      mapMetaValuation g (mapMetaValuation f valuation) := rfl

/-- The environment represented by a metavariable's argument vector is
preserved pointwise by a model morphism. -/
theorem argsEnvironment_map {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) :
    ∀ {bs : List S.Srt} {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier
        (bs.map (fun b => ([], b))) Γ)
      (sort : S.Srt) (x : Var bs sort),
      argsEnvironment B (FamilyArgs.map h.raw.map args) sort x =
        h.raw.map (argsEnvironment A args sort x)
  | [], _, .nil, _, x => nomatch x
  | _ :: _, _, .cons _head _tail, _, .zero => rfl
  | _ :: _, _, .cons _head tail, sort, .succ old =>
      argsEnvironment_map h tail sort old

/-- Metavariable application commutes with a binding-clone morphism. -/
theorem applyMeta_map {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {bs : List S.Srt} {sort : S.Srt}
    (body : A.substitution.Carrier bs sort)
    {Γ : Ctx S}
    (args : FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) Γ) :
    h.raw.map (applyMeta A body args) =
      applyMeta B (h.raw.map body) (FamilyArgs.map h.raw.map args) := by
  unfold applyMeta
  rw [h.map_substitute]
  congr 1
  funext s x
  exact (argsEnvironment_map h args s x).symm

mutual

/-- The interpretation of an authored schema is natural in its semantic
binding-clone model. This includes all metavariable occurrences. -/
theorem interpretSchema_map {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (valuation : MetaValuation A M) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (term : Term (withMetas S M) Γ sort),
      h.raw.map (interpretSchema A valuation term) =
        interpretSchema B (mapMetaValuation h valuation) term
  | _, _, .var x => h.raw.map_variable x
  | _, _, .op (Sum.inl op) args => by
      change h.raw.map
        (A.operation op (interpretSchemaArgs A valuation args)) =
          B.operation op
            (interpretSchemaArgs B (mapMetaValuation h valuation) args)
      exact (h.raw.map_operation op
        (interpretSchemaArgs A valuation args)).trans
        (congrArg (B.operation op)
          (interpretSchemaArgs_map h valuation args))
  | _, _, .op (Sum.inr (.mk k)) args => by
      change h.raw.map
        (applyMeta A (valuation k) (interpretSchemaArgs A valuation args)) =
          applyMeta B (h.raw.map (valuation k))
            (interpretSchemaArgs B (mapMetaValuation h valuation) args)
      rw [applyMeta_map h]
      exact congrArg (applyMeta B (h.raw.map (valuation k)))
        (interpretSchemaArgs_map h valuation args)
termination_by _ _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize]
  all_goals omega

/-- Naturality extends componentwise to arbitrary sorted binder arguments. -/
theorem interpretSchemaArgs_map {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (valuation : MetaValuation A M) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S M) arity Γ),
      FamilyArgs.map h.raw.map (interpretSchemaArgs A valuation args) =
        interpretSchemaArgs B (mapMetaValuation h valuation) args
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ FamilyArgs.cons
        (interpretSchema_map h valuation head)
        (interpretSchemaArgs_map h valuation tail)
termination_by _ _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

/-- The same law holds after closing the schema's ordinary variables with a
semantic environment. This is the rule-endpoint transport law. -/
theorem interpretSchema_closed_map {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (valuation : MetaValuation A M)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (env : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier Γ Δ)
    (term : Term (withMetas S M) Γ sort) :
    h.raw.map (A.substitution.substitute env
      (interpretSchema A valuation term)) =
      B.substitution.substitute (fun s x => h.raw.map (env s x))
        (interpretSchema B (mapMetaValuation h valuation) term) := by
  rw [h.map_substitute, interpretSchema_map]

/-- Each authored equation instance remains valid after transporting all its
semantic metavariables and ordinary variables along a model morphism. This
is an image statement; it does not assert that an arbitrary target
valuation factors through the morphism. -/
theorem mapped_equation_instance
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {E : List (EqAxiom S M)} (satisfies : Satisfies A E)
    (i : Fin E.length) (valuation : MetaValuation A M)
    {Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier (E.get i).ctx Δ) :
    B.substitution.substitute (fun s x => h.raw.map (env s x))
      (interpretSchema B (mapMetaValuation h valuation) (E.get i).lhs) =
    B.substitution.substitute (fun s x => h.raw.map (env s x))
      (interpretSchema B (mapMetaValuation h valuation) (E.get i).rhs) := by
  exact (interpretSchema_closed_map h valuation env (E.get i).lhs).symm.trans
    ((congrArg h.raw.map (satisfies i valuation env)).trans
      (interpretSchema_closed_map h valuation env (E.get i).rhs))

/-- Every positioned authored rewrite has natural semantic endpoints. Its
selected position remains separate data: equality of endpoint values does
not determine which occurrence fired. -/
theorem positionedRewrite_endpoints_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) (valuation : MetaValuation A M)
    (rule : PositionedRewrite (withMetas S M))
    {Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier rule.ctx Δ) :
    h.raw.map (A.substitution.substitute env
      (interpretSchema A valuation rule.lhs)) =
        B.substitution.substitute (fun s x => h.raw.map (env s x))
          (interpretSchema B (mapMetaValuation h valuation) rule.lhs) ∧
    h.raw.map (A.substitution.substitute env
      (interpretSchema A valuation rule.rhs)) =
        B.substitution.substitute (fun s x => h.raw.map (env s x))
          (interpretSchema B (mapMetaValuation h valuation) rule.rhs) := by
  exact ⟨interpretSchema_closed_map h valuation env rule.lhs,
    interpretSchema_closed_map h valuation env rule.rhs⟩

#print axioms argsEnvironment_map
#print axioms applyMeta_map
#print axioms interpretSchema_map
#print axioms interpretSchemaArgs_map
#print axioms interpretSchema_closed_map
#print axioms mapped_equation_instance
#print axioms positionedRewrite_endpoints_map

end Mettapedia.OSLF.Binding.BindingEquationInterpretation
