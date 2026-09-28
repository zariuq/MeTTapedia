import Mettapedia.OSLF.Syntax.SemanticSchemaNaturality
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment

/-!
# Semantic metavariables with ambient context

A metavariable value can depend on both its declared arguments and the
ambient context where it was captured. These are separate context blocks.
Applying the value supplies both environments at once. The construction is
defined for any semantic binding clone and agrees with the established
syntactic contextual assignment when that clone is the term model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SemanticContextualMetavariables

open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingEquationalModels

universe u v

variable {S : Signature} {M : List (MetaArity S)}

/-- A metavariable has its declared dependency prefix followed by the
ambient variables in scope when its value was obtained. -/
abbrev Valuation (A : BindingCloneAlgebra.Algebra.{u} S)
    (Γ : Ctx S) : Type u :=
  (k : Fin M.length) →
    A.substitution.Carrier ((M.get k).1 ++ Γ) (M.get k).2

/-- Join independently supplied dependency and ambient environments.
This construction works for any context-indexed carrier family. -/
def joinEnvironment {F : Ctx S → S.Srt → Type u} :
    {dependencies Γ Δ : Ctx S} →
      Environment S F dependencies Δ → Environment S F Γ Δ →
      Environment S F (dependencies ++ Γ) Δ
  | [], _, _, _, ambient => ambient
  | _ :: _, _, _, arguments, ambient => fun _ var =>
      match var with
      | .zero => arguments _ .zero
      | .succ old => joinEnvironment
          (fun s v => arguments s (.succ v)) ambient _ old

/-- The semantic environment join recovers the established syntactic
contextual-assignment join exactly on the term carrier. -/
theorem joinEnvironment_terms {Γ Δ : Ctx S} :
    ∀ (dependencies : Ctx S)
      (arguments : Sub S dependencies Δ) (ambient : Sub S Γ Δ),
      joinEnvironment arguments ambient =
        ContextualAssignment.joinSub arguments ambient
  | [], _, _ => rfl
  | _ :: dependencies, arguments, ambient => by
      funext sort var
      cases var with
      | zero => rfl
      | succ old =>
          exact congrFun (congrFun
            (joinEnvironment_terms dependencies
              (fun s v => arguments s (.succ v)) ambient) sort) old

/-- Substitute both dependency arguments and ambient values into one
contextual metavariable body. -/
def apply (A : BindingCloneAlgebra.Algebra.{u} S)
    {dependencies Γ Δ : Ctx S} {sort : S.Srt}
    (body : A.substitution.Carrier (dependencies ++ Γ) sort)
    (arguments : Environment S A.substitution.Carrier dependencies Δ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    A.substitution.Carrier Δ sort :=
  A.substitution.substitute (joinEnvironment arguments ambient) body

/-- Semantic contextual application specializes exactly to the existing
capture-avoiding application of a syntactic contextual assignment. -/
theorem apply_terms {Γ Δ : Ctx S}
    (body : ContextualAssignment S M Γ)
    (k : Fin M.length)
    (arguments : Sub S (M.get k).1 Δ) (ambient : Sub S Γ Δ) :
    apply (BindingCloneAlgebra.terms S) (body k) arguments ambient =
      ContextualAssignment.apply body k arguments ambient := by
  change bind (joinEnvironment arguments ambient) (body k) =
    bind (ContextualAssignment.joinSub arguments ambient) (body k)
  exact congrArg (fun env => bind env (body k))
    (joinEnvironment_terms (M.get k).1 arguments ambient)

/-- Contextual metavariable values map pointwise across a binding-clone
morphism, retaining both context blocks. -/
def mapValuation {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B) {Γ : Ctx S}
    (valuation : Valuation (M := M) A Γ) : Valuation (M := M) B Γ :=
  fun k => h.raw.map (valuation k)

/-- Mapping a joined environment agrees with joining the mapped parts. -/
theorem joinEnvironment_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {Γ Δ : Ctx S} :
    ∀ (dependencies : Ctx S)
      (arguments : Environment S A.substitution.Carrier dependencies Δ)
      (ambient : Environment S A.substitution.Carrier Γ Δ)
      (sort : S.Srt) (var : Var (dependencies ++ Γ) sort),
      joinEnvironment
          (fun s x => h.raw.map (arguments s x))
          (fun s x => h.raw.map (ambient s x)) sort var =
        h.raw.map (joinEnvironment arguments ambient sort var)
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, _, .zero => rfl
  | _ :: dependencies, arguments, ambient, sort, .succ old =>
      joinEnvironment_map h dependencies
        (fun s x => arguments s (.succ x)) ambient sort old

/-- Contextual metavariable application is natural under arbitrary
binding-clone morphisms, including ambient-dependent open bodies. -/
theorem apply_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {dependencies Γ Δ : Ctx S} {sort : S.Srt}
    (body : A.substitution.Carrier (dependencies ++ Γ) sort)
    (arguments : Environment S A.substitution.Carrier dependencies Δ)
    (ambient : Environment S A.substitution.Carrier Γ Δ) :
    h.raw.map (apply A body arguments ambient) =
      apply B (h.raw.map body)
        (fun s x => h.raw.map (arguments s x))
        (fun s x => h.raw.map (ambient s x)) := by
  unfold apply
  rw [h.map_substitute]
  congr 1
  funext s x
  exact (joinEnvironment_map h dependencies arguments ambient s x).symm

/-- Weaken the values of an ambient environment past a newly opened binder
list while leaving its source context unchanged. -/
def weakenEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    (binders : Ctx S) {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ) :
    Environment S A.substitution.Carrier Γ (binders ++ Δ) :=
  fun s x => A.substitution.substitute
    (fun _s v => A.substitution.injectVar (weakenVar binders v)) (env s x)

/-- On actual terms, semantic weakening is the established contextual
assignment's `weakenSub`. -/
theorem weakenEnvironment_terms (binders : Ctx S)
    {Γ Δ : Ctx S} (env : Sub S Γ Δ) :
    weakenEnvironment (BindingCloneAlgebra.terms S) binders env =
      ContextualAssignment.weakenSub binders env := by
  funext s x
  change bind (fun s v => Term.var (weakenVar binders v)) (env s x) =
    rename (fun s v => weakenVar binders v) (env s x)
  exact bind_var_eq_rename (fun s v => weakenVar binders v) (env s x)

/-- A model map preserves one-step semantic weakening. -/
theorem weaken_map {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {Γ : Ctx S} {sort fresh : S.Srt}
    (value : A.substitution.Carrier Γ sort) :
    h.raw.map (A.substitution.weaken (fresh := fresh) value) =
      B.substitution.weaken (h.raw.map value) := by
  unfold BindingSubstitutionAlgebra.Algebra.weaken
  rw [h.map_substitute]
  congr 1
  funext s x
  exact h.raw.map_variable (.succ x)

/-- Mapping an environment after semantic weakening agrees with weakening
its mapped values. -/
theorem weakenEnvironment_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    (binders : Ctx S) {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ) :
    (fun s x => h.raw.map (weakenEnvironment A binders env s x)) =
      weakenEnvironment B binders
        (fun s x => h.raw.map (env s x)) := by
  funext s x
  unfold weakenEnvironment
  rw [h.map_substitute]
  congr 1
  funext sort var
  exact h.raw.map_variable (weakenVar binders var)

/-- The binder lift of an ordinary semantic environment is natural in a
binding-clone model map. -/
theorem liftEnvironment_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ) :
    ∀ (binders : Ctx S),
      (fun s x => h.raw.map
        (A.substitution.liftEnvironment env binders s x)) =
        B.substitution.liftEnvironment
          (fun s x => h.raw.map (env s x)) binders
  | [] => rfl
  | _ :: binders => by
      funext s x
      cases x with
      | zero => exact h.raw.map_variable Var.zero
      | succ old =>
          change h.raw.map (A.substitution.weaken
              (A.substitution.liftEnvironment env binders _ old)) =
            B.substitution.weaken
              (B.substitution.liftEnvironment
                (fun s x => h.raw.map (env s x)) binders _ old)
          rw [weaken_map h]
          exact congrArg B.substitution.weaken
            (congrFun (congrFun (liftEnvironment_map h env binders) s) old)


mutual

/-- Interpret an authored schema with contextual metavariable bodies.
Ordinary rule variables and the ambient variables of captured bodies have
independent semantic environments. -/
def interpretSchema (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ : Ctx S}
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier Ξ Δ) :
    {sort : S.Srt} → Term (withMetas S M) Ξ sort →
      A.substitution.Carrier Δ sort
  | _, .var x => ordinary _ x
  | _, .op (Sum.inl op) args =>
      A.operation op (interpretArgs A body ambient ordinary args)
  | _, .op (Sum.inr (.mk k)) args =>
      apply A (body k)
        (argsEnvironment A (interpretArgs A body ambient ordinary args))
        ambient

/-- Every operator argument is interpreted under exactly its declared
binders, with the ambient and ordinary environments transported separately. -/
def interpretArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Ξ Δ : Ctx S}
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier Ξ Δ) :
    {arity : List (List S.Srt × S.Srt)} →
      Args (withMetas S M) arity Ξ →
      FamilyArgs S A.substitution.Carrier arity Δ
  | _, .nil => .nil
  | _, .cons (bs := binders) head tail =>
      .cons
        (interpretSchema A body (weakenEnvironment A binders ambient)
          (A.substitution.liftEnvironment ordinary binders) head)
        (interpretArgs A body ambient ordinary tail)

end

mutual

/-- Interpreting a contextual authored schema commutes with every
binding-clone morphism, including metavariable bodies that use ambient
variables beyond their declared dependency prefix. -/
theorem interpretSchema_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {Γ Ξ Δ : Ctx S}
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier Ξ Δ) :
    ∀ {sort : S.Srt} (term : Term (withMetas S M) Ξ sort),
      h.raw.map (interpretSchema A body ambient ordinary term) =
        interpretSchema B (mapValuation h body)
          (fun s x => h.raw.map (ambient s x))
          (fun s x => h.raw.map (ordinary s x)) term
  | _, .var _ => rfl
  | _, .op (Sum.inl op) args => by
      change h.raw.map
        (A.operation op (interpretArgs A body ambient ordinary args)) =
          B.operation op
            (interpretArgs B (mapValuation h body)
              (fun s x => h.raw.map (ambient s x))
              (fun s x => h.raw.map (ordinary s x)) args)
      exact (h.raw.map_operation op
        (interpretArgs A body ambient ordinary args)).trans
        (congrArg (B.operation op)
          (interpretArgs_map h body ambient ordinary args))
  | _, .op (Sum.inr (.mk k)) args => by
      change h.raw.map
        (apply A (body k)
          (argsEnvironment A (interpretArgs A body ambient ordinary args))
          ambient) =
        apply B (h.raw.map (body k))
          (argsEnvironment B
            (interpretArgs B (mapValuation h body)
              (fun s x => h.raw.map (ambient s x))
              (fun s x => h.raw.map (ordinary s x)) args))
          (fun s x => h.raw.map (ambient s x))
      rw [apply_map h]
      congr 1
      funext s x
      exact (BindingEquationInterpretation.argsEnvironment_map h
        (interpretArgs A body ambient ordinary args) s x).symm.trans
        (congrArg (fun values => argsEnvironment B values s x)
          (interpretArgs_map h body ambient ordinary args))
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

/-- Argument-vector naturality retains each argument's own binder list. -/
theorem interpretArgs_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {B : BindingCloneAlgebra.Algebra.{v} S}
    (h : FreeBindingClone.Hom A B)
    {Γ Ξ Δ : Ctx S}
    (body : Valuation (M := M) A Γ)
    (ambient : Environment S A.substitution.Carrier Γ Δ)
    (ordinary : Environment S A.substitution.Carrier Ξ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S M) arity Ξ),
      FamilyArgs.map h.raw.map (interpretArgs A body ambient ordinary args) =
        interpretArgs B (mapValuation h body)
          (fun s x => h.raw.map (ambient s x))
          (fun s x => h.raw.map (ordinary s x)) args
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      have headEq := interpretSchema_map h body
        (weakenEnvironment A binders ambient)
        (A.substitution.liftEnvironment ordinary binders) head
      rw [weakenEnvironment_map h binders ambient,
        liftEnvironment_map h ordinary binders] at headEq
      exact congrArg₂ FamilyArgs.cons headEq
        (interpretArgs_map h body ambient ordinary tail)
termination_by _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

/-- The semantic argument-environment reader agrees with the existing
syntactic argument-spine reader on every dependency context. -/
theorem argsEnvironment_syntaxToFamily :
    ∀ {dependencies : Ctx S} {Γ : Ctx S}
      (args : Args S (dependencies.map (fun b => ([], b))) Γ)
      (sort : S.Srt) (x : Var dependencies sort),
      argsEnvironment (BindingCloneAlgebra.terms S)
          (syntaxToFamily args) sort x = argsToSub args sort x
  | [], _, .nil, _, x => nomatch x
  | _ :: _, _, .cons _head _tail, _, .zero => rfl
  | _ :: _, _, .cons _head tail, sort, .succ old =>
      argsEnvironment_syntaxToFamily tail sort old

mutual

/-- On the actual term binding clone, the semantic contextual schema fold
recovers the repository's syntactic contextual instantiation exactly. -/
theorem interpretSchema_terms
    {Γ Ξ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S Ξ Δ) :
    ∀ {sort : S.Srt} (term : Term (withMetas S M) Ξ sort),
      interpretSchema (BindingCloneAlgebra.terms S) body ambient ordinary term =
        ContextualAssignment.instantiate body ambient ordinary term
  | _, .var _ => rfl
  | _, .op (Sum.inl op) args => by
      change Term.op op
        ((FreeBindingTerms.terms.familyToSyntax S)
          (interpretArgs (BindingCloneAlgebra.terms S) body ambient ordinary args)) =
        Term.op op (ContextualAssignment.instantiateArgs body ambient ordinary args)
      rw [interpretArgs_terms body ambient ordinary args]
      exact congrArg (Term.op op)
        (familyToSyntax_syntaxToFamily
          (ContextualAssignment.instantiateArgs body ambient ordinary args))
  | _, .op (Sum.inr (.mk k)) args => by
      change apply (BindingCloneAlgebra.terms S) (body k)
          (argsEnvironment (BindingCloneAlgebra.terms S)
            (interpretArgs (BindingCloneAlgebra.terms S) body ambient ordinary args))
          ambient =
        ContextualAssignment.apply body k
          (argsToSub (ContextualAssignment.instantiateArgs body ambient ordinary args))
          ambient
      rw [interpretArgs_terms body ambient ordinary args]
      have envEq := argsEnvironment_syntaxToFamily
        (ContextualAssignment.instantiateArgs body ambient ordinary args)
      have envEqFun :
          argsEnvironment (BindingCloneAlgebra.terms S)
            (syntaxToFamily
              (ContextualAssignment.instantiateArgs body ambient ordinary args)) =
          argsToSub (ContextualAssignment.instantiateArgs body ambient ordinary args) := by
        funext s x
        exact envEq s x
      rw [envEqFun]
      exact apply_terms body k _ _
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

/-- The comparison also holds componentwise below every operator binder. -/
theorem interpretArgs_terms
    {Γ Ξ Δ : Ctx S} (body : ContextualAssignment S M Γ)
    (ambient : Sub S Γ Δ) (ordinary : Sub S Ξ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S M) arity Ξ),
      interpretArgs (BindingCloneAlgebra.terms S) body ambient ordinary args =
        syntaxToFamily
          (ContextualAssignment.instantiateArgs body ambient ordinary args)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      change FamilyArgs.cons
          (interpretSchema (BindingCloneAlgebra.terms S) body
            (weakenEnvironment (BindingCloneAlgebra.terms S) binders ambient)
            ((BindingCloneAlgebra.terms S).substitution.liftEnvironment
              ordinary binders) head)
          (interpretArgs (BindingCloneAlgebra.terms S) body ambient ordinary tail) =
        FamilyArgs.cons
          (ContextualAssignment.instantiate body
            (ContextualAssignment.weakenSub (S := S) binders ambient)
            (liftSub ordinary binders) head)
          (syntaxToFamily
            (ContextualAssignment.instantiateArgs body ambient ordinary tail))
      rw [weakenEnvironment_terms]
      have liftEq :
          (BindingCloneAlgebra.terms S).substitution.liftEnvironment
              ordinary binders = liftSub ordinary binders := by
        exact BindingSubstitutionAlgebra.terms_liftEnvironment_eq_liftSub
          ordinary binders
      rw [liftEq]
      exact congrArg₂ FamilyArgs.cons
        (interpretSchema_terms body _ _ head)
        (interpretArgs_terms body ambient ordinary tail)
termination_by _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

#print axioms joinEnvironment_terms
#print axioms apply_terms
#print axioms joinEnvironment_map
#print axioms apply_map
#print axioms weakenEnvironment_terms
#print axioms weaken_map
#print axioms weakenEnvironment_map
#print axioms liftEnvironment_map
#print axioms interpretSchema_map
#print axioms interpretArgs_map
#print axioms argsEnvironment_syntaxToFamily
#print axioms interpretSchema_terms
#print axioms interpretArgs_terms

end Mettapedia.OSLF.Binding.SemanticContextualMetavariables
