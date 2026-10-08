import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticReification

/-!
# Scoped mixed source-model presentations

The raw context, its generated formation and its actual chosen-model mixed
scope share one data arity. Data extensions use selected comprehension,
and assumption extensions use selected guarded contexts without changing
that arity. Variable readouts retain their authored positions and complete
dependent classes across both forms of extension.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open SyntacticScopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

structure Scope (D : Signature S) (n : Nat) where
  raw : ContextExpr S n
  formed : Formed D raw
  mixed : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
    (generatedModel D).assumptions n ((quotientProjection D).obj ⟨n, raw, formed⟩)

namespace Scope

abbrev source {n : Nat} (scope : Scope D n) : Context D := ⟨n, scope.raw, scope.formed⟩

abbrev semantic {n : Nat} (scope : Scope D n) :
    Mettapedia.TypeTheory.ContextualPredicateModelScopes.Scope (QuotientCwf.withTerminal D)
      (generatedModel D).doctrine (generatedModel D).assumptions n :=
  ⟨(quotientProjection D).obj scope.source, scope.mixed⟩

abbrev nil (D : Signature S) : Scope D 0 := ⟨.nil, .nil, .nil⟩

def ofSemantic {n : Nat}
    (context : Mettapedia.TypeTheory.ContextualPredicateModelScopes.Scope
      (QuotientCwf.withTerminal D) (generatedModel D).doctrine (generatedModel D).assumptions n) : Scope D n := by
  rcases context with ⟨⟨⟨arity, raw, formed⟩⟩, mixed⟩
  have same : arity = n := scope_arity mixed
  cases same
  exact ⟨raw, formed, mixed⟩

theorem ofSemantic_semantic {n : Nat}
    (context : Mettapedia.TypeTheory.ContextualPredicateModelScopes.Scope
      (QuotientCwf.withTerminal D) (generatedModel D).doctrine (generatedModel D).assumptions n) :
    (ofSemantic context).semantic = context := by
  rcases context with ⟨⟨⟨arity, raw, formed⟩⟩, mixed⟩
  have same : arity = n := scope_arity mixed
  cases same
  rfl

theorem ofSemantic_scope {n : Nat} (scope : Scope D n) :
    ofSemantic scope.semantic = scope := by
  cases scope
  rfl

theorem semantic_injective {n : Nat} : Function.Injective (@semantic S D n) := by
  intro first second same
  have sourceSame := congrArg ofSemantic same
  simpa only [ofSemantic_scope] using sourceSame

noncomputable def snoc {n : Nat} (scope : Scope D n)
    (type : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) : Scope D (n + 1) :=
  ⟨.snoc scope.raw (QuotientCwf.typeRepresentative type).code,
    .snoc scope.formed (QuotientCwf.typeRepresentative type).formed,
    .snoc scope.mixed type⟩

theorem snoc_source {n : Nat} (scope : Scope D n)
    (type : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) :
    (scope.snoc type).source = extend scope.source (QuotientCwf.typeRepresentative type) := rfl

theorem snoc_semantic {n : Nat} (scope : Scope D n)
    (type : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) :
    (scope.snoc type).semantic = scope.semantic.snoc type := rfl


noncomputable def assume {n : Nat} (scope : Scope D n)
    (predicate : QPredicate scope.source) : Scope D n :=
  ⟨.assume scope.raw (AssumptionModel.chosen predicate).code,
    .assume scope.formed (AssumptionModel.chosen predicate).formed,
    .assume scope.mixed predicate⟩

theorem assume_source {n : Nat} (scope : Scope D n) (predicate : QPredicate scope.source) :
    (scope.assume predicate).source = assumed scope.source (AssumptionModel.chosen predicate) := rfl

theorem assume_semantic {n : Nat} (scope : Scope D n) (predicate : QPredicate scope.source) :
    (scope.assume predicate).semantic = scope.semantic.assume predicate := rfl

theorem variable_readout {n : Nat} (scope : Scope D n) (index : Fin n) :
    TermReadout ((quotientProjection D).obj scope.source) (.var index)
      (scope.mixed.lookup index) := by
  refine ⟨variableType scope.source index, variableTerm scope.source index, rfl, ?_⟩
  exact (scope_lookup_class scope.mixed index).symm

end Scope

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
