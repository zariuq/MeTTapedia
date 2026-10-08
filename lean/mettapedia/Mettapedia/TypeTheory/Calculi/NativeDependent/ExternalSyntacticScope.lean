import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticReification

/-!
# Scoped source-model telescopes

The raw context, its generated formation and the actual chosen-model telescope
share one scope index. Extending this presentation uses the real selected
comprehension. Variable readouts retain their authored positions and complete
dependent classes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open SyntacticTelescopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

structure Scope (D : Signature S) (n : Nat) where
  raw : ContextExpr S n
  formed : Formed D raw
  telescope : Telescope (QuotientCwf.withTerminal D) n
    ((quotientProjection D).obj ⟨n, raw, formed⟩)

namespace Scope

abbrev source {n : Nat} (scope : Scope D n) : Context D := ⟨n, scope.raw, scope.formed⟩

abbrev semantic {n : Nat} (scope : Scope D n) :
    Mettapedia.TypeTheory.ContextualModelTelescopes.Context (QuotientCwf.withTerminal D) n :=
  ⟨(quotientProjection D).obj scope.source, scope.telescope⟩

abbrev nil (D : Signature S) : Scope D 0 := ⟨.nil, .nil, .nil⟩

def ofSemantic {n : Nat}
    (context : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
      (QuotientCwf.withTerminal D) n) : Scope D n := by
  rcases context with ⟨⟨⟨arity, raw, formed⟩⟩, telescope⟩
  have same : arity = n := telescope_arity telescope
  cases same
  exact ⟨raw, formed, telescope⟩

theorem ofSemantic_semantic {n : Nat}
    (context : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
      (QuotientCwf.withTerminal D) n) :
    (ofSemantic context).semantic = context := by
  rcases context with ⟨⟨⟨arity, raw, formed⟩⟩, telescope⟩
  have same : arity = n := telescope_arity telescope
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
    .snoc scope.telescope type⟩

theorem snoc_source {n : Nat} (scope : Scope D n)
    (type : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) :
    (scope.snoc type).source = extend scope.source (QuotientCwf.typeRepresentative type) := rfl

theorem snoc_semantic {n : Nat} (scope : Scope D n)
    (type : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) :
    (scope.snoc type).semantic = scope.semantic.snoc type := rfl

theorem variable_readout {n : Nat} (scope : Scope D n) (index : Fin n) :
    TermReadout ((quotientProjection D).obj scope.source) (.var index)
      (scope.telescope.lookup index) := by
  refine ⟨variableType scope.source index, variableTerm scope.source index, rfl, ?_⟩
  exact (telescope_lookup_class scope.telescope index).symm

end Scope

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification
