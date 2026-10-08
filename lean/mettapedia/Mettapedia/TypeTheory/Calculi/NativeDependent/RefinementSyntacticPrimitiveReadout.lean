import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticReification

/-!
# Primitive source readouts from checked arguments

Successful argument assembly reconstructs an admitted source substitution.
Reindexing the actual primitive declaration along it recovers the authored
family or term code, with its complete dependent type class. This calculation
uses declared formation certificates but no realization of whole source
derivations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open SyntacticModel SyntacticScopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

set_option backward.isDefEq.respectTransparency false in
theorem family_readout (headers : HeaderFormation D) (source : Context D)
    (symbol : S.TypeSymbol) (arguments : Fin (S.typeArity symbol) → TermExpr S source.arity)
    (values : Fin (S.typeArity symbol) → Option (Value (QuotientCwf.cwf D)
      ((quotientProjection D).obj source)))
    (readouts : ∀ index value, values index = some value → TermReadout _ (arguments index) value)
    (morphism : (quotientProjection D).obj source ⟶ ((data headers).typeParameters symbol).1)
    (assembled : ((data headers).typeParameters symbol).2.assemble? values = some morphism) :
    TypeReadout ((quotientProjection D).obj source) (.family symbol arguments)
      ((data headers).familyAt symbol morphism) := by
  rcases assemble_readout ((data headers).typeParameters symbol).2 source arguments values readouts
    morphism assembled with ⟨actual, classes, components⟩
  have codes : actual.substitution = arguments := by
    funext index
    exact components index
  refine ⟨(rawFamily headers symbol).reindex actual, ?_, ?_⟩
  · change (.family symbol TermExpr.var : TypeExpr S _).substitute actual.substitution = _
    change TypeExpr.family symbol actual.substitution = _
    rw [codes]
  · change QType.mk ((rawFamily headers symbol).reindex actual) =
      QuotientCwf.tySub (QType.mk (rawFamily headers symbol)) morphism
    rw [← classes]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem primitive_readout (headers : HeaderFormation D) (source : Context D)
    (symbol : S.TermSymbol) (arguments : Fin (S.termArity symbol) → TermExpr S source.arity)
    (values : Fin (S.termArity symbol) → Option (Value (QuotientCwf.cwf D)
      ((quotientProjection D).obj source)))
    (readouts : ∀ index value, values index = some value → TermReadout _ (arguments index) value)
    (morphism : (quotientProjection D).obj source ⟶ ((data headers).termParameters symbol).1)
    (assembled : ((data headers).termParameters symbol).2.assemble? values = some morphism) :
    TermReadout ((quotientProjection D).obj source) (.primitive symbol arguments)
      ((data headers).primitiveAt symbol morphism) := by
  rcases assemble_readout ((data headers).termParameters symbol).2 source arguments values readouts
    morphism assembled with ⟨actual, classes, components⟩
  have codes : actual.substitution = arguments := by
    funext index
    exact components index
  refine ⟨(rawResult headers symbol).reindex actual,
    (rawPrimitive headers symbol).reindex actual, ?_, ?_⟩
  · change (.primitive symbol TermExpr.var : TermExpr S _).substitute actual.substitution = _
    change TermExpr.primitive symbol actual.substitution = _
    rw [codes]
  · change QTerm.mk ((rawPrimitive headers symbol).reindex actual) =
      QuotientCwf.totalSub (QTerm.mk (rawPrimitive headers symbol)) morphism
    rw [← classes]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem predicate_primitive_readout (headers : HeaderFormation D) (source : Context D)
    (symbol : S.PredicateSymbol)
    (arguments : Fin (S.predicateArity symbol) → TermExpr S source.arity)
    (values : Fin (S.predicateArity symbol) → Option (Value (QuotientCwf.cwf D)
      ((quotientProjection D).obj source)))
    (readouts : ∀ index value, values index = some value → TermReadout _ (arguments index) value)
    (morphism : (quotientProjection D).obj source ⟶ ((data headers).predicateParameters symbol).1)
    (assembled : ((data headers).predicateParameters symbol).2.assemble? values = some morphism) :
    PredicateReadout ((quotientProjection D).obj source) (.atom symbol arguments)
      ((data headers).predicateAt symbol morphism) := by
  rcases assemble_readout ((data headers).predicateParameters symbol).2 source arguments values readouts
    morphism assembled with ⟨actual, classes, components⟩
  have codes : actual.substitution = arguments := by
    funext index
    exact components index
  refine ⟨(rawPredicate headers symbol).reindex actual, ?_, ?_⟩
  · change (.atom symbol TermExpr.var : PropExpr S _).substitute actual.substitution = _
    change PropExpr.atom symbol actual.substitution = _
    rw [codes]
  · change QPredicate.mk ((rawPredicate headers symbol).reindex actual) =
      PredicateAction.reindex morphism (QPredicate.mk (rawPredicate headers symbol))
    rw [← classes]
    rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
