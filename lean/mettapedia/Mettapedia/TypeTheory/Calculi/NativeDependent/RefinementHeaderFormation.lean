import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementDerivedContexts

/-!
# Independently formed refinement declaration headers

Rank and raw scope conditions do not establish formation. Each declaration
supplies an actual generated formation tree for its mixed parameter context;
term declarations also supply a generated formation tree for their result.
Every occurrence in these trees uses only earlier declarations. The ordinary
proposition type and logical formers are available without primitive ranks.
No semantic interpretation or global soundness theorem is a field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {S : Symbols.{u}}

def Judgment.before (D : Signature S) (bound : Nat) : Judgment S → Prop
  | .context gamma => gamma.before D.typeRank D.termRank D.predicateRank bound
  | .type gamma expression => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      expression.before D.typeRank D.termRank D.predicateRank bound
  | .term gamma value expression => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      value.before D.typeRank D.termRank D.predicateRank bound ∧
      expression.before D.typeRank D.termRank D.predicateRank bound
  | .substitution source target mapping =>
      source.before D.typeRank D.termRank D.predicateRank bound ∧
      target.before D.typeRank D.termRank D.predicateRank bound ∧
      ∀ index, (mapping index).before D.typeRank D.termRank D.predicateRank bound
  | .contextEq first second => first.before D.typeRank D.termRank D.predicateRank bound ∧
      second.before D.typeRank D.termRank D.predicateRank bound
  | .typeEq gamma first second => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      first.before D.typeRank D.termRank D.predicateRank bound ∧
      second.before D.typeRank D.termRank D.predicateRank bound
  | .termEq gamma first second expression => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      first.before D.typeRank D.termRank D.predicateRank bound ∧
      second.before D.typeRank D.termRank D.predicateRank bound ∧
      expression.before D.typeRank D.termRank D.predicateRank bound
  | .substitutionEq source target first second =>
      source.before D.typeRank D.termRank D.predicateRank bound ∧
      target.before D.typeRank D.termRank D.predicateRank bound ∧
      (∀ index, (first index).before D.typeRank D.termRank D.predicateRank bound) ∧
      ∀ index, (second index).before D.typeRank D.termRank D.predicateRank bound
  | .predicate gamma formula => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      formula.before D.typeRank D.termRank D.predicateRank bound
  | .entails gamma formula => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      formula.before D.typeRank D.termRank D.predicateRank bound
  | .predicateEq gamma first second => gamma.before D.typeRank D.termRank D.predicateRank bound ∧
      first.before D.typeRank D.termRank D.predicateRank bound ∧
      second.before D.typeRank D.termRank D.predicateRank bound

variable {D : Signature S}

def Derivation.before (bound : Nat) : {judgment : Judgment S} → Derivation D judgment → Prop
  | _, .node rule premises => rule.val.conclusion.before D bound ∧
      ∀ position, Derivation.before bound (premises position)

def PremiseEvidence.before (bound : Nat) : {judgments : List (Judgment S)} →
    PremiseEvidence D judgments → Prop
  | _, .nil => True
  | _, .cons first remaining => first.before bound ∧ remaining.before bound

theorem PremiseEvidence.at_before {judgments : List (Judgment S)}
    (premises : PremiseEvidence D judgments) (bound : Nat) (ordered : premises.before bound)
    (position : Fin judgments.length) : (premises.at position).before bound := by
  induction premises with
  | nil => exact Fin.elim0 position
  | cons first remaining ih =>
      cases position using Fin.cases with
      | zero => exact ordered.1
      | succ prior => exact ih ordered.2 prior

theorem deriveList_before (rule : RuleCode D) (premises : PremiseEvidence D rule.premises)
    (bound : Nat) (conclusion : rule.conclusion.before D bound)
    (ordered : premises.before bound) : (deriveList rule premises).before bound :=
  ⟨conclusion, fun position => premises.at_before bound ordered position.down⟩

theorem Derivation.before_judgment {bound : Nat} : ∀ {judgment : Judgment S}
    (tree : Derivation D judgment), tree.before bound → judgment.before D bound
  | _, .node rule _, ordered => by
      rw [← rule.property]
      exact ordered.1

/-- Local syntactic admission of every independently declared header. -/
structure HeaderFormation (D : Signature S) where
  typeHeader : (symbol : S.TypeSymbol) → Derivation D (.context (D.typeParameters symbol))
  typeHeader_before : ∀ symbol, (typeHeader symbol).before (D.typeRank symbol)
  termHeader : (symbol : S.TermSymbol) → Derivation D (.context (D.termParameters symbol))
  termHeader_before : ∀ symbol, (termHeader symbol).before (D.termRank symbol)
  termResult : (symbol : S.TermSymbol) →
    Derivation D (.type (D.termParameters symbol) (D.termResult symbol))
  termResult_before : ∀ symbol, (termResult symbol).before (D.termRank symbol)
  predicateHeader : (symbol : S.PredicateSymbol) →
    Derivation D (.context (D.predicateParameters symbol))
  predicateHeader_before : ∀ symbol, (predicateHeader symbol).before (D.predicateRank symbol)

/-- Primitive family occurrences require a genuine earlier declaration rank. -/
theorem TypeExpr.family_not_before_zero {n : Nat} (symbol : S.TypeSymbol)
    (arguments : Fin (S.typeArity symbol) → TermExpr S n)
    (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat)
    (predicateRank : S.PredicateSymbol → Nat) :
    ¬ (TypeExpr.family symbol arguments).before typeRank termRank predicateRank 0 :=
  fun ordered => Nat.not_lt_zero _ ordered.1

/-- The ordinary proposition type is available without an internal universe. -/
theorem TypeExpr.propositions_before {n : Nat} (typeRank : S.TypeSymbol → Nat)
    (termRank : S.TermSymbol → Nat) (predicateRank : S.PredicateSymbol → Nat) (bound : Nat) :
    (TypeExpr.propositions (S := S) (n := n)).before typeRank termRank predicateRank bound :=
  True.intro

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
