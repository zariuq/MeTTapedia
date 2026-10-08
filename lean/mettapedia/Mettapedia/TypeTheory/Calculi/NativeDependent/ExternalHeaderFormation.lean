import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalJudgments
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalDeclarationOrder

/-!
# Formed ordered declaration headers

Raw dependency bounds do not prove formation. This qualifier supplies actual
generated formation trees for primitive headers and result types. Every rule
occurrence and every premise tree must respect the declaration's earlier-rank
bound. The data is entirely syntactic; no model interpretation or global
soundness theorem is supplied as a field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

universe u

variable {S : Symbols.{u}}

def Judgment.before (D : Signature S) (bound : Nat) : Judgment S → Prop
  | .context gamma => gamma.before D.typeRank D.termRank bound
  | .type gamma expression => gamma.before D.typeRank D.termRank bound ∧
      expression.before D.typeRank D.termRank bound
  | .term gamma value expression => gamma.before D.typeRank D.termRank bound ∧
      value.before D.typeRank D.termRank bound ∧ expression.before D.typeRank D.termRank bound
  | .substitution source target mapping => source.before D.typeRank D.termRank bound ∧
      target.before D.typeRank D.termRank bound ∧
      ∀ index, (mapping index).before D.typeRank D.termRank bound
  | .contextEq first second => first.before D.typeRank D.termRank bound ∧
      second.before D.typeRank D.termRank bound
  | .typeEq gamma first second => gamma.before D.typeRank D.termRank bound ∧
      first.before D.typeRank D.termRank bound ∧ second.before D.typeRank D.termRank bound
  | .termEq gamma first second expression => gamma.before D.typeRank D.termRank bound ∧
      first.before D.typeRank D.termRank bound ∧ second.before D.typeRank D.termRank bound ∧
      expression.before D.typeRank D.termRank bound
  | .substitutionEq source target first second => source.before D.typeRank D.termRank bound ∧
      target.before D.typeRank D.termRank bound ∧
      (∀ index, (first index).before D.typeRank D.termRank bound) ∧
      ∀ index, (second index).before D.typeRank D.termRank bound

variable {D : Signature S}

/-- Change only the authored judgment index of a supplied derivation. -/
def Derivation.reindex {first second : Judgment S} (same : first = second)
    (tree : Derivation D first) : Derivation D second := same ▸ tree

/-- The supplied tree is bounded at every node, not only at its root. -/
def Derivation.before (bound : Nat) : {judgment : Judgment S} → Derivation D judgment → Prop
  | _, .node rule premises => rule.val.conclusion.before D bound ∧
      ∀ position, Derivation.before bound (premises position)

@[simp] theorem Derivation.before_reindex {bound : Nat} {first second : Judgment S}
    (same : first = second) (tree : Derivation D first) :
    (tree.reindex same).before bound ↔ tree.before bound := by
  cases same
  rfl

theorem Derivation.before_judgment {bound : Nat} : ∀ {judgment : Judgment S}
    (tree : Derivation D judgment), tree.before bound → judgment.before D bound
  | _, .node rule _, ordered => by
      rw [← rule.property]
      exact ordered.1

/-- Each separately supplied declaration has genuinely formed earlier headers. -/
structure HeaderFormation (D : Signature S) where
  typeHeader : (symbol : S.TypeSymbol) → Derivation D (.context (D.typeParameters symbol))
  typeHeader_before : ∀ symbol, (typeHeader symbol).before (D.typeRank symbol)
  termHeader : (symbol : S.TermSymbol) → Derivation D (.context (D.termParameters symbol))
  termHeader_before : ∀ symbol, (termHeader symbol).before (D.termRank symbol)
  termResult : (symbol : S.TermSymbol) →
    Derivation D (.type (D.termParameters symbol) (D.termResult symbol))
  termResult_before : ∀ symbol, (termResult symbol).before (D.termRank symbol)

/-- No external generated type uses strictly negative declaration ranks. -/
theorem TypeExpr.not_before_zero : ∀ {n : Nat} (type : TypeExpr S n)
    (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat),
    ¬ type.before typeRank termRank 0
  | _, .family _ _, _, _ => fun ordered => Nat.not_lt_zero _ ordered.1
  | _, .pi domain _, typeRank, termRank => fun ordered =>
      TypeExpr.not_before_zero domain typeRank termRank ordered.1
  | _, .sigma domain _, typeRank, termRank => fun ordered =>
      TypeExpr.not_before_zero domain typeRank termRank ordered.1

/-- A nonempty header cannot be justified merely by assigning it rank zero. -/
theorem ContextExpr.extension_not_before_zero {n : Nat} (context : ContextExpr S n)
    (type : TypeExpr S n) (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat) :
    ¬ (context.snoc type).before typeRank termRank 0 := fun ordered =>
  type.not_before_zero typeRank termRank ordered.2

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
