import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPresentation

/-!
# Complete chosen mixed scopes in the generated model

The source model retains raw contexts. A selected data extension determines
its preceding context and actual type class; a selected assumption determines
its preceding context and actual predicate class. Constructor separation and
these injectivity laws earn uniqueness of a complete finite mixed scope over
an actual source object. This is a result about the generated source model,
not an arbitrary-model scope-uniqueness assumption.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticScopes

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateModelScopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem raw_context_ext {first second : Context D}
    (arity : first.arity = second.arity) (raw : HEq first.raw second.raw) : first = second := by
  cases first
  cases second
  cases arity
  cases eq_of_heq raw
  rfl

theorem extension_injective {first second : QuotientCwf.QContext D}
    {left : QuotientCwf.Ty first} {right : QuotientCwf.Ty second}
    (equal : QuotientCwf.ext first left = QuotientCwf.ext second right) :
    first = second ∧ HEq left right := by
  have counts : first.as.arity = second.as.arity :=
    Nat.succ.inj (congrArg (fun context => context.as.arity) equal)
  cases first with
  | mk first =>
    cases second with
    | mk second =>
      cases first with
      | mk firstArity firstRaw firstFormed =>
        cases second with
        | mk secondArity secondRaw secondFormed =>
          dsimp only at counts
          cases counts
          have raws :
              ContextExpr.snoc firstRaw (QuotientCwf.typeRepresentative left).code =
                ContextExpr.snoc secondRaw (QuotientCwf.typeRepresentative right).code :=
            eq_of_heq (Sigma.mk.inj (congrArg
              (fun context => (⟨context.as.arity, context.as.raw⟩ : Σ n, ContextExpr S n)) equal)).2
          have parts := ContextExpr.snoc.inj raws
          cases parts.1
          have types : left = right := by
            calc
              left = QType.mk (QuotientCwf.typeRepresentative left) :=
                (QuotientCwf.typeRepresentative_class left).symm
              _ = QType.mk (QuotientCwf.typeRepresentative right) :=
                congrArg QType.mk (TypeOver.ext parts.2)
              _ = right := QuotientCwf.typeRepresentative_class right
          exact ⟨rfl, heq_of_eq types⟩


theorem assumption_injective {first second : QuotientCwf.QContext D}
    {left : QPredicate first.as} {right : QPredicate second.as}
    (equal : AssumptionModel.selected first left = AssumptionModel.selected second right) :
    first = second ∧ HEq left right := by
  have counts : first.as.arity = second.as.arity :=
    congrArg (fun context => context.as.arity) equal
  cases first with
  | mk first =>
    cases second with
    | mk second =>
      cases first with
      | mk firstArity firstRaw firstFormed =>
        cases second with
        | mk secondArity secondRaw secondFormed =>
          dsimp only at counts
          cases counts
          have raws :
              ContextExpr.assume firstRaw (AssumptionModel.chosen left).code =
                ContextExpr.assume secondRaw (AssumptionModel.chosen right).code :=
            eq_of_heq (Sigma.mk.inj (congrArg
              (fun context => (⟨context.as.arity, context.as.raw⟩ : Σ n, ContextExpr S n)) equal)).2
          have parts := ContextExpr.assume.inj raws
          cases parts.1
          have predicates : left = right := by
            calc
              left = QPredicate.mk (AssumptionModel.chosen left) := (AssumptionModel.chosen_class left).symm
              _ = QPredicate.mk (AssumptionModel.chosen right) :=
                congrArg QPredicate.mk (PredicateOver.ext parts.2)
              _ = right := AssumptionModel.chosen_class right
          exact ⟨rfl, heq_of_eq predicates⟩

def outerBinder : {n : Nat} → ContextExpr S n → Nat
  | _, .nil => 0
  | _, .snoc _ _ => 1
  | _, .assume _ _ => 2

theorem empty_ne_assumption (context : QuotientCwf.QContext D) (predicate : QPredicate context.as) :
    (quotientProjection D).obj (Contextual.empty D) ≠ AssumptionModel.selected context predicate := by
  intro same
  have tags : (0 : Nat) = 2 := congrArg
    (fun context : QuotientCwf.QContext D => outerBinder context.as.raw) same
  exact Nat.noConfusion tags

theorem extension_ne_assumption (first : QuotientCwf.QContext D) (type : QType first.as)
    (second : QuotientCwf.QContext D) (predicate : QPredicate second.as) :
    QuotientCwf.ext first type ≠ AssumptionModel.selected second predicate := by
  intro same
  have tags : (1 : Nat) = 2 := congrArg
    (fun context : QuotientCwf.QContext D => outerBinder context.as.raw) same
  exact Nat.noConfusion (Nat.succ.inj tags)

theorem scope_arity : {n : Nat} → {context : QuotientCwf.QContext D} →
    ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n context → context.as.arity = n
  | _, _, .nil => rfl
  | _, _, .snoc previous _ => congrArg Nat.succ (scope_arity previous)
  | n, _, @ScopeData.assume _ _ _ _ prior previous _ => by
      change prior.as.arity = n
      exact scope_arity (n := n) (context := prior) previous

theorem scope_heq : {n : Nat} → {firstContext secondContext : QuotientCwf.QContext D} →
    (first : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n firstContext) →
    (second : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n secondContext) →
    firstContext = secondContext → HEq first second
  | _, _, _, .nil, .nil, _ => HEq.rfl
  | _, _, _, .nil, .assume earlier predicate, contexts =>
      False.elim (empty_ne_assumption _ predicate contexts)
  | _, _, _, .assume previous predicate, .nil, contexts =>
      False.elim (empty_ne_assumption _ predicate contexts.symm)
  | _, _, _, .snoc previous type, .assume earlier predicate, contexts =>
      False.elim (extension_ne_assumption _ type _ predicate contexts)
  | _, _, _, .assume previous predicate, .snoc earlier type, contexts =>
      False.elim (extension_ne_assumption _ type _ predicate contexts.symm)
  | _, _, _, .snoc previous type, .snoc earlier family, contexts => by
      have parts := extension_injective contexts
      cases parts.1
      cases eq_of_heq parts.2
      cases eq_of_heq (scope_heq previous earlier rfl)
      rfl
  | _, _, _, .assume previous predicate, .assume earlier assumption, contexts => by
      have parts := assumption_injective contexts
      cases parts.1
      cases eq_of_heq parts.2
      cases eq_of_heq (scope_heq previous earlier rfl)
      rfl

instance scopeSubsingleton {n : Nat} (context : QuotientCwf.QContext D) :
    Subsingleton (ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n context) :=
  ⟨fun first second => eq_of_heq (scope_heq first second rfl)⟩

theorem semantic_scope_ext {n : Nat}
    (first second : Scope (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n)
    (contexts : first.1 = second.1) : first = second :=
  Sigma.ext contexts (scope_heq first.2 second.2 contexts)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticScopes
