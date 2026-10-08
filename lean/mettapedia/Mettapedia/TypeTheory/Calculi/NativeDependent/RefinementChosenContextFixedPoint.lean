import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticScopes

/-!
# Fixed points of chosen mixed-context presentations

Selection fixes contexts assembled with the actual chosen type and
predicate representatives. Data and assumption steps retain their separate
roles: the former introduces a variable, while the latter changes the
admitted substitutions. Every complete mixed scope of the constructed source
model belongs to this fixed-point image. Other raw contexts keep their
comparison isomorphisms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Presentation

open Mettapedia.TypeTheory.ContextualPredicateModelScopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

private theorem representative_code_at_equal_context {n : Nat}
    {first second : ContextExpr S n} (firstFormed : Formed D first)
    (secondFormed : Formed D second) (same : first = second)
    (type : QType (contextOf second secondFormed))
    (typed : Holds D (.type first (QuotientCwf.typeRepresentative type).code)) :
    (QuotientCwf.typeRepresentative
      (QType.mk (⟨(QuotientCwf.typeRepresentative type).code, typed⟩ :
        TypeOver (contextOf first firstFormed)))).code =
      (QuotientCwf.typeRepresentative type).code := by
  cases same
  change (QuotientCwf.typeRepresentative
    (QType.mk (QuotientCwf.typeRepresentative type))).code = _
  rw [QuotientCwf.typeRepresentative_class]

private theorem predicate_code_at_equal_context {n : Nat}
    {first second : ContextExpr S n} (firstFormed : Formed D first)
    (secondFormed : Formed D second) (same : first = second)
    (predicate : QPredicate (contextOf second secondFormed))
    (formed : Holds D (.predicate first (AssumptionModel.chosen predicate).code)) :
    (AssumptionModel.chosen
      (QPredicate.mk (⟨(AssumptionModel.chosen predicate).code, formed⟩ :
        PredicateOver (contextOf first firstFormed)))).code =
      (AssumptionModel.chosen predicate).code := by
  cases same
  change (AssumptionModel.chosen (QPredicate.mk (AssumptionModel.chosen predicate))).code = _
  rw [AssumptionModel.chosen_class]

theorem selectedContext_fixed {context : Context D} (chosen : Chosen D context) :
    selectedContext context = context := by
  induction chosen with
  | empty => rfl
  | @extend context previous type earlier =>
    cases context with
    | mk n raw formed =>
      change (select raw formed).context = contextOf raw formed at earlier
      have raws : (select raw formed).selected = raw := by
        have same := congrArg
          (fun context : Context D => (⟨context.arity, context.raw⟩ : Σ n, ContextExpr S n)) earlier
        exact eq_of_heq (Sigma.mk.inj same).2
      refine SyntacticScopes.raw_context_ext
        (selected_arity (extend (contextOf raw formed) (QuotientCwf.typeRepresentative type))) ?_
      apply heq_of_eq
      change ContextExpr.snoc (select raw formed).selected _ = ContextExpr.snoc raw _
      apply congrArg₂ ContextExpr.snoc raws
      exact representative_code_at_equal_context (select raw formed).formed formed raws type _
  | @assume context previous predicate earlier =>
    cases context with
    | mk n raw formed =>
      change (select raw formed).context = contextOf raw formed at earlier
      have raws : (select raw formed).selected = raw := by
        have same := congrArg
          (fun context : Context D => (⟨context.arity, context.raw⟩ : Σ n, ContextExpr S n)) earlier
        exact eq_of_heq (Sigma.mk.inj same).2
      refine SyntacticScopes.raw_context_ext
        (selected_arity (assumed (contextOf raw formed) (AssumptionModel.chosen predicate))) ?_
      apply heq_of_eq
      change ContextExpr.assume (select raw formed).selected _ = ContextExpr.assume raw _
      apply congrArg₂ ContextExpr.assume raws
      exact predicate_code_at_equal_context (select raw formed).formed formed raws predicate _

theorem chosen_of_scope : {n : Nat} → {context : QuotientCwf.QContext D} →
    ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n context → Chosen D context.as
  | _, _, .nil => .empty
  | _, _, .snoc previous type => .extend (chosen_of_scope previous) type
  | _, _, .assume previous predicate => .assume (chosen_of_scope previous) predicate

theorem selectedContext_scope_fixed {n : Nat} {context : QuotientCwf.QContext D}
    (scope : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n context) : selectedContext context.as = context.as :=
  selectedContext_fixed (chosen_of_scope scope)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Presentation
