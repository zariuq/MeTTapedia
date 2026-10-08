import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticScopes

/-!
# Mixed source variables retain authored positions

The variables of a constructed mixed scope are the complete generated
variable classes at their original data positions. Data weakening and
assumption inclusion both preserve the actual dependent annotation. Assumption
nodes restrict the scope without introducing an additional data position.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticScopes

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateModelScopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

def variableType (context : Context D) (position : Fin context.arity) : TypeOver context :=
  ⟨context.raw.lookup position, context.formed.lookup position⟩

def variableTerm (context : Context D) (position : Fin context.arity) :
    Term context (variableType context position) :=
  ⟨.var position, conclude (.variable context.raw position) ⟨context.formed.judgment, trivial⟩⟩

theorem cast_succ {n m : Nat} (same : n = m) (index : Fin n) :
    Fin.cast (congrArg Nat.succ same) index.succ = (Fin.cast same index).succ := by
  cases same
  rfl

theorem cast_zero {n m : Nat} (same : n = m) :
    Fin.cast (congrArg Nat.succ same) (0 : Fin (n + 1)) = (0 : Fin (m + 1)) := by
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem scope_lookup_class : {n : Nat} → {context : QuotientCwf.QContext D} →
    (scope : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n context) → (index : Fin n) →
    (scope.lookup index).2.val =
      QTerm.mk (variableTerm context.as (Fin.cast (scope_arity scope).symm index))
  | _, _, .nil, index => Fin.elim0 index
  | _, _, @ScopeData.snoc _ _ _ n context previous type, index => by
      cases index using Fin.cases with
      | zero =>
          change QTerm.mk (newest context.as (QuotientCwf.typeRepresentative type)) = _
          apply (QTerm.mk_eq_iff _ _).mpr
          have position : Fin.cast (scope_arity (.snoc previous type)).symm (0 : Fin (n + 1)) =
              (0 : Fin (context.as.arity + 1)) := cast_zero (scope_arity previous).symm
          rw [position]
          constructor
          · change Holds D (.typeEq _
              ((QuotientCwf.typeRepresentative type).code.substitute
                (fun index => .var index.succ))
              ((QuotientCwf.typeRepresentative type).code.rename Fin.succ))
            rw [TypeExpr.substitute_variables]
            exact typeEquality_refl
              (variableType (extend context.as (QuotientCwf.typeRepresentative type)) 0)
          · change Holds D (.termEq _ (.var 0) (.var 0)
              ((QuotientCwf.typeRepresentative type).code.substitute
                (fun index => .var index.succ)))
            rw [TypeExpr.substitute_variables]
            exact termEquality_refl
              (variableTerm (extend context.as (QuotientCwf.typeRepresentative type)) 0)
      | succ older =>
          change QuotientCwf.totalSub (previous.lookup older).2.val (QuotientCwf.wk type) = _
          rw [scope_lookup_class previous older]
          change QTerm.mk ((variableTerm context.as (Fin.cast (scope_arity previous).symm older)).reindex
            (projectionHom context.as (QuotientCwf.typeRepresentative type))) = _
          have position : Fin.cast (scope_arity (.snoc previous type)).symm older.succ =
              (Fin.cast (scope_arity previous).symm older).succ :=
            cast_succ (scope_arity previous).symm older
          rw [position]
          apply (QTerm.mk_eq_iff _ _).mpr
          constructor
          · change Holds D (.typeEq _
              ((context.as.raw.lookup (Fin.cast (scope_arity previous).symm older)).substitute
                (fun index => .var index.succ))
              ((context.as.raw.lookup (Fin.cast (scope_arity previous).symm older)).rename Fin.succ))
            rw [TypeExpr.substitute_variables]
            exact typeEquality_refl
              (variableType (extend context.as (QuotientCwf.typeRepresentative type))
                (Fin.cast (scope_arity previous).symm older).succ)
          · exact termEquality_refl
              ((variableTerm context.as (Fin.cast (scope_arity previous).symm older)).reindex
                (projectionHom context.as (QuotientCwf.typeRepresentative type)))

  | _, _, @ScopeData.assume _ _ _ n context previous predicate, index => by
      change QuotientCwf.totalSub (previous.lookup index).2.val
        (AssumptionModel.inclusion predicate) = _
      rw [scope_lookup_class previous index]
      change QTerm.mk ((variableTerm context.as (Fin.cast (scope_arity previous).symm index)).reindex
        (assumptionInclusion context.as (AssumptionModel.chosen predicate))) = _
      apply (QTerm.mk_eq_iff _ _).mpr
      constructor
      · change Holds D (.typeEq _
          ((context.as.raw.lookup (Fin.cast (scope_arity previous).symm index)).substitute TermExpr.var)
          (context.as.raw.lookup (Fin.cast (scope_arity previous).symm index)))
        rw [TypeExpr.substitute_identity]
        exact typeEquality_refl (variableType
          (assumed context.as (AssumptionModel.chosen predicate))
          (Fin.cast (scope_arity previous).symm index))
      · change Holds D (.termEq _
          ((.var (Fin.cast (scope_arity previous).symm index) : TermExpr S _).substitute TermExpr.var)
          (.var (Fin.cast (scope_arity previous).symm index))
          ((context.as.raw.lookup (Fin.cast (scope_arity previous).symm index)).substitute TermExpr.var))
        rw [TermExpr.substitute_identity, TypeExpr.substitute_identity]
        exact termEquality_refl (variableTerm
          (assumed context.as (AssumptionModel.chosen predicate))
          (Fin.cast (scope_arity previous).symm index))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticScopes
