import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticTelescopes

/-!
# Source telescope variables retain authored positions

The variables of an actual generated-model telescope are the complete
generated variable classes at their original positions. Weakening preserves
the position and its dependent annotation. This connects model component
checking to the authored source substitution arrays.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticTelescopes

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

def variableType (context : Context D) (position : Fin context.arity) : TypeOver context :=
  ⟨context.raw.lookup position, context.formed.lookup position⟩

def variableTerm (context : Context D) (position : Fin context.arity) :
    Term context (variableType context position) :=
  ⟨.var position, conclude (.variable context.raw position) ⟨context.formed.judgment, trivial⟩⟩

theorem telescope_arity : {n : Nat} → {context : QuotientCwf.QContext D} →
    Telescope (QuotientCwf.withTerminal D) n context → context.as.arity = n
  | _, _, .nil => rfl
  | _, _, .snoc previous _ => congrArg Nat.succ (telescope_arity previous)

theorem cast_succ {n m : Nat} (same : n = m) (index : Fin n) :
    Fin.cast (congrArg Nat.succ same) index.succ = (Fin.cast same index).succ := by
  cases same
  rfl

theorem cast_zero {n m : Nat} (same : n = m) :
    Fin.cast (congrArg Nat.succ same) (0 : Fin (n + 1)) = (0 : Fin (m + 1)) := by
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem telescope_lookup_class : {n : Nat} → {context : QuotientCwf.QContext D} →
    (telescope : Telescope (QuotientCwf.withTerminal D) n context) → (index : Fin n) →
    (telescope.lookup index).2.val =
      QTerm.mk (variableTerm context.as (Fin.cast (telescope_arity telescope).symm index))
  | _, _, .nil, index => Fin.elim0 index
  | _, _, @Telescope.snoc _ n context previous type, index => by
      cases index using Fin.cases with
      | zero =>
          change QTerm.mk (newest context.as (QuotientCwf.typeRepresentative type)) = _
          apply (QTerm.mk_eq_iff _ _).mpr
          have position : Fin.cast (telescope_arity (.snoc previous type)).symm (0 : Fin (n + 1)) =
              (0 : Fin (context.as.arity + 1)) := cast_zero (telescope_arity previous).symm
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
          rw [telescope_lookup_class previous older]
          change QTerm.mk ((variableTerm context.as (Fin.cast (telescope_arity previous).symm older)).reindex
            (projectionHom context.as (QuotientCwf.typeRepresentative type))) = _
          have position : Fin.cast (telescope_arity (.snoc previous type)).symm older.succ =
              (Fin.cast (telescope_arity previous).symm older).succ :=
            cast_succ (telescope_arity previous).symm older
          rw [position]
          apply (QTerm.mk_eq_iff _ _).mpr
          constructor
          · change Holds D (.typeEq _
              ((context.as.raw.lookup (Fin.cast (telescope_arity previous).symm older)).substitute
                (fun index => .var index.succ))
              ((context.as.raw.lookup (Fin.cast (telescope_arity previous).symm older)).rename Fin.succ))
            rw [TypeExpr.substitute_variables]
            exact typeEquality_refl
              (variableType (extend context.as (QuotientCwf.typeRepresentative type))
                (Fin.cast (telescope_arity previous).symm older).succ)
          · exact termEquality_refl
              ((variableTerm context.as (Fin.cast (telescope_arity previous).symm older)).reindex
                (projectionHom context.as (QuotientCwf.typeRepresentative type)))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticTelescopes
