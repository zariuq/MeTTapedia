import Mettapedia.Languages.Agda.Adequacy.StaticContext

/-!
# Raw static correspondence controls

These examples exercise nested capture avoidance, changing annotated types,
ordered telescope lookup, unreduced beta syntax, and excluded structural shapes.
They are controls of the raw correspondence, not typing derivations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Controls

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def ambientToNewest : StaticSpecification.Substitution 1 2 := fun _ => .var 0

def nestedLambda : StaticSpecification.Term 1 := .lam (.bind (.lam (.bind (.var 2))))

theorem nested_capture_avoided :
    bind (embedSub ambientToNewest) (embedTerm nestedLambda) =
      (Structural.lam (Structural.lam (.var (.succ (.succ .zero)))) : Structural.Tm (scope 2)) := rfl

theorem nested_capture_rejected :
    bind (embedSub ambientToNewest) (embedTerm nestedLambda) ≠
      (Structural.lam (Structural.lam (.var .zero)) : Structural.Tm (scope 2)) := by
  intro same
  cases same

def dependentType : StaticSpecification.Ty 1 := .el 1 (.var 0)
def replaceWithUniverse (level : Nat) : StaticSpecification.Substitution 1 1 := fun _ => .sort level

theorem dependent_annotation_changes :
    bind (embedSub (replaceWithUniverse 0)) (embedTy dependentType) =
      Structural.el (Structural.set (Structural.levelClosed 1))
        (Structural.sortTerm (Structural.set (Structural.levelClosed 0))) := rfl

theorem dependent_annotation_not_constant :
    bind (embedSub (replaceWithUniverse 0)) (embedTy dependentType) ≠
      bind (embedSub (replaceWithUniverse 1)) (embedTy dependentType) := by
  intro same
  cases same

def dependentPi : StaticSpecification.Term 1 :=
  .pi dependentType (.bind (.el 1 (.var 1)))

theorem pi_annotation_avoids_capture :
    bind (embedSub ambientToNewest) (embedTerm dependentPi) =
      (Structural.pi (Structural.el (Structural.set (Structural.levelClosed 1)) (.var .zero))
        (Structural.el (Structural.set (Structural.levelClosed 1)) (.var (.succ .zero))) :
          Structural.Tm (scope 2)) := rfl

theorem pi_annotation_does_not_capture :
    bind (embedSub ambientToNewest) (embedTerm dependentPi) ≠
      (Structural.pi (Structural.el (Structural.set (Structural.levelClosed 1)) (.var .zero))
        (Structural.el (Structural.set (Structural.levelClosed 1)) (.var .zero)) :
          Structural.Tm (scope 2)) := by
  intro same
  cases same

theorem noAbs_substitution :
    bind (embedSub ambientToNewest) (embedTerm (.lam (.noBind (.var 0)))) =
      (Structural.lamNoAbs (.var .zero) : Structural.Tm (scope 2)) := rfl

theorem noAbs_remains_distinct :
    embedTerm (StaticSpecification.Term.lam (.noBind (.var (0 : Fin 1)))) ≠
      embedTerm (.lam (.bind (.var 0))) := by
  intro same
  cases same

def betaRedex : StaticSpecification.Term 0 := .app (.lam (.bind (.var 0))) (.sort 0)

theorem beta_redex_is_in_image : decodeTerm (embedTerm betaRedex) = some betaRedex :=
  decodeTerm_embedTerm betaRedex

theorem beta_redex_is_unreduced : embedTerm betaRedex ≠ embedTerm (.sort 0) := by
  intro same
  cases same

def nestedApplication : StaticSpecification.Term 1 :=
  .app (.app (.var 0) (.sort 0)) (.sort 1)

theorem nested_application_shape : embedTerm nestedApplication =
    Structural.eliminate
      (Structural.eliminate (.var .zero)
        (Structural.cons (Structural.apply (embedTerm (n := 1) (.sort 0))) Structural.nil))
      (Structural.cons (Structural.apply (embedTerm (n := 1) (.sort 1))) Structural.nil) := rfl

theorem projection_is_not_in_image {n : Nat} (name : String) (source : StaticSpecification.Elim n) :
    embedElim source ≠ Structural.proj name := by
  intro same
  have decoded := congrArg decodeElim same
  rw [decodeElim_embedElim, decode_rejects_projection] at decoded
  cases decoded

theorem empty_elimination_is_not_in_image {n : Nat} (head : Structural.Tm (scope n))
    (source : StaticSpecification.Term n) :
    embedTerm source ≠ Structural.eliminate head Structural.nil := by
  intro same
  have decoded := congrArg decodeTerm same
  rw [decodeTerm_embedTerm, decode_rejects_empty_elimination] at decoded
  cases decoded

theorem combined_spine_is_not_in_image {n : Nat} (head : Structural.Tm (scope n))
    (first second : Structural.Elim (scope n)) (rest : Structural.Spine (scope n))
    (source : StaticSpecification.Term n) :
    embedTerm source ≠ Structural.eliminate head (Structural.cons first (Structural.cons second rest)) := by
  intro same
  have decoded := congrArg decodeTerm same
  rw [decodeTerm_embedTerm, decode_rejects_multiple_elimination] at decoded
  cases decoded

def contextOne : StaticSpecification.RawContext 1 := .snoc .nil (StaticSpecification.Ty.universe 1)
def contextTwo : StaticSpecification.RawContext 2 := .snoc contextOne dependentType

theorem newest_lookup :
    Structural.ContextGeometry.lookup (embedContext contextTwo) .zero =
      Structural.el (Structural.set (Structural.levelClosed 1)) (.var (.succ .zero)) := rfl

theorem older_lookup :
    Structural.ContextGeometry.lookup (embedContext contextTwo) (.succ .zero) =
      Structural.el (Structural.set (Structural.levelClosed 2))
        (Structural.sortTerm (Structural.set (Structural.levelClosed 1))) := rfl

theorem lookup_does_not_capture :
    Structural.ContextGeometry.lookup (embedContext contextTwo) .zero ≠
      Structural.el (Structural.set (Structural.levelClosed 1)) (.var .zero) := by
  intro same
  cases same

theorem dependent_telescope_round_trip :
    decodeContext (embedContext contextTwo) = some contextTwo := decodeContext_embedContext contextTwo

theorem prop_telescope_excluded :
    decodeContext (Telescope.RawContext.snoc (Telescope.RawContext.nil : Structural.ContextGeometry.RawContext 0)
      (Structural.el (Structural.prop (Structural.levelClosed 0)) (embedTerm (.sort 0)))) = none := by
  change (decodeTy (Structural.el (Structural.prop (Structural.levelClosed 0))
    (embedTerm (.sort 0)))).bind (fun type => some (StaticSpecification.RawContext.snoc .nil type)) = none
  rw [decode_rejects_prop_annotation]
  rfl

end Mettapedia.Languages.Agda.StaticAdequacy.Controls
