import Mettapedia.Languages.Agda.Adequacy.StaticObservationNaturality
import Mettapedia.Languages.Agda.Adequacy.StaticRetraction
import Mettapedia.OSLF.Syntax.BindingTelescopeSubstitution

/-!
# Recursive administrative observation controls

Administrative syntax can occur beneath binders and within type annotations.
Observation retains application order and the Abs/NoAbs distinction while
identifying genuinely distinct empty/append representations. Unsupported
constructors and unsupported substitution images remain outside its domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Observation.Controls

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def nestedAdministrative : Structural.Tm (scope 1) :=
  Structural.lam (Structural.lam
    (Structural.eliminate (.var (.succ (.succ .zero))) Structural.nil))

def nestedSource : StaticSpecification.Term 1 := .lam (.bind (.lam (.bind (.var 2))))

theorem nested_observation : term nestedAdministrative = some nestedSource := rfl

theorem nested_raw_terms_differ : nestedAdministrative ≠ embedTerm nestedSource := by
  intro same
  cases same

theorem nested_canonical_decoder_rejects : decodeTerm nestedAdministrative = none := by
  rw [decodeTerm.eq_def]
  change (decodeTerm (n := 2) (Structural.lam
    (Structural.eliminate (.var (.succ (.succ .zero))) Structural.nil))).map _ = none
  rw [decodeTerm.eq_def]
  change ((decodeTerm (n := 3) (Structural.eliminate
    (.var (.succ (.succ .zero))) Structural.nil)).map _).map _ = none
  rw [decodeTerm.eq_def]
  change (((decodeTerm (n := 3) (.var (.succ (.succ .zero)))).bind (fun f =>
    (decodeSingleton (n := 3) Structural.nil).bind (fun e => some (StaticSpecification.Term.elim f e)))).map _).map _ = none
  rw [decodeSingleton.eq_def]
  cases decodeTerm (n := 3) (.var (.succ (.succ .zero))) <;> rfl

def administrativeIdentitySub : Sub sig (scope 1) (scope 1) :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 1)
    (Structural.eliminate (.var .zero) Structural.nil)

theorem administrative_identity_images :
    SubObserves administrativeIdentitySub (StaticSpecification.Term.var : StaticSpecification.Substitution 1 1) := by
  intro index
  refine Fin.cases rfl (fun impossible => Fin.elim0 impossible) index

theorem substitution_beneath_two_binders :
    term (bind administrativeIdentitySub nestedAdministrative) = some nestedSource := by
  exact (observe_bind_of_some administrative_identity_images nested_observation).trans
    (congrArg some (StaticSpecification.Term.subst_id nestedSource))

theorem nested_variable_not_captured :
    term (bind administrativeIdentitySub nestedAdministrative) ≠
      some (StaticSpecification.Term.lam (.bind (.lam (.bind (.var 0))))) := by
  rw [substitution_beneath_two_binders]
  intro same
  cases same

def dependentAnnotation : Structural.Ty (scope 1) :=
  Structural.el (Structural.set (Structural.levelClosed 1))
    (Structural.eliminate (.var .zero) Structural.nil)

def closeTypeVariable : Sub sig (scope 1) (scope 0) :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 0)
    (Structural.sortTerm (Structural.set (Structural.levelClosed 0)))

theorem dependent_annotation_observation :
    type dependentAnnotation = some (.el 1 (.var 0)) := rfl

theorem dependent_annotation_changes :
    type (bind closeTypeVariable dependentAnnotation) = some (.el 1 (.sort 0)) := rfl

def firstArgument : StaticSpecification.Term 1 := .sort 0
def secondArgument : StaticSpecification.Term 1 := .sort 1
def orderedSource : StaticSpecification.Term 1 :=
  .elim (.elim (.var 0) (.apply firstArgument)) (.apply secondArgument)

def orderedSpine : Structural.Spine (scope 1) :=
  Structural.append
    (Structural.cons (Structural.apply (embedTerm firstArgument)) Structural.nil)
    (Structural.cons (Structural.apply (embedTerm secondArgument)) Structural.nil)

def orderedAdministrative : Structural.Tm (scope 1) :=
  Structural.eliminate (.var .zero) orderedSpine

theorem applications_stay_in_order : term orderedAdministrative = some orderedSource := rfl

theorem append_raw_representation_differs : orderedAdministrative ≠ embedTerm orderedSource := by
  intro same
  cases same

theorem reversed_arguments_change_observation : term orderedAdministrative ≠
    some (StaticSpecification.Term.elim (.elim (.var 0) (.apply secondArgument)) (.apply firstArgument)) := by
  rw [applications_stay_in_order]
  intro same
  cases same

def identityApplication : Structural.Tm (scope 0) :=
  Structural.eliminate (Structural.lam (.var .zero))
    (Structural.cons (Structural.apply (Structural.sortTerm (Structural.set (Structural.levelClosed 0))))
      Structural.nil)

theorem beta_is_not_performed : term identityApplication =
    some (StaticSpecification.Term.elim (.lam (.bind (.var 0))) (.apply (.sort 0))) := rfl

theorem application_observation_is_not_its_beta_result : term identityApplication ≠ some (.sort 0) := by
  rw [beta_is_not_performed]
  intro same
  cases same

theorem noAbs_remains_distinct :
    term (Structural.lamNoAbs (.var .zero) : Structural.Tm (scope 1)) ≠
      term (Structural.lam (.var (.succ .zero)) : Structural.Tm (scope 1)) := by
  intro same
  cases same

theorem projection_is_unsupported :
    elim (Structural.proj "field" : Structural.Elim (scope 0)) = none := rfl

theorem projection_spine_is_unsupported :
    spine (Structural.append Structural.nil
      (Structural.cons (Structural.proj "field") Structural.nil) : Structural.Spine (scope 0)) = none := rfl

theorem nonfinite_annotation_is_unsupported :
    type (Structural.el (Structural.prop (Structural.levelClosed 0)) (.var .zero) : Structural.Ty (scope 1)) =
      none := rfl

def unsupportedSub : Sub sig (scope 1) (scope 0) :=
  Telescope.pair (Telescope.emptySub (S := sig) .term 0) (Structural.natLiteral 7)

theorem unsupported_image_has_no_source_substitution (τ : StaticSpecification.Substitution 1 0) :
    ¬ SubObserves unsupportedSub τ := by
  intro images
  have impossible := images 0
  cases impossible

theorem successful_input_can_lose_support_without_image_hypothesis :
    term (Term.var .zero : Structural.Tm (scope 1)) = some (.var 0) ∧
      term (bind unsupportedSub (Term.var .zero)) = none := ⟨rfl, rfl⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Observation.Controls
