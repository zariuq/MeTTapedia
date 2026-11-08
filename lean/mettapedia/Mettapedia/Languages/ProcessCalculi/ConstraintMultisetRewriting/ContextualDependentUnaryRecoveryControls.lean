import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUnaryConstancy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextNormalizationControls

/-!
# Constraint-forced extraction, beta erasure, and rigid arguments

The typed body (lambda z.m) x initially mentions the local x and fails raw
inversion. Equality at two independent arguments is proved by beta. Actual
normalization and extraction return the existing outer m. An identity body
cannot satisfy the same constraint, even when its argument type has no
supplied closed inhabitant. Unnormalized context declarations are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUnaryRecovery.Controls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUnaryScope

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal

abbrev outer := ContextualDependentInversion.Controls.small
abbrev type := ContextualDependentInversion.Controls.expected
abbrev source := extend outer type

theorem function_formed : Typed Tower.rules source.raw (.pi (.var 2) (.var 3))
    (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (.var 2) (.sort _) (.var 3) (.sort _) (.sorts _ _)

def value : Term source (type.reindex (projectionHom outer type)) :=
  ⟨.app (.lam (.var 2)) (.var 0), Derivable.appElim (R := Tower.rules) (A := .var 2) (B := .var 3)
    (.lamIntro function_formed (.sort _) (.var 2)) (.var 0)⟩

theorem beta : Equal Tower.rules source.raw value.code (.var 1) (type.reindex (projectionHom outer type)).code :=
  .betaPi function_formed (.sort _) (.var 2) (.var 0)

theorem equation : Equal Tower.rules (twice (S := setting) outer type).raw
    (Presentation.rename wk value.code) (Presentation.rename (liftRen wk) value.code)
    (Presentation.rename wk (type.reindex (projectionHom outer type)).code) := by
  have first := beta.rename (left_compatible (S := setting) outer type)
  have second := beta.rename (right_compatible (S := setting) outer type)
  have second' : Equal Tower.rules (twice (S := setting) outer type).raw
      (Presentation.rename (liftRen wk) value.code) (.var (2 : Fin 4))
      (Presentation.rename wk (type.reindex (projectionHom outer type)).code) :=
    (codomain_images (S := setting) outer type type) ▸ second
  exact first.trans second'.symm

def run (fuel : Nat) := ContextualDependentUnaryConstancy.recover (fun _ => (0 : Nat)) fuel outer type type value equation
def result := (run 2).get (by decide +kernel)

theorem raw_inversion_does_not_finish :
    ContextualDependentInversion.invert (ContextualDependentInversion.lookup (wk : Ren 2 3)) value.code = none := by rfl'

theorem actual_outer_value_extracted : result.body.code = .var 0 := by rfl'

theorem solves_original_erasing_body :
    (frames setting.levels).E (TotalTerm.reindex (⟨type, result.body⟩ : TotalTerm outer) (projectionHom outer type))
      (⟨_, value⟩ : TotalTerm source) := result.solves

theorem one_step_budget_is_unfinished : run 1 = none := by rfl'

namespace Identity

def ground : TypeOver (empty Tower.rules) := ⟨.head .legacyGround, .sort Tower.zero, .sort _, .headType .legacyGround⟩
def value : Term (extend (empty Tower.rules) ground) (ground.reindex (projectionHom _ ground)) := ⟨.var 0, .var 0⟩

theorem no_argument_independence : ¬ Equal Tower.rules (twice (S := setting) (empty Tower.rules) ground).raw
    (Presentation.rename wk value.code) (Presentation.rename (liftRen wk) value.code)
    (Presentation.rename wk (ground.reindex (projectionHom _ ground)).code) := by
  intro same
  have impossible := inverse_forced (S := setting) rigid TowerModel.complete
    (empty Tower.rules) ground ground value (normal _ (by rfl')) same
  change false = true at impossible
  cases impossible

end Identity

namespace UnnormalizedPrefix

abbrev outer := ContextualDependentContextNormalization.Controls.values
abbrev type := ContextualDependentContextNormalization.Controls.carrier
def value : Term (extend outer type) (type.reindex (projectionHom outer type)) := ⟨.var 1, .var 1⟩

theorem equation : Equal Tower.rules (twice (S := setting) outer type).raw
    (Presentation.rename wk value.code) (Presentation.rename (liftRen wk) value.code)
    (Presentation.rename wk (type.reindex (projectionHom outer type)).code) :=
  .refl (value.typed.rename (left_compatible (S := setting) outer type))

def result := (ContextualDependentUnaryConstancy.recover (fun _ => (0 : Nat)) 1 outer type type value equation).get
  (by decide +kernel)

theorem annotation_still_needs_reduction :
    ExecutableReduction.normalize Tower.rules (fun _ => none) 1 type.code = none := by rfl'

theorem existing_outer_obligation_is_recovered : result.body.code = .var 0 := by rfl'

theorem original_expected_type_is_retained : Typed Tower.rules outer.raw result.body.code type.code := result.body.typed

end UnnormalizedPrefix
end ContextualDependentUnaryRecovery.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
