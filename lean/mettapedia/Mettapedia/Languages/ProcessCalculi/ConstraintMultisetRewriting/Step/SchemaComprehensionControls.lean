import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SchemaComprehension
import Mettapedia.TypeTheory.ContextualSchemaControls

/-!
# Comprehension does not assume model lifting or closed inhabitation

In the actual set-family model, adjoining an empty fibre supplies a formed
context but no closed point. Symbolic solvability still has its identity
solution. Universal observations therefore cannot be reflected through
weakening without the appropriate model-lifting hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.SchemaComprehension.Controls

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory
open ContextualSchemaTelescopes

abbrev model := familiesCwf.{0}
abbrev frame := NativeUniverse.cwfFrames model

def emptyHelper : Extension model Unit := .cons (fun _ => Empty) (.nil _)

theorem symbolic_empty_helper_is_solvable :
    frame.Solvable ([] : EquationStore (NativeUniverse.Judged model emptyHelper.target)) :=
  ⟨emptyHelper.target, frame.id emptyHelper.target, Frames.models_nil _⟩

theorem no_closed_empty_helper : ¬ Nonempty (model.Sub Unit emptyHelper.target) := by
  rintro ⟨point⟩
  exact (point ()).2.elim

/-- The weakening's closed old model has no lift to a helper assignment. -/
theorem weakening_does_not_lift_every_model :
    ¬ (∀ substitution : model.Sub Unit Unit,
      ∃ lift : model.Sub Unit emptyHelper.target,
        model.compS emptyHelper.weaken lift = substitution) := by
  intro lifts
  obtain ⟨lift, _⟩ := lifts (fun point => point)
  exact no_closed_empty_helper ⟨lift⟩

/-- Every solution of the extended context has an empty domain. -/
theorem extended_entails_empty_domain :
    frame.Entails ([] : EquationStore (NativeUniverse.Judged model emptyHelper.target))
      (fun destination _ => IsEmpty destination) := by
  intro destination substitution _
  exact ⟨fun value => (substitution value).2.elim⟩

theorem base_does_not_entail_empty_domain :
    ¬ frame.Entails ([] : EquationStore (NativeUniverse.Judged model Unit))
      (fun destination _ => IsEmpty destination) := by
  intro holds
  have empty := holds Unit (fun point => point) (Frames.models_nil _)
  exact empty.false ()

/-- The observation pulls back along weakening, yet its universal verdict
changes. A universal context extension alone is not a conservativity license. -/
theorem universal_guard_reflection_needs_lifting :
    frame.Entails ([] : EquationStore (NativeUniverse.Judged model emptyHelper.target))
        (fun destination _ => IsEmpty destination) ∧
      ¬ frame.Entails ([] : EquationStore (NativeUniverse.Judged model Unit))
        (fun destination _ => IsEmpty destination) :=
  ⟨extended_entails_empty_domain, base_does_not_entail_empty_domain⟩

section Presheaf

open CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafCwf

universe u v w

variable (Syntax : Type u) [Category.{v} Syntax]

/-- Relative schema comprehension instantiated in the existing, proof-relevant
displayed-presheaf CwF, with natural substitutions and actual dependent sections. -/
def presheafOpeningEquiv {base : (presheafCwf.{u, v, w} Syntax).Ctx}
    (telescope : Extension (presheafCwf.{u, v, w} Syntax) base)
    (source : (presheafCwf.{u, v, w} Syntax).Ctx) :
    (presheafCwf.{u, v, w} Syntax).Sub source telescope.target ≃
      telescope.Assignment source := telescope.comprehensionEquiv source

theorem presheaf_opening_preserves_the_base
    {base source : (presheafCwf.{u, v, w} Syntax).Ctx}
    (telescope : Extension (presheafCwf.{u, v, w} Syntax) base)
    (substitution : (presheafCwf.{u, v, w} Syntax).Sub source telescope.target) :
    (presheafOpeningEquiv Syntax telescope source substitution).1 =
      (presheafCwf.{u, v, w} Syntax).compS telescope.weaken substitution :=
  telescope.decompose_base substitution

end Presheaf

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.SchemaComprehension.Controls
