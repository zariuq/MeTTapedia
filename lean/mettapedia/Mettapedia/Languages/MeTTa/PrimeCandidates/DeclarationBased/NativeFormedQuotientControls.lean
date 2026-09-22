import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient
import Mathlib.CategoryTheory.Quotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedContextControls

/-! # Concrete controls for conversion quotient of formed substitutions -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual
open _root_.CategoryTheory FormationSensitive
/-! ## Exact positive and noncollapsed common-package controls -/

namespace QuotientControls

open NativeRelatorConversionParallel

/-- The section relation retains the actual common-package conversion of
the newest component, ready for dependent reindexing consumers. -/
theorem mixed_projection_homConversion (wire : NativeWireData.Wire) :
    homConversion HOLNativeRelatorCompatibility.rules
      (Common.sectionHom (Common.projected wire)) (Common.sectionHom (Common.result wire)) := by
  apply homConversion_pair (homConversion_refl _)
  simpa only [Term.cast_code] using Common.projected_converts_result wire

/-- The actual native computation changes raw syntax, but not the section
in the quotient of admitted substitutions. -/
theorem mixed_projection_sections_equal (wire : NativeWireData.Wire) :
    (quotientProjection HOLNativeRelatorCompatibility.rules).map
        (Common.sectionHom (Common.projected wire)) =
      (quotientProjection HOLNativeRelatorCompatibility.rules).map
        (Common.sectionHom (Common.result wire)) :=
  (quotientProjection_map_eq_iff _ _).mpr (mixed_projection_homConversion wire)

theorem mixed_section_is_a_genuine_identification :
    Common.sectionHom (Common.projected (.natural 7)) ≠
        Common.sectionHom (Common.result (.natural 7)) ∧
      (quotientProjection HOLNativeRelatorCompatibility.rules).map
          (Common.sectionHom (Common.projected (.natural 7))) =
        (quotientProjection HOLNativeRelatorCompatibility.rules).map
          (Common.sectionHom (Common.result (.natural 7))) :=
  ⟨Common.converted_sections_distinct, mixed_projection_sections_equal _⟩

private theorem parStar_const_eq {n : Nat} {name : DeclName} {target : Tower.Tm n}
    (steps : ParStar (.const name) target) : target = .const name := by
  induction steps with
  | refl => rfl
  | tail _ finalStep ih =>
      rw [ih] at finalStep
      cases finalStep
      rfl

/-- Opacity and the existing native common-reduct theorem, not a global
assumption about every possible rule package, separate constant names. -/
theorem opaque_constants_conversion_iff {signature : Declaration.Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature) {n : Nat} (first second : DeclName) :
    Conv (OpaqueRelatorExtension.rules signature).headEq
        (.const first : Tower.Tm n) (.const second)
        (OpaqueRelatorExtension.rules signature).computation ↔ first = second := by
  constructor
  · intro converted
    obtain ⟨common, firstSteps, secondSteps⟩ :=
      conversion_join ((OpaqueRelatorExtension.conversion_iff opacity).mp converted)
    exact Tm.const.inj ((parStar_const_eq firstSteps).symm.trans (parStar_const_eq secondSteps))
  · rintro rfl
    exact .refl _

theorem natural_conversion_iff {n : Nat} (first second : Nat) :
    Conv HOLNativeRelatorCompatibility.rules.headEq
        (NativeWireData.encode (n := n) (.natural first)) (NativeWireData.encode (.natural second))
        HOLNativeRelatorCompatibility.rules.computation ↔ first = second := by
  constructor
  · intro converted
    simp only [NativeWireData.encode] at converted
    have names := (opaque_constants_conversion_iff (n := n) HOLNativeRelatorCompatibility.opacity
      (.num NativeWireData.naturalPrefix first) (.num NativeWireData.naturalPrefix second)).mp converted
    exact (Lean.Name.num.inj names).2
  · rintro rfl
    exact .refl _

theorem natural_sections_equal_iff (first second : Nat) :
    (quotientProjection HOLNativeRelatorCompatibility.rules).map
        (Common.sectionHom (Common.result (.natural first))) =
      (quotientProjection HOLNativeRelatorCompatibility.rules).map
        (Common.sectionHom (Common.result (.natural second))) ↔ first = second := by
  constructor
  · intro same
    have component := ((quotientProjection_map_eq_iff _ _).mp same) 0
    apply (natural_conversion_iff (n := Common.context.arity) first second).mp
    simpa only [Common.sectionHom, pair, consSub_zero, Term.cast_code, Common.result] using component
  · rintro rfl
    rfl

theorem seven_and_eight_remain_distinct :
    (quotientProjection HOLNativeRelatorCompatibility.rules).map
        (Common.sectionHom (Common.result (.natural 7))) ≠
      (quotientProjection HOLNativeRelatorCompatibility.rules).map
        (Common.sectionHom (Common.result (.natural 8))) := by
  intro same
  have impossible := (natural_sections_equal_iff 7 8).mp same
  cases impossible

end QuotientControls
end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
