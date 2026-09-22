import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalProfile
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionConservativeExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ConservativeConversion

/-!
# Exact conversion boundary of the extensional HOL profile

The extensional HOL profile adds two formed proof constants but no reduction
rules.  This module proves the precise consequence: the profile has exactly
the base proof calculus's contextual conversion relation, while its typing
relation is intentionally stronger because the two new constants are
available.  Thus extensionality is an explicit object-theory capability, not
an equation silently installed in the intensional kernel.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalConservativity

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLExtensionalProfile

variable {n : Nat}

/-- Every declaration in the profile is opaque. -/
theorem declarations_opaque (name : DeclName) :
    declarations.valueOf? name = none := by
  by_cases functionEqual : name = functionExtensionalityName
  · subst name
    rfl
  by_cases propositionEqual : name = propositionExtensionalityName
  · subst name
    simp [declarations, Signature.valueOf?, Signature.insert,
      functionExtensionalityName, propositionExtensionalityName]
  · simpa [declarations, Signature.valueOf?, Signature.insert,
      functionEqual, propositionEqual] using
      FormationSensitiveHOLProofConversion.declarations_opaque name

/-- Root steps are unchanged: both packages carry the same proof-family
decoder steps, and neither can unfold an opaque declaration. -/
theorem root_iff {left right : Tower.Tm n} :
    rules.computation.step left right ↔
      baseRules.computation.step left right := by
  constructor
  · intro root
    cases root with
    | inherited inherited => exact RootStep.inherited inherited
    | delta lookup => rw [declarations_opaque] at lookup; cases lookup
    | declared declared => exact RootStep.declared declared
  · intro root
    cases root with
    | inherited inherited => exact RootStep.inherited inherited
    | delta lookup =>
        rw [FormationSensitiveHOLProofConversion.declarations_opaque] at lookup
        cases lookup
    | declared declared => exact RootStep.declared declared

/-- The profile changes available proof constants, but not judgmental
conversion. -/
theorem conservative : ConversionConservativeExtension baseRules rules where
  headEq_eq := rfl
  root_inclusion {n} {left} {right} root :=
    (root_iff (n := n) (left := left) (right := right)).mpr root
  root_sound {n} {left} {right} root :=
    .rel left right (.root ((root_iff (n := n) (left := left) (right := right)).mp root))

theorem conversion_iff (left right : Tower.Tm n) :
    Conv baseRules.headEq left right baseRules.computation ↔
      Conv rules.headEq left right rules.computation :=
  conservative.conversion_iff left right

/-- Every old typing derivation is still accepted. -/
theorem base_typing_preserved {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing baseRules context term type) :
    Typing rules context term type :=
  include_typed typed

/-- The converse typing implication is false for the intended reason: the
profile really introduces a proposition-extensionality proof constant. -/
theorem proposition_extensionality_is_new (context : Tower.Ctx n) :
    Typing rules context (.const propositionExtensionalityName)
        (liftClosed propositionExtensionalityType) ∧
      ¬ ∃ type, Typing baseRules context
        (.const propositionExtensionalityName) type := by
  refine ⟨propositionExtensionality_typed context, ?_⟩
  rintro ⟨type, typed⟩
  obtain ⟨_, _, lookup, _, _⟩ := typed.constFormation
  rw [Controls.proposition_extensionality_absent_from_base] at lookup
  cases lookup

/-- Function extensionality is likewise absent when the profile is removed. -/
theorem function_extensionality_is_new (context : Tower.Ctx n) :
    Typing rules context (.const functionExtensionalityName)
        (liftClosed functionExtensionalityType) ∧
      ¬ ∃ type, Typing baseRules context
        (.const functionExtensionalityName) type := by
  refine ⟨functionExtensionality_typed context, ?_⟩
  rintro ⟨type, typed⟩
  obtain ⟨_, _, lookup, _, _⟩ := typed.constFormation
  rw [Controls.function_extensionality_absent_from_base] at lookup
  cases lookup

#print axioms declarations_opaque
#print axioms root_iff
#print axioms conservative
#print axioms conversion_iff
#print axioms base_typing_preserved
#print axioms proposition_extensionality_is_new
#print axioms function_extensionality_is_new

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalConservativity
