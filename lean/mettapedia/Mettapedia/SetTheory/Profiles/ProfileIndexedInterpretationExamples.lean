import Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretationFragments
import Mettapedia.SetTheory.Profiles.ProfileIndexedCalculusDependencies

/-!
# Deductions, expansion and evidence controls on the constructed profiles

The containment macro expands a nontrivial authored quantified proof from
Pairing, and is interpreted in the varying graph model. Local-hypothesis
cut protects a universal binder. Duplicate assumptions have the same
formula but different evidence origins, and a derived-rule extension
cannot make Foundation or excluded middle derivable in the common profile.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula weakenFormula)
open GraphRealizedDeduction (Proof)
open ProfileIndexedCalculus

universe u

def containment : Derivation commonProfile [] CommonCore.containmentTheorem :=
  commonEmbedding.derivation (fromCommonCore CommonCore.containmentDerivation)

def containmentMacro : Derivation (withDerivedRules commonProfile) [] CommonCore.containmentTheorem :=
  Derivation.adopt 17 (.primitive (.derived 42 containment))

def expandedContainment : Derivation commonProfile [] CommonCore.containmentTheorem :=
  derived_conservative containmentMacro

/-- The call-site macro origin is distinct from the adopted Pairing origin
retained in its earlier proof. The expansion exposes the latter. -/
theorem containment_macro_origin : containmentMacro.origins = [17] := rfl

theorem expanded_containment_origin : expandedContainment.origins = [0] := rfl

theorem expanded_containment_rule :
    expandedContainment.declarations.map (fun declaration => declaration.adoption.name) =
      [CommonCore.LawName.pairing] := rfl

def containmentRealizer {D : Type u} [Category.{u} D] (point : D)
    (environment : ContextualGraphFormulaRealization.Environment D 0 point) :
    ContextualGraphFormulaRealization.realize D CommonCore.containmentTheorem point environment :=
  contextualClosed expandedContainment point environment

def quantifiedLocalProof : Proof ([Formula.equal 0 0] : List (Formula 1))
    (.all (.equal 1 1)) :=
  .allIntro (.hypothesis (assumptions := [weakenFormula (Formula.equal 0 0 : Formula 1)]) 0)

/-- Hypothesis substitution crosses the universal binder by weakening
the supplied reflexivity proof, rather than capturing the new variable. -/
def quantifiedCut : Proof ([] : List (Formula 1)) (.all (.equal 1 1)) :=
  substituteHypotheses quantifiedLocalProof
    (Fin.cases (Proof.equalRefl 0) (fun index => Fin.elim0 index))

theorem quantifiedCut_uses_no_assumptions : hypothesisPositions quantifiedCut = [] := rfl

def quantifiedCutRealizer {D : Type u} [Category.{u} D] (point : D)
    (environment : ContextualGraphFormulaRealization.Environment D 1 point) :
    ContextualGraphFormulaRealization.realize D (.all (.equal 1 1)) point environment :=
  ContextualGraphRealizedDeduction.closed quantifiedCut point environment

theorem derived_rules_do_not_enable_foundation :
    ¬ Nonempty (Derivation (withDerivedRules commonProfile) [] CommonCore.foundationAxiom) := by
  rintro ⟨proof⟩
  exact contextual_foundation_not_derived ⟨derived_conservative proof⟩

theorem derived_rules_do_not_enable_excluded_middle :
    ¬ Nonempty (Derivation (withDerivedRules commonProfile) []
      ContextualGraphRealizedDeductionControls.excludedMiddle) := by
  rintro ⟨proof⟩
  exact contextual_excluded_middle_not_derived ⟨derived_conservative proof⟩

def foundationToClassicalFoundation : Translation
    (fragmentProfile .foundation) (fragmentProfile .classicalFoundation) :=
  fragmentTranslation ⟨fun _ => rfl, fun impossible => Bool.noConfusion impossible⟩

def classicalToClassicalFoundation : Translation
    (fragmentProfile .classical) (fragmentProfile .classicalFoundation) :=
  fragmentTranslation ⟨fun impossible => Bool.noConfusion impossible, fun _ => rfl⟩

theorem foundation_translation_preserves_origin :
    (foundationToClassicalFoundation.derivation foundationDerivation).origins = [0] := rfl

/-- Deriving Foundation at the stronger endpoint does not establish a
backward interpretation into the common constructive endpoint. -/
theorem stronger_profile_still_has_no_common_translation :
    ¬ Nonempty (Translation (fragmentProfile .classicalFoundation) commonProfile) := by
  rintro ⟨translation⟩
  exact contextual_foundation_not_derived
    ⟨translation.derivation (foundationToClassicalFoundation.derivation foundationDerivation)⟩

end Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation
