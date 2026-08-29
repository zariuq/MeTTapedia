import Mettapedia.OSLF.Framework.SelectedNativeTypeCalculusCompiler
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationValidation
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.StructuralCategory

/-!
# The honest fit category for inverse native-type synthesis

An inverse-OSLF question starts with a desired calculus `blue` and asks for a
language presentation whose generated native type theory contains it.  Two
different issues must not be conflated:

1. In the unrestricted category of calculus embeddings, `blue` itself is a
   trivial initial fit.
2. The hard question is whether that fit lies in the essential image of a
   real language-indexed native-type generator, and whether one such generated
   fit is least among the generated fits.

This module makes that distinction explicit.  `FitCandidate blue` is the
coslice category of validated calculus languages under `blue`.
`GeneratedBySelectedNTT` is the additional essential-image predicate for the
current profile-sensitive contextual compiler.  The unrestricted identity
candidate is proved initial, but it is not declared generated.

The concrete non-root contextual canary supplies a nontrivial positive fit:
its validated carrier foundation embeds into the larger, profile-sensitive
calculus produced from a grounded rewrite occurrence.  A complementary
obstruction proves that no observation which factors through the
profile-forgetting signature can reconstruct the complete star/box-sensitive
output.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NativeTypeInverseFit

open CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework

/-! ## The unrestricted fit category -/

/-- A target calculus together with a structural embedding of the requested
calculus. -/
structure FitCandidate (blue : ValidatedCalculusLanguageDef) where
  output : ValidatedCalculusLanguageDef
  embedding : CalculusStructuralMorphism blue output

namespace FitCandidate

variable {blue : ValidatedCalculusLanguageDef}

/-- Maps between fits must commute with the chosen embedding of `blue`. -/
structure Hom (source target : FitCandidate blue) where
  arrow : CalculusStructuralMorphism source.output target.output
  commutes :
    CalculusStructuralMorphism.comp source.embedding arrow = target.embedding

@[ext]
theorem Hom.ext {source target : FitCandidate blue}
    {first second : Hom source target}
    (arrowEquality : first.arrow = second.arrow) :
    first = second := by
  cases first
  cases second
  cases arrowEquality
  rfl

private theorem structural_id_comp
    {source target : ValidatedCalculusLanguageDef}
    (morphism : CalculusStructuralMorphism source target) :
    CalculusStructuralMorphism.comp
        (CalculusStructuralMorphism.id source) morphism = morphism := by
  apply CalculusStructuralMorphism.ext
  exact CalculusLanguageSymbols.id_comp morphism.symbols

private theorem structural_comp_id
    {source target : ValidatedCalculusLanguageDef}
    (morphism : CalculusStructuralMorphism source target) :
    CalculusStructuralMorphism.comp morphism
        (CalculusStructuralMorphism.id target) = morphism := by
  apply CalculusStructuralMorphism.ext
  exact CalculusLanguageSymbols.comp_id morphism.symbols

private theorem structural_comp_assoc
    {first second third fourth : ValidatedCalculusLanguageDef}
    (earlier : CalculusStructuralMorphism first second)
    (middle : CalculusStructuralMorphism second third)
    (later : CalculusStructuralMorphism third fourth) :
    CalculusStructuralMorphism.comp
        (CalculusStructuralMorphism.comp earlier middle) later =
      CalculusStructuralMorphism.comp earlier
        (CalculusStructuralMorphism.comp middle later) := by
  apply CalculusStructuralMorphism.ext
  exact CalculusLanguageSymbols.comp_assoc
    earlier.symbols middle.symbols later.symbols

instance : CategoryTheory.Category (FitCandidate blue) where
  Hom := Hom
  id source :=
    { arrow := CalculusStructuralMorphism.id source.output
      commutes := structural_comp_id source.embedding }
  comp earlier later :=
    { arrow := CalculusStructuralMorphism.comp earlier.arrow later.arrow
      commutes := by
        rw [← structural_comp_assoc, earlier.commutes, later.commutes] }
  id_comp morphism := by
    apply Hom.ext
    exact structural_id_comp morphism.arrow
  comp_id morphism := by
    apply Hom.ext
    exact structural_comp_id morphism.arrow
  assoc first second third := by
    apply Hom.ext
    exact structural_comp_assoc first.arrow second.arrow third.arrow

/-- The desired calculus embedded in itself.  This is the trivial initial
object before any generated-image restriction is imposed. -/
def selfFit (blue : ValidatedCalculusLanguageDef) : FitCandidate blue where
  output := blue
  embedding := CalculusStructuralMorphism.id blue

/-- The canonical arrow from the unrestricted identity fit. -/
def fromIdentity (candidate : FitCandidate blue) :
    selfFit blue ⟶ candidate where
  arrow := candidate.embedding
  commutes := structural_id_comp candidate.embedding

/-- A classifying fit is initial in the selected candidate category. -/
def IsClassifying (candidate : FitCandidate blue) : Prop :=
  ∀ other, Nonempty (candidate ⟶ other) ∧ Subsingleton (candidate ⟶ other)

/-- The unrestricted fit problem is categorically trivial.  Therefore the
essential-image restriction is load-bearing, not optional terminology. -/
theorem selfFit_isClassifying (blue : ValidatedCalculusLanguageDef) :
    (selfFit blue).IsClassifying := by
  intro other
  constructor
  · exact ⟨fromIdentity other⟩
  · constructor
    intro first second
    apply Hom.ext
    have firstArrow : first.arrow = other.embedding := by
      have firstCommutes := first.commutes
      change CalculusStructuralMorphism.comp
          (CalculusStructuralMorphism.id blue) first.arrow =
        other.embedding at firstCommutes
      rw [structural_id_comp] at firstCommutes
      exact firstCommutes
    have secondArrow : second.arrow = other.embedding := by
      have secondCommutes := second.commutes
      change CalculusStructuralMorphism.comp
          (CalculusStructuralMorphism.id blue) second.arrow =
        other.embedding at secondCommutes
      rw [structural_id_comp] at secondCommutes
      exact secondCommutes
    exact firstArrow.trans secondArrow.symm

end FitCandidate

/-! ## Essential-image restriction -/

/-- The fit output is exactly an admitted result of the current selected,
profile-sensitive native-type compiler. -/
def GeneratedBySelectedNTT {blue : ValidatedCalculusLanguageDef}
    (candidate : FitCandidate blue) : Prop :=
  ∃ (source : ValidatedLanguageDef)
    (demand : SelectedNativeTypeDemand source)
    (valid :
      (SelectedNativeTypeCalculusCompiler.definition demand).isValid = true),
    candidate.output =
      ⟨SelectedNativeTypeCalculusCompiler.definition demand, valid⟩

/-- Initiality after restricting to real generated outputs.  Unlike the
unrestricted theorem, this property is not discharged by identity alone. -/
def IsClassifyingAmongGenerated {blue : ValidatedCalculusLanguageDef}
    (candidate : FitCandidate blue) : Prop :=
  GeneratedBySelectedNTT candidate ∧
    ∀ other, GeneratedBySelectedNTT other →
      Nonempty (candidate ⟶ other) ∧ Subsingleton (candidate ⟶ other)

/-! ## A nontrivial generated fit -/

namespace Canary

abbrev source : ValidatedLanguageDef :=
  ContextualModalSignature.Canary.source

abbrev demand : SelectedNativeTypeDemand
    ContextualModalSignature.Canary.source :=
  SelectedNativeTypeContextualCalculus.Canary.middleDemand .star

def foundation : ValidatedCalculusLanguageDef :=
  SelectedNativeTypeFoundation.validated demand.foundation

def output : ValidatedCalculusLanguageDef :=
  ⟨SelectedNativeTypeCalculusCompiler.definition demand,
    SelectedNativeTypeCalculusCompiler.Canary.middle_definition_valid⟩

/-- The single extension whose rows take the carrier foundation to the
grouped complete contextual calculus. -/
def contextualExtension : CalculusLanguageExtension :=
  (ContextualModalExtension.extension demand.foundation).comp
    ((ContextualCarrierClaims.extension
      (SelectedNativeTypeFoundation.stableCarrierNames
        demand.foundation)).comp
      (SelectedNativeTypeContextualCalculus.profileExtension demand))

theorem contextualExtension_apply :
    contextualExtension.apply
        (SelectedNativeTypeFoundation.definition demand.foundation) =
      SelectedNativeTypeCalculusCompiler.definition demand := by
  rw [SelectedNativeTypeCalculusCompiler.Canary.middle_definition_eq_contextual,
    SelectedNativeTypeContextualCalculus.Canary.middle_definition_eq_grouped]
  simp [contextualExtension,
    SelectedNativeTypeContextualCalculus.groupedDefinition,
    ContextualModalExtension.language, ContextualCarrierClaims.apply,
    CalculusLanguageExtension.comp_apply]

theorem foundation_appendOnly :
    CalculusLanguageExtension.AppendOnlyCalculusRefinement
      foundation.1 output.1 := by
  have refinement := CalculusLanguageExtension.apply_appendOnly
    contextualExtension
      (SelectedNativeTypeFoundation.definition demand.foundation)
  rw [contextualExtension_apply] at refinement
  exact refinement

/-- This inclusion is nontrivial: the target adds contextual constructors,
claims, and profile-sensitive inference rules to the carrier foundation. -/
def inclusion : CalculusStructuralMorphism foundation output :=
  CalculusStructuralMorphism.ofAppendOnly foundation_appendOnly

def generatedFit : FitCandidate foundation where
  output := output
  embedding := inclusion

theorem generatedFit_isGenerated :
    GeneratedBySelectedNTT generatedFit := by
  refine ⟨source, demand,
    SelectedNativeTypeCalculusCompiler.Canary.middle_definition_valid, ?_⟩
  rfl

/-- The fit is strictly larger at the raw row level: the contextual target
has more terms and more inference rules than the carrier foundation. -/
theorem generatedFit_adds_rows :
    foundation.1.terms.length < output.1.terms.length ∧
      foundation.1.rules.length < output.1.rules.length := by
  constructor
  · change
      (SelectedNativeTypeFoundation.definition demand.foundation).terms.length <
        (SelectedNativeTypeCalculusCompiler.definition demand).terms.length
    rw [SelectedNativeTypeFoundation.definition_term_count,
      SelectedNativeTypeContextualCalculus.Canary.middle_carrier_objects,
      SelectedNativeTypeCalculusCompiler.Canary.middle_definition_eq_contextual,
      SelectedNativeTypeContextualCalculus.Canary.middle_definition_eq_grouped,
      SelectedNativeTypeContextualCalculus.Canary.middle_grouped_terms_explicit]
    decide
  · change
      (SelectedNativeTypeFoundation.definition demand.foundation).rules.length <
        (SelectedNativeTypeCalculusCompiler.definition demand).rules.length
    rw [SelectedNativeTypeFoundation.definition_rules,
      SelectedNativeTypeContextualCalculus.Canary.middle_stableCarrierNames,
      SelectedNativeTypeCalculusCompiler.Canary.middle_definition_eq_contextual,
      SelectedNativeTypeContextualCalculus.Canary.middle_definition_eq_grouped,
      SelectedNativeTypeContextualCalculus.Canary.middle_grouped_rules]
    decide

end Canary

/-! ## Profile-forgetting obstruction -/

namespace ProfileObstruction

abbrev source : ValidatedLanguageDef :=
  ContextualModalSignature.Canary.source

/-- An observation really distinguishes the two local modal endpoints. -/
def SeparatesEndpoints {Observation : Sort _}
    (observe : CalculusLanguageDef → Observation) : Prop :=
  observe (SelectedNativeTypeCalculusCompiler.definition
      (SelectedNativeTypeContextualCalculus.Canary.middleDemand .star)) ≠
    observe (SelectedNativeTypeCalculusCompiler.definition
      (SelectedNativeTypeContextualCalculus.Canary.middleDemand .box))

/-- The observation depends only on the profile-forgetting signature. -/
def FactorsThroughSignature {Observation : Sort _}
    (observe : CalculusLanguageDef → Observation) : Prop :=
  ∃ reduced : CalculusLanguageDef → Observation,
    ∀ code : CarrierUniverseSignature.Code,
      observe (SelectedNativeTypeCalculusCompiler.definition
          (SelectedNativeTypeContextualCalculus.Canary.middleDemand code)) =
        reduced (SelectedNativeTypeContextualCalculus.signature
          (SelectedNativeTypeContextualCalculus.Canary.middleDemand code))

/-- Any endpoint-separating observation is obstructed from factoring through
the profile-free signature. -/
theorem separating_not_factorsThroughSignature {Observation : Sort _}
    (observe : CalculusLanguageDef → Observation)
    (separates : SeparatesEndpoints observe) :
    ¬ FactorsThroughSignature observe := by
  rintro ⟨reduced, factor⟩
  apply separates
  calc
    observe (SelectedNativeTypeCalculusCompiler.definition
        (SelectedNativeTypeContextualCalculus.Canary.middleDemand .star)) =
        reduced (SelectedNativeTypeContextualCalculus.signature
          (SelectedNativeTypeContextualCalculus.Canary.middleDemand .star)) :=
      factor .star
    _ = reduced (SelectedNativeTypeContextualCalculus.signature
          (SelectedNativeTypeContextualCalculus.Canary.middleDemand .box)) :=
      congrArg reduced
        SelectedNativeTypeContextualCalculus.Canary.middle_signatures_equal
    _ = observe (SelectedNativeTypeCalculusCompiler.definition
          (SelectedNativeTypeContextualCalculus.Canary.middleDemand .box)) :=
      (factor .box).symm

theorem complete_output_separates : SeparatesEndpoints id := by
  exact
    SelectedNativeTypeCalculusCompiler.Canary.middle_compiled_endpoints_distinct

/-- Negative control: the profile-free signature cannot reconstruct the
complete generated native-type calculus. -/
theorem complete_output_not_factorsThroughSignature :
    ¬ FactorsThroughSignature id :=
  separating_not_factorsThroughSignature id complete_output_separates

end ProfileObstruction

/-! ## Axiom audit -/

#print axioms FitCandidate.selfFit_isClassifying
#print axioms Canary.contextualExtension_apply
#print axioms Canary.foundation_appendOnly
#print axioms Canary.generatedFit_isGenerated
#print axioms Canary.generatedFit_adds_rows
#print axioms ProfileObstruction.separating_not_factorsThroughSignature
#print axioms ProfileObstruction.complete_output_not_factorsThroughSignature

end Mettapedia.OSLF.Framework.NativeTypeInverseFit
