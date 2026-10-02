import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteraction
import Mettapedia.GSLT.LanguageDef.ConstructorSupportTransport
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding

/-!
# Code admission excludes authority at the current Cost layer

The wrapped sort admits both signed code and funding. Consequently sorting
alone cannot license arbitrary copying of a wrapped argument. The existing
constructor-support predicate supplies a separate, executable code check.

The check excludes the current layer's funding constructor throughout literal
syntax, including suspended or quoted syntax. It is stronger than absence of
an active purse. Translation to a fresh base namespace turns a prior layer's
apparatus into source code; it does not grant authority in the new layer.
Source-layer authority still needs its own invariant when interpreted at that
layer. The namespace comparison is syntactic and does not supply iteration closure
or an operational correspondence between the two layers.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open WellSorted

set_option autoImplicit false

/-- Code may mention every constructor except current-layer funding. -/
def CurrentLayerCode (pattern : Pattern) : Prop :=
  ConstructorsWithin (fun label => label ≠ costFundingConstructorName) pattern

/-- Admission reuses the generic executable constructor-support check. -/
def checkCurrentLayerCode (pattern : Pattern) : Bool :=
  checkConstructorsWithin (fun label => label != costFundingConstructorName) pattern

theorem checkCurrentLayerCode_iff (pattern : Pattern) :
    checkCurrentLayerCode pattern = true ↔ CurrentLayerCode pattern := by
  simpa only [checkCurrentLayerCode, CurrentLayerCode, bne_iff_ne] using
    checkConstructorsWithin_eq_true_iff
      (fun label => label != costFundingConstructorName) pattern

/-- Any authored syntax can be represented in the new base namespace without
manufacturing authority of the new layer. -/
theorem base_translation_currentLayerCode (pattern : Pattern) :
    CurrentLayerCode (mapPattern costBaseLanguageDefSymbolMap pattern) := by
  exact constructorsWithin_mapPattern_of_range costBaseLanguageDefSymbolMap
    (fun label => costBaseConstructorName_ne_apparatus label "funding") pattern

/-- Finite contractum decoration uses only base and wrapped source labels;
neither namespace is a current-layer funding declaration. -/
theorem contractum_translation_currentLayerCode {theory : IGSLT}
    {cut : InteractionCutPresentation theory} (profile : ContinuationDecorationProfile cut)
    (pattern : Pattern) : CurrentLayerCode (profile.mapContractum pattern) := by
  apply constructorsWithin_mapPattern_of_range profile.contractumSymbols _ pattern
  intro label
  change (if label ∈ profile.wrappedLabels then costWrappedConstructorName label
    else costBaseConstructorName label) ≠ costFundingConstructorName
  split
  · exact costWrappedConstructorName_ne_apparatus label "funding"
  · exact costBaseConstructorName_ne_apparatus label "funding"

/-- Opening a code-only continuation with code-only payload cannot introduce
funding at any retained local binder depth. -/
theorem CurrentLayerCode.instantiateBVarAt {body replacement : Pattern}
    (bodyCode : CurrentLayerCode body) (replacementCode : CurrentLayerCode replacement)
    (depth : Nat) : CurrentLayerCode (instantiateBVarAt depth replacement body) :=
  constructorsWithin_instantiateBVarAt bodyCode replacementCode depth

/-- Typing and authority separation survive the same actual binder elimination. -/
theorem typed_code_instantiateBVar {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {body replacement : Pattern} {domain result : TypeExpr}
    (bodyTyped : HasType language free (domain :: bound) body result)
    (replacementTyped : HasType language free bound replacement domain)
    (bodyCode : CurrentLayerCode body) (replacementCode : CurrentLayerCode replacement) :
    HasType language free bound (instantiateBVar replacement body) result ∧
      CurrentLayerCode (instantiateBVar replacement body) :=
  ⟨bodyTyped.instantiateBVar replacementTyped,
    bodyCode.instantiateBVarAt replacementCode 0⟩

/-- Ordinary relational matching takes its binding images from the matched
code. Applying those images to a code-only schema cannot introduce funding.
This support law does not identify matcher substitution with structural
substitution or with a reflective substitution policy. -/
theorem CurrentLayerCode.applyMatchedBindings {schema redex contractum : Pattern}
    {bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
    (matched : Mettapedia.OSLF.MeTTaIL.MatchSpec.MatchRel schema redex bindings)
    (redexCode : CurrentLayerCode redex) (contractumCode : CurrentLayerCode contractum) :
    CurrentLayerCode (Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings contractum) :=
  constructorsWithin_applyBindings contractumCode (matchRel_bindingsWithin matched redexCode)

theorem funding_not_currentLayerCode (stack : Pattern) :
    ¬ CurrentLayerCode (.apply costFundingConstructorName [stack]) :=
  fun code => code.1 rfl

/-- A prior-layer purse becomes ordinary authored code under base translation.
Keeping the unrenamed purse instead would fail the current-layer code check. -/
theorem prior_layer_funding_is_code (stack : Pattern) :
    CurrentLayerCode (mapPattern costBaseLanguageDefSymbolMap
      (.apply costFundingConstructorName [stack])) ∧
    ¬ CurrentLayerCode (.apply costFundingConstructorName [stack]) :=
  ⟨base_translation_currentLayerCode _, funding_not_currentLayerCode stack⟩

/-- The wrapped sort deliberately includes a purse, so it does not by itself
establish the separate duplicable-code admission predicate. -/
theorem wrapped_typing_does_not_imply_code {theory : IGSLT}
    {cut : InteractionCutPresentation theory} (profile : ContinuationDecorationProfile cut) :
    ∃ pattern, HasSort profile.costCoreLanguage FreeTypeContext.empty [] pattern
      costWrappedSortName ∧ ¬ CurrentLayerCode pattern := by
  refine ⟨.apply costFundingConstructorName
    [.apply costTokenStackEmptyConstructorName []], ?_, funding_not_currentLayerCode _⟩
  apply CostApparatus.funding_hasType
    (profile.apparatus_mem_costCore _ (by simp [costCoreConstructors]))
  apply HasType.constructor
    (profile.apparatus_mem_costCore costTokenStackEmptyConstructor (by simp [costCoreConstructors]))
  · simp [UsesBareCollection, costTokenStackEmptyConstructor]
  · exact .nil

#print axioms typed_code_instantiateBVar
#print axioms prior_layer_funding_is_code
#print axioms wrapped_typing_does_not_imply_code

end Mettapedia.GSLT.LanguageDef.Cost
