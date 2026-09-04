import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Source-preserving coproduct with a generated calculus

A generated native-type calculus owns both an object signature and a proof
calculus.  Attaching only its judgments and rules loses the constructors used
by those rules, while appending only its object language loses derivability.
This module performs both operations as one structural construction.

The authored source is the left summand and remains byte-for-byte unchanged.
Every namespace of the generated right summand is mapped explicitly before
its rows are appended.  `Compatibility` exposes the finite admission checks
at the resulting boundary; it does not replace them with a raw-list axiom.
The output is one ordinary validated `CalculusLanguageDef`, together with
structural inclusions of the source language and the complete generated
calculus.

The present construction intentionally accepts generated calculi without a
rooted conversion authority.  A conversion root is unique global authority,
not an appendable row, and requires a separate conflict-resolution policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private theorem map_eq_self_of_mem {α : Type*} (function : α → α)
    (elements : List α)
    (fixed : ∀ element ∈ elements, function element = element) :
    elements.map function = elements := by
  calc
    elements.map function = elements.map _root_.id :=
      List.map_congr_left fixed
    _ = elements := List.map_id elements

/-- The authored language with an empty proof-calculus fibre. -/
def sourceBase (source : ValidatedLanguageDef) : CalculusLanguageDef :=
  CalculusLanguageDef.extend source.language ProofCalculus.empty

/-- An authored language with no inference rows is admitted exactly through
its existing `LanguageDef` validation evidence. -/
theorem sourceBase_valid (source : ValidatedLanguageDef) :
    (sourceBase source).isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  simp [sourceBase, ProofCalculus.empty,
    CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid, source.valid]

/-- Proof-carrying empty-calculus view of the authored source. -/
def validatedSourceBase (source : ValidatedLanguageDef) :
    ValidatedCalculusLanguageDef :=
  ⟨sourceBase source, sourceBase_valid source⟩

/-- Structural action on the proof-calculus coordinate.  Constructor names
inside judgments follow the ordinary presentation map, while judgment heads
and rule identifiers use their dedicated namespaces. -/
def reindexProofCalculus (symbols : CalculusLanguageSymbols)
    (calculus : ProofCalculus) : ProofCalculus where
  judgments := calculus.judgments.map (mapJudgmentDecl symbols)
  rules := calculus.rules.map (mapRuleSchema symbols)
  conversion := calculus.conversion.map (mapConversionDecl symbols)

/-- One source-preserving extension containing every reindexed row of the
generated flat calculus except its separately governed conversion root. -/
def extension (symbols : CalculusLanguageSymbols)
    (generated : ValidatedCalculusLanguageDef) :
    CalculusLanguageExtension where
  newTypes := generated.1.types.map
    (mapTypeDecl symbols.toLanguageDefSymbolMap)
  newTerms := generated.1.terms.map
    (mapGrammarRule symbols.toLanguageDefSymbolMap)
  newEquations := generated.1.equations.map
    (mapEquation symbols.toLanguageDefSymbolMap)
  newRewrites := generated.1.rewrites.map
    (mapRewriteRule symbols.toLanguageDefSymbolMap)
  newJudgments := generated.1.judgments.map (mapJudgmentDecl symbols)
  newRules := generated.1.rules.map (mapRuleSchema symbols)

@[simp] theorem extension_id_types
    (generated : ValidatedCalculusLanguageDef) :
    (extension CalculusLanguageSymbols.id generated).newTypes =
      generated.1.types := by
  exact map_eq_self_of_mem _ _ fun declaration _ => mapTypeDecl_id declaration

@[simp] theorem extension_id_terms
    (generated : ValidatedCalculusLanguageDef) :
    (extension CalculusLanguageSymbols.id generated).newTerms =
      generated.1.terms := by
  exact map_eq_self_of_mem _ _ fun declaration _ =>
    mapGrammarRule_id declaration

@[simp] theorem extension_id_equations
    (generated : ValidatedCalculusLanguageDef) :
    (extension CalculusLanguageSymbols.id generated).newEquations =
      generated.1.equations := by
  exact map_eq_self_of_mem _ _ fun declaration _ => mapEquation_id declaration

@[simp] theorem extension_id_rewrites
    (generated : ValidatedCalculusLanguageDef) :
    (extension CalculusLanguageSymbols.id generated).newRewrites =
      generated.1.rewrites := by
  exact map_eq_self_of_mem _ _ fun declaration _ =>
    mapRewriteRule_id declaration

@[simp] theorem extension_id_judgments
    (generated : ValidatedCalculusLanguageDef) :
    (extension CalculusLanguageSymbols.id generated).newJudgments =
      generated.1.judgments := by
  exact map_eq_self_of_mem _ _ fun declaration _ =>
    mapJudgmentDecl_id declaration

@[simp] theorem extension_id_rules
    (generated : ValidatedCalculusLanguageDef) :
    (extension CalculusLanguageSymbols.id generated).newRules =
      generated.1.rules := by
  exact map_eq_self_of_mem _ _ fun declaration _ =>
    mapRuleSchema_id declaration

/-- The single flat result before admission evidence is attached. -/
def definition (source : ValidatedLanguageDef)
    (symbols : CalculusLanguageSymbols)
    (generated : ValidatedCalculusLanguageDef) : CalculusLanguageDef :=
  (extension symbols generated).apply (sourceBase source)

/-- Exact, decomposed admission obligations for the one-sided coproduct.
These are the ordinary checker boundaries, plus disjointness and the explicit
new-judgment conservativity policy needed by extension clients. -/
structure Compatibility (source : ValidatedLanguageDef)
    (symbols : CalculusLanguageSymbols)
    (generated : ValidatedCalculusLanguageDef) : Prop where
  generatedConversionNone : generated.1.conversion = none
  generatedEquationsEmpty : generated.1.equations = []
  generatedRewritesEmpty : generated.1.rewrites = []
  disjoint : (extension symbols generated).disjointFrom
    (sourceBase source) = true
  policy : (extension symbols generated).policyHolds
    (sourceBase source) .newJudgmentsOnly = true
  languageValid :
    (definition source symbols generated).toLanguageDef.validate = []
  rulesLocallyValid :
    (definition source symbols generated).rules.all
      RuleSchema.isLocallyValid = true
  ruleIdsUnique :
    (((definition source symbols generated).ruleIds.eraseDups.length ==
      (definition source symbols generated).ruleIds.length) = true)
  judgmentSignatureValid :
    (definition source symbols generated).judgmentSignatureValid = true
  rulesValidIn :
    (definition source symbols generated).rules.all
      (RuleSchema.isValidIn (definition source symbols generated)) = true

namespace Compatibility

variable {source : ValidatedLanguageDef}
  {symbols : CalculusLanguageSymbols}
  {generated : ValidatedCalculusLanguageDef}

/-- The decomposed compatibility boundary implies complete admission by the
ordinary flat-calculus validator. -/
theorem target_valid
    (compatible : Compatibility source symbols generated) :
    (definition source symbols generated).isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [compatible.languageValid, compatible.rulesLocallyValid,
    compatible.ruleIdsUnique, compatible.judgmentSignatureValid,
    compatible.rulesValidIn]
  rfl

/-- The admitted source-preserving coproduct as one flat calculus language. -/
def target (compatible : Compatibility source symbols generated) :
    ValidatedCalculusLanguageDef :=
  ⟨definition source symbols generated, compatible.target_valid⟩

/-- The construction is also an ordinary validated calculus extension of the
source's empty proof fibre. -/
def validatedExtension
    (compatible : Compatibility source symbols generated) :
    ValidatedCalculusLanguageExtension (validatedSourceBase source) where
  extension := extension symbols generated
  policy := .newJudgmentsOnly
  disjoint := compatible.disjoint
  policyHolds := compatible.policy
  valid := compatible.target_valid

/-- Erasing only derivability recovers exactly the combined object language;
proof rows are not serialized into its five fields. -/
theorem erase_calculus
    (compatible : Compatibility source symbols generated) :
    compatible.target.1.toLanguageDef =
      (definition source symbols generated).toLanguageDef :=
  rfl

/-- The authored source language embeds by the identity symbol action.  Its
rows are literal prefixes, so source-facing codecs need no renaming. -/
def sourceInclusion
    (compatible : Compatibility source symbols generated) :
    StructuralMorphism source compatible.target.toValidatedLanguageDef where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    rw [mapEquation_id]
    exact List.mem_append_left _ membership
  mapsRewrites declaration membership := by
    rw [mapRewriteRule_id]
    exact List.mem_append_left _ membership

/-- The complete generated calculus embeds through the declared reindexing,
including its judgment and inference-rule rows. -/
def generatedInclusion
    (compatible : Compatibility source symbols generated) :
    CalculusStructuralMorphism generated compatible.target where
  symbols := symbols
  mapsTypes declaration membership :=
    List.mem_append_right _ (List.mem_map_of_mem membership)
  mapsTerms declaration membership :=
    List.mem_append_right _ (List.mem_map_of_mem membership)
  mapsEquations declaration membership :=
    List.mem_append_right _ (List.mem_map_of_mem membership)
  mapsRewrites declaration membership :=
    List.mem_append_right _ (List.mem_map_of_mem membership)
  mapsJudgments declaration membership :=
    List.mem_append_right _ (List.mem_map_of_mem membership)
  mapsRules declaration membership :=
    List.mem_append_right _ (List.mem_map_of_mem membership)
  mapsConversion declaration equality := by
    rw [compatible.generatedConversionNone] at equality
    cases equality

/-- The generated layer contributes no object reduction in the conservative
signature fragment, so the flat typed result retains the exact authored
rewrite list and its order. -/
theorem target_rewrites
    (compatible : Compatibility source symbols generated) :
    compatible.target.1.rewrites = source.language.rewrites := by
  simp [target, definition, extension, sourceBase,
    compatible.generatedRewritesEmpty]

/-- The same conservative fragment retains the authored equation list
exactly. -/
theorem target_equations
    (compatible : Compatibility source symbols generated) :
    compatible.target.1.equations = source.language.equations := by
  simp [target, definition, extension, sourceBase,
    compatible.generatedEquationsEmpty]

end Compatibility

#print axioms sourceBase_valid
#print axioms Compatibility.target_valid
#print axioms Compatibility.sourceInclusion
#print axioms Compatibility.generatedInclusion
#print axioms Compatibility.target_rewrites

end Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct
