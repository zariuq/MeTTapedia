import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.TptpOfficialSourceLocation
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Source-preserving semantic carrier for official TPTP syntax

The official TPTP abstract syntax already owns formulae, annotations, TSTP
sources, parent records, useful information, and scalar source spans.  This
module does not copy any of those rows.  It appends only the semantic identity
and collection structure needed after parsing:

* a document source digest and per-input occurrence identity;
* family-indexed annotated inputs whose payloads are the official AST sorts;
* source-preserving documents, including unresolved include directives; and
* topologically ordered derivation candidates containing formula inputs only.

`eraseToOfficialInput` is the explicit refinement map back to the sole
concrete-syntax authority.  The family tag is intrinsic in the semantic
constructor, so a FOF payload cannot be mislabeled as THF.  NHF is not a
separate top-level TPTP annotated language: the official grammar embeds its
connectives in THF.  Its later semantic admission is therefore a refinement of
the THF payload, not an invented seventh annotated-formula alternative.

The carrier is inert.  It performs neither proof search nor proof checking.
The derivation list is only a topological-order candidate for a verifier.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.OSLF.Framework.TypeSynthesis

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := none
}

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def addedTypes : List TypeDecl := [
  "TptpSemantic:source-digest",
  "TptpSemantic:occurrence-id",
  "TptpSemantic:annotated-input",
  "TptpSemantic:document-input",
  "TptpSemantic:document-inputs",
  "TptpSemantic:document",
  "TptpSemantic:derivation-nodes",
  "TptpSemantic:derivation"]

def addedTerms : List GrammarRule := [
  ctor "tptp-semantic:source-digest" "TptpSemantic:source-digest"
    [("value", "String")],
  ctor "tptp-semantic:occurrence-id" "TptpSemantic:occurrence-id"
    [("source", "TptpSemantic:source-digest"), ("index", "Integer")],

  ctor "tptp-semantic:thf-input" "TptpSemantic:annotated-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("formula", "Tptp92Ast:thf-annotated"),
     ("span", "Tptp92Ast:source-span")],
  ctor "tptp-semantic:tff-input" "TptpSemantic:annotated-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("formula", "Tptp92Ast:tff-annotated"),
     ("span", "Tptp92Ast:source-span")],
  ctor "tptp-semantic:tcf-input" "TptpSemantic:annotated-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("formula", "Tptp92Ast:tcf-annotated"),
     ("span", "Tptp92Ast:source-span")],
  ctor "tptp-semantic:fof-input" "TptpSemantic:annotated-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("formula", "Tptp92Ast:fof-annotated"),
     ("span", "Tptp92Ast:source-span")],
  ctor "tptp-semantic:cnf-input" "TptpSemantic:annotated-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("formula", "Tptp92Ast:cnf-annotated"),
     ("span", "Tptp92Ast:source-span")],
  ctor "tptp-semantic:tpi-input" "TptpSemantic:annotated-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("formula", "Tptp92Ast:tpi-annotated"),
     ("span", "Tptp92Ast:source-span")],

  ctor "tptp-semantic:document-formula" "TptpSemantic:document-input"
    [("input", "TptpSemantic:annotated-input")],
  ctor "tptp-semantic:document-include" "TptpSemantic:document-input"
    [("occurrence", "TptpSemantic:occurrence-id"),
     ("include", "Tptp92Ast:include"),
     ("span", "Tptp92Ast:source-span")],
  ctor "tptp-semantic:document-inputs-nil" "TptpSemantic:document-inputs" [],
  ctor "tptp-semantic:document-inputs-cons" "TptpSemantic:document-inputs"
    [("first", "TptpSemantic:document-input"),
     ("rest", "TptpSemantic:document-inputs")],
  ctor "tptp-semantic:document" "TptpSemantic:document"
    [("source", "TptpSemantic:source-digest"),
     ("inputs", "TptpSemantic:document-inputs")],

  ctor "tptp-semantic:derivation-nodes-nil"
    "TptpSemantic:derivation-nodes" [],
  ctor "tptp-semantic:derivation-nodes-cons"
    "TptpSemantic:derivation-nodes"
    [("first", "TptpSemantic:annotated-input"),
     ("rest", "TptpSemantic:derivation-nodes")],
  ctor "tptp-semantic:derivation" "TptpSemantic:derivation"
    [("source", "TptpSemantic:source-digest"),
     ("nodes", "TptpSemantic:derivation-nodes")]
]

private def base : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialAbstractSyntax.language {}

def extension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialSemanticCarrierV9200")

def calculusLanguage : CalculusLanguageDef := extension.apply base

def language : LanguageDef := calculusLanguage.toLanguageDef

theorem extension_disjoint : extension.disjointFrom base = true := by
  decide +kernel

theorem appendOnly :
    AppendOnlyCalculusRefinement base calculusLanguage :=
  extension.apply_appendOnly base

theorem official_types_exact_prefix :
    TptpOfficialAbstractSyntax.language.types.IsPrefix language.types := by
  change TptpOfficialAbstractSyntax.language.types.IsPrefix
    calculusLanguage.types
  exact appendOnly.types

theorem official_terms_exact_prefix :
    TptpOfficialAbstractSyntax.language.terms.IsPrefix language.terms := by
  change TptpOfficialAbstractSyntax.language.terms.IsPrefix
    calculusLanguage.terms
  exact appendOnly.terms

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_absent :
    addedTypes.all (fun declaration =>
      !(base.types.any fun existing => existing.name == declaration.name)) =
        true := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint base.toLanguageDef.typeNames (addedTypes.map (·.name)) := by
  have absent := added_type_names_absent
  simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false] at absent
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  rcases List.mem_map.mp baseMembership with
    ⟨baseDeclaration, baseDeclarationMembership, baseName⟩
  rcases List.mem_map.mp addedMembership with
    ⟨addedDeclaration, addedDeclarationMembership, addedName⟩
  exact absent addedDeclaration addedDeclarationMembership
    baseDeclaration baseDeclarationMembership
    (by simpa using baseName.trans addedName.symm)

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_absent :
    addedTerms.all (fun declaration =>
      !(base.terms.any fun existing => existing.label == declaration.label)) =
        true := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (base.terms.map (·.label)) (addedTerms.map (·.label)) := by
  have absent := added_term_labels_absent
  simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false] at absent
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  rcases List.mem_map.mp baseMembership with
    ⟨baseDeclaration, baseDeclarationMembership, baseLabel⟩
  rcases List.mem_map.mp addedMembership with
    ⟨addedDeclaration, addedDeclarationMembership, addedLabel⟩
  exact absent addedDeclaration addedDeclarationMembership
    baseDeclaration baseDeclarationMembership
    (by simpa using baseLabel.trans addedLabel.symm)

private theorem added_terms_validate_all :
    addedTerms.all (fun term => language.validateTerm term == []) = true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    language.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem language_validate : language.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    base addedTypes addedTerms
    (some "TptpOfficialSemanticCarrierV9200")
  · simpa [base] using TptpOfficialAbstractSyntax.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

theorem language_inventory :
    language.types.length = 259 ∧ language.terms.length = 483 ∧
      language.rewrites.length = 0 := by
  decide

theorem family_input_constructors_present :
    "tptp-semantic:thf-input" ∈ language.terms.map (·.label) ∧
      "tptp-semantic:fof-input" ∈ language.terms.map (·.label) ∧
      "tptp-semantic:cnf-input" ∈ language.terms.map (·.label) := by
  decide +kernel

theorem no_unchecked_derivation_constructor :
    "tptp-semantic:unchecked-formula" ∉ language.terms.map (·.label) := by
  decide +kernel

private theorem addedTerm_mem_language (term : GrammarRule)
    (membership : term ∈ addedTerms) : term ∈ language.terms := by
  change term ∈ base.terms ++ addedTerms
  exact List.mem_append_right _ membership

private def thfInputRuleIndex : Fin addedTerms.length := ⟨2, by decide⟩
private def tffInputRuleIndex : Fin addedTerms.length := ⟨3, by decide⟩
private def tcfInputRuleIndex : Fin addedTerms.length := ⟨4, by decide⟩
private def fofInputRuleIndex : Fin addedTerms.length := ⟨5, by decide⟩
private def cnfInputRuleIndex : Fin addedTerms.length := ⟨6, by decide⟩
private def tpiInputRuleIndex : Fin addedTerms.length := ⟨7, by decide⟩

def thfInputRule : GrammarRule := addedTerms.get thfInputRuleIndex
def tffInputRule : GrammarRule := addedTerms.get tffInputRuleIndex
def tcfInputRule : GrammarRule := addedTerms.get tcfInputRuleIndex
def fofInputRule : GrammarRule := addedTerms.get fofInputRuleIndex
def cnfInputRule : GrammarRule := addedTerms.get cnfInputRuleIndex
def tpiInputRule : GrammarRule := addedTerms.get tpiInputRuleIndex

theorem thfInputRule_shape :
    thfInputRule =
      ctor "tptp-semantic:thf-input" "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", "Tptp92Ast:thf-annotated"),
         ("span", "Tptp92Ast:source-span")] := by
  rfl

theorem tffInputRule_shape :
    tffInputRule =
      ctor "tptp-semantic:tff-input" "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", "Tptp92Ast:tff-annotated"),
         ("span", "Tptp92Ast:source-span")] := by
  rfl

theorem tcfInputRule_shape :
    tcfInputRule =
      ctor "tptp-semantic:tcf-input" "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", "Tptp92Ast:tcf-annotated"),
         ("span", "Tptp92Ast:source-span")] := by
  rfl

theorem fofInputRule_shape :
    fofInputRule =
      ctor "tptp-semantic:fof-input" "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", "Tptp92Ast:fof-annotated"),
         ("span", "Tptp92Ast:source-span")] := by
  rfl

theorem cnfInputRule_shape :
    cnfInputRule =
      ctor "tptp-semantic:cnf-input" "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", "Tptp92Ast:cnf-annotated"),
         ("span", "Tptp92Ast:source-span")] := by
  rfl

theorem tpiInputRule_shape :
    tpiInputRule =
      ctor "tptp-semantic:tpi-input" "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", "Tptp92Ast:tpi-annotated"),
         ("span", "Tptp92Ast:source-span")] := by
  rfl

theorem thfInputRule_mem_language : thfInputRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms thfInputRuleIndex)

theorem tffInputRule_mem_language : tffInputRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms tffInputRuleIndex)

theorem tcfInputRule_mem_language : tcfInputRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms tcfInputRuleIndex)

theorem fofInputRule_mem_language : fofInputRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms fofInputRuleIndex)

theorem cnfInputRule_mem_language : cnfInputRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms cnfInputRuleIndex)

theorem tpiInputRule_mem_language : tpiInputRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms tpiInputRuleIndex)

def symbolicFamilyInputContext (payloadSort : String) :
    WellSorted.FreeTypeContext := fun name =>
  if name = "occurrence" then
    some (.base "TptpSemantic:occurrence-id")
  else if name = "formula" then
    some (.base payloadSort)
  else if name = "span" then
    some (.base "Tptp92Ast:source-span")
  else
    none

def symbolicFamilyInput (label : String) : Pattern :=
  a label [.fvar "occurrence", .fvar "formula", .fvar "span"]

private theorem symbolicFamilyInput_has_type
    (label payloadSort : String) (rule : GrammarRule)
    (ruleMembership : rule ∈ language.terms)
    (ruleShape : rule =
      ctor label "TptpSemantic:annotated-input"
        [("occurrence", "TptpSemantic:occurrence-id"),
         ("formula", payloadSort),
         ("span", "Tptp92Ast:source-span")]) :
    HasType language (symbolicFamilyInputContext payloadSort) []
      (symbolicFamilyInput label)
      (.base "TptpSemantic:annotated-input") := by
  have argumentsTyped :
      ArgumentsHaveTypes language (symbolicFamilyInputContext payloadSort) []
        [.fvar "occurrence", .fvar "formula", .fvar "span"] rule.params := by
    rw [ruleShape]
    exact .cons (by trivial) rfl
      (.fvar (by simp [symbolicFamilyInputContext]))
      (.cons (by trivial) rfl
        (.fvar (by simp [symbolicFamilyInputContext]))
        (.cons (by trivial) rfl
          (.fvar (by simp [symbolicFamilyInputContext])) .nil))
  have typed := HasType.constructor ruleMembership
    (by
      rw [ruleShape]
      simp [ctor, WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [symbolicFamilyInput, ruleShape, ctor, a] using typed

theorem thf_symbolic_input_has_type :
    HasType language
      (symbolicFamilyInputContext "Tptp92Ast:thf-annotated") []
      (symbolicFamilyInput "tptp-semantic:thf-input")
      (.base "TptpSemantic:annotated-input") :=
  symbolicFamilyInput_has_type _ _ thfInputRule
    thfInputRule_mem_language thfInputRule_shape

theorem tff_symbolic_input_has_type :
    HasType language
      (symbolicFamilyInputContext "Tptp92Ast:tff-annotated") []
      (symbolicFamilyInput "tptp-semantic:tff-input")
      (.base "TptpSemantic:annotated-input") :=
  symbolicFamilyInput_has_type _ _ tffInputRule
    tffInputRule_mem_language tffInputRule_shape

theorem tcf_symbolic_input_has_type :
    HasType language
      (symbolicFamilyInputContext "Tptp92Ast:tcf-annotated") []
      (symbolicFamilyInput "tptp-semantic:tcf-input")
      (.base "TptpSemantic:annotated-input") :=
  symbolicFamilyInput_has_type _ _ tcfInputRule
    tcfInputRule_mem_language tcfInputRule_shape

theorem fof_symbolic_input_has_type :
    HasType language
      (symbolicFamilyInputContext "Tptp92Ast:fof-annotated") []
      (symbolicFamilyInput "tptp-semantic:fof-input")
      (.base "TptpSemantic:annotated-input") :=
  symbolicFamilyInput_has_type _ _ fofInputRule
    fofInputRule_mem_language fofInputRule_shape

theorem cnf_symbolic_input_has_type :
    HasType language
      (symbolicFamilyInputContext "Tptp92Ast:cnf-annotated") []
      (symbolicFamilyInput "tptp-semantic:cnf-input")
      (.base "TptpSemantic:annotated-input") :=
  symbolicFamilyInput_has_type _ _ cnfInputRule
    cnfInputRule_mem_language cnfInputRule_shape

theorem tpi_symbolic_input_has_type :
    HasType language
      (symbolicFamilyInputContext "Tptp92Ast:tpi-annotated") []
      (symbolicFamilyInput "tptp-semantic:tpi-input")
      (.base "TptpSemantic:annotated-input") :=
  symbolicFamilyInput_has_type _ _ tpiInputRule
    tpiInputRule_mem_language tpiInputRule_shape

private theorem symbolicFamilyInput_is_object (label : String) :
    WellSorted.isObjectPattern (symbolicFamilyInput label) = true := by
  rfl

theorem thf_symbolic_input_admitted :
    checkHasType language
      (symbolicFamilyInputContext "Tptp92Ast:thf-annotated") []
      (symbolicFamilyInput "tptp-semantic:thf-input")
      (.base "TptpSemantic:annotated-input") = true :=
  checkHasType_complete_of_object thf_symbolic_input_has_type
    (symbolicFamilyInput_is_object _)

theorem tff_symbolic_input_admitted :
    checkHasType language
      (symbolicFamilyInputContext "Tptp92Ast:tff-annotated") []
      (symbolicFamilyInput "tptp-semantic:tff-input")
      (.base "TptpSemantic:annotated-input") = true :=
  checkHasType_complete_of_object tff_symbolic_input_has_type
    (symbolicFamilyInput_is_object _)

theorem tcf_symbolic_input_admitted :
    checkHasType language
      (symbolicFamilyInputContext "Tptp92Ast:tcf-annotated") []
      (symbolicFamilyInput "tptp-semantic:tcf-input")
      (.base "TptpSemantic:annotated-input") = true :=
  checkHasType_complete_of_object tcf_symbolic_input_has_type
    (symbolicFamilyInput_is_object _)

theorem fof_symbolic_input_admitted :
    checkHasType language
      (symbolicFamilyInputContext "Tptp92Ast:fof-annotated") []
      (symbolicFamilyInput "tptp-semantic:fof-input")
      (.base "TptpSemantic:annotated-input") = true :=
  checkHasType_complete_of_object fof_symbolic_input_has_type
    (symbolicFamilyInput_is_object _)

theorem cnf_symbolic_input_admitted :
    checkHasType language
      (symbolicFamilyInputContext "Tptp92Ast:cnf-annotated") []
      (symbolicFamilyInput "tptp-semantic:cnf-input")
      (.base "TptpSemantic:annotated-input") = true :=
  checkHasType_complete_of_object cnf_symbolic_input_has_type
    (symbolicFamilyInput_is_object _)

theorem tpi_symbolic_input_admitted :
    checkHasType language
      (symbolicFamilyInputContext "Tptp92Ast:tpi-annotated") []
      (symbolicFamilyInput "tptp-semantic:tpi-input")
      (.base "TptpSemantic:annotated-input") = true :=
  checkHasType_complete_of_object tpi_symbolic_input_has_type
    (symbolicFamilyInput_is_object _)

private def documentRuleIndex : Fin addedTerms.length := ⟨12, by decide⟩
private def derivationRuleIndex : Fin addedTerms.length := ⟨15, by decide⟩

def documentRule : GrammarRule := addedTerms.get documentRuleIndex
def derivationRule : GrammarRule := addedTerms.get derivationRuleIndex

theorem documentRule_shape :
    documentRule =
      ctor "tptp-semantic:document" "TptpSemantic:document"
        [("source", "TptpSemantic:source-digest"),
         ("inputs", "TptpSemantic:document-inputs")] := by
  rfl

theorem derivationRule_shape :
    derivationRule =
      ctor "tptp-semantic:derivation" "TptpSemantic:derivation"
        [("source", "TptpSemantic:source-digest"),
         ("nodes", "TptpSemantic:derivation-nodes")] := by
  rfl

theorem documentRule_mem_language : documentRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms documentRuleIndex)

theorem derivationRule_mem_language : derivationRule ∈ language.terms :=
  addedTerm_mem_language _ (List.get_mem addedTerms derivationRuleIndex)

def symbolicRootContext (payloadSort : String) :
    WellSorted.FreeTypeContext := fun name =>
  if name = "source" then
    some (.base "TptpSemantic:source-digest")
  else if name = "payload" then
    some (.base payloadSort)
  else
    none

def symbolicRoot (label : String) : Pattern :=
  a label [.fvar "source", .fvar "payload"]

private theorem symbolicRoot_has_type
    (label resultSort payloadSort payloadName : String)
    (rule : GrammarRule) (ruleMembership : rule ∈ language.terms)
    (ruleShape : rule =
      ctor label resultSort
        [("source", "TptpSemantic:source-digest"),
         (payloadName, payloadSort)]) :
    HasType language (symbolicRootContext payloadSort) []
      (symbolicRoot label) (.base resultSort) := by
  have argumentsTyped :
      ArgumentsHaveTypes language (symbolicRootContext payloadSort) []
        [.fvar "source", .fvar "payload"] rule.params := by
    rw [ruleShape]
    exact .cons (by trivial) rfl
      (.fvar (by simp [symbolicRootContext]))
      (.cons (by trivial) rfl
        (.fvar (by simp [symbolicRootContext])) .nil)
  have typed := HasType.constructor ruleMembership
    (by
      rw [ruleShape]
      simp [ctor, WellSorted.UsesBareCollection])
    argumentsTyped
  simpa [symbolicRoot, ruleShape, ctor, a] using typed

theorem symbolic_document_has_type :
    HasType language
      (symbolicRootContext "TptpSemantic:document-inputs") []
      (symbolicRoot "tptp-semantic:document")
      (.base "TptpSemantic:document") :=
  symbolicRoot_has_type _ _ _ _ documentRule
    documentRule_mem_language documentRule_shape

theorem symbolic_derivation_has_type :
    HasType language
      (symbolicRootContext "TptpSemantic:derivation-nodes") []
      (symbolicRoot "tptp-semantic:derivation")
      (.base "TptpSemantic:derivation") :=
  symbolicRoot_has_type _ _ _ _ derivationRule
    derivationRule_mem_language derivationRule_shape

private theorem symbolicRoot_is_object (label : String) :
    WellSorted.isObjectPattern (symbolicRoot label) = true := by
  rfl

theorem symbolic_document_admitted :
    checkHasType language
      (symbolicRootContext "TptpSemantic:document-inputs") []
      (symbolicRoot "tptp-semantic:document")
      (.base "TptpSemantic:document") = true :=
  checkHasType_complete_of_object symbolic_document_has_type
    (symbolicRoot_is_object _)

theorem symbolic_derivation_admitted :
    checkHasType language
      (symbolicRootContext "TptpSemantic:derivation-nodes") []
      (symbolicRoot "tptp-semantic:derivation")
      (.base "TptpSemantic:derivation") = true :=
  checkHasType_complete_of_object symbolic_derivation_has_type
    (symbolicRoot_is_object _)

/-! ## Exact refinement to the official AST input -/

inductive FormulaPayload where
  | thf (formula : Pattern)
  | tff (formula : Pattern)
  | tcf (formula : Pattern)
  | fof (formula : Pattern)
  | cnf (formula : Pattern)
  | tpi (formula : Pattern)
  deriving DecidableEq

structure AnnotatedInputView where
  occurrence : Pattern
  payload : FormulaPayload
  span : Pattern
  deriving DecidableEq

def encodeAnnotatedInput (input : AnnotatedInputView) : Pattern :=
  match input.payload with
  | .thf formula =>
      .apply "tptp-semantic:thf-input" [input.occurrence, formula, input.span]
  | .tff formula =>
      .apply "tptp-semantic:tff-input" [input.occurrence, formula, input.span]
  | .tcf formula =>
      .apply "tptp-semantic:tcf-input" [input.occurrence, formula, input.span]
  | .fof formula =>
      .apply "tptp-semantic:fof-input" [input.occurrence, formula, input.span]
  | .cnf formula =>
      .apply "tptp-semantic:cnf-input" [input.occurrence, formula, input.span]
  | .tpi formula =>
      .apply "tptp-semantic:tpi-input" [input.occurrence, formula, input.span]

def decodeAnnotatedInput? : Pattern → Option AnnotatedInputView
  | .apply "tptp-semantic:thf-input" [occurrence, formula, span] =>
      some ⟨occurrence, .thf formula, span⟩
  | .apply "tptp-semantic:tff-input" [occurrence, formula, span] =>
      some ⟨occurrence, .tff formula, span⟩
  | .apply "tptp-semantic:tcf-input" [occurrence, formula, span] =>
      some ⟨occurrence, .tcf formula, span⟩
  | .apply "tptp-semantic:fof-input" [occurrence, formula, span] =>
      some ⟨occurrence, .fof formula, span⟩
  | .apply "tptp-semantic:cnf-input" [occurrence, formula, span] =>
      some ⟨occurrence, .cnf formula, span⟩
  | .apply "tptp-semantic:tpi-input" [occurrence, formula, span] =>
      some ⟨occurrence, .tpi formula, span⟩
  | _ => none

theorem decode_encode (input : AnnotatedInputView) :
    decodeAnnotatedInput? (encodeAnnotatedInput input) = some input := by
  cases input with
  | mk occurrence payload span =>
      cases payload <;> rfl

theorem encodeAnnotatedInput_injective :
    Function.Injective encodeAnnotatedInput := by
  intro left right equality
  have decoded := congrArg decodeAnnotatedInput? equality
  simpa only [decode_encode, Option.some.injEq] using decoded

def toOfficialAnnotatedFormula : FormulaPayload → Pattern
  | .thf formula =>
      a "tptp92-ast:annotated-formula:alt-1" [formula]
  | .tff formula =>
      a "tptp92-ast:annotated-formula:alt-2" [formula]
  | .tcf formula =>
      a "tptp92-ast:annotated-formula:alt-3" [formula]
  | .fof formula =>
      a "tptp92-ast:annotated-formula:alt-4" [formula]
  | .cnf formula =>
      a "tptp92-ast:annotated-formula:alt-5" [formula]
  | .tpi formula =>
      a "tptp92-ast:annotated-formula:alt-6" [formula]

/-- Forget semantic occurrence identity and recover the exact official
top-level syntax input. -/
def eraseToOfficialInput (input : AnnotatedInputView) : Pattern :=
  a "tptp92-ast:tptp-input:alt-1"
    [toOfficialAnnotatedFormula input.payload, input.span]

/-- Refine one official formula input after assigning its canonical source
occurrence.  Include inputs are deliberately handled by the document layer. -/
def refineOfficialFormulaInput? (occurrence : Pattern) :
    Pattern → Option AnnotatedInputView
  | .apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-1" [formula], span] =>
      some ⟨occurrence, .thf formula, span⟩
  | .apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-2" [formula], span] =>
      some ⟨occurrence, .tff formula, span⟩
  | .apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-3" [formula], span] =>
      some ⟨occurrence, .tcf formula, span⟩
  | .apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-4" [formula], span] =>
      some ⟨occurrence, .fof formula, span⟩
  | .apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-5" [formula], span] =>
      some ⟨occurrence, .cnf formula, span⟩
  | .apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-6" [formula], span] =>
      some ⟨occurrence, .tpi formula, span⟩
  | _ => none

theorem refine_erase (input : AnnotatedInputView) :
    refineOfficialFormulaInput? input.occurrence
        (eraseToOfficialInput input) = some input := by
  cases input with
  | mk occurrence payload span =>
      cases payload <;> rfl

theorem erase_preserves_span (occurrence start stop : Pattern)
    (payload : FormulaPayload) :
    TptpOfficialSourceLocation.decodeLocatedInput?
        (eraseToOfficialInput
          ⟨occurrence, payload,
            a "tptp92-ast:source-span" [start, stop]⟩) =
      some {
        payload := .annotatedFormula (toOfficialAnnotatedFormula payload)
        span := { start, stop }} := by
  cases payload <;> rfl

/-! ## Positive and negative carrier witnesses -/

def sourceDigestExample : Pattern :=
  a "tptp-semantic:source-digest" [a "sha256-demo"]

def occurrenceExample : Pattern :=
  a "tptp-semantic:occurrence-id" [sourceDigestExample, a "0"]

def spanExample : Pattern :=
  a "tptp92-ast:source-span" [a "4", a "23"]

def thfInputExample : Pattern :=
  encodeAnnotatedInput
    ⟨occurrenceExample, .thf TptpOfficialAbstractSyntax.thfAnnotatedExample,
      spanExample⟩

def tffInputExample : Pattern :=
  encodeAnnotatedInput
    ⟨occurrenceExample, .tff TptpOfficialAbstractSyntax.tffAnnotatedExample,
      spanExample⟩

def tcfInputExample : Pattern :=
  encodeAnnotatedInput
    ⟨occurrenceExample, .tcf TptpOfficialAbstractSyntax.tcfAnnotatedExample,
      spanExample⟩

def fofInputExample : Pattern :=
  encodeAnnotatedInput
    ⟨occurrenceExample, .fof TptpOfficialAbstractSyntax.fofAnnotatedExample,
      spanExample⟩

def cnfInputExample : Pattern :=
  encodeAnnotatedInput
    ⟨occurrenceExample, .cnf TptpOfficialAbstractSyntax.cnfAnnotatedExample,
      spanExample⟩

def tpiInputExample : Pattern :=
  encodeAnnotatedInput
    ⟨occurrenceExample, .tpi TptpOfficialAbstractSyntax.tpiAnnotatedExample,
      spanExample⟩

def documentExample : Pattern :=
  a "tptp-semantic:document" [sourceDigestExample,
    a "tptp-semantic:document-inputs-cons" [
      a "tptp-semantic:document-formula" [fofInputExample],
      a "tptp-semantic:document-inputs-nil"]]

def derivationExample : Pattern :=
  a "tptp-semantic:derivation" [sourceDigestExample,
    a "tptp-semantic:derivation-nodes-cons" [
      fofInputExample,
      a "tptp-semantic:derivation-nodes-nil"]]

def mislabeledThfInput : Pattern :=
  a "tptp-semantic:thf-input"
    [occurrenceExample, TptpOfficialAbstractSyntax.fofAnnotatedExample,
      spanExample]

theorem official_include_not_formula_refinement
    (occurrence directive span : Pattern) :
    refineOfficialFormulaInput? occurrence
      (a "tptp92-ast:tptp-input:alt-2" [directive, span]) = none := by
  rfl

theorem raw_official_input_not_semantic_encoding (input : AnnotatedInputView) :
    decodeAnnotatedInput? (eraseToOfficialInput input) = none := by
  cases input with
  | mk occurrence payload span =>
      cases payload <;> rfl

theorem document_and_derivation_constructors_distinct :
    a "tptp-semantic:document" ≠ a "tptp-semantic:derivation" := by
  decide

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_no_equations rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  change langReducesUsing RelationEnv.empty language source target at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

def stepDecision : EffectiveStructure.StepDecision theory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact theory_no_step source target

def oslf := langOSLF language "TptpSemantic:derivation"

theorem galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms extension_disjoint
#print axioms official_types_exact_prefix
#print axioms official_terms_exact_prefix
#print axioms language_validate
#print axioms family_input_constructors_present
#print axioms no_unchecked_derivation_constructor
#print axioms decode_encode
#print axioms encodeAnnotatedInput_injective
#print axioms refine_erase
#print axioms erase_preserves_span
#print axioms thf_symbolic_input_admitted
#print axioms tff_symbolic_input_admitted
#print axioms tcf_symbolic_input_admitted
#print axioms fof_symbolic_input_admitted
#print axioms cnf_symbolic_input_admitted
#print axioms tpi_symbolic_input_admitted
#print axioms symbolic_document_admitted
#print axioms symbolic_derivation_admitted
#print axioms official_include_not_formula_refinement
#print axioms raw_official_input_not_semantic_encoding
#print axioms document_and_derivation_constructors_distinct
#print axioms theory_no_step
#print axioms galois
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier
