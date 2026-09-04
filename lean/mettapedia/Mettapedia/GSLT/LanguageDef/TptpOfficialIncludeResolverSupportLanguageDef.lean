import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeLocalMachinesLanguageDef

/-!
# Structural support for recursive TPTP include resolution

The local include machines decode directives, classify inputs, perform exact
environment lookup, and apply formula selection.  Recursive resolution also
needs a small ordered-list algebra.  This module declares that algebra as
ordinary rewrite rules:

* convert directive selections into the resolution-result carrier;
* append one active source or include edge;
* concatenate child and remaining formula/edge lists.

These operations preserve order and multiplicity.  They contain no file-system
access and no recursive include controller.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolverSupportLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

namespace Local

abbrev language := TptpOfficialIncludeLocalMachinesLanguageDef.language
abbrev rewrites := TptpOfficialIncludeLocalMachinesLanguageDef.rewrites

end Local

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def v (name : String) : Pattern := .fvar name

private def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := policy
}

private def mkRule (name : String) (context : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule := {
  name
  typeContext := typed context
  premises
  left
  right
}

private def congruence (source target : Pattern) : Premise :=
  .congruence source target

def stringsNil : Pattern :=
  a "tptp-include-result:strings-nil"

def stringsCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:strings-cons" [head, tail]

def edgesNil : Pattern :=
  a "tptp-include-result:include-edges-nil"

def edgesCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:include-edges-cons" [head, tail]

def formulasNil : Pattern :=
  a "tptp-include-result:resolved-formulas-nil"

def formulasCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:resolved-formulas-cons" [head, tail]

def selectionImplicitAll : Pattern :=
  a "tptp-include-result:selection-implicit-all"

def selectionExplicitAll : Pattern :=
  a "tptp-include-result:selection-explicit-all"

def selectionNamed (names : Pattern) : Pattern :=
  a "tptp-include-result:selection-named" [names]

def convertNames (names : Pattern) : Pattern :=
  a "tptp-include-controller:convert-names" [names]

def convertSelection (selection : Pattern) : Pattern :=
  a "tptp-include-controller:convert-selection" [selection]

def appendString (strings value : Pattern) : Pattern :=
  a "tptp-include-controller:append-string" [strings, value]

def appendEdge (edges edge : Pattern) : Pattern :=
  a "tptp-include-controller:append-edge" [edges, edge]

def appendFormulas (left right : Pattern) : Pattern :=
  a "tptp-include-controller:append-formulas" [left, right]

def appendEdges (left right : Pattern) : Pattern :=
  a "tptp-include-controller:append-edges" [left, right]

def supportTypes : List TypeDecl := [
  TypeDecl.plain "TptpIncludeController:NameConversion"]

def supportTerms : List GrammarRule := [
  ctor "tptp-include-controller:convert-names"
    "TptpIncludeController:NameConversion"
    [("names", "TptpInclude:Names")] (some .rewrite),
  ctor "tptp-include-controller:converted-names"
    "TptpIncludeController:NameConversion"
    [("names", "TptpIncludeResult:Strings")],
  ctor "tptp-include-controller:convert-selection"
    "TptpIncludeResult:FormulaSelection"
    [("selection", "TptpInclude:Selection")] (some .rewrite),
  ctor "tptp-include-controller:append-string"
    "TptpIncludeResult:Strings"
    [("strings", "TptpIncludeResult:Strings"), ("value", "String")]
    (some .rewrite),
  ctor "tptp-include-controller:append-edge"
    "TptpIncludeResult:IncludeEdges"
    [("edges", "TptpIncludeResult:IncludeEdges"),
      ("edge", "TptpIncludeResult:IncludeEdge")] (some .rewrite),
  ctor "tptp-include-controller:append-formulas"
    "TptpIncludeResult:ResolvedFormulas"
    [("left", "TptpIncludeResult:ResolvedFormulas"),
      ("right", "TptpIncludeResult:ResolvedFormulas")] (some .rewrite),
  ctor "tptp-include-controller:append-edges"
    "TptpIncludeResult:IncludeEdges"
    [("left", "TptpIncludeResult:IncludeEdges"),
      ("right", "TptpIncludeResult:IncludeEdges")] (some .rewrite)]

private def convertedNames (names : Pattern) : Pattern :=
  a "tptp-include-controller:converted-names" [names]

private def directiveNamesOne (name : Pattern) : Pattern :=
  a "tptp-include:names-one" [name]

private def directiveNamesCons (name rest : Pattern) : Pattern :=
  a "tptp-include:names-cons" [name, rest]

private def directiveImplicitAll : Pattern :=
  a "tptp-include:implicit-all"

private def directiveExplicitAll : Pattern :=
  a "tptp-include:explicit-all"

private def directiveNamed (names : Pattern) : Pattern :=
  a "tptp-include:named-selection" [names]

def supportRewrites : List RewriteRule := [
  mkRule "tptp-include-controller:convert-names-one"
    [("name", "String")] []
    (convertNames (directiveNamesOne (v "name")))
    (convertedNames (stringsCons (v "name") stringsNil)),
  mkRule "tptp-include-controller:convert-names-cons"
    [("name", "String"), ("rest", "TptpInclude:Names"),
      ("converted", "TptpIncludeResult:Strings")]
    [congruence (convertNames (v "rest"))
      (convertedNames (v "converted"))]
    (convertNames (directiveNamesCons (v "name") (v "rest")))
    (convertedNames (stringsCons (v "name") (v "converted"))),
  mkRule "tptp-include-controller:convert-selection-implicit" [] []
    (convertSelection directiveImplicitAll) selectionImplicitAll,
  mkRule "tptp-include-controller:convert-selection-explicit" [] []
    (convertSelection directiveExplicitAll) selectionExplicitAll,
  mkRule "tptp-include-controller:convert-selection-named"
    [("names", "TptpInclude:Names"),
      ("converted", "TptpIncludeResult:Strings")]
    [congruence (convertNames (v "names"))
      (convertedNames (v "converted"))]
    (convertSelection (directiveNamed (v "names")))
    (selectionNamed (v "converted")),
  mkRule "tptp-include-controller:append-string-nil"
    [("value", "String")] []
    (appendString stringsNil (v "value"))
    (stringsCons (v "value") stringsNil),
  mkRule "tptp-include-controller:append-string-cons"
    [("head", "String"), ("tail", "TptpIncludeResult:Strings"),
      ("value", "String"), ("result", "TptpIncludeResult:Strings")]
    [congruence (appendString (v "tail") (v "value")) (v "result")]
    (appendString (stringsCons (v "head") (v "tail")) (v "value"))
    (stringsCons (v "head") (v "result")),
  mkRule "tptp-include-controller:append-edge-nil"
    [("edge", "TptpIncludeResult:IncludeEdge")] []
    (appendEdge edgesNil (v "edge"))
    (edgesCons (v "edge") edgesNil),
  mkRule "tptp-include-controller:append-edge-cons"
    [("head", "TptpIncludeResult:IncludeEdge"),
      ("tail", "TptpIncludeResult:IncludeEdges"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("result", "TptpIncludeResult:IncludeEdges")]
    [congruence (appendEdge (v "tail") (v "edge")) (v "result")]
    (appendEdge (edgesCons (v "head") (v "tail")) (v "edge"))
    (edgesCons (v "head") (v "result")),
  mkRule "tptp-include-controller:append-formulas-nil"
    [("right", "TptpIncludeResult:ResolvedFormulas")] []
    (appendFormulas formulasNil (v "right")) (v "right"),
  mkRule "tptp-include-controller:append-formulas-cons"
    [("head", "TptpIncludeResult:ResolvedFormula"),
      ("tail", "TptpIncludeResult:ResolvedFormulas"),
      ("right", "TptpIncludeResult:ResolvedFormulas"),
      ("result", "TptpIncludeResult:ResolvedFormulas")]
    [congruence (appendFormulas (v "tail") (v "right")) (v "result")]
    (appendFormulas (formulasCons (v "head") (v "tail")) (v "right"))
    (formulasCons (v "head") (v "result")),
  mkRule "tptp-include-controller:append-edges-nil"
    [("right", "TptpIncludeResult:IncludeEdges")] []
    (appendEdges edgesNil (v "right")) (v "right"),
  mkRule "tptp-include-controller:append-edges-cons"
    [("head", "TptpIncludeResult:IncludeEdge"),
      ("tail", "TptpIncludeResult:IncludeEdges"),
      ("right", "TptpIncludeResult:IncludeEdges"),
      ("result", "TptpIncludeResult:IncludeEdges")]
    [congruence (appendEdges (v "tail") (v "right")) (v "result")]
    (appendEdges (edgesCons (v "head") (v "tail")) (v "right"))
    (edgesCons (v "head") (v "result"))]

def addedTypes : List TypeDecl := supportTypes
def addedTerms : List GrammarRule := supportTerms
def rewrites : List RewriteRule := Local.rewrites ++ supportRewrites

private def signatureBaseLanguage : LanguageDef := {
  name := Local.language.name
  types := Local.language.types
  terms := Local.language.terms
  equations := []
  rewrites := []
}

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend signatureBaseLanguage {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeResolverSupportV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeResolverSupportV1"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

@[simp] theorem typeNames_exact :
    language.typeNames = Local.language.typeNames ++ addedTypes.map (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, signatureBaseLanguage,
    ConstructorSignatureExtension.ofLists, LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures Local.language ++
        addedTerms.map fun declaration =>
          (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, signatureBaseLanguage,
    ConstructorSignatureExtension.ofLists]

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.toLanguageDef.typeNames
      (addedTypes.map (·.name)) := by
  have baseSeparate :
      signatureBase.toLanguageDef.typeNames.all
        (fun name => !(name.startsWith "TptpIncludeController:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTypes.map (·.name)).all
        (fun name => name.startsWith "TptpIncludeController:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  have baseNot := (List.all_eq_true.mp baseSeparate) name baseMembership
  have addedYes := (List.all_eq_true.mp addedNamespaced) name addedMembership
  simp [addedYes] at baseNot

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.toLanguageDef.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have baseSeparate :
      (signatureBase.toLanguageDef.terms.map (·.label)).all
        (fun label => !(label.startsWith "tptp-include-controller:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTerms.map (·.label)).all
        (fun label => label.startsWith "tptp-include-controller:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  have baseNot := (List.all_eq_true.mp baseSeparate) label baseMembership
  have addedYes := (List.all_eq_true.mp addedNamespaced) label addedMembership
  simp [addedYes] at baseNot

private theorem added_terms_validate_all :
    addedTerms.all
      (fun term => signatureLanguage.validateTerm term == []) = true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    signatureLanguage.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

private theorem signatureBaseLanguage_validate :
    signatureBaseLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · change Local.language.typeNames.Nodup
    exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      Local.language
      TptpOfficialIncludeLocalMachinesLanguageDef.language_validate
  · change (Local.language.terms.map (·.label)).Nodup
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      Local.language
      TptpOfficialIncludeLocalMachinesLanguageDef.language_validate
  · simp [signatureBaseLanguage]
  · simp [signatureBaseLanguage]
  · intro term membership
    change Local.language.validateTerm term = []
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      Local.language
      TptpOfficialIncludeLocalMachinesLanguageDef.language_validate
      term membership
  · intro equation membership
    simp [signatureBaseLanguage] at membership
  · intro rewrite membership
    simp [signatureBaseLanguage] at membership

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase addedTypes addedTerms
      (some "TptpOfficialIncludeResolverSupportV1")
  · simpa [signatureBase] using signatureBaseLanguage_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

private theorem language_constructor_labels_nodup :
    (language.terms.map (·.label)).Nodup := by
  simpa [language] using
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate

def constructorLabelReserved (label : String) : Bool :=
  label.startsWith "tptp" ||
    label.startsWith "pattern-equality-decision:"

private theorem constructor_labels_reserved :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelReserved = true := by
  decide +kernel

private def requiredTypes : List String := [
  "String", "TptpInclude:Names", "TptpInclude:Selection",
  "TptpIncludeResult:Strings", "TptpIncludeResult:FormulaSelection",
  "TptpIncludeResult:IncludeEdge", "TptpIncludeResult:IncludeEdges",
  "TptpIncludeResult:ResolvedFormula",
  "TptpIncludeResult:ResolvedFormulas",
  "TptpIncludeController:NameConversion"]

private def resultRequiredSignatures : List (String × Nat) := [
  ("tptp-include-result:strings-nil", 0),
  ("tptp-include-result:strings-cons", 2),
  ("tptp-include-result:include-edges-nil", 0),
  ("tptp-include-result:include-edges-cons", 2),
  ("tptp-include-result:resolved-formulas-nil", 0),
  ("tptp-include-result:resolved-formulas-cons", 2),
  ("tptp-include-result:selection-implicit-all", 0),
  ("tptp-include-result:selection-explicit-all", 0),
  ("tptp-include-result:selection-named", 1)]

private def directiveRequiredSignatures : List (String × Nat) := [
  ("tptp-include:names-one", 1),
  ("tptp-include:names-cons", 2),
  ("tptp-include:implicit-all", 0),
  ("tptp-include:explicit-all", 0),
  ("tptp-include:named-selection", 1)]

private def controllerRequiredSignatures : List (String × Nat) := [
  ("tptp-include-controller:convert-names", 1),
  ("tptp-include-controller:converted-names", 1),
  ("tptp-include-controller:convert-selection", 1),
  ("tptp-include-controller:append-string", 2),
  ("tptp-include-controller:append-edge", 2),
  ("tptp-include-controller:append-formulas", 2),
  ("tptp-include-controller:append-edges", 2)]

private def requiredSignatures : List (String × Nat) :=
  resultRequiredSignatures ++ directiveRequiredSignatures ++
    controllerRequiredSignatures

private theorem requiredType_declared {name : String}
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames := by
  rw [typeNames_exact]
  simp only [List.mem_append]
  by_cases controller : name.startsWith "TptpIncludeController:"
  · right
    revert name
    decide +kernel
  · left
    simp only [TptpOfficialIncludeLocalMachinesLanguageDef.typeNames_exact,
      List.mem_append]
    revert name
    decide +kernel

private theorem requiredSignature_declared {signature : String × Nat}
    (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures
      language := by
  rw [constructorSignatures_exact]
  simp only [List.mem_append]
  simp only [requiredSignatures, List.mem_append] at membership
  rcases membership with (resultMember | directiveMember) | controllerMember
  · left
    rw [TptpOfficialIncludeLocalMachinesLanguageDef.constructorSignatures_exact]
    have table :
        resultRequiredSignatures.all fun candidate =>
          decide (candidate ∈
            RewriteValidationCertificate.constructorSignatures
              TptpOfficialIncludeResolutionResultCarrier.language) := by
      decide +kernel
    exact List.mem_append_left _
      (decide_eq_true_eq.mp
        (List.all_eq_true.mp table signature resultMember))
  · left
    rw [TptpOfficialIncludeLocalMachinesLanguageDef.constructorSignatures_exact]
    have table :
        directiveRequiredSignatures.all fun candidate =>
          decide (candidate ∈
            TptpOfficialIncludeDirectiveLanguageDef.addedTerms.map
              (fun declaration =>
                (declaration.label, declaration.params.length))) := by
      decide +kernel
    have inDirective :
        signature ∈
          TptpOfficialIncludeDirectiveLanguageDef.addedTerms.map
            (fun declaration =>
              (declaration.label, declaration.params.length)) :=
      decide_eq_true_eq.mp
        (List.all_eq_true.mp table signature directiveMember)
    simp [TptpOfficialIncludeLocalMachinesLanguageDef.addedTerms, inDirective]
  · right
    have table :
        controllerRequiredSignatures.all fun candidate =>
          decide (candidate ∈ addedTerms.map
            (fun declaration =>
              (declaration.label, declaration.params.length))):= by
      decide +kernel
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp table signature controllerMember)

private theorem plainName_not_constructor {name : String}
    (plain : constructorLabelReserved name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have reserved :=
    (List.all_eq_true.mp constructor_labels_reserved) name membership
  simp [plain] at reserved

private def contextSubsetCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    entry.2.baseNames.all fun name => decide (name ∈ requiredTypes)

private def patternSubsetCheck (pattern : Pattern) : Bool :=
  pattern.constructorRefs.all fun signature =>
    decide (signature ∈ requiredSignatures)

private def premisesSubsetCheck (rewrite : RewriteRule) : Bool :=
  (rewrite.premises.flatMap LanguageDef.premisePatterns).all
    patternSubsetCheck

private def fvarsPlainCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternFvarNames [] rewrite.left ++
    LanguageDef.patternFvarNames [] rewrite.right ++
    rewrite.premises.flatMap
      (LanguageDef.premiseFvarNames [])).eraseDups).all fun name =>
    !constructorLabelReserved name

private def bindersPlainCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternBinderNames rewrite.left ++
    LanguageDef.patternBinderNames rewrite.right ++
    (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
      LanguageDef.patternBinderNames ++
    rewrite.premises.flatMap
      LanguageDef.premiseForAllParams).eraseDups).all fun name =>
    !constructorLabelReserved name

private def contextNamesPlainCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    !constructorLabelReserved entry.1

private def subsetCheck (rewrite : RewriteRule) : Bool :=
  contextSubsetCheck rewrite &&
    (patternSubsetCheck rewrite.left &&
      (patternSubsetCheck rewrite.right &&
        (premisesSubsetCheck rewrite &&
          (RewriteValidationCertificate.allPatternsScopedCheck rewrite &&
            (fvarsPlainCheck rewrite &&
              (bindersPlainCheck rewrite &&
                (contextNamesPlainCheck rewrite &&
                  RewriteValidationCertificate.rightBoundCheck rewrite)))))))

private theorem certificate_of_subsetCheck {rewrite : RewriteRule}
    (checked : subsetCheck rewrite = true) :
    RewriteValidationCertificate.Certificate language rewrite := by
  simp only [subsetCheck, Bool.and_eq_true] at checked
  rcases checked with
    ⟨contextChecked, leftChecked, rightChecked, premisesChecked,
      scopedChecked, fvarsChecked, bindersChecked, contextNamesChecked,
      rightBoundedChecked⟩
  simp only [contextSubsetCheck] at contextChecked
  simp only [patternSubsetCheck] at leftChecked rightChecked
  simp only [premisesSubsetCheck] at premisesChecked
  simp only [fvarsPlainCheck] at fvarsChecked
  simp only [bindersPlainCheck] at bindersChecked
  simp only [contextNamesPlainCheck] at contextNamesChecked
  refine {
    contextTypes := ?_
    leftDeclared := ?_
    rightDeclared := ?_
    premisesDeclared := ?_
    allPatternsScoped := scopedChecked
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := ?_ }
  · intro entry entryMembership name nameMembership
    apply requiredType_declared
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp contextChecked entry entryMembership)
      name nameMembership)
  · intro signature signatureMembership
    apply requiredSignature_declared
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp leftChecked signature signatureMembership)
  · intro signature signatureMembership
    apply requiredSignature_declared
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightChecked signature signatureMembership)
  · intro pattern patternMembership signature signatureMembership
    apply requiredSignature_declared
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp premisesChecked pattern patternMembership)
      signature signatureMembership)
  · intro name nameMembership
    apply plainName_not_constructor
    simpa using List.all_eq_true.mp fvarsChecked name nameMembership
  · intro name nameMembership
    apply plainName_not_constructor
    simpa using List.all_eq_true.mp bindersChecked name nameMembership
  · intro entry entryMembership
    apply plainName_not_constructor
    simpa using List.all_eq_true.mp contextNamesChecked entry entryMembership
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightBoundedChecked name nameMembership)

private theorem support_rewrites_checked :
    supportRewrites.all subsetCheck = true := by
  simp [supportRewrites, subsetCheck, contextSubsetCheck,
    patternSubsetCheck, premisesSubsetCheck, fvarsPlainCheck,
    bindersPlainCheck, contextNamesPlainCheck,
    RewriteValidationCertificate.allPatternsScopedCheck,
    RewriteValidationCertificate.rightBoundCheck, requiredTypes,
    requiredSignatures, resultRequiredSignatures,
    directiveRequiredSignatures, controllerRequiredSignatures,
    constructorLabelReserved, convertNames,
    convertSelection, appendString, appendEdge, appendFormulas,
    appendEdges, convertedNames, directiveNamesOne, directiveNamesCons,
    directiveImplicitAll, directiveExplicitAll, directiveNamed,
    stringsNil, stringsCons, edgesNil, edgesCons, formulasNil,
    formulasCons, selectionImplicitAll, selectionExplicitAll,
    selectionNamed, mkRule, congruence, typed, a, v,
    LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
    LanguageDef.premiseForAllParams,
    LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames]

private theorem support_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ supportRewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  apply certificate_of_subsetCheck
  exact List.all_eq_true.mp support_rewrites_checked rewrite membership

private theorem local_type_names_subset :
    ∀ name ∈ Local.language.typeNames, name ∈ language.typeNames := by
  intro name membership
  rw [typeNames_exact]
  exact List.mem_append_left _ membership

private theorem local_signatures_subset :
    ∀ signature ∈ RewriteValidationCertificate.constructorSignatures
        Local.language,
      signature ∈ RewriteValidationCertificate.constructorSignatures
        language := by
  intro signature membership
  rw [constructorSignatures_exact]
  exact List.mem_append_left _ membership

private theorem local_schema_avoids_target {rewrite : RewriteRule}
    (membership : rewrite ∈ Local.rewrites) :
    ∀ name ∈ RewriteValidationCertificateExtension.schemaNames rewrite,
      name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro name schemaMembership constructorMembership
  have plainChecked :=
    (List.all_eq_true.mp
      (TptpOfficialIncludeLocalMachinesLanguageDef.rewrite_schema_names_unreserved
        membership)) name schemaMembership
  have reservedChecked :=
    (List.all_eq_true.mp constructor_labels_reserved) name constructorMembership
  have notReserved : constructorLabelReserved name = false := by
    simpa [constructorLabelReserved,
      TptpOfficialIncludeLocalMachinesLanguageDef.constructorLabelReserved]
      using plainChecked
  simp [notReserved] at reservedChecked

private theorem local_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ Local.rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  apply RewriteValidationCertificateExtension.Certificate.embed
    (TptpOfficialIncludeLocalMachinesLanguageDef.rewrite_certificate
      rewrite membership)
  exact {
    typeNames := local_type_names_subset
    signatures := local_signatures_subset
    avoidsSchema := local_schema_avoids_target membership
  }

theorem rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  simp only [rewrites, List.mem_append] at membership
  rcases membership with localMember | supportMember
  · exact local_rewrite_certificate rewrite localMember
  · exact support_rewrite_certificate rewrite supportMember

theorem rewrite_schema_names_unreserved (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    (RewriteValidationCertificateExtension.schemaNames rewrite).all
      (fun name => !constructorLabelReserved name) = true := by
  simp only [rewrites, List.mem_append] at membership
  rcases membership with localMember | supportMember
  · simpa [constructorLabelReserved,
      TptpOfficialIncludeLocalMachinesLanguageDef.constructorLabelReserved]
      using TptpOfficialIncludeLocalMachinesLanguageDef.rewrite_schema_names_unreserved
        localMember
  · have checked :=
      List.all_eq_true.mp support_rewrites_checked rewrite supportMember
    simp only [subsetCheck, Bool.and_eq_true] at checked
    rcases checked with
      ⟨_contextChecked, _leftChecked, _rightChecked, _premisesChecked,
        _scopedChecked, fvarsChecked, bindersChecked, contextNamesChecked,
        _rightBoundedChecked⟩
    simp only [fvarsPlainCheck] at fvarsChecked
    simp only [bindersPlainCheck] at bindersChecked
    simp only [contextNamesPlainCheck] at contextNamesChecked
    exact RewriteValidationCertificateExtension.schemaNames_all_of_components
      rewrite (fun name => !constructorLabelReserved name)
        fvarsChecked bindersChecked contextNamesChecked

private theorem rewrites_valid :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] := by
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil
    language_constructor_labels_nodup
  exact rewrite_certificate rewrite membership

private theorem rewrite_names_nodup :
    (rewrites.map (·.name)).Nodup := by
  decide +kernel

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · simp [language]
  · exact rewrite_names_nodup
  · intro term membership
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate term membership
  · intro equation membership
    simp [language] at membership
  · exact rewrites_valid

def validated : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

theorem language_supported : CanonicalWire.languageSupported language := by
  have termsExact :
      language.terms = Local.language.terms ++ addedTerms := by
    simp [language, signatureLanguage, signatureCalculusLanguage,
      signatureExtension, signatureBase, signatureBaseLanguage,
      ConstructorSignatureExtension.ofLists]
  have rewritesExact :
      language.rewrites = Local.language.rewrites ++ supportRewrites := by
    rfl
  have localSupported :=
    TptpOfficialIncludeLocalMachinesLanguageDef.language_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at localSupported
  have termsSupported :
      language.terms.all CanonicalWire.grammarRuleSupported = true := by
    rw [termsExact, List.all_append, Bool.and_eq_true]
    exact ⟨localSupported.1.2, by decide +kernel⟩
  have rewritesSupported :
      language.rewrites.all CanonicalWire.rewriteSupported = true := by
    rw [rewritesExact, List.all_append, Bool.and_eq_true]
    exact ⟨localSupported.2, by decide +kernel⟩
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, termsSupported⟩, rewritesSupported⟩

theorem rewrite_count : rewrites.length = 89 := by
  decide +kernel

#print axioms language_validate
#print axioms language_supported
#print axioms rewrite_certificate
#print axioms rewrite_schema_names_unreserved
#print axioms rewrite_count

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolverSupportLanguageDef
