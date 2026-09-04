import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Official TPTP include-directive transformation

This finite `LanguageDef` transforms the official ParserPack include AST into
an operationally useful directive value.  It does not parse TPTP text, open
files, resolve paths, or expand includes.  Those responsibilities remain at
the source-loading and include-DAG layers.

The rules retain the complete official include node in every result.  File,
selection, and namespace projections are separate congruence steps, so the
same generic contextual runner used by other GSLT transformations can execute
the language without a TPTP-specific native decoder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) : List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String) (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := policy
}

def mkRule (name : String) (context : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule := {
  name
  typeContext := typed context
  premises
  left
  right
}

def congruence (source target : Pattern) : Premise :=
  .congruence source target

def decodeName (source : Pattern) : Pattern :=
  a "tptp-include:decode-name" [source]

def decodedName (lexeme : Pattern) : Pattern :=
  a "tptp-include:decoded-name" [lexeme]

def decodeNameList (source : Pattern) : Pattern :=
  a "tptp-include:decode-name-list" [source]

def decodedNameList (names : Pattern) : Pattern :=
  a "tptp-include:decoded-name-list" [names]

def namesOne (name : Pattern) : Pattern :=
  a "tptp-include:names-one" [name]

def namesCons (name rest : Pattern) : Pattern :=
  a "tptp-include:names-cons" [name, rest]

def decodeSelection (source : Pattern) : Pattern :=
  a "tptp-include:decode-selection" [source]

def decodedSelection (selection : Pattern) : Pattern :=
  a "tptp-include:decoded-selection" [selection]

def implicitAll : Pattern := a "tptp-include:implicit-all"
def explicitAll : Pattern := a "tptp-include:explicit-all"
def namedSelection (names : Pattern) : Pattern :=
  a "tptp-include:named-selection" [names]

def decodeFileName (source : Pattern) : Pattern :=
  a "tptp-include:decode-file-name" [source]

def decodedFileName (lexeme : Pattern) : Pattern :=
  a "tptp-include:decoded-file-name" [lexeme]

def decodeSpaceName (source : Pattern) : Pattern :=
  a "tptp-include:decode-space-name" [source]

def decodedSpaceName (lexeme : Pattern) : Pattern :=
  a "tptp-include:decoded-space-name" [lexeme]

def noSpace : Pattern := a "tptp-include:no-space"
def someSpace (lexeme : Pattern) : Pattern :=
  a "tptp-include:some-space" [lexeme]

def decodeDirective (source : Pattern) : Pattern :=
  a "tptp-include:decode-directive" [source]

def decodedDirective (file selection space raw : Pattern) : Pattern :=
  a "tptp-include:decoded-directive" [file, selection, space, raw]

def sourceToken (tokenLabel : String) (lexeme : Pattern) : Pattern :=
  a tokenLabel [lexeme]

def sourceAtomicWord (alternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a alternative [sourceToken tokenLabel lexeme]

def sourceNameWord (alternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:name:alt-1"
    [sourceAtomicWord alternative tokenLabel lexeme]

def sourceIntegerName (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:name:alt-2"
    [sourceToken "tptp92-ast:token:integer" lexeme]

def sourceFileName (alternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:file-name:alt-1"
    [sourceAtomicWord alternative tokenLabel lexeme]

def sourceDirective (file optionals : Pattern) : Pattern :=
  a "tptp92-ast:include:alt-1" [file, optionals]

def nameWordRule (name alternative tokenLabel : String) : RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (decodeName (sourceNameWord alternative tokenLabel (v "lexeme")))
    (decodedName (v "lexeme"))

def nameIntegerRule : RewriteRule :=
  mkRule "tptp-include:name-integer" [("lexeme", "String")] []
    (decodeName (sourceIntegerName (v "lexeme")))
    (decodedName (v "lexeme"))

def fileNameRule (name alternative tokenLabel : String) : RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (decodeFileName (sourceFileName alternative tokenLabel (v "lexeme")))
    (decodedFileName (v "lexeme"))

def nameListOneRule : RewriteRule :=
  mkRule "tptp-include:name-list-one"
    [("sourceName", "Tptp92Ast:name"), ("lexeme", "String")]
    [congruence (decodeName (v "sourceName"))
      (decodedName (v "lexeme"))]
    (decodeNameList (a "tptp92-ast:name-list:alt-1" [v "sourceName"]))
    (decodedNameList (namesOne (v "lexeme")))

def nameListConsRule : RewriteRule :=
  mkRule "tptp-include:name-list-cons"
    [("sourceName", "Tptp92Ast:name"),
     ("sourceRest", "Tptp92Ast:name-list"),
     ("lexeme", "String"), ("decodedRest", "TptpInclude:Names")]
    [congruence (decodeName (v "sourceName"))
        (decodedName (v "lexeme")),
     congruence (decodeNameList (v "sourceRest"))
        (decodedNameList (v "decodedRest"))]
    (decodeNameList (a "tptp92-ast:name-list:alt-2"
      [v "sourceName", v "sourceRest"]))
    (decodedNameList (namesCons (v "lexeme") (v "decodedRest")))

def selectionNamedRule : RewriteRule :=
  mkRule "tptp-include:selection-named"
    [("sourceNames", "Tptp92Ast:name-list"),
     ("decodedNames", "TptpInclude:Names")]
    [congruence (decodeNameList (v "sourceNames"))
      (decodedNameList (v "decodedNames"))]
    (decodeSelection (a "tptp92-ast:formula-selection:alt-1"
      [v "sourceNames"]))
    (decodedSelection (namedSelection (v "decodedNames")))

def selectionExplicitAllRule : RewriteRule :=
  mkRule "tptp-include:selection-explicit-all" [] []
    (decodeSelection (a "tptp92-ast:formula-selection:alt-2"))
    (decodedSelection explicitAll)

def spaceNameRule : RewriteRule :=
  mkRule "tptp-include:space-name"
    [("sourceName", "Tptp92Ast:name"), ("lexeme", "String")]
    [congruence (decodeName (v "sourceName"))
      (decodedName (v "lexeme"))]
    (decodeSpaceName (a "tptp92-ast:space-name:alt-1" [v "sourceName"]))
    (decodedSpaceName (v "lexeme"))

def directiveImplicitRule : RewriteRule :=
  let optionals := a "tptp92-ast:include-optionals:alt-1"
  mkRule "tptp-include:directive-implicit-all"
    [("sourceFile", "Tptp92Ast:file-name"), ("file", "String")]
    [congruence (decodeFileName (v "sourceFile"))
      (decodedFileName (v "file"))]
    (decodeDirective (sourceDirective (v "sourceFile") optionals))
    (decodedDirective (v "file") implicitAll noSpace
      (sourceDirective (v "sourceFile") optionals))

def directiveSelectionRule : RewriteRule :=
  let optionals := a "tptp92-ast:include-optionals:alt-2"
    [v "sourceSelection"]
  mkRule "tptp-include:directive-selection"
    [("sourceFile", "Tptp92Ast:file-name"),
     ("sourceSelection", "Tptp92Ast:formula-selection"),
     ("file", "String"), ("selection", "TptpInclude:Selection")]
    [congruence (decodeFileName (v "sourceFile"))
        (decodedFileName (v "file")),
     congruence (decodeSelection (v "sourceSelection"))
        (decodedSelection (v "selection"))]
    (decodeDirective (sourceDirective (v "sourceFile") optionals))
    (decodedDirective (v "file") (v "selection") noSpace
      (sourceDirective (v "sourceFile") optionals))

def directiveSpaceRule : RewriteRule :=
  let optionals := a "tptp92-ast:include-optionals:alt-3"
    [v "sourceSelection", v "sourceSpace"]
  mkRule "tptp-include:directive-space"
    [("sourceFile", "Tptp92Ast:file-name"),
     ("sourceSelection", "Tptp92Ast:formula-selection"),
     ("sourceSpace", "Tptp92Ast:space-name"),
     ("file", "String"), ("selection", "TptpInclude:Selection"),
     ("space", "String")]
    [congruence (decodeFileName (v "sourceFile"))
        (decodedFileName (v "file")),
     congruence (decodeSelection (v "sourceSelection"))
        (decodedSelection (v "selection")),
     congruence (decodeSpaceName (v "sourceSpace"))
        (decodedSpaceName (v "space"))]
    (decodeDirective (sourceDirective (v "sourceFile") optionals))
    (decodedDirective (v "file") (v "selection") (someSpace (v "space"))
      (sourceDirective (v "sourceFile") optionals))

def rewrites : List RewriteRule := [
  nameWordRule "tptp-include:name-lower"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
  nameWordRule "tptp-include:name-single-quoted"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  nameWordRule "tptp-include:name-back-quoted"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted",
  nameIntegerRule,
  fileNameRule "tptp-include:file-lower"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
  fileNameRule "tptp-include:file-single-quoted"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  fileNameRule "tptp-include:file-back-quoted"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted",
  nameListOneRule,
  nameListConsRule,
  selectionNamedRule,
  selectionExplicitAllRule,
  spaceNameRule,
  directiveImplicitRule,
  directiveSelectionRule,
  directiveSpaceRule]

def addedTypes : List TypeDecl := [
  "TptpInclude:Names",
  "TptpInclude:Selection",
  "TptpInclude:Space",
  "TptpInclude:NameStep",
  "TptpInclude:NameListStep",
  "TptpInclude:SelectionStep",
  "TptpInclude:FileNameStep",
  "TptpInclude:SpaceNameStep",
  "TptpInclude:DirectiveStep"]

def addedTerms : List GrammarRule := [
  ctor "tptp-include:names-one" "TptpInclude:Names" [("name", "String")],
  ctor "tptp-include:names-cons" "TptpInclude:Names"
    [("name", "String"), ("rest", "TptpInclude:Names")],
  ctor "tptp-include:implicit-all" "TptpInclude:Selection" [],
  ctor "tptp-include:explicit-all" "TptpInclude:Selection" [],
  ctor "tptp-include:named-selection" "TptpInclude:Selection"
    [("names", "TptpInclude:Names")],
  ctor "tptp-include:no-space" "TptpInclude:Space" [],
  ctor "tptp-include:some-space" "TptpInclude:Space" [("name", "String")],
  ctor "tptp-include:decode-name" "TptpInclude:NameStep"
    [("source", "Tptp92Ast:name")] (some .rewrite),
  ctor "tptp-include:decoded-name" "TptpInclude:NameStep"
    [("name", "String")],
  ctor "tptp-include:decode-name-list" "TptpInclude:NameListStep"
    [("source", "Tptp92Ast:name-list")] (some .rewrite),
  ctor "tptp-include:decoded-name-list" "TptpInclude:NameListStep"
    [("names", "TptpInclude:Names")],
  ctor "tptp-include:decode-selection" "TptpInclude:SelectionStep"
    [("source", "Tptp92Ast:formula-selection")] (some .rewrite),
  ctor "tptp-include:decoded-selection" "TptpInclude:SelectionStep"
    [("selection", "TptpInclude:Selection")],
  ctor "tptp-include:decode-file-name" "TptpInclude:FileNameStep"
    [("source", "Tptp92Ast:file-name")] (some .rewrite),
  ctor "tptp-include:decoded-file-name" "TptpInclude:FileNameStep"
    [("name", "String")],
  ctor "tptp-include:decode-space-name" "TptpInclude:SpaceNameStep"
    [("source", "Tptp92Ast:space-name")] (some .rewrite),
  ctor "tptp-include:decoded-space-name" "TptpInclude:SpaceNameStep"
    [("name", "String")],
  ctor "tptp-include:decode-directive" "TptpInclude:DirectiveStep"
    [("source", "Tptp92Ast:include")] (some .rewrite),
  ctor "tptp-include:decoded-directive" "TptpInclude:DirectiveStep"
    [("file", "String"), ("selection", "TptpInclude:Selection"),
     ("space", "TptpInclude:Space"), ("raw", "Tptp92Ast:include")]]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialAbstractSyntax.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeDirectiveV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeDirective"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.typeNames (addedTypes.map (·.name)) := by
  rw [List.disjoint_left]
  intro name sourceMembership addedMembership
  simp [addedTypes] at addedMembership
  rcases addedMembership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change _ ∈ TptpOfficialAbstractSyntax.language.typeNames at sourceMembership
    revert sourceMembership
    decide +kernel

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have sourceNamespaced :
      (signatureBase.terms.map (·.label)).all
        (fun label => label.startsWith "tptp92-ast:") = true := by
    decide +kernel
  have addedSeparate :
      (addedTerms.map (·.label)).all
        (fun label => !(label.startsWith "tptp92-ast:")) = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label sourceMembership addedMembership
  have sourcePrefix :=
    (List.all_eq_true.mp sourceNamespaced) label sourceMembership
  have targetNotPrefix :=
    (List.all_eq_true.mp addedSeparate) label addedMembership
  simp [sourcePrefix] at targetNotPrefix

private theorem added_terms_validate_all :
    addedTerms.all (fun term => signatureLanguage.validateTerm term == []) =
      true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    signatureLanguage.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase addedTypes addedTerms
      (some "TptpOfficialIncludeDirectiveV1")
  · simpa [signatureBase] using TptpOfficialAbstractSyntax.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

@[simp] theorem typeNames_exact :
    language.typeNames = TptpOfficialAbstractSyntax.language.typeNames ++
      addedTypes.map (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpOfficialAbstractSyntax.language ++
      addedTerms.map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

@[simp] theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpOfficialAbstractSyntax.language ++ addedTerms.map (·.label) := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp" ||
    label.startsWith "pattern-equality-decision:"

theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  rw [constructorLabels_exact, List.all_append, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro label membership
    have official := (List.all_eq_true.mp
      TptpOfficialAbstractSyntax.constructorLabels_namespaced)
        label membership
    have longPrefix : "tptp92-ast:".toList <+: label.toList := by
      simpa [String.startsWith_string_iff] using official
    have shortPrefix : "tptp".toList <+: "tptp92-ast:".toList := by
      decide
    simp only [constructorLabelNamespaced, Bool.or_eq_true,
      String.startsWith_string_iff]
    exact Or.inl (shortPrefix.trans longPrefix)
  · decide +kernel

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelNamespaced name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have namespaced := (List.all_eq_true.mp constructorLabels_namespaced)
    name membership
  simp [plain] at namespaced

private def requiredTypes : List String := [
  "String", "Tptp92Ast:name", "Tptp92Ast:name-list",
  "Tptp92Ast:formula-selection", "Tptp92Ast:file-name",
  "Tptp92Ast:space-name", "Tptp92Ast:include", "TptpInclude:Names",
  "TptpInclude:Selection", "TptpInclude:Space", "TptpInclude:NameStep",
  "TptpInclude:NameListStep", "TptpInclude:SelectionStep",
  "TptpInclude:FileNameStep", "TptpInclude:SpaceNameStep",
  "TptpInclude:DirectiveStep"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) =
      true := by
  decide +kernel

@[simp] private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp92-ast:atomic-word:alt-1", 1),
  ("tptp92-ast:atomic-word:alt-2", 1),
  ("tptp92-ast:atomic-word:alt-3", 1),
  ("tptp92-ast:token:lower-word", 1),
  ("tptp92-ast:token:single-quoted", 1),
  ("tptp92-ast:token:back-quoted", 1),
  ("tptp92-ast:token:integer", 1),
  ("tptp92-ast:name:alt-1", 1), ("tptp92-ast:name:alt-2", 1),
  ("tptp92-ast:file-name:alt-1", 1),
  ("tptp92-ast:name-list:alt-1", 1),
  ("tptp92-ast:name-list:alt-2", 2),
  ("tptp92-ast:formula-selection:alt-1", 1),
  ("tptp92-ast:formula-selection:alt-2", 0),
  ("tptp92-ast:space-name:alt-1", 1),
  ("tptp92-ast:include-optionals:alt-1", 0),
  ("tptp92-ast:include-optionals:alt-2", 1),
  ("tptp92-ast:include-optionals:alt-3", 2),
  ("tptp92-ast:include:alt-1", 2),
  ("tptp-include:names-one", 1), ("tptp-include:names-cons", 2),
  ("tptp-include:implicit-all", 0), ("tptp-include:explicit-all", 0),
  ("tptp-include:named-selection", 1), ("tptp-include:no-space", 0),
  ("tptp-include:some-space", 1), ("tptp-include:decode-name", 1),
  ("tptp-include:decoded-name", 1),
  ("tptp-include:decode-name-list", 1),
  ("tptp-include:decoded-name-list", 1),
  ("tptp-include:decode-selection", 1),
  ("tptp-include:decoded-selection", 1),
  ("tptp-include:decode-file-name", 1),
  ("tptp-include:decoded-file-name", 1),
  ("tptp-include:decode-space-name", 1),
  ("tptp-include:decoded-space-name", 1),
  ("tptp-include:decode-directive", 1),
  ("tptp-include:decoded-directive", 4)]

private theorem requiredSignatures_declared :
    requiredSignatures.all (fun signature => decide
      (signature ∈ RewriteValidationCertificate.constructorSignatures
        language)) = true := by
  decide +kernel

@[simp] private theorem requiredSignature_declared
    (signature : String × Nat) (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures language :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredSignatures_declared signature membership)

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
    !constructorLabelNamespaced name

private def bindersPlainCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternBinderNames rewrite.left ++
    LanguageDef.patternBinderNames rewrite.right ++
    (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
      LanguageDef.patternBinderNames ++
    rewrite.premises.flatMap
      LanguageDef.premiseForAllParams).eraseDups).all fun name =>
    !constructorLabelNamespaced name

private def contextNamesPlainCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    !constructorLabelNamespaced entry.1

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
    apply requiredType_declared name
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp contextChecked entry entryMembership)
      name nameMembership)
  · intro signature signatureMembership
    apply requiredSignature_declared signature
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp leftChecked signature signatureMembership)
  · intro signature signatureMembership
    apply requiredSignature_declared signature
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightChecked signature signatureMembership)
  · intro pattern patternMembership signature signatureMembership
    apply requiredSignature_declared signature
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp premisesChecked pattern patternMembership)
      signature signatureMembership)
  · intro name nameMembership
    apply plainName_not_constructor name
    have plain := List.all_eq_true.mp fvarsChecked name nameMembership
    simpa using plain
  · intro name nameMembership
    apply plainName_not_constructor name
    have plain := List.all_eq_true.mp bindersChecked name nameMembership
    simpa using plain
  · intro entry entryMembership
    apply plainName_not_constructor entry.1
    have plain := List.all_eq_true.mp contextNamesChecked entry entryMembership
    simpa using plain
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightBoundedChecked name nameMembership)

local macro "certify_subset_row" : tactic =>
  `(tactic|
    simp [subsetCheck, contextSubsetCheck, patternSubsetCheck,
      premisesSubsetCheck, fvarsPlainCheck, bindersPlainCheck,
      contextNamesPlainCheck, nameWordRule, nameIntegerRule, fileNameRule,
      nameListOneRule, nameListConsRule, selectionNamedRule,
      selectionExplicitAllRule, spaceNameRule, directiveImplicitRule,
      directiveSelectionRule, directiveSpaceRule, sourceNameWord,
      sourceIntegerName, sourceFileName, sourceAtomicWord, sourceToken,
      sourceDirective, decodeName, decodedName, decodeNameList,
      decodedNameList, namesOne, namesCons, decodeSelection,
      decodedSelection, implicitAll, explicitAll, namedSelection,
      decodeFileName, decodedFileName, decodeSpaceName, decodedSpaceName,
      noSpace, someSpace, decodeDirective, decodedDirective, mkRule,
      congruence, typed, a, v, LanguageDef.premisePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead, requiredTypes,
      requiredSignatures, constructorLabelNamespaced,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.rightBoundCheck])

private theorem subset00_checked : subsetCheck
    (nameWordRule "tptp-include:name-lower"
      "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word") =
      true := by certify_subset_row
private theorem subset01_checked : subsetCheck
    (nameWordRule "tptp-include:name-single-quoted"
      "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted") =
      true := by certify_subset_row
private theorem subset02_checked : subsetCheck
    (nameWordRule "tptp-include:name-back-quoted"
      "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted") =
      true := by certify_subset_row
private theorem subset03_checked : subsetCheck nameIntegerRule = true := by
  certify_subset_row
private theorem subset04_checked : subsetCheck
    (fileNameRule "tptp-include:file-lower"
      "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word") =
      true := by certify_subset_row
private theorem subset05_checked : subsetCheck
    (fileNameRule "tptp-include:file-single-quoted"
      "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted") =
      true := by certify_subset_row
private theorem subset06_checked : subsetCheck
    (fileNameRule "tptp-include:file-back-quoted"
      "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted") =
      true := by certify_subset_row
private theorem subset07_checked : subsetCheck nameListOneRule = true := by
  certify_subset_row
private theorem subset08_checked : subsetCheck nameListConsRule = true := by
  certify_subset_row
private theorem subset09_checked : subsetCheck selectionNamedRule = true := by
  certify_subset_row
private theorem subset10_checked : subsetCheck selectionExplicitAllRule =
    true := by certify_subset_row
private theorem subset11_checked : subsetCheck spaceNameRule = true := by
  certify_subset_row
private theorem subset12_checked : subsetCheck directiveImplicitRule = true := by
  certify_subset_row
private theorem subset13_checked : subsetCheck directiveSelectionRule = true := by
  certify_subset_row
private theorem subset14_checked : subsetCheck directiveSpaceRule = true := by
  certify_subset_row

private theorem every_rewrite_subset_checked (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) : subsetCheck rewrite = true := by
  simp only [rewrites, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact subset00_checked
  · exact subset01_checked
  · exact subset02_checked
  · exact subset03_checked
  · exact subset04_checked
  · exact subset05_checked
  · exact subset06_checked
  · exact subset07_checked
  · exact subset08_checked
  · exact subset09_checked
  · exact subset10_checked
  · exact subset11_checked
  · exact subset12_checked
  · exact subset13_checked
  · exact subset14_checked

private theorem every_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite :=
  certificate_of_subsetCheck
    (every_rewrite_subset_checked rewrite membership)

/-- Reusable row certificate for linking the directive decoder into a larger
capture-free operational language. -/
theorem rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite :=
  every_rewrite_certificate rewrite membership

theorem rewrite_schema_names_unreserved (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    (RewriteValidationCertificateExtension.schemaNames rewrite).all
      (fun name => !constructorLabelNamespaced name) = true := by
  have checked := every_rewrite_subset_checked rewrite membership
  simp only [subsetCheck, Bool.and_eq_true] at checked
  rcases checked with
    ⟨_contextChecked, _leftChecked, _rightChecked, _premisesChecked,
      _scopedChecked, fvarsChecked, bindersChecked, contextNamesChecked,
      _rightBoundedChecked⟩
  simp only [fvarsPlainCheck] at fvarsChecked
  simp only [bindersPlainCheck] at bindersChecked
  simp only [contextNamesPlainCheck] at contextNamesChecked
  exact RewriteValidationCertificateExtension.schemaNames_all_of_components
    rewrite (fun name => !constructorLabelNamespaced name)
      fvarsChecked bindersChecked contextNamesChecked

private theorem rewrite_names_nodup :
    (rewrites.map (·.name)).Nodup := by
  decide +kernel

private theorem constructor_labels_nodup :
    (language.terms.map (·.label)).Nodup := by
  simpa [language] using
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate

private theorem rewrites_valid :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] := by
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil
    constructor_labels_nodup
  exact every_rewrite_certificate rewrite membership

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

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

private theorem source_supported :
    CanonicalWire.languageSupported TptpOfficialAbstractSyntax.language := by
  rw [← CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact TptpOfficialAbstractSyntax.wire_isSome

private theorem language_terms :
    language.terms = TptpOfficialAbstractSyntax.language.terms ++ addedTerms := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists]

private theorem terms_supported :
    language.terms.all CanonicalWire.grammarRuleSupported = true := by
  have source := source_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at source
  rw [language_terms, List.all_append]
  simp [source.1.2, addedTerms, ctor, CanonicalWire.grammarRuleSupported,
    CanonicalWire.termParamSupported, CanonicalWire.typeExprSupported]

private theorem rewrites_supported :
    language.rewrites.all CanonicalWire.rewriteSupported = true := by
  decide +kernel

theorem language_supported : CanonicalWire.languageSupported language := by
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, terms_supported⟩, rewrites_supported⟩

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

namespace Canary

def lexeme (value : String) : Pattern := a value

def quotedFile (value : String) : Pattern :=
  sourceFileName "tptp92-ast:atomic-word:alt-2"
    "tptp92-ast:token:single-quoted" (lexeme value)

def lowerName (value : String) : Pattern :=
  sourceNameWord "tptp92-ast:atomic-word:alt-1"
    "tptp92-ast:token:lower-word" (lexeme value)

def oneNameSelection (value : String) : Pattern :=
  a "tptp92-ast:formula-selection:alt-1"
    [a "tptp92-ast:name-list:alt-1" [lowerName value]]

def implicitDirective : Pattern :=
  sourceDirective (quotedFile "Axioms/SET001.ax")
    (a "tptp92-ast:include-optionals:alt-1")

def malformedDirective : Pattern :=
  sourceDirective (quotedFile "Axioms/SET001.ax")
    (a "tptp92-ast:include-optionals:invented")

theorem independent_decoder_accepts_implicit :
    TptpOfficialIncludeResolution.decodeIncludeDirective? implicitDirective =
      some {
        requestedFile := "Axioms/SET001.ax"
        selection := .implicitAll
        spaceName := none
        raw := implicitDirective } := by
  rfl

theorem independent_decoder_rejects_malformed :
    TptpOfficialIncludeResolution.decodeIncludeDirective? malformedDirective =
      none := by
  rfl

end Canary

#print axioms signatureLanguage_validate
#print axioms language_validate
#print axioms language_supported
#print axioms Canary.independent_decoder_accepts_implicit
#print axioms Canary.independent_decoder_rejects_malformed

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveLanguageDef
