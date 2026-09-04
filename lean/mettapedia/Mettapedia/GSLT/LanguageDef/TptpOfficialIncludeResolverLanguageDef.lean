import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolverSupportLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeIndexSuccessor

/-!
# Recursive official TPTP include resolver

This `LanguageDef` composes the independently qualified include machines into
one depth-first resolver.  It consumes a finite source environment rather than
performing file-system effects.  Its rules make active-path cycle rejection,
source-depth fuel, textual input order, post-expansion selection, and complete
include-edge provenance explicit.

The only relation services are structural pattern equality and canonical
source-index successor.  File lookup, include binding, directive decoding,
input classification, selection, and ordered list assembly remain ordinary
declared rewrites.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolverLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

namespace Base

abbrev language := TptpOfficialIncludeResolverSupportLanguageDef.language
abbrev rewrites := TptpOfficialIncludeResolverSupportLanguageDef.rewrites

end Base

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

private def successorQuery (source target : Pattern) : Premise :=
  .relationQuery TptpOfficialIncludeIndexSuccessor.relationName
    [source, target]

private def zeroQuery (target : Pattern) : Premise :=
  .relationQuery TptpOfficialIncludeIndexSuccessor.zeroRelationName [target]

def fuelZero : Pattern := a "tptp-include-resolver:fuel-zero"
def fuelSucc (fuel : Pattern) : Pattern :=
  a "tptp-include-resolver:fuel-succ" [fuel]

def chunkOk (formulas edges : Pattern) : Pattern :=
  a "tptp-include-resolver:chunk-ok" [formulas, edges]
def chunkError (failure : Pattern) : Pattern :=
  a "tptp-include-resolver:chunk-error" [failure]

def resolve (environment root : Pattern) : Pattern :=
  a "tptp-include-resolver:resolve" [environment, root]
def rootLookupDecision (environment root outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:root-lookup-decision"
    [environment, root, outcome]
def rootChunkDecision (root digest outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:root-chunk-decision" [root, digest, outcome]
def fuelOfDocuments (documents : Pattern) : Pattern :=
  a "tptp-include-resolver:fuel-of-documents" [documents]

def resolveSource (fuel environment active path source : Pattern) : Pattern :=
  a "tptp-include-resolver:resolve-source"
    [fuel, environment, active, path, source]
def sourceMembershipDecision (decision fuel environment active path source :
    Pattern) : Pattern :=
  a "tptp-include-resolver:source-membership-decision"
    [decision, fuel, environment, active, path, source]
def sourceDocumentDecision (fuel environment active path source outcome :
    Pattern) : Pattern :=
  a "tptp-include-resolver:source-document-decision"
    [fuel, environment, active, path, source, outcome]

def resolveInputs (fuel environment active path source digest index inputs :
    Pattern) : Pattern :=
  a "tptp-include-resolver:resolve-inputs"
    [fuel, environment, active, path, source, digest, index, inputs]
def inputDecision (fuel environment active path source digest index nextIndex
    input rest outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:input-decision"
    [fuel, environment, active, path, source, digest, index, nextIndex,
      input, rest, outcome]
def prependFormula (formula outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:prepend-formula" [formula, outcome]

def includeDecision (fuel environment active path source digest index nextIndex
    rest directive span decoded : Pattern) : Pattern :=
  a "tptp-include-resolver:include-decision"
    [fuel, environment, active, path, source, digest, index, nextIndex,
      rest, directive, span, decoded]
def bindingDecision (fuel environment active path source digest index nextIndex
    rest directive span requested selection outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:binding-decision"
    [fuel, environment, active, path, source, digest, index, nextIndex,
      rest, directive, span, requested, selection, outcome]
def targetDecision (fuel environment active path source digest index nextIndex
    rest directive span requested selection target outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:target-decision"
    [fuel, environment, active, path, source, digest, index, nextIndex,
      rest, directive, span, requested, selection, target, outcome]
def childDecision (fuel environment active path source digest nextIndex rest
    edge selection target outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:child-decision"
    [fuel, environment, active, path, source, digest, nextIndex, rest,
      edge, selection, target, outcome]
def selectionDecision (fuel environment active path source digest nextIndex rest
    edge childEdges outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:selection-decision"
    [fuel, environment, active, path, source, digest, nextIndex, rest,
      edge, childEdges, outcome]
def restDecision (edge childEdges selected outcome : Pattern) : Pattern :=
  a "tptp-include-resolver:rest-decision"
    [edge, childEdges, selected, outcome]

private def stringsNil : Pattern :=
  a "tptp-include-result:strings-nil"
private def edgesNil : Pattern :=
  a "tptp-include-result:include-edges-nil"
private def edgesCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:include-edges-cons" [head, tail]
private def formulasNil : Pattern :=
  a "tptp-include-result:resolved-formulas-nil"
private def formulasCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:resolved-formulas-cons" [head, tail]
private def noString : Pattern := a "tptp-include-result:no-string"
private def resolutionError (failure : Pattern) : Pattern :=
  a "tptp-include-result:resolution-error" [failure]
private def resolutionOk (document : Pattern) : Pattern :=
  a "tptp-include-result:resolution-ok" [document]
private def resolvedDocument (root digest formulas edges : Pattern) : Pattern :=
  a "tptp-include-result:resolved-document"
    [root, digest, formulas, edges]
private def includeEdge (source index requested target targetDigest selection
    directive span : Pattern) : Pattern :=
  a "tptp-include-result:include-edge"
    [source, index, requested, target, targetDigest, selection, noString,
      directive, span]

private def sourceEnvironment (documents bindings : Pattern) : Pattern :=
  a "tptp-include-resolution:source-environment" [documents, bindings]
private def documentsNil : Pattern :=
  a "tptp-include-resolution:source-documents-nil"
private def documentsCons (head tail : Pattern) : Pattern :=
  a "tptp-include-resolution:source-documents-cons" [head, tail]
private def sourceDocument (source digest file : Pattern) : Pattern :=
  a "tptp-include-resolution:source-document" [source, digest, file]
private def includeBinding (source requested target : Pattern) : Pattern :=
  a "tptp-include-resolution:include-binding" [source, requested, target]

private def documentOk (document : Pattern) : Pattern :=
  a "tptp-include-lookup:document-ok" [document]
private def documentError (failure : Pattern) : Pattern :=
  a "tptp-include-lookup:document-error" [failure]
private def bindingOk (binding : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-ok" [binding]
private def bindingError (failure : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-error" [failure]
private def lookupDocument (source environment : Pattern) : Pattern :=
  a "tptp-include-lookup:lookup-document" [source, environment]
private def lookupBinding (source requested environment : Pattern) : Pattern :=
  a "tptp-include-lookup:lookup-binding" [source, requested, environment]

private def boolFalse : Pattern := a "tptp-include-selection:false"
private def boolTrue : Pattern := a "tptp-include-selection:true"
private def contains (needle strings : Pattern) : Pattern :=
  a "tptp-include-selection:contains" [needle, strings]
private def selectionOk (formulas : Pattern) : Pattern :=
  a "tptp-include-selection:ok" [formulas]
private def selectionError (failure : Pattern) : Pattern :=
  a "tptp-include-selection:error" [failure]
private def applySelection (target selection formulas : Pattern) : Pattern :=
  a "tptp-include-selection:apply" [target, selection, formulas]

private def formulaOutcome (formula : Pattern) : Pattern :=
  a "tptp-include-input:formula" [formula]
private def includeOutcome (directive span : Pattern) : Pattern :=
  a "tptp-include-input:include" [directive, span]
private def classify (source digest index path input : Pattern) : Pattern :=
  a "tptp-include-input:classify" [source, digest, index, path, input]

private def decodedDirective (requested selection space raw : Pattern) : Pattern :=
  a "tptp-include:decoded-directive" [requested, selection, space, raw]
private def decodeDirective (directive : Pattern) : Pattern :=
  a "tptp-include:decode-directive" [directive]
private def noSpace : Pattern := a "tptp-include:no-space"
private def someSpace (space : Pattern) : Pattern :=
  a "tptp-include:some-space" [space]

private def convertSelection (selection : Pattern) : Pattern :=
  a "tptp-include-controller:convert-selection" [selection]
private def appendString (strings value : Pattern) : Pattern :=
  a "tptp-include-controller:append-string" [strings, value]
private def appendEdge (edges edge : Pattern) : Pattern :=
  a "tptp-include-controller:append-edge" [edges, edge]
private def appendFormulas (left right : Pattern) : Pattern :=
  a "tptp-include-controller:append-formulas" [left, right]
private def appendEdges (left right : Pattern) : Pattern :=
  a "tptp-include-controller:append-edges" [left, right]

private def file (inputs : Pattern) : Pattern :=
  a "tptp92-ast:tptp-file:alt-1" [inputs]
private def inputsNil : Pattern :=
  a "tptp92-ast:list:tptp92ast-tptp-input:nil"
private def inputsCons (head tail : Pattern) : Pattern :=
  a "tptp92-ast:list:tptp92ast-tptp-input:cons" [head, tail]

private def errorCycle (path : Pattern) : Pattern :=
  a "tptp-include-result:error-cycle" [path]
private def errorDepth (path : Pattern) : Pattern :=
  a "tptp-include-result:error-source-depth-exhausted" [path]
private def errorSpace (source requested space : Pattern) : Pattern :=
  a "tptp-include-result:error-unsupported-space-namespace"
    [source, requested, space]

def supportTypes : List TypeDecl := [
  TypeDecl.plain "TptpIncludeResolver:Fuel",
  TypeDecl.plain "TptpIncludeResolver:ChunkOutcome"]

def supportTerms : List GrammarRule := [
  ctor "tptp-include-resolver:fuel-zero" "TptpIncludeResolver:Fuel" [],
  ctor "tptp-include-resolver:fuel-succ" "TptpIncludeResolver:Fuel"
    [("fuel", "TptpIncludeResolver:Fuel")],
  ctor "tptp-include-resolver:chunk-ok" "TptpIncludeResolver:ChunkOutcome"
    [("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("edges", "TptpIncludeResult:IncludeEdges")],
  ctor "tptp-include-resolver:chunk-error"
    "TptpIncludeResolver:ChunkOutcome"
    [("failure", "TptpIncludeResult:ResolutionError")],
  ctor "tptp-include-resolver:resolve" "TptpIncludeResult:ResolutionResult"
    [("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("root", "String")] (some .rewrite),
  ctor "tptp-include-resolver:root-lookup-decision"
    "TptpIncludeResult:ResolutionResult"
    [("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("root", "String"),
      ("outcome", "TptpIncludeLookup:DocumentOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:root-chunk-decision"
    "TptpIncludeResult:ResolutionResult"
    [("root", "String"), ("digest", "String"),
      ("outcome", "TptpIncludeResolver:ChunkOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:fuel-of-documents"
    "TptpIncludeResolver:Fuel"
    [("documents", "TptpIncludeResolution:SourceDocuments")]
    (some .rewrite),
  ctor "tptp-include-resolver:resolve-source"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String")] (some .rewrite),
  ctor "tptp-include-resolver:source-membership-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("decision", "TptpIncludeSelection:Bool"),
      ("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String")] (some .rewrite),
  ctor "tptp-include-resolver:source-document-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"),
      ("outcome", "TptpIncludeLookup:DocumentOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:resolve-inputs"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"),
      ("inputs", "Tptp92AstList:tptp92ast-tptp-input")]
    (some .rewrite),
  ctor "tptp-include-resolver:input-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("input", "Tptp92Ast:tptp-input"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("outcome", "TptpIncludeInput:Outcome")] (some .rewrite),
  ctor "tptp-include-resolver:prepend-formula"
    "TptpIncludeResolver:ChunkOutcome"
    [("formula", "TptpIncludeResult:ResolvedFormula"),
      ("outcome", "TptpIncludeResolver:ChunkOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:include-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"),
      ("decoded", "TptpInclude:DirectiveStep")] (some .rewrite),
  ctor "tptp-include-resolver:binding-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("outcome", "TptpIncludeLookup:BindingOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:target-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"),
      ("outcome", "TptpIncludeLookup:DocumentOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:child-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"),
      ("outcome", "TptpIncludeResolver:ChunkOutcome")] (some .rewrite),
  ctor "tptp-include-resolver:selection-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("child-edges", "TptpIncludeResult:IncludeEdges"),
      ("outcome", "TptpIncludeSelection:Outcome")] (some .rewrite),
  ctor "tptp-include-resolver:rest-decision"
    "TptpIncludeResolver:ChunkOutcome"
    [("edge", "TptpIncludeResult:IncludeEdge"),
      ("child-edges", "TptpIncludeResult:IncludeEdges"),
      ("selected", "TptpIncludeResult:ResolvedFormulas"),
      ("outcome", "TptpIncludeResolver:ChunkOutcome")] (some .rewrite)]

def rootRules : List RewriteRule := [
  mkRule "tptp-include-resolver:resolve"
    [("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("root", "String"),
      ("lookup", "TptpIncludeLookup:DocumentOutcome")]
    [congruence (lookupDocument (v "root") (v "environment")) (v "lookup")]
    (resolve (v "environment") (v "root"))
    (rootLookupDecision (v "environment") (v "root") (v "lookup")),
  mkRule "tptp-include-resolver:root-lookup-error"
    [("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("root", "String"), ("failure", "TptpIncludeResult:ResolutionError")]
    []
    (rootLookupDecision (v "environment") (v "root")
      (documentError (v "failure")))
    (resolutionError (v "failure")),
  mkRule "tptp-include-resolver:root-lookup-ok"
    [("documents", "TptpIncludeResolution:SourceDocuments"),
      ("bindings", "TptpIncludeResolution:IncludeBindings"),
      ("root", "String"), ("digest", "String"),
      ("file", "Tptp92Ast:tptp-file"),
      ("fuel", "TptpIncludeResolver:Fuel"),
      ("chunk", "TptpIncludeResolver:ChunkOutcome")]
    [congruence (fuelOfDocuments (v "documents")) (v "fuel"),
      congruence
        (resolveSource (v "fuel")
          (sourceEnvironment (v "documents") (v "bindings"))
          stringsNil edgesNil (v "root"))
        (v "chunk")]
    (rootLookupDecision
      (sourceEnvironment (v "documents") (v "bindings")) (v "root")
      (documentOk (sourceDocument (v "root") (v "digest") (v "file"))))
    (rootChunkDecision (v "root") (v "digest") (v "chunk")),
  mkRule "tptp-include-resolver:root-chunk-error"
    [("root", "String"), ("digest", "String"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (rootChunkDecision (v "root") (v "digest")
      (chunkError (v "failure")))
    (resolutionError (v "failure")),
  mkRule "tptp-include-resolver:root-chunk-ok"
    [("root", "String"), ("digest", "String"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("edges", "TptpIncludeResult:IncludeEdges")] []
    (rootChunkDecision (v "root") (v "digest")
      (chunkOk (v "formulas") (v "edges")))
    (resolutionOk
      (resolvedDocument (v "root") (v "digest")
        (v "formulas") (v "edges")))]

def fuelRules : List RewriteRule := [
  mkRule "tptp-include-resolver:fuel-nil" [] []
    (fuelOfDocuments documentsNil) (fuelSucc fuelZero),
  mkRule "tptp-include-resolver:fuel-cons"
    [("document", "TptpIncludeResolution:SourceDocument"),
      ("documents", "TptpIncludeResolution:SourceDocuments"),
      ("fuel", "TptpIncludeResolver:Fuel")]
    [congruence (fuelOfDocuments (v "documents")) (v "fuel")]
    (fuelOfDocuments (documentsCons (v "document") (v "documents")))
    (fuelSucc (v "fuel"))]

def sourceRules : List RewriteRule := [
  mkRule "tptp-include-resolver:source-membership"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("decision", "TptpIncludeSelection:Bool")]
    [congruence (contains (v "source") (v "active")) (v "decision")]
    (resolveSource (v "fuel") (v "environment") (v "active")
      (v "path") (v "source"))
    (sourceMembershipDecision (v "decision") (v "fuel")
      (v "environment") (v "active") (v "path") (v "source")),
  mkRule "tptp-include-resolver:source-cycle"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("cycle", "TptpIncludeResult:Strings")]
    [congruence (appendString (v "active") (v "source")) (v "cycle")]
    (sourceMembershipDecision boolTrue (v "fuel") (v "environment")
      (v "active") (v "path") (v "source"))
    (chunkError (errorCycle (v "cycle"))),
  mkRule "tptp-include-resolver:source-depth-exhausted"
    [("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("exhausted", "TptpIncludeResult:Strings")]
    [congruence (appendString (v "active") (v "source")) (v "exhausted")]
    (sourceMembershipDecision boolFalse fuelZero (v "environment")
      (v "active") (v "path") (v "source"))
    (chunkError (errorDepth (v "exhausted"))),
  mkRule "tptp-include-resolver:source-lookup"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"),
      ("lookup", "TptpIncludeLookup:DocumentOutcome")]
    [congruence (lookupDocument (v "source") (v "environment")) (v "lookup")]
    (sourceMembershipDecision boolFalse (fuelSucc (v "fuel"))
      (v "environment") (v "active") (v "path") (v "source"))
    (sourceDocumentDecision (v "fuel") (v "environment")
      (v "active") (v "path") (v "source") (v "lookup")),
  mkRule "tptp-include-resolver:source-lookup-error"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("failure", "TptpIncludeResult:ResolutionError")]
    []
    (sourceDocumentDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (documentError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:source-lookup-ok"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("inputs", "Tptp92AstList:tptp92ast-tptp-input"),
      ("next-active", "TptpIncludeResult:Strings"),
      ("zero", "Integer")]
    [congruence (appendString (v "active") (v "source")) (v "next-active"),
      zeroQuery (v "zero")]
    (sourceDocumentDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source")
      (documentOk (sourceDocument (v "source") (v "digest")
        (file (v "inputs")))))
    (resolveInputs (v "fuel") (v "environment") (v "next-active")
      (v "path") (v "source") (v "digest") (v "zero") (v "inputs"))]

def formulaRules : List RewriteRule := [
  mkRule "tptp-include-resolver:inputs-nil"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer")] []
    (resolveInputs (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index") inputsNil)
    (chunkOk formulasNil edgesNil),
  mkRule "tptp-include-resolver:inputs-cons"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("input", "Tptp92Ast:tptp-input"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("outcome", "TptpIncludeInput:Outcome")]
    [congruence
      (classify (v "source") (v "digest") (v "index")
        (v "path") (v "input")) (v "outcome"),
      successorQuery (v "index") (v "next-index")]
    (resolveInputs (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (inputsCons (v "input") (v "rest")))
    (inputDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "input") (v "rest") (v "outcome")),
  mkRule "tptp-include-resolver:input-formula"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("input", "Tptp92Ast:tptp-input"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("formula", "TptpIncludeResult:ResolvedFormula"),
      ("outcome", "TptpIncludeResolver:ChunkOutcome")]
    [congruence
      (resolveInputs (v "fuel") (v "environment") (v "active")
        (v "path") (v "source") (v "digest") (v "next-index")
        (v "rest")) (v "outcome")]
    (inputDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "input") (v "rest")
      (formulaOutcome (v "formula")))
    (prependFormula (v "formula") (v "outcome")),
  mkRule "tptp-include-resolver:prepend-error"
    [("formula", "TptpIncludeResult:ResolvedFormula"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (prependFormula (v "formula") (chunkError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:prepend-ok"
    [("formula", "TptpIncludeResult:ResolvedFormula"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("edges", "TptpIncludeResult:IncludeEdges")] []
    (prependFormula (v "formula")
      (chunkOk (v "formulas") (v "edges")))
    (chunkOk (formulasCons (v "formula") (v "formulas")) (v "edges"))]

def includeDecodeRules : List RewriteRule := [
  mkRule "tptp-include-resolver:input-include"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("input", "Tptp92Ast:tptp-input"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"),
      ("decoded", "TptpInclude:DirectiveStep")]
    [congruence (decodeDirective (v "directive")) (v "decoded")]
    (inputDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "input") (v "rest")
      (includeOutcome (v "directive") (v "span")))
    (includeDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "decoded")),
  mkRule "tptp-include-resolver:include-space-error"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpInclude:Selection"), ("space", "String")] []
    (includeDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (decodedDirective (v "requested") (v "selection")
        (someSpace (v "space")) (v "directive")))
    (chunkError (errorSpace (v "source") (v "requested") (v "space"))),
  mkRule "tptp-include-resolver:include-binding"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("directive-selection", "TptpInclude:Selection"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("lookup", "TptpIncludeLookup:BindingOutcome")]
    [congruence (convertSelection (v "directive-selection")) (v "selection"),
      congruence
        (lookupBinding (v "source") (v "requested") (v "environment"))
        (v "lookup")]
    (includeDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (decodedDirective (v "requested") (v "directive-selection")
        noSpace (v "directive")))
    (bindingDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "requested") (v "selection") (v "lookup"))]

def includeLookupRules : List RewriteRule := [
  mkRule "tptp-include-resolver:binding-error"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (bindingDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "requested") (v "selection") (bindingError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:binding-ok"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"),
      ("lookup", "TptpIncludeLookup:DocumentOutcome")]
    [congruence (lookupDocument (v "target") (v "environment")) (v "lookup")]
    (bindingDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "requested") (v "selection")
      (bindingOk (includeBinding (v "source") (v "requested")
        (v "target"))))
    (targetDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "requested") (v "selection") (v "target") (v "lookup")),
  mkRule "tptp-include-resolver:target-error"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (targetDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "requested") (v "selection") (v "target")
      (documentError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:target-ok"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("index", "Integer"), ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span"), ("requested", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"), ("target-digest", "String"),
      ("target-file", "Tptp92Ast:tptp-file"),
      ("child-path", "TptpIncludeResult:IncludeEdges"),
      ("child", "TptpIncludeResolver:ChunkOutcome")]
    [congruence
      (appendEdge (v "path")
        (includeEdge (v "source") (v "index") (v "requested")
          (v "target") (v "target-digest") (v "selection")
          (v "directive") (v "span")))
      (v "child-path"),
      congruence
        (resolveSource (v "fuel") (v "environment") (v "active")
          (v "child-path") (v "target"))
        (v "child")]
    (targetDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "index")
      (v "next-index") (v "rest") (v "directive") (v "span")
      (v "requested") (v "selection") (v "target")
      (documentOk
        (sourceDocument (v "target") (v "target-digest") (v "target-file"))))
    (childDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "next-index")
      (v "rest")
      (includeEdge (v "source") (v "index") (v "requested")
        (v "target") (v "target-digest") (v "selection")
        (v "directive") (v "span"))
      (v "selection") (v "target") (v "child"))]

def mergeRules : List RewriteRule := [
  mkRule "tptp-include-resolver:child-error"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (childDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "next-index")
      (v "rest") (v "edge") (v "selection") (v "target")
      (chunkError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:child-ok"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("target", "String"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("edges", "TptpIncludeResult:IncludeEdges"),
      ("outcome", "TptpIncludeSelection:Outcome")]
    [congruence
      (applySelection (v "target") (v "selection") (v "formulas"))
      (v "outcome")]
    (childDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "next-index")
      (v "rest") (v "edge") (v "selection") (v "target")
      (chunkOk (v "formulas") (v "edges")))
    (selectionDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "next-index")
      (v "rest") (v "edge") (v "edges") (v "outcome")),
  mkRule "tptp-include-resolver:selection-error"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("child-edges", "TptpIncludeResult:IncludeEdges"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (selectionDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "next-index")
      (v "rest") (v "edge") (v "child-edges")
      (selectionError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:selection-ok"
    [("fuel", "TptpIncludeResolver:Fuel"),
      ("environment", "TptpIncludeResolution:SourceEnvironment"),
      ("active", "TptpIncludeResult:Strings"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("source", "String"), ("digest", "String"),
      ("next-index", "Integer"),
      ("rest", "Tptp92AstList:tptp92ast-tptp-input"),
      ("edge", "TptpIncludeResult:IncludeEdge"),
      ("child-edges", "TptpIncludeResult:IncludeEdges"),
      ("selected", "TptpIncludeResult:ResolvedFormulas"),
      ("outcome", "TptpIncludeResolver:ChunkOutcome")]
    [congruence
      (resolveInputs (v "fuel") (v "environment") (v "active")
        (v "path") (v "source") (v "digest") (v "next-index")
        (v "rest")) (v "outcome")]
    (selectionDecision (v "fuel") (v "environment") (v "active")
      (v "path") (v "source") (v "digest") (v "next-index")
      (v "rest") (v "edge") (v "child-edges")
      (selectionOk (v "selected")))
    (restDecision (v "edge") (v "child-edges")
      (v "selected") (v "outcome")),
  mkRule "tptp-include-resolver:rest-error"
    [("edge", "TptpIncludeResult:IncludeEdge"),
      ("child-edges", "TptpIncludeResult:IncludeEdges"),
      ("selected", "TptpIncludeResult:ResolvedFormulas"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (restDecision (v "edge") (v "child-edges") (v "selected")
      (chunkError (v "failure")))
    (chunkError (v "failure")),
  mkRule "tptp-include-resolver:rest-ok"
    [("edge", "TptpIncludeResult:IncludeEdge"),
      ("child-edges", "TptpIncludeResult:IncludeEdges"),
      ("selected", "TptpIncludeResult:ResolvedFormulas"),
      ("rest-formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("rest-edges", "TptpIncludeResult:IncludeEdges"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("edges", "TptpIncludeResult:IncludeEdges")]
    [congruence (appendFormulas (v "selected") (v "rest-formulas"))
      (v "formulas"),
      congruence
        (appendEdges (edgesCons (v "edge") (v "child-edges"))
          (v "rest-edges")) (v "edges")]
    (restDecision (v "edge") (v "child-edges") (v "selected")
      (chunkOk (v "rest-formulas") (v "rest-edges")))
    (chunkOk (v "formulas") (v "edges"))]

def controllerRules : List RewriteRule :=
  rootRules ++ fuelRules ++ sourceRules ++ formulaRules ++
    includeDecodeRules ++ includeLookupRules ++ mergeRules

def addedTypes : List TypeDecl := supportTypes
def addedTerms : List GrammarRule := supportTerms
def rewrites : List RewriteRule := Base.rewrites ++ controllerRules

private def signatureBaseLanguage : LanguageDef := {
  name := Base.language.name
  types := Base.language.types
  terms := Base.language.terms
  equations := []
  rewrites := []
}

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend signatureBaseLanguage {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeResolverV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeResolverV1"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem typeNames_exact :
    language.typeNames = Base.language.typeNames ++ addedTypes.map (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, signatureBaseLanguage,
    ConstructorSignatureExtension.ofLists, LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures Base.language ++
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
        (fun name => !(name.startsWith "TptpIncludeResolver:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTypes.map (·.name)).all
        (fun name => name.startsWith "TptpIncludeResolver:") = true := by
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
        (fun label => !(label.startsWith "tptp-include-resolver:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTerms.map (·.label)).all
        (fun label => label.startsWith "tptp-include-resolver:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  have baseNot := (List.all_eq_true.mp baseSeparate) label baseMembership
  have addedYes := (List.all_eq_true.mp addedNamespaced) label addedMembership
  simp [addedYes] at baseNot

private theorem added_terms_validate_all :
    addedTerms.all
      (fun term => signatureLanguage.validateTerm term == []) = true := by
  rw [← List.take_append_drop 5 addedTerms, List.all_append,
    Bool.and_eq_true]
  constructor
  · decide +kernel
  · rw [← List.take_append_drop 5 (addedTerms.drop 5),
      List.all_append, Bool.and_eq_true]
    constructor
    · decide +kernel
    · rw [← List.take_append_drop 5 (addedTerms.drop 5 |>.drop 5),
        List.all_append, Bool.and_eq_true]
      constructor <;> decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    signatureLanguage.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

private theorem signatureBaseLanguage_validate :
    signatureBaseLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · change Base.language.typeNames.Nodup
    exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      Base.language
      TptpOfficialIncludeResolverSupportLanguageDef.language_validate
  · change (Base.language.terms.map (·.label)).Nodup
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      Base.language
      TptpOfficialIncludeResolverSupportLanguageDef.language_validate
  · simp [signatureBaseLanguage]
  · simp [signatureBaseLanguage]
  · intro term membership
    change Base.language.validateTerm term = []
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      Base.language
      TptpOfficialIncludeResolverSupportLanguageDef.language_validate
      term membership
  · intro equation membership
    simp [signatureBaseLanguage] at membership
  · intro rewrite membership
    simp [signatureBaseLanguage] at membership

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase addedTypes addedTerms
      (some "TptpOfficialIncludeResolverV1")
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

private def baseRequiredTypes : List String := [
  "String", "Integer", "TptpInclude:DirectiveStep",
  "TptpInclude:Selection", "TptpIncludeInput:Outcome",
  "TptpIncludeLookup:BindingOutcome", "TptpIncludeLookup:DocumentOutcome",
  "TptpIncludeResolution:IncludeBindings",
  "TptpIncludeResolution:SourceDocument",
  "TptpIncludeResolution:SourceDocuments",
  "TptpIncludeResolution:SourceEnvironment",
  "TptpIncludeResult:FormulaSelection", "TptpIncludeResult:IncludeEdge",
  "TptpIncludeResult:IncludeEdges", "TptpIncludeResult:ResolutionError",
  "TptpIncludeResult:ResolutionResult", "TptpIncludeResult:ResolvedDocument",
  "TptpIncludeResult:ResolvedFormula", "TptpIncludeResult:ResolvedFormulas",
  "TptpIncludeResult:Strings", "TptpIncludeSelection:Bool",
  "TptpIncludeSelection:Outcome", "Tptp92Ast:include",
  "Tptp92Ast:source-span", "Tptp92Ast:tptp-file",
  "Tptp92Ast:tptp-input", "Tptp92AstList:tptp92ast-tptp-input"]

private def resolverRequiredTypes : List String := [
  "TptpIncludeResolver:Fuel", "TptpIncludeResolver:ChunkOutcome"]

private def requiredTypes : List String :=
  baseRequiredTypes ++ resolverRequiredTypes

private def baseRequiredSignatures : List (String × Nat) := [
  ("tptp-include-lookup:lookup-document", 2),
  ("tptp-include-lookup:document-error", 1),
  ("tptp-include-lookup:document-ok", 1),
  ("tptp-include-lookup:lookup-binding", 3),
  ("tptp-include-lookup:binding-error", 1),
  ("tptp-include-lookup:binding-ok", 1),
  ("tptp-include-result:resolution-error", 1),
  ("tptp-include-result:resolution-ok", 1),
  ("tptp-include-result:resolved-document", 4),
  ("tptp-include-result:strings-nil", 0),
  ("tptp-include-result:include-edges-nil", 0),
  ("tptp-include-result:include-edges-cons", 2),
  ("tptp-include-result:resolved-formulas-nil", 0),
  ("tptp-include-result:resolved-formulas-cons", 2),
  ("tptp-include-result:include-edge", 9),
  ("tptp-include-result:no-string", 0),
  ("tptp-include-result:error-cycle", 1),
  ("tptp-include-result:error-source-depth-exhausted", 1),
  ("tptp-include-result:error-unsupported-space-namespace", 3),
  ("tptp-include-resolution:source-environment", 2),
  ("tptp-include-resolution:source-document", 3),
  ("tptp-include-resolution:source-documents-nil", 0),
  ("tptp-include-resolution:source-documents-cons", 2),
  ("tptp-include-resolution:include-binding", 3),
  ("tptp-include-selection:contains", 2),
  ("tptp-include-selection:true", 0),
  ("tptp-include-selection:false", 0),
  ("tptp-include-selection:apply", 3),
  ("tptp-include-selection:error", 1),
  ("tptp-include-selection:ok", 1),
  ("tptp-include-input:classify", 5),
  ("tptp-include-input:formula", 1),
  ("tptp-include-input:include", 2),
  ("tptp-include:decode-directive", 1),
  ("tptp-include:decoded-directive", 4),
  ("tptp-include:some-space", 1),
  ("tptp-include:no-space", 0),
  ("tptp-include-controller:append-string", 2),
  ("tptp-include-controller:append-edge", 2),
  ("tptp-include-controller:append-formulas", 2),
  ("tptp-include-controller:append-edges", 2),
  ("tptp-include-controller:convert-selection", 1),
  ("tptp92-ast:tptp-file:alt-1", 1),
  ("tptp92-ast:list:tptp92ast-tptp-input:nil", 0),
  ("tptp92-ast:list:tptp92ast-tptp-input:cons", 2)]

private def resolverRequiredSignatures : List (String × Nat) := [
  ("tptp-include-resolver:resolve", 2),
  ("tptp-include-resolver:root-lookup-decision", 3),
  ("tptp-include-resolver:root-chunk-decision", 3),
  ("tptp-include-resolver:fuel-of-documents", 1),
  ("tptp-include-resolver:resolve-source", 5),
  ("tptp-include-resolver:chunk-error", 1),
  ("tptp-include-resolver:chunk-ok", 2),
  ("tptp-include-resolver:fuel-succ", 1),
  ("tptp-include-resolver:fuel-zero", 0),
  ("tptp-include-resolver:source-membership-decision", 6),
  ("tptp-include-resolver:source-document-decision", 6),
  ("tptp-include-resolver:resolve-inputs", 8),
  ("tptp-include-resolver:input-decision", 11),
  ("tptp-include-resolver:prepend-formula", 2),
  ("tptp-include-resolver:include-decision", 12),
  ("tptp-include-resolver:binding-decision", 14),
  ("tptp-include-resolver:target-decision", 15),
  ("tptp-include-resolver:child-decision", 12),
  ("tptp-include-resolver:selection-decision", 11),
  ("tptp-include-resolver:rest-decision", 4)]

private def requiredSignatures : List (String × Nat) :=
  baseRequiredSignatures ++ resolverRequiredSignatures

private theorem base_required_types_declared :
    baseRequiredTypes.all fun name =>
      decide (name ∈ Base.language.typeNames) := by
  decide +kernel

private theorem resolver_required_types_declared :
    resolverRequiredTypes.all fun name =>
      decide (name ∈ addedTypes.map (·.name)) := by
  decide +kernel

private theorem requiredType_declared {name : String}
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames := by
  rw [typeNames_exact]
  simp only [requiredTypes, List.mem_append] at membership
  rcases membership with baseMember | resolverMember
  · exact List.mem_append_left _ <| decide_eq_true_eq.mp <|
      List.all_eq_true.mp base_required_types_declared name baseMember
  · exact List.mem_append_right _ <| decide_eq_true_eq.mp <|
      List.all_eq_true.mp resolver_required_types_declared name resolverMember

private def baseSignatureDeclared (signature : String × Nat) : Bool :=
  decide (signature ∈
    RewriteValidationCertificate.constructorSignatures Base.language)

private theorem base_required_signatures_chunk0 :
    (baseRequiredSignatures.take 8).all baseSignatureDeclared = true := by
  decide +kernel

private theorem base_required_signatures_chunk1 :
    ((baseRequiredSignatures.drop 8).take 8).all
      baseSignatureDeclared = true := by
  decide +kernel

private theorem base_required_signatures_chunk2 :
    ((baseRequiredSignatures.drop 8 |>.drop 8).take 8).all
      baseSignatureDeclared = true := by
  decide +kernel

private theorem base_required_signatures_chunk3 :
    ((baseRequiredSignatures.drop 8 |>.drop 8 |>.drop 8).take 8).all
      baseSignatureDeclared = true := by
  decide +kernel

private theorem base_required_signatures_chunk4 :
    ((baseRequiredSignatures.drop 8 |>.drop 8 |>.drop 8 |>.drop 8).take 8).all
      baseSignatureDeclared = true := by
  decide +kernel

private theorem base_required_signatures_chunk5 :
    (baseRequiredSignatures.drop 8 |>.drop 8 |>.drop 8 |>.drop 8 |>.drop 8).all
      baseSignatureDeclared = true := by
  decide +kernel

private theorem base_required_signatures_declared :
    baseRequiredSignatures.all baseSignatureDeclared = true := by
  rw [← List.take_append_drop 8 baseRequiredSignatures, List.all_append,
    Bool.and_eq_true]
  refine ⟨base_required_signatures_chunk0, ?_⟩
  · rw [← List.take_append_drop 8 (baseRequiredSignatures.drop 8),
      List.all_append, Bool.and_eq_true]
    refine ⟨base_required_signatures_chunk1, ?_⟩
    · rw [← List.take_append_drop 8
          (baseRequiredSignatures.drop 8 |>.drop 8),
        List.all_append, Bool.and_eq_true]
      refine ⟨base_required_signatures_chunk2, ?_⟩
      · rw [← List.take_append_drop 8
            (baseRequiredSignatures.drop 8 |>.drop 8 |>.drop 8),
          List.all_append, Bool.and_eq_true]
        refine ⟨base_required_signatures_chunk3, ?_⟩
        · rw [← List.take_append_drop 8
              (baseRequiredSignatures.drop 8 |>.drop 8 |>.drop 8 |>.drop 8),
            List.all_append, Bool.and_eq_true]
          exact ⟨base_required_signatures_chunk4,
            base_required_signatures_chunk5⟩

private theorem resolver_required_signatures_declared :
    resolverRequiredSignatures.all fun signature =>
      decide (signature ∈ addedTerms.map fun declaration =>
        (declaration.label, declaration.params.length)) := by
  decide +kernel

private theorem requiredSignature_declared {signature : String × Nat}
    (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures
      language := by
  rw [constructorSignatures_exact]
  simp only [requiredSignatures, List.mem_append] at membership
  rcases membership with baseMember | resolverMember
  · exact List.mem_append_left _ <| decide_eq_true_eq.mp <|
      List.all_eq_true.mp base_required_signatures_declared
        signature baseMember
  · exact List.mem_append_right _ <| decide_eq_true_eq.mp <|
      List.all_eq_true.mp resolver_required_signatures_declared
        signature resolverMember

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

local macro "certify_controller_rows" : tactic =>
  `(tactic|
    simp [controllerRules, rootRules, fuelRules, sourceRules, formulaRules,
      includeDecodeRules, includeLookupRules, mergeRules,
      subsetCheck, contextSubsetCheck,
      patternSubsetCheck, premisesSubsetCheck, fvarsPlainCheck,
      bindersPlainCheck, contextNamesPlainCheck, requiredTypes,
      baseRequiredTypes, resolverRequiredTypes, requiredSignatures,
      baseRequiredSignatures, resolverRequiredSignatures,
      constructorLabelReserved, resolve, rootLookupDecision,
      rootChunkDecision, fuelOfDocuments, resolveSource,
      sourceMembershipDecision, sourceDocumentDecision, resolveInputs,
      inputDecision, prependFormula, includeDecision, bindingDecision,
      targetDecision, childDecision, selectionDecision, restDecision,
      fuelZero, fuelSucc, chunkOk, chunkError, stringsNil, edgesNil,
      edgesCons, formulasNil, formulasCons, noString, resolutionError,
      resolutionOk, resolvedDocument, includeEdge, sourceEnvironment,
      documentsNil, documentsCons, sourceDocument, includeBinding,
      documentOk, documentError, bindingOk, bindingError, lookupDocument,
      lookupBinding, boolFalse, boolTrue, contains, selectionOk,
      selectionError, applySelection, formulaOutcome, includeOutcome,
      classify, decodedDirective, decodeDirective, noSpace, someSpace,
      convertSelection, appendString, appendEdge, appendFormulas,
      appendEdges, file, inputsNil, inputsCons, errorCycle, errorDepth,
      errorSpace, mkRule, congruence, successorQuery, zeroQuery, typed,
      a, v, LanguageDef.premisePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.rightBoundCheck])

private theorem root_rewrites_checked :
    rootRules.all subsetCheck = true := by
  certify_controller_rows

private theorem fuel_rewrites_checked :
    fuelRules.all subsetCheck = true := by
  certify_controller_rows

private theorem source_rewrites_chunk0 :
    (sourceRules.take 2).all subsetCheck = true := by
  certify_controller_rows

private theorem source_rewrites_chunk1 :
    ((sourceRules.drop 2).take 2).all subsetCheck = true := by
  certify_controller_rows

private theorem source_rewrites_chunk2 :
    (sourceRules.drop 2 |>.drop 2).all subsetCheck = true := by
  certify_controller_rows

private theorem source_rewrites_checked :
    sourceRules.all subsetCheck = true := by
  rw [← List.take_append_drop 2 sourceRules, List.all_append,
    Bool.and_eq_true]
  refine ⟨source_rewrites_chunk0, ?_⟩
  rw [← List.take_append_drop 2 (sourceRules.drop 2), List.all_append,
    Bool.and_eq_true]
  exact ⟨source_rewrites_chunk1, source_rewrites_chunk2⟩

private theorem formula_rewrites_chunk0 :
    (formulaRules.take 2).all subsetCheck = true := by
  certify_controller_rows

private theorem formula_rewrites_chunk1 :
    ((formulaRules.drop 2).take 2).all subsetCheck = true := by
  certify_controller_rows

private theorem formula_rewrites_chunk2 :
    (formulaRules.drop 2 |>.drop 2).all subsetCheck = true := by
  certify_controller_rows

private theorem formula_rewrites_checked :
    formulaRules.all subsetCheck = true := by
  rw [← List.take_append_drop 2 formulaRules, List.all_append,
    Bool.and_eq_true]
  refine ⟨formula_rewrites_chunk0, ?_⟩
  rw [← List.take_append_drop 2 (formulaRules.drop 2), List.all_append,
    Bool.and_eq_true]
  exact ⟨formula_rewrites_chunk1, formula_rewrites_chunk2⟩

private theorem include_decode_rewrite0 :
    subsetCheck (includeDecodeRules.get ⟨0, by decide⟩) = true := by
  certify_controller_rows

private theorem include_decode_rewrite1 :
    subsetCheck (includeDecodeRules.get ⟨1, by decide⟩) = true := by
  certify_controller_rows

private theorem include_decode_rewrite2 :
    subsetCheck (includeDecodeRules.get ⟨2, by decide⟩) = true := by
  certify_controller_rows

private theorem include_decode_rewrites_checked :
    includeDecodeRules.all subsetCheck = true := by
  rw [show includeDecodeRules =
    [includeDecodeRules.get ⟨0, by decide⟩,
      includeDecodeRules.get ⟨1, by decide⟩,
      includeDecodeRules.get ⟨2, by decide⟩] by rfl]
  simp only [List.all_cons, List.all_nil,
    include_decode_rewrite0, include_decode_rewrite1,
    include_decode_rewrite2, Bool.and_self]

private theorem include_lookup_rewrite0 :
    subsetCheck (includeLookupRules.get ⟨0, by decide⟩) = true := by
  certify_controller_rows

private theorem include_lookup_rewrite1 :
    subsetCheck (includeLookupRules.get ⟨1, by decide⟩) = true := by
  certify_controller_rows

private theorem include_lookup_rewrite2 :
    subsetCheck (includeLookupRules.get ⟨2, by decide⟩) = true := by
  certify_controller_rows

private def targetOkRule : RewriteRule :=
  includeLookupRules.get ⟨3, by decide⟩

private theorem target_ok_context_checked :
    contextSubsetCheck targetOkRule = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_left_checked :
    patternSubsetCheck targetOkRule.left = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_right_checked :
    patternSubsetCheck targetOkRule.right = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_premises_checked :
    premisesSubsetCheck targetOkRule = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_scoped_checked :
    RewriteValidationCertificate.allPatternsScopedCheck targetOkRule =
      true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_fvars_checked :
    fvarsPlainCheck targetOkRule = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_binders_checked :
    bindersPlainCheck targetOkRule = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_context_names_checked :
    contextNamesPlainCheck targetOkRule = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem target_ok_right_bound_checked :
    RewriteValidationCertificate.rightBoundCheck targetOkRule = true := by
  unfold targetOkRule
  certify_controller_rows

private theorem include_lookup_rewrite3 :
    subsetCheck targetOkRule = true := by
  simp only [subsetCheck, Bool.and_eq_true]
  exact ⟨target_ok_context_checked, target_ok_left_checked,
    target_ok_right_checked, target_ok_premises_checked,
    target_ok_scoped_checked, target_ok_fvars_checked,
    target_ok_binders_checked, target_ok_context_names_checked,
    target_ok_right_bound_checked⟩

private theorem include_lookup_rewrites_checked :
    includeLookupRules.all subsetCheck = true := by
  rw [show includeLookupRules =
    [includeLookupRules.get ⟨0, by decide⟩,
      includeLookupRules.get ⟨1, by decide⟩,
      includeLookupRules.get ⟨2, by decide⟩,
      targetOkRule] by rfl]
  simp only [List.all_cons, List.all_nil,
    include_lookup_rewrite0, include_lookup_rewrite1,
    include_lookup_rewrite2, include_lookup_rewrite3, Bool.and_self]

private theorem merge_rewrites_chunk0 :
    (mergeRules.take 2).all subsetCheck = true := by
  certify_controller_rows

private theorem merge_rewrites_chunk1 :
    ((mergeRules.drop 2).take 2).all subsetCheck = true := by
  certify_controller_rows

private theorem merge_rewrites_chunk2 :
    (mergeRules.drop 2 |>.drop 2).all subsetCheck = true := by
  certify_controller_rows

private theorem merge_rewrites_checked :
    mergeRules.all subsetCheck = true := by
  rw [← List.take_append_drop 2 mergeRules, List.all_append,
    Bool.and_eq_true]
  refine ⟨merge_rewrites_chunk0, ?_⟩
  rw [← List.take_append_drop 2 (mergeRules.drop 2), List.all_append,
    Bool.and_eq_true]
  exact ⟨merge_rewrites_chunk1, merge_rewrites_chunk2⟩

private theorem controller_rewrites_checked :
    controllerRules.all subsetCheck = true := by
  simp only [controllerRules, List.all_append, root_rewrites_checked,
    fuel_rewrites_checked, source_rewrites_checked,
    formula_rewrites_checked, include_decode_rewrites_checked,
    include_lookup_rewrites_checked, merge_rewrites_checked,
    Bool.and_self]

private theorem controller_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ controllerRules) :
    RewriteValidationCertificate.Certificate language rewrite := by
  apply certificate_of_subsetCheck
  exact List.all_eq_true.mp controller_rewrites_checked rewrite membership

private theorem base_type_names_subset :
    ∀ name ∈ Base.language.typeNames, name ∈ language.typeNames := by
  intro name membership
  rw [typeNames_exact]
  exact List.mem_append_left _ membership

private theorem base_signatures_subset :
    ∀ signature ∈ RewriteValidationCertificate.constructorSignatures
        Base.language,
      signature ∈ RewriteValidationCertificate.constructorSignatures
        language := by
  intro signature membership
  rw [constructorSignatures_exact]
  exact List.mem_append_left _ membership

private theorem base_schema_avoids_target {rewrite : RewriteRule}
    (membership : rewrite ∈ Base.rewrites) :
    ∀ name ∈ RewriteValidationCertificateExtension.schemaNames rewrite,
      name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro name schemaMembership constructorMembership
  have plainChecked :=
    (List.all_eq_true.mp
      (TptpOfficialIncludeResolverSupportLanguageDef.rewrite_schema_names_unreserved
        rewrite membership)) name schemaMembership
  have reservedChecked :=
    (List.all_eq_true.mp constructor_labels_reserved) name constructorMembership
  have notReserved : constructorLabelReserved name = false := by
    simpa [constructorLabelReserved,
      TptpOfficialIncludeResolverSupportLanguageDef.constructorLabelReserved]
      using plainChecked
  simp [notReserved] at reservedChecked

private theorem base_rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ Base.rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  apply RewriteValidationCertificateExtension.Certificate.embed
    (TptpOfficialIncludeResolverSupportLanguageDef.rewrite_certificate
      rewrite membership)
  exact {
    typeNames := base_type_names_subset
    signatures := base_signatures_subset
    avoidsSchema := base_schema_avoids_target membership
  }

theorem rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  simp only [rewrites, List.mem_append] at membership
  rcases membership with baseMember | controllerMember
  · exact base_rewrite_certificate rewrite baseMember
  · exact controller_rewrite_certificate rewrite controllerMember

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
      language.terms = Base.language.terms ++ addedTerms := by
    simp [language, signatureLanguage, signatureCalculusLanguage,
      signatureExtension, signatureBase, signatureBaseLanguage,
      ConstructorSignatureExtension.ofLists]
  have rewritesExact :
      language.rewrites = Base.language.rewrites ++ controllerRules := by
    rfl
  have baseSupported :=
    TptpOfficialIncludeResolverSupportLanguageDef.language_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
    at baseSupported
  have termsSupported :
      language.terms.all CanonicalWire.grammarRuleSupported = true := by
    rw [termsExact, List.all_append, Bool.and_eq_true]
    exact ⟨baseSupported.1.2, by decide +kernel⟩
  have rewritesSupported :
      language.rewrites.all CanonicalWire.rewriteSupported = true := by
    rw [rewritesExact, List.all_append, Bool.and_eq_true]
    exact ⟨baseSupported.2, by decide +kernel⟩
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, termsSupported⟩, rewritesSupported⟩

def relationTuples (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  PatternEqualityDecision.relationTuples relation arguments ++
    TptpOfficialIncludeIndexSuccessor.indexTuples relation arguments

def relations : RelationEnv where tuples := relationTuples

theorem relation_pattern_equality_exact (arguments : List Pattern) :
    relationTuples PatternEqualityDecision.relationName arguments =
      PatternEqualityDecision.relationTuples
        PatternEqualityDecision.relationName arguments := by
  simp [relationTuples, PatternEqualityDecision.relationName,
    TptpOfficialIncludeIndexSuccessor.indexTuples,
    TptpOfficialIncludeIndexSuccessor.zeroTuples,
    TptpOfficialIncludeIndexSuccessor.successorTuples]

theorem relation_successor_exact (arguments : List Pattern) :
    relationTuples TptpOfficialIncludeIndexSuccessor.relationName arguments =
      TptpOfficialIncludeIndexSuccessor.indexTuples
        TptpOfficialIncludeIndexSuccessor.relationName arguments := by
  simp [relationTuples, TptpOfficialIncludeIndexSuccessor.relationName,
    PatternEqualityDecision.relationTuples]

theorem relation_zero_exact (arguments : List Pattern) :
    relationTuples TptpOfficialIncludeIndexSuccessor.zeroRelationName arguments =
      TptpOfficialIncludeIndexSuccessor.indexTuples
        TptpOfficialIncludeIndexSuccessor.zeroRelationName arguments := by
  simp [relationTuples, TptpOfficialIncludeIndexSuccessor.zeroRelationName,
    PatternEqualityDecision.relationTuples]

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem rewrite_count : rewrites.length = 120 := by
  decide +kernel

#print axioms language_validate
#print axioms language_supported
#print axioms rewrite_certificate
#print axioms relation_pattern_equality_exact
#print axioms relation_successor_exact
#print axioms relation_zero_exact
#print axioms rewrite_count

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolverLanguageDef
