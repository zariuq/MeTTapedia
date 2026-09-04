import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement

/-!
# Official TPTP include-DAG resolution

The concrete parser produces official TPTP ASTs.  File lookup and path
canonicalization are effects of the source-loading boundary, so this module
does not read files or normalize path strings.  Instead it consumes a finite
environment whose documents have canonical source identities and whose
include bindings record the result of resolving one request from one source.

Resolution expands includes at their textual positions, rejects active-path
cycles, and applies formula selection after recursively expanding the target
file.  This is the selection behavior specified by the TPTP documentation:
every requested name must occur exactly once in the expanded target, while
the selected formulae retain source order rather than request-list order.

Each flattened formula retains its canonical source, source digest, local
input index, and complete include-edge path.  The downstream derivation still
uses one dense occurrence space for chronological checking; this module
retains the exact map from those flattened positions back to source
occurrences.

The optional include namespace is not inert metadata: it renames formulae and
symbols throughout the included hierarchy.  Until that renaming is supplied
by a separate source-preserving transformation, namespaced includes are
rejected explicitly rather than silently interpreted as ordinary includes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialSourceLocation
open Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-! ## Exact views of official include syntax -/

inductive FormulaSelection where
  | implicitAll
  | explicitAll
  | named (names : List String)
  deriving DecidableEq, Repr

structure IncludeDirectiveView where
  requestedFile : String
  selection : FormulaSelection
  spaceName : Option String
  raw : Pattern
  deriving DecidableEq, Repr

/-- Decode an official atomic word while checking the token class prescribed
by its ParserPack alternative.  The shared derivation-level lexical projection
is intentionally more permissive; include admission needs this exact boundary
so a malformed token-class substitution cannot become a source request. -/
def decodeCanonicalAtomicWord? : Pattern -> Option String
  | .apply "tptp92-ast:atomic-word:alt-1"
      [.apply "tptp92-ast:token:lower-word" [.apply lexeme []]] =>
      some lexeme
  | .apply "tptp92-ast:atomic-word:alt-2"
      [.apply "tptp92-ast:token:single-quoted" [.apply lexeme []]] =>
      some lexeme
  | .apply "tptp92-ast:atomic-word:alt-3"
      [.apply "tptp92-ast:token:back-quoted" [.apply lexeme []]] =>
      some lexeme
  | _ => none

/-- Exact official name projection for include selection and namespace data. -/
def decodeCanonicalName? : Pattern -> Option String
  | .apply "tptp92-ast:name:alt-1" [word] =>
      decodeCanonicalAtomicWord? word
  | .apply "tptp92-ast:name:alt-2"
      [.apply "tptp92-ast:token:integer" [.apply lexeme []]] =>
      some lexeme
  | _ => none

def decodeFileName? : Pattern -> Option String
  | .apply "tptp92-ast:file-name:alt-1" [word] =>
      decodeCanonicalAtomicWord? word
  | _ => none

def decodeSpaceName? : Pattern -> Option String
  | .apply "tptp92-ast:space-name:alt-1" [name] =>
      decodeCanonicalName? name
  | _ => none

def decodeNameList? : Pattern -> Option (List String)
  | .apply "tptp92-ast:name-list:alt-1" [name] => do
      let decoded <- decodeCanonicalName? name
      some [decoded]
  | .apply "tptp92-ast:name-list:alt-2" [name, rest] => do
      let decoded <- decodeCanonicalName? name
      let decodedRest <- decodeNameList? rest
      some (decoded :: decodedRest)
  | _ => none

def decodeFormulaSelection? : Pattern -> Option FormulaSelection
  | .apply "tptp92-ast:formula-selection:alt-1" [names] => do
      let decoded <- decodeNameList? names
      some (.named decoded)
  | .apply "tptp92-ast:formula-selection:alt-2" [] =>
      some .explicitAll
  | _ => none

def decodeIncludeDirective? (directive : Pattern) :
    Option IncludeDirectiveView :=
  match directive with
  | .apply "tptp92-ast:include:alt-1" [fileName, optionals] => do
      let requestedFile <- decodeFileName? fileName
      match optionals with
      | .apply "tptp92-ast:include-optionals:alt-1" [] =>
          some {
            requestedFile := requestedFile
            selection := .implicitAll
            spaceName := none
            raw := directive
          }
      | .apply "tptp92-ast:include-optionals:alt-2" [selection] => do
          let decodedSelection <- decodeFormulaSelection? selection
          some {
            requestedFile := requestedFile
            selection := decodedSelection
            spaceName := none
            raw := directive
          }
      | .apply "tptp92-ast:include-optionals:alt-3"
          [selection, spaceName] => do
          let decodedSelection <- decodeFormulaSelection? selection
          let decodedSpaceName <- decodeSpaceName? spaceName
          some {
            requestedFile := requestedFile
            selection := decodedSelection
            spaceName := some decodedSpaceName
            raw := directive
          }
      | _ => none
  | _ => none

/-! ## Loader-supplied finite source environment -/

/-- One parsed source file after the loading boundary has assigned its
canonical identity and authenticated content digest. -/
structure SourceDocument where
  canonicalId : String
  digest : String
  officialFile : Pattern
  deriving DecidableEq, Repr

/-- Resolution of one include spelling relative to one canonical source.
Different parent sources may lawfully bind the same spelling differently. -/
structure IncludeBinding where
  fromSource : String
  requestedFile : String
  targetSource : String
  deriving DecidableEq, Repr

structure SourceEnvironment where
  documents : List SourceDocument
  bindings : List IncludeBinding
  deriving DecidableEq, Repr

inductive ResolutionError where
  | missingDocument (canonicalId : String)
  | ambiguousDocument (canonicalId : String)
  | missingBinding (fromSource requestedFile : String)
  | ambiguousBinding (fromSource requestedFile : String)
  | malformedDocument (canonicalId : String)
  | malformedInput (canonicalId : String) (inputIndex : Nat)
  | malformedFormula (canonicalId : String) (inputIndex : Nat)
  | malformedInclude (canonicalId : String) (inputIndex : Nat)
  | duplicateSelectionName (targetSource name : String)
  | missingSelectionName (targetSource name : String)
  | ambiguousSelectionName (targetSource name : String)
  | unsupportedSpaceNamespace
      (fromSource requestedFile spaceName : String)
  | cycle (canonicalPath : List String)
  | sourceDepthExhausted (canonicalPath : List String)
  | refinementRejected (rootSource resolutionDigest : String)
  deriving DecidableEq, Repr

def documentsNamed (environment : SourceEnvironment) (canonicalId : String) :
    List SourceDocument :=
  environment.documents.filter (fun document => document.canonicalId = canonicalId)

def lookupDocument (environment : SourceEnvironment) (canonicalId : String) :
    Except ResolutionError SourceDocument :=
  match documentsNamed environment canonicalId with
  | [] => .error (.missingDocument canonicalId)
  | [document] => .ok document
  | _ => .error (.ambiguousDocument canonicalId)

def bindingsFor (environment : SourceEnvironment)
    (fromSource requestedFile : String) : List IncludeBinding :=
  environment.bindings.filter (fun binding =>
    binding.fromSource = fromSource && binding.requestedFile = requestedFile)

def lookupBinding (environment : SourceEnvironment)
    (fromSource requestedFile : String) :
    Except ResolutionError IncludeBinding :=
  match bindingsFor environment fromSource requestedFile with
  | [] => .error (.missingBinding fromSource requestedFile)
  | [binding] => .ok binding
  | _ => .error (.ambiguousBinding fromSource requestedFile)

/-! ## Provenance-bearing flattened formulae -/

structure IncludeEdge where
  fromSource : String
  fromInputIndex : Nat
  requestedFile : String
  targetSource : String
  targetDigest : String
  selection : FormulaSelection
  spaceName : Option String
  directive : Pattern
  span : Pattern
  deriving DecidableEq, Repr

structure FormulaOrigin where
  sourceId : String
  sourceDigest : String
  sourceInputIndex : Nat
  includePath : List IncludeEdge
  deriving DecidableEq, Repr

structure ResolvedFormula where
  name : String
  input : Pattern
  origin : FormulaOrigin
  deriving DecidableEq, Repr

structure ResolutionChunk where
  formulas : List ResolvedFormula
  edges : List IncludeEdge
  deriving DecidableEq, Repr

def ResolutionChunk.append (left right : ResolutionChunk) : ResolutionChunk := {
  formulas := left.formulas ++ right.formulas
  edges := left.edges ++ right.edges
}

structure ResolvedDocument where
  rootSource : String
  rootDigest : String
  formulas : List ResolvedFormula
  edges : List IncludeEdge
  deriving DecidableEq, Repr

def ResolvedDocument.officialInputs (resolved : ResolvedDocument) : List Pattern :=
  resolved.formulas.map ResolvedFormula.input

def ResolvedDocument.officialFile (resolved : ResolvedDocument) : Pattern :=
  a "tptp92-ast:tptp-file:alt-1"
    [encodeOfficialInputs resolved.officialInputs]

def ResolvedDocument.provenance (resolved : ResolvedDocument) :
    List FormulaOrigin :=
  resolved.formulas.map ResolvedFormula.origin

def decodeFormulaName? (input : Pattern) : Option String := do
  let semantic <- refineOfficialFormulaInput? (a "include-resolution-probe") input
  let formula <- decodeAnnotatedFormula? semantic.payload
  decodeCanonicalName? formula.name

theorem refine_formula_occurrence {assigned input : Pattern}
    {view : AnnotatedInputView}
    (refined : refineOfficialFormulaInput? assigned input = some view) :
    view.occurrence = assigned := by
  cases input with
  | bvar index => simp [refineOfficialFormulaInput?] at refined
  | fvar name => simp [refineOfficialFormulaInput?] at refined
  | apply label arguments =>
      simp only [refineOfficialFormulaInput?] at refined
      split at refined <;> try contradiction
      all_goals
        cases refined
        rfl
  | lambda name body => simp [refineOfficialFormulaInput?] at refined
  | multiLambda count names body =>
      simp [refineOfficialFormulaInput?] at refined
  | subst body replacement => simp [refineOfficialFormulaInput?] at refined
  | collection kind elements rest =>
      simp [refineOfficialFormulaInput?] at refined

def assignedOccurrences (source : Pattern) :
    Nat -> List Pattern -> List Pattern
  | _, [] => []
  | index, _ :: inputs =>
      occurrence source index :: assignedOccurrences source (index + 1) inputs

theorem refineInputs?_occurrences {source : Pattern} {index : Nat}
    {inputs : List Pattern} {views : List AnnotatedInputView}
    (refined : refineInputs? source index inputs = some views) :
    views.map AnnotatedInputView.occurrence =
      assignedOccurrences source index inputs := by
  induction inputs generalizing index views with
  | nil =>
      simp [refineInputs?] at refined
      subst views
      rfl
  | cons input inputs ih =>
      unfold refineInputs? at refined
      generalize firstEq :
          refineOfficialFormulaInput? (occurrence source index) input = firstResult
        at refined
      cases firstResult with
      | none => simp at refined
      | some first =>
          generalize restEq :
              refineInputs? source (index + 1) inputs = restResult at refined
          cases restResult with
          | none => simp at refined
          | some rest =>
              simp at refined
              subst views
              simp only [List.map_cons, assignedOccurrences]
              rw [refine_formula_occurrence firstEq, ih restEq]

def decodeDocumentInputs? (officialFile : Pattern) : Option (List Pattern) :=
  match officialFile with
  | .apply "tptp92-ast:tptp-file:alt-1" [encoded] =>
      decodeOfficialInputs? encoded
  | _ => none

/-! ## Selection after recursive expansion -/

def firstDuplicate? : List String -> Option String
  | [] => none
  | name :: names =>
      if name ∈ names then some name else firstDuplicate? names

/-- One left-to-right pass over an expanded source.  `requested` is fixed for
membership tests; `remaining` records missing requests, and `seen` detects a
second matching formula occurrence. -/
def selectNamed (targetSource : String) (requested : List String) :
    List String -> List String -> List ResolvedFormula ->
      Except ResolutionError (List ResolvedFormula)
  | remaining, _, [] =>
      match remaining with
      | [] => .ok []
      | missing :: _ => .error (.missingSelectionName targetSource missing)
  | remaining, seen, formula :: formulas =>
      if formula.name ∈ requested then
        if formula.name ∈ seen then
          .error (.ambiguousSelectionName targetSource formula.name)
        else
          match selectNamed targetSource requested
              (remaining.erase formula.name) (formula.name :: seen) formulas with
          | .error failure => .error failure
          | .ok selected => .ok (formula :: selected)
      else
        selectNamed targetSource requested remaining seen formulas

def applySelection (targetSource : String) (selection : FormulaSelection)
    (formulas : List ResolvedFormula) :
    Except ResolutionError (List ResolvedFormula) :=
  match selection with
  | .implicitAll => .ok formulas
  | .explicitAll => .ok formulas
  | .named requested =>
      match firstDuplicate? requested with
      | some duplicate =>
          .error (.duplicateSelectionName targetSource duplicate)
      | none => selectNamed targetSource requested requested [] formulas

theorem selectNamed_sublist {targetSource : String} {requested remaining seen : List String}
    {formulas selected : List ResolvedFormula}
    (accepted :
      selectNamed targetSource requested remaining seen formulas = .ok selected) :
    List.Sublist selected formulas := by
  induction formulas generalizing remaining seen selected with
  | nil =>
      cases remaining with
      | nil =>
          simp [selectNamed] at accepted
          subst selected
          exact .slnil
      | cons missing remaining =>
          simp [selectNamed] at accepted
  | cons formula formulas ih =>
      unfold selectNamed at accepted
      split at accepted <;> rename_i requestedMem
      · split at accepted <;> rename_i seenMem
        · simp at accepted
        · generalize recursiveEq :
              selectNamed targetSource requested
                (remaining.erase formula.name) (formula.name :: seen) formulas =
                recursiveResult
            at accepted
          cases recursiveResult with
          | error failure => simp at accepted
          | ok rest =>
              simp at accepted
              subst selected
              exact (ih recursiveEq).cons_cons formula
      · exact (ih accepted).cons formula

theorem selectNamed_selected_names {targetSource : String}
    {requested remaining seen : List String}
    {formulas selected : List ResolvedFormula}
    (accepted :
      selectNamed targetSource requested remaining seen formulas = .ok selected) :
    forall formula, formula ∈ selected -> formula.name ∈ requested := by
  induction formulas generalizing remaining seen selected with
  | nil =>
      cases remaining with
      | nil =>
          simp [selectNamed] at accepted
          subst selected
          simp
      | cons missing remaining =>
          simp [selectNamed] at accepted
  | cons formula formulas ih =>
      unfold selectNamed at accepted
      split at accepted <;> rename_i requestedMem
      · split at accepted <;> rename_i seenMem
        · simp at accepted
        · generalize recursiveEq :
              selectNamed targetSource requested
                (remaining.erase formula.name) (formula.name :: seen) formulas =
                recursiveResult
            at accepted
          cases recursiveResult with
          | error failure => simp at accepted
          | ok rest =>
              simp at accepted
              subst selected
              intro candidate member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact requestedMem
              · exact ih recursiveEq candidate member
      · exact ih accepted

theorem applySelection_sublist {targetSource : String}
    {selection : FormulaSelection} {formulas selected : List ResolvedFormula}
    (accepted : applySelection targetSource selection formulas = .ok selected) :
    List.Sublist selected formulas := by
  cases selection with
  | implicitAll =>
      simp [applySelection] at accepted
      subst selected
      exact .refl _
  | explicitAll =>
      simp [applySelection] at accepted
      subst selected
      exact .refl _
  | named requested =>
      unfold applySelection at accepted
      cases duplicateEq : firstDuplicate? requested with
      | none =>
          simp only [duplicateEq] at accepted
          exact selectNamed_sublist accepted
      | some duplicate =>
          simp [duplicateEq] at accepted

theorem applySelection_named_selected_names {targetSource : String}
    {requested : List String} {formulas selected : List ResolvedFormula}
    (accepted :
      applySelection targetSource (.named requested) formulas = .ok selected) :
    forall formula, formula ∈ selected -> formula.name ∈ requested := by
  unfold applySelection at accepted
  cases duplicateEq : firstDuplicate? requested with
  | none =>
      simp only [duplicateEq] at accepted
      exact selectNamed_selected_names accepted
  | some duplicate =>
      simp [duplicateEq] at accepted

theorem applySelection_implicitAll (targetSource : String)
    (formulas : List ResolvedFormula) :
    applySelection targetSource .implicitAll formulas = .ok formulas := by
  rfl

theorem applySelection_explicitAll (targetSource : String)
    (formulas : List ResolvedFormula) :
    applySelection targetSource .explicitAll formulas = .ok formulas := by
  rfl

/-! ## Depth-first include-DAG resolution -/

/-- Resolve a list of inputs once a child resolver has been fixed.  The child
callback is the only source of recursion through include edges; this function
itself is structurally recursive on the official input list. -/
def resolveInputs (source : SourceDocument) (path : List IncludeEdge)
    (resolveChild : Nat -> IncludeDirectiveView -> Pattern ->
      Except ResolutionError ResolutionChunk) :
    Nat -> List Pattern -> Except ResolutionError ResolutionChunk
  | _, [] => .ok {
      formulas := []
      edges := []
    }
  | inputIndex, input :: inputs =>
      match decodeLocatedInput? input with
      | none => .error (.malformedInput source.canonicalId inputIndex)
      | some located =>
          match located.payload with
          | .annotatedFormula _ =>
              match decodeFormulaName? input with
              | none =>
                  .error (.malformedFormula source.canonicalId inputIndex)
              | some name =>
                  match resolveInputs source path resolveChild
                      (inputIndex + 1) inputs with
                  | .error failure => .error failure
                  | .ok rest => .ok {
                      formulas := {
                        name
                        input
                        origin := {
                          sourceId := source.canonicalId
                          sourceDigest := source.digest
                          sourceInputIndex := inputIndex
                          includePath := path
                        }
                      } :: rest.formulas
                      edges := rest.edges
                    }
          | .includeDirective directive =>
              match decodeIncludeDirective? directive with
              | none =>
                  .error (.malformedInclude source.canonicalId inputIndex)
              | some includeView =>
                  match resolveChild inputIndex includeView
                      (encodeSourceSpan located.span) with
                  | .error failure => .error failure
                  | .ok included =>
                      match resolveInputs source path resolveChild
                          (inputIndex + 1) inputs with
                      | .error failure => .error failure
                      | .ok rest => .ok (included.append rest)

/-- Resolve one canonical source.  Fuel decreases only when following an
include edge.  The public entry point supplies one more unit than the number
of environment documents; active-path cycle detection is checked before fuel
exhaustion. -/
def resolveSource : Nat -> SourceEnvironment -> List String ->
    List IncludeEdge -> String -> Except ResolutionError ResolutionChunk
  | fuel, environment, active, path, sourceId =>
      if sourceId ∈ active then
        .error (.cycle (active ++ [sourceId]))
      else
        match fuel with
        | 0 => .error (.sourceDepthExhausted (active ++ [sourceId]))
        | remainingFuel + 1 =>
            match lookupDocument environment sourceId with
            | .error failure => .error failure
            | .ok source =>
                match decodeDocumentInputs? source.officialFile with
                | none => .error (.malformedDocument sourceId)
                | some inputs =>
                    resolveInputs source path
                      (fun inputIndex includeView span =>
                        match includeView.spaceName with
                        | some spaceName =>
                            .error (.unsupportedSpaceNamespace
                              sourceId includeView.requestedFile spaceName)
                        | none =>
                            match lookupBinding environment sourceId
                                includeView.requestedFile with
                            | .error failure => .error failure
                            | .ok binding =>
                                match lookupDocument environment
                                    binding.targetSource with
                                | .error failure => .error failure
                                | .ok target =>
                                    let edge : IncludeEdge := {
                                      fromSource := sourceId
                                      fromInputIndex := inputIndex
                                      requestedFile := includeView.requestedFile
                                      targetSource := target.canonicalId
                                      targetDigest := target.digest
                                      selection := includeView.selection
                                      spaceName := includeView.spaceName
                                      directive := includeView.raw
                                      span
                                    }
                                    match resolveSource remainingFuel environment
                                        (active ++ [sourceId]) (path ++ [edge])
                                        target.canonicalId with
                                    | .error failure => .error failure
                                    | .ok child =>
                                        match applySelection target.canonicalId
                                            includeView.selection child.formulas with
                                        | .error failure => .error failure
                                        | .ok selected => .ok {
                                            formulas := selected
                                            edges := edge :: child.edges
                                          })
                      0 inputs

def resolve? (environment : SourceEnvironment) (rootSource : String) :
    Except ResolutionError ResolvedDocument :=
  match lookupDocument environment rootSource with
  | .error failure => .error failure
  | .ok root =>
      match resolveSource (environment.documents.length + 1)
          environment [] [] rootSource with
      | .error failure => .error failure
      | .ok resolved => .ok {
          rootSource
          rootDigest := root.digest
          formulas := resolved.formulas
          edges := resolved.edges
        }

/-! ## Composition with semantic derivation refinement -/

/-- A successful result retains both executable equations.  The resolution
digest names the complete source manifest, not merely the root file. -/
structure RefinedResolution (environment : SourceEnvironment)
    (rootSource resolutionDigest : String) where
  resolved : ResolvedDocument
  resolution_exact : resolve? environment rootSource = .ok resolved
  refined : RefinedFile resolutionDigest resolved.officialFile
  refinement_exact :
    refine? resolutionDigest resolved.officialFile = some refined

def resolveAndRefine? (environment : SourceEnvironment)
    (rootSource resolutionDigest : String) :
    Except ResolutionError
      (RefinedResolution environment rootSource resolutionDigest) :=
  match resolutionEq : resolve? environment rootSource with
  | .error failure => .error failure
  | .ok resolved =>
      match refinementEq : refine? resolutionDigest resolved.officialFile with
      | none => .error (.refinementRejected rootSource resolutionDigest)
      | some refined => .ok {
          resolved
          resolution_exact := resolutionEq
          refined
          refinement_exact := refinementEq
        }

/-- The executable constructor returns any artifact carrying its two exact
stage equations.  This lets downstream compilers reuse the retained
refinement instead of normalizing the resolved file a second time. -/
theorem resolveAndRefine?_eq_ok_of_artifact
    {environment : SourceEnvironment} {rootSource resolutionDigest : String}
    (artifact : RefinedResolution environment rootSource resolutionDigest) :
    resolveAndRefine? environment rootSource resolutionDigest = .ok artifact := by
  unfold resolveAndRefine?
  split
  case h_1 failure branchEq =>
    have impossible := branchEq.symm.trans artifact.resolution_exact
    cases impossible
  case h_2 resolved branchEq =>
    have resolvedEq : resolved = artifact.resolved :=
      Except.ok.inj (branchEq.symm.trans artifact.resolution_exact)
    subst resolved
    split
    case h_1 branchEq =>
      have impossible := branchEq.symm.trans artifact.refinement_exact
      cases impossible
    case h_2 refined branchEq =>
      have refinedEq : refined = artifact.refined :=
        Option.some.inj (branchEq.symm.trans artifact.refinement_exact)
      subst refined
      congr

theorem RefinedResolution.refined_inputs_exact
    {environment : SourceEnvironment} {rootSource resolutionDigest : String}
    (artifact : RefinedResolution environment rootSource resolutionDigest) :
    artifact.refined.inputs = artifact.resolved.officialInputs := by
  have fileEq := artifact.refined.inputList_exact
  change
    Pattern.apply "tptp92-ast:tptp-file:alt-1"
        [encodeOfficialInputs artifact.resolved.officialInputs] =
      Pattern.apply "tptp92-ast:tptp-file:alt-1"
        [encodeOfficialInputs artifact.refined.inputs]
    at fileEq
  injection fileEq with _ argumentsEq
  injection argumentsEq with encodedEq
  exact (encodeOfficialInputs_injective encodedEq).symm

theorem RefinedResolution.views_erase_to_resolved_inputs
    {environment : SourceEnvironment} {rootSource resolutionDigest : String}
    (artifact : RefinedResolution environment rootSource resolutionDigest) :
    artifact.refined.views.map eraseToOfficialInput =
      artifact.resolved.officialInputs := by
  rw [refineInputs?_erases artifact.refined.views_exact]
  exact artifact.refined_inputs_exact

theorem RefinedResolution.occurrences_enumerate_resolved_inputs
    {environment : SourceEnvironment} {rootSource resolutionDigest : String}
    (artifact : RefinedResolution environment rootSource resolutionDigest) :
    artifact.refined.views.map AnnotatedInputView.occurrence =
      assignedOccurrences (sourceDigest resolutionDigest) 0
        artifact.resolved.officialInputs := by
  rw [refineInputs?_occurrences artifact.refined.views_exact]
  rw [artifact.refined_inputs_exact]

theorem RefinedResolution.views_match_provenance_length
    {environment : SourceEnvironment} {rootSource resolutionDigest : String}
    (artifact : RefinedResolution environment rootSource resolutionDigest) :
    artifact.refined.views.length = artifact.resolved.provenance.length := by
  have lengthEq := refineInputs?_length artifact.refined.views_exact
  rw [artifact.refined_inputs_exact] at lengthEq
  simpa [ResolvedDocument.officialInputs, ResolvedDocument.provenance]
    using lengthEq

theorem resolved_provenance_length (resolved : ResolvedDocument) :
    resolved.provenance.length = resolved.officialInputs.length := by
  simp [ResolvedDocument.provenance, ResolvedDocument.officialInputs]

/-! ## Positive and adversarial controls -/

namespace Canary

def token (label value : String) : Pattern := a label [a value]

def atomicWord (value : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-1"
    [token "tptp92-ast:token:lower-word" value]

def quotedWord (value : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-2"
    [token "tptp92-ast:token:single-quoted" value]

def name (value : String) : Pattern :=
  a "tptp92-ast:name:alt-1" [atomicWord value]

def namedFof (value : String) : Pattern :=
  match TptpOfficialAbstractSyntax.fofAnnotatedExample with
  | .apply label [_oldName, role, formula, annotations] =>
      .apply label [name value, role, formula, annotations]
  | fallback => fallback

def span (index : Nat) : Pattern :=
  a "tptp92-ast:source-span" [a (toString index), a (toString (index + 1))]

def formulaInput (value : String) (index : Nat) : Pattern :=
  a "tptp92-ast:tptp-input:alt-1" [
    a "tptp92-ast:annotated-formula:alt-4" [namedFof value], span index]

def encodeNameList : List String -> Pattern
  | [] => a "invalid-empty-name-list"
  | [value] => a "tptp92-ast:name-list:alt-1" [name value]
  | value :: values =>
      a "tptp92-ast:name-list:alt-2" [name value, encodeNameList values]

def namedSelection (names : List String) : Pattern :=
  a "tptp92-ast:formula-selection:alt-1" [encodeNameList names]

def explicitAllSelection : Pattern :=
  a "tptp92-ast:formula-selection:alt-2"

def includeInput (requested : String) (selection : Option Pattern)
    (spaceName : Option String) (index : Nat) : Pattern :=
  let optionals :=
    match selection, spaceName with
    | none, none => a "tptp92-ast:include-optionals:alt-1"
    | some selected, none =>
        a "tptp92-ast:include-optionals:alt-2" [selected]
    | some selected, some namespaceName =>
        a "tptp92-ast:include-optionals:alt-3" [selected,
          a "tptp92-ast:space-name:alt-1" [name namespaceName]]
    | none, some _ => a "invalid-space-without-selection"
  a "tptp92-ast:tptp-input:alt-2" [
    a "tptp92-ast:include:alt-1" [
      a "tptp92-ast:file-name:alt-1" [quotedWord requested], optionals],
    span index]

def file (inputs : List Pattern) : Pattern :=
  a "tptp92-ast:tptp-file:alt-1" [encodeOfficialInputs inputs]

def rootDocument : SourceDocument := {
  canonicalId := "root"
  digest := "root-digest"
  officialFile := file [includeInput "mid.p" none none 0, formulaInput "r" 1]
}

def midDocument : SourceDocument := {
  canonicalId := "mid"
  digest := "mid-digest"
  officialFile := file [
    includeInput "leaf.p" (some (namedSelection ["b"])) none 0,
    formulaInput "c" 1]
}

def leafDocument : SourceDocument := {
  canonicalId := "leaf"
  digest := "leaf-digest"
  officialFile := file [formulaInput "a" 0, formulaInput "b" 1]
}

def nestedEnvironment : SourceEnvironment := {
  documents := [rootDocument, midDocument, leafDocument]
  bindings := [
    {
      fromSource := "root"
      requestedFile := "mid.p"
      targetSource := "mid"
    },
    {
      fromSource := "mid"
      requestedFile := "leaf.p"
      targetSource := "leaf"
    }]
}

theorem nested_selection_is_transitive_and_source_ordered :
    match resolve? nestedEnvironment "root" with
    | .error _ => False
    | .ok resolved => resolved.formulas.map ResolvedFormula.name = ["b", "c", "r"] := by
  rfl

theorem nested_provenance_is_exact :
    match resolve? nestedEnvironment "root" with
    | .error _ => False
    | .ok resolved =>
        resolved.formulas.map (fun formula =>
          (formula.origin.sourceId, formula.origin.sourceInputIndex,
            formula.origin.includePath.length)) =
          [("leaf", 1, 2), ("mid", 1, 1), ("root", 1, 0)] := by
  rfl

def sharedSpellingRoot : SourceDocument := {
  canonicalId := "shared-spelling-root"
  digest := "shared-spelling-root-digest"
  officialFile := file [
    includeInput "left.p" none none 0,
    includeInput "right.p" none none 1]
}

def sharedSpellingLeft : SourceDocument := {
  canonicalId := "shared-spelling-left"
  digest := "shared-spelling-left-digest"
  officialFile := file [includeInput "common.p" none none 0]
}

def sharedSpellingRight : SourceDocument := {
  canonicalId := "shared-spelling-right"
  digest := "shared-spelling-right-digest"
  officialFile := file [includeInput "common.p" none none 0]
}

def sharedSpellingLeafA : SourceDocument := {
  canonicalId := "shared-spelling-leaf-a"
  digest := "shared-spelling-leaf-a-digest"
  officialFile := file [formulaInput "a" 0]
}

def sharedSpellingLeafB : SourceDocument := {
  canonicalId := "shared-spelling-leaf-b"
  digest := "shared-spelling-leaf-b-digest"
  officialFile := file [formulaInput "b" 0]
}

def sharedSpellingEnvironment : SourceEnvironment := {
  documents := [sharedSpellingRoot, sharedSpellingLeft, sharedSpellingRight,
    sharedSpellingLeafA, sharedSpellingLeafB]
  bindings := [
    {
      fromSource := "shared-spelling-root"
      requestedFile := "left.p"
      targetSource := "shared-spelling-left"
    },
    {
      fromSource := "shared-spelling-root"
      requestedFile := "right.p"
      targetSource := "shared-spelling-right"
    },
    {
      fromSource := "shared-spelling-left"
      requestedFile := "common.p"
      targetSource := "shared-spelling-leaf-a"
    },
    {
      fromSource := "shared-spelling-right"
      requestedFile := "common.p"
      targetSource := "shared-spelling-leaf-b"
    }]
}

theorem include_spelling_is_resolved_relative_to_each_parent :
    (resolve? sharedSpellingEnvironment "shared-spelling-root").toOption.map
        (fun resolved =>
          (resolved.formulas.map ResolvedFormula.name,
            resolved.formulas.map
              (fun formula => formula.origin.includePath.length))) =
      some (["a", "b"], [2, 2]) := by
  decide +kernel

def sourceOrderRoot : SourceDocument := {
  canonicalId := "source-order-root"
  digest := "source-order-root-digest"
  officialFile := file [
    includeInput "leaf.p" (some (namedSelection ["b", "a"])) none 0]
}

def sourceOrderEnvironment : SourceEnvironment := {
  documents := [sourceOrderRoot, leafDocument]
  bindings := [{
    fromSource := "source-order-root"
    requestedFile := "leaf.p"
    targetSource := "leaf"
  }]
}

theorem selection_preserves_source_order_not_request_order :
    match resolve? sourceOrderEnvironment "source-order-root" with
    | .error _ => False
    | .ok resolved => resolved.formulas.map ResolvedFormula.name = ["a", "b"] := by
  rfl

def explicitAllRoot : SourceDocument := {
  canonicalId := "explicit-all-root"
  digest := "explicit-all-root-digest"
  officialFile := file [
    includeInput "leaf.p" (some explicitAllSelection) none 0]
}

def explicitAllEnvironment : SourceEnvironment := {
  documents := [explicitAllRoot, leafDocument]
  bindings := [{
    fromSource := "explicit-all-root"
    requestedFile := "leaf.p"
    targetSource := "leaf"
  }]
}

theorem explicit_star_selects_all :
    match resolve? explicitAllEnvironment "explicit-all-root" with
    | .error _ => False
    | .ok resolved => resolved.formulas.map ResolvedFormula.name = ["a", "b"] := by
  rfl

def missingSelectionRoot : SourceDocument := {
  canonicalId := "missing-selection-root"
  digest := "missing-selection-root-digest"
  officialFile := file [
    includeInput "leaf.p" (some (namedSelection ["z"])) none 0]
}

def missingSelectionEnvironment : SourceEnvironment := {
  documents := [missingSelectionRoot, leafDocument]
  bindings := [{
    fromSource := "missing-selection-root"
    requestedFile := "leaf.p"
    targetSource := "leaf"
  }]
}

theorem missing_selection_fails_closed :
    resolve? missingSelectionEnvironment "missing-selection-root" =
      .error (.missingSelectionName "leaf" "z") := by
  rfl

def duplicateFormulaDocument : SourceDocument := {
  canonicalId := "duplicates"
  digest := "duplicates-digest"
  officialFile := file [formulaInput "a" 0, formulaInput "a" 1]
}

def ambiguousSelectionRoot : SourceDocument := {
  canonicalId := "ambiguous-selection-root"
  digest := "ambiguous-selection-root-digest"
  officialFile := file [
    includeInput "duplicates.p" (some (namedSelection ["a"])) none 0]
}

def ambiguousSelectionEnvironment : SourceEnvironment := {
  documents := [ambiguousSelectionRoot, duplicateFormulaDocument]
  bindings := [{
    fromSource := "ambiguous-selection-root"
    requestedFile := "duplicates.p"
    targetSource := "duplicates"
  }]
}

theorem ambiguous_selected_name_fails_closed :
    resolve? ambiguousSelectionEnvironment "ambiguous-selection-root" =
      .error (.ambiguousSelectionName "duplicates" "a") := by
  rfl

def duplicateRequestRoot : SourceDocument := {
  canonicalId := "duplicate-request-root"
  digest := "duplicate-request-root-digest"
  officialFile := file [
    includeInput "leaf.p" (some (namedSelection ["a", "a"])) none 0]
}

def duplicateRequestEnvironment : SourceEnvironment := {
  documents := [duplicateRequestRoot, leafDocument]
  bindings := [{
    fromSource := "duplicate-request-root"
    requestedFile := "leaf.p"
    targetSource := "leaf"
  }]
}

theorem duplicate_selection_request_fails_closed :
    resolve? duplicateRequestEnvironment "duplicate-request-root" =
      .error (.duplicateSelectionName "leaf" "a") := by
  rfl

def cycleRoot : SourceDocument := {
  canonicalId := "cycle-root"
  digest := "cycle-root-digest"
  officialFile := file [includeInput "child.p" none none 0]
}

def cycleChild : SourceDocument := {
  canonicalId := "cycle-child"
  digest := "cycle-child-digest"
  officialFile := file [includeInput "root.p" none none 0]
}

def cycleEnvironment : SourceEnvironment := {
  documents := [cycleRoot, cycleChild]
  bindings := [
    {
      fromSource := "cycle-root"
      requestedFile := "child.p"
      targetSource := "cycle-child"
    },
    {
      fromSource := "cycle-child"
      requestedFile := "root.p"
      targetSource := "cycle-root"
    }]
}

theorem active_path_cycle_fails_closed :
    resolve? cycleEnvironment "cycle-root" =
      .error (.cycle ["cycle-root", "cycle-child", "cycle-root"]) := by
  rfl

def missingBindingEnvironment : SourceEnvironment := {
  documents := [rootDocument, midDocument, leafDocument]
  bindings := []
}

theorem missing_relative_binding_fails_closed :
    resolve? missingBindingEnvironment "root" =
      .error (.missingBinding "root" "mid.p") := by
  rfl

def ambiguousDocumentEnvironment : SourceEnvironment := {
  documents := [rootDocument, { rootDocument with digest := "other-root-digest" }]
  bindings := []
}

theorem ambiguous_root_document_fails_closed :
    resolve? ambiguousDocumentEnvironment "root" =
      .error (.ambiguousDocument "root") := by
  rfl

def ambiguousBindingEnvironment : SourceEnvironment := {
  documents := [rootDocument, midDocument, leafDocument]
  bindings := [
    {
      fromSource := "root"
      requestedFile := "mid.p"
      targetSource := "mid"
    },
    {
      fromSource := "root"
      requestedFile := "mid.p"
      targetSource := "leaf"
    }]
}

theorem ambiguous_relative_binding_fails_closed :
    resolve? ambiguousBindingEnvironment "root" =
      .error (.ambiguousBinding "root" "mid.p") := by
  rfl

def malformedDocument : SourceDocument := {
  canonicalId := "malformed-document"
  digest := "malformed-document-digest"
  officialFile := a "not-a-tptp-file"
}

def malformedDocumentEnvironment : SourceEnvironment := {
  documents := [malformedDocument]
  bindings := []
}

theorem malformed_document_fails_closed :
    resolve? malformedDocumentEnvironment "malformed-document" =
      .error (.malformedDocument "malformed-document") := by
  rfl

def malformedInputDocument : SourceDocument := {
  canonicalId := "malformed-input"
  digest := "malformed-input-digest"
  officialFile := file [a "not-a-located-input"]
}

def malformedInputEnvironment : SourceEnvironment := {
  documents := [malformedInputDocument]
  bindings := []
}

theorem malformed_input_fails_closed :
    resolve? malformedInputEnvironment "malformed-input" =
      .error (.malformedInput "malformed-input" 0) := by
  rfl

def malformedFormulaDocument : SourceDocument := {
  canonicalId := "malformed-formula"
  digest := "malformed-formula-digest"
  officialFile := file [
    a "tptp92-ast:tptp-input:alt-1" [a "not-an-annotated-formula", span 0]]
}

def malformedFormulaEnvironment : SourceEnvironment := {
  documents := [malformedFormulaDocument]
  bindings := []
}

theorem malformed_formula_fails_closed :
    resolve? malformedFormulaEnvironment "malformed-formula" =
      .error (.malformedFormula "malformed-formula" 0) := by
  rfl

def malformedIncludeDocument : SourceDocument := {
  canonicalId := "malformed-include"
  digest := "malformed-include-digest"
  officialFile := file [
    a "tptp92-ast:tptp-input:alt-2" [a "not-an-include", span 0]]
}

def malformedIncludeEnvironment : SourceEnvironment := {
  documents := [malformedIncludeDocument]
  bindings := []
}

theorem malformed_include_fails_closed :
    resolve? malformedIncludeEnvironment "malformed-include" =
      .error (.malformedInclude "malformed-include" 0) := by
  rfl

def namespaceRoot : SourceDocument := {
  canonicalId := "namespace-root"
  digest := "namespace-root-digest"
  officialFile := file [
    includeInput "leaf.p" (some explicitAllSelection) (some "top") 0]
}

def namespaceEnvironment : SourceEnvironment := {
  documents := [namespaceRoot, leafDocument]
  bindings := [{
    fromSource := "namespace-root"
    requestedFile := "leaf.p"
    targetSource := "leaf"
  }]
}

theorem active_namespace_is_not_silently_ignored :
    resolve? namespaceEnvironment "namespace-root" =
      .error (.unsupportedSpaceNamespace "namespace-root" "leaf.p" "top") := by
  rfl

theorem nested_resolution_refines :
    match resolveAndRefine? nestedEnvironment "root" "resolved-manifest" with
    | .error _ => False
    | .ok artifact =>
        artifact.refined.views.length = artifact.resolved.formulas.length := by
  rfl

end Canary

#print axioms applySelection_implicitAll
#print axioms applySelection_explicitAll
#print axioms selectNamed_sublist
#print axioms selectNamed_selected_names
#print axioms applySelection_sublist
#print axioms applySelection_named_selected_names
#print axioms refine_formula_occurrence
#print axioms resolveAndRefine?_eq_ok_of_artifact
#print axioms refineInputs?_occurrences
#print axioms RefinedResolution.refined_inputs_exact
#print axioms RefinedResolution.views_erase_to_resolved_inputs
#print axioms RefinedResolution.occurrences_enumerate_resolved_inputs
#print axioms RefinedResolution.views_match_provenance_length
#print axioms resolved_provenance_length
#print axioms Canary.nested_selection_is_transitive_and_source_ordered
#print axioms Canary.nested_provenance_is_exact
#print axioms Canary.include_spelling_is_resolved_relative_to_each_parent
#print axioms Canary.selection_preserves_source_order_not_request_order
#print axioms Canary.explicit_star_selects_all
#print axioms Canary.missing_selection_fails_closed
#print axioms Canary.ambiguous_selected_name_fails_closed
#print axioms Canary.duplicate_selection_request_fails_closed
#print axioms Canary.active_path_cycle_fails_closed
#print axioms Canary.missing_relative_binding_fails_closed
#print axioms Canary.ambiguous_root_document_fails_closed
#print axioms Canary.ambiguous_relative_binding_fails_closed
#print axioms Canary.malformed_document_fails_closed
#print axioms Canary.malformed_input_fails_closed
#print axioms Canary.malformed_formula_fails_closed
#print axioms Canary.malformed_include_fails_closed
#print axioms Canary.active_namespace_is_not_silently_ignored
#print axioms Canary.nested_resolution_refines

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
