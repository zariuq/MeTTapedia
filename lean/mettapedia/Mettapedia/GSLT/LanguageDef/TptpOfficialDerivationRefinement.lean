import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission

/-!
# Source-preserving refinement of an official TPTP file to a derivation

The official parser produces one `Tptp92Ast:tptp-file`.  The derivation
checker consumes the semantic `TptpSemantic:derivation` carrier.  This module
defines the structural bridge between them.

Formula inputs are copied without changing their family payload or source
span.  The bridge adds only a caller-supplied source digest and dense,
source-relative occurrence identities in file order.  Unresolved include
directives fail explicitly; include-DAG resolution must happen before a file
can be treated as one derivation.

No inference rule is interpreted here.  Structural admission and calculus
checking remain later, independent stages.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-- Canonical semantic identity of one already-resolved source document. -/
def sourceDigest (digest : String) : Pattern :=
  a "tptp-semantic:source-digest" [a digest]

/-- Canonical identity of the input at `index` in one source document. -/
def occurrence (source : Pattern) (index : Nat) : Pattern :=
  a "tptp-semantic:occurrence-id" [source, a (toString index)]

/-- Reconstruct the unique official list spine for a list of inputs. -/
def encodeOfficialInputs : List Pattern → Pattern
  | [] => a "tptp92-ast:list:tptp92ast-tptp-input:nil"
  | first :: rest =>
      a "tptp92-ast:list:tptp92ast-tptp-input:cons"
        [first, encodeOfficialInputs rest]

structure DecodedInputs (encoded : Pattern) where
  inputs : List Pattern
  encoded_exact : encodeOfficialInputs inputs = encoded

/-- Decode the official list spine without inspecting formula payloads.  The
dependent result retains the inverse equation instead of asking a later phase
to rediscover it. -/
def decodeOfficialInputs : (encoded : Pattern) → Option (DecodedInputs encoded)
  | .apply "tptp92-ast:list:tptp92ast-tptp-input:nil" [] =>
      some { inputs := [], encoded_exact := rfl }
  | .apply "tptp92-ast:list:tptp92ast-tptp-input:cons" [first, rest] =>
      match decodeOfficialInputs rest with
      | none => none
      | some decoded => some {
          inputs := first :: decoded.inputs
          encoded_exact := by
            simp only [encodeOfficialInputs, a]
            rw [decoded.encoded_exact]
        }
  | _ => none

def decodeOfficialInputs? (encoded : Pattern) : Option (List Pattern) :=
  (decodeOfficialInputs encoded).map DecodedInputs.inputs

theorem decode_encode_official_inputs (inputs : List Pattern) :
    decodeOfficialInputs? (encodeOfficialInputs inputs) = some inputs := by
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
      unfold decodeOfficialInputs? at ih ⊢
      simp only [encodeOfficialInputs, a, decodeOfficialInputs]
      generalize restEq :
          decodeOfficialInputs (encodeOfficialInputs rest) = restResult at ih ⊢
      cases restResult with
      | none => simp at ih
      | some decoded =>
          simp at ih ⊢
          rw [ih]

theorem encodeOfficialInputs_injective :
    Function.Injective encodeOfficialInputs := by
  intro left right equality
  have decoded := congrArg decodeOfficialInputs? equality
  simpa only [decode_encode_official_inputs, Option.some.injEq] using decoded

/-- Refinement of a successful formula input is lossless after occurrence
identity is forgotten. -/
theorem refine_formula_erases {assigned input : Pattern}
    {view : AnnotatedInputView}
    (refined : refineOfficialFormulaInput? assigned input = some view) :
    eraseToOfficialInput view = input := by
  cases input with
  | bvar index => simp [refineOfficialFormulaInput?] at refined
  | fvar name => simp [refineOfficialFormulaInput?] at refined
  | apply label arguments =>
      simp only [refineOfficialFormulaInput?] at refined
      split at refined <;> try contradiction
      all_goals
        rename_i _ formula span shape
        cases refined
        injection shape with labelEq argumentsEq
        subst label
        subst arguments
        rfl
  | lambda name body => simp [refineOfficialFormulaInput?] at refined
  | multiLambda count names body =>
      simp [refineOfficialFormulaInput?] at refined
  | subst body replacement => simp [refineOfficialFormulaInput?] at refined
  | collection kind elements rest =>
      simp [refineOfficialFormulaInput?] at refined

/-- Assign canonical occurrences in one left-to-right pass. -/
def refineInputs? (source : Pattern) :
    Nat → List Pattern → Option (List AnnotatedInputView)
  | _, [] => some []
  | index, input :: inputs => do
      let first ← refineOfficialFormulaInput? (occurrence source index) input
      let rest ← refineInputs? source (index + 1) inputs
      some (first :: rest)

theorem refineInputs?_length {source : Pattern} {index : Nat}
    {inputs : List Pattern} {views : List AnnotatedInputView}
    (refined : refineInputs? source index inputs = some views) :
    views.length = inputs.length := by
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
              simp [ih restEq]

theorem refineInputs?_erases {source : Pattern} {index : Nat}
    {inputs : List Pattern} {views : List AnnotatedInputView}
    (refined : refineInputs? source index inputs = some views) :
    views.map eraseToOfficialInput = inputs := by
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
              simp [refine_formula_erases firstEq, ih restEq]

/-- Encode semantic derivation nodes in their original file order. -/
def encodeDerivationNodes : List AnnotatedInputView → Pattern
  | [] => a "tptp-semantic:derivation-nodes-nil"
  | first :: rest =>
      a "tptp-semantic:derivation-nodes-cons"
        [encodeAnnotatedInput first, encodeDerivationNodes rest]

/-- The official syntax tree reconstructed by forgetting semantic occurrence
identities. -/
def eraseRefinedFile (views : List AnnotatedInputView) : Pattern :=
  a "tptp92-ast:tptp-file:alt-1"
    [encodeOfficialInputs (views.map eraseToOfficialInput)]

structure RefinedFile (digest : String) (officialFile : Pattern) where
  inputs : List Pattern
  inputList_exact :
    officialFile =
      a "tptp92-ast:tptp-file:alt-1" [encodeOfficialInputs inputs]
  views : List AnnotatedInputView
  views_exact : refineInputs? (sourceDigest digest) 0 inputs = some views

def RefinedFile.semantic {digest : String} {officialFile : Pattern}
    (refined : RefinedFile digest officialFile) : Pattern :=
  a "tptp-semantic:derivation"
    [sourceDigest digest, encodeDerivationNodes refined.views]

theorem RefinedFile.source_exact {digest : String} {officialFile : Pattern}
    (_refined : RefinedFile digest officialFile) :
    decodeSourceDigest? (sourceDigest digest) = some digest := by
  rfl

theorem RefinedFile.erases_exact {digest : String} {officialFile : Pattern}
    (refined : RefinedFile digest officialFile) :
    eraseRefinedFile refined.views = officialFile := by
  calc
    eraseRefinedFile refined.views =
        a "tptp92-ast:tptp-file:alt-1"
          [encodeOfficialInputs refined.inputs] := by
      unfold eraseRefinedFile
      rw [refineInputs?_erases refined.views_exact]
    _ = officialFile := refined.inputList_exact.symm

def refine? (digest : String) (officialFile : Pattern) :
    Option (RefinedFile digest officialFile) :=
  match officialFile with
  | .apply "tptp92-ast:tptp-file:alt-1" [inputList] =>
      match decodedEq : decodeOfficialInputs inputList with
      | none => none
      | some decoded =>
          match viewsEq :
              refineInputs? (sourceDigest digest) 0 decoded.inputs with
          | none => none
          | some views => some {
              inputs := decoded.inputs
              inputList_exact := by
                exact congrArg
                  (fun list => a "tptp92-ast:tptp-file:alt-1" [list])
                  decoded.encoded_exact.symm
              views
              views_exact := viewsEq
            }
  | _ => none

/-- Refine an include-free official file into the semantic derivation carrier.
The digest is data supplied by the source-loading boundary, not computed or
trusted by this structural transformation. -/
def refineOfficialDerivation? (digest : String) (officialFile : Pattern) :
    Option Pattern :=
  (refine? digest officialFile).map RefinedFile.semantic

theorem refine?_semantic_exact {digest : String} {officialFile : Pattern}
    {refined : RefinedFile digest officialFile}
    (found : refine? digest officialFile = some refined) :
    refineOfficialDerivation? digest officialFile = some refined.semantic := by
  simp [refineOfficialDerivation?, found]

/-! ## Six-family and rejection controls -/

namespace Canary

def span : Pattern :=
  a "tptp92-ast:source-span" [a "0", a "1"]

def officialInput (payload : FormulaPayload) : Pattern :=
  eraseToOfficialInput {
    occurrence := a "ignored"
    payload
    span
  }

def allFamilyInputs : List Pattern := [
  officialInput (.thf TptpOfficialAbstractSyntax.thfAnnotatedExample),
  officialInput (.tff TptpOfficialAbstractSyntax.tffAnnotatedExample),
  officialInput (.tcf TptpOfficialAbstractSyntax.tcfAnnotatedExample),
  officialInput (.fof TptpOfficialAbstractSyntax.fofAnnotatedExample),
  officialInput (.cnf TptpOfficialAbstractSyntax.cnfAnnotatedExample),
  officialInput (.tpi TptpOfficialAbstractSyntax.tpiAnnotatedExample)
]

def allFamilyFile : Pattern :=
  a "tptp92-ast:tptp-file:alt-1" [encodeOfficialInputs allFamilyInputs]

def includeInput : Pattern :=
  a "tptp92-ast:tptp-input:alt-2"
    [a "tptp92-ast:include:alt-1" [
      a "tptp92-ast:file-name:alt-1" [a "example.p"],
      a "tptp92-ast:include-optionals:alt-1"], span]

def unresolvedIncludeFile : Pattern :=
  a "tptp92-ast:tptp-file:alt-1"
    [encodeOfficialInputs [includeInput]]

theorem all_families_refine :
    (refine? "all-families" allFamilyFile).isSome = true := by
  rfl

theorem all_families_preserve_length :
    match refine? "all-families" allFamilyFile with
    | none => False
    | some refined => refined.views.length = 6 := by
  rfl

theorem unresolved_include_fails_closed :
    refine? "include-unresolved" unresolvedIncludeFile = none := by
  rfl

theorem malformed_list_fails_closed :
    refine? "malformed"
      (a "tptp92-ast:tptp-file:alt-1" [a "not-a-list"]) = none := by
  rfl

end Canary

#print axioms decode_encode_official_inputs
#print axioms encodeOfficialInputs_injective
#print axioms refine_formula_erases
#print axioms refineInputs?_length
#print axioms refineInputs?_erases
#print axioms RefinedFile.source_exact
#print axioms RefinedFile.erases_exact
#print axioms refine?_semantic_exact
#print axioms Canary.all_families_refine
#print axioms Canary.all_families_preserve_length
#print axioms Canary.unresolved_include_fails_closed
#print axioms Canary.malformed_list_fails_closed

end Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement
