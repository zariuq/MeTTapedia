import Mettapedia.GSLT.Parsing.PlainBnfDeclarationSemantics
import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Declaration data encoded for the current source-certificate bridge

This module instantiates the independent declaration model with the current
source certificate's ground terms. It owns all source-specific constructor
spellings and injective encodings; the generic declaration algorithms do not
import this representation.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationEncoding

open HornCertificate PlainBnfDeclarationSemantics

def encodeDefinition (definition : Definition GroundTerm GroundTerm GroundTerm) : GroundTerm :=
  .app "BNFDefinitionV1" (GroundTerms.ofList
    [definition.name, definition.expression, definition.span])

def encodeDefinitions : List (Definition GroundTerm GroundTerm GroundTerm) → GroundTerm
  | [] => .atom "BNFDefinitionsNilV1"
  | head :: tail => .app "BNFDefinitionsConsV1"
      (GroundTerms.ofList [encodeDefinition head, encodeDefinitions tail])

def encodeEntry : Entry GroundTerm GroundTerm GroundTerm GroundTerm → GroundTerm
  | .rule name expression span =>
      .app "bnf-v1:rule" (GroundTerms.ofList [name, expression, span])
  | .comment text span => .app "bnf-v1:comment" (GroundTerms.ofList [text, span])
  | .blank span => .app "bnf-v1:blank" (GroundTerms.ofList [span])

def encodeEntries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm) → GroundTerm
  | [] => .app "metta-nullary" (.cons (.atom "bnf-v1:entries-nil") .nil)
  | head :: tail => .app "bnf-v1:entries-cons"
      (GroundTerms.ofList [encodeEntry head, encodeEntries tail])

def encodeDiagnostic : Diagnostic GroundTerm GroundTerm → GroundTerm
  | .duplicate name firstSpan duplicateSpan =>
      .app "BNFDuplicateDefinitionV1" (GroundTerms.ofList [name, firstSpan, duplicateSpan])

def encodeDiagnostics : List (Diagnostic GroundTerm GroundTerm) → GroundTerm
  | [] => .atom "BNFDiagnosticsNilV1"
  | head :: tail => .app "BNFDiagnosticsConsV1"
      (GroundTerms.ofList [encodeDiagnostic head, encodeDiagnostics tail])

def encodeLookupResult : LookupResult GroundTerm GroundTerm → GroundTerm
  | .missing => .atom "BNFDefinitionMissingV1"
  | .found expression span =>
      .app "BNFDefinitionFoundV1" (GroundTerms.ofList [expression, span])

theorem encodeDefinition_injective : Function.Injective encodeDefinition := by
  intro left right equal
  cases left
  cases right
  simpa [encodeDefinition, GroundTerms.ofList] using equal

theorem encodeDefinitions_injective : Function.Injective encodeDefinitions := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons => cases equal
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => cases equal
      | cons head' tail' =>
          have fields : encodeDefinition head = encodeDefinition head' ∧
              encodeDefinitions tail = encodeDefinitions tail' := by
            simpa [encodeDefinitions, GroundTerms.ofList] using equal
          exact congrArg₂ List.cons (encodeDefinition_injective fields.1) (ih fields.2)

theorem encodeEntry_injective : Function.Injective encodeEntry := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [encodeEntry, GroundTerms.ofList]

theorem encodeEntries_injective : Function.Injective encodeEntries := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons => simp [encodeEntries] at equal
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => simp [encodeEntries] at equal
      | cons head' tail' =>
          have fields : encodeEntry head = encodeEntry head' ∧
              encodeEntries tail = encodeEntries tail' := by
            simpa [encodeEntries, GroundTerms.ofList] using equal
          exact congrArg₂ List.cons (encodeEntry_injective fields.1) (ih fields.2)

theorem encodeDiagnostic_injective : Function.Injective encodeDiagnostic := by
  intro left right equal
  cases left
  cases right
  simpa [encodeDiagnostic, GroundTerms.ofList] using equal

theorem encodeDiagnostics_injective : Function.Injective encodeDiagnostics := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons => cases equal
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => cases equal
      | cons head' tail' =>
          have fields : encodeDiagnostic head = encodeDiagnostic head' ∧
              encodeDiagnostics tail = encodeDiagnostics tail' := by
            simpa [encodeDiagnostics, GroundTerms.ofList] using equal
          exact congrArg₂ List.cons (encodeDiagnostic_injective fields.1) (ih fields.2)

theorem encodeLookupResult_injective : Function.Injective encodeLookupResult := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [encodeLookupResult, GroundTerms.ofList]

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationEncoding
