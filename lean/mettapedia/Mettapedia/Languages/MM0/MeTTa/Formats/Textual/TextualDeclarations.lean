import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualProjection

/-!
# Structural MM0 declaration projection

The raw frontend keeps names, expression trees and source trace metadata in
the existing Atom carrier. Projection resolves names into the existing
kernel declarations and preterms. Sort annotations are frontend metadata;
the retained kernel performs typing and declaration admission separately.

These laws describe data projection. Execution correspondence for the
authored MeTTa adapter is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TextualDeclarations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Kernel (Binder Context TermDecl Preterm TheoremDecl SpecificationEntry)
open TextualData (SortEntry)
open TextualProjection (SourceBinder SourceType)

deriving instance DecidableEq for SpecificationEntry

structure SourceTermSignature where
  binders : List SourceBinder
  result : SourceType
  deriving DecidableEq, Repr

def termSignatureValue (signature : SourceTermSignature) : Atom :=
  .expression [.symbol "MM0TermSignatureV1", TextualProjection.bindersValue signature.binders,
    TextualProjection.typeValue signature.result]

def decodeTermSignature : Atom → Option SourceTermSignature
  | .expression [.symbol "MM0TermSignatureV1", binders, result] => do
      let arguments ← TextualProjection.decodeBinders binders
      let returnType ← TextualProjection.decodeType result
      pure ⟨arguments, returnType⟩
  | _ => none

@[simp] theorem decodeTermSignature_termSignatureValue (signature : SourceTermSignature) :
    decodeTermSignature (termSignatureValue signature) = some signature := by
  cases signature
  simp [termSignatureValue, decodeTermSignature]

theorem decodeTermSignature_reflects (atom : Atom) (signature : SourceTermSignature)
    (decoded : decodeTermSignature atom = some signature) : atom = termSignatureValue signature := by
  unfold decodeTermSignature at decoded
  split at decoded
  · rename_i binders result
    obtain ⟨arguments, argumentsDecoded, afterArguments⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨returnType, resultDecoded, output⟩ := Option.bind_eq_some_iff.mp afterArguments
    have same : (⟨arguments, returnType⟩ : SourceTermSignature) = signature := by simpa using output
    subst signature
    rw [TextualProjection.decodeBinders_reflects binders arguments argumentsDecoded,
      TextualProjection.decodeType_reflects result returnType resultDecoded]
    rfl
  · simp at decoded

/-- A hypothesis name is trace metadata; its tree uses the existing source Atom. -/
abbrev SourceHypothesis := Option String × Atom

def hypothesisNameValue : Option String → Atom
  | none => .symbol "MM0AnonymousHypothesisNameV1"
  | some name => TextualData.nameValue name

def decodeHypothesisName : Atom → Option (Option String)
  | .symbol "MM0AnonymousHypothesisNameV1" => some none
  | atom => (TextualData.decodeName atom).map some

@[simp] theorem decodeHypothesisName_hypothesisNameValue (name : Option String) :
    decodeHypothesisName (hypothesisNameValue name) = some name := by
  cases name with
  | none => rfl
  | some name =>
      have notAnonymous : TextualData.nameValue name ≠ .symbol "MM0AnonymousHypothesisNameV1" := by
        cases chars : name.toList <;>
          simp [TextualData.nameValue, TextualData.nameCharsValue, TextualData.scalarListValue, chars]
      have fallback : decodeHypothesisName (TextualData.nameValue name) =
          (TextualData.decodeName (TextualData.nameValue name)).map some := by
        unfold decodeHypothesisName
        split
        · rename_i matched
          exact (notAnonymous matched).elim
        · rfl
      change decodeHypothesisName (TextualData.nameValue name) = some (some name)
      rw [fallback]
      simp

theorem decodeHypothesisName_reflects (atom : Atom) (name : Option String)
    (decoded : decodeHypothesisName atom = some name) : atom = hypothesisNameValue name := by
  unfold decodeHypothesisName at decoded
  split at decoded
  · cases decoded
    rfl
  · obtain ⟨decodedName, named, output⟩ := Option.map_eq_some_iff.mp decoded
    subst name
    exact TextualData.decodeName_reflects atom decodedName named

def hypothesisValue (hypothesis : SourceHypothesis) : Atom :=
  .expression [.symbol "MM0HypothesisV1", hypothesisNameValue hypothesis.1, hypothesis.2]

def decodeHypothesis : Atom → Option SourceHypothesis
  | .expression [.symbol "MM0HypothesisV1", name, expression] =>
      (decodeHypothesisName name).map (fun decoded => (decoded, expression))
  | _ => none

@[simp] theorem decodeHypothesis_hypothesisValue (hypothesis : SourceHypothesis) :
    decodeHypothesis (hypothesisValue hypothesis) = some hypothesis := by
  cases hypothesis
  simp [hypothesisValue, decodeHypothesis]

theorem decodeHypothesis_reflects (atom : Atom) (hypothesis : SourceHypothesis)
    (decoded : decodeHypothesis atom = some hypothesis) : atom = hypothesisValue hypothesis := by
  unfold decodeHypothesis at decoded
  split at decoded
  · rename_i name expression
    obtain ⟨decodedName, named, same⟩ := Option.map_eq_some_iff.mp decoded
    subst hypothesis
    rw [decodeHypothesisName_reflects name decodedName named]
    rfl
  · simp at decoded

def hypothesesValue : List SourceHypothesis → Atom
  | [] => .symbol "nil"
  | first :: rest => .expression [.symbol "cons", hypothesisValue first, hypothesesValue rest]

def decodeHypotheses : Atom → Option (List SourceHypothesis)
  | .symbol "nil" => some []
  | .expression [.symbol "cons", first, rest] => do
      let hypothesis ← decodeHypothesis first
      let remaining ← decodeHypotheses rest
      pure (hypothesis :: remaining)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeHypotheses_hypothesesValue (hypotheses : List SourceHypothesis) :
    decodeHypotheses (hypothesesValue hypotheses) = some hypotheses := by
  induction hypotheses with
  | nil => simp [hypothesesValue, decodeHypotheses]
  | cons first rest ih => simp [hypothesesValue, decodeHypotheses, ih]

theorem decodeHypotheses_reflects (atom : Atom) (hypotheses : List SourceHypothesis)
    (decoded : decodeHypotheses atom = some hypotheses) : atom = hypothesesValue hypotheses := by
  unfold decodeHypotheses at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i first rest
    obtain ⟨hypothesis, hypothesisDecoded, afterFirst⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨remaining, remainingDecoded, output⟩ := Option.bind_eq_some_iff.mp afterFirst
    have same : hypothesis :: remaining = hypotheses := by simpa using output
    subst hypotheses
    rw [decodeHypothesis_reflects first hypothesis hypothesisDecoded,
      decodeHypotheses_reflects rest remaining remainingDecoded]
    rfl
  · simp at decoded
termination_by sizeOf atom

structure SourceAssertionSignature where
  binders : List SourceBinder
  hypotheses : List SourceHypothesis
  conclusion : Atom
  deriving DecidableEq, Repr

def assertionSignatureValue (signature : SourceAssertionSignature) : Atom :=
  .expression [.symbol "MM0AssertionSignatureV1", TextualProjection.bindersValue signature.binders,
    hypothesesValue signature.hypotheses, signature.conclusion]

def decodeAssertionSignature : Atom → Option SourceAssertionSignature
  | .expression [.symbol "MM0AssertionSignatureV1", binders, hypotheses, conclusion] => do
      let arguments ← TextualProjection.decodeBinders binders
      let premises ← decodeHypotheses hypotheses
      pure ⟨arguments, premises, conclusion⟩
  | _ => none

@[simp] theorem decodeAssertionSignature_assertionSignatureValue (signature : SourceAssertionSignature) :
    decodeAssertionSignature (assertionSignatureValue signature) = some signature := by
  cases signature
  simp [assertionSignatureValue, decodeAssertionSignature]

theorem decodeAssertionSignature_reflects (atom : Atom) (signature : SourceAssertionSignature)
    (decoded : decodeAssertionSignature atom = some signature) : atom = assertionSignatureValue signature := by
  unfold decodeAssertionSignature at decoded
  split at decoded
  · rename_i binders hypotheses conclusion
    obtain ⟨arguments, argumentsDecoded, afterArguments⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨premises, hypothesesDecoded, output⟩ := Option.bind_eq_some_iff.mp afterArguments
    have same : (⟨arguments, premises, conclusion⟩ : SourceAssertionSignature) = signature := by
      simpa using output
    subst signature
    rw [TextualProjection.decodeBinders_reflects binders arguments argumentsDecoded,
      decodeHypotheses_reflects hypotheses premises hypothesesDecoded]
    rfl
  · simp at decoded

def assertionKindValue : Bool → Atom
  | false => .symbol "MM0AxiomDeclarationV1"
  | true => .symbol "MM0TheoremDeclarationV1"

def decodeAssertionKind : Atom → Option Bool
  | .symbol "MM0AxiomDeclarationV1" => some false
  | .symbol "MM0TheoremDeclarationV1" => some true
  | _ => none

@[simp] theorem decodeAssertionKind_assertionKindValue (isTheorem : Bool) :
    decodeAssertionKind (assertionKindValue isTheorem) = some isTheorem := by
  cases isTheorem <;> rfl

theorem decodeAssertionKind_reflects (atom : Atom) (isTheorem : Bool)
    (decoded : decodeAssertionKind atom = some isTheorem) : atom = assertionKindValue isTheorem := by
  unfold decodeAssertionKind at decoded
  split at decoded <;> simp_all [assertionKindValue]

structure SourceTermEntry where
  name : String
  signature : SourceTermSignature
  sourcePosition : Nat
  source : Atom
  deriving DecidableEq, Repr

structure SourceAssertionEntry where
  isTheorem : Bool
  name : String
  signature : SourceAssertionSignature
  sourcePosition : Nat
  source : Atom
  deriving DecidableEq, Repr

def termEntryValue (entry : SourceTermEntry) : Atom :=
  .expression [.symbol "MM0TermEntryV1", TextualData.nameValue entry.name,
    termSignatureValue entry.signature, TextualData.indexValue entry.sourcePosition, entry.source]

def decodeTermEntry : Atom → Option SourceTermEntry
  | .expression [.symbol "MM0TermEntryV1", name, signature, position, source] => do
      let decodedName ← TextualData.decodeName name
      let decodedSignature ← decodeTermSignature signature
      let decodedPosition ← TextualData.decodeIndex position
      pure ⟨decodedName, decodedSignature, decodedPosition, source⟩
  | _ => none

@[simp] theorem decodeTermEntry_termEntryValue (entry : SourceTermEntry) :
    decodeTermEntry (termEntryValue entry) = some entry := by
  cases entry
  simp [termEntryValue, decodeTermEntry]

theorem decodeTermEntry_reflects (atom : Atom) (entry : SourceTermEntry)
    (decoded : decodeTermEntry atom = some entry) : atom = termEntryValue entry := by
  unfold decodeTermEntry at decoded
  split at decoded
  · rename_i name signature position source
    obtain ⟨decodedName, nameDecoded, afterName⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨decodedSignature, signatureDecoded, afterSignature⟩ := Option.bind_eq_some_iff.mp afterName
    obtain ⟨decodedPosition, positionDecoded, output⟩ := Option.bind_eq_some_iff.mp afterSignature
    have same : (⟨decodedName, decodedSignature, decodedPosition, source⟩ : SourceTermEntry) = entry := by
      simpa using output
    subst entry
    rw [TextualData.decodeName_reflects name decodedName nameDecoded,
      decodeTermSignature_reflects signature decodedSignature signatureDecoded,
      TextualData.decodeIndex_reflects position decodedPosition positionDecoded]
    rfl
  · simp at decoded

def assertionEntryValue (entry : SourceAssertionEntry) : Atom :=
  .expression [.symbol "MM0AssertionEntryV1", assertionKindValue entry.isTheorem,
    TextualData.nameValue entry.name, assertionSignatureValue entry.signature,
    TextualData.indexValue entry.sourcePosition, entry.source]

def decodeAssertionEntry : Atom → Option SourceAssertionEntry
  | .expression [.symbol "MM0AssertionEntryV1", kind, name, signature, position, source] => do
      let isTheorem ← decodeAssertionKind kind
      let decodedName ← TextualData.decodeName name
      let decodedSignature ← decodeAssertionSignature signature
      let decodedPosition ← TextualData.decodeIndex position
      pure ⟨isTheorem, decodedName, decodedSignature, decodedPosition, source⟩
  | _ => none

@[simp] theorem decodeAssertionEntry_assertionEntryValue (entry : SourceAssertionEntry) :
    decodeAssertionEntry (assertionEntryValue entry) = some entry := by
  cases entry
  simp [assertionEntryValue, decodeAssertionEntry]

theorem decodeAssertionEntry_reflects (atom : Atom) (entry : SourceAssertionEntry)
    (decoded : decodeAssertionEntry atom = some entry) : atom = assertionEntryValue entry := by
  unfold decodeAssertionEntry at decoded
  split at decoded
  · rename_i kind name signature position source
    obtain ⟨isTheorem, kindDecoded, afterKind⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨decodedName, nameDecoded, afterName⟩ := Option.bind_eq_some_iff.mp afterKind
    obtain ⟨decodedSignature, signatureDecoded, afterSignature⟩ := Option.bind_eq_some_iff.mp afterName
    obtain ⟨decodedPosition, positionDecoded, output⟩ := Option.bind_eq_some_iff.mp afterSignature
    have same : (⟨isTheorem, decodedName, decodedSignature, decodedPosition, source⟩ : SourceAssertionEntry) =
        entry := by simpa using output
    subst entry
    rw [decodeAssertionKind_reflects kind isTheorem kindDecoded,
      TextualData.decodeName_reflects name decodedName nameDecoded,
      decodeAssertionSignature_reflects signature decodedSignature signatureDecoded,
      TextualData.decodeIndex_reflects position decodedPosition positionDecoded]
    rfl
  · simp at decoded

/-- Source row metadata, with expressions retained in the existing Atom carrier. -/
inductive SourceDeclaration where
  | term (entry : SourceTermEntry)
  | assertion (entry : SourceAssertionEntry)
  deriving DecidableEq, Repr

def declarationValue : SourceDeclaration → Atom
  | .term entry => termEntryValue entry
  | .assertion entry => assertionEntryValue entry

def decodeDeclaration (atom : Atom) : Option SourceDeclaration :=
  match decodeTermEntry atom with
  | some entry => some (.term entry)
  | none => (decodeAssertionEntry atom).map SourceDeclaration.assertion

@[simp] theorem decodeDeclaration_declarationValue (declaration : SourceDeclaration) :
    decodeDeclaration (declarationValue declaration) = some declaration := by
  cases declaration with
  | term entry => simp [declarationValue, decodeDeclaration]
  | assertion entry =>
      simp [declarationValue, decodeDeclaration, decodeTermEntry, assertionEntryValue, decodeAssertionEntry]

theorem decodeDeclaration_reflects (atom : Atom) (declaration : SourceDeclaration)
    (decoded : decodeDeclaration atom = some declaration) : atom = declarationValue declaration := by
  unfold decodeDeclaration at decoded
  split at decoded
  · rename_i entry found
    cases decoded
    exact decodeTermEntry_reflects atom entry found
  · obtain ⟨entry, found, output⟩ := Option.map_eq_some_iff.mp decoded
    subst declaration
    exact decodeAssertionEntry_reflects atom entry found

theorem declarationValue_injective : Function.Injective declarationValue := by
  intro first second same
  have decoded := congrArg decodeDeclaration same
  simpa using decoded

def declarationEntriesValue : List SourceDeclaration → Atom
  | [] => .symbol "MM0DeclarationEntriesNilV1"
  | first :: rest => .expression [.symbol "MM0DeclarationEntriesConsV1",
      declarationValue first, declarationEntriesValue rest]

def decodeDeclarationEntries : Atom → Option (List SourceDeclaration)
  | .symbol "MM0DeclarationEntriesNilV1" => some []
  | .expression [.symbol "MM0DeclarationEntriesConsV1", first, rest] => do
      let entry ← decodeDeclaration first
      let remaining ← decodeDeclarationEntries rest
      pure (entry :: remaining)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeDeclarationEntries_declarationEntriesValue (entries : List SourceDeclaration) :
    decodeDeclarationEntries (declarationEntriesValue entries) = some entries := by
  induction entries with
  | nil => simp [declarationEntriesValue, decodeDeclarationEntries]
  | cons first rest ih => simp [declarationEntriesValue, decodeDeclarationEntries, ih]

theorem decodeDeclarationEntries_reflects (atom : Atom) (entries : List SourceDeclaration)
    (decoded : decodeDeclarationEntries atom = some entries) : atom = declarationEntriesValue entries := by
  unfold decodeDeclarationEntries at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i first rest
    obtain ⟨entry, entryDecoded, afterFirst⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨remaining, remainingDecoded, output⟩ := Option.bind_eq_some_iff.mp afterFirst
    have same : entry :: remaining = entries := by simpa using output
    subst entries
    rw [decodeDeclaration_reflects first entry entryDecoded,
      decodeDeclarationEntries_reflects rest remaining remainingDecoded]
    rfl
  · simp at decoded
termination_by sizeOf atom

structure DefinitionSource where
  dummies : List SourceBinder
  body : Option Atom
  deriving DecidableEq, Repr

def optionalExpressionValue : Option Atom → Atom
  | none => .symbol "none"
  | some expression => .expression [.symbol "some", expression]

def decodeOptionalExpression : Atom → Option (Option Atom)
  | .symbol "none" => some none
  | .expression [.symbol "some", expression] => some (some expression)
  | _ => none

@[simp] theorem decodeOptionalExpression_optionalExpressionValue (expression : Option Atom) :
    decodeOptionalExpression (optionalExpressionValue expression) = some expression := by
  cases expression <;> rfl

theorem decodeOptionalExpression_reflects (atom : Atom) (expression : Option Atom)
    (decoded : decodeOptionalExpression atom = some expression) : atom = optionalExpressionValue expression := by
  unfold decodeOptionalExpression at decoded
  split at decoded
  · simp only [Option.some.injEq] at decoded
    subst expression
    rfl
  · simp only [Option.some.injEq] at decoded
    subst expression
    rfl
  · simp at decoded

def definitionSourceValue (source : DefinitionSource) : Atom :=
  .expression [.symbol "MM0DefinitionSourceV1", TextualProjection.bindersValue source.dummies,
    optionalExpressionValue source.body, .symbol "MM0RuntimeTextualSourceV1"]

def decodeDefinitionSource : Atom → Option DefinitionSource
  | .expression [.symbol "MM0DefinitionSourceV1", dummies, body, .symbol "MM0RuntimeTextualSourceV1"] => do
      let binders ← TextualProjection.decodeBinders dummies
      let expression ← decodeOptionalExpression body
      pure ⟨binders, expression⟩
  | _ => none

@[simp] theorem decodeDefinitionSource_definitionSourceValue (source : DefinitionSource) :
    decodeDefinitionSource (definitionSourceValue source) = some source := by
  cases source
  simp [definitionSourceValue, decodeDefinitionSource]

theorem decodeDefinitionSource_reflects (atom : Atom) (source : DefinitionSource)
    (decoded : decodeDefinitionSource atom = some source) : atom = definitionSourceValue source := by
  unfold decodeDefinitionSource at decoded
  split at decoded
  · rename_i dummies body
    obtain ⟨binders, bindersDecoded, afterBinders⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨expression, expressionDecoded, output⟩ := Option.bind_eq_some_iff.mp afterBinders
    have same : (⟨binders, expression⟩ : DefinitionSource) = source := by simpa using output
    subst source
    rw [TextualProjection.decodeBinders_reflects dummies binders bindersDecoded,
      decodeOptionalExpression_reflects body expression expressionDecoded]
    rfl
  · simp at decoded

/-! ## Dense term namespace, shared by primitives and definitions -/

def termEntries (declarations : List SourceDeclaration) : List SourceTermEntry :=
  declarations.filterMap (fun declaration => match declaration with
    | .term entry => some entry
    | .assertion _ => none)

def termIndex? (declarations : List SourceDeclaration) (name : String) : Option Nat :=
  (termEntries declarations).findIdx? (fun entry => entry.name == name)

def termRows (declarations : List SourceDeclaration) : List (Nat × SourceTermEntry) :=
  (termEntries declarations).zipIdx.map (fun entry => (entry.2, entry.1))

theorem termIndex_sound {declarations : List SourceDeclaration} {name : String} {index : Nat}
    (found : termIndex? declarations name = some index) :
    ∃ entry, (termEntries declarations)[index]? = some entry ∧ entry.name = name := by
  obtain ⟨bound, matched, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  exact ⟨(termEntries declarations)[index], List.getElem?_eq_getElem bound, by simpa using matched⟩

theorem termIndex_complete {declarations : List SourceDeclaration}
    (unique : ((termEntries declarations).map SourceTermEntry.name).Nodup)
    {entry : SourceTermEntry} {index : Nat}
    (found : (termEntries declarations)[index]? = some entry) : termIndex? declarations entry.name = some index := by
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp found
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨bound, by simp [atIndex], ?_⟩
  intro previous earlier
  simp only [beq_iff_eq]
  intro same
  have previousBound : previous < ((termEntries declarations).map SourceTermEntry.name).length := by
    simpa using Nat.lt_trans earlier bound
  have indexBound : index < ((termEntries declarations).map SourceTermEntry.name).length := by
    simpa using bound
  have equalNames : ((termEntries declarations).map SourceTermEntry.name)[previous]'previousBound =
      ((termEntries declarations).map SourceTermEntry.name)[index]'indexBound := by
    simp [List.getElem_map, atIndex, same]
  have equalIndices : previous = index := unique.getElem_inj_iff.mp equalNames
  omega

theorem termIndex_missing_iff (declarations : List SourceDeclaration) (name : String) :
    termIndex? declarations name = none ↔ ∀ entry ∈ termEntries declarations, entry.name ≠ name := by
  simp [termIndex?, List.findIdx?_eq_none_iff]

theorem termIndex_prefix {preceding : List SourceDeclaration} (suffix : List SourceDeclaration)
    {name : String} {index : Nat} (found : termIndex? preceding name = some index) :
    termIndex? (preceding ++ suffix) name = some index := by
  change (termEntries preceding).findIdx? (fun entry => entry.name == name) = some index at found
  have appended : termEntries (preceding ++ suffix) = termEntries preceding ++ termEntries suffix := by
    simp [termEntries, List.filterMap_append]
  unfold termIndex?
  rw [appended, List.findIdx?_append, found]
  rfl

@[simp] theorem termRows_getElem? (declarations : List SourceDeclaration) (index : Nat) :
    (termRows declarations)[index]? = ((termEntries declarations)[index]?).map (fun entry => (index, entry)) := by
  simp [termRows, List.getElem?_zipIdx, Option.map_map, Function.comp_def]

theorem termIndex_row_alignment {declarations : List SourceDeclaration} {name : String} {index : Nat}
    (found : termIndex? declarations name = some index) :
    ∃ entry, (termEntries declarations)[index]? = some entry ∧ entry.name = name ∧
      (termRows declarations)[index]? = some (index, entry) := by
  obtain ⟨entry, atIndex, named⟩ := termIndex_sound found
  exact ⟨entry, atIndex, named, by simp [atIndex]⟩

theorem termRows_dense_ids (declarations : List SourceDeclaration) :
    (termRows declarations).map Prod.fst = List.range (termEntries declarations).length := by
  simp [termRows, List.map_map, Function.comp_def, List.range_eq_range']

theorem termRows_unique_ids (declarations : List SourceDeclaration) :
    ((termRows declarations).map Prod.fst).Nodup := by
  rw [termRows_dense_ids]
  exact List.nodup_range

theorem termRows_no_skipped_ids (declarations : List SourceDeclaration) (index : Nat) :
    index ∈ (termRows declarations).map Prod.fst ↔ index < (termEntries declarations).length := by
  rw [termRows_dense_ids]
  exact List.mem_range

def visibleTermIndex? (declarations : List SourceDeclaration) (limit : Nat) (name : String) : Option Nat :=
  (termIndex? declarations name).bind (Option.guard (fun index => index < limit))

theorem visibleTermIndex_iff (declarations : List SourceDeclaration) (limit : Nat) (name : String) (index : Nat) :
    visibleTermIndex? declarations limit name = some index ↔
      termIndex? declarations name = some index ∧ index < limit := by
  simp [visibleTermIndex?, Option.bind_eq_some_iff, Option.guard]

theorem visibleTermIndex_prefix (declarations : List SourceDeclaration) (limit : Nat) (name : String) :
    visibleTermIndex? declarations limit name =
      ((termEntries declarations).take limit).findIdx? (fun entry => entry.name == name) := by
  exact List.findIdx?_take.symm

/-! ## Signature and expression projection -/

def projectTermSignature (sorts : List SortEntry) (sortLimit : Nat)
    (signature : SourceTermSignature) : Option TermDecl := do
  let arguments ← TextualProjection.projectContext (sorts.take sortLimit) signature.binders
  let resultSort ← TextualProjection.sortIndex? (sorts.take sortLimit) signature.result.sortName
  let dependencies ← TextualProjection.dependencies? signature.binders signature.result.dependencies
  pure ⟨arguments, resultSort, dependencies⟩

theorem projectTermSignature_arguments {sorts : List SortEntry} {sortLimit : Nat}
    {signature : SourceTermSignature} {target : TermDecl}
    (projected : projectTermSignature sorts sortLimit signature = some target) :
    TextualProjection.projectContext (sorts.take sortLimit) signature.binders = some target.arguments := by
  obtain ⟨arguments, contextProjected, afterContext⟩ := Option.bind_eq_some_iff.mp projected
  obtain ⟨resultSort, _, afterSort⟩ := Option.bind_eq_some_iff.mp afterContext
  obtain ⟨dependencies, _, output⟩ := Option.bind_eq_some_iff.mp afterSort
  have same : (⟨arguments, resultSort, dependencies⟩ : TermDecl) = target := by simpa using output
  subst target
  exact contextProjected

theorem projectTermSignature_result_scope {sorts : List SortEntry} {sortLimit : Nat}
    {signature : SourceTermSignature} {target : TermDecl}
    (projected : projectTermSignature sorts sortLimit signature = some target) :
    TextualProjection.sortIndex? sorts signature.result.sortName = some target.resultSort ∧
      target.resultSort < sortLimit := by
  obtain ⟨arguments, _, afterContext⟩ := Option.bind_eq_some_iff.mp projected
  obtain ⟨resultSort, resultFound, afterSort⟩ := Option.bind_eq_some_iff.mp afterContext
  obtain ⟨dependencies, _, output⟩ := Option.bind_eq_some_iff.mp afterSort
  have same : (⟨arguments, resultSort, dependencies⟩ : TermDecl) = target := by simpa using output
  subst target
  exact (TextualProjection.sortIndex_before_iff sorts sortLimit signature.result.sortName resultSort).mp resultFound

theorem projectTermSignature_dependencies_bound {sorts : List SortEntry} {sortLimit : Nat}
    {signature : SourceTermSignature} {target : TermDecl}
    (projected : projectTermSignature sorts sortLimit signature = some target)
    {index : Nat} (member : index ∈ target.dependencies) :
    ∃ sort, target.arguments[index]? = some (.bound sort) := by
  obtain ⟨arguments, contextProjected, afterContext⟩ := Option.bind_eq_some_iff.mp projected
  obtain ⟨resultSort, _, afterSort⟩ := Option.bind_eq_some_iff.mp afterContext
  obtain ⟨dependencies, resolved, output⟩ := Option.bind_eq_some_iff.mp afterSort
  have same : (⟨arguments, resultSort, dependencies⟩ : TermDecl) = target := by simpa using output
  subst target
  exact TextualProjection.dependencies_in_projected_context contextProjected resolved member

def variableValue (name : String) (sort : Atom) : Atom :=
  .expression [.symbol "MM0ExpressionVariableV1", TextualData.nameValue name, sort]

def argumentsValue : List Atom → Atom
  | [] => .symbol "MM0ExpressionArgumentsNilV1"
  | first :: rest => .expression [.symbol "MM0ExpressionArgumentsConsV1", first, argumentsValue rest]

def decodeArguments : Atom → Option (List Atom)
  | .symbol "MM0ExpressionArgumentsNilV1" => some []
  | .expression [.symbol "MM0ExpressionArgumentsConsV1", first, rest] =>
      (decodeArguments rest).map (first :: ·)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeArguments_argumentsValue (arguments : List Atom) :
    decodeArguments (argumentsValue arguments) = some arguments := by
  induction arguments with
  | nil => simp [argumentsValue, decodeArguments]
  | cons first rest ih => simp [argumentsValue, decodeArguments, ih]

theorem decodeArguments_reflects (atom : Atom) (arguments : List Atom)
    (decoded : decodeArguments atom = some arguments) : atom = argumentsValue arguments := by
  unfold decodeArguments at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i first rest
    obtain ⟨remaining, remainingDecoded, output⟩ := Option.map_eq_some_iff.mp decoded
    subst arguments
    rw [decodeArguments_reflects rest remaining remainingDecoded]
    rfl
  · simp at decoded
termination_by sizeOf atom

def termApplicationValue (name : String) (arguments : List Atom) (sort : Atom) : Atom :=
  .expression [.symbol "MM0ExpressionTermApplicationV1", TextualData.nameValue name,
    argumentsValue arguments, sort]

mutual
  def projectExpression (declarations : List SourceDeclaration) (termLimit : Nat)
      (binders : List SourceBinder) : Atom → Option Preterm
    | .expression [.symbol "MM0ExpressionVariableV1", sourceName, _] => do
        let name ← TextualData.decodeName sourceName
        let index ← TextualProjection.binderIndex? binders name
        pure (.var index)
    | .expression [.symbol "MM0ExpressionTermApplicationV1", sourceName, arguments, _] => do
        let name ← TextualData.decodeName sourceName
        let index ← visibleTermIndex? declarations termLimit name
        applyArguments declarations termLimit binders arguments (.term index)
    | _ => none
  termination_by atom => sizeOf atom

  def applyArguments (declarations : List SourceDeclaration) (termLimit : Nat)
      (binders : List SourceBinder) (arguments : Atom) (head : Preterm) : Option Preterm :=
    match arguments with
    | .symbol "MM0ExpressionArgumentsNilV1" => some head
    | .expression [.symbol "MM0ExpressionArgumentsConsV1", first, rest] => do
        let argument ← projectExpression declarations termLimit binders first
        applyArguments declarations termLimit binders rest (.app head argument)
    | _ => none
  termination_by sizeOf arguments
end

/-- Every numeric reference stays inside its supplied namespace and context. -/
def Scoped (binderCount termLimit : Nat) : Preterm → Prop
  | .var index => index < binderCount
  | .term index => index < termLimit
  | .app function argument => Scoped binderCount termLimit function ∧ Scoped binderCount termLimit argument

mutual
  theorem projectExpression_scoped (declarations : List SourceDeclaration) (termLimit : Nat)
      (binders : List SourceBinder) (expression : Atom) (target : Preterm)
      (projected : projectExpression declarations termLimit binders expression = some target) :
      Scoped binders.length termLimit target := by
    unfold projectExpression at projected
    split at projected
    · obtain ⟨name, _, afterName⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨index, found, output⟩ := Option.bind_eq_some_iff.mp afterName
      have same : Preterm.var index = target := by simpa using output
      subst target
      obtain ⟨_, atIndex, _⟩ := TextualProjection.binderIndex_sound found
      exact (List.getElem?_eq_some_iff.mp atIndex).1
    · rename_i sourceName arguments sort
      obtain ⟨name, _, afterName⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨index, found, applied⟩ := Option.bind_eq_some_iff.mp afterName
      have inScope := (visibleTermIndex_iff declarations termLimit name index).mp found
      exact applyArguments_scoped declarations termLimit binders arguments (.term index) target inScope.2 applied
    · simp at projected
  termination_by sizeOf expression

  theorem applyArguments_scoped (declarations : List SourceDeclaration) (termLimit : Nat)
      (binders : List SourceBinder) (arguments : Atom) (head target : Preterm)
      (headScoped : Scoped binders.length termLimit head)
      (projected : applyArguments declarations termLimit binders arguments head = some target) :
      Scoped binders.length termLimit target := by
    unfold applyArguments at projected
    split at projected
    · cases projected
      exact headScoped
    · rename_i first rest
      obtain ⟨argument, firstProjected, restProjected⟩ := Option.bind_eq_some_iff.mp projected
      have firstScoped := projectExpression_scoped declarations termLimit binders first argument firstProjected
      exact applyArguments_scoped declarations termLimit binders rest (.app head argument) target
        ⟨headScoped, firstScoped⟩ restProjected
    · simp at projected
  termination_by sizeOf arguments
end

theorem projectExpression_variable (declarations : List SourceDeclaration) (termLimit : Nat)
    (binders : List SourceBinder) (name : String) (sort : Atom) :
    projectExpression declarations termLimit binders (variableValue name sort) =
      (TextualProjection.binderIndex? binders name).map Preterm.var := by
  simp [projectExpression, variableValue, Option.bind_some, Option.map_eq_bind]

def projectHypotheses (declarations : List SourceDeclaration) (termLimit : Nat)
    (binders : List SourceBinder) : List SourceHypothesis → Option (List Preterm)
  | [] => some []
  | first :: rest => do
      let expression ← projectExpression declarations termLimit binders first.2
      let remaining ← projectHypotheses declarations termLimit binders rest
      pure (expression :: remaining)

theorem projectHypotheses_scoped {declarations : List SourceDeclaration} {termLimit : Nat}
    {binders : List SourceBinder} {hypotheses : List SourceHypothesis} {targets : List Preterm}
    (projected : projectHypotheses declarations termLimit binders hypotheses = some targets) :
    ∀ target ∈ targets, Scoped binders.length termLimit target := by
  induction hypotheses generalizing targets with
  | nil => simp [projectHypotheses] at projected; subst targets; simp
  | cons first rest ih =>
      obtain ⟨expression, firstProjected, afterFirst⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨remaining, remainingProjected, output⟩ := Option.bind_eq_some_iff.mp afterFirst
      have same : expression :: remaining = targets := by simpa using output
      subst targets
      intro target member
      rcases List.mem_cons.mp member with sameTarget | present
      · subst target
        exact projectExpression_scoped declarations termLimit binders first.2 expression firstProjected
      · exact ih remainingProjected target present

def projectAssertionSignature (sorts : List SortEntry) (sortLimit : Nat)
    (declarations : List SourceDeclaration) (termLimit : Nat)
    (signature : SourceAssertionSignature) : Option TheoremDecl := do
  let arguments ← TextualProjection.projectContext (sorts.take sortLimit) signature.binders
  let hypotheses ← projectHypotheses declarations termLimit signature.binders signature.hypotheses
  let conclusion ← projectExpression declarations termLimit signature.binders signature.conclusion
  pure ⟨arguments, hypotheses, conclusion⟩

theorem projectAssertionSignature_scoped {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {termLimit : Nat} {signature : SourceAssertionSignature}
    {target : TheoremDecl}
    (projected : projectAssertionSignature sorts sortLimit declarations termLimit signature = some target) :
    (∀ premise ∈ target.hypotheses, Scoped target.arguments.length termLimit premise) ∧
      Scoped target.arguments.length termLimit target.conclusion := by
  obtain ⟨arguments, contextProjected, afterContext⟩ := Option.bind_eq_some_iff.mp projected
  obtain ⟨hypotheses, hypothesesProjected, afterHypotheses⟩ := Option.bind_eq_some_iff.mp afterContext
  obtain ⟨conclusion, conclusionProjected, output⟩ := Option.bind_eq_some_iff.mp afterHypotheses
  have same : (⟨arguments, hypotheses, conclusion⟩ : TheoremDecl) = target := by simpa using output
  subst target
  have length := TextualProjection.projectContext_length contextProjected
  rw [length]
  exact ⟨projectHypotheses_scoped hypothesesProjected,
    projectExpression_scoped declarations termLimit signature.binders signature.conclusion conclusion conclusionProjected⟩

/-! ## Definition dummies remain outside the public signature -/

def dummySort? (sorts : List SortEntry) (binder : SourceBinder) : Option Nat :=
  if binder.isBound && binder.name.isSome && binder.typeInfo.dependencies.isEmpty then
    TextualProjection.sortIndex? sorts binder.typeInfo.sortName
  else none

def projectDummies (sorts : List SortEntry) : List SourceBinder → Option (List Nat)
  | [] => some []
  | binder :: rest => do
      let sort ← dummySort? sorts binder
      let remaining ← projectDummies sorts rest
      pure (sort :: remaining)

theorem projectDummies_length {sorts : List SortEntry} {dummies : List SourceBinder} {indices : List Nat}
    (projected : projectDummies sorts dummies = some indices) : indices.length = dummies.length := by
  induction dummies generalizing indices with
  | nil => simp [projectDummies] at projected; subst indices; rfl
  | cons binder rest ih =>
      obtain ⟨sort, _, afterSort⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨remaining, remainingProjected, output⟩ := Option.bind_eq_some_iff.mp afterSort
      have same : sort :: remaining = indices := by simpa using output
      subst indices
      simp [ih remainingProjected]

theorem dummySort_projects_bound {sorts : List SortEntry} {binder : SourceBinder} {sort : Nat}
    (projected : dummySort? sorts binder = some sort) (preceding : List SourceBinder) :
    TextualProjection.projectBinder sorts preceding binder = some (.bound sort) := by
  unfold dummySort? at projected
  split at projected
  · rename_i shape
    simp only [Bool.and_eq_true] at shape
    simp [TextualProjection.projectBinder, shape.1.1, shape.2, projected]
  · simp at projected

theorem projectDummies_contextFrom {sorts : List SortEntry} {dummies : List SourceBinder} {indices : List Nat}
    (projected : projectDummies sorts dummies = some indices) (preceding : List SourceBinder) :
    TextualProjection.projectContextFrom sorts preceding dummies = some (indices.map Binder.bound) := by
  induction dummies generalizing indices preceding with
  | nil => simp [projectDummies] at projected; subst indices; rfl
  | cons binder rest ih =>
      obtain ⟨sort, sortProjected, afterSort⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨remaining, remainingProjected, output⟩ := Option.bind_eq_some_iff.mp afterSort
      have same : sort :: remaining = indices := by simpa using output
      subst indices
      simp [TextualProjection.projectContextFrom, dummySort_projects_bound sortProjected preceding,
        ih remainingProjected (preceding ++ [binder])]

theorem projectContextFrom_append (sorts : List SortEntry) (preceding first second : List SourceBinder) :
    TextualProjection.projectContextFrom sorts preceding (first ++ second) =
      (TextualProjection.projectContextFrom sorts preceding first).bind (fun left =>
        (TextualProjection.projectContextFrom sorts (preceding ++ first) second).map
          (fun right => left ++ right)) := by
  induction first generalizing preceding with
  | nil => simp [TextualProjection.projectContextFrom]
  | cons binder rest ih =>
      simp only [List.cons_append, TextualProjection.projectContextFrom]
      rw [ih]
      simp [Option.bind_assoc, Option.map_eq_bind, List.append_assoc]

theorem definition_context_alignment {sorts : List SortEntry} {sortLimit : Nat}
    {signature : SourceTermSignature} {declaration : TermDecl}
    (publicProjected : projectTermSignature sorts sortLimit signature = some declaration)
    {dummies : List SourceBinder} {indices : List Nat}
    (dummiesProjected : projectDummies (sorts.take sortLimit) dummies = some indices)
    {fullContext : Context}
    (fullProjected : TextualProjection.projectContext (sorts.take sortLimit) (signature.binders ++ dummies) =
      some fullContext) :
    fullContext = declaration.arguments ++ indices.map Binder.bound := by
  have publicContext := projectTermSignature_arguments publicProjected
  unfold TextualProjection.projectContext at publicContext fullProjected
  split at publicContext
  · split at fullProjected
    · rw [projectContextFrom_append] at fullProjected
      simp only [List.nil_append, publicContext, Option.bind_some,
        projectDummies_contextFrom dummiesProjected, Option.map_some, Option.some.injEq] at fullProjected
      exact fullProjected.symm
    · simp at fullProjected
  · simp at publicContext

def projectDefinitionBody (sorts : List SortEntry) (sortLimit : Nat)
    (declarations : List SourceDeclaration) (termLimit : Nat)
    (signature : SourceTermSignature) (source : DefinitionSource) : Option (Option Kernel.Definition.Body) :=
  match source.body with
  | none => if source.dummies.isEmpty then some none else none
  | some expression => do
      let dummies ← projectDummies (sorts.take sortLimit) source.dummies
      let _context ← TextualProjection.projectContext (sorts.take sortLimit) (signature.binders ++ source.dummies)
      let body ← projectExpression declarations termLimit (signature.binders ++ source.dummies) expression
      pure (some ⟨dummies, body⟩)

theorem projectDefinitionBody_context {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {termLimit : Nat} {signature : SourceTermSignature}
    {declaration : TermDecl} (publicProjected : projectTermSignature sorts sortLimit signature = some declaration)
    {source : DefinitionSource} {body : Kernel.Definition.Body}
    (bodyProjected : projectDefinitionBody sorts sortLimit declarations termLimit signature source = some (some body)) :
    TextualProjection.projectContext (sorts.take sortLimit) (signature.binders ++ source.dummies) =
      some (Kernel.Definition.Body.context declaration body) ∧
      Scoped (Kernel.Definition.Body.context declaration body).length termLimit body.expression := by
  unfold projectDefinitionBody at bodyProjected
  split at bodyProjected
  · split at bodyProjected <;> simp at bodyProjected
  · rename_i expression hasBody
    obtain ⟨dummies, dummiesProjected, afterDummies⟩ := Option.bind_eq_some_iff.mp bodyProjected
    obtain ⟨context, contextProjected, afterContext⟩ := Option.bind_eq_some_iff.mp afterDummies
    obtain ⟨projectedExpression, expressionProjected, output⟩ := Option.bind_eq_some_iff.mp afterContext
    have same : (⟨dummies, projectedExpression⟩ : Kernel.Definition.Body) = body := by simpa using output
    subst body
    have aligned := definition_context_alignment publicProjected dummiesProjected contextProjected
    have fullLength := TextualProjection.projectContext_length contextProjected
    have scopedExpression := projectExpression_scoped declarations termLimit (signature.binders ++ source.dummies)
      expression projectedExpression expressionProjected
    constructor
    · simpa [Kernel.Definition.Body.context, aligned] using contextProjected
    · change Scoped (declaration.arguments ++ dummies.map Binder.bound).length termLimit projectedExpression
      rw [← aligned, fullLength]
      exact scopedExpression

/-! ## Existing specification entries, preserving the two dense namespaces -/

def projectDeclaration (sorts : List SortEntry) (sortLimit : Nat)
    (declarations : List SourceDeclaration) (termIndex assertionIndex : Nat) :
    SourceDeclaration → Option SpecificationEntry
  | .term entry => do
      let declaration ← projectTermSignature sorts sortLimit entry.signature
      if entry.source == .symbol "MM0RuntimeTextualSourceV1" then
        some (.term termIndex declaration)
      else do
        let source ← decodeDefinitionSource entry.source
        let body ← projectDefinitionBody sorts sortLimit declarations termIndex entry.signature source
        pure (.definition termIndex declaration body)
  | .assertion entry => do
      let declaration ← projectAssertionSignature sorts sortLimit declarations termIndex entry.signature
      if entry.isTheorem then some (.theoremDecl assertionIndex declaration)
      else some (.axiomDecl assertionIndex declaration)

def specificationTermId : SpecificationEntry → Option Nat
  | .term index _ | .definition index _ _ => some index
  | _ => none

def specificationAssertionId : SpecificationEntry → Option Nat
  | .axiomDecl index _ | .theoremDecl index _ => some index
  | _ => none

theorem projectDeclaration_term_ids {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {termIndex assertionIndex : Nat}
    {entry : SourceTermEntry} {target : SpecificationEntry}
    (projected : projectDeclaration sorts sortLimit declarations termIndex assertionIndex (.term entry) = some target) :
    specificationTermId target = some termIndex ∧ specificationAssertionId target = none := by
  obtain ⟨declaration, _, afterSignature⟩ := Option.bind_eq_some_iff.mp projected
  split at afterSignature
  · have same : SpecificationEntry.term termIndex declaration = target := by simpa using afterSignature
    subst target
    exact ⟨rfl, rfl⟩
  · obtain ⟨source, _, afterSource⟩ := Option.bind_eq_some_iff.mp afterSignature
    obtain ⟨body, _, output⟩ := Option.bind_eq_some_iff.mp afterSource
    have same : SpecificationEntry.definition termIndex declaration body = target := by simpa using output
    subst target
    exact ⟨rfl, rfl⟩

theorem projectDeclaration_assertion_ids {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {termIndex assertionIndex : Nat}
    {entry : SourceAssertionEntry} {target : SpecificationEntry}
    (projected : projectDeclaration sorts sortLimit declarations termIndex assertionIndex (.assertion entry) =
      some target) :
    specificationTermId target = none ∧ specificationAssertionId target = some assertionIndex := by
  obtain ⟨declaration, _, afterSignature⟩ := Option.bind_eq_some_iff.mp projected
  split at afterSignature
  · have same : SpecificationEntry.theoremDecl assertionIndex declaration = target := by simpa using afterSignature
    subst target
    exact ⟨rfl, rfl⟩
  · have same : SpecificationEntry.axiomDecl assertionIndex declaration = target := by simpa using afterSignature
    subst target
    exact ⟨rfl, rfl⟩

def assertionEntries (declarations : List SourceDeclaration) : List SourceAssertionEntry :=
  declarations.filterMap (fun declaration => match declaration with
    | .term _ => none
    | .assertion entry => some entry)

def projectDeclarationsFrom (sorts : List SortEntry) (sortLimit : Nat) (all : List SourceDeclaration) :
    List SourceDeclaration → Nat → Nat → Option (List SpecificationEntry)
  | [], _, _ => some []
  | .term entry :: rest, termIndex, assertionIndex => do
      let first ← projectDeclaration sorts sortLimit all termIndex assertionIndex (.term entry)
      let remaining ← projectDeclarationsFrom sorts sortLimit all rest (termIndex + 1) assertionIndex
      pure (first :: remaining)
  | .assertion entry :: rest, termIndex, assertionIndex => do
      let first ← projectDeclaration sorts sortLimit all termIndex assertionIndex (.assertion entry)
      let remaining ← projectDeclarationsFrom sorts sortLimit all rest termIndex (assertionIndex + 1)
      pure (first :: remaining)

def SourceDeclaration.name : SourceDeclaration → String
  | .term entry => entry.name
  | .assertion entry => entry.name

def SourceDeclaration.sourcePosition : SourceDeclaration → Nat
  | .term entry => entry.sourcePosition
  | .assertion entry => entry.sourcePosition

/-- MM0 keeps term/definition names separate from axiom/theorem names. The
shared declaration sequence preserves source order across both families. -/
def declarationScope (declarations : List SourceDeclaration) : Prop :=
  ((termEntries declarations).map SourceTermEntry.name).Nodup ∧
    ((assertionEntries declarations).map SourceAssertionEntry.name).Nodup ∧
    declarations.Pairwise (fun earlier later => earlier.sourcePosition < later.sourcePosition)

instance (declarations : List SourceDeclaration) : Decidable (declarationScope declarations) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Projection within a fixed available sort prefix. The outer source merge
chooses the changing sort prefix when sort and declaration rows interleave. -/
def projectDeclarations (sorts : List SortEntry) (sortLimit : Nat)
    (declarations : List SourceDeclaration) : Option (List SpecificationEntry) :=
  if declarationScope declarations then
    projectDeclarationsFrom sorts sortLimit declarations declarations 0 0
  else none

theorem projectDeclarations_scope {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {targets : List SpecificationEntry}
    (projected : projectDeclarations sorts sortLimit declarations = some targets) :
    declarationScope declarations := by
  unfold projectDeclarations at projected
  split at projected
  · assumption
  · simp at projected

theorem projectDeclarations_namespace_uniqueness {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {targets : List SpecificationEntry}
    (projected : projectDeclarations sorts sortLimit declarations = some targets) :
    ((termEntries declarations).map SourceTermEntry.name).Nodup ∧
      ((assertionEntries declarations).map SourceAssertionEntry.name).Nodup :=
  ⟨(projectDeclarations_scope projected).1, (projectDeclarations_scope projected).2.1⟩

theorem projectDeclarations_source_order {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {targets : List SpecificationEntry}
    (projected : projectDeclarations sorts sortLimit declarations = some targets) :
    declarations.Pairwise (fun earlier later => earlier.sourcePosition < later.sourcePosition) :=
  (projectDeclarations_scope projected).2.2

theorem visibleTermIndex_at_declaration_prefix (preceding suffix : List SourceDeclaration)
    (name : String) :
    visibleTermIndex? (preceding ++ suffix) (termEntries preceding).length name =
      termIndex? preceding name := by
  rw [visibleTermIndex_prefix]
  simp [termEntries, List.filterMap_append, termIndex?]

theorem visible_term_precedes_current_declaration {preceding suffix : List SourceDeclaration}
    {current : SourceDeclaration} {name : String} {index : Nat}
    (ordered : (preceding ++ current :: suffix).Pairwise
      (fun earlier later => earlier.sourcePosition < later.sourcePosition))
    (found : visibleTermIndex? (preceding ++ current :: suffix)
      (termEntries preceding).length name = some index) :
    ∃ entry, (termEntries preceding)[index]? = some entry ∧ entry.name = name ∧
      entry.sourcePosition < current.sourcePosition := by
  rw [visibleTermIndex_at_declaration_prefix] at found
  obtain ⟨entry, atIndex, named⟩ := termIndex_sound found
  have member : entry ∈ termEntries preceding := List.mem_of_getElem? atIndex
  obtain ⟨source, sourceMember, selected⟩ := List.mem_filterMap.mp member
  have termMember : SourceDeclaration.term entry ∈ preceding := by
    cases source with
    | term candidate =>
        have same : candidate = entry := by simpa using selected
        simpa [same] using sourceMember
    | assertion candidate => simp at selected
  have earlier := (List.pairwise_append.mp ordered).2.2
    (.term entry) termMember current (by simp)
  exact ⟨entry, atIndex, named, earlier⟩

theorem projectDeclarationsFrom_dense_ids {sorts : List SortEntry} {sortLimit : Nat}
    {all remaining : List SourceDeclaration} {termIndex assertionIndex : Nat}
    {targets : List SpecificationEntry}
    (projected : projectDeclarationsFrom sorts sortLimit all remaining termIndex assertionIndex = some targets) :
    targets.filterMap specificationTermId = List.range' termIndex (termEntries remaining).length ∧
      targets.filterMap specificationAssertionId = List.range' assertionIndex (assertionEntries remaining).length := by
  induction remaining generalizing targets termIndex assertionIndex with
  | nil =>
      simp [projectDeclarationsFrom] at projected
      subst targets
      simp [termEntries, assertionEntries]
  | cons first rest ih =>
      cases first with
      | term entry =>
          obtain ⟨target, targetProjected, afterFirst⟩ := Option.bind_eq_some_iff.mp projected
          obtain ⟨remainingTargets, restProjected, output⟩ := Option.bind_eq_some_iff.mp afterFirst
          have same : target :: remainingTargets = targets := by simpa using output
          subst targets
          have ids := projectDeclaration_term_ids targetProjected
          have restIds := ih restProjected
          simp [termEntries, assertionEntries, ids.1, ids.2, restIds.1, restIds.2, List.range'_succ]
      | assertion entry =>
          obtain ⟨target, targetProjected, afterFirst⟩ := Option.bind_eq_some_iff.mp projected
          obtain ⟨remainingTargets, restProjected, output⟩ := Option.bind_eq_some_iff.mp afterFirst
          have same : target :: remainingTargets = targets := by simpa using output
          subst targets
          have ids := projectDeclaration_assertion_ids targetProjected
          have restIds := ih restProjected
          simp [termEntries, assertionEntries, ids.1, ids.2, restIds.1, restIds.2, List.range'_succ]

theorem projectDeclarations_dense_ids {sorts : List SortEntry} {sortLimit : Nat}
    {declarations : List SourceDeclaration} {targets : List SpecificationEntry}
    (projected : projectDeclarations sorts sortLimit declarations = some targets) :
    targets.filterMap specificationTermId = List.range (termEntries declarations).length ∧
      targets.filterMap specificationAssertionId = List.range (assertionEntries declarations).length := by
  unfold projectDeclarations at projected
  split at projected
  · simpa [List.range_eq_range'] using projectDeclarationsFrom_dense_ids projected
  · simp at projected

theorem decoded_term_signature_projects_to_existing_codec (sorts : List SortEntry) (sortLimit : Nat)
    (signature : SourceTermSignature) (target : TermDecl)
    (projected : projectTermSignature sorts sortLimit signature = some target) :
    ((decodeTermSignature (termSignatureValue signature)).bind (projectTermSignature sorts sortLimit)).map
      Data.declaration = some (Data.declaration target) := by simp [projected]

theorem decoded_assertion_signature_projects_to_existing_codec (sorts : List SortEntry) (sortLimit : Nat)
    (declarations : List SourceDeclaration) (termLimit : Nat) (signature : SourceAssertionSignature)
    (target : TheoremDecl)
    (projected : projectAssertionSignature sorts sortLimit declarations termLimit signature = some target) :
    ((decodeAssertionSignature (assertionSignatureValue signature)).bind
      (projectAssertionSignature sorts sortLimit declarations termLimit)).map TheoremInstantiation.declarationValue =
      some (TheoremInstantiation.declarationValue target) := by simp [projected]

theorem decoded_declaration_projects_to_existing_codec (sorts : List SortEntry) (sortLimit : Nat)
    (declarations : List SourceDeclaration) (termIndex assertionIndex : Nat) (source : SourceDeclaration)
    (target : SpecificationEntry)
    (projected : projectDeclaration sorts sortLimit declarations termIndex assertionIndex source = some target) :
    ((decodeDeclaration (declarationValue source)).bind
      (projectDeclaration sorts sortLimit declarations termIndex assertionIndex)).map SpecificationMatching.entryValue =
      some (SpecificationMatching.entryValue target) := by simp [projected]

/-! ## Scoped positive and negative controls -/

private def setSort : SortEntry := ⟨"set", {}, 0⟩
private def propSort : SortEntry := ⟨"prop", ⟨false, false, true, false⟩, 2⟩
private def sorts : List SortEntry := [setSort, propSort]
private def setName : Atom := TextualData.nameValue "set"
private def propName : Atom := TextualData.nameValue "prop"

private def anonymousRegular : SourceBinder := ⟨false, none, ⟨"set", []⟩⟩
private def boundX : SourceBinder := ⟨true, some "x", ⟨"set", []⟩⟩
private def regularU : SourceBinder := ⟨false, some "u", ⟨"set", ["x"]⟩⟩
private def dummyY : SourceBinder := ⟨true, some "y", ⟨"set", []⟩⟩
private def publicBinders : List SourceBinder := [anonymousRegular, boundX, regularU]
private def publicSignature : SourceTermSignature := ⟨publicBinders, ⟨"set", ["x"]⟩⟩

private def bindEntry : SourceTermEntry :=
  ⟨"bind", ⟨[⟨true, some "a", ⟨"set", []⟩⟩, ⟨false, none, ⟨"set", ["a"]⟩⟩], ⟨"set", []⟩⟩,
    4, .symbol "MM0RuntimeTextualSourceV1"⟩
private def truthEntry : SourceTermEntry :=
  ⟨"truth", ⟨[], ⟨"prop", []⟩⟩, 8, .symbol "MM0RuntimeTextualSourceV1"⟩
private def dummyBody : Atom :=
  termApplicationValue "bind" [variableValue "y" setName, variableValue "x" setName] setName
private def definedEntry : SourceTermEntry :=
  ⟨"defined", publicSignature, 14, definitionSourceValue ⟨[dummyY], some dummyBody⟩⟩
private def futureEntry : SourceTermEntry :=
  ⟨"future", ⟨[], ⟨"set", []⟩⟩, 18, .symbol "MM0RuntimeTextualSourceV1"⟩
private def truthExpression : Atom := termApplicationValue "truth" [] propName
private def seedEntry : SourceAssertionEntry :=
  ⟨false, "seed", ⟨publicBinders, [(some "h", truthExpression)], truthExpression⟩,
    10, .symbol "MM0RuntimeTextualSourceV1"⟩
private def theoremEntry : SourceAssertionEntry :=
  ⟨true, "later", ⟨publicBinders, [(some "h1", truthExpression), (some "h2", truthExpression)], truthExpression⟩,
    20, .symbol "MM0RuntimeTextualSourceV1"⟩
private def declarations : List SourceDeclaration :=
  [.term bindEntry, .term truthEntry, .assertion seedEntry, .term definedEntry,
    .term futureEntry, .assertion theoremEntry]

theorem primitives_and_definitions_share_dense_term_ids :
    termIndex? declarations "bind" = some 0 ∧
      termIndex? declarations "truth" = some 1 ∧
      termIndex? declarations "defined" = some 2 ∧
      termIndex? declarations "future" = some 3 ∧
      termIndex? declarations "seed" = none ∧
      (termRows declarations).map Prod.fst = [0, 1, 2, 3] := by
  decide +kernel

theorem expression_variables_use_full_context_positions :
    projectExpression declarations 2 (publicBinders ++ [dummyY]) (variableValue "u" setName) = some (.var 2) ∧
      projectExpression declarations 2 (publicBinders ++ [dummyY]) (variableValue "x" setName) = some (.var 1) ∧
      projectExpression declarations 2 (publicBinders ++ [dummyY]) (variableValue "y" setName) = some (.var 3) := by
  decide +kernel

theorem self_and_future_term_references_are_refused :
    projectExpression declarations 2 publicBinders (termApplicationValue "defined" [] setName) = none ∧
      projectExpression declarations 3 publicBinders (termApplicationValue "future" [] setName) = none ∧
      projectExpression declarations 3 publicBinders (termApplicationValue "defined" [] setName) = some (.term 2) := by
  decide +kernel

theorem mixed_public_signature_preserves_bound_dependency :
    projectTermSignature sorts 2 publicSignature =
      some ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], 0, {1}⟩ := by
  decide +kernel

theorem definition_body_uses_public_then_dummy_context :
    projectDeclaration sorts 2 declarations 2 1 (.term definedEntry) =
      some (.definition 2 ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], 0, {1}⟩
        (some ⟨[0], .app (.app (.term 0) (.var 3)) (.var 1)⟩)) := by
  decide +kernel

theorem definition_context_has_one_extra_bound_slot :
    Kernel.Definition.Body.context
      ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], 0, {1}⟩
      ⟨[0], .app (.app (.term 0) (.var 3)) (.var 1)⟩ =
        [.regular 0 ∅, .bound 0, .regular 0 {1}, .bound 0] := by
  rfl

theorem dummy_names_cannot_enter_public_return_dependencies :
    projectTermSignature sorts 2 ⟨publicBinders, ⟨"set", ["y"]⟩⟩ = none := by
  decide +kernel

theorem definition_without_body_remains_unspecified :
    projectDeclaration sorts 2 declarations 2 1
      (.term ⟨"unspecified", publicSignature, 14, definitionSourceValue ⟨[], none⟩⟩) =
      some (.definition 2 ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], 0, {1}⟩ none) := by
  decide +kernel

theorem dummies_without_definition_body_are_refused :
    projectDefinitionBody sorts 2 declarations 2 publicSignature ⟨[dummyY], none⟩ = none := by
  decide +kernel

theorem malformed_dummy_shapes_are_refused :
    projectDummies sorts [anonymousRegular] = none ∧
      projectDummies sorts [⟨true, none, ⟨"set", []⟩⟩] = none ∧
      projectDummies sorts [⟨true, some "y", ⟨"set", ["x"]⟩⟩] = none := by
  decide +kernel

theorem public_and_dummy_name_collision_is_refused :
    projectDefinitionBody sorts 2 declarations 2 publicSignature
      ⟨[boundX], some (variableValue "x" setName)⟩ = none := by
  decide +kernel

theorem definition_body_cannot_refer_to_itself_or_future_terms :
    projectDefinitionBody sorts 2 declarations 2 publicSignature
      ⟨[], some (termApplicationValue "defined" [] setName)⟩ = none ∧
      projectDefinitionBody sorts 2 declarations 2 publicSignature
        ⟨[], some (termApplicationValue "future" [] setName)⟩ = none := by
  decide +kernel

theorem future_result_sort_is_refused :
    projectTermSignature sorts 1 truthEntry.signature = none ∧
      projectTermSignature sorts 2 truthEntry.signature = some ⟨[], 1, ∅⟩ := by
  decide +kernel

theorem assertions_preserve_order_and_repeated_premises :
    projectDeclaration sorts 2 declarations 4 1 (.assertion theoremEntry) =
      some (.theoremDecl 1 ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], [.term 1, .term 1], .term 1⟩) ∧
      projectDeclaration sorts 2 declarations 2 0 (.assertion seedEntry) =
        some (.axiomDecl 0 ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], [.term 1], .term 1⟩) := by
  decide +kernel

theorem future_term_in_assertion_premise_is_refused :
    projectAssertionSignature sorts 2 declarations 3
      ⟨publicBinders, [(some "bad", termApplicationValue "future" [] setName)], truthExpression⟩ = none := by
  decide +kernel

theorem unknown_expression_names_are_refused :
    projectExpression declarations 4 publicBinders (variableValue "missing" setName) = none ∧
      projectExpression declarations 4 publicBinders (termApplicationValue "missing" [] setName) = none := by
  decide +kernel

theorem unknown_source_metadata_is_refused :
    projectDeclaration sorts 2 declarations 2 0
      (.term ⟨"bad", publicSignature, 14, .symbol "UnknownSource"⟩) = none := by
  decide +kernel

theorem canonical_duplicate_declaration_names_are_refused :
    projectDeclarations sorts 2 [.term bindEntry, .term bindEntry] = none := by
  simp [projectDeclarations, declarationScope, termEntries]

theorem same_spelling_across_namespaces_is_accepted :
    projectDeclarations sorts 2 [.term truthEntry, .assertion { seedEntry with name := "truth" }] =
      some [.term 0 ⟨[], 1, ∅⟩,
        .axiomDecl 0 ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], [.term 0], .term 0⟩] := by
  decide +kernel

theorem duplicate_term_and_definition_name_is_refused :
    projectDeclarations sorts 2
      [.term truthEntry, .term { definedEntry with name := "truth" }] = none := by
  decide +kernel

theorem duplicate_axiom_and_theorem_name_is_refused :
    projectDeclarations sorts 2
      [.term truthEntry, .assertion seedEntry,
        .assertion { theoremEntry with name := "seed" }] = none := by
  decide +kernel

theorem declaration_position_collision_is_refused :
    projectDeclarations sorts 2
      [.term truthEntry, .assertion { seedEntry with sourcePosition := 8 }] = none := by
  decide +kernel

theorem decreasing_declaration_positions_are_refused :
    projectDeclarations sorts 2 [.term truthEntry, .term bindEntry] = none := by
  decide +kernel

theorem future_term_in_ordered_declaration_stream_is_refused :
    projectDeclarations sorts 2
      [.assertion seedEntry, .term { truthEntry with sourcePosition := 12 }] = none := by
  decide +kernel

theorem malformed_optional_body_is_refused :
    decodeDefinitionSource (.expression [.symbol "MM0DefinitionSourceV1",
      TextualProjection.bindersValue [], .expression [.symbol "Some", truthExpression],
      .symbol "MM0RuntimeTextualSourceV1"]) = none := by
  simp [decodeDefinitionSource, decodeOptionalExpression]

theorem native_hypothesis_container_is_refused :
    decodeHypotheses (.expression [hypothesisValue (some "h", truthExpression)]) = none ∧
      decodeHypotheses (hypothesesValue [(some "h", truthExpression)]) = some [(some "h", truthExpression)] := by
  constructor
  · simp [decodeHypotheses]
  · simp

theorem anonymous_hypothesis_name_preserves_its_own_tag :
    decodeHypothesis (.expression [.symbol "MM0HypothesisV1",
      .symbol "MM0AnonymousHypothesisNameV1", truthExpression]) = some (none, truthExpression) ∧
      hypothesisNameValue none ≠ hypothesisNameValue (some "") := by
  decide +kernel

theorem anonymous_hypotheses_still_occupy_ordered_premise_slots :
    projectAssertionSignature sorts 2 declarations 2
      ⟨publicBinders, [(none, truthExpression), (some "h", truthExpression)], truthExpression⟩ =
      some ⟨[.regular 0 ∅, .bound 0, .regular 0 {1}], [.term 1, .term 1], .term 1⟩ := by
  decide +kernel

theorem projected_expression_uses_existing_application_codec :
    (projectExpression declarations 2 (publicBinders ++ [dummyY]) dummyBody).map Data.preterm =
      some (.expression [.symbol "MM0:App",
        .expression [.symbol "MM0:App", .expression [.symbol "MM0:Term", Store.natural 0],
          .expression [.symbol "MM0:Var", Store.natural 3]],
        .expression [.symbol "MM0:Var", Store.natural 1]]) := by
  decide +kernel

theorem mixed_declaration_stream_retains_dense_namespaces :
    ((projectDeclarations sorts 2 declarations).map (List.filterMap specificationTermId)) = some [0, 1, 2, 3] ∧
      ((projectDeclarations sorts 2 declarations).map (List.filterMap specificationAssertionId)) = some [0, 1] := by
  decide +kernel

end Mettapedia.Languages.MM0.MeTTa.TextualDeclarations
