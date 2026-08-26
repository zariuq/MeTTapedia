import Std.Data.String.ToNat
import Mettapedia.Languages.Metamath.SourceStateGSLT
import Mettapedia.GSLT.LanguageDef.InferencePresentationWireFormat
import Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
import Mettapedia.Languages.ProcessCalculi.MORK.ProofRelevantGSLT

/-!
# Lossless Metamath data in an MM2 space

MM2 spaces are sets.  Metamath databases, formulas, proof streams, stacks,
and compressed-proof heaps are ordered and may contain repeated values.  The
encoding below therefore makes every sequence position explicit.  Equality of
payloads never identifies two different occurrences.

Source strings are encoded structurally instead of being printed as raw MM2
symbols.  Metamath permits tokens that overlap the surface syntax of an
S-expression language; embedding such a token directly would make printing a
second, partial parser.  Decimal character codes are ordinary safe MM2 symbols
and have a proved inverse.
-/

namespace Mettapedia.Languages.Metamath.MM2DataEncoding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceStateGSLT
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (WireTerm)
open Mettapedia.GSLT.LanguageDef.InferencePresentationWire
  (RuntimePresentation encodeRuntimePresentation decodeRuntimePresentation)

/-! ## Surface-safe scalar data -/

def natTag : String := "mm-nat"
def stringTag : String := "mm-string"
def constTag : String := "mm-const"
def variableTag : String := "mm-variable"

/-- A natural number represented by a tagged decimal symbol.  The decimal
payload is compact, contains no MM2 delimiter, and is injective. -/
def natAtom (value : Nat) : Atom :=
  .expression [.symbol natTag, .symbol (Nat.repr value)]

@[simp] theorem isGroundAtom_natAtom (value : Nat) :
    isGroundAtom (natAtom value) = true := by
  simp [natAtom, isGroundAtom, isGroundAtom.isGroundList]

/-- Partial inverse of `natAtom`; malformed or non-decimal surface data is
outside the compiler image. -/
def decodeNatAtom : Atom → Option Nat
  | .expression [.symbol tag, .symbol digits] =>
      if tag = natTag then digits.toNat? else none
  | _ => none

@[simp] theorem decodeNatAtom_natAtom (value : Nat) :
    decodeNatAtom (natAtom value) = some value := by
  simp [decodeNatAtom, natAtom, natTag]

theorem natAtom_injective : Function.Injective natAtom := by
  intro left right equal
  have decoded := congrArg decodeNatAtom equal
  simpa using decoded

/-- One character as a compact, surface-safe decimal code. -/
def charAtom (value : Char) : Atom := natAtom value.toNat

def decodeCharAtom (atom : Atom) : Option Char :=
  Char.ofNat <$> decodeNatAtom atom

@[simp] theorem decodeCharAtom_charAtom (value : Char) :
    decodeCharAtom (charAtom value) = some value := by
  simp [decodeCharAtom, charAtom]

private def charNilTag : String := "mm-char-nil"
private def charConsTag : String := "mm-char-cons"

private def charListAtom : List Char → Atom
  | [] => .expression [.symbol charNilTag]
  | head :: tail =>
      .expression [.symbol charConsTag, charAtom head, charListAtom tail]

private def decodeCharListAtom : Atom → Option (List Char)
  | .expression [.symbol tag] =>
      if tag = charNilTag then some [] else none
  | .expression [.symbol tag, encodedHead, encodedTail] =>
      if tag = charConsTag then do
        let head ← decodeCharAtom encodedHead
        let tail ← decodeCharListAtom encodedTail
        pure (head :: tail)
      else
        none
  | _ => none
termination_by atom => sizeOf atom

@[simp] private theorem decodeCharListAtom_charListAtom (values : List Char) :
    decodeCharListAtom (charListAtom values) = some values := by
  induction values with
  | nil => simp [charListAtom, decodeCharListAtom, charNilTag]
  | cons head tail ih =>
      simp [charListAtom, decodeCharListAtom, charConsTag, ih]

/-- Arbitrary Metamath text as an ordered expression of character codes.
This is intentionally independent of quoting and escaping conventions. -/
def stringAtom (value : String) : Atom :=
  .expression [.symbol stringTag, charListAtom value.toList]

@[simp] private theorem isGroundAtom_charListAtom (values : List Char) :
    isGroundAtom (charListAtom values) = true := by
  induction values with
  | nil =>
      simp [charListAtom, isGroundAtom, isGroundAtom.isGroundList]
  | cons head tail induction =>
      simp [charListAtom, charAtom, natAtom, isGroundAtom,
        isGroundAtom.isGroundList, induction]

@[simp] theorem isGroundAtom_stringAtom (value : String) :
    isGroundAtom (stringAtom value) = true := by
  simp [stringAtom, isGroundAtom, isGroundAtom.isGroundList]

def decodeStringAtom : Atom → Option String
  | .expression [.symbol tag, encodedChars] =>
      if tag = stringTag then
        String.ofList <$> decodeCharListAtom encodedChars
      else
        none
  | _ => none

@[simp] theorem decodeStringAtom_stringAtom (value : String) :
    decodeStringAtom (stringAtom value) = some value := by
  unfold decodeStringAtom stringAtom
  simp only [stringTag, ↓reduceIte]
  rw [decodeCharListAtom_charListAtom]
  simp

theorem stringAtom_injective : Function.Injective stringAtom := by
  intro left right equal
  have decoded := congrArg decodeStringAtom equal
  simpa using decoded

/-! ## Runtime symbols and formulas -/

/-- Constant and variable occurrences remain distinct even when their source
names are equal. -/
def runtimeSymAtom : Metamath.Verify.Sym → Atom
  | Metamath.Verify.Sym.const name =>
      .expression [.symbol constTag, stringAtom name]
  | Metamath.Verify.Sym.var name =>
      .expression [.symbol variableTag, stringAtom name]

def decodeRuntimeSymAtom : Atom → Option Metamath.Verify.Sym
  | .expression [.symbol tag, encodedName] =>
      if tag = constTag then
        Metamath.Verify.Sym.const <$> decodeStringAtom encodedName
      else if tag = variableTag then
        Metamath.Verify.Sym.var <$> decodeStringAtom encodedName
      else
        none
  | _ => none

@[simp] theorem decodeRuntimeSymAtom_runtimeSymAtom
    (symbol : Metamath.Verify.Sym) :
    decodeRuntimeSymAtom (runtimeSymAtom symbol) = some symbol := by
  cases symbol <;>
    simp [decodeRuntimeSymAtom, runtimeSymAtom, constTag, variableTag]

theorem runtimeSymAtom_injective : Function.Injective runtimeSymAtom := by
  intro left right equal
  have decoded := congrArg decodeRuntimeSymAtom equal
  simpa using decoded

/-! ## Bounded-arity structured values -/

def nilTag : String := "mm-nil"
def consTag : String := "mm-cons"

/-- Recursive list data keeps every MM2 expression at bounded arity.  This
matters for long Metamath formulas and avoids relying on a target parser's
maximum flat expression arity. -/
def listAtom {Source : Type} (encode : Source → Atom) : List Source → Atom
  | [] => .expression [.symbol nilTag]
  | head :: tail =>
      .expression [.symbol consTag, encode head, listAtom encode tail]

def decodeListAtom {Source : Type} (decode : Atom → Option Source) :
    Atom → Option (List Source)
  | .expression [.symbol tag] =>
      if tag = nilTag then some [] else none
  | .expression [.symbol tag, encodedHead, encodedTail] =>
      if tag = consTag then do
        let head ← decode encodedHead
        let tail ← decodeListAtom decode encodedTail
        pure (head :: tail)
      else
        none
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeListAtom_listAtom {Source : Type}
    (encode : Source → Atom) (decode : Atom → Option Source)
    (leftInverse : ∀ value, decode (encode value) = some value)
    (values : List Source) :
    decodeListAtom decode (listAtom encode values) = some values := by
  induction values with
  | nil => simp [listAtom, decodeListAtom, nilTag]
  | cons head tail ih =>
      simp [listAtom, decodeListAtom, consTag, leftInverse, ih]

theorem listAtom_injective {Source : Type}
    (encode : Source → Atom) (decode : Atom → Option Source)
    (leftInverse : ∀ value, decode (encode value) = some value) :
    Function.Injective (listAtom encode) := by
  intro left right equal
  have decoded := congrArg (decodeListAtom decode) equal
  simpa [decodeListAtom_listAtom encode decode leftInverse] using decoded

def stringPairAtom (pair : String × String) : Atom :=
  .expression [.symbol "mm-pair", stringAtom pair.1, stringAtom pair.2]

def decodeStringPairAtom : Atom → Option (String × String)
  | .expression [.symbol tag, encodedLeft, encodedRight] =>
      if tag = "mm-pair" then do
        let left ← decodeStringAtom encodedLeft
        let right ← decodeStringAtom encodedRight
        pure (left, right)
      else
        none
  | _ => none

@[simp] theorem decodeStringPairAtom_stringPairAtom
    (pair : String × String) :
    decodeStringPairAtom (stringPairAtom pair) = some pair := by
  cases pair
  simp [decodeStringPairAtom, stringPairAtom]

def formulaAtom (formula : ConstantHeadedFormula) : Atom :=
  .expression
    [.symbol "mm-formula", stringAtom formula.typecode,
      listAtom runtimeSymAtom formula.body]

def decodeFormulaAtom : Atom → Option ConstantHeadedFormula
  | .expression [.symbol tag, encodedTypecode, encodedBody] =>
      if tag = "mm-formula" then do
        let typecode ← decodeStringAtom encodedTypecode
        let body ← decodeListAtom decodeRuntimeSymAtom encodedBody
        pure { typecode, body }
      else
        none
  | _ => none

@[simp] theorem decodeFormulaAtom_formulaAtom
    (formula : ConstantHeadedFormula) :
    decodeFormulaAtom (formulaAtom formula) = some formula := by
  cases formula
  simp [decodeFormulaAtom, formulaAtom]

def hypothesisAtom : HypothesisView → Atom
  | .floating label typecode variableName =>
      .expression
        [.symbol "mm-floating", stringAtom label, stringAtom typecode,
          stringAtom variableName]
  | .essential label formula =>
      .expression
        [.symbol "mm-essential", stringAtom label, formulaAtom formula]

def decodeHypothesisAtom : Atom → Option HypothesisView
  | .expression
      [.symbol tag, encodedLabel, encodedTypecode, encodedVariable] =>
      if tag = "mm-floating" then do
        let label ← decodeStringAtom encodedLabel
        let typecode ← decodeStringAtom encodedTypecode
        let variableName ← decodeStringAtom encodedVariable
        pure (.floating label typecode variableName)
      else
        none
  | .expression [.symbol tag, encodedLabel, encodedFormula] =>
      if tag = "mm-essential" then do
        let label ← decodeStringAtom encodedLabel
        let formula ← decodeFormulaAtom encodedFormula
        pure (.essential label formula)
      else
        none
  | _ => none

@[simp] theorem decodeHypothesisAtom_hypothesisAtom
    (hypothesis : HypothesisView) :
    decodeHypothesisAtom (hypothesisAtom hypothesis) = some hypothesis := by
  cases hypothesis <;>
    simp [decodeHypothesisAtom, hypothesisAtom]

def sourceFrameAtom (frame : SourceFrame) : Atom :=
  .expression
    [.symbol "mm-frame",
      listAtom stringPairAtom frame.distinctVariables,
      listAtom stringAtom frame.hypothesisLabels]

def decodeSourceFrameAtom : Atom → Option SourceFrame
  | .expression [.symbol tag, encodedDistinct, encodedHypotheses] =>
      if tag = "mm-frame" then do
        let distinctVariables ←
          decodeListAtom decodeStringPairAtom encodedDistinct
        let hypothesisLabels ← decodeListAtom decodeStringAtom encodedHypotheses
        pure { distinctVariables, hypothesisLabels }
      else
        none
  | _ => none

@[simp] theorem decodeSourceFrameAtom_sourceFrameAtom (frame : SourceFrame) :
    decodeSourceFrameAtom (sourceFrameAtom frame) = some frame := by
  cases frame
  simp [decodeSourceFrameAtom, sourceFrameAtom]

def sourceAssertionAtom (assertion : SourceAssertion) : Atom :=
  .expression
    [.symbol "mm-assertion", stringAtom assertion.label,
      formulaAtom assertion.formula, sourceFrameAtom assertion.frame,
      listAtom hypothesisAtom assertion.hypotheses]

def decodeSourceAssertionAtom : Atom → Option SourceAssertion
  | .expression
      [.symbol tag, encodedLabel, encodedFormula, encodedFrame,
        encodedHypotheses] =>
      if tag = "mm-assertion" then do
        let label ← decodeStringAtom encodedLabel
        let formula ← decodeFormulaAtom encodedFormula
        let frame ← decodeSourceFrameAtom encodedFrame
        let hypotheses ← decodeListAtom decodeHypothesisAtom encodedHypotheses
        pure { label, formula, frame, hypotheses }
      else
        none
  | _ => none

@[simp] theorem decodeSourceAssertionAtom_sourceAssertionAtom
    (assertion : SourceAssertion) :
    decodeSourceAssertionAtom (sourceAssertionAtom assertion) =
      some assertion := by
  cases assertion
  simp [decodeSourceAssertionAtom, sourceAssertionAtom]

/-! ## Shared runtime lookup rows

These constructors are part of the MM2 data representation rather than the
verifier transformation.  The source-data transformation uses them to prepare
inert assertion rows, and the generic verifier publishes those exact rows only
after the corresponding theorem proof succeeds. -/

/-- Direct lookup data for an active Metamath hypothesis. -/
def hypothesisLookupRow (scopeOwner : Atom)
    (hypothesis : HypothesisView) : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", scopeOwner,
      stringAtom hypothesis.label, formulaAtom hypothesis.formula]

def hypothesisLookupRows (scopeOwner : Atom)
    (state : SourceState) : List Atom :=
  state.activeHypotheses.map (hypothesisLookupRow scopeOwner)

def assertionHeaderRow (scopeOwner : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) : Atom :=
  .expression
    [.symbol "mm-assertion-header", scopeOwner, natAtom assertionPosition,
      stringAtom assertion.label, natAtom assertion.hypotheses.length]

def assertionHypothesisRow (scopeOwner : Atom) (assertion : SourceAssertion)
    (hypothesisPosition : Nat) (hypothesis : HypothesisView) : Atom :=
  .expression
    [.symbol "mm-assertion-hypothesis", scopeOwner,
      stringAtom assertion.label, natAtom hypothesisPosition,
      hypothesisAtom hypothesis]

def assertionHypothesisRows (scopeOwner : Atom)
    (assertion : SourceAssertion) : List Atom :=
  assertion.hypotheses.mapIdx fun position hypothesis =>
    assertionHypothesisRow scopeOwner assertion position hypothesis

def assertionHypothesisSuccessorRow (scopeOwner : Atom)
    (assertion : SourceAssertion) (position : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
      stringAtom assertion.label, natAtom position, natAtom (position + 1)]

def assertionHypothesisSuccessorRows (scopeOwner : Atom)
    (assertion : SourceAssertion) : List Atom :=
  (List.range assertion.hypotheses.length).map fun position =>
    assertionHypothesisSuccessorRow scopeOwner assertion position

/-- One source-owned callee disjoint-variable obligation. -/
def assertionDVPairRow (scopeOwner : Atom) (assertion : SourceAssertion)
    (pairPosition : Nat) (pair : String × String) : Atom :=
  .expression
    [.symbol "mm-assertion-dv-pair", scopeOwner,
      stringAtom assertion.label, natAtom pairPosition,
      stringAtom pair.1, stringAtom pair.2]

def assertionDVPairRows (scopeOwner : Atom)
    (assertion : SourceAssertion) : List Atom :=
  assertion.frame.distinctVariables.mapIdx fun position pair =>
    assertionDVPairRow scopeOwner assertion position pair

def assertionDVSuccessorRows (scopeOwner : Atom)
    (assertion : SourceAssertion) : List Atom :=
  (List.range assertion.frame.distinctVariables.length).map fun position =>
    .expression
      [.symbol "mm-assertion-dv-successor", scopeOwner,
        stringAtom assertion.label, natAtom position, natAtom (position + 1)]

def assertionDVHeaderRow (scopeOwner : Atom)
    (assertion : SourceAssertion) : Atom :=
  .expression
    [.symbol "mm-assertion-dv-header", scopeOwner,
      stringAtom assertion.label,
      natAtom assertion.frame.distinctVariables.length]

/-- The full source conclusion remains data.  The generic target machine
applies the dynamically collected substitution; no assertion-shaped rule is
generated. -/
def assertionResultRow (scopeOwner : Atom)
    (assertion : SourceAssertion) : Atom :=
  .expression
    [.symbol "mm-assertion-result", scopeOwner,
      stringAtom assertion.label, stringAtom assertion.formula.typecode,
      listAtom runtimeSymAtom assertion.formula.body]

def assertionExecutionRowsFor (scopeOwner : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) : List Atom :=
  [assertionHeaderRow scopeOwner assertionPosition assertion] ++
    assertionHypothesisRows scopeOwner assertion ++
    assertionHypothesisSuccessorRows scopeOwner assertion ++
    [assertionDVHeaderRow scopeOwner assertion] ++
    assertionDVPairRows scopeOwner assertion ++
    assertionDVSuccessorRows scopeOwner assertion ++
    [assertionResultRow scopeOwner assertion]

theorem sourceAssertionAtom_injective :
    Function.Injective sourceAssertionAtom := by
  intro left right equal
  have decoded := congrArg decodeSourceAssertionAtom equal
  simpa using decoded

def scopeBoundaryAtom (boundary : ScopeBoundary) : Atom :=
  .expression
    [.symbol "mm-scope-boundary", natAtom boundary.activeVariableLength,
      natAtom boundary.activeHypothesisLength,
      natAtom boundary.activeDistinctLength]

/-! ## Indexed rows: sequences represented faithfully in a set -/

/-- One row of an ordered family.  `family` and `owner` identify the table;
`position` is semantic data, not an enumeration accident. -/
def indexedRow (family : String) (owner : Atom)
    (position : Nat) (payload : Atom) : Atom :=
  .expression
    [.symbol "mm-row", stringAtom family, owner, natAtom position, payload]

/-- Recover one row only from the named family and owner.  The family and
owner checks prevent a successful payload decode from crossing table or scope
boundaries. -/
def decodeIndexedRow (family : String) (owner : Atom) :
    Atom → Option (Nat × Atom)
  | .expression
      [.symbol tag, encodedFamily, actualOwner, encodedPosition, payload] =>
      if tag = "mm-row" && encodedFamily = stringAtom family &&
          actualOwner = owner then do
        let position ← decodeNatAtom encodedPosition
        pure (position, payload)
      else
        none
  | _ => none

@[simp] theorem decodeIndexedRow_indexedRow
    (family : String) (owner payload : Atom) (position : Nat) :
    decodeIndexedRow family owner
      (indexedRow family owner position payload) = some (position, payload) := by
  simp [decodeIndexedRow, indexedRow]

/-- Decode one assertion-table row without consulting any external database. -/
def decodeAssertionRow (owner : Atom) (row : Atom) :
    Option (Nat × SourceAssertion) := do
  let (position, payload) ← decodeIndexedRow "assertion" owner row
  let assertion ← decodeSourceAssertionAtom payload
  pure (position, assertion)

@[simp] theorem decodeAssertionRow_indexedRow
    (owner : Atom) (position : Nat) (assertion : SourceAssertion) :
    decodeAssertionRow owner
        (indexedRow "assertion" owner position
          (sourceAssertionAtom assertion)) =
      some (position, assertion) := by
  simp [decodeAssertionRow]

/-- Encode a sequence as rows.  The payload encoder is supplied by the source
presentation; the row construction does not inspect files, digests, or guest
names. -/
def indexedRows {Source : Type} (family : String) (owner : Atom)
    (encode : Source → Atom) (values : List Source) : List Atom :=
  values.mapIdx fun position value =>
    indexedRow family owner position (encode value)

/-- One input occurrence together with its explicit successor position.
MM2 need not parse or increment a decimal counter in order to advance. -/
def linkedRow (family : String) (owner : Atom)
    (position nextPosition : Nat) (payload : Atom) : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom family, owner,
      natAtom position, natAtom nextPosition, payload]

/-- Encode a sequence as linked rows.  Computing successor positions is a
representation transformation; it does not inspect or validate the payload. -/
def linkedRows {Source : Type} (family : String) (owner : Atom)
    (encode : Source → Atom) (values : List Source) : List Atom :=
  values.mapIdx fun position value =>
    linkedRow family owner position (position + 1) (encode value)

/-- Explicit successor data for a finite index interval `[0, count]`. -/
def indexSuccessorRows (owner : Atom) (count : Nat) : List Atom :=
  (List.range count).map fun position =>
    .expression
      [.symbol "mm-index-successor", owner,
        natAtom position, natAtom (position + 1)]

@[simp] theorem indexedRows_length {Source : Type}
    (family : String) (owner : Atom) (encode : Source → Atom)
    (values : List Source) :
    (indexedRows family owner encode values).length = values.length := by
  simp [indexedRows]

@[simp] theorem linkedRows_length {Source : Type}
    (family : String) (owner : Atom) (encode : Source → Atom)
    (values : List Source) :
    (linkedRows family owner encode values).length = values.length := by
  simp [linkedRows]

@[simp] theorem indexSuccessorRows_length (owner : Atom) (count : Nat) :
    (indexSuccessorRows owner count).length = count := by
  simp [indexSuccessorRows]

theorem mem_indexedRows_iff {Source : Type}
    (family : String) (owner : Atom) (encode : Source → Atom)
    (values : List Source) (row : Atom) :
    row ∈ indexedRows family owner encode values ↔
      ∃ (position : Nat) (inBounds : position < values.length),
        indexedRow family owner position (encode values[position]) = row := by
  simp [indexedRows]

theorem mem_linkedRows_iff {Source : Type}
    (family : String) (owner : Atom) (encode : Source → Atom)
    (values : List Source) (row : Atom) :
    row ∈ linkedRows family owner encode values ↔
      ∃ (position : Nat) (inBounds : position < values.length),
        linkedRow family owner position (position + 1)
          (encode values[position]) = row := by
  simp [linkedRows]

theorem mem_indexSuccessorRows_iff (owner : Atom) (count : Nat)
    (row : Atom) :
    row ∈ indexSuccessorRows owner count ↔
      ∃ position < count,
        (.expression
          [.symbol "mm-index-successor", owner,
            natAtom position, natAtom (position + 1)] : Atom) = row := by
  simp [indexSuccessorRows]

/-- Different positions remain different rows, independently of whether their
payloads are equal. -/
theorem indexedRow_position_injective
    (family : String) (owner payload : Atom) :
    Function.Injective fun position =>
      indexedRow family owner position payload := by
  intro left right equal
  simp [indexedRow] at equal
  exact natAtom_injective equal

/-- An indexed list has no row collisions when its payload encoding is
injective. -/
theorem indexedRows_nodup {Source : Type}
    (family : String) (owner : Atom) (encode : Source → Atom)
    (values : List Source) :
    (indexedRows family owner encode values).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro first second rowsEqual
  apply Fin.ext
  simp [indexedRows, indexedRow] at rowsEqual
  exact natAtom_injective rowsEqual.1

/-! ## The authored inference presentation as MM2 data -/

private def wireSymbolTag : String := "mm-wire-symbol"
private def wireNaturalTag : String := "mm-wire-natural"
private def wireListTag : String := "mm-wire-list"
private def wireNilTag : String := "mm-wire-nil"
private def wireConsTag : String := "mm-wire-cons"

mutual
  /-- Lossless target data for the canonical inference-presentation wire
  carrier.  Lists are cons encoded, so no source rule or formula can exceed
  MORK's bounded flat-expression arity. -/
  def wireTermAtom : WireTerm → Atom
    | .symbol name =>
        .expression [.symbol wireSymbolTag, stringAtom name]
    | .natural value =>
        .expression [.symbol wireNaturalTag, natAtom value]
    | .list items =>
        .expression [.symbol wireListTag, wireTermsAtom items]

  def wireTermsAtom : List WireTerm → Atom
    | [] => .expression [.symbol wireNilTag]
    | head :: tail =>
        .expression [.symbol wireConsTag, wireTermAtom head,
          wireTermsAtom tail]
end

mutual
  /-- Fail-closed inverse for `wireTermAtom`. -/
  def decodeWireTermAtom : Atom → Option WireTerm
    | .expression [.symbol tag, encodedName] =>
        if tag = wireSymbolTag then
          WireTerm.symbol <$> decodeStringAtom encodedName
        else if tag = wireNaturalTag then
          WireTerm.natural <$> decodeNatAtom encodedName
        else if tag = wireListTag then
          WireTerm.list <$> decodeWireTermsAtom encodedName
        else
          none
    | _ => none

  def decodeWireTermsAtom : Atom → Option (List WireTerm)
    | .expression [.symbol tag] =>
        if tag = wireNilTag then some [] else none
    | .expression [.symbol tag, encodedHead, encodedTail] =>
        if tag = wireConsTag then do
          let head ← decodeWireTermAtom encodedHead
          let tail ← decodeWireTermsAtom encodedTail
          pure (head :: tail)
        else
          none
    | _ => none
end

mutual
  @[simp] theorem decodeWireTermAtom_wireTermAtom
      (term : WireTerm) :
      decodeWireTermAtom (wireTermAtom term) = some term := by
    cases term with
    | symbol name =>
        simp [wireTermAtom, decodeWireTermAtom, wireSymbolTag]
    | natural value =>
        simp [wireTermAtom, decodeWireTermAtom, wireSymbolTag,
          wireNaturalTag]
    | list items =>
        simp [wireTermAtom, decodeWireTermAtom, wireSymbolTag,
          wireNaturalTag, wireListTag,
          decodeWireTermsAtom_wireTermsAtom items]

  @[simp] theorem decodeWireTermsAtom_wireTermsAtom
      (terms : List WireTerm) :
      decodeWireTermsAtom (wireTermsAtom terms) = some terms := by
    cases terms with
    | nil =>
        simp [wireTermsAtom, decodeWireTermsAtom, wireNilTag]
    | cons head tail =>
        simp [wireTermsAtom, decodeWireTermsAtom, wireConsTag,
          decodeWireTermAtom_wireTermAtom head,
          decodeWireTermsAtom_wireTermsAtom tail]
end

theorem wireTermAtom_injective : Function.Injective wireTermAtom := by
  intro left right equal
  have decoded := congrArg decodeWireTermAtom equal
  simpa using decoded

/-- Exact target data for the checker-facing projection of the supplied
authored presentation.  This includes constructor signatures, judgments,
ordered rules, side conditions, and conversion identity. -/
def runtimePresentationAtom
    (presentation : RuntimePresentation) : Atom :=
  wireTermAtom (encodeRuntimePresentation presentation)

def decodeRuntimePresentationAtom
    (atom : Atom) : Option RuntimePresentation := do
  let wire ← decodeWireTermAtom atom
  decodeRuntimePresentation wire

@[simp] theorem decodeRuntimePresentationAtom_runtimePresentationAtom
    (presentation : RuntimePresentation) :
    decodeRuntimePresentationAtom (runtimePresentationAtom presentation) =
      some presentation := by
  simp [decodeRuntimePresentationAtom, runtimePresentationAtom]

theorem runtimePresentationAtom_injective :
    Function.Injective runtimePresentationAtom := by
  intro left right equal
  have decoded := congrArg decodeRuntimePresentationAtom equal
  simpa using decoded

/-! ## The source database as MM2 tables -/

/-- Each component of the admitted source state becomes an independently
named MM2 table.  The database is data; no declaration or assertion becomes
generated executable code. -/
structure SourceStateTables where
  declaredConstants : List Atom
  declaredVariables : List Atom
  activeVariables : List Atom
  variableTypecodes : List Atom
  usedLabels : List Atom
  activeHypotheses : List Atom
  activeDistinctVariables : List Atom
  assertions : List Atom
  scopes : List Atom
  pendingBlockCompletions : Atom
deriving DecidableEq

/-- Transform the actual source-state value into MM2 table rows.  `owner`
names an admitted source scope and is supplied by the hosting boundary. -/
def sourceStateTables (owner : Atom) (state : SourceState) :
    SourceStateTables where
  declaredConstants :=
    indexedRows "declared-constant" owner stringAtom state.declaredConstants
  declaredVariables :=
    indexedRows "declared-variable" owner stringAtom state.declaredVariables
  activeVariables :=
    indexedRows "active-variable" owner stringAtom state.activeVariables
  variableTypecodes :=
    indexedRows "variable-typecode" owner stringPairAtom state.variableTypecodes
  usedLabels :=
    indexedRows "used-label" owner stringAtom state.usedLabels
  activeHypotheses :=
    indexedRows "active-hypothesis" owner hypothesisAtom state.activeHypotheses
  activeDistinctVariables :=
    indexedRows "active-dv" owner stringPairAtom state.activeDistinctVariables
  assertions :=
    indexedRows "assertion" owner sourceAssertionAtom state.assertions
  scopes :=
    indexedRows "scope" owner scopeBoundaryAtom state.scopes
  pendingBlockCompletions :=
    indexedRow "pending-block-completions" owner 0
      (natAtom state.pendingBlockCompletions)

/-- Ordinary MM2 input facts obtained by concatenating the named tables. -/
def SourceStateTables.rows (tables : SourceStateTables) : List Atom :=
  tables.declaredConstants ++ tables.declaredVariables ++
    tables.activeVariables ++ tables.variableTypecodes ++
    tables.usedLabels ++ tables.activeHypotheses ++
    tables.activeDistinctVariables ++ tables.assertions ++ tables.scopes ++
    [tables.pendingBlockCompletions]

def sourceStateRows (owner : Atom) (state : SourceState) : List Atom :=
  (sourceStateTables owner state).rows

/-- The target-owned ordinary-MM2 renderer is a separate stage from source
encoding.  Its partiality records the actual MORK surface capability. -/
def renderSourceStateData? (owner : Atom) (state : SourceState) :
    Option String :=
  renderProgram? (sourceStateRows owner state)

/-! ## Admitted source presentation input -/

/-- The concrete source input to the MM-to-MM2 transformation.  It contains
the actual source state and the actual source-generated inference
presentation, together with their existing admission facts.  No filename,
digest, or implementation callback occurs in this input. -/
structure AdmittedSourceScope where
  state : SourceState
  stateValid : sourceStateValid state = true
  presentation : SourcePresentation
  presentationGenerated :
    presentationOfSourcePrefix? state.toSourcePrefix = some presentation

/-- The target-side data artifact produced before executable MM2 rules are
added.  Keeping the presentation packet separate from state rows lets later
proof-machine rules query one immutable calculus packet and ordinary indexed
database data. -/
structure ScopeDataArtifact where
  presentation : Atom
  stateRows : List Atom
deriving DecidableEq

def ScopeDataArtifact.rows (artifact : ScopeDataArtifact) : List Atom :=
  artifact.presentation :: artifact.stateRows

def decodeRuntimePresentationFact (owner : Atom) :
    Atom → Option RuntimePresentation
  | .expression [.symbol tag, actualOwner, encodedPresentation] =>
      if tag = "mm-runtime-presentation" && actualOwner = owner then
        decodeRuntimePresentationAtom encodedPresentation
      else
        none
  | _ => none

/-- Transform the supplied admitted Metamath presentation and source state
into MM2 data.  This is the representation stage of the compiler, not yet the
proof-execution stage. -/
def transformScopeData (owner : Atom)
    (source : AdmittedSourceScope) : ScopeDataArtifact where
  presentation :=
    .expression
      [.symbol "mm-runtime-presentation", owner,
        runtimePresentationAtom
          (RuntimePresentation.ofPresentation source.presentation)]
  stateRows := sourceStateRows owner source.state

/-- The presentation packet in a transformed artifact decodes to the exact
checker-facing projection of the supplied authored presentation. -/
theorem transformScopeData_presentation_exact
    (owner : Atom) (source : AdmittedSourceScope) :
    decodeRuntimePresentationFact owner
        (transformScopeData owner source).presentation =
      some (RuntimePresentation.ofPresentation source.presentation) := by
  simp [transformScopeData, decodeRuntimePresentationFact]

/-- The transformation carries the actual supplied source state, field by
field, rather than reconstructing it from an external file. -/
@[simp] theorem transformScopeData_stateRows
    (owner : Atom) (source : AdmittedSourceScope) :
    (transformScopeData owner source).stateRows =
      sourceStateRows owner source.state :=
  rfl

/-- A checker-facing presentation mutation cannot disappear behind the same
compiled presentation atom. -/
theorem transformScopeData_presentation_sensitive
    (owner : Atom) (left right : AdmittedSourceScope)
    (changed :
      RuntimePresentation.ofPresentation left.presentation ≠
        RuntimePresentation.ofPresentation right.presentation) :
    (transformScopeData owner left).presentation ≠
      (transformScopeData owner right).presentation := by
  intro equal
  apply changed
  apply runtimePresentationAtom_injective
  simpa [transformScopeData] using equal

def renderScopeData? (owner : Atom) (source : AdmittedSourceScope) :
    Option String :=
  renderProgram? (transformScopeData owner source).rows

/-! ## Dynamic normal and compressed proof input -/

/-- Proof evidence remains a dynamic input to the residual MM2 verifier. -/
inductive ProofInput where
  | normal
      (theoremLabel : String)
      (formula : ConstantHeadedFormula)
      (proofLabels : List String)
  | compressed
      (theoremLabel : String)
      (formula : ConstantHeadedFormula)
      (explicitHeaderLabels : List String)
      (bodyWords : List (List UInt8))
deriving DecidableEq

/-- Recover dynamic proof input from the source-owned theorem action. -/
def StateAction.proofInput? : StateAction → Option ProofInput
  | .localAction _ => none
  | .theoremNormal label formula proofLabels =>
      some (.normal label formula proofLabels)
  | .theoremCompressed label formula header body =>
      some (.compressed label formula header body)

def uint8Atom (byte : UInt8) : Atom := natAtom byte.toNat

def compressedWordAtom (word : List UInt8) : Atom :=
  listAtom uint8Atom word

structure ProofInputTables where
  descriptor : Atom
  normalSteps : List Atom
  compressedHeaderLabels : List Atom
  compressedBodyWords : List Atom
  indexSuccessors : List Atom
  programEnd : Atom
  initialControl : Atom
deriving DecidableEq

/-- Encode either proof syntax without checking it.  Normal labels and
compressed header/body occurrences retain their source positions. -/
def proofInputTables (scopeOwner proofOwner : Atom) : ProofInput → ProofInputTables
  | .normal theoremLabel formula proofLabels =>
      { descriptor :=
          .expression
            [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "normal",
              stringAtom theoremLabel, formulaAtom formula]
        normalSteps :=
          linkedRows "normal-proof-label" proofOwner stringAtom proofLabels
        compressedHeaderLabels := []
        compressedBodyWords := []
        indexSuccessors := indexSuccessorRows proofOwner proofLabels.length
        programEnd :=
          .expression
            [.symbol "mm-proof-end", proofOwner, natAtom proofLabels.length]
        initialControl :=
          .expression
            [.symbol "mm-normal-control", scopeOwner, proofOwner,
              natAtom 0, natAtom 0] }
  | .compressed theoremLabel formula header body =>
      { descriptor :=
          .expression
            [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "compressed",
              stringAtom theoremLabel, formulaAtom formula]
        normalSteps := []
        compressedHeaderLabels :=
          indexedRows "compressed-header-label" proofOwner stringAtom header
        compressedBodyWords :=
          indexedRows "compressed-body-word" proofOwner compressedWordAtom body
        indexSuccessors := indexSuccessorRows proofOwner body.length
        programEnd :=
          .expression
            [.symbol "mm-proof-end", proofOwner, natAtom body.length]
        initialControl :=
          .expression
            [.symbol "mm-compressed-control", scopeOwner, proofOwner,
              natAtom 0, natAtom 0] }

def ProofInputTables.rows (tables : ProofInputTables) : List Atom :=
  tables.descriptor ::
    (tables.normalSteps ++ tables.compressedHeaderLabels ++
      tables.compressedBodyWords ++ tables.indexSuccessors ++
      [tables.programEnd, tables.initialControl])

def proofInputRows (scopeOwner proofOwner : Atom)
    (proof : ProofInput) : List Atom :=
  (proofInputTables scopeOwner proofOwner proof).rows

/-- Independent source-indexed classification of the ordinary MM2 data for
one normal proof invocation.  Every occurrence and successor is tied to its
exact submitted position. -/
def NormalProofInputRowFrom (scopeOwner proofOwner : Atom)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (proofLabels : List String) (row : Atom) : Prop :=
  (.expression
    [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "normal",
      stringAtom theoremLabel, formulaAtom formula] : Atom) = row ∨
  (∃ (position : Nat) (inBounds : position < proofLabels.length),
    linkedRow "normal-proof-label" proofOwner position (position + 1)
      (stringAtom proofLabels[position]) = row) ∨
  (∃ position < proofLabels.length,
    (.expression
      [.symbol "mm-index-successor", proofOwner,
        natAtom position, natAtom (position + 1)] : Atom) = row) ∨
  (.expression
    [.symbol "mm-proof-end", proofOwner,
      natAtom proofLabels.length] : Atom) = row ∨
  (.expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner,
      natAtom 0, natAtom 0] : Atom) = row

/-- Normal proof serialization is exact: target-row membership is equivalent
to one source-indexed input occurrence or boundary fact. -/
theorem mem_normalProofInputRows_iff (scopeOwner proofOwner : Atom)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (proofLabels : List String) (row : Atom) :
    row ∈ proofInputRows scopeOwner proofOwner
        (.normal theoremLabel formula proofLabels) ↔
      NormalProofInputRowFrom scopeOwner proofOwner theoremLabel formula
        proofLabels row := by
  simp [proofInputRows, proofInputTables, ProofInputTables.rows,
    NormalProofInputRowFrom, mem_linkedRows_iff,
    mem_indexSuccessorRows_iff, eq_comm]

def renderProofInput? (scopeOwner proofOwner : Atom) (proof : ProofInput) :
    Option String :=
  renderProgram? (proofInputRows scopeOwner proofOwner proof)

@[simp] theorem normal_label_row_count
    (proofOwner : Atom) (theoremLabel : String)
    (formula : ConstantHeadedFormula) (proofLabels : List String) :
    (proofInputTables (stringAtom "scope") proofOwner
      (.normal theoremLabel formula proofLabels)).normalSteps.length =
      proofLabels.length := by
  simp [proofInputTables]

@[simp] theorem compressed_header_row_count
    (proofOwner : Atom) (theoremLabel : String)
    (formula : ConstantHeadedFormula) (header : List String)
    (body : List (List UInt8)) :
    (proofInputTables (stringAtom "scope") proofOwner
      (.compressed theoremLabel formula header body)).compressedHeaderLabels.length =
      header.length := by
  simp [proofInputTables]

@[simp] theorem compressed_body_row_count
    (proofOwner : Atom) (theoremLabel : String)
    (formula : ConstantHeadedFormula) (header : List String)
    (body : List (List UInt8)) :
    (proofInputTables (stringAtom "scope") proofOwner
      (.compressed theoremLabel formula header body)).compressedBodyWords.length =
      body.length := by
  simp [proofInputTables]

/-- The encoder does not confuse the two proof syntaxes even when both carry
empty streams. -/
theorem normal_and_compressed_descriptors_differ
    (proofOwner : Atom) (theoremLabel : String)
    (formula : ConstantHeadedFormula) :
    (proofInputTables (stringAtom "scope") proofOwner
      (.normal theoremLabel formula [])).descriptor ≠
    (proofInputTables (stringAtom "scope") proofOwner
      (.compressed theoremLabel formula [] [])).descriptor := by
  simp [proofInputTables]

/-! ## Positive and negative representation controls -/

def repeatedLabels : List String := ["ax", "ax"]
def proofOwner : Atom := stringAtom "proof-1"

/-- The indexed representation retains two occurrences of the same label. -/
theorem indexed_repetition_has_two_rows :
    (indexedRows "proof-label" proofOwner stringAtom repeatedLabels).toFinset.card = 2 := by
  rw [List.toFinset_card_of_nodup (indexedRows_nodup _ _ _ _)]
  rfl

/-- The tempting unindexed set representation loses that occurrence. -/
theorem unindexed_repetition_collapses :
    (repeatedLabels.map stringAtom).toFinset.card = 1 := by
  simp [repeatedLabels]

/-- Changing source semantics changes the generated table value even when the
scope owner is held fixed.  The transformation is not a source-identity
dispatcher. -/
theorem constant_declaration_changes_tables :
    sourceStateTables (stringAtom "scope") initialState ≠
      sourceStateTables (stringAtom "scope") oneConstantState := by
  intro equal
  have declaredEqual := congrArg SourceStateTables.declaredConstants equal
  simp [sourceStateTables, oneConstantState, initialState, indexedRows] at declaredEqual

/-- A source token containing MM2 delimiters and whitespace still round-trips
because it is data, never pasted into the surface grammar. -/
theorem delimiter_token_roundtrip :
    decodeStringAtom (stringAtom "($x) a b;\n") =
      some "($x) a b;\n" := by
  simp

#print axioms natAtom_injective
#print axioms stringAtom_injective
#print axioms runtimeSymAtom_injective
#print axioms indexedRows_nodup
#print axioms mem_linkedRows_iff
#print axioms mem_indexSuccessorRows_iff
#print axioms mem_normalProofInputRows_iff
#print axioms indexed_repetition_has_two_rows
#print axioms unindexed_repetition_collapses
#print axioms constant_declaration_changes_tables
#print axioms normal_and_compressed_descriptors_differ
#print axioms delimiter_token_roundtrip

end Mettapedia.Languages.Metamath.MM2DataEncoding
