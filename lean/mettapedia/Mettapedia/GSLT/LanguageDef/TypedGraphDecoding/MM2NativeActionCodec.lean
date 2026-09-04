import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics
import Mathlib.Tactic

/-!
# Exact MM2 native-action codec

The neural decoder does not emit the constructors of the reader grammar.
It emits a preorder code consisting of a program arity, list arities,
task-local symbol references, and canonical variable references.  This module
models that code directly and connects successful action decoding to the
existing MM2 `LanguageDef` parser and lowering theorem.

The parsing relation is deliberately independent of the encoder.  The
round-trip theorem is therefore a real adequacy result rather than a
definition compared with itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics

/-- Lossless, bounded-tree content of the runtime's native S-expression
presentation.  Symbol and variable indices are resolved by an episode-local
context. -/
inductive NativeAtom where
  | reference (index : Nat)
  | var (index : Nat)
  | expression (children : List NativeAtom)
  deriving Repr

/-- The four non-special action families in `native-sexpr-preorder-v1`. -/
inductive Action where
  | program (formCount : Nat)
  | list (arity : Nat)
  | reference (index : Nat)
  | var (index : Nat)
  deriving Repr, DecidableEq

mutual
  /-- Canonical preorder encoding of one native atom. -/
  def encodeAtom : NativeAtom → List Action
    | .reference index => [.reference index]
    | .var index => [.var index]
    | .expression children => .list children.length :: encodeAtoms children

  /-- Concatenated preorder encodings of ordered siblings. -/
  def encodeAtoms : List NativeAtom → List Action
    | [] => []
    | atom :: atoms => encodeAtom atom ++ encodeAtoms atoms
end

/-- Canonical trace of one nonempty program.  The nonemptiness condition is a
separate admission judgment because the runtime action family can represent
`program 0` even though the registered synthesis root forbids it. -/
def encodeProgram (program : List NativeAtom) : List Action :=
  .program program.length :: encodeAtoms program

mutual
  /-- Independent relational decoder for one atom and its unconsumed suffix. -/
  inductive ParsesAtom :
      List Action → NativeAtom → List Action → Prop where
    | reference (index : Nat) (rest : List Action) :
        ParsesAtom (.reference index :: rest) (.reference index) rest
    | var (index : Nat) (rest : List Action) :
        ParsesAtom (.var index :: rest) (.var index) rest
    | expression {arity : Nat} {input rest : List Action}
        {children : List NativeAtom}
        (childrenParse : ParsesAtoms arity input children rest) :
        ParsesAtom (.list arity :: input) (.expression children) rest

  /-- Parse exactly `count` ordered siblings. -/
  inductive ParsesAtoms :
      Nat → List Action → List NativeAtom → List Action → Prop where
    | nil (rest : List Action) : ParsesAtoms 0 rest [] rest
    | cons {count : Nat} {input middle rest : List Action}
        {atom : NativeAtom} {atoms : List NativeAtom}
        (headParse : ParsesAtom input atom middle)
        (tailParse : ParsesAtoms count middle atoms rest) :
        ParsesAtoms (count + 1) input (atom :: atoms) rest
end

/-- A complete action trace has one program root, exactly the declared number
of forms, and no trailing actions. -/
inductive ParsesProgram : List Action → List NativeAtom → Prop where
  | intro {count : Nat} {input : List Action} {program : List NativeAtom}
      (forms : ParsesAtoms count input program []) :
      ParsesProgram (.program count :: input) program

mutual
  /-- The independently defined atom parser accepts the encoder's trace with
  any following action suffix left untouched. -/
  theorem encodeAtom_parses (atom : NativeAtom) (rest : List Action) :
      ParsesAtom (encodeAtom atom ++ rest) atom rest := by
    cases atom with
    | reference index => exact .reference index rest
    | var index => exact .var index rest
    | expression children =>
        simp only [encodeAtom, List.cons_append]
        exact .expression (encodeAtoms_parses children rest)

  /-- The sibling parser consumes exactly the concatenated sibling encoding. -/
  theorem encodeAtoms_parses (atoms : List NativeAtom) (rest : List Action) :
      ParsesAtoms atoms.length (encodeAtoms atoms ++ rest) atoms rest := by
    cases atoms with
    | nil =>
        simp only [List.length_nil, encodeAtoms, List.nil_append]
        exact .nil rest
    | cons atom atoms =>
        simp only [List.length_cons, encodeAtoms, List.append_assoc]
        exact .cons
          (encodeAtom_parses atom (encodeAtoms atoms ++ rest))
          (encodeAtoms_parses atoms rest)
end

/-- Every canonical program encoding decodes to exactly that native program. -/
theorem encodeProgram_parses (program : List NativeAtom) :
    ParsesProgram (encodeProgram program) program := by
  unfold encodeProgram
  exact .intro (by simpa using encodeAtoms_parses program [])

mutual
  /-- Atom parsing is deterministic, including the unconsumed suffix. -/
  theorem ParsesAtom.deterministic
      {input : List Action} {first second : NativeAtom}
      {firstRest secondRest : List Action}
      (firstParse : ParsesAtom input first firstRest)
      (secondParse : ParsesAtom input second secondRest) :
      first = second ∧ firstRest = secondRest := by
    cases firstParse with
    | reference index rest =>
        cases secondParse
        exact ⟨rfl, rfl⟩
    | var index rest =>
        cases secondParse
        exact ⟨rfl, rfl⟩
    | expression firstChildren =>
        cases secondParse with
        | expression secondChildren =>
            have exactChildren :=
              ParsesAtoms.deterministic firstChildren secondChildren
            exact ⟨congrArg NativeAtom.expression exactChildren.1,
              exactChildren.2⟩

  /-- Fixed-count sibling parsing is deterministic. -/
  theorem ParsesAtoms.deterministic
      {count : Nat} {input : List Action}
      {first second : List NativeAtom}
      {firstRest secondRest : List Action}
      (firstParse : ParsesAtoms count input first firstRest)
      (secondParse : ParsesAtoms count input second secondRest) :
      first = second ∧ firstRest = secondRest := by
    cases firstParse with
    | nil rest =>
        cases secondParse
        exact ⟨rfl, rfl⟩
    | cons firstHead firstTail =>
        cases secondParse with
        | cons secondHead secondTail =>
            rcases ParsesAtom.deterministic firstHead secondHead with
              ⟨rfl, rfl⟩
            rcases ParsesAtoms.deterministic firstTail secondTail with
              ⟨rfl, rfl⟩
            exact ⟨rfl, rfl⟩
end

/-- Complete native action decoding has at most one result. -/
theorem ParsesProgram.deterministic
    {actions : List Action} {first second : List NativeAtom}
    (firstParse : ParsesProgram actions first)
    (secondParse : ParsesProgram actions second) :
    first = second := by
  cases firstParse with
  | intro firstForms =>
      cases secondParse with
      | intro secondForms =>
          exact (ParsesAtoms.deterministic firstForms secondForms).1

mutual
  /-- Relational parsing consumes exactly the canonical encoder image of the
  parsed atom.  This is the converse direction of `encodeAtom_parses`. -/
  theorem ParsesAtom.input_eq_encode_append
      {input rest : List Action} {atom : NativeAtom}
      (parsed : ParsesAtom input atom rest) :
      input = encodeAtom atom ++ rest := by
    cases parsed with
    | reference _ _ => rfl
    | var _ _ => rfl
    | expression childrenParse =>
        rcases childrenParse.count_and_input_eq_encode_append with
          ⟨rfl, rfl⟩
        rfl

  /-- Fixed-count sibling parsing determines both the count and the complete
  consumed encoder segment. -/
  theorem ParsesAtoms.count_and_input_eq_encode_append
      {count : Nat} {input rest : List Action} {atoms : List NativeAtom}
      (parsed : ParsesAtoms count input atoms rest) :
      count = atoms.length ∧ input = encodeAtoms atoms ++ rest := by
    cases parsed with
    | nil _ => exact ⟨rfl, rfl⟩
    | cons headParse tailParse =>
        rw [headParse.input_eq_encode_append]
        rcases tailParse.count_and_input_eq_encode_append with ⟨rfl, rfl⟩
        exact ⟨rfl, by simp [encodeAtoms, List.append_assoc]⟩
end

/-- A complete relational parse is definitionally the canonical native
program encoding of its unique tree. -/
theorem ParsesProgram.actions_eq_encodeProgram
    {actions : List Action} {program : List NativeAtom}
    (parsed : ParsesProgram actions program) :
    actions = encodeProgram program := by
  cases parsed with
  | intro forms =>
      rcases forms.count_and_input_eq_encode_append with ⟨rfl, exactInput⟩
      simp [encodeProgram, exactInput]

mutual
  /-- Resolve one native atom through the authenticated task-local symbol
  table.  Canonical variable indices use the same `vN` payload convention as
  the runtime after its leading `$` reader marker is removed. -/
  def realizeAtom (symbols : List String) : NativeAtom → Option Atom
    | .reference index => symbols[index]?.map Atom.symbol
    | .var index => some (.var s!"v{index}")
    | .expression children => do
        pure (.expression (← realizeAtoms symbols children))

  /-- Resolve ordered siblings, failing if any symbol reference is absent. -/
  def realizeAtoms (symbols : List String) :
      List NativeAtom → Option (List Atom)
    | [] => some []
    | atom :: atoms => do
        pure ((← realizeAtom symbols atom) ::
          (← realizeAtoms symbols atoms))
end

/-- A complete source-bound witness connecting one native action trace to the
MM2 parser generated from the authored reader `LanguageDef`. -/
structure GSLTAdmission (symbols : List String) (actions : List Action) where
  nativeProgram : List NativeAtom
  atoms : List Atom
  actionDecode : ParsesProgram actions nativeProgram
  symbolResolution : realizeAtoms symbols nativeProgram = some atoms
  readerSafe : programSafe atoms = true
  rendered : String
  renderedExact : renderProgram? atoms = some rendered
  parsed : ParsedProgram (stringScalars rendered)
  parsedAtomsExact : parsed.atoms = atoms

/-- Successful native decoding, symbol resolution, and the ordinary MM2
representation gate produce a generated-parser derivation whose lowering is
the exact resolved atom program. -/
theorem admits_through_mm2_gslt
    {actions : List Action} (symbols : List String)
    (nativeProgram : List NativeAtom)
    (actionDecode : ParsesProgram actions nativeProgram)
    (atoms : List Atom)
    (symbolResolution : realizeAtoms symbols nativeProgram = some atoms)
    (readerSafe : programSafe atoms = true) :
    Nonempty (GSLTAdmission symbols actions) := by
  have renderedExact :
      renderProgram? atoms = some (ordinaryProgramString atoms) := by
    simp [renderProgram?, readerSafe]
  obtain ⟨parsed, parsedAtomsExact⟩ :=
    successful_render_has_exact_parser_lowering renderedExact
  exact ⟨{
    nativeProgram := nativeProgram
    atoms := atoms
    actionDecode := actionDecode
    symbolResolution := symbolResolution
    readerSafe := readerSafe
    rendered := ordinaryProgramString atoms
    renderedExact := renderedExact
    parsed := parsed
    parsedAtomsExact := parsedAtomsExact }⟩

private def fixtureSymbols : List String :=
  ["exec", "key", ",", "g", "7"]

private def fixtureNativeProgram : List NativeAtom :=
  [.expression
    [.reference 0, .reference 1,
      .expression [.reference 2],
      .expression [.reference 2,
        .expression [.reference 3, .reference 1,
          .var 0, .var 0, .reference 4]]]]

/-- Positive codec fixture: nested MM2 structure round-trips through the exact
native preorder action relation. -/
theorem fixture_native_trace_round_trips :
    ParsesProgram (encodeProgram fixtureNativeProgram) fixtureNativeProgram :=
  encodeProgram_parses fixtureNativeProgram

/-- Negative codec fixture: changing a list arity prevents the trace from
decoding as the original expression. -/
theorem wrong_arity_does_not_decode_fixture :
    ¬ ParsesProgram
      (.program 1 :: .list 2 :: .reference 0 :: .reference 1 :: [])
      [.expression [.reference 0]] := by
  intro parsed
  cases parsed with
  | intro forms =>
      cases forms with
      | cons head tail =>
          cases head with
          | expression children =>
              cases children with
              | cons firstChild remainingChildren =>
                  cases remainingChildren

/-- Negative source-binding fixture: an absent task-local reference fails
before any MM2 parser claim is available. -/
theorem absent_reference_fails_resolution :
    realizeAtom ["only"] (.reference 1) = none := by
  rfl

#print axioms encodeAtom_parses
#print axioms encodeAtoms_parses
#print axioms encodeProgram_parses
#print axioms ParsesAtom.deterministic
#print axioms ParsesAtoms.deterministic
#print axioms ParsesProgram.deterministic
#print axioms ParsesAtom.input_eq_encode_append
#print axioms ParsesAtoms.count_and_input_eq_encode_append
#print axioms ParsesProgram.actions_eq_encodeProgram
#print axioms admits_through_mm2_gslt
#print axioms fixture_native_trace_round_trips
#print axioms wrong_arity_does_not_decode_fixture
#print axioms absent_reference_fails_resolution

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec
