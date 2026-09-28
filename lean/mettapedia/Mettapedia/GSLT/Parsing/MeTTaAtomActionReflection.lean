import Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler

/-!
# Reflected checking for compiled MeTTa construction actions

Grammar-specific action tables are ordinary first-order data.  This module
checks that data against the existing action wire without reconstructing a
dependent route for every production.  The checker verifies the complete
slot context, the result sort, every primitive signature, and exact agreement
with a separately derived expected row.

The table carries the established encoded `CompiledAction`; it does not add a
second action language.  A generator may be untrusted: an accepted candidate
decodes, is structurally well sorted, and is byte-for-byte the expected action.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.MeTTaAtomActionReflection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.Parsing.MeTTaAtomConstruction
open Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler
open Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-- Every typed construction value has a host-atom encoding.  The public
`atom` sort may therefore receive an encoded auxiliary value, while no
auxiliary sort may be recovered from an arbitrary atom without decoding it.
This is the explicit representation law behind the compiler's erased
`string`, `integer`, and `expression` operations. -/
def representationEmbeds : Kind → Kind → Bool
  | _, .atom => true
  | source, target => decide (source = target)

/-- The input signature of a generic primitive at a requested result sort.
`cons` has two admitted result sorts because the same physical operation
represents both an auxiliary sequence and a host application. -/
def primitiveInputs? : Primitive → Kind → Option (List Kind)
  | .symbol, .atom => some [.text]
  | .cons, .atoms => some [.atom, .atoms]
  | .cons, .atom => some [.atom, .atoms]
  | .append, .atoms => some [.atoms, .atoms]
  | .append, .atom => some [.atoms, .atoms]
  | .textAppend, .text => some [.text, .text]
  | .textAppend, .atom => some [.text, .text]
  | .integerValue, .integer => some [.integerLexeme]
  | .integerValue, .atom => some [.integerLexeme]
  | .rationalComponents, .atoms => some [.rationalLexeme]
  | .rationalComponents, .atom => some [.rationalLexeme]
  | _, _ => none

mutual
  /-- A compiled action has the requested result sort in the declared slot
  context.  Constants are checked by the same sort-indexed decoder used at
  execution; no spelling-based fallback is available. -/
  inductive WellTyped (context : List Kind) : Kind → CompiledAction → Prop where
    | slot {actual output index}
        (exact : context[index]? = some actual)
        (embeds : representationEmbeds actual output = true) :
        WellTyped context output (.slot index)
    | constant {output value}
        (decodes : (decodeValue output value).isSome = true) :
        WellTyped context output (.constant value)
    | apply {head arguments}
        (typed : WellTypedArguments context
          (List.replicate arguments.length .atom) arguments) :
        WellTyped context .atom (.apply head arguments)
    | primitive {operation arguments output inputs}
        (signature : primitiveInputs? operation output = some inputs)
        (typed : WellTypedArguments context inputs arguments) :
        WellTyped context output (.primitive operation arguments)

  /-- Ordered argument checking retains arity and every individual sort. -/
  inductive WellTypedArguments (context : List Kind) :
      List Kind → List CompiledAction → Prop where
    | nil : WellTypedArguments context [] []
    | cons {kind kinds action actions}
        (head : WellTyped context kind action)
        (tail : WellTypedArguments context kinds actions) :
        WellTypedArguments context (kind :: kinds) (action :: actions)
end

mutual
  /-- Executable Boolean reflection of `WellTyped`. -/
  def checkAction (context : List Kind) (output : Kind) : CompiledAction → Bool
    | .slot index =>
        match context[index]? with
        | some actual => representationEmbeds actual output
        | none => false
    | .constant value => (decodeValue output value).isSome
    | .apply _ arguments =>
        match output with
        | .atom => checkArguments context
            (List.replicate arguments.length .atom) arguments
        | _ => false
    | .primitive operation arguments =>
        match primitiveInputs? operation output with
        | some inputs => checkArguments context inputs arguments
        | none => false

  def checkArguments (context : List Kind) :
      List Kind → List CompiledAction → Bool
    | [], [] => true
    | kind :: kinds, action :: actions =>
        checkAction context kind action &&
          checkArguments context kinds actions
    | [], _ :: _ | _ :: _, [] => false
end

mutual
  theorem checkAction_sound {context : List Kind} {output : Kind}
      {action : CompiledAction} (accepted : checkAction context output action = true) :
      WellTyped context output action := by
    match action with
    | .slot index =>
        cases exact : context[index]? with
        | none => simp [checkAction, exact] at accepted
        | some actual =>
            exact .slot exact (by simpa [checkAction, exact] using accepted)
    | .constant value =>
        exact .constant accepted
    | .apply head arguments =>
        cases output <;> simp [checkAction] at accepted
        exact .apply (checkArguments_sound accepted)
    | .primitive operation arguments =>
        cases signature : primitiveInputs? operation output with
        | none => simp [checkAction, signature] at accepted
        | some inputs =>
            exact .primitive signature (checkArguments_sound
              (by simpa [checkAction, signature] using accepted))
    termination_by structural action

  theorem checkArguments_sound {context : List Kind} {kinds : List Kind}
      {actions : List CompiledAction}
      (accepted : checkArguments context kinds actions = true) :
      WellTypedArguments context kinds actions := by
    match kinds, actions with
    | [], [] => exact .nil
    | kind :: kinds, action :: actions =>
        have both : checkAction context kind action = true ∧
            checkArguments context kinds actions = true := by
          simpa [checkArguments] using accepted
        exact .cons (checkAction_sound both.1) (checkArguments_sound both.2)
    | [], _ :: _ => simp [checkArguments] at accepted
    | _ :: _, [] => simp [checkArguments] at accepted
    termination_by structural actions
end

mutual
  theorem checkAction_complete {context : List Kind} {output : Kind}
      {action : CompiledAction} (typed : WellTyped context output action) :
      checkAction context output action = true := by
    cases typed with
    | slot exact embeds => simp [checkAction, exact, embeds]
    | constant decodes => exact decodes
    | apply typed => simpa [checkAction] using checkArguments_complete typed
    | primitive signature typed =>
        simpa [checkAction, signature] using checkArguments_complete typed

  theorem checkArguments_complete {context : List Kind} {kinds : List Kind}
      {actions : List CompiledAction}
      (typed : WellTypedArguments context kinds actions) :
      checkArguments context kinds actions = true := by
    cases typed with
    | nil => rfl
    | cons head tail =>
        simp [checkArguments, checkAction_complete head,
          checkArguments_complete tail]
end

theorem checkAction_iff {context : List Kind} {output : Kind}
    {action : CompiledAction} :
    checkAction context output action = true ↔ WellTyped context output action := by
  exact ⟨checkAction_sound, checkAction_complete⟩

/-- First-order row format shared by kernel reflection, the build-time
checker, and the native table exporter.  Production identifiers are numeric;
labels remain diagnostic data outside this trusted core. -/
structure Row where
  production : Nat
  context : List Kind
  output : Kind
  actionCode : Atom
  deriving DecidableEq, Repr

/-! ## Compact first-order wire

Kinds and production identifiers use numeric codes.  The only nested payload
is the already established action encoding.  This format is intentionally
straightforward to reproduce in a build-time C or MeTTa checker. -/

def encodeNat (value : Nat) : Atom :=
  .grounded (.int (Int.ofNat value))

def decodeNat : Atom → Option Nat
  | .grounded (.int value) =>
      if value < 0 then none else some value.toNat
  | _ => none

theorem decodeNat_encodeNat (value : Nat) :
    decodeNat (encodeNat value) = some value := by
  simp [decodeNat, encodeNat]

def encodeKind : Kind → Atom
  | .atom => encodeNat 0
  | .atoms => encodeNat 1
  | .text => encodeNat 2
  | .integer => encodeNat 3
  | .integerLexeme => encodeNat 4
  | .rationalLexeme => encodeNat 5

def decodeKind : Atom → Option Kind
  | .grounded (.int 0) => some .atom
  | .grounded (.int 1) => some .atoms
  | .grounded (.int 2) => some .text
  | .grounded (.int 3) => some .integer
  | .grounded (.int 4) => some .integerLexeme
  | .grounded (.int 5) => some .rationalLexeme
  | _ => none

theorem decodeKind_encodeKind (kind : Kind) :
    decodeKind (encodeKind kind) = some kind := by cases kind <;> rfl

def encodeKinds (kinds : List Kind) : Atom :=
  .expression (kinds.map encodeKind)

def decodeKinds : Atom → Option (List Kind)
  | .expression codes => codes.mapM decodeKind
  | _ => none

private theorem mapM_decodeKind_encodeKind (kinds : List Kind) :
    (kinds.map encodeKind).mapM decodeKind = some kinds := by
  induction kinds with
  | nil => rfl
  | cons kind kinds ih => simp [decodeKind_encodeKind, ih]

theorem decodeKinds_encodeKinds (kinds : List Kind) :
    decodeKinds (encodeKinds kinds) = some kinds := by
  exact mapM_decodeKind_encodeKind kinds

def Row.encode (row : Row) : Atom :=
  .expression [.symbol "reflected-action-row-v1",
    encodeNat row.production, encodeKinds row.context,
    encodeKind row.output, row.actionCode]

def Row.decode : Atom → Option Row
  | .expression [.symbol "reflected-action-row-v1", production, context,
      output, actionCode] => do
      let production ← decodeNat production
      let context ← decodeKinds context
      let output ← decodeKind output
      some ⟨production, context, output, actionCode⟩
  | _ => none

theorem Row.decode_encode (row : Row) : Row.decode row.encode = some row := by
  simp [Row.decode, Row.encode, decodeNat_encodeNat, decodeKinds_encodeKinds,
    decodeKind_encodeKind]

def encodeTable (rows : List Row) : Atom :=
  .expression (.symbol "reflected-action-table-v1" :: rows.map Row.encode)

def decodeTable : Atom → Option (List Row)
  | .expression (.symbol "reflected-action-table-v1" :: rows) =>
      rows.mapM Row.decode
  | _ => none

private theorem mapM_decodeRow_encodeRow (rows : List Row) :
    (rows.map Row.encode).mapM Row.decode = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [Row.decode_encode, ih]

theorem decodeTable_encodeTable (rows : List Row) :
    decodeTable (encodeTable rows) = some rows := by
  exact mapM_decodeRow_encodeRow rows

/-- Decode and sort-check one independently supplied row. -/
def Row.checkWellTyped (row : Row) : Bool :=
  match decodeAction row.actionCode with
  | some action => checkAction row.context row.output action
  | none => false

/-- A candidate row is admitted only when its identity, complete type, and
encoded action agree with the independently derived expectation. -/
def Row.checkAgainst (expected candidate : Row) : Bool :=
  decide (candidate.production = expected.production) &&
  decide (candidate.context = expected.context) &&
  decide (candidate.output = expected.output) &&
  decide (candidate.actionCode = expected.actionCode) &&
  candidate.checkWellTyped

/-- Logical content of one accepted reflected row. -/
def Row.Admitted (expected candidate : Row) : Prop :=
  candidate = expected ∧
    ∃ action, decodeAction candidate.actionCode = some action ∧
      WellTyped candidate.context candidate.output action

theorem Row.checkAgainst_sound {expected candidate : Row}
    (accepted : candidate.checkAgainst expected = true) :
    Row.Admitted expected candidate := by
  simp only [Row.checkAgainst, Bool.and_eq_true] at accepted
  rcases accepted with ⟨⟨⟨⟨production, context⟩, output⟩, code⟩, typed⟩
  have production' : candidate.production = expected.production :=
    (of_decide_eq_true production).symm
  have context' : candidate.context = expected.context :=
    (of_decide_eq_true context).symm
  have output' : candidate.output = expected.output :=
    (of_decide_eq_true output).symm
  have code' : candidate.actionCode = expected.actionCode :=
    (of_decide_eq_true code).symm
  have exact : candidate = expected := by
    cases candidate
    cases expected
    simp_all
  subst candidate
  cases decoded : decodeAction expected.actionCode with
  | none => simp [Row.checkWellTyped, decoded] at typed
  | some action =>
      exact ⟨rfl, action, decoded,
        checkAction_sound (by simpa [Row.checkWellTyped, decoded] using typed)⟩

/-- Pairwise whole-table checking rejects missing, duplicate, reordered, or
extra rows in addition to checking each action. -/
def checkTable : List Row → List Row → Bool
  | [], [] => true
  | expected :: expectedRest, candidate :: candidateRest =>
      candidate.checkAgainst expected && checkTable expectedRest candidateRest
  | [], _ :: _ | _ :: _, [] => false

theorem checkTable_sound {expected candidate : List Row}
    (accepted : checkTable expected candidate = true) :
    List.Forall₂ Row.Admitted expected candidate := by
  induction expected generalizing candidate with
  | nil =>
      cases candidate with
      | nil => exact .nil
      | cons _ _ => simp [checkTable] at accepted
  | cons expectedHead expectedRest ih =>
      cases candidate with
      | nil => simp [checkTable] at accepted
      | cons candidateHead candidateRest =>
          have both : candidateHead.checkAgainst expectedHead = true ∧
              checkTable expectedRest candidateRest = true := by
            simpa [checkTable] using accepted
          exact .cons (Row.checkAgainst_sound both.1) (ih both.2)

theorem admittedTable_exact {expected candidate : List Row}
    (admitted : List.Forall₂ Row.Admitted expected candidate) :
    candidate = expected := by
  induction admitted with
  | nil => rfl
  | cons row rest ih => simp [row.1, ih]

theorem checkTable_exact {expected candidate : List Row}
    (accepted : checkTable expected candidate = true) : candidate = expected :=
  admittedTable_exact (checkTable_sound accepted)

/-- Construct the expected first-order row from an already typed route. -/
def expectedRow {context : List Kind} {output : Kind}
    (production : Nat) (route : MeTTaAtomConstruction.Action context output) : Row :=
  { production := production
    context := context
    output := output
    actionCode := encodeAction (compile route) }

/-! ## Positive and negative controls -/

private def symbolRow : Row := expectedRow 0 symbolAction

example : symbolRow.checkWellTyped = true := by decide +kernel

example : checkTable [symbolRow] [symbolRow] = true := by decide +kernel

private def wrongSlotRow : Row :=
  { symbolRow with actionCode := encodeAction (.slot 1) }

/-- A decodable action with an out-of-range slot is rejected. -/
example : checkTable [symbolRow] [wrongSlotRow] = false := by decide +kernel

private def wrongProductionRow : Row :=
  { symbolRow with production := 1 }

/-- A well-typed action at the wrong production occurrence is rejected. -/
example : checkTable [symbolRow] [wrongProductionRow] = false := by decide +kernel

/-- Truncating the candidate inventory is rejected. -/
example : checkTable [symbolRow] [] = false := rfl

#print axioms checkAction_iff
#print axioms Row.checkAgainst_sound
#print axioms checkTable_sound
#print axioms checkTable_exact

end Mettapedia.GSLT.Parsing.MeTTaAtomActionReflection
