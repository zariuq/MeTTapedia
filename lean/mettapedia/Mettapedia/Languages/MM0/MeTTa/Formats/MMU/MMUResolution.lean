import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualProjection

/-!
# MMU public identities and captured name resolution

Public metadata retains the independently supplied specification entries.
Working maps contain only preceding declarations and lexical bindings. The
resolver source is quoted without restating any declaration or proof checker.

These laws cover constructor data and the quoted pure lookup operations.
String scanning, generic reader execution, full declaration resolution and
service submission require separate execution correspondence.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.MMUResolution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SpaceSemantics (Program)
open Eval
open Effects (State boolean)
open Kernel (SpecificationEntry)
open Store (natural)
open ListAccess (listValue optionValue)
open scoped ProgramQuotation

def resolverSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/mmu.metta"
    sha256 "6d826f18b5d5f1a014f0e32204d6f2b0e1ca501efd43d650f7c0e315e74b110c"

def program : Program := TextualExecution.program.append resolverSource.program

/-- Checker requests do not enter the input-stream dispatcher or the newly
introduced frontend functions. All other literal data and primitive heads
remain available to the checker. -/
def checkerHead (head : String) : Bool :=
  head != "eval" && head != "mm0:stream" &&
    !(head.startsWith "mm0:text:") && !(head.startsWith "mm0:mmu:")

/-- This finite check inspects every retained checker equation body. The
stream's dynamic evaluation is outside the start/submit/finish call graph. -/
theorem checker_bodies_within :
    MeTTa.program.equations.all (fun equation =>
      !checkerHead equation.head || codeWithin checkerHead equation.body) = true := by
  decide +kernel

theorem checker_program_closed : ProgramClosed checkerHead MeTTa.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp checker_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

theorem frontend_equations_fresh :
    (TextualExecution.textualSource.program.equations ++ resolverSource.program.equations).all
      (fun equation => !checkerHead equation.head) = true := by decide +kernel

theorem frontend_declarations_fresh :
    (TextualExecution.textualSource.program.declarations ++ resolverSource.program.declarations).all
      (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
            !checkerHead head
        | _ => true) = true := by decide +kernel

theorem program_eq_checker_append :
    program = MeTTa.program.append
      (TextualExecution.textualSource.program.append resolverSource.program) := by
  simp [program, TextualExecution.program, SpaceSemantics.Program.append, List.append_assoc]

/-- Equation and type-declaration freshness are earned from both quoted
frontend files; they are not assumptions about the executing checker. -/
theorem checker_program_agreement : ProgramAgreementOn checkerHead MeTTa.program program := by
  rw [program_eq_checker_append]
  apply appended_program_agreement
  · intro equation member
    have checked := List.all_eq_true.mp frontend_equations_fresh equation member
    cases result : checkerHead equation.head with
    | false => rfl
    | true => simp [result] at checked
  · intro name types member
    have checked := List.all_eq_true.mp frontend_declarations_fresh
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases result : checkerHead name with
    | false => rfl
    | true => simp [result] at checked

/-- Actual checker paths survive frontend loading. Captured environments may
hold arbitrary constructor values; only the code being executed is checked. -/
theorem checker_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin checkerHead code = true)
    (checked : PureReturns MeTTa.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement checker_program_closed checker_program_agreement ⟨supported, rfl⟩ checked

/-- MMU identifiers remain strings even when another reader would parse a
number, Boolean or constructor symbol with the same spelling. -/
def nameValue (name : String) : Atom := .grounded (.string name)

def decodeName : Atom → Option String
  | .grounded (.string name) => some name
  | _ => none

@[simp] theorem decodeName_nameValue (name : String) :
    decodeName (nameValue name) = some name := rfl

theorem decodeName_reflects (atom : Atom) (name : String)
    (decoded : decodeName atom = some name) : atom = nameValue name := by
  unfold decodeName at decoded
  split at decoded
  · have same := Option.some.inj decoded
    simpa [nameValue] using congrArg (fun value => Atom.grounded (.string value)) same
  · simp at decoded

theorem nameValue_injective : Function.Injective nameValue := by
  intro first second same
  simpa [nameValue] using same

/-- Numerical namespace IDs use the existing grounded natural codec. -/
def decodeNatural : Atom → Option Nat
  | .grounded (.int value) => if 0 ≤ value then some value.toNat else none
  | _ => none

@[simp] theorem decodeNatural_natural (index : Nat) :
    decodeNatural (natural index) = some index := by
  simp [decodeNatural, natural]

theorem decodeNatural_reflects (atom : Atom) (index : Nat)
    (decoded : decodeNatural atom = some index) : atom = natural index := by
  unfold decodeNatural at decoded
  split at decoded
  · rename_i value
    split at decoded
    · rename_i nonnegative
      have same : value.toNat = index := Option.some.inj decoded
      rw [← same]
      simp [natural, Int.toNat_of_nonneg nonnegative]
    · simp at decoded
  · simp at decoded

inductive Namespace where
  | sort | term | theorem
  deriving DecidableEq, Repr

inductive Kind where
  | sort | term | definition | axiomDecl | theoremDecl
  deriving DecidableEq, Repr

def kindValue : Kind → Atom
  | .sort => .symbol "MM0:MMUSort"
  | .term => .symbol "MM0:MMUTerm"
  | .definition => .symbol "MM0:MMUDefinition"
  | .axiomDecl => .symbol "MM0:MMUAxiom"
  | .theoremDecl => .symbol "MM0:MMUTheorem"

def decodeKind : Atom → Option Kind
  | .symbol "MM0:MMUSort" => some .sort
  | .symbol "MM0:MMUTerm" => some .term
  | .symbol "MM0:MMUDefinition" => some .definition
  | .symbol "MM0:MMUAxiom" => some .axiomDecl
  | .symbol "MM0:MMUTheorem" => some .theoremDecl
  | _ => none

@[simp] theorem decodeKind_kindValue (kind : Kind) :
    decodeKind (kindValue kind) = some kind := by cases kind <;> rfl

theorem decodeKind_reflects (atom : Atom) (kind : Kind)
    (decoded : decodeKind atom = some kind) : atom = kindValue kind := by
  unfold decodeKind at decoded
  split at decoded
  all_goals first
    | (have same := Option.some.inj decoded; subst kind; rfl)
    | simp at decoded

def Kind.namespace : Kind → Namespace
  | .sort => .sort
  | .term | .definition => .term
  | .axiomDecl | .theoremDecl => .theorem

def entryKind : SpecificationEntry → Kind
  | .sort .. => .sort
  | .term .. => .term
  | .definition .. => .definition
  | .axiomDecl .. => .axiomDecl
  | .theoremDecl .. => .theoremDecl

def entryIndex : SpecificationEntry → Nat
  | .sort index _ | .term index _ | .definition index _ _
  | .axiomDecl index _ | .theoremDecl index _ => index

/-- A public identity is attached to an existing specification entry. -/
structure PublicSlot where
  name : String
  specification : SpecificationEntry

/-- Decoding syntax does not admit the payload as a logical declaration. -/
structure PublicWire where
  name : String
  kind : Kind
  index : Nat
  payload : Atom
  deriving DecidableEq, Repr

def PublicSlot.wire (slot : PublicSlot) : PublicWire :=
  ⟨slot.name, entryKind slot.specification, entryIndex slot.specification,
    SpecificationMatching.entryValue slot.specification⟩

def publicWireValue (slot : PublicWire) : Atom :=
  .expression [.symbol "MM0:MMUPublic", nameValue slot.name,
    kindValue slot.kind, natural slot.index, slot.payload]

def decodePublicWire : Atom → Option PublicWire
  | .expression [.symbol "MM0:MMUPublic", name, kind, index, payload] => do
      let decodedName ← decodeName name
      let decodedKind ← decodeKind kind
      let decodedIndex ← decodeNatural index
      pure ⟨decodedName, decodedKind, decodedIndex, payload⟩
  | _ => none

@[simp] theorem decodePublicWire_publicWireValue (slot : PublicWire) :
    decodePublicWire (publicWireValue slot) = some slot := by
  cases slot
  simp [publicWireValue, decodePublicWire]

theorem decodePublicWire_reflects (atom : Atom) (slot : PublicWire)
    (decoded : decodePublicWire atom = some slot) : atom = publicWireValue slot := by
  unfold decodePublicWire at decoded
  split at decoded
  · rename_i name kind index payload
    obtain ⟨actualName, nameDecoded, afterName⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨actualKind, kindDecoded, afterKind⟩ := Option.bind_eq_some_iff.mp afterName
    obtain ⟨actualIndex, indexDecoded, output⟩ := Option.bind_eq_some_iff.mp afterKind
    have same : (⟨actualName, actualKind, actualIndex, payload⟩ : PublicWire) = slot := by
      simpa using output
    subst slot
    rw [decodeName_reflects name actualName nameDecoded,
      decodeKind_reflects kind actualKind kindDecoded,
      decodeNatural_reflects index actualIndex indexDecoded]
    rfl
  · simp at decoded

theorem decodePublicWire_iff (atom : Atom) (slot : PublicWire) :
    decodePublicWire atom = some slot ↔ atom = publicWireValue slot :=
  ⟨decodePublicWire_reflects atom slot, fun same => by simp [same]⟩

def publicSlotValue (slot : PublicSlot) : Atom := publicWireValue slot.wire

theorem publicSlotValue_injective : Function.Injective publicSlotValue := by
  intro first second same
  have wires : first.wire = second.wire := by
    have decoded := congrArg decodePublicWire same
    simpa [publicSlotValue] using decoded
  have names : first.name = second.name := congrArg PublicWire.name wires
  have payloads : SpecificationMatching.entryValue first.specification =
      SpecificationMatching.entryValue second.specification := congrArg PublicWire.payload wires
  have entries := SpecificationMatching.entryValue_injective payloads
  cases first; cases second
  simp_all

/-- Source names are supplied independently; the specification order is fixed. -/
def publicSlots (sourceName : SpecificationEntry → String) (entries : List SpecificationEntry) :
    List PublicSlot := entries.map fun entry => ⟨sourceName entry, entry⟩

def publicSlotsValue (slots : List PublicSlot) : Atom := listValue (slots.map publicSlotValue)

theorem publicSlots_preserve_specification (sourceName : SpecificationEntry → String)
    (entries : List SpecificationEntry) :
    (publicSlots sourceName entries).map PublicSlot.specification = entries := by
  simp [publicSlots, List.map_map, Function.comp_def]

theorem publicSlots_source_order (sourceName : SpecificationEntry → String)
    (entries : List SpecificationEntry) (position : Nat) :
    (publicSlots sourceName entries)[position]? =
      (entries[position]?).map (fun entry => ⟨sourceName entry, entry⟩) := by
  simp [publicSlots, List.getElem?_map]

theorem publicSlots_prefix (sourceName : SpecificationEntry → String)
    (entries : List SpecificationEntry) (limit : Nat) :
    (publicSlots sourceName entries).take limit = publicSlots sourceName (entries.take limit) := by
  simp [publicSlots]

/-- Exact payload identity recovers the existing typed entry, independently of
the displayed kind, namespace counter or proof-input spelling. -/
theorem public_payload_reflects (first second : PublicSlot)
    (same : first.wire.payload = second.wire.payload) :
    first.specification = second.specification :=
  SpecificationMatching.entryValue_injective same

def publicWiresValue (slots : List PublicWire) : Atom := listValue (slots.map publicWireValue)

def decodePublicWires : Atom → Option (List PublicWire)
  | .expression [.symbol "MM0:L", .expression entries] => entries.mapM decodePublicWire
  | _ => none

@[simp] theorem decodePublicWires_publicWiresValue (slots : List PublicWire) :
    decodePublicWires (publicWiresValue slots) = some slots := by
  change (slots.map publicWireValue).mapM decodePublicWire = some slots
  induction slots with
  | nil => rfl
  | cons first rest ih => simp [ih]

private theorem decodeWireEntries_reflects (entries : List Atom) (slots : List PublicWire)
    (decoded : entries.mapM decodePublicWire = some slots) : entries = slots.map publicWireValue := by
  induction entries generalizing slots with
  | nil =>
      have same : slots = [] := by simpa using decoded.symm
      simp [same]
  | cons first rest ih =>
      rw [List.mapM_cons] at decoded
      change (decodePublicWire first >>= fun head =>
        rest.mapM decodePublicWire >>= fun tail => pure (head :: tail)) = some slots at decoded
      obtain ⟨head, headDecoded, afterHead⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨tail, tailDecoded, output⟩ := Option.bind_eq_some_iff.mp afterHead
      have same : head :: tail = slots := by simpa using output
      subst slots
      rw [decodePublicWire_reflects first head headDecoded, ih tail tailDecoded]
      rfl

theorem decodePublicWires_reflects (atom : Atom) (slots : List PublicWire)
    (decoded : decodePublicWires atom = some slots) : atom = publicWiresValue slots := by
  unfold decodePublicWires at decoded
  split at decoded
  · rename_i entries
    rw [decodeWireEntries_reflects entries slots decoded]
    rfl
  · simp at decoded

structure Binding where
  key : Atom
  value : Atom
  deriving DecidableEq, Repr

def bindingValue (binding : Binding) : Atom :=
  .expression [.symbol "MM0:MMUBinding", binding.key, binding.value]

def decodeBinding : Atom → Option Binding
  | .expression [.symbol "MM0:MMUBinding", key, value] => some ⟨key, value⟩
  | _ => none

@[simp] theorem decodeBinding_bindingValue (binding : Binding) :
    decodeBinding (bindingValue binding) = some binding := by cases binding; rfl

theorem decodeBinding_reflects (atom : Atom) (binding : Binding)
    (decoded : decodeBinding atom = some binding) : atom = bindingValue binding := by
  unfold decodeBinding at decoded
  split at decoded
  · have same := Option.some.inj decoded
    subst binding
    rfl
  · simp at decoded

def bindingsValue (entries : List Binding) : Atom := listValue (entries.map bindingValue)

/-- Lookup chooses the first working-map binding, whose order is independent
of the pending public specification. Lexical extension prepends a binding. -/
def lookup : List Binding → Atom → Option Atom
  | [], _ => none
  | entry :: rest, key => if entry.key = key then some entry.value else lookup rest key

@[simp] theorem lookup_shadow (entries : List Binding) (key value : Atom) :
    lookup (⟨key, value⟩ :: entries) key = some value := by simp [lookup]

theorem lookup_other (entries : List Binding) (key other value : Atom) (different : key ≠ other) :
    lookup (⟨key, value⟩ :: entries) other = lookup entries other := by simp [lookup, different]

theorem lookup_append (first second : List Binding) (key : Atom) :
    lookup (first ++ second) key = (lookup first key).orElse (fun _ => lookup second key) := by
  induction first with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first.key = key <;> simp [lookup, same, ih]

theorem lookup_preceding {entries : List Binding} {key value : Atom}
    (found : lookup entries key = some value) :
    ∃ before after, entries = before ++ ⟨key, value⟩ :: after ∧
      ∀ earlier ∈ before, earlier.key ≠ key := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      by_cases same : entry.key = key
      · have answer : entry.value = value := by simpa [lookup, same] using found
        refine ⟨[], rest, ?_, by simp⟩
        cases entry
        simp_all
      · have tail : lookup rest key = some value := by simpa [lookup, same] using found
        obtain ⟨before, after, split, precedes⟩ := ih tail
        refine ⟨entry :: before, after, by simp [split], ?_⟩
        intro earlier member
        rcases List.mem_cons.mp member with equal | member
        · subst earlier; exact same
        · exact precedes earlier member

theorem lookup_prefix_cannot_see_future (preceding : List Binding) (key : Atom)
    (absent : ∀ binding ∈ preceding, binding.key ≠ key) : lookup preceding key = none := by
  induction preceding with
  | nil => rfl
  | cons first rest ih =>
      have different := absent first (by simp)
      simp [lookup, different, ih (fun entry member => absent entry (by simp [member]))]

theorem lookup_member {entries : List Binding} {key value : Atom}
    (found : lookup entries key = some value) : (⟨key, value⟩ : Binding) ∈ entries := by
  obtain ⟨before, after, split, _⟩ := lookup_preceding found
  rw [split]
  simp

theorem lookup_unique_complete {entries : List Binding}
    (unique : (entries.map Binding.key).Nodup) {key value : Atom}
    (present : (⟨key, value⟩ : Binding) ∈ entries) : lookup entries key = some value := by
  induction entries with
  | nil => simp at present
  | cons first rest ih =>
      have distinct : first.key ∉ rest.map Binding.key := (List.nodup_cons.mp unique).1
      have tailUnique : (rest.map Binding.key).Nodup := (List.nodup_cons.mp unique).2
      rcases List.mem_cons.mp present with same | member
      · subst first; simp [lookup]
      · have different : first.key ≠ key := by
          intro same
          apply distinct
          rw [same]
          exact List.mem_map.mpr ⟨⟨key, value⟩, member, rfl⟩
        simpa [lookup, different] using ih tailUnique member

/-- First and last source occurrences agree only under uniqueness. -/
theorem lookup_reverse_of_unique (entries : List Binding) (key : Atom)
    (unique : (entries.map Binding.key).Nodup) :
    lookup entries.reverse key = lookup entries key := by
  cases found : lookup entries key with
  | none =>
      cases backwards : lookup entries.reverse key with
      | none => rfl
      | some value =>
          have member : (⟨key, value⟩ : Binding) ∈ entries := by
            simpa using lookup_member backwards
          have existsValue := lookup_unique_complete unique member
          simp [found] at existsValue
  | some value =>
      apply lookup_unique_complete
      · simpa [List.map_reverse] using List.nodup_reverse.mpr unique
      · simpa using lookup_member found

def publicBinding (space : Namespace) (slot : PublicSlot) : Option Binding :=
  if (entryKind slot.specification).namespace = space then
    some ⟨nameValue slot.name, natural (entryIndex slot.specification)⟩ else none

/-- Only the submitted prefix populates a public working namespace. The full
pending metadata list is not inserted into this map. -/
def publicBindings (space : Namespace) (preceding : List PublicSlot) : List Binding :=
  (preceding.filterMap (publicBinding space)).reverse

theorem public_lookup_preceding (space : Namespace) (preceding : List PublicSlot)
    (name : String) (index : Nat)
    (found : lookup (publicBindings space preceding) (nameValue name) = some (natural index)) :
    ∃ slot ∈ preceding, (entryKind slot.specification).namespace = space ∧
      slot.name = name ∧ entryIndex slot.specification = index := by
  have member : (⟨nameValue name, natural index⟩ : Binding) ∈ preceding.filterMap (publicBinding space) := by
    simpa [publicBindings] using lookup_member found
  obtain ⟨slot, present, matched⟩ := List.mem_filterMap.mp member
  unfold publicBinding at matched
  split at matched
  · rename_i rightNamespace
    have same := Option.some.inj matched
    have named : slot.name = name := nameValue_injective (congrArg Binding.key same)
    have identity : entryIndex slot.specification = index :=
      Data.natural_injective (congrArg Binding.value same)
    exact ⟨slot, present, rightNamespace, named, identity⟩
  · simp at matched

theorem public_prefix_lookup_refused (space : Namespace) (slots : List PublicSlot)
    (limit : Nat) (name : String)
    (notPreceding : ∀ slot ∈ slots.take limit,
      (entryKind slot.specification).namespace = space → slot.name ≠ name) :
    lookup (publicBindings space (slots.take limit)) (nameValue name) = none := by
  apply lookup_prefix_cannot_see_future
  intro binding member same
  have inPrefix : binding ∈ (slots.take limit).filterMap (publicBinding space) := by
    simpa [publicBindings] using member
  obtain ⟨slot, present, matched⟩ := List.mem_filterMap.mp inPrefix
  unfold publicBinding at matched
  split at matched
  · rename_i rightNamespace
    have exactBinding := Option.some.inj matched
    have named : slot.name = name := nameValue_injective
      ((congrArg Binding.key exactBinding).trans same)
    exact notPreceding slot present rightNamespace named
  · simp at matched

/-- The resolver's fresh counter lies above every independently fixed public
identity in the corresponding namespace. It does not allocate declarations. -/
def publicCeiling (space : Namespace) : List PublicSlot → Nat
  | [] => 0
  | slot :: rest =>
      if (entryKind slot.specification).namespace = space then
        max (entryIndex slot.specification + 1) (publicCeiling space rest)
      else publicCeiling space rest

theorem publicCeiling_fresh (space : Namespace) (slots : List PublicSlot)
    (slot : PublicSlot) (present : slot ∈ slots)
    (sameNamespace : (entryKind slot.specification).namespace = space) :
    entryIndex slot.specification < publicCeiling space slots := by
  induction slots with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with same | member
      · subst first
        simp only [publicCeiling, sameNamespace, if_pos]
        exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
      · have earlier := ih member
        unfold publicCeiling
        split
        · exact Nat.lt_of_lt_of_le earlier (Nat.le_max_right _ _)
        · exact earlier

def bindVariable (entries : List Binding) (name : String) (index : Nat) : List Binding :=
  if name = "_" then entries else ⟨nameValue name, natural index⟩ :: entries

@[simp] theorem bindVariable_anonymous (entries : List Binding) (index : Nat) :
    bindVariable entries "_" index = entries := by simp [bindVariable]

theorem bindVariable_shadows (entries : List Binding) (name : String) (index : Nat)
    (named : name ≠ "_") :
    lookup (bindVariable entries name index) (nameValue name) = some (natural index) := by
  simp [bindVariable, named]

/-- The variable and bound-dependency maps are separate lexical histories.
A regular binder extends only the variable map. -/
structure Scope where
  variableBindings : List Binding
  boundBindings : List Binding
  deriving DecidableEq, Repr

def Scope.extend (scope : Scope) (name : String) (index : Nat) (isBound : Bool) : Scope :=
  ⟨bindVariable scope.variableBindings name index,
    if isBound then bindVariable scope.boundBindings name index else scope.boundBindings⟩

theorem regular_preserves_bound_lookup (scope : Scope) (name : String) (index : Nat) (key : Atom) :
    lookup (scope.extend name index false).boundBindings key = lookup scope.boundBindings key := rfl

theorem bound_extends_both_histories (scope : Scope) (name : String) (index : Nat)
    (named : name ≠ "_") :
    lookup (scope.extend name index true).variableBindings (nameValue name) = some (natural index) ∧
    lookup (scope.extend name index true).boundBindings (nameValue name) = some (natural index) := by
  constructor <;> exact bindVariable_shadows _ name index named

private def lookupEquation : SpaceSemantics.Equation :=
  resolverSource.program.equations[10]'(by decide)

private def lookupCases : SpaceSemantics.Cases :=
  match lookupEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def lookupEnvironment (entries : List Binding) (key : Atom) : Subst :=
  [("name", key), ("entries", .expression (entries.map bindingValue))]

private def lookupNonempty : Atom := (lookupCases[1]'(by decide)).2

private theorem lookup_unique :
    program.equations.filter (fun equation => equation.head == "mm0:mmu:lookup") =
      [lookupEquation] := by decide

private theorem lookup_formals : lookupEquation.arguments =
    [.expression [.symbol "MM0:L", .var "entries"], .var "name"] := by decide

private theorem lookup_shape : lookupEquation.body =
    .expression [.symbol "case", .var "entries",
      .expression (lookupCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem lookup_cases : lookupCases =
    [(.expression [], .symbol "None"),
      (.expression [.symbol "cons",
        .expression [.symbol "MM0:MMUBinding", .var "stored", .var "value"], .var "rest"],
        lookupNonempty), (.var "bad", .symbol "None")] := by decide

private theorem lookup_nonempty_shape : lookupNonempty =
    .expression [.symbol "if", .expression [.symbol "==", .var "stored", .var "name"],
      .expression [.symbol "Some", .var "value"],
      .expression [.symbol "mm0:mmu:lookup", .expression [.symbol "MM0:L", .var "rest"],
        .var "name"]] := by decide

private theorem lookup_clause (entries : List Binding) (key : Atom) :
    clauses program "mm0:mmu:lookup" [bindingsValue entries, key] =
      [.evaluate (lookupEnvironment entries key) lookupEquation.body] := by
  rw [clauses_use_only_the_named_equations, lookup_unique]
  simp [lookup_formals, bindingsValue, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, lookupEnvironment]

private theorem lookup_raw_call_returns (bindings : Subst) (state : State)
    (entries : List Binding) (key itemsArgument nameArgument answer : Atom)
    (capturedItems : applySubst bindings itemsArgument = bindingsValue entries)
    (capturedName : applySubst bindings nameArgument = key)
    (computed : PureReturns program (lookupEnvironment entries key) state lookupEquation.body state answer) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:lookup", itemsArgument, nameArgument]) state answer := by
  apply call_returns program bindings state state "mm0:mmu:lookup" _ answer (by decide) _ (by decide)
  apply raw_arguments_return program bindings state state "mm0:mmu:lookup" _ [] 0 answer
  · intro offset bounded
    have cases : offset = 0 ∨ offset = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases cases with rfl | rfl <;> decide
  · simpa [capturedItems, capturedName] using
      authored_function_arguments_return program bindings (lookupEnvironment entries key) state state
        "mm0:mmu:lookup" [bindingsValue entries, key] 2 lookupEquation.body answer
        (by decide) (by decide) (lookup_clause entries key) computed

private theorem lookup_body_returns (state : State) (entries : List Binding) (key : Atom) :
    PureReturns program (lookupEnvironment entries key) state lookupEquation.body state
      (optionValue (lookup entries key)) := by
  induction entries with
  | nil =>
      rw [lookup_shape]
      apply case_returns program (lookupEnvironment [] key) (lookupEnvironment [] key)
        state state state (.var "entries") (.expression []) (.symbol "None") _ _ lookupCases
        (read_cases_encoded _)
      · simpa [lookupEnvironment, applySubst, Subst.lookup] using
          variable_returns program (lookupEnvironment [] key) state "entries"
      · simp [lookup_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · exact symbol_returns program _ state "None"
  | cons first rest ih =>
      let outer := lookupEnvironment (first :: rest) key
      let bound : Subst := ("rest", .expression (rest.map bindingValue)) ::
        ("value", first.value) :: ("stored", first.key) :: outer
      rw [lookup_shape]
      apply case_returns program outer bound state state state (.var "entries")
        (.expression ((first :: rest).map bindingValue)) lookupNonempty _ _ lookupCases
        (read_cases_encoded _)
      · simpa [outer, lookupEnvironment, applySubst, Subst.lookup] using
          variable_returns program outer state "entries"
      · simp [lookup_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindingValue,
          bound, outer, lookupEnvironment]
      · rw [lookup_nonempty_shape]
        apply if_returns program bound state state state _
          (boolean (decide (first.key = key))) _ _ _
        · apply native_variable_call_returns program bound state state "==" ["stored", "name"] _
            (by decide) (by decide) _ (by decide)
          simp [StdLib.apply, bound, outer, lookupEnvironment, applySubst, Subst.lookup, beq_eq_decide]
        · by_cases same : first.key = key
          · simp only [same, decide_true, boolean, lookup, if_pos] at ⊢
            simpa [bound, applySubst, Subst.lookup, optionValue] using
              unary_constructor_returns program bound state "Some" "value" (by decide) (by decide)
          · simp only [same, decide_false, boolean, lookup] at ⊢
            apply lookup_raw_call_returns bound state rest key _ _ _ _ _ ih
            · simp [bound, outer, lookupEnvironment, applySubst, applySubst.applySubstList,
                Subst.lookup, bindingsValue, listValue]
            · simp [bound, outer, lookupEnvironment, applySubst, Subst.lookup]

theorem lookup_captured_returns (bindings : Subst) (state : State) (entries : List Binding)
    (key : Atom) (entriesName keyName : String)
    (capturedEntries : applySubst bindings (.var entriesName) = bindingsValue entries)
    (capturedKey : applySubst bindings (.var keyName) = key) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:lookup", .var entriesName, .var keyName]) state
      (optionValue (lookup entries key)) :=
  lookup_raw_call_returns bindings state entries key _ _ _ capturedEntries capturedKey
    (lookup_body_returns state entries key)

theorem lookup_sufficient_fuel (bindings : Subst) (state : State) (entries : List Binding)
    (key : Atom) (entriesName keyName : String)
    (capturedEntries : applySubst bindings (.var entriesName) = bindingsValue entries)
    (capturedKey : applySubst bindings (.var keyName) = key) :
    ∃ fuel, ∀ extra, Eval.run program (fuel + extra)
      { state, control := .evaluate bindings (.expression
          [.symbol "mm0:mmu:lookup", .var entriesName, .var keyName]) } =
      .complete state [optionValue (lookup entries key)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (lookup_captured_returns bindings state entries key entriesName keyName capturedEntries capturedKey)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [optionValue (lookup entries key)] [] [] completed⟩

private def consEquation : SpaceSemantics.Equation := dataSource.program.equations[4]'(by decide)
private def consEnvironment (first : Atom) (rest : List Atom) : Subst :=
  [("tail", listValue rest), ("first", first)]
private def consCases : SpaceSemantics.Cases :=
  match consEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def consBody : Atom := (consCases[0]'(by decide)).2

private theorem cons_unique :
    program.equations.filter (fun equation => equation.head == "mm0:list-cons") =
      [consEquation] := by decide
private theorem cons_formals : consEquation.arguments = [.var "first", .var "tail"] := by decide
private theorem cons_shape : consEquation.body =
    .expression [.symbol "case", .expression [.var "first", .var "tail"],
      .expression (consCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cons_cases_head : consCases =
    (.expression [.var "item", .expression [.symbol "MM0:L", .var "rest"]], consBody) ::
      consCases.tail := by decide
private theorem cons_body_shape : consBody =
    .expression [.symbol "let", .var "items", .expression [.symbol "cons", .var "item", .var "rest"],
      .expression [.symbol "MM0:L", .var "items"]] := by decide

private theorem cons_clause (first : Atom) (rest : List Atom) :
    clauses program "mm0:list-cons" [first, listValue rest] =
      [.evaluate (consEnvironment first rest) consEquation.body] := by
  rw [clauses_use_only_the_named_equations, cons_unique]
  simp [cons_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, consEnvironment]

private theorem cons_body_returns (state : State) (first : Atom) (rest : List Atom) :
    PureReturns program (consEnvironment first rest) state consEquation.body state
      (listValue (first :: rest)) := by
  let bindings := consEnvironment first rest
  let bound := ("rest", .expression rest) :: ("item", first) :: bindings
  rw [cons_shape]
  apply case_returns program bindings bound state state state (.expression [.var "first", .var "tail"])
    (.expression [first, listValue rest]) consBody _ _ consCases (read_cases_encoded consCases)
  · simpa [bindings, consEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings state ["first", "tail"]
  · rw [cons_cases_head]
    simp [SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, listValue, bound, bindings, consEnvironment]
  · rw [cons_body_shape]
    let wrapped := ("items", .expression (first :: rest)) :: bound
    apply let_returns program bound wrapped state state state (.var "items") _ _
      (.expression (first :: rest)) _
    · apply native_variable_call_returns program bound state state "cons" ["item", "rest"] _
        (by decide) (by decide) _ (by decide)
      simp [StdLib.apply, bound, bindings, consEnvironment, applySubst, Subst.lookup]
    · simp [SpaceSemantics.matchValue, matchAtom, wrapped, bound, bindings, consEnvironment, Subst.lookup]
    · simpa [wrapped, listValue, applySubst, Subst.lookup] using
        unary_constructor_returns program wrapped state "MM0:L" "items" (by decide) (by decide)

private theorem cons_raw_call_returns (bindings : Subst) (state : State)
    (first : Atom) (rest : List Atom) (firstArgument restArgument : Atom)
    (capturedFirst : applySubst bindings firstArgument = first)
    (capturedRest : applySubst bindings restArgument = listValue rest) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:list-cons", firstArgument, restArgument]) state
      (listValue (first :: rest)) := by
  apply call_returns program bindings state state "mm0:list-cons" _ _ (by decide) _ (by decide)
  apply raw_arguments_return program bindings state state "mm0:list-cons" _ [] 0 _
  · intro offset bounded
    have cases : offset = 0 ∨ offset = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases cases with rfl | rfl <;> decide
  · simpa [capturedFirst, capturedRest] using
      authored_function_arguments_return program bindings (consEnvironment first rest) state state
        "mm0:list-cons" [first, listValue rest] 2 consEquation.body (listValue (first :: rest))
        (by decide) (by decide) (cons_clause first rest) (cons_body_returns state first rest)

private def bindEquation : SpaceSemantics.Equation := resolverSource.program.equations[11]'(by decide)
private def bindEnvironment (entries : List Binding) (key value : Atom) : Subst :=
  [("value", value), ("name", key), ("bindings", bindingsValue entries)]
private theorem bind_unique :
    program.equations.filter (fun equation => equation.head == "mm0:mmu:bind") =
      [bindEquation] := by decide
private theorem bind_formals : bindEquation.arguments =
    [.var "bindings", .var "name", .var "value"] := by decide
private theorem bind_shape : bindEquation.body =
    .expression [.symbol "mm0:list-cons", .expression [.symbol "MM0:MMUBinding", .var "name", .var "value"],
      .var "bindings"] := by decide

private theorem bind_body_returns (state : State) (entries : List Binding) (key value : Atom) :
    PureReturns program (bindEnvironment entries key value) state bindEquation.body state
      (bindingsValue (⟨key, value⟩ :: entries)) := by
  rw [bind_shape]
  apply cons_raw_call_returns (bindEnvironment entries key value) state
    (bindingValue ⟨key, value⟩) (entries.map bindingValue)
  · simp [bindEnvironment, bindingValue, applySubst, applySubst.applySubstList, Subst.lookup]
  · simp [bindEnvironment, bindingsValue, applySubst, Subst.lookup]

theorem bind_captured_returns (bindings : Subst) (state : State) (entries : List Binding)
    (key value : Atom) (entriesName keyName valueName : String)
    (capturedEntries : applySubst bindings (.var entriesName) = bindingsValue entries)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (capturedValue : applySubst bindings (.var valueName) = value) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:bind", .var entriesName, .var keyName, .var valueName]) state
      (bindingsValue (⟨key, value⟩ :: entries)) := by
  apply authored_variable_call_returns program bindings (bindEnvironment entries key value) state state
    "mm0:mmu:bind" [entriesName, keyName, valueName] bindEquation.body _
    (by decide) (by decide) (by decide) _ (bind_body_returns state entries key value) (by decide)
  rw [clauses_use_only_the_named_equations, bind_unique]
  simp [capturedEntries, capturedKey, capturedValue, bind_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindEnvironment]

private def bindVariableEquation : SpaceSemantics.Equation := resolverSource.program.equations[12]'(by decide)
private def bindVariableEnvironment (entries : List Binding) (name : String) (index : Nat) : Subst :=
  [("index", natural index), ("name", nameValue name), ("bindings", bindingsValue entries)]
private theorem bindVariable_unique :
    program.equations.filter (fun equation => equation.head == "mm0:mmu:bind-variable") =
      [bindVariableEquation] := by decide
private theorem bindVariable_formals : bindVariableEquation.arguments =
    [.var "bindings", .var "name", .var "index"] := by decide
private theorem bindVariable_shape : bindVariableEquation.body =
    .expression [.symbol "if", .expression [.symbol "==", .var "name", nameValue "_"],
      .var "bindings", .expression [.symbol "mm0:mmu:bind", .var "bindings", .var "name", .var "index"]] := by decide

private theorem bindVariable_body_returns (state : State) (entries : List Binding) (name : String) (index : Nat) :
    PureReturns program (bindVariableEnvironment entries name index) state bindVariableEquation.body state
      (bindingsValue (bindVariable entries name index)) := by
  let bindings := bindVariableEnvironment entries name index
  rw [bindVariable_shape]
  apply if_returns program bindings state state state _ (boolean (decide (name = "_"))) _ _ _
  · apply native_binary_call_returns program bindings state state state state "=="
      (.var "name") (nameValue "_") (nameValue name) (nameValue "_") _
      (by decide) (by decide) (by decide) (by decide)
    · simpa [bindings, bindVariableEnvironment, applySubst, Subst.lookup] using
        variable_returns program bindings state "name"
    · exact grounded_returns program bindings state (.string "_")
    · simp [StdLib.apply, nameValue, beq_eq_decide]
    · decide
  · by_cases anonymous : name = "_"
    · simp only [anonymous, decide_true, boolean, bindVariable_anonymous]
      simpa [bindings, bindVariableEnvironment, applySubst, Subst.lookup] using
        variable_returns program bindings state "bindings"
    · simp only [anonymous, decide_false, boolean, bindVariable]
      apply bind_captured_returns bindings state entries (nameValue name) (natural index)
        "bindings" "name" "index"
      all_goals simp [bindings, bindVariableEnvironment, applySubst, Subst.lookup]

theorem bindVariable_captured_returns (bindings : Subst) (state : State) (entries : List Binding)
    (name : String) (index : Nat) (entriesName nameName indexName : String)
    (capturedEntries : applySubst bindings (.var entriesName) = bindingsValue entries)
    (capturedName : applySubst bindings (.var nameName) = nameValue name)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:bind-variable", .var entriesName, .var nameName, .var indexName]) state
      (bindingsValue (bindVariable entries name index)) := by
  apply authored_variable_call_returns program bindings (bindVariableEnvironment entries name index) state state
    "mm0:mmu:bind-variable" [entriesName, nameName, indexName] bindVariableEquation.body _
    (by decide) (by decide) (by decide) _ (bindVariable_body_returns state entries name index) (by decide)
  rw [clauses_use_only_the_named_equations, bindVariable_unique]
  simp [capturedEntries, capturedName, capturedIndex, bindVariable_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindVariableEnvironment]

theorem lookup_missing_captured_refused (bindings : Subst) (state : State) (entries : List Binding)
    (key : Atom) (entriesName keyName : String)
    (capturedEntries : applySubst bindings (.var entriesName) = bindingsValue entries)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (missing : ∀ entry ∈ entries, entry.key ≠ key) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:lookup", .var entriesName, .var keyName]) state (.symbol "None") := by
  have returned := lookup_captured_returns bindings state entries key entriesName keyName
    capturedEntries capturedKey
  rw [lookup_prefix_cannot_see_future entries key missing] at returned
  exact returned

/-- The inner map is earned by the actual bind equation. The second lookup
uses the original capture after the temporary lexical binding returns. -/
theorem shadowing_restores_outer_captured (bindings : Subst) (state : State) (entries : List Binding)
    (key value : Atom) (entriesName keyName valueName : String)
    (capturedEntries : applySubst bindings (.var entriesName) = bindingsValue entries)
    (capturedKey : applySubst bindings (.var keyName) = key)
    (capturedValue : applySubst bindings (.var valueName) = value)
    (freshInner : Subst.lookup bindings "mmuInner" = none)
    (keyOutside : "mmuInner" ≠ keyName) :
    PureReturns program bindings state
      (.expression [
        .expression [.symbol "let", .var "mmuInner",
          .expression [.symbol "mm0:mmu:bind", .var entriesName, .var keyName, .var valueName],
          .expression [.symbol "mm0:mmu:lookup", .var "mmuInner", .var keyName]],
        .expression [.symbol "mm0:mmu:lookup", .var entriesName, .var keyName]]) state
      (.expression [optionValue (some value), optionValue (lookup entries key)]) := by
  let inner : Subst := ("mmuInner", bindingsValue (⟨key, value⟩ :: entries)) :: bindings
  have first : PureReturns program bindings state
      (.expression [.symbol "let", .var "mmuInner",
        .expression [.symbol "mm0:mmu:bind", .var entriesName, .var keyName, .var valueName],
        .expression [.symbol "mm0:mmu:lookup", .var "mmuInner", .var keyName]]) state
      (optionValue (some value)) := by
    apply let_returns program bindings inner state state state (.var "mmuInner") _ _
      (bindingsValue (⟨key, value⟩ :: entries)) _
    · exact bind_captured_returns bindings state entries key value entriesName keyName valueName
        capturedEntries capturedKey capturedValue
    · simp [SpaceSemantics.matchValue, matchAtom, freshInner, inner]
    · have newEntries : applySubst inner (.var "mmuInner") = bindingsValue (⟨key, value⟩ :: entries) := by
        simp [inner, applySubst, Subst.lookup]
      have sameKey : applySubst inner (.var keyName) = key := by
        simpa [inner, applySubst, Subst.lookup, keyOutside] using capturedKey
      simpa only [lookup_shadow] using
        lookup_captured_returns inner state (⟨key, value⟩ :: entries) key "mmuInner" keyName newEntries sameKey
  have second := lookup_captured_returns bindings state entries key entriesName keyName capturedEntries capturedKey
  refine .step (step_transition rfl) ?_
  apply evaluated_argument_returns program bindings state state state .data _ (optionValue (some value)) _
    _ [] 0 rfl first
  apply evaluated_argument_returns program bindings state state state .data _ (optionValue (lookup entries key)) _
    [] [optionValue (some value)] 1 rfl second
  exact data_arguments_values_return program bindings state _ 2

theorem malformed_native_binding_refused (state : State) :
    PureReturns program [("key", nameValue "x"), ("items", listValue [natural 0])] state
      (.expression [.symbol "mm0:mmu:lookup", .var "items", .var "key"]) state (.symbol "None") := by
  let caller : Subst := [("key", nameValue "x"), ("items", listValue [natural 0])]
  let callee : Subst := [("name", nameValue "x"), ("entries", .expression [natural 0])]
  let bound : Subst := ("bad", .expression [natural 0]) :: callee
  apply authored_variable_call_returns program caller callee state state "mm0:mmu:lookup" ["items", "key"]
    lookupEquation.body (.symbol "None") (by decide) (by decide) (by decide)
  · rw [clauses_use_only_the_named_equations, lookup_unique]
    simp [caller, callee, applySubst, Subst.lookup, listValue, lookup_formals,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
  · rw [lookup_shape]
    apply case_returns program callee bound state state state (.var "entries") (.expression [natural 0])
      (.symbol "None") (.symbol "None") _ lookupCases (read_cases_encoded _)
    · simpa [callee, applySubst, Subst.lookup] using variable_returns program callee state "entries"
    · simp [lookup_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, callee, bound, Subst.lookup, natural]
    · exact symbol_returns program bound state "None"
  · decide

/-- Scanner operations belong to the shared primitive layer. Acquiring the
original file's bytes from the filesystem remains an explicit input boundary. -/
theorem scanner_primitives_registered :
    StdLib.known "str:from-codepoints" = true ∧ StdLib.known "str:byte-slice" = true ∧
      StdLib.known "str:byte-length" = true ∧ StdLib.known "str:concat" = true ∧
      StdLib.known "str:join" = true ∧ StdLib.known "parse" = true ∧
      StdLib.known "fs:read-text" = false := by decide

theorem exact_name_collision_controls :
    nameValue "01" ≠ nameValue "1" ∧ nameValue "True" ≠ boolean true ∧
      decodeName (.symbol "cons") = none ∧ decodeNatural (natural 3) = some 3 ∧
      decodeNatural (.grounded (.int (-1))) = none := by decide

theorem lexical_shadow_and_bound_control :
    let outer : Scope := ⟨[⟨nameValue "x", natural 0⟩], [⟨nameValue "x", natural 0⟩]⟩
    let inner := outer.extend "x" 1 false
    lookup inner.variableBindings (nameValue "x") = some (natural 1) ∧
      lookup inner.boundBindings (nameValue "x") = some (natural 0) ∧
      lookup outer.variableBindings (nameValue "x") = some (natural 0) ∧
      lookup inner.boundBindings (nameValue "future") = none := by decide

theorem future_public_metadata_does_not_extend_lookup :
    lookup [⟨nameValue "past", natural 0⟩] (nameValue "future") = none ∧
      lookup [⟨nameValue "future", natural 1⟩, ⟨nameValue "past", natural 0⟩]
        (nameValue "future") = some (natural 1) := by decide

theorem duplicate_history_orders_disagree :
    let entries : List Binding := [⟨nameValue "x", natural 0⟩, ⟨nameValue "x", natural 1⟩]
    lookup entries (nameValue "x") = some (natural 0) ∧
      lookup entries.reverse (nameValue "x") = some (natural 1) := by decide

theorem public_namespace_and_prefix_controls :
    let sortSlot : PublicSlot := ⟨"s", .sort 5 {}⟩
    let termSlot : PublicSlot := ⟨"t", .term 2 ⟨[], 5, ∅⟩⟩
    let slots := [sortSlot, termSlot]
    publicCeiling .sort slots = 6 ∧ publicCeiling .term slots = 3 ∧
      publicCeiling .theorem slots = 0 ∧
      lookup (publicBindings .term (slots.take 1)) (nameValue "t") = none ∧
      lookup (publicBindings .term slots) (nameValue "t") = some (natural 2) ∧
      lookup (publicBindings .sort slots) (nameValue "t") = none := by decide

theorem public_wire_malformed_controls :
    decodePublicWire (.expression [.symbol "MM0:MMUPublic", .symbol "s", kindValue .sort,
      natural 0, .symbol "payload"]) = none ∧
    decodePublicWire (.expression [.symbol "MM0:MMUPublic", nameValue "s", kindValue .sort,
      .grounded (.int (-1)), .symbol "payload"]) = none ∧
    decodePublicWire (.expression [.symbol "MM0:MMUPublic", nameValue "s", kindValue .sort,
      natural 0, .symbol "payload", .symbol "extra"]) = none ∧
    decodePublicWires (.expression [.symbol "MM0:MMUPublic", nameValue "s", kindValue .sort,
      natural 0, .symbol "payload"]) = none := by decide

end Mettapedia.Languages.MM0.MeTTa.MMUResolution
