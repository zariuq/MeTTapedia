import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingPlans

/-!
# Portable templates for a binding plan

The interface singles out two local laws: the opening instruction
installs one shared chain, and a hold instruction preserves the datum
at its lexically compiled slots. Representations may decline any
instruction. An accepted sequence has a representation-independent
readback. A finite word representation supplies a checked instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingTemplates

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open BindingPlans

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

inductive Refusal where
  | capacity
  | scopeOverflow
  | unrepresentable
  | inconsistent
  | credit
  deriving DecidableEq

structure Templates (κ : Keys S) (Γ : Ctx S) (star : S.Srt) where
  Table : Type
  Value : Type
  scopes : Table → ScopeTable
  view : Value → Data κ Γ star
  openScope : Table → Nat → Nat → Option Nat → Except Refusal Table
  hold : (operand : Operand κ Γ star) → Table → List Nat → Except Refusal Value
  open_exact : ∀ {table offset fresh parent next},
    openScope table offset fresh parent = .ok next →
    scopes next = Function.update (scopes table) offset (fresh :: chain (scopes table) parent)
  hold_exact : ∀ {operand table entry result},
    hold operand table entry = .ok result →
    view result = operand.read (scopes table) entry

section ExecutionAlgebra

variable {M : Type → Type} [Monad M] {Table Value : Type}
  (hold : Operand κ Γ star → Table → List Nat → M Value)
  (openScope : Table → Nat → Nat → Option Nat → M Table)

/-- The instruction order is shared by every realization, including a
realization that accounts for the work of a refused instruction. -/
def runBindingsWith (origin : Nat) (entry : List Nat) :
    List (Binding κ Γ star) → Nat → Table → M (Table × List (Value × Value))
  | [], _, table => pure (table, [])
  | binding :: later, offset, table => do
    let value ← hold binding.value table entry
    let opened ← openScope table offset (origin + offset) binding.parent
    let pattern ← hold binding.pattern opened entry
    (fun result => (result.1, (pattern, value) :: result.2)) <$>
      runBindingsWith origin entry later (offset + 1) opened

def runWith (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat) (table : Table) :
    M ((Table × List (Value × Value)) × Value) := do
  let result ← runBindingsWith hold openScope origin entry plan.code offset table
  Prod.mk result <$> hold plan.result result.1 entry

end ExecutionAlgebra

section Execution

variable (templates : Templates κ Γ star)

private theorem bind_error {A B : Type} (error : Refusal) (next : A → Except Refusal B) :
    (Except.error error >>= next) = Except.error error := rfl

private theorem bind_ok {A B : Type} (value : A) (next : A → Except Refusal B) :
    (Except.ok value >>= next) = next value := rfl

private theorem map_error {A B : Type} (error : Refusal) (view : A → B) :
    view <$> Except.error error = Except.error error := rfl

private theorem map_ok {A B : Type} (value : A) (view : A → B) :
    view <$> (Except.ok value : Except Refusal A) = Except.ok (view value) := rfl

attribute [local simp] bind_error bind_ok map_error map_ok

def Templates.equation (pair : templates.Value × templates.Value) : Constraint κ Γ star :=
  (templates.view pair.1, templates.view pair.2)

def runBindings (origin : Nat) (entry : List Nat) :
    List (Binding κ Γ star) → Nat → templates.Table →
      Except Refusal (templates.Table × List (templates.Value × templates.Value)) :=
  runBindingsWith templates.hold templates.openScope origin entry

theorem runBindings_cons (origin : Nat) (entry : List Nat) (binding : Binding κ Γ star)
    (later : List (Binding κ Γ star)) (offset : Nat) (table : templates.Table) :
    runBindings templates origin entry (binding :: later) offset table = (do
      let value ← templates.hold binding.value table entry
      let opened ← templates.openScope table offset (origin + offset) binding.parent
      let pattern ← templates.hold binding.pattern opened entry
      (fun result => (result.1, (pattern, value) :: result.2)) <$>
        runBindings templates origin entry later (offset + 1) opened) := rfl

def run (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat) (table : templates.Table) :
    Except Refusal ((templates.Table × List (templates.Value × templates.Value)) × templates.Value) :=
  runWith templates.hold templates.openScope plan origin entry offset table

theorem run_parts (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat)
    (table : templates.Table) : run templates plan origin entry offset table = (do
  let result ← runBindings templates origin entry plan.code offset table
  Prod.mk result <$> templates.hold plan.result result.1 entry) := rfl

theorem runBindings_exact (origin : Nat) (entry : List Nat) (code : List (Binding κ Γ star))
    (offset : Nat) (table : templates.Table) {after : templates.Table}
    {facts : List (templates.Value × templates.Value)}
    (accepted : runBindings templates origin entry code offset table = .ok (after, facts)) :
    (templates.scopes after, facts.map templates.equation) =
      executeBindings origin entry code offset (templates.scopes table) := by
  induction code generalizing offset table after facts with
  | nil =>
    cases accepted
    rfl
  | cons binding rest ih =>
    cases recordedValue : templates.hold binding.value table entry with
    | error failed => simp [runBindings_cons, recordedValue] at accepted
    | ok value =>
      cases opened : templates.openScope table offset (origin + offset) binding.parent with
      | error failed => simp [runBindings_cons, recordedValue, opened] at accepted
      | ok next =>
        cases recordedPattern : templates.hold binding.pattern next entry with
        | error failed => simp [runBindings_cons, recordedValue, opened, recordedPattern] at accepted
        | ok pattern =>
          cases continued : runBindings templates origin entry rest (offset + 1) next with
          | error failed => simp [runBindings_cons, recordedValue, opened, recordedPattern, continued] at accepted
          | ok result =>
            obtain ⟨last, following⟩ := result
            simp [runBindings_cons, recordedValue, opened, recordedPattern, continued] at accepted
            obtain ⟨rfl, rfl⟩ := accepted
            have tail := ih (offset + 1) next continued
            have installed : binding.extend origin offset (templates.scopes table) =
                templates.scopes next := (templates.open_exact opened).symm
            simp only [List.map_cons, Templates.equation, templates.hold_exact recordedPattern,
              templates.hold_exact recordedValue, executeBindings, installed]
            rw [← tail]

theorem run_exact (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat)
    (table : templates.Table) {after : templates.Table} {facts : List (templates.Value × templates.Value)}
    {value : templates.Value}
    (accepted : run templates plan origin entry offset table = .ok ((after, facts), value)) :
    ((templates.scopes after, facts.map templates.equation), templates.view value) =
      plan.execute origin entry offset (templates.scopes table) := by
  cases ran : runBindings templates origin entry plan.code offset table with
  | error failed => simp [run_parts, ran] at accepted
  | ok result =>
    obtain ⟨last, facts'⟩ := result
    cases held : templates.hold plan.result last entry with
    | error failed => simp [run_parts, ran, held] at accepted
    | ok answer =>
      simp [run_parts, ran, held] at accepted
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := accepted
      simp only [Plan.execute, ← runBindings_exact templates origin entry plan.code offset table ran,
        templates.hold_exact held]

/-- Two accepted realizations with the same initial readback give the
same facts and value. The result includes the extension of the scope
table, so scope-preserving relocation can be used between regions. -/
theorem accepted_readback_independent (other : Templates κ Γ star)
    (plan : Plan κ Γ star) (origin : Nat) (entry : List Nat) (offset : Nat)
    (table : templates.Table) (otherTable : other.Table)
    (same : templates.scopes table = other.scopes otherTable)
    {after : templates.Table} {facts : List (templates.Value × templates.Value)} {value : templates.Value}
    {otherAfter : other.Table} {otherFacts : List (other.Value × other.Value)} {otherValue : other.Value}
    (first : run templates plan origin entry offset table = .ok ((after, facts), value))
    (second : run other plan origin entry offset otherTable = .ok ((otherAfter, otherFacts), otherValue)) :
    ((templates.scopes after, facts.map templates.equation), templates.view value) =
      ((other.scopes otherAfter, otherFacts.map other.equation), other.view otherValue) := by
  rw [run_exact templates _ _ _ _ _ first, run_exact other _ _ _ _ _ second, same]

end Execution

namespace Words

/-- Each cell contains the head of a persistent chain of scope words.
The slot bound and the word width are independent parameters. -/
abbrev Table (capacity width : Nat) := Vector (List (BitVec width)) capacity

def read {capacity width : Nat} (table : Table capacity width) (slot : Option Nat) :
    List (BitVec width) :=
  match slot with
  | none => []
  | some index => if bounded : index < capacity then table[index] else []

def scopes {capacity width : Nat} (table : Table capacity width) : ScopeTable :=
  fun index => (read table (some index)).map BitVec.toNat

theorem read_view {capacity width : Nat} (table : Table capacity width) (slot : Option Nat) :
    (read table slot).map BitVec.toNat = chain (scopes table) slot := by cases slot <;> rfl

def openScope {capacity width : Nat} (table : Table capacity width) (offset fresh : Nat)
    (parent : Option Nat) : Except Refusal (Table capacity width) :=
  if bounded : offset < capacity then
    if fresh < 2 ^ width then
      .ok (table.set offset (BitVec.ofNat width fresh :: read table parent))
    else .error .scopeOverflow
  else .error .capacity

theorem open_exact {capacity width : Nat} {table next : Table capacity width} {offset fresh : Nat}
    {parent : Option Nat} (ran : openScope table offset fresh parent = .ok next) :
    scopes next = Function.update (scopes table) offset (fresh :: chain (scopes table) parent) := by
  unfold openScope at ran
  split at ran
  · rename_i within
    split at ran
    · rename_i fits
      cases ran
      funext index
      by_cases same : index = offset
      · subst index
        simp [scopes, read, within, Nat.mod_eq_of_lt fits, ← read_view]
      · rw [Function.update_of_ne same]
        by_cases indexFits : index < capacity
        · simp [scopes, read, indexFits, Ne.symm same]
        · simp [scopes, read, indexFits]
    · cases ran
  · cases ran

/-- Capture only the designated chains. Changes to the table after a
hold leave its value and its aliases intact. -/
structure Held (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (width : Nat) where
  operand : Operand κ Γ star
  chains : Vector (List (BitVec width)) operand.names.length
  entry : List Nat

def Held.datum {width : Nat} (held : Held κ Γ star width) : Data κ Γ star :=
  held.operand.readSlots (fun port => held.chains[port].map BitVec.toNat) held.entry

def hold {capacity width : Nat} (operand : Operand κ Γ star) (table : Table capacity width)
    (entry : List Nat) : Held κ Γ star width :=
  ⟨operand, Vector.ofFn (fun slot => read table (operand.reference slot)), entry⟩

theorem hold_exact {capacity width : Nat} (operand : Operand κ Γ star)
    (table : Table capacity width) (entry : List Nat) :
    (hold operand table entry).datum = operand.read (scopes table) entry := by
  unfold Held.datum hold Operand.read
  congr 1
  funext port
  change (Vector.ofFn (fun slot => read table (operand.reference slot)))[port.val].map BitVec.toNat = _
  rw [Vector.getElem_ofFn, read_view]

def templates (capacity width : Nat) : Templates κ Γ star where
  Table := Table capacity width
  Value := Held κ Γ star width
  scopes := scopes
  view := Held.datum
  openScope := openScope
  hold operand table entry := .ok (hold operand table entry)
  open_exact := open_exact
  hold_exact := by
    intro operand table entry result accepted
    cases accepted
    exact hold_exact operand table entry

/-- Because the instruction stream visits contiguous positions, the
last position and the last fresh scope bound the whole run. -/
theorem runBindings_complete (capacity width origin : Nat) (entry : List Nat)
    (code : List (Binding κ Γ star)) (offset : Nat) (table : Table capacity width)
    (ready : code.isEmpty = true ∨ offset + code.length ≤ capacity ∧
      origin + offset + code.length ≤ 2 ^ width) :
    ∃ result, runBindings (templates capacity width) origin entry code offset table = .ok result := by
  induction code generalizing offset table with
  | nil => exact ⟨_, rfl⟩
  | cons binding later ih =>
    have fits := ready.resolve_left (by simp)
    have bound : offset < capacity := by simp only [List.length_cons] at fits; omega
    have word : origin + offset < 2 ^ width := by simp only [List.length_cons] at fits; omega
    let next := table.set offset (BitVec.ofNat width (origin + offset) :: read table binding.parent)
    obtain ⟨after, runs⟩ := ih (offset + 1) next (.inr (by
      simp only [List.length_cons] at fits
      exact ⟨by omega, by omega⟩))
    refine ⟨(after.1, (hold binding.pattern next entry, hold binding.value table entry) :: after.2), ?_⟩
    have opens : openScope table offset (origin + offset) binding.parent = .ok next := by
      simp only [openScope, dif_pos bound, if_pos word, next]
    change (do
      let value ← (.ok (hold binding.value table entry) : Except Refusal _)
      let opened ← openScope table offset (origin + offset) binding.parent
      let pattern ← (.ok (hold binding.pattern opened entry) : Except Refusal _)
      (fun (result : Table capacity width × List (Held κ Γ star width × Held κ Γ star width)) =>
        (result.1, (pattern, value) :: result.2)) <$>
        runBindings (templates capacity width) origin entry later (offset + 1) opened) = _
    simp [bind_ok, opens, runs]
    rfl

end Words

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingTemplates
