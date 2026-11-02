import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation

/-!
# Actual immutable context-table allocation follows original local admission

The initial context occupies slot zero. Proof commands retain their context
ID; accepted declaration commands append the actual computed context at the
old finite table size. Earlier lookup results survive. The returned source
entry's routing proof is constructed from that actual admission and lookup,
without context equality by names, a digest axiom or a fresh-ID oracle.

Registration stores a context value; logical availability still requires the
separate rooted source-premise licensing boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTable

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open HOLLightContextActivation

structure Table where
  contexts : Array TheoryContext

def initial (context : TheoryContext) : Table := ⟨#[context]⟩
def lookup (table : Table) (id : Nat) : Option TheoryContext := table.contexts[id]?
def append (table : Table) (context : TheoryContext) : Table := ⟨table.contexts.push context⟩
def interpret (table : Table) (fallback : TheoryContext) (id : Nat) : TheoryContext := (lookup table id).getD fallback

theorem initial_lookup (context : TheoryContext) : lookup (initial context) 0 = some context := rfl

theorem append_lookup_new (table : Table) (context : TheoryContext) :
    lookup (append table context) table.contexts.size = some context := by simp [lookup, append]

theorem append_lookup_old (table : Table) (context : TheoryContext) {id : Nat} {old : TheoryContext}
    (known : lookup table id = some old) : lookup (append table context) id = some old := by
  have bounded : id < table.contexts.size := (Array.getElem?_eq_some_iff.mp known).1
  change (table.contexts.push context)[id]? = some old
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt bounded)]
  exact known

def changesContext : Command → Bool
  | .proof _ _ => false
  | .constant _ _ _ _ | .typeDefinition _ _ _ _ => true

def updated (table : Table) (before : Nat) (command : Command) (output : Output) : Table × Nat × Output :=
  if changesContext command then (append table output.context, table.contexts.size, output)
  else (table, before, output)

def register (policy : AxiomPolicy) [DecidablePred policy] (table : Table) (before : Nat)
    (command : Command) (cache : Array Theorem) : Option (Table × Nat × Output) := do
  let context ← lookup table before
  let output ← command.check policy context cache
  pure (updated table before command output)

theorem registration_origin (policy : AxiomPolicy) [DecidablePred policy] (table : Table) (before : Nat)
    (command : Command) (cache : Array Theorem) {result : Table × Nat × Output}
    (computed : register policy table before command cache = some result) :
    ∃ context output, lookup table before = some context ∧
      command.check policy context cache = some output ∧ result = updated table before command output := by
  cases known : lookup table before with
  | none => simp [register, known] at computed
  | some context =>
      cases checked : command.check policy context cache with
      | none => simp [register, known, checked] at computed
      | some output =>
          have same : updated table before command output = result := by simpa [register, known, checked] using computed
          exact ⟨context, output, rfl, checked, same.symm⟩

theorem updated_retains_old (table : Table) (before : Nat) (command : Command) (output : Output)
    {id : Nat} {context : TheoryContext} (known : lookup table id = some context) :
    lookup (updated table before command output).1 id = some context := by
  unfold updated
  split
  · exact append_lookup_old table output.context known
  · exact known

theorem updated_lookup_target (policy : AxiomPolicy) [DecidablePred policy] (table : Table) (before : Nat)
    (command : Command) (cache : Array Theorem) {context : TheoryContext} {output : Output}
    (known : lookup table before = some context) (checked : command.check policy context cache = some output) :
    lookup (updated table before command output).1 (updated table before command output).2.1 = some output.context := by
  cases command with
  | proof node witnesses =>
      have same : context = output.context := Option.some.inj (checked_target_context policy _ _ _ checked)
      change lookup table before = some output.context
      exact known.trans (congrArg some same)
  | constant origin name body witnesses => exact append_lookup_new table output.context
  | typeDefinition origin request index witnesses => exact append_lookup_new table output.context

/-- A successful registration constructs the exact routed original source
entry in the returned actual table interpretation. -/
theorem registration_builds_entry (policy : AxiomPolicy) [DecidablePred policy] (table : Table) (before : Nat)
    (command : Command) (cache : Array Theorem) {result : Table × Nat × Output}
    (computed : register policy table before command cache = some result) (fallback : TheoryContext) :
    ∃ entry : Entry (interpret result.1 fallback), entry.before = before ∧ entry.after = result.2.1 ∧ entry.command = command := by
  obtain ⟨context, output, known, checked, rfl⟩ := registration_origin policy table before command cache computed
  have beforeLookup := updated_retains_old table before command output known
  have afterLookup := updated_lookup_target policy table before command cache known checked
  refine ⟨⟨before, (updated table before command output).2.1, command, ?_⟩, rfl, rfl, rfl⟩
  simp only [interpret, beforeLookup, afterLookup, Option.getD_some]
  exact checked_target_context policy context cache command checked

theorem declaration_gets_fresh_actual_slot (table : Table) (before : Nat) (command : Command) (output : Output)
    (declaration : changesContext command = true) :
    (updated table before command output).2.1 = table.contexts.size ∧
      ∀ id context, lookup table id = some context → id ≠ (updated table before command output).2.1 := by
  simp only [updated, declaration, if_true]
  refine ⟨trivial, ?_⟩
  intro id context known same
  have bounded : id < table.contexts.size := (Array.getElem?_eq_some_iff.mp known).1
  omega

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextTable
