import Mettapedia.Computability.StackMachineComposition

/-!
# Packaging supported stack programs without changing their transitions

A finite label support is closed under every source command. Restriction
keeps the original registers and physical stacks, replaces labels by members
of that support, and preserves counted executions in both directions.

The total label selector has an entry-label fallback outside the support.
The support proofs show that successful source runs never take that fallback.
Constructing the finite package is preparation, not a native execution bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FiniteSupportMachine

open Turing StateTransition

variable {Key Label State : Type} {Alphabet : Key → Type}
  [DecidableEq Key] [DecidableEq Label]

abbrev Restricted (labels : Finset Label) := {label // label ∈ labels}

def select (labels : Finset Label) (entry : Restricted labels) (label : Label) : Restricted labels :=
  if present : label ∈ labels then ⟨label, present⟩ else entry

theorem select_present (labels : Finset Label) (entry : Restricted labels) (label : Restricted labels) :
    select labels entry label.val = label := by
  simp [select, label.property]

def statement (labels : Finset Label) (entry : Restricted labels)
    (source : TM2.Stmt Alphabet Label State) : TM2.Stmt Alphabet (Restricted labels) State :=
  StackMachineRegisters.embedStatement (Alphabet := Alphabet) (TargetAlphabet := Alphabet)
    id (select labels entry) id (fun _ value => value) (fun _ => rfl) .halt source

def embed (labels : Finset Label) (entry : Restricted labels) (source : TM2.Cfg Alphabet Label State) :
    TM2.Cfg Alphabet (Restricted labels) State where
  l := source.l.map (select labels entry)
  var := source.var
  stk := source.stk

def erase (labels : Finset Label) (source : TM2.Cfg Alphabet (Restricted labels) State) :
    TM2.Cfg Alphabet Label State where
  l := source.l.map Subtype.val
  var := source.var
  stk := source.stk

def Valid (labels : Finset Label) (source : TM2.Cfg Alphabet Label State) : Prop :=
  source.l ∈ Finset.insertNone labels

omit [DecidableEq Key] [DecidableEq Label] in
theorem erase_valid (labels : Finset Label) (source : TM2.Cfg Alphabet (Restricted labels) State) :
    Valid labels (erase labels source) := by
  cases source with
  | mk label registers contents =>
      cases label with
      | none => simp [Valid, erase]
      | some label => simp [Valid, erase, label.property]

omit [DecidableEq Key] in
theorem embed_erase (labels : Finset Label) (entry : Restricted labels)
    (source : TM2.Cfg Alphabet (Restricted labels) State) :
    embed labels entry (erase labels source) = source := by
  cases source with
  | mk label registers contents =>
      cases label with
      | none => rfl
      | some label => simp [embed, erase, select_present]

omit [DecidableEq Key] in
theorem erase_embed (labels : Finset Label) (entry : Restricted labels)
    (source : TM2.Cfg Alphabet Label State) (valid : Valid labels source) :
    erase labels (embed labels entry source) = source := by
  cases source with
  | mk label registers contents =>
      cases label with
      | none => rfl
      | some label =>
          have present : label ∈ labels := by simpa [Valid] using valid
          simp [erase, embed, select, present]

theorem stepAux_statement (labels : Finset Label) (entry : Restricted labels)
    (source : TM2.Stmt Alphabet Label State) (registers : State)
    (contents : ∀ key, List (Alphabet key)) :
    TM2.stepAux (statement labels entry source) registers contents =
      embed labels entry (TM2.stepAux source registers contents) := by
  have relabeled := StackMachineRegisters.stepAux_embedContinuation
    (Alphabet := Alphabet) (TargetAlphabet := Alphabet)
    id (select labels entry) .halt id (fun _ value => value) (fun _ => rfl) id id
    (fun _ => rfl) (fun _ _ => rfl)
    (by intro contents key; change contents key = (contents key).map id; simp)
    (by intro contents key word; change Function.update contents key word = Function.update contents key (word.map id); simp)
    source registers contents
  have same (configuration : TM2.Cfg Alphabet Label State) :
      StackMachineRegisters.embeddedContinuationConfig (select labels entry) id id .halt configuration =
        embed labels entry configuration := by
    cases configuration with
    | mk label values stored => cases label <;> rfl
  exact relabeled.trans (same _)

def program (source : Label → TM2.Stmt Alphabet Label State) (labels : Finset Label)
    (entry : Restricted labels) : Restricted labels → TM2.Stmt Alphabet (Restricted labels) State :=
  fun label => statement labels entry (source label.val)

theorem step_embed (source : Label → TM2.Stmt Alphabet Label State) (labels : Finset Label)
    (entry : Restricted labels) (configuration : TM2.Cfg Alphabet Label State) (valid : Valid labels configuration) :
    TM2.step (program source labels entry) (embed labels entry configuration) =
      (TM2.step source configuration).map (embed labels entry) := by
  cases configuration with
  | mk label registers contents =>
      cases label with
      | none => rfl
      | some label =>
          have present : label ∈ labels := by simpa [Valid] using valid
          simp only [embed, Option.map_some, TM2.step, program]
          simp only [select, dif_pos present]
          exact congrArg some (stepAux_statement labels entry (source label) registers contents)

omit [DecidableEq Label] in
theorem step_valid (source : Label → TM2.Stmt Alphabet Label State) (labels : Finset Label)
    (entry : Restricted labels) (closed : ∀ label ∈ labels, TM2.SupportsStmt labels (source label))
    (before after : TM2.Cfg Alphabet Label State) (valid : Valid labels before)
    (advanced : TM2.step source before = some after) : Valid labels after := by
  let : Inhabited Label := ⟨entry.val⟩
  let bounded : @TM2.Supports Key Alphabet Label State ⟨entry.val⟩ source labels := ⟨entry.property, closed⟩
  exact TM2.step_supports source bounded (Option.mem_def.mpr advanced) valid

def lift_execution (source : Label → TM2.Stmt Alphabet Label State) (labels : Finset Label)
    (entry : Restricted labels) (closed : ∀ label ∈ labels, TM2.SupportsStmt labels (source label))
    {before : TM2.Cfg Alphabet Label State} {after : Option (TM2.Cfg Alphabet Label State)} {time : Nat}
    (valid : Valid labels before) (executed : EvalsToInTime (TM2.step source) before after time) :
    EvalsToInTime (TM2.step (program source labels entry)) (embed labels entry before)
      (after.map (embed labels entry)) time :=
  StackMachineRegisters.evalsInto (TM2.step source) (TM2.step (program source labels entry))
    (embed labels entry) (Valid labels) (step_valid source labels entry closed)
    (step_embed source labels entry) valid executed

theorem step_erase (source : Label → TM2.Stmt Alphabet Label State) (labels : Finset Label)
    (entry : Restricted labels) (closed : ∀ label ∈ labels, TM2.SupportsStmt labels (source label))
    (configuration : TM2.Cfg Alphabet (Restricted labels) State) :
    TM2.step source (erase labels configuration) =
      (TM2.step (program source labels entry) configuration).map (erase labels) := by
  have forward := step_embed source labels entry (erase labels configuration) (erase_valid labels configuration)
  rw [embed_erase] at forward
  rw [forward]
  cases advanced : TM2.step source (erase labels configuration) with
  | none => rfl
  | some after =>
      have valid := step_valid source labels entry closed _ after (erase_valid labels configuration) advanced
      simp only [Option.map_some, erase_embed labels entry after valid]

def erase_execution (source : Label → TM2.Stmt Alphabet Label State) (labels : Finset Label)
    (entry : Restricted labels) (closed : ∀ label ∈ labels, TM2.SupportsStmt labels (source label))
    {before after : TM2.Cfg Alphabet (Restricted labels) State} {time : Nat}
    (executed : EvalsToInTime (TM2.step (program source labels entry)) before (some after) time) :
    EvalsToInTime (TM2.step source) (erase labels before) (some (erase labels after)) time := by
  apply StackMachineComposition.lift_execution _ _ (erase labels) _ executed
  intro before after advanced
  rw [step_erase source labels entry closed before, advanced]
  rfl

/-- A single fixed finite transition table, constructed before any input.
The closure proof is used for execution correspondence, not as a clock law. -/
def machine [Fintype Key] [Fintype State] (source : Label → TM2.Stmt Alphabet Label State)
    (labels : Finset Label) (entry : Restricted labels) (initial : State)
    (input output : Key) [Fintype (Alphabet input)] : FinTM2 where
  K := Key
  k₀ := input
  k₁ := output
  Γ := Alphabet
  Λ := Restricted labels
  main := entry
  σ := State
  initialState := initial
  m := program source labels entry

end Mettapedia.Computability.FiniteSupportMachine
