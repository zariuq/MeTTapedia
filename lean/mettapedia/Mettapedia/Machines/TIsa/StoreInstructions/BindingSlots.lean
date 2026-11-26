import Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms

/-!
# Single-slot bindings for an open match

The abstract matcher records every variable occurrence in a list.
For the lookup observer, one cell per variable is enough. An empty
cell can be written; a filled cell is tested without writing it.
This keeps the consistency check for a repeated variable without
requiring a second copy of its binding.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.BindingSlots

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Derivation.FirstOrderTerms (Bindings lookup lookup_some lookup_isSome extend)

variable {σ : LPSignature}

abbrev Table (σ : LPSignature) := σ.vars → Option (GroundTerm σ)

def Represents (table : Table σ) (history : Bindings σ) : Prop :=
  ∀ name value, table name = some value ↔ (name, value) ∈ history

theorem represented_consistent {table : Table σ} {history : Bindings σ} (view : Represents table history) :
    BindingsConsistent history := by
  intro name first second foundFirst foundSecond
  exact Option.some.inj (((view name first).mpr foundFirst).symm.trans ((view name second).mpr foundSecond))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem lookup_represents (history : Bindings σ) (consistent : BindingsConsistent history) :
    Represents (lookup history) history := by
  intro name value
  refine ⟨lookup_some, fun member => ?_⟩
  have found := lookup_isSome (θ := history) (x := name) ⟨value, member⟩
  obtain ⟨selected, atName⟩ := Option.isSome_iff_exists.mp found
  exact (congrArg some (consistent name selected value (lookup_some atName) member)) ▸ atName

def bind (table : Table σ) (name : σ.vars) (value : GroundTerm σ) : Option (Table σ) :=
  match table name with
  | none => some (Function.update table name (some value))
  | some old => if old = value then some table else none

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem append_same {table : Table σ} {history : Bindings σ} (view : Represents table history)
    {name : σ.vars} {value : GroundTerm σ} (present : table name = some value) :
    Represents table (history ++ [(name, value)]) := by
  intro x word
  rw [List.mem_append, List.mem_singleton, ← view x word]
  refine ⟨Or.inl, fun found => ?_⟩
  rcases found with old | here
  · exact old
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj here
    exact present

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem append_new {table : Table σ} {history : Bindings σ} (view : Represents table history)
    {name : σ.vars} (empty : table name = none) (value : GroundTerm σ) :
    Represents (Function.update table name (some value)) (history ++ [(name, value)]) := by
  intro x word
  rw [List.mem_append, List.mem_singleton, ← view x word]
  by_cases same : x = name
  · subst x
    simp [empty, eq_comm]
  · simp [same]

theorem bind_represents {table after : Table σ} {history : Bindings σ} (view : Represents table history)
    (name : σ.vars) (value : GroundTerm σ) (found : bind table name value = some after) :
    Represents after (history ++ [(name, value)]) := by
  cases present : table name with
  | none =>
    simp only [bind, present, Option.some.injEq] at found
    exact found ▸ append_new view present value
  | some old =>
    by_cases same : old = value
    · simp only [bind, present, if_pos same, Option.some.injEq] at found
      exact found ▸ append_same view (same ▸ present)
    · simp [bind, present, same] at found

theorem bind_accepts {table : Table σ} {history : Bindings σ} (view : Represents table history)
    (name : σ.vars) (value : GroundTerm σ) :
    (bind table name value).isSome = true ↔ BindingsConsistent (history ++ [(name, value)]) := by
  constructor
  · intro accepts
    obtain ⟨after, found⟩ := Option.isSome_iff_exists.mp accepts
    exact represented_consistent (bind_represents view name value found)
  · intro consistent
    cases present : table name with
    | none => simp [bind, present]
    | some old =>
      have same := consistent name old value (List.mem_append_left _ ((view name old).mp present))
        (List.mem_append_right _ List.mem_cons_self)
      simp [bind, present, same]

/-- When a variable is already bound, the successful path only reads
its slot. The repeated occurrence still counts as a constraint. -/
theorem bind_equal_does_not_write (table : Table σ) (name : σ.vars) (value : GroundTerm σ)
    (present : table name = some value) : bind table name value = some table := by
  simp [bind, present]

theorem bind_keeps_other {table next : Table σ} {name other : σ.vars} (value : GroundTerm σ)
    (distinct : other ≠ name) (accepted : bind table name value = some next) : next other = table other := by
  cases filled : table name with
  | none =>
    have same : Function.update table name (some value) = next := Option.some.inj (by simpa [bind, filled] using accepted)
    rw [← same, Function.update_of_ne distinct]
  | some held =>
    by_cases equal : held = value
    · have same : table = next := Option.some.inj (by simpa [bind, filled, equal] using accepted)
      rw [← same]
    · simp [bind, filled, equal] at accepted

def install : Table σ → Bindings σ → Option (Table σ)
  | table, [] => some table
  | table, (name, value) :: rest => (bind table name value).bind (fun next => install next rest)

theorem install_represents {table : Table σ} {history : Bindings σ} (view : Represents table history)
    (fresh : Bindings σ) {after : Table σ} (result : install table fresh = some after) :
    Represents after (history ++ fresh) := by
  induction fresh generalizing table history with
  | nil =>
    have same : table = after := Option.some.inj result
    simpa only [List.append_nil, ← same] using view
  | cons first rest ih =>
    obtain ⟨name, value⟩ := first
    obtain ⟨next, bound, continued⟩ := Option.bind_eq_some_iff.mp result
    have exact := ih (bind_represents view name value bound) continued
    simpa only [List.append_assoc, List.singleton_append] using exact

theorem install_accepts {table : Table σ} {history : Bindings σ} (view : Represents table history)
    (fresh : Bindings σ) :
    (install table fresh).isSome = true ↔ BindingsConsistent (history ++ fresh) := by
  constructor
  · intro accepts
    obtain ⟨after, found⟩ := Option.isSome_iff_exists.mp accepts
    exact represented_consistent (install_represents view fresh found)
  · intro consistent
    induction fresh generalizing table history with
    | nil => rfl
    | cons first rest ih =>
      obtain ⟨name, value⟩ := first
      have more : BindingsConsistent ((history ++ [(name, value)]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using consistent
      have initial : BindingsConsistent (history ++ [(name, value)]) := fun x left right l r =>
        more x left right (List.mem_append_left _ l) (List.mem_append_left _ r)
      obtain ⟨next, inserted⟩ := Option.isSome_iff_exists.mp ((bind_accepts view name value).mpr initial)
      have later := ih (bind_represents view name value inserted) more
      simpa only [install, inserted, Option.bind_some] using later

def matchPattern (table : Table σ) (pattern : Term σ) (candidate : GroundTerm σ) : Option (Table σ) :=
  (collectBindings pattern candidate).bind (install table)

/-- Checked slot insertion realizes every successful open first-order
match. Its outcome agrees with the list matcher on the complete binding
history, including name sharing and refusals on inconsistency. -/
theorem matchPattern_accepts {table : Table σ} {history : Bindings σ} (view : Represents table history)
    (pattern : Term σ) (candidate : GroundTerm σ) :
    (matchPattern table pattern candidate).isSome = (extend history pattern candidate).isSome := by
  unfold matchPattern extend
  cases collected : collectBindings pattern candidate with
  | none => rfl
  | some fresh =>
    simp only [Option.bind_some]
    by_cases consistent : BindingsConsistent (history ++ fresh)
    · rw [if_pos ((bindingsConsistent?_eq_true _).mpr consistent)]
      exact (install_accepts view fresh).mpr consistent
    · have denied : bindingsConsistent? (history ++ fresh) ≠ true :=
        fun h => consistent ((bindingsConsistent?_eq_true _).mp h)
      rw [if_neg denied]
      apply Bool.eq_false_iff.mpr
      exact fun accepted => consistent ((install_accepts view fresh).mp accepted)

theorem matchPattern_represents {table after : Table σ} {history result : Bindings σ}
    (view : Represents table history) (pattern : Term σ) (candidate : GroundTerm σ)
    (matched : matchPattern table pattern candidate = some after)
    (reference : extend history pattern candidate = some result) : Represents after result := by
  obtain ⟨fresh, collected, _, rfl⟩ := Derivation.FirstOrderTerms.extend_some reference
  have result := install_represents view fresh (after := after)
  exact result (by simpa only [matchPattern, collected, Option.bind_some] using matched)

namespace Examples

private abbrev atoms : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := nofun

private instance : DecidableEq atoms.vars := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq atoms.constants := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq atoms.functionSymbols := inferInstanceAs (DecidableEq Empty)

private def empty : Table atoms := fun _ => none
private def red : GroundTerm atoms := .const 7
private def blue : GroundTerm atoms := .const 8

theorem repeated_variable_keeps_one_binding :
    (install empty [(0, red), (0, red)]).bind (· 0) = some red := by decide +kernel

theorem inconsistent_repetition_refuses :
    (install empty [(0, red), (0, blue)]).isNone = true := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.BindingSlots
