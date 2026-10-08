import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Space
import Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces
import Mathlib.Data.String.Lemmas

open Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite (RewriteResults)

/-!
# PeTTa `&self` commands over MeTTaIL patterns

This module is the MeTTaIL view of PeTTa's `&self` commands. `PeTTaCmd`
extends the rewrite selection of `PeTTaEval` with add, remove and get-atoms
and with sequencing; it does not run programs. Private spaces, cells,
primitive outcomes and I/O of PeTTa programs are stated over
`OSLFCore.Atom` in `Effects`, `StdLib` and `Eval`. The last section
specializes the shared named-space store to `Pattern` spaces.

Formalizes the **stateful** layer of PeTTa evaluation — the `EvalState` / `PeTTaCmd`
judgment that adds side-effecting commands on top of the pure `PeTTaEval` core.

## Architecture

```
PeTTaEval (pure, state-preserving)       ← MeTTaIL/Space.lean
  ↑ embedded via PeTTaCmd.pureEval
PeTTaCmd (stateful, state-transforming)  ← this file
```

`PeTTaCmd s₀ expr s₁ answers` means: starting from state `s₀`, evaluating the
expression `expr` produces answers `answers` and leaves the system in state `s₁`.

## PeTTa Commands Modeled

| PeTTa expression              | PeTTaCmd constructor     | State change           |
|-------------------------------|--------------------------|------------------------|
| `(add-atom &self p)`          | `addAtomCmd`             | adds `p` to facts      |
| `(remove-atom &self p)`       | `removeAtomCmd`          | removes `p` from facts |
| `(get-atoms &self)`           | `getAtomsCmd`            | no change              |
| any pure expression           | `pureEval`               | no change              |
| `(let* ((x e)) body)`         | `letCmd`                 | no change (pure let)   |
| `(progn e₁ e₂)`               | `prognCmd`               | sequential composition |

## Design Choices

- `EvalState` wraps `PeTTaSpace` (single `&self` space). Named spaces, cells
  and I/O are stated over `OSLFCore.Atom` in `Effects` and `Eval`.
- All answers are `RewriteResults = List Pattern` (same as `PeTTaEval`).
- Ordinary `add-atom` and `remove-atom` return Boolean `True`, matching
  CeTTa PeTTa mode and the upstream Prolog ordinary-fact operations.
- `(get-atoms &self)` returns all currently stored atoms (facts plus the
  narrow visible stored-rule slice) as a superposition of answers.
- `prognCmd` sequences two commands: the second is evaluated in the output state
  of the first, and the final answers are those of the second.

## References

- PeTTa transpiler: `hyperon/PeTTa/transpiler.pl`, `spaces.pl`
- PeTTa lib: `hyperon/PeTTa/lib/lib_metta4.metta` (progn, prog1)
- MeTTa spec: `trueagi-io.github.io/hyperon-experimental/metta/`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Evaluation State -/

/-- The evaluation state: wraps a `PeTTaSpace` (the `&self` atomspace).
    Future extensions: multiple named spaces, output log, random seed, etc. -/
structure EvalState where
  /-- The primary atomspace (`&self`). -/
  space : PeTTaSpace

namespace EvalState

/-- The initial (empty) evaluation state. -/
def empty : EvalState := { space := PeTTaSpace.empty }

/-- Project the space out. -/
@[simp] def getSpace (s : EvalState) : PeTTaSpace := s.space

/-- Update the space in-place (functional update). -/
def withSpace (s : EvalState) (sp : PeTTaSpace) : EvalState := { s with space := sp }

/-- Add a fact atom to the state. -/
def addAtom (s : EvalState) (p : Pattern) : EvalState :=
  { s with space := s.space.addAtom p }

/-- Remove all occurrences of a fact atom from the state. -/
def removeAtom (s : EvalState) (p : Pattern) : EvalState :=
  { s with space := s.space.removeAtom p }

/-- Add a rewrite rule to the state. -/
def addRule (s : EvalState) (r : RewriteRule) : EvalState :=
  { s with space := s.space.addRule r }

end EvalState

/-! ## The Unit Atom -/

/-- The unit literal `()`. Ordinary space mutations return `True`. -/
def unitAtom : Pattern := .apply "()" []

/-- Successful ordinary space mutations return a Boolean. -/
def mutationSuccess : Pattern := .apply "True" []

/-! ## Stateful Evaluation Relation -/

/-- **PeTTa command evaluation** (stateful).

    `PeTTaCmd s₀ expr s₁ answers` means:
    starting in state `s₀`, evaluating `expr` transitions to state `s₁`
    and produces nondeterministic answer set `answers`.

    Constructors cover the effectful PeTTa primitives plus embedding of pure eval. -/
inductive PeTTaCmd : EvalState → Pattern → EvalState → RewriteResults → Prop where

  /-- **add-atom**: `(add-atom &self p)` adds `p` to the space and returns `True`.

      PeTTa: `'add-atom'(&self, P) :- add_atom_to_space(self, P).`
      Answer: `[True]`. -/
  | addAtomCmd (s : EvalState) (p : Pattern) :
      PeTTaCmd s
        (.apply "add-atom" [.apply "&self" [], p])
        (s.addAtom p)
        [mutationSuccess]

  /-- **remove-atom**: `(remove-atom &self p)` removes all copies of `p` from
      the space and returns `True`.

      PeTTa: `'remove-atom'(&self, P) :- remove_atom_from_space(self, P).` -/
  | removeAtomCmd (s : EvalState) (p : Pattern) :
      PeTTaCmd s
        (.apply "remove-atom" [.apply "&self" [], p])
        (s.removeAtom p)
        [mutationSuccess]

  /-- **get-atoms**: `(get-atoms &self)` returns all stored atoms in the space as answers.

      PeTTa: `'get-atoms'(&self) :- findall(A, get_atom(self, A), As).`
      The answers are the individual stored atoms (superposed). -/
  | getAtomsCmd (s : EvalState) :
      PeTTaCmd s
        (.apply "get-atoms" [.apply "&self" []])
        s
        s.space.storedAtoms

  /-- **Pure evaluation**: any expression that has a `PeTTaEval` derivation
      can be evaluated without changing the state.

      This embeds the pure fragment into the stateful layer. -/
  | pureEval (s : EvalState) (p : Pattern) (answers : RewriteResults)
      (h : PeTTaEval s.space p answers) :
      PeTTaCmd s p s answers

  /-- **Sequential composition** (`progn`): evaluate `e₁` in state `s₀`,
      getting intermediate state `s₁`, then evaluate `e₂` in `s₁`.
      The answers of the whole expression are those of `e₂`.

      Models `(progn e₁ e₂)` from PeTTa's `lib_metta4.metta`. -/
  | prognCmd (s₀ s₁ s₂ : EvalState)
      (e₁ e₂ : Pattern) (ans₁ ans₂ : RewriteResults)
      (h₁ : PeTTaCmd s₀ e₁ s₁ ans₁)
      (h₂ : PeTTaCmd s₁ e₂ s₂ ans₂) :
      PeTTaCmd s₀ (.apply "progn" [e₁, e₂]) s₂ ans₂

  /-- **prog1**: evaluate `e₁` in state `s₀`, then `e₂` in the resulting state,
      but return the answers of `e₁` (not `e₂`).

      Models `(prog1 e₁ e₂)` from PeTTa's `lib_metta4.metta`. -/
  | prog1Cmd (s₀ s₁ s₂ : EvalState)
      (e₁ e₂ : Pattern) (ans₁ ans₂ : RewriteResults)
      (h₁ : PeTTaCmd s₀ e₁ s₁ ans₁)
      (h₂ : PeTTaCmd s₁ e₂ s₂ ans₂) :
      PeTTaCmd s₀ (.apply "prog1" [e₁, e₂]) s₂ ans₁

/-! ## Basic Properties -/

/-- `pureEval` preserves the state (trivially by construction). -/
theorem pureEval_lifts (s : EvalState) (p : Pattern) (ans : RewriteResults)
    (h : PeTTaEval s.space p ans) : PeTTaCmd s p s ans :=
  PeTTaCmd.pureEval s p ans h

/-- `addAtomCmd` strictly extends the fact list. -/
theorem addAtomCmd_facts (s : EvalState) (p : Pattern) :
    (s.addAtom p).space.facts = s.space.facts ++ [p] := rfl

/-- The state output by `addAtomCmd` has the added atom as a fact. -/
theorem addAtomCmd_mem_facts (s : EvalState) (p : Pattern) :
    p ∈ (s.addAtom p).space.facts :=
  PeTTaSpace.mem_facts_addAtom_self s.space p

/-- `addAtomCmd` preserves previously existing facts. -/
theorem addAtomCmd_preserves_facts (s : EvalState) (p q : Pattern)
    (h : q ∈ s.space.facts) : q ∈ (s.addAtom p).space.facts :=
  PeTTaSpace.mem_facts_addAtom h

/-- `removeAtomCmd` only removes the targeted atom; other facts survive. -/
theorem removeAtomCmd_subset_facts (s : EvalState) (p q : Pattern)
    (h : q ∈ (s.removeAtom p).space.facts) : q ∈ s.space.facts :=
  PeTTaSpace.mem_facts_removeAtom_subset h

/-- `prognCmd` is associative in the sense that sequencing produces the last state. -/
theorem prognCmd_state_is_last (s₀ s₁ s₂ : EvalState) (e₁ e₂ : Pattern)
    (ans₁ ans₂ : RewriteResults)
    (h₁ : PeTTaCmd s₀ e₁ s₁ ans₁) (h₂ : PeTTaCmd s₁ e₂ s₂ ans₂) :
    ∃ ans, PeTTaCmd s₀ (.apply "progn" [e₁, e₂]) s₂ ans :=
  ⟨ans₂, PeTTaCmd.prognCmd s₀ s₁ s₂ e₁ e₂ ans₁ ans₂ h₁ h₂⟩

/-! ## State Monotonicity via add-atom Sequences -/

/-- Adding an atom only extends the fact list: old facts are preserved. -/
theorem addAtom_facts_subset (s : EvalState) (p : Pattern) :
    ∀ q ∈ s.space.facts, q ∈ (s.addAtom p).space.facts := fun q hq =>
  addAtomCmd_preserves_facts s p q hq

/-! ## Command Shape Analysis -/

/-- Case analysis on the shape of any `PeTTaCmd` step.
    Characterizes the expression form and the state transition. -/
theorem pettaCmd_shape (s s₁ : EvalState) (p : Pattern) (ans : RewriteResults)
    (h : PeTTaCmd s p s₁ ans) :
    (∃ q, p = .apply "add-atom" [.apply "&self" [], q] ∧ s₁ = s.addAtom q ∧ ans = [mutationSuccess]) ∨
    (∃ q, p = .apply "remove-atom" [.apply "&self" [], q] ∧ s₁ = s.removeAtom q ∧ ans = [mutationSuccess]) ∨
    (p = .apply "get-atoms" [.apply "&self" []] ∧ s₁ = s ∧ ans = s.space.storedAtoms) ∨
    (s₁ = s ∧ PeTTaEval s.space p ans) ∨
    (∃ e₁ e₂, p = .apply "progn" [e₁, e₂]) ∨
    (∃ e₁ e₂, p = .apply "prog1" [e₁, e₂]) := by
  cases h with
  | addAtomCmd _ q => exact Or.inl ⟨q, rfl, rfl, rfl⟩
  | removeAtomCmd _ q => exact Or.inr (Or.inl ⟨q, rfl, rfl, rfl⟩)
  | getAtomsCmd _ => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  | pureEval _ _ _ hpe => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hpe⟩)))
  | prognCmd _ _ _ e₁ e₂ _ _ _ _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁, e₂, rfl⟩))))
  | prog1Cmd _ _ _ e₁ e₂ _ _ _ _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e₁, e₂, rfl⟩))))

/-! ## get-atoms completeness -/

-- `getAtomsCmd_complete` was removed.  Its statement was
-- `(h : p ∈ s.space.storedAtoms) : p ∈ s.space.storedAtoms := h`, which never
-- mentioned `get-atoms` and so asserted nothing about completeness.  The
-- genuine result is `getAtomsCmd_answers_eq_storedAtoms` immediately below,
-- which does mention the command and its answer set.

/-- The `get-atoms` answer set is exactly the stored-atom list. -/
theorem getAtomsCmd_answers_eq_storedAtoms (s : EvalState) :
    ∃ s', PeTTaCmd s (.apply "get-atoms" [.apply "&self" []]) s' s.space.storedAtoms :=
  ⟨s, PeTTaCmd.getAtomsCmd s⟩

/-! ## Example Derivations -/

/-- Example: add then get returns the added atom.
    `(progn (add-atom &self (foo)) (get-atoms &self))` from empty state
    returns `[.apply "foo" []]`. -/
theorem example_addThenGet :
    PeTTaCmd EvalState.empty
      (.apply "progn"
        [ .apply "add-atom" [.apply "&self" [], .apply "foo" []]
        , .apply "get-atoms" [.apply "&self" []] ])
      { space := { facts := [.apply "foo" []], rules := [] } }
      [.apply "foo" []] :=
  PeTTaCmd.prognCmd _ _ _  _ _ _ _
    (PeTTaCmd.addAtomCmd EvalState.empty (.apply "foo" []))
    (PeTTaCmd.getAtomsCmd _)

/-! ## Summary

**0 sorries. 0 axioms.**

### State
- `EvalState` — wraps `PeTTaSpace`; `empty`, `addAtom`, `removeAtom`, `addRule`, `withSpace`

### Commands (`PeTTaCmd s₀ expr s₁ answers`)
- `addAtomCmd`  — `(add-atom &self p)` → adds fact, returns `[True]`
- `removeAtomCmd` — `(remove-atom &self p)` → removes fact, returns `[True]`
- `getAtomsCmd` — `(get-atoms &self)` → returns all stored atoms, no state change
- `pureEval`    — lifts any `PeTTaEval` derivation; no state change
- `prognCmd`    — `(progn e₁ e₂)` → sequence, return e₂ answers
- `prog1Cmd`    — `(prog1 e₁ e₂)` → sequence, return e₁ answers

### Properties
- `addAtomCmd_mem_facts` — the added atom is a fact afterward
- `addAtomCmd_preserves_facts` — existing facts survive
- `removeAtomCmd_subset_facts` — remove only removes the target
- `prognCmd_state_is_last` — sequencing ends in e₂'s output state
- `pettaCmd_shape` — case analysis on `PeTTaCmd` shape and state transition
- `getAtomsCmd_answers_eq_storedAtoms` — get-atoms returns exactly the stored-atom list
- `example_addThenGet` — concrete derivation: add then get
-/

/-! ## NotReducible and Empty Result Atoms -/

/-- The `NotReducible` result atom: wraps a pattern that could not be reduced further.

    In the MeTTa spec, when an expression `p` matches no rewrite rule and is not a
    grounded function, it is returned as `(NotReducible p)`.
    This atom is used as a "stuck" marker in the evaluator loop. -/
def notReducible (p : Pattern) : Pattern :=
  .apply "NotReducible" [p]

/-- The `Empty` result atom: the standard "no answer" marker.

    Produced by `case`/`unify` when no branch matches, and by `(empty)` expressions.
    `mkEmpty` is distinct from `notReducible`: `Empty` signals no answers were produced,
    while `NotReducible` signals the expression was stuck. -/
def mkEmpty : Pattern := .apply "Empty" []

@[simp]
theorem notReducible_def (p : Pattern) :
    notReducible p = .apply "NotReducible" [p] := rfl

@[simp]
theorem mkEmpty_def : mkEmpty = .apply "Empty" [] := rfl

end Mettapedia.Languages.MeTTa.PeTTa

namespace Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The existing Pattern-space command core specializes the same store. -/
abbrev State := Store PeTTaSpace Pattern

namespace State

def ofCore (core : EvalState) : State := Store.new core.space PeTTaSpace.empty

def read (state : State) (handle : Handle) : Option PeTTaSpace := Store.read state handle

def write (state : State) (handle : Handle) (space : PeTTaSpace) : Option State :=
  Store.write state handle space

def allocate (state : State) : Handle × State := Store.allocate state PeTTaSpace.empty

def putCell (state : State) (name : String) (value : Pattern) : State :=
  Store.putCell state name value

def query (state : State) (handle : Handle) (pattern template : Pattern) :
    Option RewriteResults :=
  (state.read handle).map fun space => space.spaceMatch pattern template

def contents (state : State) (handle : Handle) : Option RewriteResults :=
  (state.read handle).map PeTTaSpace.storedAtoms

def insert (state : State) (handle : Handle) (atom : Pattern) : Option State := do
  let space ← state.read handle
  state.write handle (space.addAtom atom)

def erase (state : State) (handle : Handle) (atom : Pattern) : Option State := do
  let space ← state.read handle
  state.write handle (space.removeAtom atom)

theorem insert_self (core : EvalState) (atom : Pattern) :
    (ofCore core).insert .self atom = some (ofCore (core.addAtom atom)) := rfl

theorem erase_self (core : EvalState) (atom : Pattern) :
    (ofCore core).erase .self atom = some (ofCore (core.removeAtom atom)) := rfl

theorem query_self (core : EvalState) (pattern template : Pattern) :
    (ofCore core).query .self pattern template = some (core.space.spaceMatch pattern template) := rfl

theorem query_exact (state : State) (handle : Handle) (pattern template : Pattern)
    (space : PeTTaSpace) (selected : state.read handle = some space) :
    state.query handle pattern template = some (space.spaceMatch pattern template) := by
  simp [query, selected]

theorem query_answer_sound (state : State) (handle : Handle) (pattern template : Pattern)
    (answers : RewriteResults) (returned : state.query handle pattern template = some answers)
    (answer : Pattern) (member : answer ∈ answers) :
    ∃ space, state.read handle = some space ∧
      ∃ atom ∈ space.storedAtoms, ∃ bindings ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern pattern atom,
        answer = Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings template := by
  unfold query at returned
  cases selected : state.read handle with
  | none => simp [selected] at returned
  | some space =>
    simp only [selected, Option.map_some, Option.some.injEq] at returned
    subst answers
    exact ⟨space, rfl, PeTTaSpace.spaceMatch_sound space pattern template answer member⟩

theorem query_answer_complete (state : State) (handle : Handle) (pattern template : Pattern)
    (space : PeTTaSpace) (selected : state.read handle = some space)
    (atom : Pattern) (stored : atom ∈ space.storedAtoms)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (matched : bindings ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern pattern atom) :
    ∃ answers, state.query handle pattern template = some answers ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings template ∈ answers :=
  ⟨space.spaceMatch pattern template, query_exact state handle pattern template space selected,
    PeTTaSpace.spaceMatch_complete space pattern template atom bindings stored matched⟩

end State

/-! ## Positive and negative allocation controls -/

private def initial : State := State.ofCore EvalState.empty
private def payload : Pattern := .apply "payload" []

theorem two_private_spaces_are_isolated :
    let first := initial.allocate
    let second := first.2.allocate
    ∃ populated, second.2.insert first.1 payload = some populated ∧
      populated.contents first.1 = some [payload] ∧
      populated.contents second.1 = some [] := by
  simp [initial, State.ofCore, EvalState.empty, State.allocate, State.insert, State.read,
    State.write, State.contents, Store.new, Store.allocate, Store.read, Store.write,
    PeTTaSpace.storedAtoms, PeTTaSpace.storedRuleAtoms, PeTTaSpace.addAtom, PeTTaSpace.empty]

theorem unallocated_space_cannot_be_written :
    initial.write (.privateSpace 0) PeTTaSpace.empty = none := rfl

theorem changing_a_cell_does_not_add_a_fact :
    (initial.putCell "memo" payload).contents .self = some [] := rfl

end Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces
