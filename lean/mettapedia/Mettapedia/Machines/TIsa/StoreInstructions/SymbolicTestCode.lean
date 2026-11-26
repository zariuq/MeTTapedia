import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPortCode

/-!
# Compiling the determinate part of a symbolic firing

The first refusal exits before the continuation. Until that
continuation starts, no occurrence is taken or made. The pending
level holds the original information, its principal answer, the
settled collect sets, and the open output terms.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicTestCode

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (Check)
open Derivation (Match Store)
open SymbolicExecution (Atom Work Equations Frame Code Goal profile test)
open SymbolicPortCode (passReg)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def emit (level : ℕ) : List (Goal σ) → Code σ → Code σ
  | [], next => next
  | first :: rest, next =>
    .seq (.instruction (.transform (.test first level passReg)))
      (.branch passReg (emit level rest next) (.ret .refused passReg))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def apply (base : Equations σ) (store : Store (Term σ)) :
    List (Goal σ) → Match (Term σ) (Work σ) → Option (Match (Term σ) (Work σ))
  | [], entry => some entry
  | first :: rest, entry => (test base store first entry).bind (apply base store rest)

theorem execute_emit (base : Equations σ) (state : Frame σ) (level : ℕ)
    (goals : List (Goal σ)) (next : Code σ) :
    match apply base state.store goals (state.levels level) with
    | none => ∃ stopped, stopped.store = state.store ∧ SameFuel state stopped ∧
        SymbolicExecution.execute base state (emit level goals next) = .returned .refused 0 stopped
    | some matched => ∃ staged, staged.store = state.store ∧ SameFuel state staged ∧ staged.levels level = matched ∧
        SymbolicExecution.execute base state (emit level goals next) = SymbolicExecution.execute base staged next := by
  induction goals generalizing state with
  | nil => exact ⟨state, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
  | cons first rest ih =>
    cases tested : test base state.store first (state.levels level) with
    | none =>
      let stopped := state.write passReg 0
      have firstStep : SymbolicExecution.execute base state (.instruction (.transform (.test first level passReg))) =
          .continuing stopped := by
        simp only [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, profile, tested]; rfl
      have flag : stopped.machine.registers passReg = 0 := by simp [stopped, StoreInstructions.State.write, P1WordExecution.State.write]
      have clear : (0 : Word) ≠ 1 := by decide
      simp only [apply, tested, Option.bind_none]
      refine ⟨stopped, rfl, ⟨rfl, rfl⟩, ?_⟩
      change (SymbolicExecution.execute base state (.instruction (.transform (.test first level passReg)))).thenContinue
        (fun s => SymbolicExecution.execute base s (.branch passReg (emit level rest next) (.ret .refused passReg))) = _
      rw [firstStep, Flow.thenContinue]
      simp only [executeWith, flag, clear, if_false, if_true]
    | some passing =>
      let prepared := (state.setLevel level passing).write passReg 1
      have firstStep : SymbolicExecution.execute base state (.instruction (.transform (.test first level passReg))) =
          .continuing prepared := by
        simp only [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, profile, tested]; rfl
      have flag : prepared.machine.registers passReg = 1 := by
        simp [prepared, StoreInstructions.State.write, P1WordExecution.State.write]
      have saved : prepared.levels level = passing := by
        simp [prepared, StoreInstructions.State.setLevel, StoreInstructions.State.write]
      have small := ih prepared
      change (match apply base prepared.store rest (prepared.levels level) with
        | none => ∃ stopped, stopped.store = prepared.store ∧ SameFuel prepared stopped ∧
            SymbolicExecution.execute base prepared (emit level rest next) = .returned .refused 0 stopped
        | some matched => ∃ staged, staged.store = prepared.store ∧ SameFuel prepared staged ∧ staged.levels level = matched ∧
            SymbolicExecution.execute base prepared (emit level rest next) = SymbolicExecution.execute base staged next) at small
      have sameStore : prepared.store = state.store := rfl
      rw [saved, sameStore] at small
      have step :
          SymbolicExecution.execute base state (emit level (first :: rest) next) =
            SymbolicExecution.execute base prepared (emit level rest next) := by
        change (SymbolicExecution.execute base state (.instruction (.transform (.test first level passReg)))).thenContinue
          (fun s => SymbolicExecution.execute base s (.branch passReg (emit level rest next) (.ret .refused passReg))) = _
        rw [firstStep, Flow.thenContinue]
        simp only [executeWith, flag, if_true]
      change (match apply base state.store (first :: rest) (state.levels level) with
        | none => ∃ stopped, stopped.store = state.store ∧ SameFuel state stopped ∧
            SymbolicExecution.execute base state (emit level (first :: rest) next) = .returned .refused 0 stopped
        | some matched => ∃ staged, staged.store = state.store ∧ SameFuel state staged ∧ staged.levels level = matched ∧
            SymbolicExecution.execute base state (emit level (first :: rest) next) = SymbolicExecution.execute base staged next)
      simp only [apply, tested, Option.bind_some, step]
      have free : SameFuel state prepared := ⟨rfl, rfl⟩
      cases tried : apply base state.store rest passing with
      | none =>
        rw [tried] at small
        obtain ⟨stopped, same, fuel, ran⟩ := small
        exact ⟨stopped, same, free.trans fuel, ran⟩
      | some matched =>
        rw [tried] at small
        obtain ⟨staged, same, fuel, level, ran⟩ := small
        exact ⟨staged, same, free.trans fuel, level, ran⟩

theorem apply_append (base : Equations σ) (store : Store (Term σ))
    (first second : List (Goal σ)) (entry : Match (Term σ) (Work σ)) :
    apply base store (first ++ second) entry = (apply base store first entry).bind (apply base store second) := by
  induction first generalizing entry with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.cons_append, apply, Option.bind_assoc]
    congr 1
    funext m
    exact ih m

def tells (equations : Equations σ) : List (Goal σ) := equations.map fun (left, right) => .perform (.tell left right)
def checks (conditions : List (Check (Term σ))) : List (Goal σ) := conditions.map fun condition => .perform (.check condition)
def collects (patterns : List (Term σ)) : List (Goal σ) := patterns.map fun pattern => .perform (.collect pattern)
def makes (terms : List (Term σ)) : List (Goal σ) := terms.map fun template => .perform (.produce template)

def afterTells (entry : Match (Term σ) (Work σ)) (equations : Equations σ) : Match (Term σ) (Work σ) :=
  match equations with
  | [] => entry
  | _ :: _ => {entry with bindings := ⟨equations.reverse ++ entry.bindings.newer, none⟩}

theorem apply_tells (base : Equations σ) (store : Store (Term σ))
    (equations : Equations σ) (entry : Match (Term σ) (Work σ)) :
    apply base store (tells equations) entry = some (afterTells entry equations) := by
  induction equations generalizing entry with
  | nil => rfl
  | cons eq more ih =>
    change apply base store (tells more) {entry with bindings := entry.bindings.extend eq} = _
    rw [ih]
    cases more <;> simp [afterTells, Work.extend, List.reverse_cons, List.append_assoc]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem afterTells_problem (base : Equations σ) (entry : Match (Term σ) (Work σ)) (equations : Equations σ) :
    (afterTells entry equations).bindings.problem base = entry.bindings.problem base ++ equations := by
  cases equations <;> simp [afterTells, Work.problem, List.reverse_append, List.append_assoc]

theorem apply_checks (base : Equations σ) (store : Store (Term σ)) (answer : Subst σ)
    (conditions : List (Check (Term σ))) (entry : Match (Term σ) (Work σ))
    (resolved : entry.bindings.answer = some answer) :
    apply base store (checks conditions) entry =
      if conditions.all (SymbolicExecution.guard answer store.occurrences) then some entry else none := by
  induction conditions with
  | nil => rfl
  | cons condition later ih =>
    change ((test base store (.perform (.check condition)) entry).bind (apply base store (checks later))) = _
    cases accepted : SymbolicExecution.guard answer store.occurrences condition <;>
      simp [test, resolved, accepted, ih]

theorem apply_collects (base : Equations σ) (store : Store (Term σ)) (answer : Subst σ)
    (patterns : List (Term σ)) (entry : Match (Term σ) (Work σ))
    (resolved : entry.bindings.answer = some answer) :
    apply base store (collects patterns) entry =
      (patterns.mapM (SymbolicExecution.collect answer store.occurrences)).rec none
        (fun groups => some {entry with seen := entry.seen ++ groups}) := by
  induction patterns generalizing entry with
  | nil => simp [collects, apply]
  | cons pattern tail ih =>
    cases read : SymbolicExecution.collect answer store.occurrences pattern with
    | none => simp [collects, apply, test, resolved, read]
    | some selected =>
      change ((test base store (.perform (.collect pattern)) entry).bind (apply base store (collects tail))) = _
      let bumped := {entry with seen := entry.seen ++ [selected]}
      rw [show test base store (.perform (.collect pattern)) entry = some bumped by
        simp [test, resolved, read, bumped], Option.bind_some, ih bumped resolved, List.mapM_cons, read]
      cases tail.mapM (SymbolicExecution.collect answer store.occurrences) with
      | none => rfl
      | some groups => simp [bumped, List.append_assoc]

theorem apply_makes (base : Equations σ) (store : Store (Term σ)) (answer : Subst σ)
    (terms : List (Term σ)) (entry : Match (Term σ) (Work σ)) (resolved : entry.bindings.answer = some answer) :
    apply base store (makes terms) entry = some {entry with made := entry.made ++ terms} := by
  induction terms generalizing entry with
  | nil => simp [makes, apply]
  | cons first rest ih =>
    change ((test base store (.perform (.produce first)) entry).bind (apply base store (makes rest))) = _
    let bumped := {entry with made := entry.made ++ [first]}
    rw [show test base store (.perform (.produce first)) entry = some bumped by
      simp [test, resolved, bumped], Option.bind_some, ih bumped resolved]
    simp only [bumped, List.append_assoc]
    rfl

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicTestCode
