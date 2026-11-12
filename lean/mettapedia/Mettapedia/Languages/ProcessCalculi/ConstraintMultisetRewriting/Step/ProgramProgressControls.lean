import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramProgress
import Mettapedia.Machines.ProgressSearch

/-!
# A live recursive program and a resumable administrative prefix

The source profile's dynamic call rule repeatedly calls its own installed
definition and records a citation on each invocation. This supplies an actual
infinite source execution and, through the proved lifting, an infinite execution
of admitted occurrence firings. A lexical-binding prefix has two erased steps;
search suspends after those steps and resumes at the semantic binding event.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program.Progress.Controls

open Mettapedia.Machines.ProgressObservation
open ProgramRows ProgramTranslation

attribute [local instance] sourceQuiver

def key : Sx := .sym 101
def version : Sx := .sym 102
def value : Sx := .sym 103
def thread : Sx := ev (call key) nil nil
def definition : Sx := defn key version (call key)
def citation : Sx := cite key version

def loopWorld (n : ℕ) : World := thread ::ₘ definition ::ₘ Multiset.replicate n citation

def callEvent (n : ℕ) : SourceEvent (loopWorld n) (loopWorld (n + 1)) where
  rule := .call
  fired := by
    refine ⟨args [key, nil, nil, version, call key], Multiset.replicate n citation, rfl, ?_⟩
    change thread ::ₘ definition ::ₘ Multiset.replicate (n + 1) citation =
      thread ::ₘ citation ::ₘ definition ::ₘ Multiset.replicate n citation
    simp [Multiset.replicate_succ, Multiset.cons_swap]

def sourceLoop : Execution World where
  state := loopWorld
  event := callEvent

theorem source_loop_observed (n : ℕ) : sourceObservation (sourceLoop.event n) = some .call := rfl

theorem source_loop_count (n : ℕ) : sourceLoop.observedCount sourceObservation n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Execution.observedCount_succ, ih, source_loop_observed]
      rfl

noncomputable def occurrenceLoop : Execution State :=
  liftExecution sourceLoop (initialState [thread, definition]) rfl

theorem occurrence_loop_observed (n : ℕ) : observation (occurrenceLoop.event n) = some .call :=
  liftExecution_observation sourceLoop (initialState [thread, definition]) rfl n

theorem occurrence_loop_count (n : ℕ) : occurrenceLoop.observedCount observation n = n := by
  exact (liftExecution_counts sourceLoop (initialState [thread, definition]) rfl n).trans (source_loop_count n)

def bindingFrame : Sx := cons (letK (call key) nil) nil

def bindingStart : World := ev (let_ (atom value) (call key)) nil nil ::ₘ {definition}
def bindingFirst : World := ev (atom value) nil bindingFrame ::ₘ {definition}
def bindingSecond : World := ret (atom value) bindingFrame ::ₘ {definition}
def bindingThird : World := ev (call key) (cons (atom value) nil) nil ::ₘ {definition}

def bindingEvent : SourceEvent bindingStart bindingFirst where
  rule := .let_
  fired := ⟨args [atom value, call key, nil, nil], {definition}, rfl, rfl⟩

def atomEvent : SourceEvent bindingFirst bindingSecond where
  rule := .atom
  fired := ⟨args [value, nil, bindingFrame], {definition}, rfl, rfl⟩

def bindValueEvent : SourceEvent bindingSecond bindingThird where
  rule := .letK
  fired := ⟨args [atom value, call key, nil, nil], {definition}, rfl, rfl⟩

def firstCall : SourceEvent bindingThird (loopWorld 1) where
  rule := .call
  fired := by
    refine ⟨args [key, cons (atom value) nil, nil, version, call key], 0, rfl, ?_⟩
    change thread ::ₘ definition ::ₘ Multiset.replicate 1 citation =
      thread ::ₘ citation ::ₘ definition ::ₘ 0
    rw [Multiset.replicate_succ]
    exact congrArg (fun rest : World => thread ::ₘ rest) (Multiset.cons_swap definition citation 0)

def bindingWorld : ℕ → World
  | 0 => bindingStart
  | 1 => bindingFirst
  | 2 => bindingSecond
  | 3 => bindingThird
  | n + 4 => loopWorld (n + 1)

def bindingExecution : Execution World where
  state := bindingWorld
  event n := by
    cases n with
    | zero => exact bindingEvent
    | succ n => cases n with
      | zero => exact atomEvent
      | succ n => cases n with
        | zero => exact bindValueEvent
        | succ n => cases n with
          | zero => exact firstCall
          | succ n => exact callEvent (n + 1)

theorem two_bookkeeping_steps_suspend :
    seek sourceObservation bindingExecution 2 0 = .suspended 2 := rfl

theorem next_budget_finds_semantic_binding :
    resume sourceObservation bindingExecution (.suspended 2) 1 = .found 2 .letK := rfl

theorem combined_budget_agrees :
    seek sourceObservation bindingExecution 3 0 = .found 2 .letK := rfl

theorem zero_budget_is_not_absence :
    seek sourceObservation sourceLoop 0 0 = .suspended 0 ∧
      sourceObservation (sourceLoop.event 0) = some .call := ⟨rfl, rfl⟩

theorem unit_chunks_reach_binding :
    searchChunks sourceObservation bindingExecution (fun _ => 1) 0 3 = .found 2 .letK := rfl

theorem zero_chunks_do_not_progress (n : ℕ) :
    searchChunks sourceObservation sourceLoop (fun _ => 0) 0 n = .suspended 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [searchChunks, ih, resume, seek]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program.Progress.Controls
