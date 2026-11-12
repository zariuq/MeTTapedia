import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Candidate presentations of an existing effect core

A program selects and compiles candidates of an existing step. This change
of candidate presentation retains its states, frame action, resource update
and knowledge contracts. Additional permission is independent of preparation.
Candidate identities remain in the new event/run type even when compilation
maps two of them to the same underlying effect.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uG

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {Candidate : State → Type uG}

namespace EffectCore

/-- Reindex candidates without changing the effect or its preparation evidence. -/
def reindexCandidates (core : EffectCore X O State Firing)
    (compile : {state : State} → Candidate state → Firing state) :
    EffectCore X O State Candidate where
  frame := core.frame
  knowledge := core.knowledge
  present := core.present
  selection candidate := core.selection (compile candidate)
  target candidate := core.target (compile candidate)
  extension candidate := core.extension (compile candidate)
  information candidate := core.information (compile candidate)
  information_refines candidate := core.information_refines (compile candidate)
  Shapes candidate := core.Shapes (compile candidate)
  preparedResult candidate := core.preparedResult (compile candidate)
  present_preparedResult candidate := core.present_preparedResult (compile candidate)
  preparedSettle candidate := core.preparedSettle (compile candidate)
  result_refines candidate := core.result_refines (compile candidate)

end EffectCore

namespace Step

namespace Run

variable (step : Step X O State Firing)

theorem last_cast {source target : State} (same : source = target) (run : step.Run source) :
    (same ▸ run).last = run.last := by
  cases same
  rfl

theorem word_cast {source target : State} (same : source = target) (run : step.Run source) :
    (same ▸ run).word = run.word := by
  cases same
  rfl

/-- A complete word retains states and full candidates, so it determines
the execution. This says nothing about a coarser observation of that word. -/
theorem eq_of_word_eq {state : State} (first : step.Run state) :
    ∀ second : step.Run state, first.word = second.word → first = second := by
  induction first with
  | nil state =>
      intro second same
      cases second with
      | nil => rfl
      | cons candidate admitted rest => cases same
  | @cons state candidate admitted rest ih =>
      intro second same
      cases second with
      | nil => cases same
      | cons other allowed tail =>
          have words := List.cons.inj same
          have candidates : candidate = other := eq_of_heq (Sigma.mk.inj words.1).2
          subst other
          have tails := ih tail words.2
          subst tail
          rfl

end Run

/-- A presented program uses the existing admission and an independent
permission predicate on its own retained candidate identity. -/
def reindexCandidates (step : Step X O State Firing)
    (compile : {state : State} → Candidate state → Firing state)
    (permission : {state : State} → Candidate state → Prop) :
    Step X O State Candidate where
  toEffectCore := step.effectCore.reindexCandidates compile
  Admits candidate := step.Admits (compile candidate) ∧ permission candidate
  admitted_prepares _candidate admitted := step.prepares admitted.1

variable (step : Step X O State Firing)
  (compile : {state : State} → Candidate state → Firing state)
  (permission : {state : State} → Candidate state → Prop)

theorem reindexCandidates_admits_iff {state : State} (candidate : Candidate state) :
    (step.reindexCandidates compile permission).Admits candidate ↔
      step.Admits (compile candidate) ∧ permission candidate := Iff.rfl

theorem reindexCandidates_result {state : State} (candidate : Candidate state)
    (admitted : (step.reindexCandidates compile permission).Admits candidate) :
    (step.reindexCandidates compile permission).result candidate admitted =
      step.result (compile candidate) admitted.1 := rfl

/-- Complete executions map to complete executions with the same states.
Only this explicitly requested map forgets the presented candidate identity. -/
def compileRun : {state : State} →
    (step.reindexCandidates compile permission).Run state → step.Run state
  | _, .nil state => .nil state
  | _, .cons candidate admitted rest =>
      .cons (compile candidate) admitted.1 (compileRun rest)

theorem compileRun_last : {state : State} →
    (run : (step.reindexCandidates compile permission).Run state) →
      (step.compileRun compile permission run).last = run.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => compileRun_last rest

theorem compileRun_word : {state : State} →
    (run : (step.reindexCandidates compile permission).Run state) →
      (step.compileRun compile permission run).word =
        run.word.map (fun event => ⟨event.1, compile event.2⟩)
  | _, .nil _ => rfl
  | state, .cons candidate _ rest => by
      simp only [compileRun, Run.word, List.map_cons]
      exact congrArg (List.cons (⟨state, compile candidate⟩ : Σ next : State, Firing next))
        (compileRun_word rest)

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
