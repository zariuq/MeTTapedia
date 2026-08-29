import Mettapedia.GSLT.LanguageDef.StatefulCalculusExtension

/-!
# Stateful incremental generation of flat calculus languages

An incremental generator consumes an ordered input stream while carrying the
minimum state needed to allocate stable names and avoid regenerating earlier
rows.  Each input emits an ordinary `CalculusLanguageExtension`; the generic
runner composes those deltas and applies their composite to one flat
`CalculusLanguageDef`.

This is a writer-state factorization of generation, not a second language
representation.  Its public artifact is the same flat calculus language used
by checking and compilation.  The append theorem is load-bearing: compiling
`first ++ second` continues the second segment from the state reached after
the first segment.  Restarting the state is observably different and is
rejected by the negative control below.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

universe uState uInput

/-- A deterministic stateful producer of flat calculus-language deltas. -/
structure IncrementalCalculusGenerator
    (State : Type uState) (Input : Type uInput) where
  /-- Consume one input and emit exactly the rows introduced at this step. -/
  step : State → Input → State × CalculusLanguageExtension

namespace IncrementalCalculusGenerator

variable {State : Type uState} {Input : Type uInput}

/-- One input as a lawful stateful extension arrow. -/
def stepArrow (generator : IncrementalCalculusGenerator State Input)
    (input : Input) : StatefulCalculusExtension State State where
  run state := generator.step state input

/-- The lawful composite arrow for an ordered input segment. -/
def inputArrow (generator : IncrementalCalculusGenerator State Input) :
    List Input → StatefulCalculusExtension State State
  | [] => .id
  | input :: inputs =>
      (generator.stepArrow input).comp (generator.inputArrow inputs)

/-- Run a generator from an explicit state, returning the final state and the
ordered composite of all emitted deltas. -/
def runFrom (generator : IncrementalCalculusGenerator State Input) :
    State → List Input → State × CalculusLanguageExtension
  | state, [] => (state, .empty)
  | state, input :: inputs =>
      let first := generator.step state input
      let rest := generator.runFrom first.1 inputs
      (rest.1, first.2.comp rest.2)

@[simp]
theorem runFrom_nil (generator : IncrementalCalculusGenerator State Input)
    (state : State) :
    generator.runFrom state [] = (state, .empty) :=
  rfl

@[simp]
theorem runFrom_cons (generator : IncrementalCalculusGenerator State Input)
    (state : State) (input : Input) (inputs : List Input) :
    generator.runFrom state (input :: inputs) =
      let first := generator.step state input
      let rest := generator.runFrom first.1 inputs
      (rest.1, first.2.comp rest.2) :=
  rfl

/-- Running a concatenated input is exactly sequential state threading and
extension composition. -/
theorem runFrom_append (generator : IncrementalCalculusGenerator State Input)
    (state : State) (first second : List Input) :
    generator.runFrom state (first ++ second) =
      let firstRun := generator.runFrom state first
      let secondRun := generator.runFrom firstRun.1 second
      (secondRun.1, firstRun.2.comp secondRun.2) := by
  induction first generalizing state with
  | nil =>
      simp [runFrom, CalculusLanguageExtension.empty_comp]
  | cons input inputs inductionHypothesis =>
      simp only [List.cons_append, runFrom_cons]
      generalize stepEquation : generator.step state input = firstStep
      rw [inductionHypothesis]
      simp only
      rw [CalculusLanguageExtension.comp_assoc]

/-- The recursive runner is exactly the interpretation of the input segment
through lawful stateful-arrow composition. -/
theorem inputArrow_run (generator : IncrementalCalculusGenerator State Input)
    (state : State) (inputs : List Input) :
    (generator.inputArrow inputs).run state =
      generator.runFrom state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs inductionHypothesis =>
      simp only [inputArrow, StatefulCalculusExtension.comp_run,
        stepArrow, runFrom_cons]
      generalize generator.step state input = first
      rw [inductionHypothesis]

/-- Input append is composition of the two corresponding stateful arrows. -/
theorem inputArrow_append
    (generator : IncrementalCalculusGenerator State Input)
    (first second : List Input) :
    generator.inputArrow (first ++ second) =
      (generator.inputArrow first).comp (generator.inputArrow second) := by
  apply StatefulCalculusExtension.ext
  intro state
  rw [inputArrow_run, runFrom_append]
  simp only [StatefulCalculusExtension.comp_run]
  rw [inputArrow_run, inputArrow_run]

/-- Compile an input stream to the single flat language consumed downstream. -/
def compileFrom (generator : IncrementalCalculusGenerator State Input)
    (base : CalculusLanguageDef) (state : State) (inputs : List Input) :
    CalculusLanguageDef :=
  (generator.runFrom state inputs).2.apply base

/-- Compilation is the flat-language action of the lawfully composed input
arrow; the state coordinate remains available to incremental clients. -/
theorem inputArrow_apply
    (generator : IncrementalCalculusGenerator State Input)
    (base : CalculusLanguageDef) (state : State) (inputs : List Input) :
    (generator.inputArrow inputs).apply state base =
      ((generator.runFrom state inputs).1,
        generator.compileFrom base state inputs) := by
  unfold StatefulCalculusExtension.apply compileFrom
  rw [inputArrow_run]

/-- Incremental compilation of a concatenated stream reuses the first
artifact and applies only the continuation delta produced from its final
state. -/
theorem compileFrom_append
    (generator : IncrementalCalculusGenerator State Input)
    (base : CalculusLanguageDef) (state : State)
    (first second : List Input) :
    generator.compileFrom base state (first ++ second) =
      let firstRun := generator.runFrom state first
      let secondRun := generator.runFrom firstRun.1 second
      secondRun.2.apply (firstRun.2.apply base) := by
  rw [compileFrom, runFrom_append]
  exact CalculusLanguageExtension.comp_apply _ _ _

/-- Every generated artifact contains its base as an exact prefix in all row
families. -/
theorem compileFrom_appendOnly
    (generator : IncrementalCalculusGenerator State Input)
    (base : CalculusLanguageDef) (state : State) (inputs : List Input) :
    CalculusLanguageExtension.AppendOnlyCalculusRefinement base
      (generator.compileFrom base state inputs) :=
  CalculusLanguageExtension.apply_appendOnly _ _

/-! ## State-threading controls -/

namespace Canary

private def stateName (index : Nat) : String :=
  String.ofList ("incremental-calculus:".toList ++ List.replicate index 's')

private def generator : IncrementalCalculusGenerator Nat Unit where
  step state _ :=
    (state + 1,
      { newTypes := [TypeDecl.plain (stateName state)] })

private def base : CalculusLanguageDef :=
  { name := "incremental-calculus"
    types := []
    terms := []
    equations := []
    rewrites := [] }

/-- Two inputs retain authored order and allocate two distinct state-indexed
rows in one flat language. -/
theorem two_steps_allocate_distinct_rows :
    (generator.compileFrom base 0 [(), ()]).types =
      [TypeDecl.plain (stateName 0), TypeDecl.plain (stateName 1)] := by
  simp [compileFrom, runFrom, generator, base,
    CalculusLanguageExtension.apply, CalculusLanguageExtension.comp,
    CalculusLanguageExtension.empty]

/-- Restarting the generator for the second segment is not incremental
compilation: it reuses the first wire name instead of continuing the state. -/
theorem restarting_state_changes_output :
    (generator.runFrom 0 [(), ()]).2 ≠
      (generator.runFrom 0 [()]).2.comp (generator.runFrom 0 [()]).2 := by
  intro equality
  have typeRows := congrArg CalculusLanguageExtension.newTypes equality
  simp [generator, runFrom, CalculusLanguageExtension.comp,
    CalculusLanguageExtension.empty, stateName, TypeDecl.plain] at typeRows

end Canary

#print axioms runFrom_append
#print axioms inputArrow_run
#print axioms inputArrow_append
#print axioms inputArrow_apply
#print axioms compileFrom_append
#print axioms compileFrom_appendOnly
#print axioms Canary.two_steps_allocate_distinct_rows
#print axioms Canary.restarting_state_changes_output

end IncrementalCalculusGenerator

end Mettapedia.GSLT.LanguageDef
