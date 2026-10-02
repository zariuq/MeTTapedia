import Mettapedia.Languages.TuringMachine.OneSort
import Mettapedia.Languages.TuringMachine.Steps
import Mettapedia.GSLT.LanguageDef.Contexts.Structural

/-!
# Presentation versus encoding, for a Turing machine

A Turing machine has no interactive presentation.  It can nevertheless be
run inside an interactive theory, and the two facts do not conflict.

The interactive theory is the machine read at one sort.  The map of
declarations from the machine into it is a morphism of theories: it preserves
and reflects the transitions that contexts label, so what every probe of the
machine sees is preserved.  It is hosting: it identifies no two terms of the
machine.  The host runs the machine.

It is not exhausting.  The host has terms that are the image of no term of
the machine, a state running on a state among them, and so it has contexts
that the machine cannot assemble.  The interaction sites of the host are
sites of the host: a fact about them is a fact about the one-sort theory,
and the machine itself still has no site at which two things of one sort
meet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.SortMerging
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## A morphism of theories -/

/-- **Every reduction of the image of a term of the machine is the image of a
reduction of that term.**  The two presentations have the same steps on
patterns, and a step of the machine preserves sorts. -/
theorem toOneSort_reflectsSteps (machine : Machine) : ReflectsSteps base (toOneSort machine) :=
  reflectsSteps_of_equationFree base (toOneSort machine) (turingMachine_equationFree machine)
    (oneSortMachine_equationFree machine) (by
      intro interface term next step
      have image : Step base (oneSortMachine machine) term.1 next := by
        have raw : Step base (oneSortMachine machine) (mapPattern oneSort term.1) next := step
        rwa [mapPattern_mergeSorts] at raw
      have sourceStep : Step base (turingMachine machine) term.1 next :=
        (oneSort_step_iff machine).mp image
      exact ⟨⟨next, step_sorted sourceStep term.2⟩, sourceStep,
        (mapPattern_mergeSorts _ _).symm⟩)

/-- **The map from a machine to its one-sort presentation is a morphism of
theories.** -/
def hostingMorphism (machine : Machine) :
    ContextMorphism (contextTheory base (naive machine))
      (contextTheory base (oneSorted machine)) :=
  structuralContextMorphism_of_reflects (toOneSort machine) rfl
    (mergeSorts_fixesDeclaredUnits _ _) (toOneSort_reflectsSteps machine)

/-- The morphism preserves the transitions that contexts label. -/
theorem hostingMorphism_preservesTransitions (machine : Machine) :
    (hostingMorphism machine).toContextMap.PreservesTransitions :=
  structuralContextMap_preservesTransitions base (toOneSort machine)
    (preservesEquations_default (toOneSort machine) rfl (mergeSorts_fixesDeclaredUnits _ _))
    (preservesSteps_default (toOneSort machine) rfl (mergeSorts_fixesDeclaredUnits _ _))

/-- The morphism reflects the transitions of images along images of
contexts. -/
theorem hostingMorphism_reflectsTransitions (machine : Machine) :
    (hostingMorphism machine).toContextMap.ReflectsTransitions :=
  structuralContextMap_reflectsTransitions base (toOneSort machine)
    (preservesEquations_default (toOneSort machine) rfl (mergeSorts_fixesDeclaredUnits _ _))
    (toOneSort_reflectsSteps machine)

/-! ## Hosting -/

/-- The morphism is faithful: it identifies no two terms of the machine. -/
theorem hostingMorphism_faithful (machine : Machine) :
    (hostingMorphism machine).toContextMap.Faithful := by
  apply (ContextMap.faithful_iff_reflectsEquations _).mpr
  intro origin first second equivalent
  have same := (termSetoid_iff_eq base _ (oneSortMachine_equationFree machine) _ _).mp
    equivalent
  have patterns : first.1 = second.1 := by
    have raw : mapPattern oneSort first.1 = mapPattern oneSort second.1 :=
      congrArg Subtype.val same
    rwa [mapPattern_mergeSorts, mapPattern_mergeSorts] at raw
  have equal : first = second := Subtype.ext patterns
  rw [equal]

/-- The machine is hosted faithfully, with forward transition transport and
backward lifting along the images of its contexts. -/
theorem hostingMorphism_hosting (machine : Machine) :
    (hostingMorphism machine).toContextMap.Hosting :=
  ⟨hostingMorphism_faithful machine, hostingMorphism_preservesTransitions machine,
    hostingMorphism_reflectsTransitions machine⟩

/-! ## Not exhausting -/

/-- The interface of the configurations of the machine. -/
def configurations : Interface where
  type := .base "Config"
  stage := []

/-- The state numbered zero, at the one sort. -/
theorem oneSort_zero_typed (machine : Machine) :
    HasType (oneSortMachine machine) FreeTypeContext.empty [] (stateTerm 0) (.base "Config") :=
  HasType.constructor (rule := oneSortTerms[0]) (List.getElem_mem (l := oneSortTerms) (by decide))
    (by rintro ⟨name, kind, element, shape⟩; cases shape) .nil

/-- **A state running on a state**: a term of the one-sort presentation at
the image of the interface of configurations. -/
def stateOnState (machine : Machine) :
    Term (oneSortMachine machine) (configurations.map oneSort) :=
  ⟨run (stateTerm 0) (stateTerm 0),
    HasType.constructor (rule := oneSortTerms[7])
      (List.getElem_mem (l := oneSortTerms) (by decide))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl (oneSort_zero_typed machine)
        (.cons trivial rfl (oneSort_zero_typed machine) .nil)),
    by decide, by decide, by
      show Pattern.isWellScopedAt 0 (run (stateTerm 0) (stateTerm 0)) = true
      decide⟩

/-- A state is not a tape: no term of the machine is a state running on a
state. -/
theorem not_stateOnState (machine : Machine) {interface : Interface}
    (term : Term (turingMachine machine) interface) :
    term.1 ≠ run (stateTerm 0) (stateTerm 0) := by
  intro shape
  have typed := term.2.1
  rw [shape] at typed
  obtain ⟨-, -, tapeTyped⟩ := hasType_run_iff.mp typed
  obtain ⟨rule, member, label, sortEq, -, -⟩ := tapeTyped.apply_inv
  obtain rfl := rule_eq_of_label machine member (other := terms[0])
    (List.getElem_mem (l := terms) (by decide)) label
  revert sortEq
  decide

/-- **The morphism is not exhausting**: a state running on a state is the
image of no term of the machine. -/
theorem hostingMorphism_not_exhausting (machine : Machine) :
    ¬ (hostingMorphism machine).toContextMap.Exhausting := by
  intro exhausting
  obtain ⟨preimage, equivalent⟩ := ContextMap.Exhausting.term_surjective _ exhausting
    (origin := configurations) (stateOnState machine)
  have same := (termSetoid_iff_eq base _ (oneSortMachine_equationFree machine) _ _).mp
    equivalent
  have patterns : run (stateTerm 0) (stateTerm 0) = mapPattern oneSort preimage.1 :=
    congrArg Subtype.val same
  rw [mapPattern_mergeSorts] at patterns
  exact not_stateOnState machine preimage patterns.symm

/-! ## The distinction -/

/-- **Presentation versus encoding.**  A Turing machine with at least one
table entry admits no interactive presentation; it maps into an interactive
theory by a morphism of theories that preserves and reflects transitions and
is hosting; and that theory has a term, hence a context, that the machine
cannot assemble.  Admitting an encoding into an interactive theory does not
give the machine a site of interaction. -/
theorem presentation_versus_encoding (machine : Machine)
    (nonempty : machine.transitions ≠ []) :
    ¬ AdmitsInteractivePresentation (turingMachine machine) ∧
      IsInteractive (oneSortMachine machine) ∧
      (hostingMorphism machine).toContextMap.PreservesTransitions ∧
      (hostingMorphism machine).toContextMap.ReflectsTransitions ∧
      (hostingMorphism machine).toContextMap.Hosting ∧
      ¬ (hostingMorphism machine).toContextMap.Exhausting :=
  ⟨turingMachine_not_interactive machine, oneSortMachine_isInteractive machine nonempty,
    hostingMorphism_preservesTransitions machine, hostingMorphism_reflectsTransitions machine,
    hostingMorphism_hosting machine, hostingMorphism_not_exhausting machine⟩

end Mettapedia.Languages.TuringMachine
