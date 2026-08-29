import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Stateful composition of flat calculus-language extensions

Some generated declarations depend on names allocated by earlier generation
steps.  Such stages cannot be composed by concatenating their completed
languages.  A stage is instead an arrow from an input state to an output
state together with a flat-language extension.  Sequential composition
threads the state and composes the emitted extensions in execution order.

The public artifact remains one `CalculusLanguageDef`: `apply` runs the arrow
and applies its accumulated extension.  `Interchange` is an explicit
certificate for the exceptional case where two stateful stages may be
reordered without changing either their final state or emitted extension.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

universe uSource uTarget uNext

/-- A state transition that emits an append-only flat-calculus delta. -/
structure StatefulCalculusExtension
    (Source : Type uSource) (Target : Type uTarget) where
  run : Source → Target × CalculusLanguageExtension

namespace StatefulCalculusExtension

variable {Source : Type uSource} {Target : Type uTarget}
  {Next : Type uNext}

@[ext]
theorem ext {first second : StatefulCalculusExtension Source Target}
    (run : ∀ state, first.run state = second.run state) : first = second := by
  cases first
  cases second
  congr
  funext state
  exact run state

/-- Identity stage: preserve state and emit no declaration. -/
def id : StatefulCalculusExtension Source Source where
  run state := (state, .empty)

/-- Execution-order composition.  The second stage sees the state produced by
the first, and its delta is applied after the first delta. -/
def comp (first : StatefulCalculusExtension Source Target)
    (second : StatefulCalculusExtension Target Next) :
    StatefulCalculusExtension Source Next where
  run source :=
    let firstResult := first.run source
    let secondResult := second.run firstResult.1
    (secondResult.1, firstResult.2.comp secondResult.2)

/-- Run a stateful extension and apply its emitted delta to one flat language. -/
def apply (extension : StatefulCalculusExtension Source Target)
    (source : Source) (base : CalculusLanguageDef) :
    Target × CalculusLanguageDef :=
  let result := extension.run source
  (result.1, result.2.apply base)

@[simp]
theorem id_run (state : Source) :
    (id : StatefulCalculusExtension Source Source).run state =
      (state, .empty) :=
  rfl

@[simp]
theorem comp_run (first : StatefulCalculusExtension Source Target)
    (second : StatefulCalculusExtension Target Next) (state : Source) :
    (first.comp second).run state =
      let firstResult := first.run state
      let secondResult := second.run firstResult.1
      (secondResult.1, firstResult.2.comp secondResult.2) :=
  rfl

/-- Identity is a left unit for state-threading composition. -/
theorem id_comp (extension : StatefulCalculusExtension Source Target) :
    (id : StatefulCalculusExtension Source Source).comp extension =
      extension := by
  apply ext
  intro state
  simp [comp, id, CalculusLanguageExtension.empty_comp]

/-- Identity is a right unit for state-threading composition. -/
theorem comp_id (extension : StatefulCalculusExtension Source Target) :
    extension.comp (id : StatefulCalculusExtension Target Target) =
      extension := by
  apply ext
  intro state
  simp [comp, id, CalculusLanguageExtension.comp_empty]

/-- Stateful extension composition is associative. -/
theorem comp_assoc
    {Final : Type*}
    (first : StatefulCalculusExtension Source Target)
    (second : StatefulCalculusExtension Target Next)
    (third : StatefulCalculusExtension Next Final) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply ext
  intro state
  simp only [comp_run]
  generalize firstEquation : first.run state = firstResult
  generalize secondEquation : second.run firstResult.1 = secondResult
  generalize thirdEquation : third.run secondResult.1 = thirdResult
  simp [CalculusLanguageExtension.comp_assoc]

/-- Applying identity leaves both state and flat language unchanged. -/
theorem id_apply (state : Source) (base : CalculusLanguageDef) :
    (id : StatefulCalculusExtension Source Source).apply state base =
      (state, base) := by
  simp [apply, id, CalculusLanguageExtension.empty_apply]

/-- The action of a composite is sequential application of the two stages. -/
theorem comp_apply
    (first : StatefulCalculusExtension Source Target)
    (second : StatefulCalculusExtension Target Next)
    (state : Source) (base : CalculusLanguageDef) :
    (first.comp second).apply state base =
      let firstResult := first.apply state base
      second.apply firstResult.1 firstResult.2 := by
  simp only [apply, comp]
  generalize firstEquation : first.run state = firstResult
  generalize secondEquation : second.run firstResult.1 = secondResult
  simp [CalculusLanguageExtension.comp_apply]

/-- Evidence that two endostages may be interchanged.  Both coordinates are
required: agreeing only on the final state may still reorder declarations. -/
structure Interchange
    (first second : StatefulCalculusExtension Source Source) : Prop where
  finalState : ∀ state,
    ((first.comp second).run state).1 =
      ((second.comp first).run state).1
  emittedExtension : ∀ state,
    ((first.comp second).run state).2 =
      ((second.comp first).run state).2

/-- An interchange certificate yields equality of the two composite arrows. -/
theorem comp_comm_of_interchange
    {first second : StatefulCalculusExtension Source Source}
    (interchange : Interchange first second) :
    first.comp second = second.comp first := by
  apply ext
  intro state
  apply Prod.ext
  · exact interchange.finalState state
  · exact interchange.emittedExtension state

/-- Interchange also licenses reordering after application to any flat
language. -/
theorem apply_comp_comm_of_interchange
    {first second : StatefulCalculusExtension Source Source}
    (interchange : Interchange first second)
    (state : Source) (base : CalculusLanguageDef) :
    (first.comp second).apply state base =
      (second.comp first).apply state base := by
  rw [comp_comm_of_interchange interchange]

/-! ## Positive and negative controls -/

namespace Canary

private def addType : StatefulCalculusExtension Unit Unit where
  run _ := ((), { newTypes := [TypeDecl.plain "stateful-extension:T"] })

private def addTerm : StatefulCalculusExtension Unit Unit where
  run _ :=
    ((), { newTerms :=
      [{ label := "stateful-extension:c"
         category := "stateful-extension:T"
         params := []
         syntaxPattern := [] }] })

/-- Stages writing disjoint row families admit an interchange certificate. -/
theorem type_and_term_interchange : Interchange addType addTerm := by
  constructor <;> intro state
  · rfl
  · cases state
    simp [addType, addTerm, comp, CalculusLanguageExtension.comp]

private def addFirstType : StatefulCalculusExtension Unit Unit where
  run _ := ((), { newTypes := [TypeDecl.plain "stateful-extension:first"] })

private def addSecondType : StatefulCalculusExtension Unit Unit where
  run _ := ((), { newTypes := [TypeDecl.plain "stateful-extension:second"] })

/-- Two stages writing distinct rows in the same ordered family do not admit
interchange: declaration order is observable. -/
theorem ordered_type_rows_do_not_interchange :
    ¬ Interchange addFirstType addSecondType := by
  intro interchange
  have emitted := interchange.emittedExtension ()
  have typeRows := congrArg CalculusLanguageExtension.newTypes emitted
  simp [addFirstType, addSecondType, comp,
    CalculusLanguageExtension.comp, TypeDecl.plain] at typeRows

end Canary

#print axioms id_comp
#print axioms comp_id
#print axioms comp_assoc
#print axioms comp_apply
#print axioms comp_comm_of_interchange
#print axioms Canary.type_and_term_interchange
#print axioms Canary.ordered_type_rows_do_not_interchange

end StatefulCalculusExtension

end Mettapedia.GSLT.LanguageDef
