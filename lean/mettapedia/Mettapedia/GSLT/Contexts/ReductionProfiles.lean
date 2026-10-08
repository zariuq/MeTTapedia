import Mettapedia.GSLT.Contexts.TransitionProfile

/-!
# One static theory, several reductions

The terms, the static equivalence and the contexts of a theory are one thing;
its reduction is another (`ContextTheory.withRewrites`).  This module names a
reduction on a theory (`ContextTheory.Reduction`) and the theory read at it
(`ContextTheory.reducing`), and says what hosting is for a map read at two
reductions.

* A map of theories is a map between any reductions of them: the static part
  is the same (`ContextMap.atReductions`).
* It is hosting exactly when it reflects the static equivalence, sends steps
  to steps, and every step of an image is the image of a step up to the
  static equivalence (`ContextMap.atReductions_hosting_iff`).  The last two
  clauses are the ones that hold for want of steps when both theories have no
  reduction.
* A theory with a step has no hosting map into a theory without reduction
  (`ContextMap.not_hosting_of_step_into_static`).
* The identity between two reductions of one theory is hosting exactly when
  the two reductions agree up to the static equivalence
  (`ContextMap.id_atReductions_hosting_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

/-- A reduction on the terms of a theory that respects its static
equivalence. -/
structure Reduction (theory : ContextTheory.{u}) where
  step : {interface : theory.Interface} → theory.Term interface → theory.Term interface → Prop
  left : ∀ {interface : theory.Interface} {term term' next : theory.Term interface},
    (theory.equations interface).r term term' → step term next →
      ∃ next', step term' next' ∧ (theory.equations interface).r next next'
  right : ∀ {interface : theory.Interface} {term next next' : theory.Term interface},
    step term next → (theory.equations interface).r next next' → step term next'

variable (theory : ContextTheory.{u})

/-- **The theory read at a reduction**: the same terms, static equivalence and
contexts. -/
def reducing (reduction : theory.Reduction) : ContextTheory.{u} :=
  theory.withRewrites reduction.step reduction.left reduction.right

/-- No reduction. -/
def Reduction.none : theory.Reduction where
  step := fun _ _ => False
  left := fun _ step => step.elim
  right := fun step _ => step

/-- The reduction that the theory has. -/
def Reduction.own : theory.Reduction where
  step := theory.rewrites
  left := theory.rewrites_resp_left
  right := theory.rewrites_resp_right

/-- A theory without reduction: no term has a step. -/
def Static : Prop :=
  ∀ {interface : theory.Interface} (term next : theory.Term interface), ¬ theory.rewrites term next

theorem reducing_none_static : (theory.reducing (Reduction.none theory)).Static :=
  fun _ _ step => step

@[simp] theorem reducing_rewrites (reduction : theory.Reduction) {interface : theory.Interface}
    (term next : theory.Term interface) :
    (theory.reducing reduction).rewrites term next ↔ reduction.step term next :=
  Iff.rfl

end ContextTheory

namespace ContextMap

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-- **A map of theories, read at a reduction of each.** -/
def atReductions (sourceReduction : source.Reduction) (targetReduction : target.Reduction) :
    ContextMap (source.reducing sourceReduction) (target.reducing targetReduction) where
  interface := map.interface
  term := map.term
  context := map.context
  term_resp := map.term_resp
  equivariant := map.equivariant

/-- **Hosting at two reductions**: reflect the static equivalence, send steps
to steps, and lift every step of an image. -/
theorem atReductions_hosting_iff (sourceReduction : source.Reduction)
    (targetReduction : target.Reduction) :
    (map.atReductions sourceReduction targetReduction).Hosting ↔
      map.ReflectsEquations ∧
      (∀ {interface : source.Interface} {term next : source.Term interface},
        sourceReduction.step term next → targetReduction.step (map.term term) (map.term next)) ∧
      ∀ {interface : source.Interface} {term : source.Term interface}
        {next : target.Term (map.interface interface)},
        targetReduction.step (map.term term) next →
          ∃ sourceNext, sourceReduction.step term sourceNext ∧
            (target.equations _).r next (map.term sourceNext) := by
  rw [hosting_iff, preservesTransitions_iff_rewrites, reflectsTransitions_iff_rewrites]
  exact Iff.rfl

/-- **A theory with a step has no hosting map into a theory without
reduction.** -/
theorem not_hosting_of_step_into_static (static : target.Static) {interface : source.Interface}
    {term next : source.Term interface} (step : source.rewrites term next) : ¬ map.Hosting :=
  fun hosting => static _ _ (map.preservesRewrites_of_transitions hosting.preserves step)

/-- **The identity between two reductions of one theory is hosting exactly
when they agree up to the static equivalence.** -/
theorem id_atReductions_hosting_iff (theory : ContextTheory.{u}) (first second : theory.Reduction) :
    ((ContextMap.id theory).atReductions first second).Hosting ↔
      (∀ {interface : theory.Interface} {term next : theory.Term interface},
        first.step term next → second.step term next) ∧
      ∀ {interface : theory.Interface} {term next : theory.Term interface},
        second.step term next →
          ∃ other, first.step term other ∧ (theory.equations interface).r next other := by
  rw [atReductions_hosting_iff]
  constructor
  · rintro ⟨-, preserves, reflects⟩
    exact ⟨preserves, reflects⟩
  · rintro ⟨preserves, reflects⟩
    exact ⟨fun equivalent => equivalent, preserves, reflects⟩

/-- Dropping the reduction of a theory with a step is not hosting. -/
theorem forget_not_hosting (theory : ContextTheory.{u}) (reduction : theory.Reduction)
    {interface : theory.Interface} {term next : theory.Term interface}
    (step : reduction.step term next) :
    ¬ ((ContextMap.id theory).atReductions reduction (ContextTheory.Reduction.none theory)).Hosting :=
  fun hosting =>
    ((id_atReductions_hosting_iff theory reduction (ContextTheory.Reduction.none theory)).mp
      hosting).1 step

/-- Adding a step to a theory without reduction is not hosting: the image has
a transition that nothing in the source accounts for. -/
theorem adjoin_not_hosting (theory : ContextTheory.{u}) (reduction : theory.Reduction)
    {interface : theory.Interface} {term next : theory.Term interface}
    (step : reduction.step term next) :
    ¬ ((ContextMap.id theory).atReductions (ContextTheory.Reduction.none theory) reduction).Hosting := by
  intro hosting
  obtain ⟨_, impossible, _⟩ :=
    ((id_atReductions_hosting_iff theory (ContextTheory.Reduction.none theory) reduction).mp
      hosting).2 step
  exact impossible

/-- Both maps reflect the static equivalence: it is the two clauses on
transitions that fail. -/
theorem id_atReductions_reflectsEquations (theory : ContextTheory.{u})
    (first second : theory.Reduction) :
    ((ContextMap.id theory).atReductions first second).ReflectsEquations :=
  fun equivalent => equivalent

end ContextMap

#print axioms ContextMap.atReductions_hosting_iff
#print axioms ContextMap.not_hosting_of_step_into_static
#print axioms ContextMap.id_atReductions_hosting_iff
#print axioms ContextMap.forget_not_hosting
#print axioms ContextMap.adjoin_not_hosting

end Mettapedia.GSLT
