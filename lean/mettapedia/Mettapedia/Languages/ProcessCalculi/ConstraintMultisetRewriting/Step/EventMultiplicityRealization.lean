import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicity

/-!
# Exact event realization and transfer of the parallel congruence

A realization is checked on each event fibre: labels and successor states
commute, and the event map is a bijection. Surjectivity excludes hidden target
events. Such a realization transports event bisimilarity, including the
independent asynchronous congruence, to an implementing system.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventMultiplicity

universe uS uT uU uV uA uC uD uE uF

variable {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {A : Type uA}

structure Realization (source : System.{uS,uA,uC} S A) (target : System.{uT,uA,uD} T A) where
  state : S → T
  choices : (s : S) → source.Choice s ≃ target.Choice (state s)
  actions : ∀ s choice, source.action s choice = target.action (state s) (choices s choice)
  successors : ∀ s choice, state (source.next s choice) = target.next (state s) (choices s choice)

namespace Realization

variable {source : System.{uS,uA,uC} S A} {target : System.{uT,uA,uD} T A}
  (implementation : Realization source target)

def bisimulation : Bisimulation source target (fun s t => implementation.state s = t) where
  choices same := same ▸ implementation.choices _
  actions same choice := by cases same; exact implementation.actions _ choice
  successors same choice := by cases same; exact implementation.successors _ choice

theorem bisimilar (s : S) : Bisimilar source s target (implementation.state s) :=
  ⟨_, ⟨implementation.bisimulation⟩, rfl⟩

theorem preserves_bisimilar {s t : S} (same : Bisimilar source s source t) :
    Bisimilar target (implementation.state s) target (implementation.state t) :=
  (implementation.bisimilar s).symm.trans (same.trans (implementation.bisimilar t))

theorem reflects_bisimilar {s t : S}
    (same : Bisimilar target (implementation.state s) target (implementation.state t)) :
    Bisimilar source s source t :=
  (implementation.bisimilar s).trans (same.trans (implementation.bisimilar t).symm)

end Realization

/-- Parallel congruence reaches an actual implementation when its fibres are exact. -/
theorem realized_parallel_congruence
    {left : System.{uS,uA,uC} S A} {right : System.{uT,uA,uD} T A}
    {target : System.{uU,uA,uE} U A} (implementation : Realization (asynchronous left right) target)
    {s s' : S} {t t' : T} (one : Bisimilar left s left s') (two : Bisimilar right t right t') :
    Bisimilar target (implementation.state (s, t)) target (implementation.state (s', t')) :=
  implementation.preserves_bisimilar (one.asynchronous two)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventMultiplicity
