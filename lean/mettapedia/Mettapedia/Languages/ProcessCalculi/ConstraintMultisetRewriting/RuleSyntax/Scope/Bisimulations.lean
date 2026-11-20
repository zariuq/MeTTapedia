import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Isolation

/-!
# The scope laws as strong bisimulations of the step of every program

In the tree's vocabulary (`FragmentsOfTheStep.TransitionMaps.IsBisimulation`), on the successor
relation of `RuleSyntax.step` at the one frame, for every program:

* **renaming** (`renaming_isBisimulation`): the graph of `renameState π`, for every renaming `π`;
* **scope extension** (`scope_extension_related`): beside a neighbour whose terms the renaming fixes,
  the system and its renaming are related by that bisimulation;
* **congruence** (`congruent_isBisimulation`): the same knowledge up to order and repetition, the
  same rows;
* **hiding** (`hiddenFO_isBisimulation`, first-order terms): knowledge seen alike from the rows, with
  the same unknowns; a state and its projection by solved forms are related (`hide_related`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open FragmentsOfTheStep.TransitionMaps (IsBisimulation)
open Mettapedia.Logic.LP

universe uT uS uO

section OneFrameLaws

variable {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} {O : Type uO} [DecidableEq O]
  (P : Program (Terms T))

/-- **Renaming is a bisimulation** of the step of every program. -/
theorem renaming_isBisimulation (π : Renaming A) :
    IsBisimulation (Succ (step (frames A) O (ext A) P).toStep) (Succ (step (frames A) O (ext A) P).toStep)
      (fun s t => t = renameState π s) := by
  refine ⟨fun {s t s'} related reached => ?_, fun {s t t'} related reached => ?_⟩
  · subst related
    exact ⟨_, (succ_rename_iff π s _).mpr ⟨s', reached, rfl⟩, rfl⟩
  · subst related
    obtain ⟨s', reached', rfl⟩ := (succ_rename_iff π s t').mp reached
    exact ⟨s', reached', rfl⟩

/-- **Scope extension**: beside a neighbour whose terms the renaming fixes, the system beside the
neighbour and its renaming beside the neighbour are related by the renaming bisimulation. -/
theorem scope_extension_related (π : Renaming A) {D : State (Terms T) O}
    (fixed : ∀ t, D.Mentions t → A.apply π.forward t = t) (C : State (Terms T) O) :
    beside D (renameState π C) = renameState π (beside D C) :=
  (scope_extension π fixed C).symm

/-- **Structural congruence is a bisimulation** of the step of every program. -/
theorem congruent_isBisimulation :
    IsBisimulation (Succ (step (frames A) O (ext A) P).toStep) (Succ (step (frames A) O (ext A) P).toStep)
      Congruent := by
  refine ⟨fun {s t s'} related reached => succ_congruent related reached,
    fun {s t t'} related reached => ?_⟩
  obtain ⟨s', reached', related'⟩ := succ_congruent related.symm reached
  exact ⟨s', reached', related'.symm⟩

end OneFrameLaws

section FirstOrderLaws

variable {sig : LPSignature} [DecidableEq sig.vars] {O : Type uO} [DecidableEq O]
  (P : Program (Terms (Term sig)))

/-- **Hiding is a bisimulation** of the step of every program, at first-order terms. -/
theorem hiddenFO_isBisimulation :
    IsBisimulation (Succ (step (frames (FirstOrder.action sig)) O (ext (FirstOrder.action sig)) P).toStep)
      (Succ (step (frames (FirstOrder.action sig)) O (ext (FirstOrder.action sig)) P).toStep) HiddenFO := by
  refine ⟨fun {s t s'} related reached => succ_hiddenFO related reached,
    fun {s t t'} related reached => ?_⟩
  obtain ⟨s', reached', related'⟩ := succ_hiddenFO related.symm reached
  exact ⟨s', reached', related'.symm⟩

omit [DecidableEq O] in
/-- **A state and its projection by solved forms are related by it.** -/
theorem hide_related [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]
    {s : State (Terms (Term sig)) O} {θ : Subst sig} (accepted : unifyTotal s.knowledge = some θ)
    {H : Finset sig.vars} (avoid : ∀ v, UnknownsOf (Rows s) v → v ∉ H) :
    HiddenFO s (withKnowledge s (hideStore θ H s.knowledge)) :=
  hiddenFO_hide accepted avoid

end FirstOrderLaws

#print axioms renaming_isBisimulation
#print axioms scope_extension_related
#print axioms congruent_isBisimulation
#print axioms hiddenFO_isBisimulation
#print axioms hide_related

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
