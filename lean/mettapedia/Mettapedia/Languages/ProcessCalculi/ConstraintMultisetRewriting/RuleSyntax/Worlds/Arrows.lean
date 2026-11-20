import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Pairs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.GSLT.Core.GSLTConstructions

/-!
# The one-world case and the two-world case, as functional bisimulations of the tree

The tree relates two transition systems through a map of states by a functional bisimulation
(`FragmentsOfTheStep.TransitionMaps.FunctionalBisimulation`: steps are carried, and steps out of
images lift). Such maps compose (`FunctionalBisimulation.comp`), carry bisimilarity both ways
(`TransitionMaps.bisimilar_iff_map`) and pull the modalities back (`TransitionMaps.pb_diamond`).

* **`one_world_bisimulation`**: the step of a program with a space, on states, and the firing moves of
  bags, through the map of a state to the bag of that one world: the present step is the one-world
  case.
* **`pair_bisimulation`**: the tree's interleaving product (`GSLT.interleavingProduct`) of the steps of
  two programs with a space, on pairs of states, and the firing moves of bags, through the map of a
  pair to the bag of the two worlds: two worlds of a bag, with a space no one writes to, are the
  interleaving product of their steps.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
  (FunctionalBisimulation theoryOf)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}
  [DecidableEq O]

/-- The step of a program, as a relation on states. -/
abbrev Steps (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
    (P : Program Tm) : State Tm O → State Tm O → Prop :=
  Succ (step X O E P).toStep

variable {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom}

/-- **The present step is the one-world case**: the step of a program with a space, and the firing
moves of the bags of one world with those rules and that space, are related by a functional
bisimulation. -/
theorem one_world_bisimulation (P R : Program Tm) :
    FunctionalBisimulation (Steps X O E (P ∪ R)) (Fires (events X O E))
      (fun s => (⟨{(⟨P, s⟩ : System Tm O)}, R⟩ : Bag Tm O)) where
  zig := by
    rintro s s' ⟨f, admitted, rfl⟩
    exact Fires.fire (family := events X O E) 0 R ⟨P, s⟩ ⟨f, admitted⟩
  zag := by
    intro s W' fires
    obtain ⟨f, admitted, rfl⟩ := (one_world_fires ⟨P, s⟩ R W').mp fires
    exact ⟨f.result X s, ⟨f, admitted, rfl⟩, rfl⟩

/-- **Two worlds of a bag are the interleaving product of their steps**: the interleaving product of
the steps of two programs with a space, and the firing moves of the bags of the two worlds, are
related by a functional bisimulation. -/
theorem pair_bisimulation (P₁ P₂ R : Program Tm) :
    FunctionalBisimulation
      (Mettapedia.GSLT.GSLT.interleavingProduct (theoryOf (State Tm O) (Steps X O E (P₁ ∪ R)))
        (theoryOf (State Tm O) (Steps X O E (P₂ ∪ R)))).Step
      (Fires (events X O E)) (pairBag P₁ P₂ R) where
  zig := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ (⟨⟨f, admitted, moved⟩, held⟩ | ⟨held, ⟨f, admitted, moved⟩⟩)
    · have movedEq : f.result X a = a' := moved
      have heldEq : b = b' := held
      subst movedEq
      subst heldEq
      exact Fires.add_right (Fires.fire (family := events X O E) 0 R ⟨P₁, a⟩ ⟨f, admitted⟩) {(⟨P₂, b⟩ : System Tm O)}
    · have movedEq : f.result X b = b' := moved
      have heldEq : a = a' := held
      subst movedEq
      subst heldEq
      exact Fires.add_left (Fires.fire (family := events X O E) 0 R ⟨P₂, b⟩ ⟨f, admitted⟩) {(⟨P₁, a⟩ : System Tm O)}
  zag := by
    intro p W' fires
    obtain ⟨c, rfl⟩ := (pair_fires_iff P₁ P₂ R p W').mp fires
    rcases c with c | c
    · exact ⟨(c.1.result X p.1, p.2), Or.inl ⟨⟨c.1, c.2, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨(p.1, c.1.result X p.2), Or.inr ⟨rfl, ⟨c.1, c.2, rfl⟩⟩, rfl⟩

#print axioms one_world_bisimulation
#print axioms pair_bisimulation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
