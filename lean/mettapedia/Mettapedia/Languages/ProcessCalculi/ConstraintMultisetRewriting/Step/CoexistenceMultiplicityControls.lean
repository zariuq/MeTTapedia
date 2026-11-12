import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationControls

/-!
# A core overlap counterexample for an event observation

The native board publishes its current occurrence count. Equal-size boards
are event-bisimilar, and disjoint context addition preserves that relation.
An overlapping identity collapses under union and breaks the observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.CoexistenceMultiplicityControls

open Presentation.Controls (frame)
open EventMultiplicity

def board : EffectCore frame Nat (Finset Nat) (fun _ => Unit) where
  frame _ := ()
  knowledge _ := []
  present state := state
  selection _ := ⟨[], [], []⟩
  target _ := ()
  extension _ := frame.id ()
  information _ := []
  information_refines := by intros; exact Frames.models_nil _
  Shapes _ := ([] : List Nat).Nodup
  preparedResult {s} _ _ := s
  present_preparedResult _ _ := by
    simp [Selection.commit, MeTTaCalculus.OccurrenceCommits.fire]
  preparedSettle _ _ := frame.id ()
  result_refines := by intros; exact Frames.models_nil _

theorem prepares (state : Finset Nat) : board.Prepares (s := state) () :=
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing state,
    ⟨(), frame.id (), Frames.models_nil _⟩⟩

def program : Step frame Nat (Finset Nat) (fun _ => Unit) := Step.ofEffect board (fun _ _ => True)

theorem admitted (state : Finset Nat) : program.Admits (s := state) () := ⟨prepares state, trivial⟩

def observed : System (Finset Nat) Nat := program.eventSystem (fun {state} _ => state.card)

def choices (state : Finset Nat) : Unit ≃ observed.Choice state where
  toFun _ := ⟨(), admitted state⟩
  invFun choice := choice.val
  left_inv value := by cases value; rfl
  right_inv choice := by apply Subtype.ext; cases choice.val; rfl

def sameSize : Bisimulation observed observed (fun left right => left.card = right.card) where
  choices {s} {t} _ := (choices s).symm.trans (choices t)
  actions same _ := same
  successors same _ := same

theorem bisimilar_iff_card (left right : Finset Nat) :
    Bisimilar observed left observed right ↔ left.card = right.card := by
  constructor
  · rintro ⟨_, ⟨b⟩, related⟩
    exact b.actions related (choices left ())
  · intro same
    exact ⟨_, ⟨sameSize⟩, same⟩

theorem union_is_native_tensor (left right : Finset Nat) :
    board.configuration (left ∪ right) =
      Coexistence.tensor (board.configuration left) (board.configuration right) := rfl

theorem disjoint_context_congruence {left right : Finset Nat}
    (same : Bisimilar observed left observed right) (context : Finset Nat)
    (apartLeft : Disjoint left context) (apartRight : Disjoint right context) :
    Bisimilar observed (left ∪ context) observed (right ∪ context) := by
  apply (bisimilar_iff_card _ _).mpr
  rw [Finset.card_union_of_disjoint apartLeft, Finset.card_union_of_disjoint apartRight,
    (bisimilar_iff_card _ _).mp same]

theorem overlap_changes_behaviour :
    Bisimilar observed {0} observed {1} ∧ Disjoint ({0} : Finset Nat) {1} ∧
      ¬Bisimilar observed (({0} : Finset Nat) ∪ {1}) observed (({1} : Finset Nat) ∪ {1}) := by
  refine ⟨(bisimilar_iff_card _ _).mpr (by decide), by decide, ?_⟩
  rw [bisimilar_iff_card]
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.CoexistenceMultiplicityControls
