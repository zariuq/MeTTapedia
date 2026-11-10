import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTraceCharge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls

/-!
# Actual store-changing runs under a chosen trace quotient

The existing transport identifies two candidate labels with the same store
effect. The free paths remain different. Event count and conserved net charge
descend, while the complete label word cannot descend through that quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventTraceControls

open _root_.CategoryTheory
open Presentation.Controls (Store frame)
open PublicationTransportControls

abbrev P := program permissive
abbrev T := transport permissive

def start : Store := [(true, false)]

def run (label : Bool) : P.Run start := .cons label (permissive_admits label) (.nil _)

def arrow (label : Bool) : T.Arrow (Transport.StateClass.mk T start)
    (Transport.StateClass.mk T (run true).last) := ⟨start, run label, rfl, rfl⟩

theorem related : Transport.Arrow.Rel (arrow true) (arrow false) := by
  apply Transport.Arrow.rel_of_similar
  exact Transport.Similar.cons_alike True.intro (permissive_admits true) (permissive_admits false)
    (Transport.Similar.refl (Step.Run.nil _))

def labels (value : T.Arrow (Transport.StateClass.mk T start)
    (Transport.StateClass.mk T (run true).last)) : List Bool := value.run.word.map (·.2)

theorem different_labels : labels (arrow true) ≠ labels (arrow false) := by
  simp [labels, arrow, run, Step.Run.word]

theorem labels_cannot_descend :
    ¬ ∃ read : T.Trace (Transport.StateClass.mk T start) (Transport.StateClass.mk T (run true).last) → List Bool,
      ∀ value, read (Quot.mk _ value) = labels value :=
  Transport.Trace.no_observation_of_distinguished_related T labels _ _ related different_labels

theorem free_paths_differ : (run true).eventPath P ≠ (run false).eventPath P := by
  intro same
  have words := congrArg P.eventWord same
  rw [Step.Run.eventPath_word, Step.Run.eventPath_word] at words
  have labelWords := congrArg (List.map (fun entry : (_ : Store) × Bool => entry.2)) words
  exact different_labels labelWords

local instance : Category T.StateClass := T.traceCategory

theorem quotient_identifies_paths :
    T.eventTraceFunctor.map ((run true).eventPath P) =
      T.eventTraceFunctor.map ((run false).eventPath P) := by
  rw [Transport.eventTrace_run, Transport.eventTrace_run]
  exact Quot.sound related

theorem count_is_retained (label : Bool) :
    Transport.Trace.eventCount T (T.eventTraceFunctor.map ((run label).eventPath P)) = 1 := by
  rw [Transport.eventCount_eventTrace_run]
  rfl

def charge : ConservedCharge P Int where
  potential state := state.length
  taken _ _ := 0
  made _ _ := 1
  balance := by
    intro state firing admitted
    change ((state ++ [(true, false)]).length : Int) + 0 = (state.length : Int) + 1
    simp

theorem charge_invariant : charge.Invariant T := by
  rintro source target ⟨same⟩
  cases same.down
  rfl

theorem net_is_retained (label : Bool) :
    Transport.Trace.net T charge charge_invariant
      (T.eventTraceFunctor.map ((run label).eventPath P)) = 1 := by
  rw [Transport.Trace.net_eventTrace_run]
  rfl

theorem update_is_nontrivial (label : Bool) : (run label).last ≠ start := by
  intro same
  have lengths := congrArg List.length same
  change 2 = 1 at lengths
  exact (by decide : (2 : Nat) ≠ 1) lengths

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventTraceControls
