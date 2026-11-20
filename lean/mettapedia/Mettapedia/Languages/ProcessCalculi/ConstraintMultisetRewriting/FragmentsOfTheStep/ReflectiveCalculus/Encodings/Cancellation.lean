import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls

/-!
# Control for the idempotence argument: barbed bisimilarity does not cancel a common component

The argument that every uniform translation forgets the program cancels a common parallel component,
which the equations of the reflective calculus allow (bags cancel). Barbed bisimilarity does not:
with `@0` observable, `@0!(0) | 0` and `@0!(0) | @0!(0)` are barbed bisimilar (both are stuck and show
the barb on `@0`), while `0` and `@0!(0)` are not (`bisimilarity_not_cancellative`). So with barbed
bisimilarity as the target's relation the idempotence argument does not apply.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Cancellation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (G read)

theorem sender_nil_member {m : Pattern} (member : m ∈ (fromProcess (par sender nil)).1) :
    m = CanonicalReactionControls.payload := by
  rw [fromProcess_par, sender_bag, nil_bag, add_zero, Multiset.mem_singleton] at member
  exact member

theorem sender_sender_member {m : Pattern} (member : m ∈ (fromProcess (par sender sender)).1) :
    m = CanonicalReactionControls.payload := by
  rw [fromProcess_par, sender_bag] at member
  rcases Multiset.mem_add.mp member with inside | inside <;> exact Multiset.mem_singleton.mp inside

theorem sender_nil_stuck (Q : RhoProcess) : ¬ rhoLanguageDefGSLT.Step (par sender nil) Q :=
  stuck_of_no_input (fun c b member => by
    have same := sender_nil_member member
    simp [CanonicalReaction.output, CanonicalReactionControls.payload, CanonicalReaction.input] at same) Q

theorem sender_sender_stuck (Q : RhoProcess) : ¬ rhoLanguageDefGSLT.Step (par sender sender) Q :=
  stuck_of_no_input (fun c b member => by
    have same := sender_sender_member member
    simp [CanonicalReaction.output, CanonicalReactionControls.payload, CanonicalReaction.input] at same) Q

theorem sender_barb : Barb sender (canonicalize (read ByInstantiation.nameZero)) := by
  refine ⟨CanonicalReactionControls.zero, ?_⟩
  rw [sender_bag, Multiset.mem_singleton]
  rfl

/-- **Barbed bisimilarity does not cancel a common parallel component.** -/
theorem bisimilarity_not_cancellative :
    SourceBisimilar (· = ByInstantiation.nameZero) (par sender nil) (par sender sender) ∧
      ¬ SourceBisimilar (· = ByInstantiation.nameZero) nil sender := by
  refine ⟨⟨fun P Q => (P = par sender nil ∧ Q = par sender sender) ∨
      (P = par sender sender ∧ Q = par sender nil), ⟨?_, ?_, ?_⟩, .inl ⟨rfl, rfl⟩⟩, ?_⟩
  · rintro P Q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · rintro P Q P' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) step
    · exact (sender_nil_stuck _ step).elim
    · exact (sender_sender_stuck _ step).elim
  · rintro P Q c rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _
    · exact ⟨par sender sender, .refl, barb_par_left sender sender _ sender_barb⟩
    · exact ⟨par sender nil, .refl, barb_par_left sender nil _ sender_barb⟩
  · rintro ⟨R, bisimulation, related⟩
    obtain ⟨Q', run, payload, member⟩ :=
      bisimulation.barb ByInstantiation.nameZero rfl (bisimulation.symm related) sender_barb
    exact nil_not_succeeds ByInstantiation.nameZero ⟨Q', run, payload, member⟩

#print axioms sender_nil_stuck
#print axioms sender_sender_stuck
#print axioms sender_barb
#print axioms bisimilarity_not_cancellative

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Cancellation
