import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.SourceBudget
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# The executable frame representation as an operational correspondence

`PartrecMachine.BoundedReduction` already implements the authored machine's
step on continuation frames and proves `reduces_frameState_iff`. This module
turns that implementation theorem into the existing composable operational
interfaces. No machine step is erased: every target step from an encoded
frame state reads back to exactly one executable step, including steps in
the middle of a pending evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Authored

open Mettapedia.Languages.PartrecMachine
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-- The transition relation of the existing executable frame step. Its
absorbing halted state is not counted as a further execution step. -/
def frames : GSLT := equalityGSLT FrameState fun before after =>
  isHalted before = false ∧ after = frameStep before

theorem generated_step_iff (state : FrameState) (target : Pattern) :
    machineTheory.Step (encFrameState state) target ↔
      isHalted state = false ∧ target = encFrameState (frameStep state) :=
  (reduces_iff_generatedStep _ _).symm.trans (reduces_frameState_iff state target)

/-- Encoding continuation frames preserves one actual authored transition. -/
def translation : OperationalTranslation frames machineTheory where
  mapTerm := encFrameState
  mapEquiv := by
    intro left right same
    change left = right at same
    subst right
    exact machineTheory.equations.iseqv.refl _
  mapStep := by
    rintro before after ⟨notHalted, rfl⟩
    exact (generated_step_iff before _).mpr ⟨notHalted, rfl⟩

/-- The relation includes every encoded administrative state, rather than
only the initial code and the halted output. -/
def correspondence : OperationalCorrespondence frames machineTheory where
  related state term := encFrameState state = term
  readStep := by
    rintro before current next rfl stepped
    obtain ⟨notHalted, same⟩ := (generated_step_iff before next).mp stepped
    exact .inr ⟨frameStep before, ⟨notHalted, rfl⟩, same.symm⟩
  forward := by
    rintro before after current rfl ⟨notHalted, rfl⟩
    exact ⟨_, ⟨.cons ⟨(generated_step_iff before _).mpr ⟨notHalted, rfl⟩⟩ (.refl _)⟩, rfl⟩

/-- The whole supplied target prefix has a source prefix of exactly the
same length. In particular there is no target-only administration here. -/
theorem read_path : ∀ {first last : Pattern} (path : ExecutionPath machineTheory first last)
    (state : FrameState), encFrameState state = first →
      ∃ final, ∃ sourcePath : ExecutionPath frames state final,
        encFrameState final = last ∧ sourcePath.length = path.length
  | _, _, .refl _, state, same => ⟨state, .refl state, same, rfl⟩
  | _, _, .cons step rest, state, same => by
      have stepped := step.down
      rw [← same] at stepped
      obtain ⟨notHalted, next⟩ := (generated_step_iff state _).mp stepped
      obtain ⟨final, sourceRest, related, length⟩ := read_path rest (frameStep state) next.symm
      exact ⟨final, .cons ⟨⟨notHalted, rfl⟩⟩ sourceRest, related, by
        simp only [Route.length, length]⟩

/-- The endpoint of a supplied authored prefix is the endpoint of that
many applications of the existing executable step. -/
theorem path_endpoint : ∀ {first last : Pattern} (path : ExecutionPath machineTheory first last)
    (state : FrameState), encFrameState state = first →
      last = encFrameState (frameStep^[path.length] state)
  | _, _, .refl _, _, same => same.symm
  | _, _, .cons step rest, state, same => by
      have stepped := step.down
      rw [← same] at stepped
      obtain ⟨_, next⟩ := (generated_step_iff state _).mp stepped
      have tail := path_endpoint rest (frameStep state) next.symm
      simpa only [Route.length, Function.iterate_succ_apply] using tail

theorem terminal_iff (state : FrameState) :
    (∀ target, ¬ machineTheory.Step (encFrameState state) target) ↔ isHalted state = true := by
  constructor
  · intro terminal
    cases halted : isHalted state
    · exact False.elim (terminal _ ((generated_step_iff state _).mpr ⟨halted, rfl⟩))
    · rfl
  · intro halted target step
    have notHalted := ((generated_step_iff state target).mp step).1
    simp [halted] at notHalted

/-- The authored machine and the executable frame state report exactly
the same halted value. -/
theorem answer_iff (state : FrameState) (output : List Nat) :
    encFrameState state = encCfg (.halt output) ↔
      SourceBudget.observe state = .answer output := by
  rw [SourceBudget.observe_answer_iff]
  exact ⟨fun same => encFrameState_injective same, fun same => by rw [same]; rfl⟩

namespace Controls

/-- Successor needs two authored steps from its pending evaluation to its
answer; the representation preserves both. -/
theorem successor_two_steps :
    frames.Step (SourceBudget.start .succ []) (.inr (.inl ([], [1]))) ∧
      frames.Step (.inr (.inl ([], [1]))) (.inr (.inr [1])) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Although the bounded iterator pads a halted endpoint, that padding
cannot become an authored or an executable transition. -/
theorem halted_padding_not_execution (output : List Nat) :
    frameStep (.inr (.inr output)) = .inr (.inr output) ∧
      ¬ frames.Step (.inr (.inr output)) (.inr (.inr output)) := by
  exact ⟨rfl, fun step => Bool.noConfusion step.1⟩

end Controls

#print axioms translation
#print axioms correspondence
#print axioms read_path
#print axioms path_endpoint
#print axioms terminal_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Authored
