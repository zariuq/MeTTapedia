import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-! # Certified frames for an HE equation frontier -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Steps (EquationFrontierRel EquationWork)

/-- Lift the exact source frontier to reached frames in the same order,
with one frame for each work occurrence. -/
theorem Frame.equationFrontier {policy : Policy} (activation : Frame)
    {space : Space} {live : List Atom} {query : Entry.Value} {works : List EquationWork}
    (frontier : EquationFrontierRel space live query.erase activation.bindings works) :
    ∃ frames : List Frame, works.Forall₂ (fun work reached =>
      reached.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment query
        (Entry.Value.ofAtom work.pattern) reached.environment) frames := by
  obtain ⟨_, lifted⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier
  clear frontier
  induction lifted with
  | nil => exact ⟨[], .nil⟩
  | cons here _ ih =>
      obtain ⟨frames, related⟩ := ih
      exact ⟨⟨_, _, here.2⟩ :: frames, .cons ⟨rfl, here.1⟩ related⟩

theorem Frame.equationFrontier_unifiers {policy : Policy} (activation : Frame)
    {space : Space} {live : List Atom} {query : Entry.Value} {works : List EquationWork}
    (frontier : EquationFrontierRel space live query.erase activation.bindings works) :
    ∀ work ∈ works, ∃ reached : Frame, reached.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment query
        (Entry.Value.ofAtom work.pattern) reached.environment := by
  obtain ⟨frames, reached⟩ := activation.equationFrontier (policy := policy) frontier
  intro work member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  have valid : index.val < frames.length := reached.length_eq ▸ index.isLt
  exact ⟨frames.get ⟨index, valid⟩, reached.get index.isLt valid⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
