import Mettapedia.Logic.LP.MutualInstantiation

/-!
# Mutual instances of a finite term interface differ by lossless names

One pair of substitutions acts on the entire list. Consequently variable
sharing between different interface terms is retained, not just the shape of
each term separately.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.MutualListInstantiation

variable {signature : LPSignature} [DecidableEq signature.vars]

private theorem map_fixed {A : Type*} (f : A → A) : ∀ (items : List A),
    items.map f = items → ∀ item ∈ items, f item = item := by
  intro items
  induction items with
  | nil => intro _ item member; cases member
  | cons head rest ih =>
    intro fixed item member
    obtain ⟨first, tail⟩ := List.cons.inj fixed
    rcases List.mem_cons.mp member with rfl | later
    · exact first
    · exact ih tail item later

theorem variants_of_mutual_instances (first second : List (Term signature))
    (forward backward : Subst signature)
    (advanced : first.map forward.applyTerm = second)
    (recovered : second.map backward.applyTerm = first) :
    ∃ names inverse : signature.vars → signature.vars,
      first.map (UnificationRenaming.rename names) = second ∧
      second.map (UnificationRenaming.rename inverse) = first ∧
      (∀ term ∈ first, ∀ name ∈ term.freeVars, inverse (names name) = name) ∧
      (∀ term ∈ second, ∀ name ∈ term.freeVars, names (inverse name) = name) := by
  have firstRound : first.map (fun term => backward.applyTerm (forward.applyTerm term)) = first := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map backward.applyTerm) advanced).trans recovered
  have secondRound : second.map (fun term => forward.applyTerm (backward.applyTerm term)) = second := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map forward.applyTerm) recovered).trans advanced
  refine ⟨MutualInstantiation.variableImage forward, MutualInstantiation.variableImage backward,
    ?_, ?_, ?_, ?_⟩
  · rw [← advanced]
    apply List.map_congr_left
    intro term member
    exact MutualInstantiation.rename_of_retraction forward backward term (map_fixed _ first firstRound term member)
  · rw [← recovered]
    apply List.map_congr_left
    intro term member
    exact MutualInstantiation.rename_of_retraction backward forward term (map_fixed _ second secondRound term member)
  · intro term member name present
    exact MutualInstantiation.variable_images_retract forward backward term
      (map_fixed _ first firstRound term member) name present
  · intro term member name present
    exact MutualInstantiation.variable_images_retract backward forward term
      (map_fixed _ second secondRound term member) name present

end Mettapedia.Logic.LP.MutualListInstantiation
