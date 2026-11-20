import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricSemantics

/-!
# Actual CMR information as source and local equations

Profile: one first-order occurrence-bag store, ambient rules, one-match
judgments, guards after tells. This module exposes the information of actual
firings; it does not replace that information by a new admission predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

omit [DecidableEq O] in
theorem row_identity (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) :
    f.row (frames (FirstOrder.action signature)) s = s.label := by
  funext o
  exact Subst.applyTerm_id _

omit [DecidableEq O] in
theorem matching_eq_pairs (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (patterns : List (Term signature)) (selected : List O) :
    f.matching (frames (FirstOrder.action signature)) s
        (patterns.map f.opening.applyTerm) selected =
      (patterns.zip selected).map fun pair => (f.opening.applyTerm pair.1, s.label pair.2) := by
  unfold Firing.matching
  rw [row_identity]
  rw [← List.map_uncurry_zip_eq_zipWith, List.zip_map_left, List.map_map]
  rfl

omit [DecidableEq O] in
theorem information_eq (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) :
    f.information (frames (FirstOrder.action signature)) s =
      s.knowledge ++
        (f.rule.body.take.zip f.selection.taken).map
          (fun pair => (f.opening.applyTerm pair.1, s.label pair.2)) ++
        (f.rule.body.read.zip f.selection.read).map
          (fun pair => (f.opening.applyTerm pair.1, s.label pair.2)) ++
        f.rule.body.tell.map (fun equation =>
          (f.opening.applyTerm equation.1, f.opening.applyTerm equation.2)) := by
  unfold Firing.information
  have transported : (frames (FirstOrder.action signature)).applyStore
      ((ext (FirstOrder.action signature)).weaken f.ext) s.knowledge = s.knowledge :=
    Interface.Frames.applyStore_id s.knowledge
  rw [transported]
  change s.knowledge ++ f.matching _ s (f.rule.body.take.map f.opening.applyTerm) _ ++
    f.matching _ s (f.rule.body.read.map f.opening.applyTerm) _ ++ _ = _
  rw [matching_eq_pairs, matching_eq_pairs]
  rfl

omit [DecidableEq O] in
theorem models_information_iff (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (assignment : Subst signature) :
    Unifies assignment (f.information (frames (FirstOrder.action signature)) s) ↔
      Unifies assignment s.knowledge ∧
        (∀ pair ∈ (presentation f).uses,
          (assignment.comp f.opening).applyTerm pair.1 = assignment.applyTerm (s.label pair.2)) ∧
        Unifies (assignment.comp f.opening) f.rule.body.tell := by
  rw [information_eq]
  simp only [Unifies, List.forall_mem_append, List.forall_mem_map,
    Presentation.uses, presentation, Multiset.mem_add, Multiset.mem_coe,
    Subst.applyTerm_comp]
  constructor
  · rintro ⟨⟨⟨knowledge, takes⟩, reads⟩, tells⟩
    exact ⟨knowledge, fun pair member => member.elim (takes pair) (reads pair), tells⟩
  · rintro ⟨knowledge, pairs, tells⟩
    exact ⟨⟨⟨knowledge, fun pair member => pairs pair (Or.inl member)⟩,
      fun pair member => pairs pair (Or.inr member)⟩, tells⟩

theorem used_pair_facts (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s)
    (pair : Term signature × O) (member : pair ∈ (presentation f).uses) :
    pair.1 ∈ f.rule.terms ∧ pair.2 ∈ s.present := by
  simp only [presentation, Presentation.uses, Multiset.mem_add, Multiset.mem_coe] at member
  rcases member with take | read
  · have parts := List.of_mem_zip take
    exact ⟨by simp [Rule.terms, parts.1],
      admitted.2.1.taken_subset (List.mem_toFinset.mpr parts.2)⟩
  · have parts := List.of_mem_zip read
    exact ⟨by simp [Rule.terms, parts.1],
      admitted.2.1.kept_subset (List.mem_toFinset.mpr parts.2)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
