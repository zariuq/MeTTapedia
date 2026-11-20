import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringModels

/-!
# Result models of an actual CMR firing depend on its symmetric match class

Profile: one first-order occurrence-bag store, ambient rules, one-match
admission after own tells. Result models preserve the source terms mentioned
by the state and the ordered labels made by the firing. The resource-identity
part is kept separately; no arbitrary context or provenance is erased.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

/-- The actual result's knowledge, source-interface reading, and produced
labels. It is not defined through the class interpretation. -/
def ResultModel (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (source : Subst signature) (produced : List (Term signature)) : Prop :=
  ∃ assignment : Subst signature,
    Unifies assignment (f.result (frames (FirstOrder.action signature)) s).knowledge ∧
      (∀ term, s.Mentions term → assignment.applyTerm term = source.applyTerm term) ∧
      produced = ((f.opened (frames (FirstOrder.action signature))).produce.map assignment.applyTerm)

omit [DecidableEq O] in
private theorem source_label_mentioned (s : State (Terms (Term signature)) O)
    {o : O} (present : o ∈ s.present) : s.Mentions (s.label o) := Or.inr (Or.inr ⟨o, present, rfl⟩)

theorem resultModel_iff (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s)
    (source : Subst signature) (produced : List (Term signature)) :
    ResultModel s f source produced ↔
      Unifies source s.knowledge ∧ (presentation f).Realizes s.label source produced := by
  constructor
  · rintro ⟨assignment, solved, agrees, output⟩
    obtain ⟨knowledge, pairs, tells⟩ := (models_information_iff s f assignment).mp solved
    refine ⟨?_, assignment.comp f.opening, ?_, tells, ?_⟩
    · intro equation member
      have left : s.Mentions equation.1 := Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)
      have right : s.Mentions equation.2 := Or.inr (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩))
      rw [← agrees _ left, ← agrees _ right]
      exact knowledge equation member
    · intro pair member
      rw [pairs pair member]
      exact agrees _ (source_label_mentioned s (used_pair_facts s f admitted pair member).2)
    · change produced = f.rule.body.produce.map (assignment.comp f.opening).applyTerm
      rw [output]
      change (f.rule.body.produce.map f.opening.applyTerm).map assignment.applyTerm = _
      rw [List.map_map]
      apply List.map_congr_left
      intro term _
      exact (Subst.applyTerm_comp assignment f.opening term).symm
  · rintro ⟨knowledge, locals, pairs, tells, output⟩
    obtain ⟨assignment, stateValues, ruleValues⟩ := admitted.1.1 PUnit.unit source locals
    have sourceValues : ∀ term, s.Mentions term →
        assignment.applyTerm term = source.applyTerm term := by
      intro term member
      simpa only [frames, Interface.Frames.ofSubstitution, ext, Extensions.identity,
        FirstOrder.action, Subst.applyTerm_id] using stateValues term member
    have localValues : ∀ term ∈ f.rule.terms,
        (assignment.comp f.opening).applyTerm term = locals.applyTerm term := by
      intro term member
      simpa only [frames, Interface.Frames.ofSubstitution, FirstOrder.action,
        Subst.applyTerm_comp] using ruleValues term member
    refine ⟨assignment, ?_, sourceValues, ?_⟩
    · apply (models_information_iff s f assignment).mpr
      refine ⟨?_, ?_, ?_⟩
      · intro equation member
        have left : s.Mentions equation.1 := Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)
        have right : s.Mentions equation.2 := Or.inr (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩))
        rw [sourceValues _ left, sourceValues _ right]
        exact knowledge equation member
      · intro pair member
        obtain ⟨termMember, rowPresent⟩ := used_pair_facts s f admitted pair member
        rw [localValues _ termMember, sourceValues _ (source_label_mentioned s rowPresent)]
        exact pairs pair member
      · intro equation member
        have left : equation.1 ∈ f.rule.terms := by
          have listed : equation.1 ∈ f.rule.body.tell.map Prod.fst :=
            List.mem_map.mpr ⟨equation, member, rfl⟩
          simp only [Rule.terms, List.mem_append]
          tauto
        have right : equation.2 ∈ f.rule.terms := by
          have listed : equation.2 ∈ f.rule.body.tell.map Prod.snd :=
            List.mem_map.mpr ⟨equation, member, rfl⟩
          simp only [Rule.terms, List.mem_append]
          tauto
        rw [localValues _ left, localValues _ right]
        exact tells equation member
    · rw [output]
      simp only [Firing.opened, RuleInstance.map, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro term member
      change term ∈ f.rule.body.produce at member
      have listed : term ∈ f.rule.terms := by simp [Rule.terms, member]
      change locals.applyTerm term = assignment.applyTerm (f.opening.applyTerm term)
      simpa only [Subst.applyTerm_comp] using (localValues term listed).symm

/-- Matching-class equality now preserves actual result models, not merely
the cardinality or membership of a proposed batch's keys. -/
theorem same_class_result_models (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second)
    (source : Subst signature) (produced : List (Term signature)) :
    ResultModel s first source produced ↔ ResultModel s second source produced := by
  rw [resultModel_iff s first firstAdmitted, resultModel_iff s second secondAdmitted]
  apply and_congr_right
  intro _
  exact Same.realizes_iff (Quotient.exact same) s.label source produced

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
