import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringResults

/-!
# A chosen joint realization supplies actual CMR result knowledge

Profile: one first-order occurrence-bag store, ambient rules, after-tells
one-match judgment. The value agreements are produced by freshness in the
batch consumer; no result equality or admission conclusion is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

def SourceAgrees (s : State (Terms (Term signature)) O)
    (assignment source : Subst signature) : Prop :=
  ∀ term, s.Mentions term → assignment.applyTerm term = source.applyTerm term

theorem realizes_at_given_values (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s)
    (source locals assignment : Subst signature) (produced : List (Term signature))
    (knowledge : Unifies source s.knowledge)
    (pairs : ∀ pair ∈ (presentation f).uses,
      locals.applyTerm pair.1 = source.applyTerm (s.label pair.2))
    (tells : Unifies locals f.rule.body.tell)
    (output : produced = f.rule.body.produce.map locals.applyTerm)
    (sourceValues : SourceAgrees s assignment source)
    (localValues : ∀ term ∈ f.rule.terms,
      assignment.applyTerm (f.opening.applyTerm term) = locals.applyTerm term) :
    Unifies assignment (f.information (frames (FirstOrder.action signature)) s) ∧
      produced = (f.opened (frames (FirstOrder.action signature))).produce.map assignment.applyTerm := by
  constructor
  · apply (models_information_iff s f assignment).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro equation member
      rw [sourceValues equation.1 (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)),
        sourceValues equation.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨equation, member, rfl⟩)))]
      exact knowledge equation member
    · intro pair member
      obtain ⟨termMember, rowPresent⟩ := used_pair_facts s f admitted pair member
      rw [Subst.applyTerm_comp, localValues _ termMember,
        sourceValues _ (Or.inr (Or.inr ⟨pair.2, rowPresent, rfl⟩))]
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
      rw [Subst.applyTerm_comp, Subst.applyTerm_comp, localValues _ left, localValues _ right]
      exact tells equation member
  · rw [output]
    change f.rule.body.produce.map locals.applyTerm =
      (f.rule.body.produce.map f.opening.applyTerm).map assignment.applyTerm
    rw [List.map_map]
    exact List.map_congr_left fun term member =>
      (localValues term (by simp [Rule.terms, member])).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
