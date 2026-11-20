import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFiringResults
import Mettapedia.Logic.LP.MutualListInstantiation

/-!
# Principal CMR result readouts are variants over the source interface

Profile: one first-order occurrence-bag store, ambient rules, one-match
after-tells admission. An accepted principal answer is applied to every
source-mentioned term and every produced label in one shared interface.
Names are recovered from actual factor substitutions, not assumed equal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

noncomputable def sourceTerms (s : State (Terms (Term signature)) O) : List (Term signature) :=
  s.knowledge.map Prod.fst ++ s.knowledge.map Prod.snd ++ s.present.toList.map s.label

omit [DecidableEq O] in
theorem sourceTerms_mentioned (s : State (Terms (Term signature)) O) (term : Term signature)
    (member : term ∈ sourceTerms s) : s.Mentions term := by
  simp only [sourceTerms, List.mem_append] at member
  rcases member with (left | right) | row
  · exact Or.inl left
  · exact Or.inr (Or.inl right)
  · obtain ⟨o, present, rfl⟩ := List.mem_map.mp row
    exact Or.inr (Or.inr ⟨o, Finset.mem_toList.mp present, rfl⟩)

noncomputable def readout (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (answer : Subst signature) : List (Term signature) :=
  (sourceTerms s).map answer.applyTerm ++
    (f.opened (frames (FirstOrder.action signature))).produce.map answer.applyTerm

omit [DecidableEq O] in
theorem readout_factor (s : State (Terms (Term signature)) O)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (answer candidate residual : Subst signature)
    (factors : ∀ term, candidate.applyTerm term = residual.applyTerm (answer.applyTerm term)) :
    (readout s f answer).map residual.applyTerm = readout s f candidate := by
  simp only [readout, List.map_append, List.map_map]
  apply congrArg₂ List.append
  · exact List.map_congr_left fun term _ => (factors term).symm
  · exact List.map_congr_left fun term _ => (factors term).symm

variable [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

theorem principal_readout_instance (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second)
    (firstAnswer secondAnswer : Subst signature)
    (firstAccepted : unifyTotal (first.information (frames (FirstOrder.action signature)) s) = some firstAnswer)
    (secondAccepted : unifyTotal (second.information (frames (FirstOrder.action signature)) s) = some secondAnswer) :
    ∃ residual : Subst signature,
      (readout s second secondAnswer).map residual.applyTerm = readout s first firstAnswer := by
  have firstModel : ResultModel s first firstAnswer
      ((first.opened (frames (FirstOrder.action signature))).produce.map firstAnswer.applyTerm) :=
    ⟨firstAnswer, unifyTotal_sound _ _ firstAccepted, fun _ _ => rfl, rfl⟩
  obtain ⟨candidate, solves, source, output⟩ :=
    (same_class_result_models s first second firstAdmitted secondAdmitted same _ _).mp firstModel
  obtain ⟨residual, factors⟩ :=
    (FirstOrder.accepted_principal _ secondAnswer secondAccepted).factors candidate solves
  refine ⟨residual, ?_⟩
  have through : ∀ term, candidate.applyTerm term = residual.applyTerm (secondAnswer.applyTerm term) := by
    intro term
    simpa only [FirstOrder.action, Subst.applyTerm_comp] using factors term
  rw [readout_factor s second secondAnswer candidate residual through]
  unfold readout
  apply congrArg₂ List.append
  · exact List.map_congr_left fun term member => source term (sourceTerms_mentioned s term member)
  · exact output.symm

/-- One pair of inverse-on-support variable maps handles the entire source
and result interface, preserving sharing across its component terms. -/
theorem principal_readouts_are_variants (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second)
    (firstAnswer secondAnswer : Subst signature)
    (firstAccepted : unifyTotal (first.information (frames (FirstOrder.action signature)) s) = some firstAnswer)
    (secondAccepted : unifyTotal (second.information (frames (FirstOrder.action signature)) s) = some secondAnswer) :
    ∃ names inverse : signature.vars → signature.vars,
      (readout s first firstAnswer).map (UnificationRenaming.rename names) = readout s second secondAnswer ∧
      (readout s second secondAnswer).map (UnificationRenaming.rename inverse) = readout s first firstAnswer ∧
      (∀ term ∈ readout s first firstAnswer, ∀ name ∈ term.freeVars, inverse (names name) = name) ∧
      (∀ term ∈ readout s second secondAnswer, ∀ name ∈ term.freeVars, names (inverse name) = name) := by
  obtain ⟨backward, recovered⟩ := principal_readout_instance s first second firstAdmitted
    secondAdmitted same firstAnswer secondAnswer firstAccepted secondAccepted
  obtain ⟨forward, advanced⟩ := principal_readout_instance s second first secondAdmitted
    firstAdmitted same.symm secondAnswer firstAnswer secondAccepted firstAccepted
  exact MutualListInstantiation.variants_of_mutual_instances _ _ forward backward advanced recovered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
