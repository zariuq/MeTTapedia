import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricResources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricGivenValues
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.RelabelTransport

/-!
# Equal symmetric CMR matches preserve actual labelled result states

Profile: one first-order occurrence-bag store, ambient programs, one-match
admission after tells. Every model of one residual result has a model of the
other, with the source-mentioned interface fixed and every present labelled
occurrence carried by one permutation fixing all source occurrences. This is
stronger than an unlabeled resource-count comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

theorem same_class_value_states (s : State (Terms (Term signature)) O)
    (first : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (second : Firing O (ext (FirstOrder.action signature)) P' s.frame)
    (firstAdmitted : first.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : second.Admits (frames (FirstOrder.action signature)) s)
    (same : identity.key first = identity.key second)
    (firstModel : Subst signature)
    (solves : Unifies firstModel (first.result (frames (FirstOrder.action signature)) s).knowledge) :
    ∃ secondModel : Subst signature, ∃ rename : Equiv.Perm O,
      Unifies secondModel (second.result (frames (FirstOrder.action signature)) s).knowledge ∧
      SourceAgrees s secondModel firstModel ∧ (∀ o ∈ s.present, rename o = o) ∧
      (first.result (frames (FirstOrder.action signature)) s).present.map rename.toEmbedding =
        (second.result (frames (FirstOrder.action signature)) s).present ∧
      ∀ o ∈ (first.result (frames (FirstOrder.action signature)) s).present,
        firstModel.applyTerm ((first.result (frames (FirstOrder.action signature)) s).label o) =
          secondModel.applyTerm ((second.result (frames (FirstOrder.action signature)) s).label (rename o)) := by
  have model : ResultModel s first firstModel
      ((first.opened (frames (FirstOrder.action signature))).produce.map firstModel.applyTerm) :=
    ⟨firstModel, solves, fun _ _ => rfl, rfl⟩
  obtain ⟨secondModel, secondSolves, agrees, output⟩ :=
    (same_class_result_models s first second firstAdmitted secondAdmitted same _ _).mp model
  obtain ⟨rename, fixes, maps, present⟩ :=
    same_class_occurrence_renaming s first second firstAdmitted secondAdmitted same
  refine ⟨secondModel, rename, secondSolves, agrees, fixes, present, ?_⟩
  intro o inside
  change firstModel.applyTerm (labels (first.row (frames (FirstOrder.action signature)) s)
      first.selection.made (first.opened (frames (FirstOrder.action signature))).produce o) =
    secondModel.applyTerm (labels (second.row (frames (FirstOrder.action signature)) s)
      second.selection.made (second.opened (frames (FirstOrder.action signature))).produce (rename o))
  rw [row_identity s first, row_identity s second]
  rw [map_relabel firstModel.applyTerm s.label first.selection.made
    (first.opened (frames (FirstOrder.action signature))).produce o,
    map_relabel secondModel.applyTerm s.label second.selection.made
      (second.opened (frames (FirstOrder.action signature))).produce (rename o), ← output, ← maps]
  apply relabel_transport rename
  · simp only [List.length_map, Firing.opened, RuleInstance.map]
    exact firstAdmitted.1.2.2.2.2.2.1.symm
  · intro absent
    have old : o ∈ s.present := by
      change o ∈ (s.present \ first.selection.taken.toFinset) ∪ first.selection.made.toFinset at inside
      rcases Finset.mem_union.mp inside with retained | made
      · exact (Finset.mem_sdiff.mp retained).1
      · exact False.elim (absent (List.mem_toFinset.mp made))
    rw [fixes o old]
    exact (agrees (s.label o) (Or.inr (Or.inr ⟨o, old, rfl⟩))).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
