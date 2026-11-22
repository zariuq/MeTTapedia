import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchResources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchPrincipal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.RelabelTransport

/-!
# Full labelled-result correspondence of complete symmetric CMR bags

Profile: one first-order occurrence-bag store, ambient programs, finite jointly
fresh bags, own-information guards after tells. Every result model is carried
to a result model preserving the source interface and all labelled occurrence
identities up to a permutation fixing the source. Member reordering changes
neither result labels nor residual solution sets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

theorem same_keys_batch_value_states (s : State (Terms (Term signature)) O)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstOwn : first.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (secondOwn : second.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (keys : first.keysBy identity = second.keysBy identity) (firstModel : Subst signature)
    (solves : Unifies firstModel (first.result (frames (FirstOrder.action signature)) s).knowledge) :
    ∃ secondModel : Subst signature, ∃ rename : Equiv.Perm O,
      Unifies secondModel (second.result (frames (FirstOrder.action signature)) s).knowledge ∧
      SourceAgrees s secondModel firstModel ∧ (∀ o ∈ s.present, rename o = o) ∧
      (first.result (frames (FirstOrder.action signature)) s).present.map rename.toEmbedding =
        (second.result (frames (FirstOrder.action signature)) s).present ∧
      ∀ o ∈ (first.result (frames (FirstOrder.action signature)) s).present,
        firstModel.applyTerm ((first.result (frames (FirstOrder.action signature)) s).label o) =
          secondModel.applyTerm ((second.result (frames (FirstOrder.action signature)) s).label (rename o)) := by
  have model : WordResultModel s first firstModel (outputWords first.members firstModel) :=
    ⟨firstModel, solves, fun _ _ => rfl, rfl⟩
  obtain ⟨secondModel, secondSolves, agrees, words⟩ :=
    (same_keys_word_models s first second firstOwn secondOwn keys _ _).mp model
  obtain ⟨rename, fixes, maps, present⟩ := same_keys_bag_resources s first second firstOwn secondOwn keys
  have output := congrArg List.flatten words
  simp only [outputWords_flatten] at output
  change (first.produce (frames (FirstOrder.action signature))).map firstModel.applyTerm =
    (second.produce (frames (FirstOrder.action signature))).map secondModel.applyTerm at output
  refine ⟨secondModel, rename, secondSolves, agrees, fixes, present, ?_⟩
  intro o inside
  let firstOld : O → Term signature := fun o => (frames (FirstOrder.action signature)).act
    (a := s.frame) (b := (ext (FirstOrder.action signature)).target first.ext)
    ((ext (FirstOrder.action signature)).weaken first.ext) (s.label o)
  let secondOld : O → Term signature := fun o => (frames (FirstOrder.action signature)).act
    (a := s.frame) (b := (ext (FirstOrder.action signature)).target second.ext)
    ((ext (FirstOrder.action signature)).weaken second.ext) (s.label o)
  have firstRow : firstOld = s.label := funext fun o => Subst.applyTerm_id (s.label o)
  have secondRow : secondOld = s.label := funext fun o => Subst.applyTerm_id (s.label o)
  change firstModel.applyTerm (labels firstOld first.selection.made
    (first.produce (frames (FirstOrder.action signature))) o) =
    secondModel.applyTerm (labels secondOld second.selection.made
      (second.produce (frames (FirstOrder.action signature))) (rename o))
  rw [firstRow, secondRow]
  rw [map_relabel firstModel.applyTerm s.label first.selection.made
    (first.produce (frames (FirstOrder.action signature))) o,
    map_relabel secondModel.applyTerm s.label second.selection.made
      (second.produce (frames (FirstOrder.action signature))) (rename o), ← output, ← maps]
  apply relabel_transport rename
  · rw [List.length_map]
    exact bag_made_length s first firstOwn.1
  · intro absent
    have old : o ∈ s.present := by
      change o ∈ (s.present \ first.selection.taken.toFinset) ∪ first.selection.made.toFinset at inside
      rcases Finset.mem_union.mp inside with retained | made
      · exact (Finset.mem_sdiff.mp retained).1
      · exact False.elim (absent (List.mem_toFinset.mp made))
    rw [fixes o old]
    exact (agrees (s.label o) (Or.inr (Or.inr ⟨o, old, rfl⟩))).symm

theorem complete_batch_value_states (s : State (Terms (Term signature)) O)
    (region : Class signature O → Prop)
    (first second : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (firstComplete : first.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
    (secondComplete : second.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region)
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
  obtain ⟨members, perm, keys⟩ := align_key_order s first second
    (firstComplete.keys_perm (fun _ _ => ⟨Subst.id signature⟩) secondComplete)
  have own := Bag.admitsOwn_perm (frames (FirstOrder.action signature)) perm.symm secondComplete.1
  obtain ⟨secondModel, rename, solved, agrees, fixes, present, labelled⟩ :=
    same_keys_batch_value_states s first _ firstComplete.1 own keys firstModel solves
  obtain ⟨samePresent, sameLabels, knowledge⟩ :=
    Bag.result_perm (frames (FirstOrder.action signature)) perm.symm secondComplete.1.1
  refine ⟨secondModel, rename,
    (fun e member => solved e (knowledge.mem_iff.mpr member)), agrees, fixes,
    present.trans samePresent, ?_⟩
  intro o member
  rw [← sameLabels]
  exact labelled o member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
