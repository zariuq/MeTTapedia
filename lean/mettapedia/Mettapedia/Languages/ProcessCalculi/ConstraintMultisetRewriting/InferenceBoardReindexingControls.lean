import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferencePremiseReindexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProjectionControls

/-! # Equal-valued rows still induce a nonidentity premise permutation -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBoardReindexingControls

open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a definition)
open InferenceJudgmentBoards
open InferenceProjectionControls.BoardControls
open _root_.CategoryTheory

def reversedBoard : Board doubled where
  entries := doubledBoard.entries.reverse
  distinct := by
    simpa only [List.map_reverse, List.nodup_reverse] using doubledBoard.distinct
  occupied := by
    intro occurrence
    simpa only [List.map_reverse, List.mem_reverse] using doubledBoard.occupied occurrence
  readback := fun entry member => doubledBoard.readback entry (List.mem_reverse.mp member)
  supported := fun entry member => doubledBoard.supported entry (List.mem_reverse.mp member)

def firstTarget : Fin reversedBoard.judgments.length := ⟨0, by decide⟩

theorem first_target_is_second_physical_row :
    (doubledBoard.reorder reversedBoard).position firstTarget =
      doubledBoard.premiseIndex rightPosition := by
  have actual := doubledBoard.reorder_occurrence reversedBoard firstTarget
  have actual' : doubledBoard.occurrenceAt
      (doubledBoard.entryIndex ((doubledBoard.reorder reversedBoard).position firstTarget)) =
        doubledBoard.occurrenceAt rightPosition := actual
  have same := doubledBoard.occurrenceAt_injective actual'
  simpa only [Board.premise_entry] using congrArg doubledBoard.premiseIndex same

/-- Equal values do not turn the physical swap into the identity proof. -/
theorem permutation_is_not_identity :
    (doubledBoard.reorder reversedBoard).interpret definition ≠
      𝟙 (doubledBoard.context definition) := by
  intro same
  have sameMaps := ContextMap.interpret_injective definition
    (same.trans (ContextMap.interpret_id definition doubledBoard.judgments).symm)
  have positions := congrArg (fun mapping => mapping.position firstTarget) sameMaps
  rw [first_target_is_second_physical_row] at positions
  have bad : (1 : Nat) = 0 := congrArg Fin.val positions
  cases bad

theorem genuine_inverse_substitutions :
    (doubledBoard.reorderingIso definition reversedBoard).hom ≫
      (doubledBoard.reorderingIso definition reversedBoard).inv =
        𝟙 (doubledBoard.context definition) :=
  (doubledBoard.reorderingIso definition reversedBoard).hom_inv_id

/-- An enumeration cannot manufacture two positions for one physical row. -/
theorem duplicate_identity_is_not_a_board :
    ¬ ([(firstRow, a), (firstRow, a)].map Prod.fst).Nodup := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBoardReindexingControls
