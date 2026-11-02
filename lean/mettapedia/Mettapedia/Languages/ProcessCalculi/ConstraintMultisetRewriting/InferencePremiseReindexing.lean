import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceBoardReindexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedPremises

/-!
# Actual premise selection is invariant under board enumeration

Reordering the same protected physical store changes only the assumption
addresses. The selected native read occurrences and the activated source
rule stay fixed. Their classifying arrow commutes with the physical premise
permutation, including repeated read ports.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring.KernelOrigin

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value)
open InferenceRequestExecution (Occurrence)
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}
  {before after : Configuration Value Occurrence}
  {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)

noncomputable def premiseMap (board : Board before) :
    ContextMap board.judgments origin.premises where
  position port := board.premiseIndex (origin.readPosition board port)
  judgment port := (board.premise_get (origin.readPosition board port)).trans
    (origin.read_judgment board port)

theorem premiseMap_interpret (board : Board before) :
    (origin.premiseMap board).interpret definition = origin.picked board := by
  unfold ContextMap.interpret picked premiseMap
  apply congrArg (OpenDerivationList.ofFn origin.premises)
  funext port
  rw [board.assumption_as_position]
  exact ContextMap.cast_trans _ _ _

/-- The position square commutes because both routes address the same
actual read occurrence, rather than merely an equal judgment. -/
theorem premiseMap_reorder (first second : Board before) :
    (first.reorder second).comp (origin.premiseMap second) = origin.premiseMap first := by
  apply ContextMap.ext
  funext port
  have indirect := first.reorder_occurrence second ((origin.premiseMap second).position port)
  have secondRead : second.occurrenceAt
      (second.entryIndex ((origin.premiseMap second).position port)) = origin.readOccurrence port := by
    simp only [premiseMap, Board.entry_premise]
    exact origin.position_reads_actual_occurrence second port
  have direct := origin.position_reads_actual_occurrence first port
  have same := first.occurrenceAt_injective ((indirect.trans secondRead).trans direct.symm)
  simpa only [Board.premise_entry, ContextMap.comp, premiseMap] using congrArg first.premiseIndex same

/-- Reindexing the board before selecting premises leaves exactly the
same proof-relevant ordered premise vector. -/
theorem picked_reorder (first second : Board before) :
    (first.reorder second).interpret definition ≫ origin.picked second = origin.picked first := by
  rw [← origin.premiseMap_interpret first, ← origin.premiseMap_interpret second,
    ← ContextMap.interpret_comp, origin.premiseMap_reorder]

/-- The actual newly derived judgment is independent of the chosen
enumeration, through the specified premise-permutation isomorphism. -/
theorem generator_reorder (first second : Board before) :
    (first.reorder second).interpret definition ≫
      (origin.picked second ≫ origin.generator) = origin.picked first ≫ origin.generator := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun selected => selected ≫ origin.generator) (origin.picked_reorder first second))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring.KernelOrigin
