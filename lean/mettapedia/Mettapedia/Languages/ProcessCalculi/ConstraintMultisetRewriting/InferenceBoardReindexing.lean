import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceJudgmentBoards
import Mettapedia.GSLT.LanguageDef.CertificateGSLTContextMaps

/-!
# Changing the enumeration of one physical judgment board

The same protected store can be enumerated in several orders. Physical
identity supplies the judgment-preserving premise permutation between any
two exact boards. Its interpretation is a proof-relevant isomorphism, and
changing order through an intermediate board agrees with changing directly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceJudgmentBoards.Board

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (judgment)
open InferenceSchemaKernel (Space Value)
open InferenceRequestExecution (Occurrence label location)
open _root_.CategoryTheory

variable {state : Configuration Value Occurrence}

def entryIndex (board : Board state) (index : Fin board.judgments.length) :
    Fin board.entries.length :=
  ⟨index.val, by simpa only [judgments, List.length_map] using index.isLt⟩

def premiseIndex (board : Board state) (index : Fin board.entries.length) :
    Fin board.judgments.length :=
  ⟨index.val, by simpa only [judgments, List.length_map] using index.isLt⟩

@[simp] theorem entry_premise (board : Board state) (index : Fin board.entries.length) :
    board.entryIndex (board.premiseIndex index) = index := rfl

@[simp] theorem premise_entry (board : Board state) (index : Fin board.judgments.length) :
    board.premiseIndex (board.entryIndex index) = index := rfl

theorem premise_get (board : Board state) (index : Fin board.entries.length) :
    board.judgments.get (board.premiseIndex index) = board.judgmentAt index := by
  simp only [judgments, premiseIndex, List.get_eq_getElem, List.getElem_map, judgmentAt]

theorem entry_get (board : Board state) (index : Fin board.judgments.length) :
    board.judgmentAt (board.entryIndex index) = board.judgments.get index := by
  simpa only [premise_entry] using (board.premise_get (board.entryIndex index)).symm

theorem assumption_as_position (board : Board state) (definition : ValidatedCalculusLanguageDef)
    (index : Fin board.entries.length) :
    board.assumption definition index = board.premise_get index ▸
      OpenDerivation.assumption (board.premiseIndex index) := by
  apply eq_of_heq
  have first : HEq (board.assumption definition index)
      (OpenDerivation.assumption (definition := definition) (board.premiseIndex index)) := by
    unfold assumption
    exact cast_heq _ _
  exact first.trans (eqRec_heq (board.premise_get index)
    (OpenDerivation.assumption (definition := definition) (board.premiseIndex index))).symm

theorem at_occupied (board : Board state) (index : Fin board.entries.length) :
    board.occurrenceAt index ∈ state.present ∧
      location (board.occurrenceAt index) = .judgments :=
  (board.occupied _).mp (List.mem_map.mpr ⟨board.entries.get index, List.get_mem _ _, rfl⟩)

theorem occurrenceAt_injective (board : Board state) : Function.Injective board.occurrenceAt := by
  intro first second same
  have values :
      (board.entries.map Prod.fst).get
          ⟨first.val, by simpa only [List.length_map] using first.isLt⟩ =
      (board.entries.map Prod.fst).get
          ⟨second.val, by simpa only [List.length_map] using second.isLt⟩ := by
    simpa only [occurrenceAt, List.get_eq_getElem, List.getElem_map] using same
  have indices := board.distinct.injective_get values
  have numerals := congrArg
    (fun index : Fin (board.entries.map Prod.fst).length => index.val) indices
  exact Fin.ext numerals

theorem position_at (board : Board state) (index : Fin board.entries.length) :
    board.position (board.occurrenceAt index) (board.at_occupied index).1
      (board.at_occupied index).2 = index :=
  board.occurrenceAt_injective (board.position_occurrence _ _ _)

/-- Reindex by the identity of the actual protected occurrence. -/
noncomputable def reorder (first second : Board state) :
    ContextMap first.judgments second.judgments where
  position index := first.premiseIndex
    (first.position (second.occurrenceAt (second.entryIndex index))
      (second.at_occupied (second.entryIndex index)).1
      (second.at_occupied (second.entryIndex index)).2)
  judgment index := by
    let sourceIndex := first.position (second.occurrenceAt (second.entryIndex index))
      (second.at_occupied (second.entryIndex index)).1
      (second.at_occupied (second.entryIndex index)).2
    rw [first.premise_get]
    have actual := first.at_readback sourceIndex
    rw [first.position_occurrence _ _ _] at actual
    have other := second.at_readback (second.entryIndex index)
    have same := InferenceSchemaActivation.judgment_injective
      (congrArg Prod.snd (actual.symm.trans other))
    exact same.trans (second.entry_get index)

/-- Reordering never changes the physical row addressed by a premise. -/
theorem reorder_occurrence (first second : Board state) (index : Fin second.judgments.length) :
    first.occurrenceAt (first.entryIndex ((first.reorder second).position index)) =
      second.occurrenceAt (second.entryIndex index) := by
  simp only [reorder, entry_premise]
  exact first.position_occurrence _ _ _

@[simp] theorem reorder_self (board : Board state) : board.reorder board = ContextMap.id board.judgments := by
  apply ContextMap.ext
  funext index
  have same := board.occurrenceAt_injective (board.reorder_occurrence board index)
  simpa only [premise_entry, ContextMap.id] using congrArg board.premiseIndex same

/-- Reordering through an intermediate enumeration is the same physical
position map as reordering directly. -/
theorem reorder_comp (first second third : Board state) :
    (first.reorder second).comp (second.reorder third) = first.reorder third := by
  apply ContextMap.ext
  funext index
  have indirect := (first.reorder_occurrence second ((second.reorder third).position index)).trans
    (second.reorder_occurrence third index)
  have direct := first.reorder_occurrence third index
  have same := first.occurrenceAt_injective (indirect.trans direct.symm)
  simpa only [premise_entry, ContextMap.comp] using congrArg first.premiseIndex same

/-- Any two exact enumerations of one protected physical store give
isomorphic premise contexts, with actual inverse proof substitutions. -/
noncomputable def reorderingIso (definition : ValidatedCalculusLanguageDef)
    (first second : Board state) : first.context definition ≅ second.context definition :=
  ContextMap.iso definition (first.reorder second) (second.reorder first)
    (by rw [reorder_comp, reorder_self]) (by rw [reorder_comp, reorder_self])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceJudgmentBoards.Board
