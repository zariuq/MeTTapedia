import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProjectionControls

/-!
# Persistent inference controls: exact cut and observable premise positions

Two equal judgments at distinct physical occurrences yield different proof
observations. Conversely, an actual public request post can change physical
history without changing the entire protected proof vector. The latter is
why the result is an equivalence at a declared observation, not of raw paths.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b c definition)
open InferenceSchemaActivation (judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open InferenceProjectionControls.BoardControls
open PersistentInference
open _root_.CategoryTheory

def abProof : OpenDerivation definition [a] b :=
  .byRule ⟨⟨"ab"⟩, []⟩ first_application (.cons (.assumption ⟨0, by decide⟩) .nil)

def bcProof : OpenDerivation definition [b] c :=
  .byRule ⟨⟨"bc"⟩, []⟩ second_application (.cons (.assumption ⟨0, by decide⟩) .nil)

def cutProof : OpenDerivationList definition [a] [c] :=
  (OpenDerivationList.cons bcProof .nil).bind (.cons abProof .nil)

theorem cut_keeps_both_primitive_nodes : cutProof.ruleCount = 2 := rfl

theorem actual_cut_replays_the_two_source_rules :
    let first := compile initial_consistent (prior := initialBoard) (.cons abProof .nil)
    ∃ second : Execution (definition := definition) first.after first.board [c],
      (first.follow second).observe = cutProof ∧
      (system definition).Run payload initial (first.actors ++ second.actors) second.after := by
  intro first
  obtain ⟨second, replay⟩ := realizes_cut initial_consistent first (.cons bcProof .nil)
  refine ⟨second, ?_, (first.follow second).ordinary⟩
  exact replay.trans (congrArg (fun proofs => (OpenDerivationList.cons bcProof .nil).bind proofs)
    (compile_observe initial_consistent (prior := initialBoard) (.cons abProof .nil)))

def leftOutputs : ContextMap doubledBoard.judgments [a] :=
  singletonSelection (ContextMap.id _) ⟨0, by decide⟩

def rightOutputs : ContextMap doubledBoard.judgments [a] :=
  singletonSelection (ContextMap.id _) ⟨1, by decide⟩

theorem equal_judgments_keep_distinct_proof_positions :
    (identityExecution (definition := definition) doubledBoard leftOutputs).observe ≠
      (identityExecution (definition := definition) doubledBoard rightOutputs).observe := by
  rw [identityExecution_observe, identityExecution_observe]
  intro same
  have positions := congrArg (fun proofs : OpenDerivationList definition doubledBoard.judgments [a] =>
    (proofs.get ⟨0, by decide⟩).assumptionPosition) same
  rw [ContextMap.interpret_position, ContextMap.interpret_position] at positions
  cases positions

theorem repeated_read_ports_share_one_physical_occurrence :
    selectedReads initialBoard (ContextMap.pair (ContextMap.id _) (ContextMap.id _)) =
      [firstRow, firstRow] := rfl

def extraRequest : Occurrence := (37, (.requests, judgment a))

theorem different_physical_histories_have_the_same_proof_observation :
    ∃ first second : Execution (definition := definition) initial initialBoard [a],
      first.actors ≠ second.actors ∧ first.observe = second.observe := by
  have posted := InferenceRequestExecution.client_posts definition initial initial_consistent
    (judgment a) extraRequest (by decide +kernel) rfl
  obtain ⟨client⟩ := SelectedFiring.of_step posted
  let origin := Classical.choice client.client_origin
  let trace : SelectedRun definition initial [false]
      (InferenceRequestExecution.posted initial extraRequest) := .cons client (.nil _)
  let first : Execution (definition := definition) initial initialBoard [a] :=
    identityExecution initialBoard (ContextMap.id _)
  let second : Execution (definition := definition) initial initialBoard [a] :=
    ⟨_, [false], trace, origin.board initialBoard, ContextMap.id _⟩
  refine ⟨first, second, by change ([] : List Bool) ≠ [false]; decide, ?_⟩
  have emptyReplay : first.observe = 𝟙 (initialBoard.context definition) :=
    identityExecution_observe initialBoard (ContextMap.id _)
  rw [emptyReplay]
  change 𝟙 (initialBoard.context definition) =
    ((𝟙 _ ≫ 𝟙 _) ≫ InferencePathFunctor.changeBoard
      (origin.board initialBoard) (origin.board initialBoard)) ≫ 𝟙 _
  rw [InferencePathFunctor.changeBoard_self]
  simp only [Category.id_comp]
  rfl

theorem raw_execution_is_not_determined_by_its_proof_vector :
    ¬ Function.Injective
      (Execution.observe (definition := definition) (before := initial) (prior := initialBoard)
        (goals := [a])) := by
  intro injective
  obtain ⟨first, second, actorsDifferent, same⟩ :=
    different_physical_histories_have_the_same_proof_observation
  exact actorsDifferent (congrArg Execution.actors (injective same))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceControls
