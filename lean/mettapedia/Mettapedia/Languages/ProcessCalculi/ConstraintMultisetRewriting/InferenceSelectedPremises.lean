import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceJudgmentBoards

/-!
# Actual selected premise ports become open-derivation assumptions

The premise context is selected by the firing's ordered physical reads.
Reading the same occurrence at several ports selects the same context
position repeatedly. Neither value equality nor a set of premise values
replaces these positions. The source rule node is recovered from successful
activation, including source-side admission conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload)
open InferenceSelectedFirings
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}
  {before after : Configuration Value Occurrence}
  {firing : SelectedFiring definition true before after}

namespace KernelOrigin

variable (origin : firing.KernelOrigin)

theorem read_length : origin.premises.length = firing.picked.read.length := by
  simpa only [origin.rule_eq, InferenceSchemaKernel.locate, LocatedRequest.lift,
    InferenceSchemaActivation.fromResult, List.length_map] using firing.qualified.read_length

def readOccurrence (port : Fin origin.premises.length) : Occurrence :=
  firing.picked.read.get ⟨port.val, by rw [← origin.read_length]; exact port.isLt⟩

theorem read_present (port : Fin origin.premises.length) :
    origin.readOccurrence port ∈ before.present :=
  firing.qualified.occurrences.kept_subset (by
    simpa only [readOccurrence, Selection.commit, Finset.mem_coe, List.mem_toFinset] using
      List.get_mem firing.picked.read ⟨port.val, by rw [← origin.read_length]; exact port.isLt⟩)

theorem read_protected (port : Fin origin.premises.length) :
    location (origin.readOccurrence port) = .judgments := by
  have valid := firing.qualified
  rw [origin.rule_eq] at valid
  apply LocatedRequest.read_space action location payload
    .requests .judgments .requests .judgments valid
  exact List.get_mem _ _

/-- This is the position of the actual physical read, rather than an
arbitrarily chosen equal-valued premise. -/
noncomputable def readPosition (board : Board before) (port : Fin origin.premises.length) :
    Fin board.entries.length :=
  board.position (origin.readOccurrence port) (origin.read_present port) (origin.read_protected port)

theorem position_reads_actual_occurrence (board : Board before) (port : Fin origin.premises.length) :
    board.occurrenceAt (origin.readPosition board port) = origin.readOccurrence port :=
  board.position_occurrence _ _ _

/-- Two read ports selecting one physical row remain one shared premise
position even if the source rule uses that premise twice. -/
theorem repeated_read_position (board : Board before)
    (first second : Fin origin.premises.length)
    (same : origin.readOccurrence first = origin.readOccurrence second) :
    origin.readPosition board first = origin.readPosition board second := by
  apply Fin.ext
  simp only [readPosition, Board.position, same]

theorem read_judgment (board : Board before) (port : Fin origin.premises.length) :
    board.judgmentAt (origin.readPosition board port) = origin.premises.get port := by
  obtain ⟨assignment, solved⟩ := firing.qualified.consistent
  have matched := (Selection.models_problem locatedAction firing.qualified solved).2.2.1
  have matched' : List.Forall₂
      (fun premise occurrence =>
        locatedAction.E (locatedAction.apply assignment (Space.judgments, judgment premise))
          (locatedAction.apply assignment (label occurrence)))
      origin.premises firing.picked.read := by
    have mapped : List.Forall₂
        (fun expected occurrence => locatedAction.E (locatedAction.apply assignment expected)
          (locatedAction.apply assignment (label occurrence)))
        (origin.premises.map (fun premise => (Space.judgments, judgment premise)))
        firing.picked.read := by
      simpa only [origin.rule_eq, InferenceSchemaKernel.locate, LocatedRequest.lift,
        InferenceSchemaActivation.fromResult, List.map_map, Function.comp_def] using matched
    exact List.forall₂_map_left_iff.mp mapped
  have same := matched'.get port.isLt
    (show port.val < firing.picked.read.length from by rw [← origin.read_length]; exact port.isLt)
  change Space.judgments = location (origin.readOccurrence port) ∧
    action.apply assignment (judgment (origin.premises.get port)) =
      action.apply assignment (payload (origin.readOccurrence port)) at same
  have boardRead := board.at_readback (origin.readPosition board port)
  rw [origin.position_reads_actual_occurrence board port] at boardRead
  have contents : payload (origin.readOccurrence port) =
      judgment (board.judgmentAt (origin.readPosition board port)) := congrArg Prod.snd boardRead
  have sourceScope := (InferenceSchemaActivation.application_scopes origin.application).1
    _ (List.get_mem _ port)
  have equality := same.2
  rw [contents, InferenceSchemaActivation.judgment_fixed _ sourceScope assignment,
    InferenceSchemaActivation.judgment_fixed _ (board.at_scoped _) assignment] at equality
  exact (InferenceSchemaActivation.judgment_injective equality).symm

/-- Ordered selections are represented by actual assumption nodes. -/
noncomputable def picked (board : Board before) :
    board.context definition ⟶ (⟨origin.premises⟩ : ClassifyingContext definition) :=
  OpenDerivationList.ofFn origin.premises fun port =>
    (origin.read_judgment board port) ▸ board.assumption definition (origin.readPosition board port)

theorem picked_get (board : Board before) (port : Fin origin.premises.length) :
    (origin.picked board).get port =
      (origin.read_judgment board port) ▸
        board.assumption definition (origin.readPosition board port) :=
  OpenDerivationList.get_ofFn _ port

/-- The generating arrow is the exact locally activated source rule. -/
def generator :
    (⟨origin.premises⟩ : ClassifyingContext definition) ⟶ ⟨[origin.conclusion]⟩ :=
  .cons (.byRule origin.instance_ origin.application
    (assumptionEnvironment definition origin.premises)) .nil

/-- Applying the source generator to the selected occurrences retains one
primitive rule node and the ordered, position-addressed premise vector. -/
theorem picked_generator (board : Board before) :
    origin.picked board ≫ origin.generator =
      OpenDerivationList.cons
        (.byRule origin.instance_ origin.application (origin.picked board)) .nil := by
  change (OpenDerivationList.cons
      (.byRule origin.instance_ origin.application
        (assumptionEnvironment definition origin.premises)) .nil).bind
      (origin.picked board) = _
  simp only [OpenDerivationList.bind, OpenDerivation.bind,
    OpenDerivationList.assumptionEnvironment_bind]

end KernelOrigin
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring
