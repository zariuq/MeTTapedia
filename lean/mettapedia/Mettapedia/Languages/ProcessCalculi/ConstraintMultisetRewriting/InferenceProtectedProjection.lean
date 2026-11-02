import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedPremises
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextExtension

/-!
# Protected judgment propagation of an actual request-consuming inference

The server consumes public request data and retains all protected premises.
Only its protected-space projection is read-only. Its classifying arrow
keeps the ordered board and appends the exact activated source inference.
Client data posts induce the identity on that projection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload postRule)
open InferenceJudgmentBoards
open _root_.CategoryTheory
open ClassifyingContext

variable {definition : ValidatedCalculusLanguageDef}
  {before after : Configuration Value Occurrence}

namespace KernelOrigin

variable {firing : SelectedFiring definition true before after}
  (origin : firing.KernelOrigin)

include origin

theorem taken_requests : ∀ occurrence ∈ firing.picked.taken,
    location occurrence = .requests := by
  have valid := firing.qualified
  rw [origin.rule_eq] at valid
  have places := LocatedRequest.take_space action location payload
    .requests .judgments .requests .judgments valid
  have one : firing.picked.taken.length = 1 := by
    simpa only [InferenceSchemaKernel.locate, LocatedRequest.lift,
      InferenceSchemaActivation.fromResult, List.length_map, List.length_cons,
      List.length_nil] using valid.take_length.symm
  obtain ⟨request, selected⟩ := List.length_eq_one_iff.mp one
  have place : Space.requests = location request := by
    simp only [InferenceSchemaActivation.fromResult, selected,
      List.forall₂_cons] at places
    exact places.1
  intro occurrence member
  have same : occurrence = request := by simpa only [selected, List.mem_singleton] using member
  subst occurrence
  exact place.symm

theorem output_length : firing.picked.made.length = 1 := by
  have lengths := congrArg List.length firing.qualified.outputs
  simpa only [origin.rule_eq, InferenceSchemaKernel.locate, LocatedRequest.lift,
    InferenceSchemaActivation.fromResult, List.length_map, List.length_cons,
    List.length_nil] using lengths

/-- The unique output is the actual made occurrence of the firing. -/
def output : Occurrence :=
  firing.picked.made.get ⟨0, by rw [origin.output_length]; decide⟩

theorem made_singleton : firing.picked.made = [origin.output] := by
  obtain ⟨occurrence, selected⟩ := List.length_eq_one_iff.mp origin.output_length
  have same : origin.output = occurrence := by
    simp only [output, List.get_eq_getElem, selected, List.getElem_cons_zero]
  rw [same]
  exact selected

theorem output_readback : label origin.output = (.judgments, judgment origin.conclusion) := by
  have outputs := firing.qualified.outputs
  rw [origin.made_singleton, origin.rule_eq] at outputs
  exact List.singleton_inj.mp outputs

theorem output_fresh : origin.output ∉ before.present := by
  intro present
  exact Finset.disjoint_left.mp firing.qualified.occurrences.fresh
    (by simp only [Selection.commit, origin.made_singleton, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]) present

/-- Every old protected row survives, and precisely one new protected row
appears. The consumed request is outside this equivalence. -/
theorem protected_after (occurrence : Occurrence) :
    (occurrence ∈ after.present ∧ location occurrence = .judgments) ↔
      (occurrence ∈ before.present ∧ location occurrence = .judgments) ∨
        occurrence = origin.output := by
  conv_lhs => rw [firing.destination]
  constructor
  · rintro ⟨present, protectedHere⟩
    rcases mem_fire.mp present with stayed | made
    · exact Or.inl ⟨stayed.1, protectedHere⟩
    · right
      simpa only [Selection.commit, origin.made_singleton, List.toFinset_cons,
        List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] using made
  · rintro (⟨present, protectedHere⟩ | rfl)
    · refine ⟨mem_fire.mpr (Or.inl ⟨present, ?_⟩), protectedHere⟩
      intro taken
      have selected : occurrence ∈ firing.picked.taken := by
        simpa only [Selection.commit, List.mem_toFinset] using taken
      have requested := origin.taken_requests occurrence selected
      rw [protectedHere] at requested
      cases requested
    · refine ⟨mem_fire.mpr (Or.inr ?_), congrArg Prod.fst origin.output_readback⟩
      simp only [Selection.commit, origin.made_singleton, List.toFinset_cons,
        List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]

noncomputable def board (prior : Board before) : Board after :=
  prior.extend origin.output origin.conclusion
    (fun member => origin.output_fresh ((prior.occupied _).mp member).1)
    origin.output_readback (InferenceSchemaActivation.application_scopes origin.application).2
    (fun occurrence => (origin.protected_after occurrence).trans
      (or_congr (prior.occupied occurrence).symm Iff.rfl))

theorem board_context (prior : Board before) :
    (origin.board prior).context definition =
      concat (prior.context definition) ⟨[origin.conclusion]⟩ := by
  apply congrArg ClassifyingContext.mk
  exact Board.extend_judgments ..

/-- The exact source inference is appended to the retained premise board. -/
noncomputable def arrow (prior : Board before) :
    prior.context definition ⟶ (origin.board prior).context definition :=
  ReadOnlyContextExtension.readStep (origin.picked prior) origin.generator ≫
    eqToHom (origin.board_context prior).symm

/-- Transporting the target back to its displayed concatenation recovers
the concrete read-only context extension. -/
theorem arrow_displayed (prior : Board before) :
    origin.arrow prior ≫ eqToHom (origin.board_context prior) =
      ReadOnlyContextExtension.readStep (origin.picked prior) origin.generator := by
  rw [arrow, Category.assoc, eqToHom_trans]
  change ReadOnlyContextExtension.readStep (origin.picked prior) origin.generator ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem keeps_old_positions (prior : Board before) :
    origin.arrow prior ≫ eqToHom (origin.board_context prior) ≫
      fstProjection (prior.context definition) ⟨[origin.conclusion]⟩ =
        𝟙 (prior.context definition) := by
  rw [← Category.assoc, origin.arrow_displayed]
  exact ReadOnlyContextExtension.readStep_keeps _ _

theorem publishes_actual_rule (prior : Board before) :
    origin.arrow prior ≫ eqToHom (origin.board_context prior) ≫
      sndProjection (prior.context definition) ⟨[origin.conclusion]⟩ =
        OpenDerivationList.cons
          (.byRule origin.instance_ origin.application (origin.picked prior)) .nil := by
  rw [← Category.assoc, origin.arrow_displayed,
    ReadOnlyContextExtension.readStep_adds, origin.picked_generator]

end KernelOrigin

namespace ClientOrigin

variable {firing : SelectedFiring definition false before after}
  (origin : firing.ClientOrigin)

include origin

theorem protected_unchanged (occurrence : Occurrence) :
    (occurrence ∈ after.present ∧ location occurrence = .judgments) ↔
      (occurrence ∈ before.present ∧ location occurrence = .judgments) := by
  have noTake : firing.picked.taken = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [origin.rule_eq, postRule, List.length_nil] using firing.qualified.take_length.symm
  rw [firing.destination]
  constructor
  · rintro ⟨present, protectedHere⟩
    rcases mem_fire.mp present with stayed | made
    · exact ⟨stayed.1, protectedHere⟩
    · have member : occurrence ∈ firing.picked.made := by
        simpa only [Selection.commit, List.mem_toFinset] using made
      have valueMember := List.mem_map_of_mem (f := label) member
      rw [firing.qualified.outputs, origin.rule_eq] at valueMember
      have same : label occurrence = (.requests, origin.value) :=
        List.mem_singleton.mp valueMember
      have requested : location occurrence = .requests := congrArg Prod.fst same
      rw [protectedHere] at requested
      cases requested
  · rintro ⟨present, protectedHere⟩
    refine ⟨mem_fire.mpr (Or.inl ⟨present, ?_⟩), protectedHere⟩
    simp only [Selection.commit, noTake, List.toFinset_nil, Finset.notMem_empty, not_false_eq_true]

def board (prior : Board before) : Board after :=
  prior.retain origin.protected_unchanged

/-- Public data publication changes no protected premise or proof node. -/
def arrow (prior : Board before) :
    prior.context definition ⟶ (origin.board prior).context definition :=
  𝟙 (prior.context definition)

end ClientOrigin
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings.SelectedFiring
