import Mettapedia.OSLF.Syntax.RewriteEventHistory
import Mettapedia.OSLF.Syntax.RuleListEventEmbedding

/-!
# Finite event histories under forward operational interpretations

Mapping a finite history needs a map of source events to target events; it
does not need the stronger condition that every target event leaving an image
state lift back to the source. The latter is a separate coverage property.
This module extends the existing authored event-history construction with
the ordinary forward maps used by semantic model interpretations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RewriteEventHistory

open CategoryTheory
open Mettapedia.GSLT.ProofRelevant

universe u

/-- An operational interpretation preserving equations and individual
firings. No target-event coverage or reflection is required. -/
structure ForwardEvidenceMap (source target : ProofRelevantGSLT.{u}) where
  mapTerm : source.theory.Term → target.theory.Term
  mapEquiv : ∀ {left right}, source.theory.Equiv left right →
    target.theory.Equiv (mapTerm left) (mapTerm right)
  mapEvidence : ∀ {sourceTerm sourceTarget},
    source.steps.Evidence sourceTerm sourceTarget →
      target.steps.Evidence (mapTerm sourceTerm) (mapTerm sourceTarget)

namespace ForwardEvidenceMap

/-- Identity interpretation of evidence. -/
def id (system : ProofRelevantGSLT.{u}) :
    ForwardEvidenceMap system system where
  mapTerm := fun term => term
  mapEquiv := fun equivalent => equivalent
  mapEvidence := fun event => event

/-- Forward operational interpretations compose. -/
def comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : ForwardEvidenceMap first middle)
    (later : ForwardEvidenceMap middle last) :
    ForwardEvidenceMap first last where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapEvidence := fun event => later.mapEvidence (earlier.mapEvidence event)

/-- A forward interpretation maps the generating event quiver. -/
def generators {source target : ProofRelevantGSLT.{u}}
    (f : ForwardEvidenceMap source target) :
    State source ⥤q State target where
  obj state := ⟨f.mapTerm state.term⟩
  map event := f.mapEvidence event

/-- Extend the generator map to all finite, occurrence-preserving histories. -/
def histories {source target : ProofRelevantGSLT.{u}}
    (f : ForwardEvidenceMap source target) :
    HistoryCategory source ⥤ HistoryCategory target :=
  Paths.lift (f.generators ⋙q Paths.of (State target))

/-- A singleton history maps to the selected target firing occurrence. -/
theorem histories_generator {source target : ProofRelevantGSLT.{u}}
    (f : ForwardEvidenceMap source target)
    {a b : State source} (event : a ⟶ b) :
    f.histories.map event.toPath =
      Quiver.Hom.toPath (f.mapEvidence event) :=
  Paths.lift_toPath _ event

/-- Identity interpretation fixes the full history category. -/
theorem histories_id (system : ProofRelevantGSLT.{u}) :
    (ForwardEvidenceMap.id system).histories =
      𝟭 (HistoryCategory system) := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro a b event
    rfl

/-- Interpreting a path through two stages agrees with the composite
interpretation, including every event occurrence and path concatenation. -/
theorem histories_comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : ForwardEvidenceMap first middle)
    (later : ForwardEvidenceMap middle last) :
    (earlier.comp later).histories =
      earlier.histories ⋙ later.histories := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro a b event
    rfl

end ForwardEvidenceMap

open Mettapedia.OSLF.Binding.RuleListEventEmbedding

/-- Extending an authored rule list maps every existing firing occurrence
forward, without asserting that newly added target rules lift back. -/
def ruleEmbeddingForward {S : Signature} {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) {old larger : RuleList S M}
    (embedding : Embedding old larger) (sort : S.Srt) :
    ForwardEvidenceMap
      (authoredSystem (presentation E old) sort)
      (authoredSystem (presentation E larger) sort) where
  mapTerm := fun term => term
  mapEquiv := fun equivalent => equivalent
  mapEvidence := by
    intro sourceTerm sourceTarget event
    obtain ⟨index, firing⟩ := event
    exact ⟨embedding.index index,
      (embedding.rule_eq index).symm ▸ firing⟩

/-- An exact or locally covered translation supplies an ordinary forward
model map. Its history action is unchanged when coverage is forgotten. -/
def forwardOfTranslation {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    ForwardEvidenceMap source target where
  mapTerm := translation.mapTerm
  mapEquiv := translation.mapEquiv
  mapEvidence := translation.mapEvidence

theorem forwardOfTranslation_histories
    {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    (forwardOfTranslation translation).histories =
      mapHistories translation := rfl

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

/-- Select the first of two occurrences of rho's COMM rule. -/
def firstCommEmbedding : Embedding rho.toUnpositioned.rules
    duplicatedCommunication.rules where
  index := fun _ => ⟨0, by decide⟩
  index_injective := by
    intro first second _
    fin_cases first
    fin_cases second
    rfl
  rule_eq := by
    intro index
    fin_cases index
    rfl

/-- A genuine authored forward interpretation from one COMM occurrence to
two. It need not cover the second target occurrence. -/
def firstCommForward : ForwardEvidenceMap
    (authoredSystem rho.toUnpositioned Srt.pr)
    (authoredSystem duplicatedCommunication Srt.pr) :=
  ruleEmbeddingForward rhoE firstCommEmbedding Srt.pr

/-- On the concrete source-order COMM witness, the forward map selects the
first target occurrence and preserves its whole firing data. -/
theorem firstCommForward_event :
    firstCommForward.mapEvidence rhoCommunicationEvidence =
      firstCommunicationEvent := by
  rfl

private def sourceState :
    State (authoredSystem rho.toUnpositioned Srt.pr) :=
  ⟨parT commInput commOutput⟩

private def targetState :
    State (authoredSystem rho.toUnpositioned Srt.pr) :=
  ⟨commTarget⟩

/-- The path interpretation maps the authored one-step communication history
to its first tagged target history, retaining the selected occurrence. -/
theorem firstCommForward_history :
    firstCommForward.histories.map
      (show sourceState ⟶ targetState from rhoCommunicationEvidence).toPath =
    (show (firstCommForward.generators.obj sourceState) ⟶
        (firstCommForward.generators.obj targetState) from
      firstCommunicationEvent).toPath := by
  rw [ForwardEvidenceMap.histories_generator]
  rfl

/-- The second target COMM occurrence cannot come from the source rule-list
embedding. Forward interpretation is therefore strictly weaker than
event-surjective coverage. -/
theorem firstCommForward_not_event_surjective :
    ¬ Function.Surjective
      (firstCommForward.mapEvidence (sourceTerm := parT commInput commOutput)
        (sourceTarget := commTarget)) := by
  intro surjective
  obtain ⟨sourceEvent, mapped⟩ :=
    surjective secondCommunicationEvent
  obtain ⟨index, firing⟩ := sourceEvent
  fin_cases index
  have impossible : (0 : Fin 2) = 1 :=
    congrArg Sigma.fst mapped
  cases impossible

end RhoExample

end Mettapedia.OSLF.Binding.RewriteEventHistory
