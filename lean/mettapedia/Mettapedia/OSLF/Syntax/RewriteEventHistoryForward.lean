import Mettapedia.OSLF.Syntax.RewriteEventHistory
import Mettapedia.OSLF.Syntax.RuleListEventEmbedding
import Mettapedia.CategoryTheory.RunAccount

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

open _root_.CategoryTheory
open Mettapedia.GSLT.ProofRelevant

universe u v

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

/-! A lowering can implement one occurrence by several target events. A
fusion can remove an administrative event. The same free history category
supports both, without replacing occurrence evidence by endpoint equality. -/

/-- An occurrence-sensitive operational interpretation by finite paths.
The selected path may depend on the source occurrence, even when two
occurrences have equal endpoints. Coverage and faithfulness are separate. -/
structure PathEvidenceMap (source target : ProofRelevantGSLT.{u}) where
  mapTerm : source.theory.Term → target.theory.Term
  mapEquiv : ∀ {left right}, source.theory.Equiv left right →
    target.theory.Equiv (mapTerm left) (mapTerm right)
  mapEvidence : ∀ {sourceTerm sourceTarget},
    source.steps.Evidence sourceTerm sourceTarget →
      History target ⟨mapTerm sourceTerm⟩ ⟨mapTerm sourceTarget⟩

namespace PathEvidenceMap

/-- Interpret a generating event in the existing target history category. -/
def generators {source target : ProofRelevantGSLT.{u}}
    (f : PathEvidenceMap source target) :
    State source ⥤q HistoryCategory target where
  obj state := ⟨f.mapTerm state.term⟩
  map event := f.mapEvidence event

/-- Substitute the selected finite path for every source event. -/
def histories {source target : ProofRelevantGSLT.{u}}
    (f : PathEvidenceMap source target) :
    HistoryCategory source ⥤ HistoryCategory target :=
  interpret source f.generators

theorem histories_generator {source target : ProofRelevantGSLT.{u}}
    (f : PathEvidenceMap source target)
    {a b : State source} (event : a ⟶ b) :
    f.histories.map event.toPath = f.mapEvidence event :=
  interpret_generator source f.generators event

/-- Strict event maps use singleton paths and retain their existing action. -/
def ofForward {source target : ProofRelevantGSLT.{u}}
    (f : ForwardEvidenceMap source target) : PathEvidenceMap source target where
  mapTerm := f.mapTerm
  mapEquiv := f.mapEquiv
  mapEvidence {sourceTerm sourceTarget} event :=
    (show (⟨f.mapTerm sourceTerm⟩ : State target) ⟶ ⟨f.mapTerm sourceTarget⟩ from
      f.mapEvidence event).toPath

theorem histories_ofForward {source target : ProofRelevantGSLT.{u}}
    (f : ForwardEvidenceMap source target) :
    (ofForward f).histories = f.histories := rfl

/-- Identity retains every event as a singleton. -/
def id (system : ProofRelevantGSLT.{u}) : PathEvidenceMap system system :=
  ofForward (ForwardEvidenceMap.id system)

theorem histories_id (system : ProofRelevantGSLT.{u}) :
    (id system).histories = 𝟭 (HistoryCategory system) :=
  ForwardEvidenceMap.histories_id system

/-- A second lowering substitutes into all events of the first lowering. -/
def comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : PathEvidenceMap first middle)
    (later : PathEvidenceMap middle last) : PathEvidenceMap first last where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapEvidence event := later.histories.map (earlier.mapEvidence event)

/-- Path substitution is compositional, including zero-length and
multi-event implementations. -/
theorem histories_comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : PathEvidenceMap first middle)
    (later : PathEvidenceMap middle last) :
    (earlier.comp later).histories = earlier.histories ⋙ later.histories := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro a b event
    exact congrArg later.histories.map (earlier.histories_generator event)

/-- A uniform bound on primitive implementations lifts to the complete
target path. This is a unit-transition bound; assigning machine time or
another resource requires the corresponding event account. -/
theorem length_bound {source target : ProofRelevantGSLT.{u}}
    (f : PathEvidenceMap source target) (multiplier : Nat)
    (eventBound : ∀ {a b : State source} (event : a ⟶ b),
      (f.mapEvidence event).length ≤ multiplier)
    {a b : State source} (history : History source a b) :
    (f.histories.map history).length ≤ multiplier * history.length := by
  induction history with
  | nil => exact Nat.zero_le _
  | cons past event ih =>
      calc
        (f.histories.map (past.cons event)).length =
            (f.histories.map past).length + (f.mapEvidence event).length :=
          Quiver.Path.length_comp _ _
        _ ≤ multiplier * past.length + multiplier := Nat.add_le_add ih (eventBound event)
        _ = multiplier * (past.cons event).length := by
          rw [Quiver.Path.length_cons, Nat.mul_add, Nat.mul_one]

/-- Successive lowerings multiply their checked expansion bounds. No bound
is inferred merely from preservation of the returned answer. -/
theorem length_bound_comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : PathEvidenceMap first middle) (later : PathEvidenceMap middle last)
    (firstBound secondBound : Nat)
    (earlierBound : ∀ {a b : State first} (event : a ⟶ b),
      (earlier.mapEvidence event).length ≤ firstBound)
    (laterBound : ∀ {a b : State middle} (event : a ⟶ b),
      (later.mapEvidence event).length ≤ secondBound)
    {a b : State first} (history : History first a b) :
    ((earlier.comp later).histories.map history).length ≤
      (secondBound * firstBound) * history.length := by
  rw [histories_comp]
  calc
    (later.histories.map (earlier.histories.map history)).length ≤
        secondBound * (earlier.histories.map history).length :=
      later.length_bound secondBound laterBound _
    _ ≤ secondBound * (firstBound * history.length) :=
      Nat.mul_le_mul_left secondBound (earlier.length_bound firstBound earlierBound history)
    _ = (secondBound * firstBound) * history.length := (Nat.mul_assoc _ _ _).symm

/-- An independently chosen source account is preserved on every history
when each event's full implementing path has the required account. The
coefficient monoids need not commute. -/
theorem account_preserved {source target : ProofRelevantGSLT.{u}}
    {M N : Type v} [Monoid M] [Monoid N]
    (f : PathEvidenceMap source target)
    (sourceAccount : Mettapedia.Effects.RunAccount (HistoryCategory source) M)
    (targetAccount : Mettapedia.Effects.RunAccount (HistoryCategory target) N)
    (change : M →* N)
    (eventLaw : ∀ {a b : State source} (event : a ⟶ b),
      targetAccount.of (f.mapEvidence event) =
        change (sourceAccount.of event.toPath)) :
    targetAccount.comap f.histories = sourceAccount.map change := by
  apply Mettapedia.Effects.RunAccount.ext
  funext a b history
  change targetAccount.of (f.histories.map history) =
    change (sourceAccount.of history)
  refine Paths.induction (V := State source)
    (P := fun route => targetAccount.of (f.histories.map route) =
      change (sourceAccount.of route)) ?_ ?_ history
  · intro state
    rw [f.histories.map_id, targetAccount.of_id,
      sourceAccount.of_id, change.map_one]
  · intro before middle after past event ih
    rw [f.histories.map_comp, targetAccount.of_comp, sourceAccount.of_comp,
      change.map_mul, ih]
    change _ * targetAccount.of (f.histories.map event.toPath) =
      _ * change (sourceAccount.of event.toPath)
    rw [f.histories_generator]
    exact congrArg (fun value => change (sourceAccount.of past) * value) (eventLaw event)

end PathEvidenceMap

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
