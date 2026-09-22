import Mettapedia.GSLT.Core.InterleavingRoute
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy

/-!
# Independent certificate searches: proofs versus scheduling paths

Two actual open-certificate machines run on separate state components. Their
proof-relevant interleaving erases exactly to the existing interleaving GSLT,
since the component equations are literal state equality. Any completed
interleaving retains both component proofs and their exact use ledgers.

For any two supplied proofs, left-first and right-first executions recover
the same proofs but are distinct routes. Thus proof equality determines a
route in each pending-first component but does not determine the combined
schedule. This is not a model of CeTTa's agenda, shared-state search, failure
history, or a decision procedure for finding the supplied proofs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open OpenSearchMachine

variable (leftDefinition rightDefinition : ValidatedCalculusLanguageDef)
variable (leftContext rightContext : List Pattern)

/-- Reuse the established interleaving product, with each search's existing
equational and operational authority unchanged. -/
abbrev theory : GSLT :=
  GSLT.interleavingProduct
    (OpenSearchModalAdequacy.theory leftDefinition leftContext)
    (OpenSearchModalAdequacy.theory rightDefinition rightContext)

/-- One retained event acts on exactly one independent search state. -/
abbrev Step := Interleaving.Step
  (OpenSearchMachine.Step leftDefinition leftContext)
  (OpenSearchMachine.Step rightDefinition rightContext)

/-- For these literal-equality component theories, the retained interleaving
events erase to exactly, not merely a subset of, the existing product steps. -/
theorem step_erases_iff
    (source target : State leftContext × State rightContext) :
    Nonempty (Step leftDefinition rightDefinition leftContext rightContext
      source target) ↔
      (theory leftDefinition rightDefinition leftContext rightContext).Step
        source target := by
  constructor
  · rintro ⟨event⟩
    exact Interleaving.eraseStep
      (OpenSearchModalAdequacy.system leftDefinition leftContext)
      (OpenSearchModalAdequacy.system rightDefinition rightContext) event
  · cases source with
    | mk leftSource rightSource =>
      cases target with
      | mk leftTarget rightTarget =>
        intro step
        change
          (Nonempty (OpenSearchMachine.Step leftDefinition leftContext
              leftSource leftTarget) ∧ rightSource = rightTarget) ∨
          (leftSource = leftTarget ∧
            Nonempty (OpenSearchMachine.Step rightDefinition rightContext
              rightSource rightTarget)) at step
        rcases step with ⟨⟨event⟩, hold⟩ | ⟨hold, ⟨event⟩⟩
        · subst rightTarget
          exact ⟨.left event rightSource⟩
        · subst leftTarget
          exact ⟨.right leftSource event⟩

/-- Independent search as a proof-relevant realization of the existing
interleaving product. -/
def system : ProofRelevantGSLT where
  theory := theory leftDefinition rightDefinition leftContext rightContext
  steps := {
    Evidence := Step leftDefinition rightDefinition leftContext rightContext
    erases_iff := step_erases_iff leftDefinition rightDefinition
      leftContext rightContext
  }

variable {leftDefinition rightDefinition leftContext rightContext}
variable {leftGoal rightGoal : Pattern}

/-- All finite completed schedules at the two fixed exact discharge ledgers. -/
abbrev CompletedRoute
    (leftLedger : List (Fin leftContext.length))
    (rightLedger : List (Fin rightContext.length)) :=
  Route (Step leftDefinition rightDefinition leftContext rightContext)
    ((⟨[leftGoal], []⟩ : State leftContext),
      (⟨[rightGoal], []⟩ : State rightContext))
    (⟨[], leftLedger⟩, ⟨[], rightLedger⟩)

/-- Forget only the schedule; retain the two exact reconstructed proofs. -/
def proofPair
    {leftLedger : List (Fin leftContext.length)}
    {rightLedger : List (Fin rightContext.length)}
    (route : CompletedRoute (leftDefinition := leftDefinition)
      (rightDefinition := rightDefinition) (leftGoal := leftGoal)
      (rightGoal := rightGoal) leftLedger rightLedger) :
    OpenDerivation leftDefinition leftContext leftGoal ×
      OpenDerivation rightDefinition rightContext rightGoal :=
  (derivationOfCompleteRoute (Interleaving.projectLeft route),
    derivationOfCompleteRoute (Interleaving.projectRight route))

/-- The proof-pair view keeps both exact premise-use ledgers. -/
theorem proofPair_ledgers
    {leftLedger : List (Fin leftContext.length)}
    {rightLedger : List (Fin rightContext.length)}
    (route : CompletedRoute (leftDefinition := leftDefinition)
      (rightDefinition := rightDefinition) (leftGoal := leftGoal)
      (rightGoal := rightGoal) leftLedger rightLedger) :
    holeOccurrences (proofPair route).1 = leftLedger ∧
      holeOccurrences (proofPair route).2 = rightLedger :=
  ⟨derivationOfCompleteRoute_holes (Interleaving.projectLeft route),
    derivationOfCompleteRoute_holes (Interleaving.projectRight route)⟩

/-- Two schedules of the same actual proof pair are different paths. Each
component has a genuine step because its pending goal must be discharged. -/
theorem same_proofs_distinct_schedules
    (leftProof : OpenDerivation leftDefinition leftContext leftGoal)
    (rightProof : OpenDerivation rightDefinition rightContext rightGoal) :
    let leftFirst := Interleaving.leftThenRight
      (runToCompletion leftProof) (runToCompletion rightProof)
    let rightFirst := Interleaving.rightThenLeft
      (runToCompletion leftProof) (runToCompletion rightProof)
    leftFirst ≠ rightFirst ∧
      proofPair leftFirst = (leftProof, rightProof) ∧
      proofPair rightFirst = (leftProof, rightProof) := by
  dsimp only
  refine ⟨Interleaving.schedules_distinct _ _
    (completeRoute_length_ne_zero _) (completeRoute_length_ne_zero _), ?_, ?_⟩
  · simp [proofPair, Interleaving.leftThenRight,
      derivationOfCompleteRoute_runToCompletion]
  · simp [proofPair, Interleaving.rightThenLeft,
      derivationOfCompleteRoute_runToCompletion]

/-- Even retaining the exact two proofs and their fixed ledgers cannot
recover the schedule. The counterexample uses the supplied genuine proofs. -/
theorem proofPair_not_injective
    (leftProof : OpenDerivation leftDefinition leftContext leftGoal)
    (rightProof : OpenDerivation rightDefinition rightContext rightGoal) :
    ¬ Function.Injective
      (proofPair (leftDefinition := leftDefinition)
        (rightDefinition := rightDefinition) (leftGoal := leftGoal)
        (rightGoal := rightGoal)
        (leftLedger := holeOccurrences leftProof)
        (rightLedger := holeOccurrences rightProof)) := by
  intro injective
  obtain ⟨distinct, leftEq, rightEq⟩ :=
    same_proofs_distinct_schedules leftProof rightProof
  exact distinct (injective (leftEq.trans rightEq.symm))

/-- A client inspecting the schedule cannot be implemented from the exact
proof pair alone. This rules out that information loss before such a client. -/
theorem schedule_does_not_factor_through_proofPair
    (leftProof : OpenDerivation leftDefinition leftContext leftGoal)
    (rightProof : OpenDerivation rightDefinition rightContext rightGoal) :
    ¬ ∃ observe : (OpenDerivation leftDefinition leftContext leftGoal ×
        OpenDerivation rightDefinition rightContext rightGoal) → List Bool,
      ∀ route : CompletedRoute (leftDefinition := leftDefinition)
        (rightDefinition := rightDefinition) (leftGoal := leftGoal)
        (rightGoal := rightGoal) (holeOccurrences leftProof)
        (holeOccurrences rightProof),
        observe (proofPair route) = Route.trace Interleaving.side route := by
  rintro ⟨observe, agrees⟩
  obtain ⟨_, leftEq, rightEq⟩ :=
    same_proofs_distinct_schedules leftProof rightProof
  have sameObservation := congrArg observe (leftEq.trans rightEq.symm)
  rw [agrees, agrees] at sameObservation
  exact Interleaving.schedule_traces_distinct _ _
    (completeRoute_length_ne_zero _) (completeRoute_length_ne_zero _)
    sameObservation

/-- No inhabitants can be created on either side by interleaving. -/
theorem no_completion_of_left_unprovable
    {leftLedger : List (Fin leftContext.length)}
    {rightLedger : List (Fin rightContext.length)}
    (unprovable : ¬ Nonempty
      (OpenDerivation leftDefinition leftContext leftGoal)) :
    ¬ Nonempty (CompletedRoute (leftDefinition := leftDefinition)
      (rightDefinition := rightDefinition) (leftGoal := leftGoal)
      (rightGoal := rightGoal) leftLedger rightLedger) := by
  rintro ⟨route⟩
  exact unprovable ⟨(proofPair route).1⟩

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch.step_erases_iff
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch.proofPair_ledgers
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch.same_proofs_distinct_schedules
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch.proofPair_not_injective
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch.schedule_does_not_factor_through_proofPair
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.IndependentSearch.no_completion_of_left_unprovable
