import Mettapedia.GSLT.LanguageDef.ProofGSLTRecurrentTraceAuthority
import Mettapedia.GSLT.LanguageDef.ProofGSLTFiniteTraceCanary

/-!
# Separating examples for recurrent GSLT traces

The two-state toggle supplies both sides of the finite/infinite boundary.  A
locally checked alternating controller has a finite progress certificate for
visiting `true` infinitely often.  The same locally legal cycle cannot prove
recurrence when no state is accepting: its two required strict rank decreases
would form an impossible loop.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.RecurrentTraceCanary

open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.GSLT.LanguageDef.ProofGSLT.FiniteTraceCanary

def alternatingAction (state : Bool) :
    TraceLink toggleTheory ToggleEvidence :=
  match state with
  | false => ⟨true, .up⟩
  | true => ⟨false, .down⟩

def alternatingNext : Bool → Bool
  | false => true
  | true => false

def alternatingController :
    MemorylessController Bool (TraceLink toggleTheory ToggleEvidence) where
  active := fun _ => true
  action := alternatingAction
  next := alternatingNext

def acceptsTrue : Bool → Bool
  | false => false
  | true => true

def alternatingSystem :=
  auditedLabeledSystem toggleStepAuthority acceptsTrue

def alternatingMeasure : ProgressMeasure Bool where
  rank
    | false => 1
    | true => 0

def alternatingClaim :
    RecurrentTraceClaim toggleTheory ToggleEvidence :=
  ⟨false, alternatingController⟩

theorem alternatingMeasure_valid :
    alternatingMeasure.Valid alternatingSystem alternatingController false := by
  constructor
  · constructor
    · rfl
    · intro state _
      cases state <;> exact ⟨rfl, rfl⟩
  · intro state _
    cases state <;>
      simp [alternatingSystem, auditedLabeledSystem, acceptsTrue,
        alternatingController, alternatingNext, alternatingMeasure]

def alternatingAuthority :=
  recurrentTraceAuthority "toggle-recurrence-v1"
    toggleStepAuthority acceptsTrue

/-- A finite rank certificate is accepted for the infinite recurrence claim. -/
theorem alternatingMeasure_accepted :
    alternatingAuthority.check alternatingClaim alternatingMeasure = true := by
  exact (ProgressMeasure.check_eq_true_iff alternatingSystem
    alternatingController alternatingMeasure false).2 alternatingMeasure_valid

/-- Acceptance entails both genuine toggle steps forever and infinitely many
visits to `true`. -/
theorem alternatingClaim_meaning :
    alternatingClaim.Meaning acceptsTrue :=
  alternatingAuthority.sound alternatingMeasure_accepted

/-! ## Local cycles alone do not prove recurrence -/

def acceptsNothing (_ : Bool) : Bool := false

def neverAcceptingSystem :=
  auditedLabeledSystem toggleStepAuthority acceptsNothing

/-- The alternating controller remains locally legal when the observation is
changed to one that accepts no states. -/
theorem alternatingController_locallyValid_without_acceptance :
    alternatingController.LocallyValid neverAcceptingSystem false := by
  constructor
  · rfl
  · intro state _
    cases state <;> exact ⟨rfl, rfl⟩

/-- No natural-valued progress measure can certify a locally legal cycle with
no accepting state. -/
theorem no_progress_measure_without_acceptance (measure : ProgressMeasure Bool) :
    ¬ measure.Valid neverAcceptingSystem alternatingController false := by
  intro valid
  have decreasesAtFalse := valid.2 false rfl
  have decreasesAtTrue := valid.2 true rfl
  simp [neverAcceptingSystem, auditedLabeledSystem, acceptsNothing,
    alternatingController, alternatingNext] at decreasesAtFalse decreasesAtTrue
  omega

/-- The corresponding semantic recurrence claim is false even though every
selected local edge is genuine. -/
theorem no_recurrence_without_acceptance :
    ¬ alternatingClaim.Meaning acceptsNothing := by
  intro recurrent
  have execution := alternatingController.canonicalExecution false
  obtain ⟨visit, _, accepted⟩ := (recurrent execution).2 0
  simp [acceptsNothing] at accepted

#print axioms alternatingMeasure_accepted
#print axioms alternatingClaim_meaning
#print axioms alternatingController_locallyValid_without_acceptance
#print axioms no_progress_measure_without_acceptance
#print axioms no_recurrence_without_acceptance

end Mettapedia.GSLT.LanguageDef.ProofGSLT.RecurrentTraceCanary
