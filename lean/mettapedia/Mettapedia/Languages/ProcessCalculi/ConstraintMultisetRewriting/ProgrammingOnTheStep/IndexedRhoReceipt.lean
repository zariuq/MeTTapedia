import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedResumption
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Reactions
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell

/-!
# Handing a realized closed rho reaction to an indexed continuation

The existing closed rho compiler supplies an actual reaction ending at
the declared target up to the source equations. The reply to the
continuation carries that reaction together with the typed source
receipt. The resumption uses the indexed occurrence rule and publishes
a value in the fibre of the retained communication, including its
revision. This models a separate checked handoff after communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedRhoReceipt

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DependentReflectiveCommunicationCell
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol

open IndexedResumption
open FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
  (Point Reaction compile readback source_step_congr source_roundtrip reaction_lifts)

structure ReactionReceipt (source : RhoProcess) (communication : ExactCommunication) where
  source_eq : source = (exactEndpoints communication).1
  target : Point
  reacted : Reaction (compile source) target
  target_eq : rhoProcessEquations.r (readback target) (exactEndpoints communication).2

/-- Independently authored typed communication is realized by actual
firings of the closed transform program, including one communication. -/
theorem reaction_receipt (communication : ExactCommunication) :
    Nonempty (ReactionReceipt (exactEndpoints communication).1 communication) := by
  have sourceStep := (exactCommunication_enters_saturated_rho communication).2.1
  have atCompiled := (source_step_congr (source_roundtrip _)
    (rhoProcessEquations.iseqv.refl _)).mpr sourceStep
  obtain ⟨target, reacted, readback⟩ := reaction_lifts _ atCompiled
  exact ⟨⟨rfl, target, reacted, readback⟩⟩

abbrev Phase := RhoProcess ⊕ ExactCommunication

/-- The reply carries the realized reaction. A completed phase retains the
exact typed communication, including the revision. -/
def ReactionResponse : Phase → Phase → Type 1
  | .inl source, .inr communication => ReactionReceipt source communication
  | _, _ => PEmpty

def Value : Phase → Type
  | .inl _ => PEmpty
  | .inr communication => revisionContinuation communication

abbrev operations := protocol ReactionResponse

def resume {source : RhoProcess} {communication : ExactCommunication}
    (receipt : ReactionReceipt source communication) : Resume operations Value := by
  let response : Outgoing ReactionResponse (.inl source) := ⟨.inr communication, receipt⟩
  exact ⟨0, .inl source, roundOf ReactionResponse response (fun
    | ⟨.inl _, impossible⟩ => impossible.elim
    | ⟨.inr event, _⟩ => initialContinuationToken event), response⟩

def ready {source : RhoProcess} {communication : ExactCommunication}
    (receipt : ReactionReceipt source communication) : Inventory operations Value := by
  let request := resume receipt
  exact ⟨PUnit.unit, [], {0, 1}, fun identity =>
    if identity = 0 then .suspended request.ticket request.round
    else .offered request.ticket request.round.1 request.reply⟩

theorem receives {source : RhoProcess} {communication : ExactCommunication}
    (receipt : ReactionReceipt source communication) :
    (machine operations Value .one).Admits (s := ready receipt)
      (firing (resume receipt) .one (ready receipt) 0 1 2) := by
  apply (admits_iff (resume receipt) .one (ready receipt) 0 1 2).mpr
  refine ⟨by decide, ?_, ?_, ?_, by simp [ready], rfl, rfl⟩
  · change 0 ∈ ({0, 1} : Finset Nat)
    decide
  · change 1 ∈ ({0, 1} : Finset Nat)
    decide
  · change 2 ∉ ({0, 1} : Finset Nat)
    decide

/-- The actual successor carries the exact indexed result of the handoff. -/
theorem published {source : RhoProcess} {communication : ExactCommunication}
    (receipt : ReactionReceipt source communication) :
    (after (receives receipt)).label 2 =
      .completed 0 (selectResponse operations (resume receipt).round (resume receipt).reply) :=
  (published_outcome (receives receipt)).2

/-- Every exact source communication has a realized reaction and an
admitted continuation publication with its original dependent index. -/
theorem realized (communication : ExactCommunication) :
    ∃ receipt : ReactionReceipt (exactEndpoints communication).1 communication,
      (after (receives receipt)).label 2 =
        .completed 0 (selectResponse operations (resume receipt).round (resume receipt).reply) ∧
      (selectResponse operations (resume receipt).round (resume receipt).reply).1.target = .inr communication :=
  (reaction_receipt communication).elim fun receipt => ⟨receipt, published receipt, rfl⟩

/-- Observe the typed phase of a completed occurrence. -/
def completedPhase : Row operations Value → Option Phase
  | .completed _ result => some result.1.target
  | _ => none

/-- Equal source and target process observations do not identify the
published results at revisions zero and one. -/
theorem published_revisions_distinct
    (zero : ReactionReceipt (exactEndpoints zeroCommunication).1 zeroCommunication)
    (one : ReactionReceipt (exactEndpoints oneCommunication).1 oneCommunication) :
    (after (receives zero)).label 2 ≠ (after (receives one)).label 2 := by
  intro equal
  rw [published, published] at equal
  have phases := congrArg completedPhase equal
  change some (Sum.inr zeroCommunication : Phase) = some (.inr oneCommunication) at phases
  have same := Sum.inr.inj (Option.some.inj phases)
  have sameRevision := congrArg (fun e : ExactCommunication => e.1.revision) same
  nomatch sameRevision

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedRhoReceipt
