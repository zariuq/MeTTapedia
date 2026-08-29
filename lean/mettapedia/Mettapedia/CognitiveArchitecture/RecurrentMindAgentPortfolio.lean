import Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization

/-!
# A checked recurrent portfolio of foreground and background mind-agents

This worked discriminator cycles one foreground role and four background
organizational roles through the same finite GSLT controller:

* foreground chaining;
* ECAN attention maintenance;
* incremental compression;
* PLN appraisal; and
* premise selection.

Every controller action is locally checked, every finite prefix retains exact
occurrence identity, and every action is independently bound to one typed
resident in an authored triggered space.  Same-cycle generated-work selection
and ECAN long-term protection are proved separately.  This is a semantic
portfolio canary, not a claim that the current CeTTa store realizes it.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities

/-! ## Typed roles and checked cyclic dynamics -/

inductive Role where
  | foregroundChaining
  | ecan
  | incrementalCompression
  | pln
  | premiseSelection
deriving DecidableEq, Repr, Fintype

def nextRole : Role -> Role
  | .foregroundChaining => .ecan
  | .ecan => .incrementalCompression
  | .incrementalCompression => .pln
  | .pln => .premiseSelection
  | .premiseSelection => .foregroundChaining

@[reducible] def portfolioTheory : GSLT where
  Term := Role
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => target = nextRole source
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def portfolioStepAuthority : StepAuthority Unit portfolioTheory where
  id := ()
  Certificate := Unit
  check := fun claim _ => decide (claim.target = nextRole claim.source)
  sound := by
    intro claim _ accepted
    change claim.target = nextRole claim.source
    exact of_decide_eq_true accepted

def portfolioController :
    MemorylessController portfolioTheory.Term
      (TraceLink portfolioTheory portfolioStepAuthority.Certificate) where
  active := fun _ => true
  action := fun source => ⟨nextRole source, ()⟩
  next := nextRole

def portfolioClaim :
    RecurrentTraceClaim portfolioTheory
      portfolioStepAuthority.Certificate where
  root := .foregroundChaining
  controller := portfolioController

def foregroundAccepting : Role -> Bool
  | .foregroundChaining => true
  | _ => false

/-- Rank is distance through the background portion of the cycle back to the
foreground accepting state. -/
def portfolioMeasure : ProgressMeasure Role where
  rank
    | .foregroundChaining => 0
    | .ecan => 3
    | .incrementalCompression => 2
    | .pln => 1
    | .premiseSelection => 0

/-- The five-role portfolio passes the ordinary recurrent checker. -/
theorem portfolio_checker_accepts :
    (recurrentChecker () portfolioStepAuthority foregroundAccepting).check
      portfolioClaim portfolioMeasure = true := by
  decide

theorem portfolio_checked_consequences :
    AuditedPrefixProductive portfolioStepAuthority foregroundAccepting
        portfolioClaim /\
      portfolioClaim.Meaning foregroundAccepting :=
  recurrentChecker_acceptance_consequences portfolioStepAuthority
    foregroundAccepting portfolioClaim () portfolioMeasure
    portfolio_checker_accepts

/-! ## Triggered-space realization -/

abbrev Trigger := Unit
abbrev Resident := Role
abbrev Occurrence := TriggeredOccurrence Trigger Resident

/-- Every role is resident and one heartbeat may generate one occurrence for
each of them. -/
def serviceSpace : Space Trigger Resident where
  resident := fun _ => True
  enabled := fun _ _ => True
  enabled_resident := fun _ _ _ => trivial

def heartbeatTrace (_cycle : Nat) : Option Trigger := some ()

/-- The action target names the exact resident which the step activates. -/
def actionRepresents
    (action : TraceLink portfolioTheory portfolioStepAuthority.Certificate)
    (trigger : Trigger) (resident : Resident) : Prop :=
  trigger = () /\ resident = action.target

theorem actionRepresents_resident_unique
    {action : TraceLink portfolioTheory portfolioStepAuthority.Certificate}
    {trigger : Trigger} {first second : Resident}
    (firstMeaning : actionRepresents action trigger first)
    (secondMeaning : actionRepresents action trigger second) :
    first = second :=
  firstMeaning.2.trans secondMeaning.2.symm

def portfolioCodec :
    Codec portfolioStepAuthority portfolioClaim serviceSpace heartbeatTrace
      actionRepresents where
  triggerOf := fun _ => ()
  residentOf := fun occurrence => occurrence.action.target
  semanticBinding := fun _ => ⟨rfl, rfl⟩
  generated := by
    intro occurrence
    exact serviceSpace.generated_occurrenceAt heartbeatTrace occurrence.index
      () occurrence.action.target rfl trivial

def portfolioExecution :
    ControlledExecution portfolioController portfolioClaim.root :=
  portfolioController.canonicalExecution portfolioClaim.root

def checkedPrefix (depth : Nat) :
    FiniteRoute
      (auditedRevisionTheory portfolioStepAuthority foregroundAccepting)
      (ControlledOccurrence portfolioTheory
        portfolioStepAuthority.Certificate)
      portfolioClaim.root :=
  finitePrefix portfolioStepAuthority foregroundAccepting portfolioClaim
    ((ProgressMeasure.check_eq_true_iff
      (auditedLabeledSystem portfolioStepAuthority foregroundAccepting)
      portfolioController portfolioMeasure portfolioClaim.root).mp
        portfolio_checker_accepts).1
    portfolioExecution depth

def generatedPrefix (depth : Nat) : List Occurrence :=
  portfolioCodec.realizeRoute foregroundAccepting (checkedPrefix depth)

/-- The first complete controller cycle activates each typed role exactly in
the authored order. -/
theorem first_cycle_resident_order :
    (generatedPrefix 5).map TriggeredOccurrence.resident =
      [.ecan, .incrementalCompression, .pln, .premiseSelection,
        .foregroundChaining] := by
  decide

/-- Equal resident values in later cycles retain distinct temporal occurrence
identity. -/
theorem foreground_occurrences_across_cycles_are_distinct :
    (generatedPrefix 5).getLast? ≠ (generatedPrefix 10).getLast? := by
  decide

/-! ## Independent selection and long-term attention -/

def selectedGenerated (cycle : Nat) (occurrence : Occurrence) : Prop :=
  serviceSpace.Generated heartbeatTrace cycle occurrence

def generatedSelection :
    BoundedGeneratedSelection serviceSpace heartbeatTrace 1
      selectedGenerated where
  selects cycle occurrence generated :=
    ⟨0, by omega, by simpa [selectedGenerated] using generated⟩

theorem generatedPrefix_member_selected
    (depth : Nat) {occurrence : Occurrence}
    (member : occurrence ∈ generatedPrefix depth) :
    exists offset, offset < 1 /\
      selectedGenerated (occurrence.generatedAt + offset) occurrence :=
  portfolioCodec.mem_realizeRoute_selected foregroundAccepting
    (checkedPrefix depth) generatedSelection member

/-- Every role carries one unit of LTI protection. -/
def portfolioEconomy : Economy Role Nat where
  shortTerm := 0
  longTerm := {
    balances :=
      Finsupp.single .foregroundChaining 1 +
      Finsupp.single .ecan 1 +
      Finsupp.single .incrementalCompression 1 +
      Finsupp.single .pln 1 +
      Finsupp.single .premiseSelection 1 }

theorem every_role_longTermProtected (role : Role) :
    portfolioEconomy.LongTermProtected 1 role := by
  cases role <;> simp [Economy.LongTermProtected, portfolioEconomy]

def portfolioTriggerCoverage :
    RecurringTriggerCoverage portfolioEconomy 1 1
      serviceSpace heartbeatTrace id where
  covers actor _isProtected start :=
    ⟨0, (), actor, by omega, rfl, trivial, rfl⟩

/-- All foreground and background residents satisfy the ECAN anti-starvation
contract under the independently supplied same-cycle selector. -/
theorem portfolio_honorsLongTerm :
    HonorsLongTermProtection portfolioEconomy 1 2
      (scheduledFromOccurrences
        (fun occurrence : Occurrence => occurrence.resident)
        selectedGenerated) :=
  portfolioTriggerCoverage.honorsLongTerm generatedSelection

/-- The complete positive control retains recurrence, exact role order,
selection, and LTI protection as separate facts. -/
theorem recurrent_typed_mindAgent_portfolio :
    portfolioClaim.Meaning foregroundAccepting /\
      (generatedPrefix 5).map TriggeredOccurrence.resident =
        [.ecan, .incrementalCompression, .pln, .premiseSelection,
          .foregroundChaining] /\
      (forall depth occurrence, occurrence ∈ generatedPrefix depth ->
        exists offset, offset < 1 /\
          selectedGenerated (occurrence.generatedAt + offset) occurrence) /\
      HonorsLongTermProtection portfolioEconomy 1 2
        (scheduledFromOccurrences
          (fun occurrence : Occurrence => occurrence.resident)
          selectedGenerated) := by
  exact ⟨portfolio_checked_consequences.2, first_cycle_resident_order,
    generatedPrefix_member_selected, portfolio_honorsLongTerm⟩

/-! ## Negative controls -/

def ecanAction : TraceLink portfolioTheory
    portfolioStepAuthority.Certificate :=
  ⟨.ecan, ()⟩

/-- A contemporaneous but wrong resident cannot represent the ECAN action. -/
theorem ecan_action_not_pln_resident :
    ¬ actionRepresents ecanAction () .pln := by
  simp [actionRepresents, ecanAction]

def neverSelected (_cycle : Nat) (_occurrence : Occurrence) : Prop := False

/-- Authored generation does not force a hostile selector to schedule work. -/
theorem generation_does_not_imply_selection :
    let routeOccurrence := occurrenceAt portfolioStepAuthority portfolioClaim
      portfolioExecution 0
    let generated := portfolioCodec.realize routeOccurrence
    serviceSpace.Generated heartbeatTrace generated.generatedAt generated /\
      ¬ exists cycle, neverSelected cycle generated := by
  dsimp only
  exact ⟨portfolioCodec.realize_generated _, by simp [neverSelected]⟩

#print axioms portfolio_checker_accepts
#print axioms portfolio_checked_consequences
#print axioms actionRepresents_resident_unique
#print axioms first_cycle_resident_order
#print axioms foreground_occurrences_across_cycles_are_distinct
#print axioms generatedPrefix_member_selected
#print axioms every_role_longTermProtected
#print axioms portfolio_honorsLongTerm
#print axioms recurrent_typed_mindAgent_portfolio
#print axioms ecan_action_not_pln_resident
#print axioms generation_does_not_imply_selection

end
end Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
