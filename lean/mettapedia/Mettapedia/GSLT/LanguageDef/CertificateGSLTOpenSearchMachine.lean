import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.Core.RouteTrace

/-!
# Proof-relevant operational search for open CertificateGSLT derivations

The ordinary proof-search GSLT rewrites only the first outstanding goal.
An unresolved open premise therefore blocks later goals. This machine keeps
pending goals separate from discharged, ordered premise occurrences, so an
open derivation has a finite execution with its actual rule and assumption
steps retained. It is not an executable proof-search decision procedure:
the machine route is constructed from an already given derivation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- An open-search state records both goals still to process and the exact
ordered premise positions already discharged. -/
structure State (context : List Pattern) where
  pending : List Pattern
  discharged : List (Fin context.length)

/-- A rule step retains the rule instance and its application witness; an
assumption step retains the exact occurrence position, even when two
positions carry the same judgment label. -/
inductive Step (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) : State context → State context → Type where
  | rule (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (application : RuleApplication definition ruleInstance premises conclusion)
      (suffix : List Pattern) (discharged : List (Fin context.length)) :
      Step definition context
        ⟨conclusion :: suffix, discharged⟩
        ⟨premises ++ suffix, discharged⟩
  | assumption (index : Fin context.length) (suffix : List Pattern)
      (discharged : List (Fin context.length)) :
      Step definition context
        ⟨context.get index :: suffix, discharged⟩
        ⟨suffix, discharged ++ [index]⟩

/-- A successful semantic event retains the exact rule instance or exact
assumption occurrence. Search-agenda scheduling is outside this machine. -/
inductive Event (context : List Pattern) where
  | rule (ruleInstance : RuleInstance)
  | assumption (index : Fin context.length)

def eventOfStep
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {source target : State context} :
    Step definition context source target → Event context
  | .rule ruleInstance _ _ _ => .rule ruleInstance
  | .assumption index _ _ => .assumption index

private theorem step_identified_by_source_and_event
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {source target otherSource otherTarget : State context}
    (first : Step definition context source target)
    (second : Step definition context otherSource otherTarget)
    (sameSource : source = otherSource)
    (equal : eventOfStep first = eventOfStep second) :
    (⟨source, ⟨target, first⟩⟩ :
        Σ start, Σ finish, Step definition context start finish) =
      ⟨otherSource, ⟨otherTarget, second⟩⟩ := by
  cases first with
  | rule ruleInstance application suffix discharged =>
      cases second with
      | rule otherInstance otherApplication otherSuffix otherDischarged =>
          have sameInstance : ruleInstance = otherInstance := Event.rule.inj equal
          cases sameInstance
          have samePremises := (application.outputs_unique otherApplication).1
          have sameConclusion := (application.outputs_unique otherApplication).2
          cases samePremises
          cases sameConclusion
          have sameSuffix := (List.cons.inj (congrArg State.pending sameSource)).2
          have sameDischarged := congrArg State.discharged sameSource
          cases sameSuffix
          cases sameDischarged
          rfl
      | assumption index otherSuffix otherDischarged => cases equal
  | assumption index suffix discharged =>
      cases second with
      | rule ruleInstance application otherSuffix otherDischarged => cases equal
      | assumption otherIndex otherSuffix otherDischarged =>
          have sameIndex : index = otherIndex := Event.assumption.inj equal
          cases sameIndex
          have sameSuffix := (List.cons.inj (congrArg State.pending sameSource)).2
          have sameDischarged := congrArg State.discharged sameSource
          cases sameSuffix
          cases sameDischarged
          rfl

/-- The current state and event identify the whole successful step. Rule
output uniqueness comes from the existing rule-instantiation authority. -/
theorem eventOfStep_receipt_injective
    (definition : ValidatedCalculusLanguageDef) (context : List Pattern)
    (source : State context) :
    Function.Injective
      (fun receipt : Σ target, Step definition context source target =>
        eventOfStep receipt.2) := by
  rintro ⟨target, first⟩ ⟨otherTarget, second⟩ equal
  exact eq_of_heq (Sigma.mk.inj
    (step_identified_by_source_and_event first second rfl equal)).2

/-- A successful route's event trace retains the complete route, including
its endpoint state, when the initial state is fixed. -/
theorem eventTrace_receipt_injective
    (definition : ValidatedCalculusLanguageDef) (context : List Pattern)
    (source : State context) :
    Function.Injective
      (fun receipt : Σ target, Route (Step definition context) source target =>
        Route.trace eventOfStep receipt.2) :=
  Route.trace_receipt_injective eventOfStep
    (eventOfStep_receipt_injective definition context) source

mutual

/-- Ordered assumption occurrences at the leaves of a proof tree. -/
def holeOccurrences
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} : OpenDerivation definition context goal →
      List (Fin context.length)
  | .assumption index => [index]
  | .byRule _ _ children => holeOccurrencesList children

/-- Concatenate occurrence lists in the order of rule premises. -/
def holeOccurrencesList
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern} :
    OpenDerivationList definition context goals → List (Fin context.length)
  | .nil => []
  | .cons head tail => holeOccurrences head ++ holeOccurrencesList tail

end

mutual

/-- The preorder event record of an authored proof retains every rule and
assumption occurrence, including repeated uses of the same premise. -/
def proofEvents
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} : OpenDerivation definition context goal →
      List (Event context)
  | .assumption index => [.assumption index]
  | .byRule ruleInstance _ children =>
      .rule ruleInstance :: proofEventsList children

def proofEventsList
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern} :
    OpenDerivationList definition context goals → List (Event context)
  | .nil => []
  | .cons head tail => proofEvents head ++ proofEventsList tail

end

theorem proofEventsList_append
    {definition : ValidatedCalculusLanguageDef}
    {context firstGoals secondGoals : List Pattern}
    (first : OpenDerivationList definition context firstGoals)
    (second : OpenDerivationList definition context secondGoals) :
    proofEventsList (first.append second) =
      proofEventsList first ++ proofEventsList second := by
  cases first with
  | nil => rfl
  | cons head tail =>
      simp [OpenDerivationList.append, proofEventsList,
        proofEventsList_append tail second, List.append_assoc]
termination_by sizeOf first

/-- Concatenating proof vectors concatenates their ordered premise uses. -/
theorem holeOccurrencesList_append
    {definition : ValidatedCalculusLanguageDef}
    {context firstGoals secondGoals : List Pattern}
    (left : OpenDerivationList definition context firstGoals)
    (right : OpenDerivationList definition context secondGoals) :
    holeOccurrencesList (left.append right) =
      holeOccurrencesList left ++ holeOccurrencesList right := by
  cases left with
  | nil => rfl
  | cons head tail =>
      simpa [OpenDerivationList.append, holeOccurrencesList,
        List.append_assoc] using
        congrArg (fun occurrences => holeOccurrences head ++ occurrences)
          (holeOccurrencesList_append tail right)
termination_by sizeOf left

/-- An ordered proof vector's premise uses are the concatenation of the
uses in each position, including repeated occurrences of one position. -/
theorem holeOccurrencesList_eq_finRange_flatMap
    {definition : ValidatedCalculusLanguageDef}
    {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals) :
    holeOccurrencesList derivations =
      (List.finRange goals.length).flatMap
        (fun index => holeOccurrences (derivations.get index)) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [holeOccurrencesList, List.length_cons, List.finRange_succ,
        List.flatMap_cons, List.flatMap_map]
      change holeOccurrences head ++ holeOccurrencesList tail =
        holeOccurrences head ++
          (List.finRange _).flatMap
            (fun index => holeOccurrences (tail.get index))
      rw [holeOccurrencesList_eq_finRange_flatMap tail]
termination_by sizeOf derivations

mutual

/-- Substitution of proof terms substitutes each premise-use occurrence by
the ordered uses in that premise's image. This is the noncommutative list
form of resource-accounting composition. -/
theorem holeOccurrences_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition sourceContext goal)
    (environment : OpenDerivationList definition targetContext sourceContext) :
    holeOccurrences (derivation.bind environment) =
      (holeOccurrences derivation).flatMap
        (fun index => holeOccurrences (environment.get index)) := by
  cases derivation with
  | assumption index =>
      simp only [OpenDerivation.assumption_bind, holeOccurrences,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | byRule ruleInstance application children =>
      simpa [OpenDerivation.bind, holeOccurrences] using
        holeOccurrencesList_bind children environment

/-- The same accounting law holds pointwise for an ordered proof vector. -/
theorem holeOccurrencesList_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext goals : List Pattern}
    (derivations : OpenDerivationList definition sourceContext goals)
    (environment : OpenDerivationList definition targetContext sourceContext) :
    holeOccurrencesList (derivations.bind environment) =
      (holeOccurrencesList derivations).flatMap
        (fun index => holeOccurrences (environment.get index)) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.bind, holeOccurrencesList,
        List.flatMap_append]
      rw [holeOccurrences_bind head environment,
        holeOccurrencesList_bind tail environment]

end

mutual

/-- Run one open derivation while preserving an arbitrary trailing goal
suffix and previously discharged premise occurrences. -/
def run
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} (derivation : OpenDerivation definition context goal)
    (suffix : List Pattern) (discharged : List (Fin context.length)) :
    Route (Step definition context)
      ⟨goal :: suffix, discharged⟩
      ⟨suffix, discharged ++ holeOccurrences derivation⟩ :=
  match derivation with
  | .assumption index =>
      .cons (.assumption index suffix discharged) (.refl _)
  | .byRule ruleInstance application children =>
      .cons (.rule ruleInstance application suffix discharged)
        (runList children suffix discharged)

/-- Run an ordered vector of open derivations left to right. Discharged
occurrences no longer block processing the remaining pending goals. -/
def runList
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals)
    (suffix : List Pattern) (discharged : List (Fin context.length)) :
    Route (Step definition context)
      ⟨goals ++ suffix, discharged⟩
      ⟨suffix, discharged ++ holeOccurrencesList derivations⟩ :=
  match derivations with
  | .nil => by
      simpa [holeOccurrencesList] using
        (Route.refl (⟨suffix, discharged⟩ : State context))
  | .cons (premise := premise) (premises := premises) head tail => by
      have front := run head (premises ++ suffix) discharged
      have back := runList tail suffix (discharged ++ holeOccurrences head)
      simpa [holeOccurrencesList, List.append_assoc] using
        front.append back

end

/-- The cons case of the runner is the literal route concatenation up to
the necessary reassociation of its final discharge ledger. -/
theorem runList_cons_heq
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern} {goals : List Pattern}
    (head : OpenDerivation definition context goal)
    (tail : OpenDerivationList definition context goals)
    (suffix : List Pattern) (discharged : List (Fin context.length)) :
    HEq (runList (.cons head tail) suffix discharged)
      ((run head (goals ++ suffix) discharged).append
        (runList tail suffix (discharged ++ holeOccurrences head))) := by
  simp [runList, holeOccurrencesList, cast_heq]

mutual

/-- Executing a proof emits exactly its authored preorder events. -/
theorem trace_run
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} (derivation : OpenDerivation definition context goal)
    (suffix : List Pattern) (discharged : List (Fin context.length)) :
    Route.trace eventOfStep (run derivation suffix discharged) =
      proofEvents derivation := by
  cases derivation with
  | assumption index => rfl
  | byRule ruleInstance application children =>
      exact congrArg (List.cons (.rule ruleInstance))
        (trace_runList children suffix discharged)

/-- Executing a proof vector emits its concatenated preorder events. -/
theorem trace_runList
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals)
    (suffix : List Pattern) (discharged : List (Fin context.length)) :
    Route.trace eventOfStep (runList derivations suffix discharged) =
      proofEventsList derivations := by
  cases derivations with
  | nil =>
      have routeHeq : HEq (runList (.nil :
          OpenDerivationList definition context []) suffix discharged)
          (Route.refl (⟨suffix, discharged⟩ : State context) :
            Route (Step definition context) _ _) := by
        simp [runList, cast_heq]
      exact Route.trace_heq eventOfStep rfl
        (by simp [holeOccurrencesList]) routeHeq
  | cons head tail =>
      have routeHeq := runList_cons_heq head tail suffix discharged
      have traceEq := Route.trace_heq eventOfStep rfl
        (by simp [holeOccurrencesList, List.append_assoc]) routeHeq
      rw [traceEq, Route.trace_append, trace_run head,
        trace_runList tail]
      rfl

end

/-- A complete run discharges exactly the premise occurrences of the given
proof tree and has no goals left to process. -/
def runToCompletion {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], holeOccurrences derivation⟩ := by
  simpa using run derivation [] []

/-- Completion retains exactly the proof's rule and assumption events. -/
theorem trace_runToCompletion
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    Route.trace eventOfStep (runToCompletion derivation) =
      proofEvents derivation := by
  simpa [runToCompletion] using trace_run derivation [] []

/-- A singleton pending goal cannot complete without taking an actual step. -/
theorem completeRoute_length_ne_zero
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    route.length ≠ 0 := by
  cases route with
  | cons step rest => simp [Route.length]

/-- Reconstruct the previous proof vector from one retained machine step.
The rule case splits the ordered premise and suffix derivations at the
actual rule-premise boundary; the assumption case restores its exact hole. -/
def reverseStep {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before after : State context}
    (step : Step definition context before after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    OpenDerivationList definition context before.pending :=
  match step with
  | .rule ruleInstance (premises := premises) application suffix _ =>
      .cons
        (.byRule ruleInstance application
          (OpenDerivationList.takeLeft premises suffix afterProofs))
        (OpenDerivationList.takeRight premises suffix afterProofs)
  | .assumption index _ _ =>
      .cons (.assumption index) afterProofs

/-- Reconstructing one retained step preserves the ordered ledger of
discharged assumption positions. -/
theorem reverseStep_holes
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before after : State context}
    (step : Step definition context before after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    before.discharged ++ holeOccurrencesList (reverseStep step afterProofs) =
      after.discharged ++ holeOccurrencesList afterProofs := by
  cases step with
  | assumption index suffix discharged =>
      simp [reverseStep, holeOccurrencesList, holeOccurrences,
        List.append_assoc]
  | rule ruleInstance application suffix discharged =>
      simp only [reverseStep, holeOccurrencesList, holeOccurrences]
      rw [← holeOccurrencesList_append]
      rw [OpenDerivationList.append_take]

/-- Reconstructing a step prepends its actual event to the remaining proof
events. Rule instances and assumption positions are both retained. -/
theorem reverseStep_events
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before after : State context}
    (step : Step definition context before after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    proofEventsList (reverseStep step afterProofs) =
      eventOfStep step :: proofEventsList afterProofs := by
  cases step with
  | assumption index suffix discharged => rfl
  | rule ruleInstance application suffix discharged =>
      simp only [reverseStep, proofEventsList, proofEvents, eventOfStep,
        List.cons_append]
      rw [← proofEventsList_append, OpenDerivationList.append_take]

/-- Read a finite, proof-relevant machine route backwards into derivations
of its initial pending goals, relative to derivations of its final goals. -/
def reconstruct {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before after : State context}
    (route : Route (Step definition context) before after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    OpenDerivationList definition context before.pending :=
  match route with
  | .refl _ => afterProofs
  | .cons step rest => reverseStep step (reconstruct rest afterProofs)

/-- Reading a route backwards retains its full event trace, ahead of the
events of the supplied continuation proofs. -/
theorem reconstruct_events
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before after : State context}
    (route : Route (Step definition context) before after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    proofEventsList (reconstruct route afterProofs) =
      Route.trace eventOfStep route ++ proofEventsList afterProofs := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp only [reconstruct, reverseStep_events, inductionHypothesis,
        Route.trace, List.cons_append]

/-- Reading a concatenated route backwards is continuation composition;
neither part of the operational history is discarded. -/
theorem reconstruct_append
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before middle after : State context}
    (first : Route (Step definition context) before middle)
    (second : Route (Step definition context) middle after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    reconstruct (first.append second) afterProofs =
      reconstruct first (reconstruct second afterProofs) := by
  induction first with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simpa [Route.append, reconstruct] using
        congrArg (reverseStep step) (inductionHypothesis second)

/-- Reassociation of the final discharge ledger does not change the
reconstructed derivation. The route itself is related by heterogeneous
equality, so no operational step is quotiented. -/
theorem reconstruct_heq_of_ledgers
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern}
    {before : State context} {suffix : List Pattern}
    {firstLedger secondLedger : List (Fin context.length)}
    {first : Route (Step definition context) before
      ⟨suffix, firstLedger⟩}
    {second : Route (Step definition context) before
      ⟨suffix, secondLedger⟩}
    (sameLedger : firstLedger = secondLedger)
    (sameRoute : HEq first second)
    (afterProofs : OpenDerivationList definition context suffix) :
    reconstruct first afterProofs = reconstruct second afterProofs := by
  cases sameLedger
  have equalRoute : first = second := eq_of_heq sameRoute
  cases equalRoute
  rfl

mutual

/-- Reconstructing the route generated by a proof recovers that exact proof
tree, even in the presence of a continuation of trailing goals. -/
theorem reconstruct_run
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal)
    (suffix : List Pattern) (discharged : List (Fin context.length))
    (afterProofs : OpenDerivationList definition context suffix) :
    reconstruct (run derivation suffix discharged) afterProofs =
      .cons derivation afterProofs := by
  cases derivation with
  | assumption index => rfl
  | byRule ruleInstance application children =>
      have childEq := reconstruct_runList children suffix discharged afterProofs
      have leftLaw : OpenDerivationList.takeLeft _ suffix
          (reconstruct (runList children suffix discharged) afterProofs) =
            children := by
        rw [childEq]
        exact OpenDerivationList.takeLeft_append children afterProofs
      have rightLaw : OpenDerivationList.takeRight _ suffix
          (reconstruct (runList children suffix discharged) afterProofs) =
            afterProofs := by
        rw [childEq]
        exact OpenDerivationList.takeRight_append children afterProofs
      have recovered := congrArg₂
        (fun (inner : OpenDerivationList definition context _)
          (continuation : OpenDerivationList definition context suffix) =>
          OpenDerivationList.cons
            (OpenDerivation.byRule ruleInstance application inner)
            continuation)
        leftLaw rightLaw
      change OpenDerivationList.cons
          (OpenDerivation.byRule ruleInstance application
            (OpenDerivationList.takeLeft _ suffix
              (reconstruct (runList children suffix discharged) afterProofs)))
          (OpenDerivationList.takeRight _ suffix
            (reconstruct (runList children suffix discharged) afterProofs)) =
        .cons (.byRule ruleInstance application children) afterProofs
      exact recovered

/-- The same exact round trip holds for an ordered vector of proofs, with
its continuation appended after the recovered vector. -/
theorem reconstruct_runList
    {definition : ValidatedCalculusLanguageDef}
    {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals)
    (suffix : List Pattern) (discharged : List (Fin context.length))
    (afterProofs : OpenDerivationList definition context suffix) :
    reconstruct (runList derivations suffix discharged) afterProofs =
      derivations.append afterProofs := by
  cases derivations with
  | nil =>
      have routeHeq : HEq (runList (.nil :
          OpenDerivationList definition context []) suffix discharged)
          (Route.refl (⟨suffix, discharged⟩ : State context) :
            Route (Step definition context) _ _) := by
        simp [runList, cast_heq]
      have recovered := reconstruct_heq_of_ledgers
        (List.append_nil discharged) routeHeq afterProofs
      change reconstruct (runList (.nil :
          OpenDerivationList definition context []) suffix discharged)
          afterProofs = afterProofs
      exact recovered
  | cons head tail =>
      have routeHeq := runList_cons_heq head tail suffix discharged
      have ledgerEq :
          discharged ++ holeOccurrencesList (.cons head tail) =
            (discharged ++ holeOccurrences head) ++
              holeOccurrencesList tail := by
        simp [holeOccurrencesList, List.append_assoc]
      have recovered := reconstruct_heq_of_ledgers
        ledgerEq routeHeq afterProofs
      rw [recovered, reconstruct_append]
      rw [reconstruct_runList tail suffix
        (discharged ++ holeOccurrences head) afterProofs]
      rw [reconstruct_run head]
      rfl

end

/-- Reconstruction accounts for exactly the discharged premise positions:
old discharges followed by the reconstructed proof's leaves equal the final
ledger followed by the leaves of any still-pending final goals. -/
theorem reconstruct_holes
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {before after : State context}
    (route : Route (Step definition context) before after)
    (afterProofs : OpenDerivationList definition context after.pending) :
    before.discharged ++ holeOccurrencesList (reconstruct route afterProofs) =
      after.discharged ++ holeOccurrencesList afterProofs := by
  cases route with
  | refl _ => rfl
  | cons step rest =>
      exact (reverseStep_holes step (reconstruct rest afterProofs)).trans
        (reconstruct_holes rest afterProofs)
termination_by sizeOf route

/-- A complete machine route yields an actual open proof term, not just a
proposition that the initial goal is derivable. -/
def derivationOfCompleteRoute
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    OpenDerivation definition context goal :=
  match reconstruct route .nil with
  | .cons head .nil => head

/-- The final machine ledger is exactly the ordered list of premise
occurrences in the reconstructed proof. No discharge is invented or lost. -/
theorem derivationOfCompleteRoute_holes
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    holeOccurrences (derivationOfCompleteRoute route) = discharged := by
  have ledger := reconstruct_holes route
    (.nil : OpenDerivationList definition context [])
  cases reconstructed : reconstruct route .nil with
  | cons head tail =>
      cases tail with
      | nil =>
          simpa [derivationOfCompleteRoute, reconstructed,
            holeOccurrencesList] using ledger

/-- A reconstructed complete proof retains the entire operational event
trace, not just its result and discharged assumptions. -/
theorem derivationOfCompleteRoute_events
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    proofEvents (derivationOfCompleteRoute route) =
      Route.trace eventOfStep route := by
  have events := reconstruct_events route
    (.nil : OpenDerivationList definition context [])
  cases reconstructed : reconstruct route .nil with
  | cons head tail =>
      cases tail with
      | nil =>
          simpa [derivationOfCompleteRoute, reconstructed,
            proofEventsList] using events

/-- The generated complete route reconstructs to the original authored
proof, not just to another proof with the same conclusion and ledger. -/
theorem derivationOfCompleteRoute_runToCompletion
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    derivationOfCompleteRoute (runToCompletion derivation) = derivation := by
  have recovered := reconstruct_run derivation [] []
    (OpenDerivationList.nil : OpenDerivationList definition context [])
  have headEq := congrArg
    (fun proofs : OpenDerivationList definition context [goal] =>
      proofs.get (0 : Fin 1)) recovered
  cases proofVector : reconstruct (run derivation [] [])
      (OpenDerivationList.nil : OpenDerivationList definition context []) with
  | cons head tail =>
      cases tail with
      | nil =>
          have headIsOriginal : head = derivation := by
            simpa [proofVector, OpenDerivationList.get] using headEq
          simpa [derivationOfCompleteRoute, runToCompletion, proofVector]
            using headIsOriginal

/-- The dependent route receipt records its exact final ledger together with
the route that produced it. -/
def completeRouteReceipt
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    Σ ledger : List (Fin context.length),
      Route (Step definition context)
        ⟨[goal], []⟩ ⟨[], ledger⟩ :=
  ⟨holeOccurrences derivation, runToCompletion derivation⟩

/-- Distinct authored proof trees yield distinct operational receipts with
their final ledgers; this is a left-inverse consequence, not an assumption
that arbitrary completed routes are canonical. -/
theorem completeRouteReceipt_injective
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern} :
    Function.Injective (completeRouteReceipt
      (definition := definition) (context := context) (goal := goal)) := by
  intro left right sameReceipt
  have sameProof := congrArg
    (fun receipt : Σ ledger : List (Fin context.length),
      Route (Step definition context) ⟨[goal], []⟩ ⟨[], ledger⟩ =>
      derivationOfCompleteRoute receipt.2) sameReceipt
  simpa [completeRouteReceipt,
    derivationOfCompleteRoute_runToCompletion] using sameProof

/-- Regenerate a completed route from its reconstructed proof, transporting
the endpoint along the exact ledger law. `canonicalCompleteRoute_eq` proves
that this operation changes no route of the pending-first machine. -/
def canonicalCompleteRoute
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩ :=
  (derivationOfCompleteRoute_holes route) ▸
    runToCompletion (derivationOfCompleteRoute route)

private theorem derivationOfCompleteRoute_transport
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {first second : List (Fin context.length)}
    (same : first = second)
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], first⟩) :
    derivationOfCompleteRoute (same ▸ route) =
      derivationOfCompleteRoute route := by
  cases same
  rfl

/-- Canonicalization preserves the full reconstructed proof tree, not only
its conclusion or leaf ledger. -/
theorem derivationOfCompleteRoute_canonicalCompleteRoute
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    derivationOfCompleteRoute (canonicalCompleteRoute route) =
      derivationOfCompleteRoute route := by
  unfold canonicalCompleteRoute
  rw [derivationOfCompleteRoute_transport]
  exact derivationOfCompleteRoute_runToCompletion _

/-- Every complete route of this pending-first machine is the exact run of
its reconstructed proof. The initial state and retained events determine
each dependent step, so neither scheduling nor rule witnesses are silently
quotiented by this equality. -/
theorem canonicalCompleteRoute_eq
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    canonicalCompleteRoute route = route := by
  have sameTrace : Route.trace eventOfStep (canonicalCompleteRoute route) =
      Route.trace eventOfStep route := by
    rw [← derivationOfCompleteRoute_events,
      derivationOfCompleteRoute_canonicalCompleteRoute,
      derivationOfCompleteRoute_events]
  have sameReceipt := eventTrace_receipt_injective definition context
    (⟨[goal], []⟩ : State context)
    (a₁ := ⟨⟨[], discharged⟩, canonicalCompleteRoute route⟩)
    (a₂ := ⟨⟨[], discharged⟩, route⟩) sameTrace
  exact eq_of_heq (Sigma.mk.inj sameReceipt).2

private theorem cast_runToCompletion_congr
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {discharged : List (Fin context.length)}
    {first second : OpenDerivation definition context goal}
    (same : first = second)
    (firstLedger : holeOccurrences first = discharged)
    (secondLedger : holeOccurrences second = discharged) :
    (firstLedger ▸ runToCompletion first) =
      (secondLedger ▸ runToCompletion second) := by
  cases same
  have sameProof : firstLedger = secondLedger := Subsingleton.elim _ _
  cases sameProof
  rfl

/-- Proof-generated routes are fixed points of route canonicalization. -/
theorem canonicalCompleteRoute_runToCompletion
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    canonicalCompleteRoute (runToCompletion derivation) =
      runToCompletion derivation := by
  exact cast_runToCompletion_congr
    (derivationOfCompleteRoute_runToCompletion derivation)
    (derivationOfCompleteRoute_holes (runToCompletion derivation))
    rfl

/-- Once the operational route is regenerated from its own reconstructed
proof, another regeneration changes nothing. -/
theorem canonicalCompleteRoute_idempotent
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    {discharged : List (Fin context.length)}
    (route : Route (Step definition context)
      ⟨[goal], []⟩ ⟨[], discharged⟩) :
    canonicalCompleteRoute (canonicalCompleteRoute route) =
      canonicalCompleteRoute route := by
  exact cast_runToCompletion_congr
    (derivationOfCompleteRoute_canonicalCompleteRoute route)
    (derivationOfCompleteRoute_holes (canonicalCompleteRoute route))
    (derivationOfCompleteRoute_holes route)

/-- A route receipt fixed by canonicalization is exactly the receipt of its
own reconstructed authored proof. This keeps the fixed-point criterion
independent of an existential choice of proof. -/
theorem completeRouteReceipt_reconstruct_of_fixed
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (receipt : Σ ledger : List (Fin context.length),
      Route (Step definition context)
        ⟨[goal], []⟩ ⟨[], ledger⟩)
    (fixed : canonicalCompleteRoute receipt.2 = receipt.2) :
    completeRouteReceipt (derivationOfCompleteRoute receipt.2) = receipt := by
  cases receipt with
  | mk ledger route =>
      apply Sigma.ext (derivationOfCompleteRoute_holes route)
      exact eqRec_heq_iff.mp (heq_of_eq fixed)

/-- Reconstruction followed by execution recovers every completed route
receipt, including its exact ledger and every retained operational step. -/
theorem completeRouteReceipt_reconstruct
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (receipt : Σ ledger : List (Fin context.length),
      Route (Step definition context)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    completeRouteReceipt (derivationOfCompleteRoute receipt.2) = receipt :=
  completeRouteReceipt_reconstruct_of_fixed receipt
    (canonicalCompleteRoute_eq receipt.2)

/-- Authored open proofs are equivalent to all finite completed receipts of
the pending-first search machine, without an additional canonicality gate. -/
def completeRouteProofEquiv
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) :
    (Σ ledger : List (Fin context.length),
      Route (Step definition context)
        ⟨[goal], []⟩ ⟨[], ledger⟩) ≃
      OpenDerivation definition context goal where
  toFun receipt := derivationOfCompleteRoute receipt.2
  invFun := completeRouteReceipt
  left_inv := completeRouteReceipt_reconstruct
  right_inv := derivationOfCompleteRoute_runToCompletion

/-- Exact reconstructed proof equality identifies the whole completed route
receipt in this machine, not merely its final answer. -/
theorem derivationOfCompleteRoute_receipt_injective
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) :
    Function.Injective
      (fun receipt : Σ ledger : List (Fin context.length),
        Route (Step definition context)
          ⟨[goal], []⟩ ⟨[], ledger⟩ =>
        derivationOfCompleteRoute receipt.2) :=
  (completeRouteProofEquiv definition context goal).injective

/-- Contextual proof substitution acts on a completed operational receipt by
reconstructing its retained proof and running the substituted proof. It does
not claim to transport an arbitrary raw route event-by-event. -/
def mapCompleteRouteReceipt
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (environment : OpenDerivationList definition targetContext sourceContext)
    (receipt : Σ ledger : List (Fin sourceContext.length),
      Route (Step definition sourceContext)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    Σ ledger : List (Fin targetContext.length),
      Route (Step definition targetContext)
        ⟨[goal], []⟩ ⟨[], ledger⟩ :=
  completeRouteReceipt ((derivationOfCompleteRoute receipt.2).bind environment)

/-- Substitution preserves the canonicality satisfied by every completed
route of the pending-first machine. -/
theorem mapCompleteRouteReceipt_fixed
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (environment : OpenDerivationList definition targetContext sourceContext)
    (receipt : Σ ledger : List (Fin sourceContext.length),
      Route (Step definition sourceContext)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    canonicalCompleteRoute (mapCompleteRouteReceipt environment receipt).2 =
      (mapCompleteRouteReceipt environment receipt).2 :=
  canonicalCompleteRoute_runToCompletion _

/-- The substituted route computes the exact noncommutative flat-map of
premise occurrences, rather than merely a final-state reachability fact. -/
theorem mapCompleteRouteReceipt_ledger
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (environment : OpenDerivationList definition targetContext sourceContext)
    (receipt : Σ ledger : List (Fin sourceContext.length),
      Route (Step definition sourceContext)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    (mapCompleteRouteReceipt environment receipt).1 =
      receipt.1.flatMap
        (fun index => holeOccurrences (environment.get index)) := by
  change holeOccurrences
      ((derivationOfCompleteRoute receipt.2).bind environment) = _
  rw [holeOccurrences_bind, derivationOfCompleteRoute_holes]

/-- Reconstructing the substituted operational receipt is exactly proof
substitution on the original reconstructed proof. -/
theorem mapCompleteRouteReceipt_reconstruct
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (environment : OpenDerivationList definition targetContext sourceContext)
    (receipt : Σ ledger : List (Fin sourceContext.length),
      Route (Step definition sourceContext)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    derivationOfCompleteRoute (mapCompleteRouteReceipt environment receipt).2 =
      (derivationOfCompleteRoute receipt.2).bind environment :=
  derivationOfCompleteRoute_runToCompletion _

/-- On proof-generated routes, operational substitution commutes with the
intensional proof substitution exactly. -/
theorem mapCompleteRouteReceipt_generated
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (environment : OpenDerivationList definition targetContext sourceContext)
    (derivation : OpenDerivation definition sourceContext goal) :
    mapCompleteRouteReceipt environment (completeRouteReceipt derivation) =
      completeRouteReceipt (derivation.bind environment) := by
  change completeRouteReceipt
      ((derivationOfCompleteRoute (runToCompletion derivation)).bind
        environment) = completeRouteReceipt (derivation.bind environment)
  rw [derivationOfCompleteRoute_runToCompletion]

/-- Identity substitution preserves every completed operational receipt. -/
theorem mapCompleteRouteReceipt_id
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (receipt : Σ ledger : List (Fin context.length),
      Route (Step definition context)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    mapCompleteRouteReceipt (assumptionEnvironment definition context) receipt =
      receipt := by
  simp only [mapCompleteRouteReceipt,
    OpenDerivation.bind_assumptionEnvironment]
  exact completeRouteReceipt_reconstruct receipt

/-- Substitution composes on all completed route receipts by associativity
of authored proof substitution and exact reconstruction. -/
theorem mapCompleteRouteReceipt_comp
    {definition : ValidatedCalculusLanguageDef}
    {firstContext middleContext lastContext : List Pattern} {goal : Pattern}
    (first : OpenDerivationList definition middleContext firstContext)
    (second : OpenDerivationList definition lastContext middleContext)
    (receipt : Σ ledger : List (Fin firstContext.length),
      Route (Step definition firstContext)
        ⟨[goal], []⟩ ⟨[], ledger⟩) :
    mapCompleteRouteReceipt second
        (mapCompleteRouteReceipt first receipt) =
      mapCompleteRouteReceipt (first.bind second) receipt := by
  change completeRouteReceipt
      ((derivationOfCompleteRoute (runToCompletion
          ((derivationOfCompleteRoute receipt.2).bind first))).bind
        second) =
      completeRouteReceipt
        ((derivationOfCompleteRoute receipt.2).bind (first.bind second))
  rw [derivationOfCompleteRoute_runToCompletion,
    OpenDerivation.bind_assoc]

/-- Inhabitation of open derivations is equivalent to a completed,
proof-relevant operational route. The endpoint retains the ordered discharged
positions. This is not an isomorphism of individual proofs and routes. -/
theorem derivation_nonempty_iff_completeRoute
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern) :
    Nonempty (OpenDerivation definition context goal) ↔
      ∃ discharged : List (Fin context.length),
        Nonempty (Route (Step definition context)
          ⟨[goal], []⟩ ⟨[], discharged⟩) := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨holeOccurrences derivation, ⟨runToCompletion derivation⟩⟩
  · rintro ⟨discharged, ⟨route⟩⟩
    exact ⟨derivationOfCompleteRoute route⟩

/-- Exact ordered-discharge adequacy at a fixed ledger: completed routes
exist precisely for open proofs whose leaf occurrences are that ledger.
Both directions construct actual Type-valued evidence before `Nonempty`
forgets the choice of route or proof. -/
theorem exactDischargeAdequacy
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern)
    (discharged : List (Fin context.length)) :
    Nonempty { derivation : OpenDerivation definition context goal //
      holeOccurrences derivation = discharged } ↔
      Nonempty (Route (Step definition context)
        ⟨[goal], []⟩ ⟨[], discharged⟩) := by
  constructor
  · rintro ⟨⟨derivation, ledger⟩⟩
    subst discharged
    exact ⟨runToCompletion derivation⟩
  · rintro ⟨route⟩
    exact ⟨⟨derivationOfCompleteRoute route,
      derivationOfCompleteRoute_holes route⟩⟩

/-- Two equal judgment labels at different premise positions produce
different discharged-occurrence lists. The operational machine never
identifies them merely because their goals print alike. -/
theorem duplicateAssumptions_dischargeDistinct
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    holeOccurrences
        (OpenDerivation.assumption (definition := definition)
          (context := [goal, goal]) (0 : Fin 2)) ≠
      holeOccurrences
        (OpenDerivation.assumption (definition := definition)
          (context := [goal, goal]) (1 : Fin 2)) := by
  simp [holeOccurrences]

#print axioms holeOccurrences
#print axioms eventOfStep_receipt_injective
#print axioms eventTrace_receipt_injective
#print axioms trace_runToCompletion
#print axioms derivationOfCompleteRoute_events
#print axioms canonicalCompleteRoute_eq
#print axioms completeRouteReceipt_reconstruct
#print axioms completeRouteProofEquiv
#print axioms derivationOfCompleteRoute_receipt_injective
#print axioms holeOccurrences_bind
#print axioms holeOccurrencesList_bind
#print axioms run
#print axioms runList
#print axioms runToCompletion
#print axioms reconstruct
#print axioms reconstruct_append
#print axioms reconstruct_run
#print axioms reconstruct_runList
#print axioms derivationOfCompleteRoute
#print axioms derivationOfCompleteRoute_runToCompletion
#print axioms completeRouteReceipt_injective
#print axioms derivationOfCompleteRoute_canonicalCompleteRoute
#print axioms canonicalCompleteRoute_runToCompletion
#print axioms canonicalCompleteRoute_idempotent
#print axioms completeRouteReceipt_reconstruct_of_fixed
#print axioms mapCompleteRouteReceipt_ledger
#print axioms mapCompleteRouteReceipt_fixed
#print axioms mapCompleteRouteReceipt_reconstruct
#print axioms mapCompleteRouteReceipt_generated
#print axioms mapCompleteRouteReceipt_id
#print axioms mapCompleteRouteReceipt_comp
#print axioms derivation_nonempty_iff_completeRoute
#print axioms derivationOfCompleteRoute_holes
#print axioms exactDischargeAdequacy
#print axioms duplicateAssumptions_dischargeDistinct

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine
