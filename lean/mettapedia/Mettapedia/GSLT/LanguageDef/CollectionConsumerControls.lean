import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrencePublication
import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
import Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
import Mettapedia.OSLF.MeTTaIL.CollectionRootCoverage
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearchStable
import Mettapedia.OSLF.MeTTaIL.Complete.Explore

/-! End-to-end source controls for the two authored collection consumers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
open Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
open CollectionConsumers

def completed? (request : Option Request) : Option (List Receipt) :=
  request.map fun query => publication (resume query 30 (start query))

def targets? (request : Option Request) : Option (List Pattern) := do
  let query ← request
  let receipts := publication (resume query 30 (start query))
  receipts.mapM fun receipt =>
    canon <$> reduct? query.rule query.spec query.ambient receipt.matching.assignment

def petriAB := petriRequest? 0 [token "A", token "B"]
def petriAAB := petriRequest? 0 [token "A", token "A", token "B"]
def petriMissing := petriRequest? 0 [token "A"]
def graphChain := reachabilityRequest? 0 [edge "A" "B", edge "B" "C"]
def graphLoop := reachabilityRequest? 0 [edge "A" "A"]
def graphMissing := reachabilityRequest? 0 [edge "A" "B", edge "A" "C"]

#guard (completed? petriAB).map List.length == some 1
#guard (completed? petriAAB).map List.length == some 2
#guard (completed? petriMissing).map List.length == some 0

#guard targets? petriAB == some [canon (.collection .hashBag [token "C", token "D"] none)]
#guard targets? petriAAB == some (List.replicate 2
  (canon (.collection .hashBag [token "C", token "D", token "A"] none)))

-- Four retention histories denote one set result; the histories remain
-- distinct receipts even though canonical targets coincide.
#guard (completed? graphChain).map List.length == some 4
#guard targets? graphChain == some (List.replicate 4
  (canon (.collection .hashSet [edge "A" "B", edge "B" "C", edge "A" "C"] none)))

-- Repeated selection is essential: one self-loop satisfies both premises.
#guard (completed? graphLoop).map List.length == some 2
#guard targets? graphLoop == some (List.replicate 2
  (canon (.collection .hashSet [edge "A" "A"] none)))

#guard (completed? graphMissing).map List.length == some 0

def petriSource : Pattern := .collection .hashBag [token "A", token "B"] none
def graphSource : Pattern := .collection .hashSet [edge "A" "B", edge "B" "C"] none

#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate petriSource).map Prod.fst == [0, 1]
#guard (CollectionExecutionAdmission.requestsForSource
  reachabilityPlan reachabilityCertificate graphSource).map Prod.fst == [0]
#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate (.apply "A" [])).isEmpty
#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate graphSource).isEmpty

def petriRequests := CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate petriSource

def graphRequests := CollectionExecutionAdmission.requestsForSource
  reachabilityPlan reachabilityCertificate graphSource

def completedPlanFirings (requests : List (Nat × Request)) :
    List CollectionPlanMachine.Firing :=
  CollectionPlanMachine.publication
    (CollectionPlanMachine.resume 30 (CollectionPlanMachine.start requests))

#guard (completedPlanFirings petriRequests).all
  (fun firing => !(adaptations firing).isEmpty)
#guard (completedPlanFirings graphRequests).all
  (fun firing => !(adaptations firing).isEmpty)

def duplicateOriginRequests : List (Nat × Request) :=
  match petriRequests.head? with
  | some (_, request) => [(3, request), (7, request)]
  | none => []

#guard (completedPlanFirings duplicateOriginRequests).map (·.ordinal) == [3, 7]

/-! The Petri consumer enters the generic scheduled continuation after
collection matching. This is the semantic join used by the emitted backend;
typing, premises and reduct construction are no longer collection-specific. -/

def petriFirstFiring : CollectionPlanMachine.Firing :=
  (completedPlanFirings petriRequests)[0]'(by cbv)

theorem petriFirstFiring_member :
    petriFirstFiring ∈ completedPlanFirings petriRequests :=
  List.getElem_mem _

theorem petriFirstFiring_ready : RootReady petriFirstFiring.request :=
  (source_publication_authority petriPlan petriCertificate petriSource 30
    (by simpa only [completedPlanFirings, petriRequests] using petriFirstFiring_member)).ready

theorem petriFirstFiring_valid : petriFirstFiring.Valid :=
  CollectionPlanMachine.publication_sound 30 petriRequests petriFirstFiring_member

def petriEnvironment := GeneralPlanEnvironment.environment petriPlan

theorem petriFirstAuthority : HandoffAuthority petriPlan petriCertificate
    petriSource petriFirstFiring := by
  apply source_publication_authority petriPlan petriCertificate petriSource 30
  simpa only [completedPlanFirings, petriRequests] using petriFirstFiring_member

theorem petriFirstFiring_declared :
    petriEnvironment.language.rewrites[petriFirstFiring.ordinal]? =
      some petriFirstFiring.request.rule := petriFirstAuthority.declared

theorem petriFirstFiring_specified :
    GeneralPremise.specification? petriEnvironment petriFirstFiring.ordinal =
      some petriFirstFiring.request.spec := petriFirstAuthority.specified

theorem petriFirstFiring_admitted :
    RuleBinding.admittedFor petriFirstFiring.request.rule
      petriFirstFiring.request.spec = true := petriFirstAuthority.admitted

theorem petriSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      petriEnvironment.language petriEnvironment.free [] (.base "Marking")
      petriSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

theorem petriFirstSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      petriEnvironment.language petriEnvironment.free [] (.base "Marking")
      (CollectionMatcherCompatibility.ordinaryTarget petriFirstFiring.request
        petriFirstFiring.receipt.source) :=
  petriFirstAuthority.source_typed petriSource_typed

def petriHandoffGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget petriFirstFiring.request
      petriFirstFiring.receipt.source) petriFirstFiring.ordinal

def petriHandoff := continueAll petriEnvironment petriHandoffGoal 0 (.base "Marking")
  petriFirstFiring petriFirstFiring_ready petriFirstFiring_declared
  petriFirstFiring_specified petriFirstFiring_admitted petriFirstSource_typed
  (.done petriHandoffGoal) []

#guard !petriHandoff.tasks.isEmpty
#guard petriHandoff.answers.isEmpty
#guard petriHandoff.unresolved.isEmpty

def petriScheduled := startPublished petriPlan petriCertificate petriSource 30 0
  (.base "Marking") petriFirstFiring
  (by simpa only [completedPlanFirings, petriRequests] using petriFirstFiring_member)
  petriFirstSource_typed

#guard !petriScheduled.agenda.isEmpty
#guard petriScheduled.answers.isEmpty
#guard petriScheduled.unresolved.isEmpty

def petriScheduledRun := StructuralDescent.Scheduled.run petriEnvironment
  petriHandoffGoal 20 petriScheduled

#guard petriScheduledRun.agenda.isEmpty
#guard petriScheduledRun.answers.length = 1
#guard petriScheduledRun.unresolved.isEmpty

/-! Graph closure exercises the idempotent set branch through the same generic
continuation. Its four physical retention histories remain separate tasks. -/

def graphFirstFiring : CollectionPlanMachine.Firing :=
  (completedPlanFirings graphRequests)[0]'(by cbv)

theorem graphFirstFiring_member :
    graphFirstFiring ∈ completedPlanFirings graphRequests :=
  List.getElem_mem _

theorem graphFirstFiring_ready : RootReady graphFirstFiring.request :=
  (source_publication_authority reachabilityPlan reachabilityCertificate graphSource 30
    (by simpa only [completedPlanFirings, graphRequests] using graphFirstFiring_member)).ready

theorem graphFirstFiring_valid : graphFirstFiring.Valid :=
  CollectionPlanMachine.publication_sound 30 graphRequests graphFirstFiring_member

def graphEnvironment := GeneralPlanEnvironment.environment reachabilityPlan

theorem graphFirstAuthority : HandoffAuthority reachabilityPlan reachabilityCertificate
    graphSource graphFirstFiring := by
  apply source_publication_authority reachabilityPlan reachabilityCertificate graphSource 30
  simpa only [completedPlanFirings, graphRequests] using graphFirstFiring_member

theorem graphFirstFiring_declared :
    graphEnvironment.language.rewrites[graphFirstFiring.ordinal]? =
      some graphFirstFiring.request.rule := graphFirstAuthority.declared

theorem graphFirstFiring_specified :
    GeneralPremise.specification? graphEnvironment graphFirstFiring.ordinal =
      some graphFirstFiring.request.spec := graphFirstAuthority.specified

theorem graphFirstFiring_admitted :
    RuleBinding.admittedFor graphFirstFiring.request.rule
      graphFirstFiring.request.spec = true := graphFirstAuthority.admitted

theorem graphSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      graphEnvironment.language graphEnvironment.free [] (.base "Graph")
      graphSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

theorem graphFirstSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      graphEnvironment.language graphEnvironment.free [] (.base "Graph")
      (CollectionMatcherCompatibility.ordinaryTarget graphFirstFiring.request
        graphFirstFiring.receipt.source) :=
  graphFirstAuthority.source_typed graphSource_typed

def graphHandoffGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Graph")
    (CollectionMatcherCompatibility.ordinaryTarget graphFirstFiring.request
      graphFirstFiring.receipt.source) graphFirstFiring.ordinal

def graphHandoff := continueAll graphEnvironment graphHandoffGoal 0 (.base "Graph")
  graphFirstFiring graphFirstFiring_ready graphFirstFiring_declared
  graphFirstFiring_specified graphFirstFiring_admitted graphFirstSource_typed
  (.done graphHandoffGoal) []

#guard !graphHandoff.tasks.isEmpty
#guard graphHandoff.tasks.length = 1
#guard graphHandoff.answers.isEmpty
#guard graphHandoff.unresolved.isEmpty

def graphScheduled := startPublished reachabilityPlan reachabilityCertificate graphSource 30 0
  (.base "Graph") graphFirstFiring
  (by simpa only [completedPlanFirings, graphRequests] using graphFirstFiring_member)
  graphFirstSource_typed

#guard !graphScheduled.agenda.isEmpty
#guard graphScheduled.answers.isEmpty
#guard graphScheduled.unresolved.isEmpty

def graphScheduledRun := StructuralDescent.Scheduled.run graphEnvironment
  graphHandoffGoal 20 graphScheduled

#guard graphScheduledRun.agenda.isEmpty
#guard graphScheduledRun.answers.length = 1
#guard graphScheduledRun.unresolved.isEmpty

/-! Both authored consumers now use the existing generic fair explorer through
the lawful append-only collection search. -/

def petriLoggedExplorer := Complete.Explore.explore
  (CollectionLoggedSearch.search petriPlan petriCertificate) petriSource 20

def graphLoggedExplorer := Complete.Explore.explore
  (CollectionLoggedSearch.search reachabilityPlan reachabilityCertificate) graphSource 20

#guard CanonicalBags.canon (.collection .hashBag [token "C", token "D"] none) ∈
  petriLoggedExplorer.nodes.map (·.state)
#guard CanonicalBags.canon (.collection .hashSet
    [edge "A" "B", edge "B" "C", edge "A" "C"] none) ∈
  graphLoggedExplorer.nodes.map (·.state)

/-! Chronological publication enters the existing shared continuation with
source typing transported once, independently of allocation history. -/

def petriLoggedRun := CollectionLoggedSearch.run petriPlan petriCertificate petriSource 30

def petriLoggedFirstFiring : CollectionPlanMachine.Firing :=
  (petriLoggedRun.state.log)[0]'(by cbv)

theorem petriLoggedFirst_member :
    petriLoggedFirstFiring ∈ petriLoggedRun.state.log := List.getElem_mem _

def petriLoggedGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget petriLoggedFirstFiring.request
      petriLoggedFirstFiring.receipt.source) petriLoggedFirstFiring.ordinal

def petriLoggedScheduled := startLoggedPublished petriPlan petriCertificate petriSource 30 0
  (.base "Marking") petriLoggedFirstFiring petriLoggedFirst_member petriSource_typed

def petriLoggedScheduledRun := StructuralDescent.Scheduled.run petriEnvironment
  petriLoggedGoal 20 petriLoggedScheduled

#guard !petriLoggedScheduled.agenda.isEmpty
#guard petriLoggedScheduledRun.agenda.isEmpty
#guard petriLoggedScheduledRun.answers.length = 1
#guard petriLoggedScheduledRun.unresolved.isEmpty

def graphLoggedRun := CollectionLoggedSearch.run reachabilityPlan reachabilityCertificate graphSource 30

def graphLoggedFirstFiring : CollectionPlanMachine.Firing := graphFirstFiring

theorem graphLoggedFirst_member :
    graphLoggedFirstFiring ∈ graphLoggedRun.state.log := by
  have finished : CollectionLoggedSearch.complete
      (CollectionLoggedSearch.resume (29 + 1) (CollectionLoggedSearch.begin graphRequests)) = true := by
    rw [CollectionLoggedSearch.complete_resume_begin_succ]
    cbv
  apply (CollectionLoggedSearch.completed_log_exact graphRequests 30 finished graphLoggedFirstFiring).mpr
  exact ⟨CollectionPlanMachine.publication_origin 30 graphRequests graphFirstFiring_member,
    graphFirstFiring_valid⟩

def graphLoggedGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Graph")
    (CollectionMatcherCompatibility.ordinaryTarget graphLoggedFirstFiring.request
      graphLoggedFirstFiring.receipt.source) graphLoggedFirstFiring.ordinal

def graphLoggedScheduled := startLoggedPublished reachabilityPlan reachabilityCertificate graphSource 30 0
  (.base "Graph") graphLoggedFirstFiring graphLoggedFirst_member graphSource_typed

def graphLoggedScheduledRun := StructuralDescent.Scheduled.run graphEnvironment
  graphLoggedGoal 20 graphLoggedScheduled

#guard !graphLoggedScheduled.agenda.isEmpty
#guard graphLoggedScheduledRun.agenda.isEmpty
#guard graphLoggedScheduledRun.answers.length = 1
#guard graphLoggedScheduledRun.unresolved.isEmpty

/-- A valid collection match cannot authorize an absent authored rule. -/
def wrongLoggedOrdinal : CollectionPlanMachine.Firing :=
  { petriLoggedFirstFiring with ordinal := 42 }

theorem wrongLoggedOrdinal_not_authorized :
    ¬ HandoffAuthority petriPlan petriCertificate petriSource wrongLoggedOrdinal := by
  intro authority
  have declared := authority.declared
  have absent : petriEnvironment.language.rewrites[42]? = none := by cbv
  change petriEnvironment.language.rewrites[42]? = some _ at declared
  rw [absent] at declared
  cases declared

/-! A completed collection match is provisional: a declared premise can still
reject it. Both provider snapshots are complete, including the empty one. -/

def guardedPetriPlan (permitted : Bool) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    { language := { petri with rewrites := petri.rewrites.map fun rule =>
        { rule with premises := [.relationQuery "permit" []] } }
      freeTypes := []
      provider :=
        { signatures := [{ relation := "permit", argumentTypes := [], modes := [] }]
          rows := if permitted then [{ relation := "permit", values := [] }] else [] } }
    permissions

def guardedPetriCertificate (permitted : Bool) :
    CollectionExecutionAdmission.Certificate (guardedPetriPlan permitted) :=
  ⟨by cases permitted <;> cbv⟩

theorem guardedPetriSource_typed (permitted : Bool) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (guardedPetriPlan permitted)).language
      (GeneralPlanEnvironment.environment (guardedPetriPlan permitted)).free []
      (.base "Marking") petriSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cases permitted <;> cbv

def guardedPetriLoggedRun (permitted : Bool) :=
  CollectionLoggedSearch.run (guardedPetriPlan permitted)
    (guardedPetriCertificate permitted) petriSource 30

def guardedPetriLoggedFirst (permitted : Bool) : CollectionPlanMachine.Firing :=
  (guardedPetriLoggedRun permitted).state.log[0]'(by cases permitted <;> cbv)

theorem guardedPetriLoggedFirst_member (permitted : Bool) :
    guardedPetriLoggedFirst permitted ∈ (guardedPetriLoggedRun permitted).state.log :=
  List.getElem_mem _

def guardedPetriGoal (permitted : Bool) : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget (guardedPetriLoggedFirst permitted).request
      (guardedPetriLoggedFirst permitted).receipt.source)
    (guardedPetriLoggedFirst permitted).ordinal

def guardedPetriScheduled (permitted : Bool) :=
  startLoggedPublished (guardedPetriPlan permitted) (guardedPetriCertificate permitted)
    petriSource 30 0 (.base "Marking") (guardedPetriLoggedFirst permitted)
    (guardedPetriLoggedFirst_member permitted) (guardedPetriSource_typed permitted)

def guardedPetriScheduledRun (permitted : Bool) :=
  StructuralDescent.Scheduled.run
    (GeneralPlanEnvironment.environment (guardedPetriPlan permitted))
    (guardedPetriGoal permitted) 20 (guardedPetriScheduled permitted)

#guard (guardedPetriLoggedRun true).state.log.length = 1
#guard (guardedPetriLoggedRun false).state.log.length = 1
#guard (guardedPetriScheduledRun true).answers.length = 1
#guard (guardedPetriScheduledRun false).answers.isEmpty
#guard (guardedPetriScheduledRun true).agenda.isEmpty
#guard (guardedPetriScheduledRun false).agenda.isEmpty
#guard (guardedPetriScheduledRun true).unresolved.isEmpty
#guard (guardedPetriScheduledRun false).unresolved.isEmpty

/-- Draining a depth-cut computation is not a negative semantic answer. -/
def petriDepthCutGoal : StructuralDescent.Scheduled.Goal :=
  .root 0 [] (.base "Marking") petriSource 0

def petriDepthCut := StructuralDescent.Scheduled.run petriEnvironment petriDepthCutGoal 1
  (StructuralDescent.Scheduled.start petriEnvironment petriDepthCutGoal)

#guard petriDepthCut.agenda.isEmpty
#guard petriDepthCut.answers.isEmpty
#guard petriDepthCut.unresolved == [.depthExhausted 0]
#guard !GeneralPremise.Scheduler.complete petriDepthCut

/-! Duplicate source occurrences remain separate. Alternative ordinary
proofs for each one must not multiply those occurrences a second time. -/

def petriDuplicateSource : Pattern := marking [token "A", token "A", token "B"]
def petriDuplicateLoggedRun :=
  CollectionLoggedSearch.run petriPlan petriCertificate petriDuplicateSource 30

theorem petriDuplicateSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      petriEnvironment.language petriEnvironment.free [] (.base "Marking")
      petriDuplicateSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

def petriDuplicateFiring (index : Fin 2) : CollectionPlanMachine.Firing :=
  petriDuplicateLoggedRun.state.log[index.val]'(by
    have length : petriDuplicateLoggedRun.state.log.length = 2 := by cbv
    rw [length]
    exact index.isLt)

theorem petriDuplicateFiring_member (index : Fin 2) :
    petriDuplicateFiring index ∈ petriDuplicateLoggedRun.state.log := List.getElem_mem _

def petriDuplicateGoal (index : Fin 2) : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget (petriDuplicateFiring index).request
      (petriDuplicateFiring index).receipt.source) (petriDuplicateFiring index).ordinal

def petriDuplicateScheduled (index : Fin 2) :=
  startLoggedPublished petriPlan petriCertificate petriDuplicateSource 30 0 (.base "Marking")
    (petriDuplicateFiring index) (petriDuplicateFiring_member index) petriDuplicateSource_typed

def petriDuplicateScheduledRun (index : Fin 2) :=
  StructuralDescent.Scheduled.run petriEnvironment (petriDuplicateGoal index) 20
    (petriDuplicateScheduled index)

#guard petriDuplicateLoggedRun.state.log.length = 2
#guard petriDuplicateLoggedRun.state.log.map (fun firing => (adaptations firing).length) == [2, 2]
#guard (petriDuplicateFiring 0).receipt.source.allocation.decisions !=
  (petriDuplicateFiring 1).receipt.source.allocation.decisions
#guard (petriDuplicateScheduledRun 0).answers.length = 1
#guard (petriDuplicateScheduledRun 1).answers.length = 1
#guard (petriDuplicateScheduledRun 0).unresolved.isEmpty
#guard (petriDuplicateScheduledRun 1).unresolved.isEmpty

/-! A premise can supply an RHS value absent from the initial capture. Raw
match receipts must reach the shared continuation before reduct construction. -/

def producedPetriPlan (permitted : Bool) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    { language := { petri with rewrites := petri.rewrites.map fun rule =>
        { rule with
          typeContext := rule.typeContext ++ [("made", .base "Place")]
          premises := [.relationQuery "produce" [.fvar "made"]]
          right := .collection .hashBag [.fvar "made"] (some "rest")
          bindings := none } }
      freeTypes := []
      provider :=
        { signatures := [{ relation := "produce", argumentTypes := [.base "Place"], modes := [.output] }]
          rows := if permitted then [{ relation := "produce", values := [token "C"] }] else [] } }
    permissions

def producedPetriCertificate (permitted : Bool) :
    CollectionExecutionAdmission.Certificate (producedPetriPlan permitted) :=
  ⟨by cases permitted <;> cbv⟩

def producedPetriRequests (permitted : Bool) :=
  CollectionExecutionAdmission.requestsForSource (producedPetriPlan permitted)
    (producedPetriCertificate permitted) petriSource

def producedPetriEntry (permitted : Bool) : Nat × Request :=
  (producedPetriRequests permitted)[0]'(by cases permitted <;> cbv)

def producedPetriReceipt (permitted : Bool) : Receipt :=
  (publication (resume (producedPetriEntry permitted).2 30
    (start (producedPetriEntry permitted).2)))[0]'(by cases permitted <;> cbv)

theorem producedPetriAuthority (permitted : Bool) :
    MatchAuthority (producedPetriPlan permitted) (producedPetriCertificate permitted)
      petriSource (producedPetriEntry permitted).1 (producedPetriEntry permitted).2
      (producedPetriReceipt permitted) :=
  match_authority_of_origin (producedPetriPlan permitted) (producedPetriCertificate permitted)
    petriSource (List.getElem_mem _) (ScopedCollectionMachine.publication_sound _ 30 (List.getElem_mem _))

theorem producedPetriSource_typed (permitted : Bool) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (producedPetriPlan permitted)).language
      (GeneralPlanEnvironment.environment (producedPetriPlan permitted)).free []
      (.base "Marking") petriSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cases permitted <;> cbv

def producedPetriGoal (permitted : Bool) : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget (producedPetriEntry permitted).2
      (producedPetriReceipt permitted)) (producedPetriEntry permitted).1

def producedPetriScheduled (permitted : Bool) :=
  startMatch (producedPetriPlan permitted) (producedPetriCertificate permitted)
    petriSource 0 (.base "Marking") (producedPetriEntry permitted).1
    (producedPetriEntry permitted).2 (producedPetriReceipt permitted)
    (producedPetriAuthority permitted) (producedPetriSource_typed permitted)

def producedPetriRun (permitted : Bool) :=
  StructuralDescent.Scheduled.run (GeneralPlanEnvironment.environment (producedPetriPlan permitted))
    (producedPetriGoal permitted) 30 (producedPetriScheduled permitted)

def producedPetriTargets (permitted : Bool) : List Pattern :=
  (producedPetriRun permitted).answers.map fun
    | .root _ _ _ _ target _ => target

#guard (ScopedCollectionMachine.firings (producedPetriEntry true).2
  (resume (producedPetriEntry true).2 30 (start (producedPetriEntry true).2))).isEmpty
#guard (producedPetriRun true).answers.length = 1
#guard producedPetriTargets true == [marking [token "C"]]
#guard (producedPetriRun false).answers.isEmpty
#guard (producedPetriRun true).agenda.isEmpty
#guard (producedPetriRun false).agenda.isEmpty
#guard (producedPetriRun true).unresolved.isEmpty
#guard (producedPetriRun false).unresolved.isEmpty

set_option maxHeartbeats 4000000

/-- The provisional-reduct search never publishes this source transition,
regardless of budget. Its completed empty log is stable. -/
theorem producedPetri_raw_log_empty (work : Nat) :
    (CollectionLoggedSearch.run (producedPetriPlan true) (producedPetriCertificate true)
      petriSource work).state.log = [] := by
  let search := CollectionLoggedSearch.search (producedPetriPlan true) (producedPetriCertificate true)
  have lawful := CollectionLoggedSearch.search_lawful (producedPetriPlan true) (producedPetriCertificate true)
  have empty : (search.run petriSource 30).state.log = [] := by cbv
  have complete : search.status (search.run petriSource 30) = .complete := by cbv
  change (search.run petriSource work).state.log = []
  by_cases before : work ≤ 30
  · have grown := lawful.publication_prefix petriSource work (30 - work)
    rw [Nat.add_sub_of_le before] at grown
    change (search.run petriSource work).state.log <+: (search.run petriSource 30).state.log at grown
    rw [empty] at grown
    simpa using grown
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge before))
    have stable := (CollectionLoggedSearch.search_stable
      (producedPetriPlan true) (producedPetriCertificate true))
      (search.run petriSource 30) extra complete
    rw [lawful.resume_run] at stable
    exact stable.1.trans empty

/-- Admission accepts the producer plan even though its provisional-reduct
profile stays empty. The producer controls above exercise the missing RHS. -/
theorem producedPetri_raw_admitted_empty :
    (producedPetriPlan true).complete = true ∧
    ∀ work, (CollectionLoggedSearch.run (producedPetriPlan true)
      (producedPetriCertificate true) petriSource work).state.log = [] := by
  exact ⟨by cbv, producedPetri_raw_log_empty⟩

/-- Equal-size nested allocations publish answers in successive stages.
A flattened cursor loses an earlier allocation's new receipt even though
the resulting answer-value multiset can coincide. -/
def outOfOrderRequest : Request :=
  let schemas : List Pattern := [.collection .hashBag [.fvar "X"] (some "Y")]
  let rule : RewriteRule :=
    { name := "nested-publication"
      typeContext := [("X", .base "Item"), ("Y", .base "Items"), ("R", .base "Items")]
      premises := [], left := .collection .hashBag schemas (some "R"), right := .fvar "X" }
  { rule, spec := ⟨[("X", []), ("Y", []), ("R", [])], []⟩,
    ambient := 0, site := .left, path := [], depth := 0, index := 0, initial := [],
    schemas, rest := some "R", kind := .hashBag,
    targets := arrange .hashBag
      [.collection .hashBag [token "A", token "A"] none,
       .collection .hashBag [token "A", token "B"] none] }

def outOfOrderState (work : Nat) : CollectionLoggedSearch.State :=
  CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin [(0, outOfOrderRequest)])

#guard CollectionLoggedSearch.complete (outOfOrderState 100)
#guard ((outOfOrderState 100).log.map (·.receipt.target)).countP (· == token "A") == 3
#guard ((outOfOrderState 100).log.map (·.receipt.target)).countP (· == token "B") == 1
#guard ((outOfOrderState 100).log.map (fun firing => reprStr firing.receipt)).mergeSort (· ≤ ·) ==
  ((firings outOfOrderRequest (resume outOfOrderRequest 100 (start outOfOrderRequest))).map
    reprStr).mergeSort (· ≤ ·)

/-- Every Petri marking has a finite exact collection frontier. This is the
source matching/reduct layer; shared typing and premises remain downstream. -/
theorem petri_source_frontier_exact (items : List Pattern) :
    let requests := CollectionExecutionAdmission.requestsForSource petriPlan petriCertificate (marking items)
    ∃ work, CollectionLoggedSearch.complete
        (CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)) = true ∧
      ((CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)).log.map
        CollectionLoggedSearch.outcome).Perm
        (requests.flatMap fun entry => (CollectionLoggedSearch.Lane.begin entry).sourceTargets) :=
  CollectionLoggedSearch.eventually_source_exact _

/-- The graph frontier has the same exactness for arbitrary finite edge
collections, including repeated selection and overlapping set residuals. -/
theorem graph_source_frontier_exact (items : List Pattern) :
    let requests := CollectionExecutionAdmission.requestsForSource reachabilityPlan
      reachabilityCertificate (graph items)
    ∃ work, CollectionLoggedSearch.complete
        (CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)) = true ∧
      ((CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)).log.map
        CollectionLoggedSearch.outcome).Perm
        (requests.flatMap fun entry => (CollectionLoggedSearch.Lane.begin entry).sourceTargets) :=
  CollectionLoggedSearch.eventually_source_exact _

/-! A premise-produced result has an independent source derivation and a
proved eventual publication; an empty provider has no such source firing. -/
namespace ProducedCoverage

open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.CollectionConsumers
open Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls
open CollectionMatcherBackend

def environment := GeneralPlanEnvironment.environment (producedPetriPlan true)
def request := (producedPetriEntry true).2
def receipt := producedPetriReceipt true
def captured := receipt.matching.assignment
def completed : Assignment := ("made", ⟨[], 0, token "C"⟩) :: captured
def context : GeneralPremise.Context :=
  ⟨(producedPetriEntry true).1, request.rule, request.spec, [], 0, 0⟩
def history : List GeneralPremise.Event := [.query 0 0 0 [(0, [])]]

theorem captured_typed : GeneralPremise.TypedAssignment environment context captured := by
  apply GeneralPremise.checkTypedAssignment_sound
  cbv

theorem completed_typed : GeneralPremise.TypedAssignment environment context completed := by
  apply GeneralPremise.checkTypedAssignment_sound
  cbv

theorem premises : GeneralPremise.PremisesHold environment context request.rule.premises
    captured completed history := by
  have shape : request.rule.premises = [.relationQuery "produce" [.fvar "made"]] := by cbv
  rw [shape]
  change GeneralPremise.PremisesHold environment context [.relationQuery "produce" [.fvar "made"]]
    captured completed [.query 0 0 0 [(0, [])]]
  apply GeneralPremise.PremisesHold.cons (middle := completed)
  · apply GeneralPremise.PremiseHolds.query
    apply GeneralPremise.TracedQuery.row
      (row := ⟨"produce", [token "C"]⟩)
      (signature := ⟨"produce", [.base "Place"], [.output]⟩)
    · cbv
    · cbv
    · apply GeneralPremise.checkRow_sound
      cbv
    · exact .output (.capture (by cbv)) .nil
    · exact completed_typed
  · exact .nil

theorem reduced : reductWith? (ScopedReflectiveExecution.binderOperation
    environment.reflection request.rule) request.rule request.spec 0 completed =
    some (marking [token "C"]) := by
  cbv

theorem target_typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
    environment.language environment.free [] (.base "Marking") (marking [token "C"]) := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

theorem source_firing : ∃ trace,
    GeneralPremise.RootFiring environment [] (.base "Marking")
      (CollectionMatcherCompatibility.ordinaryTarget request receipt)
      (producedPetriEntry true).1 trace captured completed history (marking [token "C"]) := by
  let authority := producedPetriAuthority true
  obtain ⟨answer, _, same⟩ := CollectionMatcherCompatibility.ordinaryAnswers_complete
    authority.ready.index authority.unordered authority.valid
  have matching := (ordinaryRootAnswer request receipt authority.ready answer).property
  change GeneralScopedMatchMachine.TracedMatches request.rule request.spec 0 .left [] 0 []
    request.rule.left (CollectionMatcherCompatibility.ordinaryTarget request receipt)
    answer.val.trace answer.val.assignment at matching
  rw [same] at matching
  exact ⟨answer.val.trace, .fire authority.declared authority.specified authority.admitted
    (authority.source_typed (producedPetriSource_typed true)) matching captured_typed
    premises reduced target_typed⟩

theorem eventual_C : ∃ fuel,
    marking [token "C"] ∈
      (StructuralDescent.Scheduled.run environment (producedPetriGoal true) fuel
        (producedPetriScheduled true)).answers.map (fun | .root _ _ _ _ target _ => target) := by
  obtain ⟨trace, held⟩ := source_firing
  let authority := producedPetriAuthority true
  obtain ⟨fuel, chosenTrace, proved, emitted⟩ := startRequest_covers environment 0 (.base "Marking")
    (producedPetriEntry true).1 request receipt authority.ready authority.unordered authority.valid
    authority.declared authority.specified authority.admitted
    (authority.source_typed (producedPetriSource_typed true)) trace completed history
    (marking [token "C"]) held (by cbv)
  refine ⟨fuel, ?_⟩
  have mapped := List.mem_map_of_mem (f := fun
    (result : StructuralDescent.Scheduled.Result environment (producedPetriGoal true)) =>
      match result with | .root _ _ _ _ target _ => target) emitted
  exact mapped

theorem empty_provider_no_firing
    (trace : List GeneralScopedMatchMachine.BagChoice) (initial final : Assignment)
    (events : List GeneralPremise.Event) (target : Pattern) :
    ¬ GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (producedPetriPlan false))
      [] (.base "Marking")
      (CollectionMatcherCompatibility.ordinaryTarget (producedPetriEntry false).2
        (producedPetriReceipt false))
      (producedPetriEntry false).1 trace initial final events target := by
  intro held
  let authority := producedPetriAuthority false
  cases held with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified _ _ _ _ premises _ _ =>
      have ruleEq := Option.some.inj (declared.symm.trans authority.declared)
      subst rule
      have shape : (producedPetriEntry false).2.rule.premises =
          [.relationQuery "produce" [.fvar "made"]] := by cbv
      rw [shape] at premises
      cases premises with
      | cons head tail =>
        cases head with
        | query query =>
          cases query with
          | row selected _ _ _ _ =>
            have empty : (GeneralPlanEnvironment.environment (producedPetriPlan false)).provider.rows = [] := by cbv
            rw [empty] at selected
            simp at selected
          | dynamicRow registered _ _ _ _ _ _ _ =>
            have empty : (GeneralPlanEnvironment.environment (producedPetriPlan false)).provider.dynamicRelations = [] := by cbv
            rw [empty] at registered
            cases registered


end ProducedCoverage

namespace RetainedControls

def producedMatch (permitted : Bool) : Retained.Match :=
  ⟨(producedPetriEntry permitted).1, (producedPetriEntry permitted).2,
    producedPetriReceipt permitted⟩

def producedFrame (permitted : Bool) :=
  Retained.Frame.initial (producedMatch permitted) (producedPetriAuthority permitted)
    (producedPetriSource_typed permitted) 0

def producedBegin (permitted : Bool) := Retained.State.begin [producedFrame permitted]
def producedRun (permitted : Bool) := Retained.State.run 30 (producedBegin permitted)
def producedTargets (permitted : Bool) : List Pattern :=
  (producedRun permitted).log.map (fun publication => publication.outcome.target)

#guard producedTargets true == [marking [token "C"]]
#guard (producedRun false).log.isEmpty
#guard (producedRun true).complete
#guard (producedRun false).complete

def duplicateMatch (index : Fin 2) : Retained.Match :=
  let firing := petriDuplicateFiring index
  ⟨firing.ordinal, firing.request, firing.receipt.source⟩

theorem duplicateAuthority (index : Fin 2) :
    MatchAuthority petriPlan petriCertificate petriDuplicateSource
      (duplicateMatch index).ordinal (duplicateMatch index).request (duplicateMatch index).receipt :=
  let authority := logged_publication_authority petriPlan petriCertificate petriDuplicateSource 30
    (petriDuplicateFiring_member index)
  match_authority_of_origin petriPlan petriCertificate petriDuplicateSource authority.origin authority.valid.1

def duplicateFrame (index : Fin 2) :=
  Retained.Frame.initial (duplicateMatch index) (duplicateAuthority index)
    petriDuplicateSource_typed 0

def duplicateBegin := Retained.State.begin [duplicateFrame 0, duplicateFrame 1]
def duplicateRun := Retained.State.run 30 duplicateBegin

#guard duplicateRun.log.length = 2
#guard duplicateRun.complete
#guard (duplicateRun.log[0]?.map (fun result => result.outcome.target)) ==
  (duplicateRun.log[1]?.map (fun result => result.outcome.target))
#guard (duplicateRun.log[0]?.map (fun result => result.matched.receipt.allocation.decisions)) !=
  (duplicateRun.log[1]?.map (fun result => result.matched.receipt.allocation.decisions))

/-- The independent producer source derivation reaches the one retained
publication log even though the old provisional-reduct search is always empty. -/
theorem producer_eventually_C :
    ∃ work, marking [token "C"] ∈
      (Retained.State.run work (producedBegin true)).log.map (fun result => result.outcome.target) := by
  obtain ⟨trace, held⟩ := ProducedCoverage.source_firing
  obtain ⟨work, chosenTrace, published⟩ := Retained.State.source_coverage
    [producedFrame true] (producedMatch true) (producedPetriAuthority true)
    (producedPetriSource_typed true) 0 List.mem_cons_self trace ProducedCoverage.completed
    ProducedCoverage.history (marking [token "C"]) held (by cbv)
  exact ⟨work, List.mem_map_of_mem published⟩

end RetainedControls

namespace RootControls

def petriProfile : CollectionRootSearch.Profile petriPlan :=
  ⟨petriCertificate, by cbv, by cbv, by cbv, by cbv, by rfl⟩

def graphProfile : CollectionRootSearch.Profile reachabilityPlan :=
  ⟨reachabilityCertificate, by cbv, by cbv, by cbv, by cbv, by rfl⟩

def petriCoverage : CollectionRootSearch.CoverageProfile petriPlan :=
  ⟨petriProfile, fun declaration member => CollectionRootSearch.canonicalRuleCheck_sound
    (List.all_eq_true.mp (show petriPlan.rules.all
      (CollectionRootSearch.canonicalRuleCheck (GeneralPlanEnvironment.environment petriPlan).reflection) = true by cbv)
      declaration member), by cbv, by cbv⟩

def graphCoverage : CollectionRootSearch.CoverageProfile reachabilityPlan :=
  ⟨graphProfile, fun declaration member => CollectionRootSearch.canonicalRuleCheck_sound
    (List.all_eq_true.mp (show reachabilityPlan.rules.all
      (CollectionRootSearch.canonicalRuleCheck (GeneralPlanEnvironment.environment reachabilityPlan).reflection) = true by cbv)
      declaration member), by cbv, by cbv⟩

#guard (CollectionRootSearch.coverageProfile? petriPlan).isSome
#guard (CollectionRootSearch.coverageProfile? reachabilityPlan).isSome

example : CollectionRootSearch.checkSpineOrder [.bvar 0, .bvar 2, .bvar 5] = true := by decide
example : CollectionRootSearch.checkSpineOrder [.bvar 2, .bvar 0] = false := by decide
example : CollectionRootSearch.checkSpineOrder [.bvar 1, .bvar 1] = true := by decide

-- Consuming two distinct positions cannot match a canonical singleton set.
-- It can match its duplicate presentation, which has the same set meaning.
#guard (graphLoop.map fun request => (matchAt request.rule request.spec 0 .left [] 0 [] request.rule.left
  (.collection .hashSet [edge "A" "A"] none)).isEmpty) == some true
#guard (graphLoop.map fun request => (matchAt request.rule request.spec 0 .left [] 0 [] request.rule.left
  (.collection .hashSet [edge "A" "A", edge "A" "A"] none)).isEmpty) == some false

private def firstPetriDeclaration : GeneralExecutionAdmission.RulePlan :=
  petriPlan.rules[0]'(by cbv)

example : CollectionRootSearch.canonicalRuleCheck .empty
    { firstPetriDeclaration with authored := { firstPetriDeclaration.authored with
      left := .collection .hashSet [.collection .hashSet [] none] none } } = false := by cbv

example : CollectionRootSearch.canonicalRuleCheck .empty
    { firstPetriDeclaration with authored := { firstPetriDeclaration.authored with
      premises := [.relationQuery "requires-service" []] } } = false := by cbv

theorem petri_presented_iff_published (source target : Pattern) :
    (Complete.Presented.gslt petriPlan [] (.base "Marking")).Step source (canon target) ↔
      ∃ work receipt, receipt ∈ CollectionRootSearch.publication (.base "Marking")
        ((CollectionRootSearch.search (profile := petriCoverage.profile) (.base "Marking")).run
          (canon source) work) ∧ canon receipt.target = canon target :=
  CollectionRootSearch.presented_iff_published petriCoverage.profile (.base "Marking")
    petriCoverage.rules petriCoverage.noLaws petriCoverage.noExtrusions source target

theorem graph_presented_iff_published (source target : Pattern) :
    (Complete.Presented.gslt reachabilityPlan [] (.base "Graph")).Step source (canon target) ↔
      ∃ work receipt, receipt ∈ CollectionRootSearch.publication (.base "Graph")
        ((CollectionRootSearch.search (profile := graphCoverage.profile) (.base "Graph")).run
          (canon source) work) ∧ canon receipt.target = canon target :=
  CollectionRootSearch.presented_iff_published graphCoverage.profile (.base "Graph")
    graphCoverage.rules graphCoverage.noLaws graphCoverage.noExtrusions source target

def producedProfile (permitted : Bool) : CollectionRootSearch.Profile (producedPetriPlan permitted) :=
  ⟨producedPetriCertificate permitted, by cases permitted <;> cbv,
    by cases permitted <;> cbv, by cases permitted <;> cbv,
    by cases permitted <;> cbv, by rfl⟩

def producedRun (permitted : Bool) (work : Nat) :=
  (CollectionRootSearch.search (profile := producedProfile permitted) (.base "Marking")).run petriSource work

theorem produced_source_reaches_C :
    ∃ work receipt,
      receipt ∈ CollectionRootSearch.publication (.base "Marking") (producedRun true work) ∧
      receipt.target = marking [token "C"] := by
  obtain ⟨trace, held⟩ := ProducedCoverage.source_firing
  let receipt : CollectionRootSearch.Receipt :=
    ⟨RetainedControls.producedMatch true, ProducedCoverage.completed,
      ProducedCoverage.history, marking [token "C"]⟩
  obtain ⟨work, published⟩ := CollectionRootSearch.source_coverage (.base "Marking")
    (receipt := receipt) (profile := producedProfile true)
    ⟨producedPetriAuthority true, trace, held⟩
  exact ⟨work, receipt, published, rfl⟩

end RootControls

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls

/-! Prefix observations retain their complete committed packets.
These readouts make no enumeration-completion assertion. -/

namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBags CollectionOccurrenceBatch CollectionCommittedObservation GeneralPremise
open Mettapedia.GSLT.LanguageDef.CollectionConsumers

namespace PetriControls

open Mettapedia.GSLT.LanguageDef.CollectionConsumers

def guardedLanguage : LanguageDef :=
  let first := petri.rewrites[0]' (by cbv)
  { petri with «rewrites» :=
    [{ first with «name» := "route-left", premises := [.relationQuery "permit" []] },
     { first with «name» := "route-right", premises := [.relationQuery "permit" []] }] }

def plan (copies : Nat) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    ⟨guardedLanguage, [],
      { signatures := [⟨"permit", [], []⟩],
        rows := List.replicate copies ⟨"permit", []⟩ }⟩
    { sites := .rootOnly, includeDerivedEquations := false }

def source : Pattern := marking [token "A", token "A", token "B"]
def expected : TypeExpr := .base "Marking"

def finished (copies : Nat) : CollectionOccurrenceMachine.State (plan copies) [] expected source :=
  CollectionOccurrenceMachine.run 0 120 (CollectionOccurrenceMachine.begin (plan copies) [] expected source)

def check : IO Unit := do
  let first := finished 1
  let duplicate := finished 2
  let none := finished 0
  let left := retained (plan 1) [] expected first.batch.log
  let replayed := retained (plan 2) [] expected duplicate.batch.log
  IO.println s!"raw {left.length} / {replayed.length}; keys {(allocationKeys (plan 1) [] expected first.batch.log).card} / {(allocationKeys (plan 2) [] expected duplicate.batch.log).card}; successorStates {(successorStates (plan 2) [] expected duplicate.batch.log).card}; bag {(allocationBag (plan 2) [] expected duplicate.batch.log).card}"
  unless left.length == 4 && replayed.length == 8 do
    throw (IO.userError "actual committed packet count disagrees")
  unless (allocationKeys (plan 2) [] expected duplicate.batch.log).card == 4 do
    throw (IO.userError "validation duplicates changed declared occurrence count")
  unless (successorStates (plan 2) [] expected duplicate.batch.log).card == 1 &&
      (allocationBag (plan 2) [] expected duplicate.batch.log).card == 4 do
    throw (IO.userError "fact and derivation aggregation were conflated")
  unless (retained (plan 0) [] expected none.batch.log).isEmpty do
    throw (IO.userError "missing premise produced a committed derivation")
  unless (allocationKeys (plan 1) [] expected first.batch.log) ==
      allocationKeys (plan 2) [] expected duplicate.batch.log do
    throw (IO.userError "duplicated validation did not preserve declared keys")
  let routes := ((retained (plan 2) [] expected duplicate.batch.log).map (fun entry => (allocationKey entry).authoredRule)).eraseDups
  unless routes.length == 2 do
    throw (IO.userError "independent authored routes were identified")
  let allocations := ((retained (plan 2) [] expected duplicate.batch.log).map (fun entry => (allocationKey entry).allocation.trace)).eraseDups
  unless allocations.length == 2 do
    throw (IO.userError "equal physical token occurrences were identified")
  IO.println "CommittedObservationControls: validation replay, route identity, token identity and absent premise passed"

#eval check

end PetriControls

namespace GraphControls

open Mettapedia.GSLT.LanguageDef.CollectionConsumers

def source : Pattern := graph [edge "A" "B", edge "B" "C"]
def finished := CollectionOccurrenceMachine.run 0 160
  (CollectionOccurrenceMachine.begin reachabilityPlan [] (.base "Graph") source)

def diamond : Pattern :=
  graph [edge "A" "B", edge "B" "C", edge "A" "C", edge "C" "C"]
def finishedDiamond := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin reachabilityPlan [] (.base "Graph") diamond)

def producedEdge? (key : AllocationKey) : Option Pattern := do
  let first ← ScopedRuleMatching.lookup key.completed "x"
  let last ← ScopedRuleMatching.lookup key.completed "z"
  some (.apply "Edge" [first.body, last.body])

def inferredBag (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Multiset Pattern :=
  (allocationKeys plan [] (.base "Graph") packets).val.filterMap producedEdge?

def inferredFacts (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset Pattern :=
  (inferredBag plan packets).toFinset

/-- The root graph observation retains the licensed typed path, but no
source focus or residual/context payload. This projection is scoped to the
root graph policy; allocation observations retain the complete site. -/
structure LogicalSiteShape where
  address : List Nat
  bound : List TypeExpr
  type : TypeExpr
  typingFrames : List GeneralTypedSites.TypingFrame
  deriving DecidableEq

def logicalSiteShape (site : GeneralTypedSites.SiteData) : LogicalSiteShape :=
  ⟨site.address, site.focusBound, site.focusType, site.typingFrames⟩

theorem logicalSiteShape_ignores_payload (site : GeneralTypedSites.SiteData)
    (focus : Pattern) (context : DerivedContexts.OneHoleContext) :
    logicalSiteShape {site with focus := focus, context := context} = logicalSiteShape site := rfl

/-- Root transitivity is identified by its non-rest input binding tuple.
Its rule has no child-step premises; the retained child-history coordinate
keeps explicit child evidence if a separate profile later authorizes it.
Allocation-sensitive publication remains available beside this readout. -/
structure LogicalKey (Choice : Type := GeneralScopedMatchMachine.BagChoice) where
  selectedRule : Nat
  authoredRule : Nat
  siteShape : LogicalSiteShape
  first : Option RuleBinding.ContextualValue
  intermediate : Option RuleBinding.ContextualValue
  last : Option RuleBinding.ContextualValue
  childHistory : List (GeneralPremise.Event Choice)
  deriving DecidableEq

def logicalKey {Choice : Type} (committed : Committed Choice) : LogicalKey Choice :=
  let packet := committed.1
  let receipt := committed.2
  ⟨packet.job.origin.ordinal, packet.job.origin.declaration.declarationIndex, logicalSiteShape packet.job.origin.site,
    (ScopedRuleMatching.lookup receipt.completed "x").map canonValue,
    (ScopedRuleMatching.lookup receipt.completed "y").map canonValue,
    (ScopedRuleMatching.lookup receipt.completed "z").map canonValue,
    validationHistoryReadout receipt.premiseHistory .factValidation⟩

def logicalEdge? {Choice : Type} (key : LogicalKey Choice) : Option Pattern := do
  let first ← key.first
  let last ← key.last
  some (.apply "Edge" [first.body, last.body])

def logicalKeys (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset LogicalKey :=
  declaredKeys logicalKey plan [] (.base "Graph") packets

def logicalBag (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Multiset Pattern :=
  (logicalKeys plan packets).val.filterMap logicalEdge?

def logicalFacts (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset Pattern :=
  (logicalBag plan packets).toFinset

theorem logicalKey_ignores_allocation {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice)
    (allocation : RecursiveCollectionMachine.Answer) (variant : CollectionSelection.SiteVariant)
    (trace : List Choice) :
    logicalKey (⟨{packet.job with variant := variant}, allocation, packet.prepared, packet.outcome⟩,
        {receipt with matcherTrace := trace}) =
      logicalKey (packet, receipt) := rfl

theorem logicalKey_ignores_source_payload {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice)
    (focus : Pattern) (context : DerivedContexts.OneHoleContext) :
    let site := {packet.job.origin.site with focus := focus, context := context}
    let origin := {packet.job.origin with site := site}
    logicalKey (⟨⟨origin, packet.job.variant⟩, packet.answer, packet.prepared, packet.outcome⟩, receipt) =
      logicalKey (packet, receipt) := rfl

theorem logicalKey_canonical_source_presentation {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice) :
    let site := {packet.job.origin.site with focus := canon packet.job.origin.site.focus}
    let origin := {packet.job.origin with site := site}
    logicalKey (⟨⟨origin, packet.job.variant⟩, packet.answer, packet.prepared, packet.outcome⟩, receipt) =
      logicalKey (packet, receipt) := rfl

theorem logicalKey_ignores_query_validation {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice)
    (p q row : Nat) (origins : List (Nat × List Choice)) :
    logicalKey (packet, {receipt with premiseHistory := [.query p q row origins]}) =
      logicalKey (packet, {receipt with premiseHistory := []}) := rfl

theorem logicalKey_erases_query_in_history {Choice : Type} (packet : Publication Choice)
    (receipt : GeneralRuleJobs.Receipt Choice) (before after : List (GeneralPremise.Event Choice))
    (premise quantifier row : Nat) (origins : List (Nat × List Choice)) :
    logicalKey (packet, {receipt with premiseHistory := before ++ .query premise quantifier row origins :: after}) =
      logicalKey (packet, {receipt with premiseHistory := before ++ after}) := by
  simp only [logicalKey, query_administration_erases]

theorem logicalKey_erases_freshness_in_history {Choice : Type} (packet : Publication Choice)
    (receipt : GeneralRuleJobs.Receipt Choice) (before after : List (GeneralPremise.Event Choice))
    (premise quantifier : Nat) (name : String) (subject : Pattern) :
    logicalKey (packet, {receipt with premiseHistory := before ++ .freshness premise quantifier name subject :: after}) =
      logicalKey (packet, {receipt with premiseHistory := before ++ after}) := by
  simp only [logicalKey, freshness_administration_erases]

theorem logicalBag_ordered_presentation (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :
    ((orderedCommittedKeys logicalKey (retained plan [] (.base "Graph") packets)).filterMap logicalEdge? :
      Multiset Pattern) = logicalBag plan packets :=
  orderedCommittedKeys_partial_bag logicalKey logicalEdge? _

theorem logicalFacts_ordered_presentation (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :
    ((orderedCommittedKeys logicalKey (retained plan [] (.base "Graph") packets)).filterMap logicalEdge?).toFinset =
      logicalFacts plan packets :=
  orderedCommittedKeys_partial_facts logicalKey logicalEdge? _

theorem logicalKey_nonrest_ext {Choice : Type} {first second : Committed Choice}
    (rule : first.1.job.origin.ordinal = second.1.job.origin.ordinal)
    (authored : first.1.job.origin.declaration.declarationIndex =
      second.1.job.origin.declaration.declarationIndex)
    (site : logicalSiteShape first.1.job.origin.site = logicalSiteShape second.1.job.origin.site)
    (x : (ScopedRuleMatching.lookup first.2.completed "x").map canonValue =
      (ScopedRuleMatching.lookup second.2.completed "x").map canonValue)
    (y : (ScopedRuleMatching.lookup first.2.completed "y").map canonValue =
      (ScopedRuleMatching.lookup second.2.completed "y").map canonValue)
    (z : (ScopedRuleMatching.lookup first.2.completed "z").map canonValue =
      (ScopedRuleMatching.lookup second.2.completed "z").map canonValue)
    (children : validationHistoryReadout first.2.premiseHistory .factValidation =
      validationHistoryReadout second.2.premiseHistory .factValidation) :
    logicalKey first = logicalKey second := by
  simp only [logicalKey, LogicalKey.mk.injEq]
  exact ⟨rule, authored, site, x, y, z, children⟩

theorem intermediate_distinguishes_route {Choice : Type} {first second : Committed Choice}
    (different : (ScopedRuleMatching.lookup first.2.completed "y").map canonValue ≠
      (ScopedRuleMatching.lookup second.2.completed "y").map canonValue) :
    logicalKey first ≠ logicalKey second := by
  intro same
  exact different (congrArg LogicalKey.intermediate same)

theorem logical_replay_invariant (plan : GeneralExecutionAdmission.Plan)
    (earlier replay : List Publication) (already : logicalKeys plan replay ⊆ logicalKeys plan earlier) :
    logicalBag plan (earlier ++ replay) = logicalBag plan earlier ∧
      logicalFacts plan (earlier ++ replay) = logicalFacts plan earlier := by
  have same : logicalKeys plan (earlier ++ replay) = logicalKeys plan earlier := by
    unfold logicalKeys at already ⊢
    rw [declaredKeys_append, Finset.union_eq_left.mpr already]
  simp only [logicalBag, logicalFacts, same, and_self]

theorem logical_balanced_observations {plan : GeneralExecutionAdmission.Plan} {source : Pattern}
    {state : State plan [] (.base "Graph") source} (balanced : state.Balanced) :
    logicalBag plan state.log = logicalBag plan (state.frames.flatMap Frame.publication) ∧
      logicalFacts plan state.log = logicalFacts plan (state.frames.flatMap Frame.publication) := by
  have same : logicalKeys plan state.log = logicalKeys plan (state.frames.flatMap Frame.publication) :=
    declaredKeys_perm logicalKey plan [] (.base "Graph") balanced
  simp only [logicalBag, logicalFacts, same, and_self]

def twoRouteLanguage : LanguageDef :=
  { reachability with «terms» := reachability.terms ++
    [{ label := "D", category := "Node", params := [], syntaxPattern := [] }] }

def twoRoutePlan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot twoRouteLanguage) permissions

def twoRouteSource : Pattern := graph
  [edge "A" "B", edge "B" "D", edge "A" "C", edge "C" "D"]

def twoRouteFinished := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") twoRouteSource)

def irrelevantExtensionSource : Pattern := graph
  [edge "A" "B", edge "B" "D", edge "A" "C", edge "C" "D", edge "D" "D"]

def irrelevantExtensionFinished := CollectionOccurrenceMachine.run 0 1600
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") irrelevantExtensionSource)

def reorderedDuplicateSource : Pattern := graph
  [edge "C" "D", edge "A" "B", edge "A" "C", edge "B" "D", edge "A" "B"]

def reorderedDuplicateFinished := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") reorderedDuplicateSource)

def canonicalSourceFinished := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") (canon twoRouteSource))

def aToDKeys (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset LogicalKey :=
  (logicalKeys plan packets).filter fun key => logicalEdge? key = some (edge "A" "D")

/-- A separating readout that deliberately retains the forbidden source
payload, used to check that the extension control detects that regression. -/
def sourceSensitiveAToDKeys (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :
    Finset (GeneralTypedSites.SiteData × LogicalKey) :=
  ((retained plan [] (.base "Graph") packets).filter
    (fun committed => logicalEdge? (logicalKey committed) == some (edge "A" "D"))).map
      (fun committed => (committed.1.job.origin.site, logicalKey committed)) |>.toFinset

def guardedTwoRouteLanguage : LanguageDef :=
  {twoRouteLanguage with «rewrites» := twoRouteLanguage.rewrites.map fun rule =>
    {rule with premises := [.relationQuery "permit" []]}}

def guardedTwoRoutePlan (copies : Nat) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    ⟨guardedTwoRouteLanguage, [],
      {signatures := [⟨"permit", [], []⟩],
        rows := List.replicate copies ⟨"permit", []⟩}⟩ permissions

def guardedTwoRouteFinished (copies : Nat) := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin (guardedTwoRoutePlan copies) [] (.base "Graph") twoRouteSource)

def actualRule : RewriteRule := (reachabilityPlan.rules[0]'(by cbv)).rule
def actualSpec : RuleBindingSpec := (reachabilityPlan.rules[0]'(by cbv)).binding.spec

def thirdEdge : Pattern := .apply "Edge" [.fvar "x", .fvar "z"]
def firstEdge : Pattern := .apply "Edge" [.fvar "x", .fvar "y"]
def secondEdge : Pattern := .apply "Edge" [.fvar "y", .fvar "z"]

theorem actual_left : actualRule.left =
    .collection .hashSet [firstEdge, secondEdge] (some "rest") := by cbv

theorem actual_right : actualRule.right =
    .collection .hashSet [firstEdge, secondEdge, thirdEdge] (some "rest") := by cbv

theorem instantiated_collection {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {assignment : ScopedRuleMatching.Assignment} {kind : CollType} {schemas : List Pattern}
    {rest : String} {target : Pattern}
    (produced : ScopedRuleMatching.instantiateWith? operation rule spec ambient .right [] 0 assignment
      (.collection kind schemas (some rest)) = some target) :
    ∃ explicit residual,
      ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient .right [] 0 assignment 0 schemas =
        some explicit ∧ target = .collection kind (explicit ++ residual) none := by
  simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at produced
  obtain ⟨explicit, built, value, found, arguments, occurrence, projected, interpreted, produced⟩ := produced
  cases projected with
  | collection actual residual rest =>
      cases rest with
      | none =>
          simp only at produced
          split_ifs at produced
          · exact ⟨explicit, residual, built, (Option.some.inj produced).symm⟩
      | some _ => cases produced
  | _ => cases produced

theorem instantiated_three_member {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {assignment : ScopedRuleMatching.Assignment} {first second third : Pattern} {outputs : List Pattern}
    (produced : ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient .right [] 0 assignment 0
      [first, second, third] = some outputs) :
    ∃ value, ScopedRuleMatching.instantiateWith? operation rule spec ambient .right [2] 0 assignment third =
      some value ∧ value ∈ outputs := by
  simp only [ScopedRuleMatching.instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.bind_some, Option.some.injEq, List.nil_append] at produced
  obtain ⟨one, oneMade, tail, tailMade, outputEq⟩ := produced
  obtain ⟨two, twoMade, last, lastMade, tailEq⟩ := tailMade
  obtain ⟨three, threeMade, lastEq⟩ := lastMade
  cases outputEq
  cases tailEq
  cases lastEq
  exact ⟨three, threeMade, by simp⟩

theorem third_edge_readout {operation : Pattern → Pattern → Pattern} {ambient : Nat}
    {assignment : ScopedRuleMatching.Assignment} {target : Pattern}
    (produced : ScopedRuleMatching.instantiateWith? operation actualRule actualSpec ambient .right [2] 0
      assignment thirdEdge = some target) :
    ∃ first last,
      ScopedRuleMatching.lookup assignment "x" = some first ∧
      ScopedRuleMatching.lookup assignment "z" = some last ∧
      target = .apply "Edge" [first.body, last.body] := by
  have xArguments : RuleBinding.arguments? actualRule actualSpec "x" .right [2, 0] = some [] := by cbv
  have zArguments : RuleBinding.arguments? actualRule actualSpec "z" .right [2, 1] = some [] := by cbv
  simp only [thirdEdge, ScopedRuleMatching.instantiateWith?, ScopedRuleMatching.instantiateArgsWith?,
    List.cons_append, List.nil_append, xArguments, zArguments,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq] at produced
  obtain ⟨arguments, built, outputEq⟩ := produced
  obtain ⟨firstBody, firstMade, tail, tailMade, argumentsEq⟩ := built
  obtain ⟨first, firstFound, firstRead⟩ := firstMade
  obtain ⟨lastBody, lastMade, tailEq⟩ := tailMade
  obtain ⟨last, lastFound, lastRead⟩ := lastMade
  have firstEq := (ConditionalEquationExecution.instantiate_root_readout first ambient firstBody firstRead).2
  have lastEq := (ConditionalEquationExecution.instantiate_root_readout last ambient lastBody lastRead).2
  cases outputEq
  cases argumentsEq
  cases tailEq
  exact ⟨first, last, firstFound, lastFound, by rw [firstEq, lastEq]⟩

theorem logical_edge_is_authored_output {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {packet : Publication} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source)
    (selected : receipt.job.declaration.rule = actualRule)
    (specified : receipt.job.declaration.binding.spec = actualSpec)
    {fact : Pattern} (read : logicalEdge? (logicalKey (packet, receipt)) = some fact) :
    ∃ items, receipt.localTarget = .collection .hashSet items none ∧ fact ∈ items.map canon := by
  have reduced := (GeneralRuleJobs.receipt_root_readout valid).2.2.2.1
  rw [selected, specified, ScopedRuleMatching.reductWith?, actual_right] at reduced
  obtain ⟨explicit, residual, instantiated, target⟩ := instantiated_collection reduced
  obtain ⟨third, thirdMade, member⟩ := instantiated_three_member instantiated
  obtain ⟨first, last, firstFound, lastFound, thirdEq⟩ := third_edge_readout thirdMade
  have inferred : fact = canon third := by
    simp only [logicalKey, logicalEdge?, firstFound, lastFound, Option.map_some, Option.bind_some,
      Option.bind_eq_bind, Option.some.injEq, CanonicalBags.canonValue] at read
    rw [← read, thirdEq, canon_apply]
    rfl
  exact ⟨explicit ++ residual, target, by
    rw [inferred]
    exact List.mem_map_of_mem (List.mem_append_left residual member)⟩

theorem logical_key_determines_fact {Choice : Type} {first second : Committed Choice}
    (same : logicalKey first = logicalKey second) :
    logicalEdge? (logicalKey first) = logicalEdge? (logicalKey second) :=
  congrArg logicalEdge? same

theorem two_route_selected {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid twoRoutePlan [] (.base "Graph") source) :
    receipt.job.declaration.rule = actualRule ∧ receipt.job.declaration.binding.spec = actualSpec := by
  have singleton : twoRoutePlan.rules = [reachabilityPlan.rules[0]'(by cbv)] := by cbv
  have member := List.fst_mem_of_mem_zipIdx valid.1.1
  rw [singleton, List.mem_singleton] at member
  change receipt.job.declaration = reachabilityPlan.rules[0]'(by cbv) at member
  rw [member]
  exact ⟨rfl, rfl⟩

/-- Each projected edge comes from the actual source rule match, over a
presentation equivalent to the caller source, and is present in that rule's
actual checked output. The inference map is not an assumed certificate. -/
theorem retained_logical_edge_licensed {source : Pattern}
    {state : State twoRoutePlan [] (.base "Graph") source} (balanced : state.Balanced)
    {committed : Committed} (published : committed ∈ retained twoRoutePlan [] (.base "Graph") state.log)
    {fact : Pattern} (read : logicalEdge? (logicalKey committed) = some fact) :
    Same source (committed.1.job.presentedSource committed.1.prepared) ∧
      GeneralScopedMatch.Matches actualRule actualSpec committed.2.job.site.focusBound.length
        .left [] 0 [] (.collection .hashSet [firstEdge, secondEdge] (some "rest"))
          committed.2.job.site.focus committed.2.captured ∧
      ∃ items, committed.2.localTarget = .collection .hashSet items none ∧ fact ∈ items.map canon := by
  have valid := retained_receipt_valid balanced published
  have selected := two_route_selected valid
  have matched := GeneralRuleJobs.receipt_source_matching valid
  rw [selected.1, selected.2, actual_left] at matched
  exact ⟨retained_source_same balanced published, matched,
    logical_edge_is_authored_output valid selected.1 selected.2 read⟩

def check : IO Unit := do
  let raw := retained reachabilityPlan [] (.base "Graph") finished.batch.log
  unless !raw.isEmpty do throw (IO.userError "authored graph module published no transitive inference")
  unless (successorStates reachabilityPlan [] (.base "Graph") finished.batch.log).card == 1 do
    throw (IO.userError "authored transitive graph observed more than one conclusion state")
  unless (allocationBag reachabilityPlan [] (.base "Graph") finished.batch.log).card > 1 do
    throw (IO.userError "set residual allocation occurrences were accidentally deduplicated")
  for committed in raw do
    unless CanonicalBags.canon committed.2.target ==
        CanonicalBags.canon (graph [edge "A" "B", edge "B" "C", edge "A" "C"]) do
      throw (IO.userError "authored graph transitivity produced a wrong conclusion")
  let cyclic := retained reachabilityPlan [] (.base "Graph") finishedDiamond.batch.log
  unless !cyclic.isEmpty do throw (IO.userError "cyclic graph consumer produced no inference")
  unless (inferredFacts reachabilityPlan finished.batch.log) == {edge "A" "C"} do
    throw (IO.userError "authored graph logical-edge readout produced a wrong fact")
  unless decide (edge "C" "A" ∉ inferredFacts reachabilityPlan finished.batch.log) do
    throw (IO.userError "authored graph inferred a reverse edge")
  let routes := retained twoRoutePlan [] (.base "Graph") twoRouteFinished.batch.log
  unless (inferredFacts twoRoutePlan twoRouteFinished.batch.log) == {edge "A" "D"} do
    throw (IO.userError "two-route graph did not infer exactly A-to-D")
  let intermediates := (routes.filterMap fun entry =>
    (ScopedRuleMatching.lookup entry.2.completed "y").map (·.body)).eraseDups
  unless intermediates.length == 2 do
    throw (IO.userError "two independent graph routes were identified")
  unless (inferredBag twoRoutePlan twoRouteFinished.batch.log).card > 1 do
    throw (IO.userError "inferred fact set replaced the derivation bag")
  unless (logicalKeys twoRoutePlan twoRouteFinished.batch.log).card == 2 &&
      (logicalBag twoRoutePlan twoRouteFinished.batch.log).card == 2 &&
      logicalFacts twoRoutePlan twoRouteFinished.batch.log == {edge "A" "D"} do
    throw (IO.userError "set residual presentations manufactured logical graph derivations")
  let once := (guardedTwoRouteFinished 1).batch.log
  let duplicate := (guardedTwoRouteFinished 2).batch.log
  unless (retained (guardedTwoRoutePlan 1) [] (.base "Graph") once).length == 8 &&
      (retained (guardedTwoRoutePlan 2) [] (.base "Graph") duplicate).length == 16 do
    throw (IO.userError "guarded graph raw validation publications changed")
  unless logicalKeys (guardedTwoRoutePlan 1) once == logicalKeys (guardedTwoRoutePlan 2) duplicate &&
      logicalKeys (guardedTwoRoutePlan 1) once == logicalKeys twoRoutePlan twoRouteFinished.batch.log do
    throw (IO.userError "provider validation manufactured logical graph derivations")
  unless (logicalBag (guardedTwoRoutePlan 2) duplicate).card == 2 &&
      logicalFacts (guardedTwoRoutePlan 2) duplicate == {edge "A" "D"} do
    throw (IO.userError "logical graph routes and fact aggregation were conflated")
  let originalKeys := aToDKeys twoRoutePlan twoRouteFinished.batch.log
  let extendedKeys := aToDKeys twoRoutePlan irrelevantExtensionFinished.batch.log
  unless originalKeys.card == 2 && originalKeys == extendedKeys do
    throw (IO.userError "Unrelated graph facts manufactured a new logical inference key")
  unless aToDKeys twoRoutePlan reorderedDuplicateFinished.batch.log == originalKeys &&
      aToDKeys twoRoutePlan canonicalSourceFinished.batch.log == originalKeys do
    throw (IO.userError "Equivalent set presentations manufactured logical inference keys")
  unless logicalFacts twoRoutePlan reorderedDuplicateFinished.batch.log == {edge "A" "D"} do
    throw (IO.userError "Equivalent graph presentation changed inferred facts")
  unless (sourceSensitiveAToDKeys twoRoutePlan twoRouteFinished.batch.log ∪
      sourceSensitiveAToDKeys twoRoutePlan irrelevantExtensionFinished.batch.log).card == 4 do
    throw (IO.userError "Source-payload identity negative no longer separates the two presentations")
  IO.println "GraphLogicalIdentityControls: same 2 A-to-D keys under unrelated fact extension, reordered duplicates and canonical presentation; distinct intermediate remains distinct"
  IO.println s!"AuthoredGraphObservationControls: {raw.length} committed allocations, {(successorStates reachabilityPlan [] (.base "Graph") finished.batch.log).card} fact-state, {(allocationBag reachabilityPlan [] (.base "Graph") finished.batch.log).card} occurrence derivations; cyclic packets {cyclic.length}"
  IO.println s!"KnowledgeGraphObservationControls: {intermediates.length} independent routes, {routes.length} retained allocations -> {(inferredFacts twoRoutePlan twoRouteFinished.batch.log).card} inferred fact / {(inferredBag twoRoutePlan twoRouteFinished.batch.log).card} occurrence derivations"
  IO.println "LogicalKnowledgeGraphControls: 8/16 allocation/validation packets -> 2 logical routes -> 1 inferred fact; consume/retain and duplicate validation do not multiply routes"

#eval check

#print axioms logicalKey_ignores_allocation
#print axioms logicalKey_ignores_source_payload
#print axioms logicalKey_canonical_source_presentation
#print axioms logicalKey_ignores_query_validation
#print axioms logicalKey_erases_query_in_history
#print axioms logicalKey_erases_freshness_in_history
#print axioms logicalKey_nonrest_ext
#print axioms intermediate_distinguishes_route
#print axioms logical_key_determines_fact
#print axioms logicalBag_ordered_presentation
#print axioms logicalFacts_ordered_presentation
#print axioms retained_logical_edge_licensed

end GraphControls

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted

private def nodeLabels : List String := ["A", "B", "C", "D"]
private def nodeCarrier : List Pattern := nodeLabels.map token

def factCarrier : Finset Pattern :=
  (nodeCarrier.flatMap fun first => nodeCarrier.map fun last => .apply "Edge" [first,last]).toFinset

/-- Canonical fact sets over the actual finite Node grammar. The powerset is
used as a finite mathematical carrier, not as a replacement executor. -/
noncomputable def canonicalGraphCarrier : Finset Pattern :=
  factCarrier.powerset.image fun facts => canon (graph facts.toList)

/-- The generic explorer preserves an arbitrary raw initial presentation.
Its subsequent search targets are canonical members of the finite carrier. -/
noncomputable def explorerCarrier (rawSource : Pattern) : List Pattern :=
  rawSource :: canonicalGraphCarrier.toList

private theorem finite_grammar_checked :
    twoRouteLanguage.terms.all (fun rule =>
      (rule.category != "Node" || (rule.params.isEmpty && nodeLabels.contains rule.label)) &&
      (rule.category != "Fact" || (rule.label == "Edge" &&
        rule.params == [.simple "source" (.base "Node"), .simple "target" (.base "Node")])) &&
      (rule.category != "Graph" ||
        rule.bareParams == [.simple "facts" (.collection .hashSet (.base "Fact"))])) = true := by cbv

private theorem node_declaration {rule : GrammarRule} (member : rule ∈ twoRouteLanguage.terms)
    (category : rule.category = "Node") : rule.params = [] ∧ rule.label ∈ nodeLabels := by
  have checked := List.all_eq_true.mp finite_grammar_checked rule member
  simp only [Bool.and_eq_true] at checked
  have node := checked.1.1
  rw [category] at node
  simpa only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff,
    List.contains_iff_mem] using node

private theorem fact_declaration {rule : GrammarRule} (member : rule ∈ twoRouteLanguage.terms)
    (category : rule.category = "Fact") : rule.label = "Edge" ∧
      rule.params = [.simple "source" (.base "Node"), .simple "target" (.base "Node")] := by
  have checked := List.all_eq_true.mp finite_grammar_checked rule member
  simp only [Bool.and_eq_true] at checked
  have fact := checked.1.2
  rw [category] at fact
  simpa only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] using fact

private theorem graph_declaration {rule : GrammarRule} (member : rule ∈ twoRouteLanguage.terms)
    (category : rule.category = "Graph") :
      rule.bareParams = [.simple "facts" (.collection .hashSet (.base "Fact"))] := by
  have checked := List.all_eq_true.mp finite_grammar_checked rule member
  simp only [Bool.and_eq_true] at checked
  have graph := checked.2
  rw [category] at graph
  simpa only [bne_self_eq_false, Bool.false_or, beq_iff_eq] using graph

private theorem node_carrier_of_typed {pattern : Pattern} {type : TypeExpr}
    (typed : HasType twoRouteLanguage FreeTypeContext.empty [] pattern type)
    (category : type = .base "Node") (object : isObjectPattern pattern = true) : pattern ∈ nodeCarrier := by
  cases typed with
  | bvar found => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | @constructor _ rule arguments declared ordinary children =>
      have cat : rule.category = "Node" := TypeExpr.base.inj category
      obtain ⟨params, label⟩ := node_declaration declared cat
      rw [params] at children
      cases children
      exact List.mem_map.mpr ⟨rule.label,label,rfl⟩
  | lambda | multiLambda | collection => cases category
  | subst => simp only [isObjectPattern, Bool.false_eq_true] at object
  | @collectionConstructor _ rule parameter kind elements rest elementType declared shape children =>
      have cat : rule.category = "Node" := TypeExpr.base.inj category
      have params := (node_declaration declared cat).1
      simp only [GrammarRule.bareParams, params] at shape
      split at shape <;> cases shape

private theorem fact_carrier_of_typed {pattern : Pattern} {type : TypeExpr}
    (typed : HasType twoRouteLanguage FreeTypeContext.empty [] pattern type)
    (category : type = .base "Fact") (object : isObjectPattern pattern = true) : pattern ∈ factCarrier := by
  cases typed with
  | bvar found => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | @constructor _ rule arguments declared ordinary children =>
      have cat : rule.category = "Fact" := TypeExpr.base.inj category
      obtain ⟨label, params⟩ := fact_declaration declared cat
      rw [params] at children
      cases children with
      | cons firstRepresentation firstExpected firstTyped tail =>
        cases tail with
        | cons lastRepresentation lastExpected lastTyped tail =>
          cases tail
          simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at object
          have firstNode := node_carrier_of_typed firstTyped (Option.some.inj firstExpected).symm object.1
          have lastNode := node_carrier_of_typed lastTyped (Option.some.inj lastExpected).symm object.2
          rw [label]
          apply List.mem_toFinset.mpr
          exact List.mem_flatMap.mpr ⟨_, firstNode, List.mem_map.mpr ⟨_,lastNode,rfl⟩⟩
  | lambda | multiLambda | collection => cases category
  | subst => simp only [isObjectPattern, Bool.false_eq_true] at object
  | @collectionConstructor _ rule parameter kind elements rest elementType declared shape children =>
      have cat : rule.category = "Fact" := TypeExpr.base.inj category
      have params := (fact_declaration declared cat).2
      simp only [GrammarRule.bareParams, params] at shape
      split at shape <;> cases shape

private theorem fact_elements_carrier {elements : List Pattern}
    (typed : ElementsHaveType twoRouteLanguage FreeTypeContext.empty [] elements (.base "Fact"))
    (objects : isObjectPatternList elements = true) : ∀ fact ∈ elements, fact ∈ factCarrier := by
  cases typed with
  | nil => intro fact member; cases member
  | cons head tail =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      intro fact member
      rcases List.mem_cons.mp member with rfl | later
      · exact fact_carrier_of_typed head rfl objects.1
      · exact fact_elements_carrier tail objects.2 fact later
termination_by elements.length

/-- Object typing in the actual authored Graph grammar bounds every canonical
state by a finite powerset. No search status or matching equivalence is input. -/
theorem canonical_graph_mem_carrier {pattern : Pattern} {type : TypeExpr}
    (typed : HasType twoRouteLanguage FreeTypeContext.empty [] pattern type)
    (category : type = .base "Graph") (object : isObjectPattern pattern = true) : canon pattern ∈ canonicalGraphCarrier := by
  cases typed with
  | bvar found => simp at found
  | fvar found => simp [FreeTypeContext.empty] at found
  | @constructor _ rule arguments declared ordinary children =>
      have shape := graph_declaration declared (TypeExpr.base.inj category)
      exact False.elim (ordinary ⟨"facts",.hashSet,.base "Fact",shape⟩)
  | lambda | multiLambda | collection => cases category
  | subst => simp only [isObjectPattern, Bool.false_eq_true] at object
  | @collectionConstructor _ rule parameter kind elements rest elementType declared shape children =>
      have actual := graph_declaration declared (TypeExpr.base.inj category)
      rw [actual] at shape
      cases shape
      have parts : rest.isNone = true ∧ isObjectPatternList elements = true :=
        Bool.and_eq_true_iff.mp object
      have tail : rest = none := Option.isNone_iff_eq_none.mp parts.1
      subst rest
      have members := fact_elements_carrier children parts.2
      apply Finset.mem_image.mpr
      refine ⟨elements.toFinset, Finset.mem_powerset.mpr ?_, ?_⟩
      · intro fact member
        exact members fact (List.mem_toFinset.mp member)
      · exact canon_collection_of_presents .hashSet none (by intro fact; simp)

theorem two_route_canonical_seed_in_carrier : canon twoRouteSource ∈ canonicalGraphCarrier := by
  apply canonical_graph_mem_carrier
  · exact (checkOpenPatternWellSorted_sound (language := twoRouteLanguage)
      (free := FreeTypeContext.empty) (bound := []) (expected := .base "Graph")
      (pattern := twoRouteSource) (by cbv)).1
  · rfl
  · rfl

/-- Every actually committed successor is in the finite carrier. This uses
retained-packet validity and actual target typing, not a matching oracle. -/
theorem search_target_in_carrier_of_signature (plan : GeneralExecutionAdmission.Plan)
    (free : plan.snapshot.free = FreeTypeContext.empty)
    (included : plan.snapshot.language.terms ⊆ twoRouteLanguage.terms) (source : Pattern) (work : Nat) (receipt : GeneralRuleJobs.Receipt)
    (published : receipt ∈ (CollectionOccurrenceSearch.search plan [] (.base "Graph") 0).publication
      ((CollectionOccurrenceSearch.search plan [] (.base "Graph") 0).run source work)) :
    canon receipt.target ∈ canonicalGraphCarrier := by
  let executed := CollectionOccurrenceMachine.run 0 work
    (CollectionOccurrenceMachine.begin plan [] (.base "Graph") (canon source))
  have balanced := (CollectionOccurrenceMachine.run_invariant 0 work
    (CollectionOccurrenceMachine.begin_invariant (plan := plan) (bound := [])
      (expected := .base "Graph") (source := canon source) 0)).1
  change receipt ∈ executed.batch.log.filterMap (fun packet => packet.finish? plan [] (.base "Graph")) at published
  obtain ⟨packet, logged, finished⟩ := List.mem_filterMap.mp published
  obtain ⟨frame, present, inFrame⟩ := List.mem_flatMap.mp (balanced.subset logged)
  have valid := CollectionCommittedObservation.frame_receipt_valid frame inFrame finished
  have sorted := (GeneralPlanEnvironment.typing_iff plan [] (.base "Graph") receipt.target).mp
    valid.2.2.2.2
  rw [free] at sorted
  exact canonical_graph_mem_carrier (HasType.of_terms_subset included sorted.1) rfl sorted.2.2.1


theorem search_target_in_carrier (source : Pattern) (work : Nat) (receipt : GeneralRuleJobs.Receipt)
    (published : receipt ∈ (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0).publication
      ((CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0).run source work)) :
    canon receipt.target ∈ canonicalGraphCarrier := by
  exact search_target_in_carrier_of_signature twoRoutePlan rfl (fun _ member => member)
    source work receipt published

/-- The actual generic exploration stays in the original raw seed plus the
finite canonical successor carrier. No settlement hypothesis is supplied. -/
theorem explored_graph_in_carrier_of_signature (plan : GeneralExecutionAdmission.Plan)
    (free : plan.snapshot.free = FreeTypeContext.empty)
    (included : plan.snapshot.language.terms ⊆ twoRouteLanguage.terms) (source : Pattern) : ∀ work,
    ∀ node ∈ (Complete.Explore.explore
      (CollectionOccurrenceSearch.search plan [] (.base "Graph") 0) source work).nodes,
      node.state ∈ explorerCarrier source := by
  let S := CollectionOccurrenceSearch.search plan [] (.base "Graph") 0
  have lawful := CollectionOccurrenceSearch.search_lawful plan [] (.base "Graph") 0
  intro work
  induction work with
  | zero =>
      intro node member
      simp only [Complete.Explore.explore, Complete.Explore.begin, List.mem_singleton] at member
      subst node
      exact List.mem_cons_self
  | succ work ih =>
      intro node member
      change node ∈ (Complete.Explore.step S (Complete.Explore.explore S source work)).nodes at member
      simp only [Complete.Explore.step, List.mem_append] at member
      rcases member with kept | fresh
      · obtain ⟨pair, pairInside, rfl⟩ := List.mem_map.mp kept
        obtain ⟨old, oldInside, rfl⟩ := List.mem_map.mp pairInside
        exact ih old oldInside
      · have generated := Complete.Explore.fresh_subset _ _ node fresh
        obtain ⟨pair, pairInside, generated⟩ := List.mem_flatMap.mp generated
        obtain ⟨old, oldInside, rfl⟩ := List.mem_map.mp pairInside
        obtain ⟨receipt, released, rfl⟩ := List.mem_map.mp generated
        have published := List.mem_of_mem_drop released
        have good := Complete.Explore.explore_good lawful source work
        rw [good.run old oldInside, lawful.resume_run] at published
        have finite := search_target_in_carrier_of_signature plan free included old.state _ receipt published
        exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr finite)


theorem explored_graph_in_carrier (source : Pattern) : ∀ work,
    ∀ node ∈ (Complete.Explore.explore
      (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      node.state ∈ explorerCarrier source := by
  exact explored_graph_in_carrier_of_signature twoRoutePlan rfl (fun _ member => member) source

#print axioms search_target_in_carrier_of_signature
#print axioms explored_graph_in_carrier_of_signature
#print axioms search_target_in_carrier
#print axioms explored_graph_in_carrier

#print axioms canonical_graph_mem_carrier
#print axioms two_route_canonical_seed_in_carrier

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem transitive_projection_checked :
    Match.binderFree actualRule.right = true ∧ checkZeroDependencies actualSpec = true ∧
    SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment twoRoutePlan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true ∧
    namesAvailable actualRule.left.freeFvarNames actualRule.right.freeFvarNames = true ∧
    namesAvailable (restCaptureNames actualRule.left) (restCaptureNames actualRule.right) = true := by cbv

/-- The actual Transitive right side projects from its real captured values.
Typed captures are supplied only by the existing post-match check; all name,
rest, schema and zero-dependency obligations are derived here. -/
theorem transitive_projection_total_in (request : RecursiveCollectionContinuation.Request)
    (selected : request.rule = actualRule) (specified : request.spec = actualSpec)
    (roleChecked : SchemaTyping.checkSchemaType [] request.environment.language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    (typed : TypedAssignment request.environment request.context request.prepared.ordinary.assignment) :
    ∃ target, reductWith? (ScopedReflectiveExecution.binderOperation
      request.environment.reflection request.rule) request.rule request.spec request.bound.length
      request.prepared.ordinary.assignment = some target := by
  obtain ⟨shape,zero,_,names,rests⟩ := transitive_projection_checked
  have actualShape : Match.binderFree request.rule.right = true := by simpa only [selected] using shape
  have actualZero : checkZeroDependencies request.spec = true := by simpa only [specified] using zero
  have actualRole : Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType request.environment.language
      (FreeTypeContext.ofList request.rule.typeContext) [] request.rule.right (.base "Graph") := by
    rw [selected]
    exact binderFree_schema_restAware (domains := []) shape roleChecked
  have actualNames : namesAvailable request.rule.left.freeFvarNames request.rule.right.freeFvarNames = true := by
    simpa only [selected] using names
  have actualRests : namesAvailable (restCaptureNames request.rule.left) (restCaptureNames request.rule.right) = true := by
    simpa only [selected] using rests
  have matched := request.matching.matching.matching
  have canonical := matching_canonicalValues (by
    intro capture value found
    simp [ScopedRuleMatching.lookup] at found) request.sourceTyped.2.1 matched
  have bound := matching_bound_names matched
  have finite := matching_finite_restCaptures matched
  obtain ⟨target,read,_⟩ := binderFree_instantiation_total_open
    (operation := ScopedReflectiveExecution.binderOperation request.environment.reflection request.rule)
    request.admitted actualZero typed canonical actualShape (NameCoherent.right request.rule) actualRole
    (fun capture member => bound capture (namesAvailable_sound _ _ actualNames capture member))
    (fun capture member => finite capture (namesAvailable_sound _ _ actualRests capture member))
  exact ⟨target,read⟩


theorem transitive_projection_total (request : RecursiveCollectionContinuation.Request)
    (environment : request.environment = GeneralPlanEnvironment.environment twoRoutePlan)
    (selected : request.rule = actualRule) (specified : request.spec = actualSpec)
    (typed : TypedAssignment request.environment request.context request.prepared.ordinary.assignment) :
    ∃ target, reductWith? (ScopedReflectiveExecution.binderOperation
      request.environment.reflection request.rule) request.rule request.spec request.bound.length
      request.prepared.ordinary.assignment = some target := by
  apply transitive_projection_total_in request selected specified _ typed
  simpa only [environment] using transitive_projection_checked.2.2.1

#print axioms transitive_projection_total_in
#print axioms transitive_projection_total

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open CollectionOccurrenceBatch
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner

private theorem allocation_transitive_fields (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    {source : Pattern} (allocation : Allocation plan [] (.base "Graph") source) :
    allocation.request.environment = GeneralPlanEnvironment.environment plan ∧
      allocation.request.rule = actualRule ∧ allocation.request.spec = actualSpec := by
  have member := List.fst_mem_of_mem_zipIdx allocation.licensed.1.1
  rw [singleton, List.mem_singleton] at member
  change allocation.job.origin.declaration = reachabilityPlan.rules[0]'(by cbv) at member
  obtain ⟨_,_,_,_,_,selected,specified,_⟩ := allocation.request_fields
  refine ⟨allocation.request_origin.1,?_,?_⟩
  · rw [selected,member]
    rfl
  · rw [specified,member]
    rfl

private theorem initial_transitive_complete (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    {source : Pattern} (allocation : Allocation plan [] (.base "Graph") source) :
    (Frame.run 3 (Frame.initial allocation)).state.agenda = [] ∧
      (Frame.run 3 (Frame.initial allocation)).state.unresolved = [] := by
  obtain ⟨environment,selected,specified⟩ := allocation_transitive_fields plan singleton allocation
  have empty : allocation.request.rule.premises = [] := by rw [selected]; cbv
  apply RecursiveCollectionContinuation.unconditional_complete allocation.request empty
  apply transitive_projection_total_in allocation.request selected specified
  simpa only [environment] using role

private theorem initialized_transitive_clean (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    {source : Pattern} (frame : Frame plan [] (.base "Graph") source)
    (initialized : CollectionOccurrenceMachine.Initialized frame) : frame.state.unresolved = [] := by
  obtain ⟨elapsed,started⟩ := initialized
  have finished := initial_transitive_complete plan singleton role frame.allocation
  have shifted : Frame.run 3 frame = Frame.run elapsed (Frame.run 3 (Frame.initial frame.allocation)) := by
    calc
      _ = Frame.run 3 (Frame.run elapsed (Frame.initial frame.allocation)) := congrArg (Frame.run 3) started
      _ = Frame.run (elapsed + 3) (Frame.initial frame.allocation) := (Frame.run_add ..).symm
      _ = _ := by rw [Nat.add_comm elapsed 3, Frame.run_add]
  have initialDone :
      (RecursiveCollectionContinuation.run frame.allocation.request 3
        (RecursiveCollectionContinuation.start frame.allocation.request)).agenda = [] ∧
      (RecursiveCollectionContinuation.run frame.allocation.request 3
        (RecursiveCollectionContinuation.start frame.allocation.request)).unresolved = [] := finished
  have laterClear : (Frame.run 3 frame).state.unresolved = [] := by
    rw [shifted]
    change (Scheduler.run (StructuralDescent.Scheduled.expand frame.allocation.request.environment
      frame.allocation.request.goal) elapsed (RecursiveCollectionContinuation.run frame.allocation.request 3
        (RecursiveCollectionContinuation.start frame.allocation.request))).unresolved = []
    rw [Scheduler.run_idle _ elapsed _ initialDone.1]
    exact initialDone.2
  obtain ⟨suffix,joined⟩ := Scheduler.run_obligations_prefix
    (StructuralDescent.Scheduled.expand frame.allocation.request.environment frame.allocation.request.goal) 3 frame.state
  have empty : frame.state.unresolved ++ suffix = [] := by
    rw [← joined]
    exact laterClear
  exact (List.append_eq_nil_iff.mp empty).1

/-- Genuine local completion is derived from real initialized allocations,
not supplied as a settled-outcome premise. Every original frame is retained. -/
theorem transitive_search_eventually_complete (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    (source : Pattern) :
    ∃ work, (CollectionOccurrenceSearch.search plan [] (.base "Graph") 0).status
      ((CollectionOccurrenceSearch.search plan [] (.base "Graph") 0).run source work) = .complete := by
  obtain ⟨work,matching,agendas⟩ := CollectionOccurrenceSearch.search_eventually_drained plan [] (.base "Graph") 0 source
  let executed := CollectionOccurrenceMachine.run 0 work
    (CollectionOccurrenceMachine.begin plan [] (.base "Graph") (canon source))
  have clean : ∀ frame ∈ executed.batch.frames, frame.state.unresolved = [] := by
    intro frame member
    exact initialized_transitive_clean plan singleton role frame
      (CollectionOccurrenceMachine.run_initialized 0 work frame member)
  have matchingBool : executed.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) = true :=
    List.all_eq_true.mpr matching
  have agendasBool : executed.batch.frames.all (fun frame => frame.state.agenda.isEmpty) = true :=
    List.all_eq_true.mpr (fun frame member => by simp only [agendas frame member, List.isEmpty_nil])
  have cleanBool : executed.batch.frames.all (fun frame => frame.state.unresolved.isEmpty) = true :=
    List.all_eq_true.mpr (fun frame member => by simp only [clean frame member, List.isEmpty_nil])
  refine ⟨work,?_⟩
  change CollectionOccurrenceSearch.status ⟨source,executed⟩ = .complete
  unfold CollectionOccurrenceSearch.status CollectionOccurrenceSearch.statusWith
  rw [matchingBool,agendasBool,cleanBool]
  rfl

/-- The actual receipt-bearing explorer settles for a finite Graph signature
and the authored Transitive declaration. Its full packets remain available. -/
theorem transitive_explorer_eventually_settled (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    (free : plan.snapshot.free = FreeTypeContext.empty)
    (included : plan.snapshot.language.terms ⊆ twoRouteLanguage.terms)
    (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.search plan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search plan [] (.base "Graph") 0) source work) = true := by
  apply Complete.Settled.eventually_settled_of_finite_carrier
    (CollectionOccurrenceSearch.search_lawful plan [] (.base "Graph") 0)
    (CollectionOccurrenceSearch.search_stable plan [] (.base "Graph") 0)
    source (explorerCarrier source) (explored_graph_in_carrier_of_signature plan free included source)
  intro state _
  exact transitive_search_eventually_complete plan singleton role state

private theorem reachability_completion_metadata :
    reachabilityPlan.rules = [reachabilityPlan.rules[0]'(by cbv)] ∧
    SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment reachabilityPlan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true ∧
    reachabilityPlan.snapshot.free = FreeTypeContext.empty ∧
    reachabilityPlan.snapshot.language.terms ⊆ twoRouteLanguage.terms := by
  refine ⟨by cbv,by cbv,rfl,?_⟩
  intro declaration member
  exact List.mem_append_left _ member

private theorem two_route_completion_metadata :
    twoRoutePlan.rules = [reachabilityPlan.rules[0]'(by cbv)] ∧
    SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment twoRoutePlan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true ∧
    twoRoutePlan.snapshot.free = FreeTypeContext.empty ∧
    twoRoutePlan.snapshot.language.terms ⊆ twoRouteLanguage.terms := by
  exact ⟨by cbv,by cbv,rfl,fun _ member => member⟩

theorem reachability_eventually_settled (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0) source work) = true := by
  obtain ⟨singleton,role,free,included⟩ := reachability_completion_metadata
  exact transitive_explorer_eventually_settled reachabilityPlan singleton role free included source

theorem two_route_eventually_settled (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work) = true := by
  obtain ⟨singleton,role,free,included⟩ := two_route_completion_metadata
  exact transitive_explorer_eventually_settled twoRoutePlan singleton role free included source

#print axioms transitive_search_eventually_complete
#print axioms transitive_explorer_eventually_settled
#print axioms reachability_eventually_settled
#print axioms two_route_eventually_settled

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner

private theorem reachability_coverage_checked :
    CollectionOccurrenceMachine.checkGuardFragment reachabilityPlan = true ∧
    reachabilityPlan.equations = [] ∧ Complete.Normalized.laws reachabilityPlan = [] ∧
    Complete.Normalized.extrusions reachabilityPlan = [] := by cbv

private theorem two_route_coverage_checked :
    CollectionOccurrenceMachine.checkGuardFragment twoRoutePlan = true ∧
    twoRoutePlan.equations = [] ∧ Complete.Normalized.laws twoRoutePlan = [] ∧
    Complete.Normalized.extrusions twoRoutePlan = [] := by cbv

/-- The actual finite graph reaches an outgoing closed receipt graph of the
presented source relation. Incoming coverage is not part of this statement. -/
theorem reachability_eventually_outgoing_closed (source : Pattern) :
    ∃ work,
      Complete.Settled.settled (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
        (Complete.Explore.explore (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
          source work) = true ∧
      ∀ node ∈ (Complete.Explore.explore
          (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0) source work).nodes,
        ∀ target, (Complete.Presented.gslt reachabilityPlan [] (.base "Graph")).Step node.state target →
          ∃ receipt target', (node.state, receipt, target') ∈ Complete.Graph.edges
            (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
            (Complete.Explore.explore (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
              source work) ∧ Same target target' := by
  obtain ⟨work, done⟩ := reachability_eventually_settled source
  obtain ⟨guards, equations, laws, extrusions⟩ := reachability_coverage_checked
  exact ⟨work, done, CollectionOccurrenceSearch.settled_edges_cover_steps guards
    equations laws extrusions 0 source work done⟩

theorem two_route_eventually_outgoing_closed (source : Pattern) :
    ∃ work,
      Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
          source work) = true ∧
      ∀ node ∈ (Complete.Explore.explore
          (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
        ∀ target, (Complete.Presented.gslt twoRoutePlan [] (.base "Graph")).Step node.state target →
          ∃ receipt target', (node.state, receipt, target') ∈ Complete.Graph.edges
            (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
            (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
              source work) ∧ Same target target' := by
  obtain ⟨work, done⟩ := two_route_eventually_settled source
  obtain ⟨guards, equations, laws, extrusions⟩ := two_route_coverage_checked
  exact ⟨work, done, CollectionOccurrenceSearch.settled_edges_cover_steps guards
    equations laws extrusions 0 source work done⟩

def selfLoop : Pattern := graph [edge "A" "A"]

private def selfLoopPresentation : Pattern := graph [edge "A" "A", edge "A" "A"]

private def selfLoopResult : Pattern := graph [edge "A" "A", edge "A" "A", edge "A" "A"]

private def selfLoopCaptured : Assignment :=
  (matchAt actualRule actualSpec 0 .left [] 0 [] actualRule.left selfLoopPresentation).head!

private def selfLoopJob : GeneralRuleJobs.Job :=
  ⟨0, reachabilityPlan.rules[0]'(by cbv),
    GeneralTypedSites.SiteData.here [] (.base "Graph") selfLoopPresentation⟩

private def selfLoopReceipt (trace : List GeneralScopedMatchMachine.BagChoice) : GeneralRuleJobs.Receipt :=
  ⟨selfLoopJob, trace, selfLoopCaptured, selfLoopCaptured, [], selfLoopResult, selfLoopResult⟩

private theorem selfLoop_matching :
    selfLoopCaptured ∈ matchAt actualRule actualSpec 0 .left [] 0 [] actualRule.left selfLoopPresentation := by
  cbv
  exact .head _

private theorem selfLoop_licensed : selfLoopJob.Valid reachabilityPlan [] (.base "Graph") selfLoopPresentation := by
  refine ⟨by cbv; exact .head _, .here (by rfl) (by rfl) ?_⟩
  exact (checkOpenPatternWellSorted_sound (language := (GeneralPlanEnvironment.environment reachabilityPlan).language)
    (free := reachabilityPlan.snapshot.free) (bound := []) (expected := .base "Graph")
    (pattern := selfLoopPresentation) (by cbv)).1

private theorem selfLoop_finished (trace : List GeneralScopedMatchMachine.BagChoice) :
    GeneralRuleJobs.finish? reachabilityPlan [] (.base "Graph") selfLoopJob trace selfLoopCaptured
      selfLoopCaptured [] = some (selfLoopReceipt trace) := by cbv

/-- A singleton set supports the real transitivity rule through a duplicate
presentation. The receipt is checked by the existing rule-job finisher. -/
theorem selfLoop_presented_step :
    (Complete.Presented.gslt reachabilityPlan [] (.base "Graph")).Step selfLoop selfLoop := by
  obtain ⟨trace, matching⟩ := GeneralScopedMatchMachine.matches_trace
    (GeneralScopedMatch.matchAt_sound selfLoop_matching)
  have typedMatch : GeneralScopedMatchMachine.TracedMatches
      selfLoopJob.declaration.rule selfLoopJob.declaration.binding.spec
      selfLoopJob.site.focusBound.length .left [] 0 [] selfLoopJob.declaration.rule.left
      selfLoopJob.site.focus trace selfLoopCaptured := matching
  have premises : PremisesHold (GeneralPlanEnvironment.environment reachabilityPlan) selfLoopJob.context
      selfLoopJob.declaration.rule.premises selfLoopCaptured selfLoopCaptured [] := by
    have empty : selfLoopJob.declaration.rule.premises = [] := by cbv
    rw [empty]
    exact .nil
  have valid := GeneralRuleJobs.finish_sound selfLoop_licensed typedMatch premises (selfLoop_finished trace)
  refine ⟨selfLoopPresentation, selfLoopReceipt trace, ?_, valid, ?_⟩
  · apply CollectionOccurrenceHandoff.same_model_equiv
    change canon selfLoop = canon selfLoopPresentation
    cbv
  · apply CollectionOccurrenceHandoff.same_model_equiv
    change canon selfLoopResult = canon selfLoop
    cbv

/-- The repeated event is an actual published receipt of the existing search,
not a fabricated transition or an administrative normalization witness. -/
theorem selfLoop_has_published_return :
    ∃ work receipt, receipt ∈ (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0).publication
      ((CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0).run selfLoop work) ∧
      (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0).target receipt = selfLoop := by
  obtain ⟨guards, equations, laws, extrusions⟩ := reachability_coverage_checked
  obtain ⟨work, receipt, published, same⟩ :=
    (CollectionOccurrenceSearch.presented_iff_published guards equations laws extrusions 0).mp selfLoop_presented_step
  refine ⟨work, receipt, published, ?_⟩
  change canon receipt.target = selfLoop
  have canonical : canon selfLoop = selfLoop := by cbv
  exact Eq.trans (Eq.symm same) canonical

/-- Finite outgoing closure and unbounded unfolded receipt histories coexist
in the actual authored graph consumer. Their completion meanings differ. -/
theorem selfLoop_closed_graph_unbounded_histories :
    (∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
        selfLoop work) = true) ∧
    (∀ bound, ∃ states receipts,
      History (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0) states receipts ∧
        bound < receipts.length) := by
  refine ⟨reachability_eventually_settled selfLoop, ?_⟩
  obtain ⟨work, receipt, published, returns⟩ := selfLoop_has_published_return
  have valid := (CollectionOccurrenceSearch.search_lawful reachabilityPlan [] (.base "Graph") 0).sound
    selfLoop work receipt published
  intro bound
  exact Complete.Graph.self_return_histories_unbounded (CollectionOccurrenceSearch.search reachabilityPlan [] (.base "Graph") 0)
    selfLoop receipt valid returns bound

#print axioms reachability_eventually_outgoing_closed
#print axioms two_route_eventually_outgoing_closed
#print axioms selfLoop_presented_step
#print axioms selfLoop_has_published_return
#print axioms selfLoop_closed_graph_unbounded_histories

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags CollectionCommittedObservation

/-- The actual two-route exploration eventually keeps exactly the same full
packet account under further scheduling. Its declared logical key, bag and
fact projections consequently stay fixed. Source-key coverage and unfolded
logical derivation enumeration remain separate obligations. -/
theorem two_route_committed_account_settles (source : Pattern) :
    ∃ work,
      let selected := CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0
      let closed := Complete.Explore.explore selected source work
      Complete.Settled.settled selected closed = true ∧
      ∀ extra,
        let earlier := closed.nodes.flatMap (fun node => CollectionOccurrenceSearch.publicationWithPackets node.run)
        let later := (Nat.iterate (Complete.Explore.step selected) extra closed).nodes.flatMap
          (fun node => CollectionOccurrenceSearch.publicationWithPackets node.run)
        later = earlier ∧
          committedKeys logicalKey later = committedKeys logicalKey earlier ∧
          (committedKeys logicalKey later).val.filterMap logicalEdge? =
            (committedKeys logicalKey earlier).val.filterMap logicalEdge? ∧
          ((committedKeys logicalKey later).val.filterMap logicalEdge?).toFinset =
            ((committedKeys logicalKey earlier).val.filterMap logicalEdge?).toFinset := by
  obtain ⟨work, done⟩ := two_route_eventually_settled source
  refine ⟨work, done, ?_⟩
  intro extra
  have same := CollectionOccurrenceSearch.settled_committed_iterate 0 extra
    (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
      source work) done
  dsimp only
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms two_route_committed_account_settles

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBags RuleBinding GeneralPremise CollectionOccurrenceBatch CollectionCommittedObservation
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The existing graph identity read on a typed source-receipt witness.
The packet projection below proves coverage of this same declared identity. -/
def sourceLogicalKey {Choice : Type} (receipt : GeneralRuleJobs.Receipt Choice) : LogicalKey Choice :=
  ⟨receipt.job.ordinal, receipt.job.declaration.declarationIndex, logicalSiteShape receipt.job.site,
    (ScopedRuleMatching.lookup receipt.completed "x").map canonValue,
    (ScopedRuleMatching.lookup receipt.completed "y").map canonValue,
    (ScopedRuleMatching.lookup receipt.completed "z").map canonValue,
    validationHistoryReadout receipt.premiseHistory .factValidation⟩

private theorem root_licensed_logical_shape {language : LanguageDef} {free : FreeTypeContext}
    {source : Pattern} {site : GeneralTypedSites.SiteData}
    (licensed : Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed
      language free .rootOnly [] (.base "Graph") source site) :
    logicalSiteShape site = ⟨[], [], .base "Graph", []⟩ := by
  have member := GeneralTypedSites.generate_complete licensed
  rw [GeneralTypedSites.generate_rootOnly] at member
  split at member
  · cases List.mem_singleton.mp member
    rfl
  · cases member

private theorem canonical_completed_lookup (completed : ScopedRuleMatching.Assignment)
    (captureName : String) :
    (ScopedRuleMatching.lookup (canonAssignment completed) captureName).map canonValue =
      (ScopedRuleMatching.lookup completed captureName).map canonValue := by
  rw [lookup_canonAssignment]
  cases found : ScopedRuleMatching.lookup completed captureName with
  | none => rfl
  | some value => simp only [Option.map_some, canonValue, canon_idempotent]

/-- Each source Transitive binding tuple reaches a real retained pair with
the same declared graph key. Root typing paths come from the actual licensed
generator; no nested address transport or whole-firing equivalence is assumed. -/
theorem two_route_source_key_eventually_published {source : Pattern} {original : GeneralRuleJobs.Receipt}
    (valid : original.Valid twoRoutePlan [] (.base "Graph") source) :
    ∃ work pair, pair ∈ CollectionOccurrenceSearch.publicationWithPackets
      ((CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0).run source work) ∧
      logicalKey pair = sourceLogicalKey original := by
  obtain ⟨checked, _, _, _⟩ := two_route_coverage_checked
  have fragment := CollectionOccurrenceMachine.checkGuardFragment_sound checked original.job.declaration
    (List.fst_mem_of_mem_zipIdx valid.1.1) original.job.site.focusBound original.job.ordinal
  have bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ 0 := by
    rw [valid.2.1.collection_guards_history_depth (GeneralRuleJobs.Job.selected_rule valid.1)
      (GeneralRuleJobs.Job.selected_specification valid.1) fragment.2.1]
  obtain ⟨work, packet, receipt, logged, finished, licensed, _, _, completed,
    history, ordinal, declaration, _, _, _⟩ :=
    CollectionOccurrenceMachine.receipt_eventually_published_with_bindings
      valid fragment.2.2 fragment.1 fragment.2.1 0 bounded
  have permissions : twoRoutePlan.permissions.sites = .rootOnly := rfl
  have packetLicense := licensed.1.2
  have sourceLicense := valid.1.2
  rw [permissions] at packetLicense sourceLicense
  have shape : logicalSiteShape packet.job.origin.site = logicalSiteShape original.job.site :=
    Eq.trans (root_licensed_logical_shape packetLicense)
      (Eq.symm (root_licensed_logical_shape sourceLicense))
  refine ⟨work, (packet, receipt), ?_, ?_⟩
  · change (packet, receipt) ∈ retained twoRoutePlan [] (.base "Graph")
      (CollectionOccurrenceMachine.run 0 work
        (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") (canon source))).batch.log
    apply List.mem_filterMap.mpr
    refine ⟨packet, logged, ?_⟩
    simp only [commit?, finished, Option.map_some]
  · simp only [logicalKey, sourceLogicalKey, LogicalKey.mk.injEq]
    refine ⟨ordinal, congrArg (fun selected => selected.declarationIndex) declaration,
      shape, ?_, ?_, ?_, ?_⟩
    · rw [completed]
      exact canonical_completed_lookup original.completed "x"
    · rw [completed]
      exact canonical_completed_lookup original.completed "y"
    · rw [completed]
      exact canonical_completed_lookup original.completed "z"
    · rw [history]

#print axioms two_route_source_key_eventually_published

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBags CollectionCommittedObservation

/-- A settled actual graph contains every declared source-receipt key from
every collection-equivalent representative of an explored state. In
particular, a singleton set may use its duplicate matching presentation. -/
theorem two_route_settled_source_key_basis (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        source work) = true) :
    ∀ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∀ representative, Same node.state representative → ∀ original : GeneralRuleJobs.Receipt,
        original.Valid twoRoutePlan [] (.base "Graph") representative →
          sourceLogicalKey original ∈ committedKeys logicalKey
            ((Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
              source work).nodes.flatMap (fun reached => CollectionOccurrenceSearch.publicationWithPackets reached.run)) := by
  intro node present representative same original valid
  obtain ⟨rounds, pair, published, observed⟩ := two_route_source_key_eventually_published valid
  have presentations := CollectionOccurrenceSearch.publicationWithPackets_run_same
    twoRoutePlan [] (.base "Graph") 0 representative node.state rounds same.symm
  rw [presentations] at published
  have atNode := CollectionOccurrenceSearch.settled_node_packets_complete
    twoRoutePlan [] (.base "Graph") 0 source work done node present rounds pair published
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨pair, List.mem_flatMap.mpr ⟨node, present, atNode⟩, observed⟩

/-- The source-key coverage condition is earned by the actual Transitive
consumer's finite carrier and local drainage, without assumed settlement. -/
theorem two_route_eventually_source_key_basis (source : Pattern) :
    ∃ work,
      Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
          source work) = true ∧
      ∀ node ∈ (Complete.Explore.explore
          (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
        ∀ representative, Same node.state representative → ∀ original : GeneralRuleJobs.Receipt,
          original.Valid twoRoutePlan [] (.base "Graph") representative →
            sourceLogicalKey original ∈ committedKeys logicalKey
              ((Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
                source work).nodes.flatMap (fun reached => CollectionOccurrenceSearch.publicationWithPackets reached.run)) := by
  obtain ⟨work, done⟩ := two_route_eventually_settled source
  exact ⟨work, done, two_route_settled_source_key_basis source work done⟩

#print axioms two_route_settled_source_key_basis
#print axioms two_route_eventually_source_key_basis

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBags RuleBinding GeneralPremise CollectionOccurrenceBatch CollectionCommittedObservation
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem packet_finished_job {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {packet : Publication} {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    receipt.job = packet.job.preparedJob packet.prepared := by
  unfold Publication.finish? CollectionOccurrenceContinuation.finish?
    CollectionOccurrenceHandoff.finish? GeneralRuleJobs.finish? GeneralRuleJobs.finishWith? at finished
  dsimp only at finished
  split at finished
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at finished
    obtain ⟨localTarget, _, finished⟩ := finished
    split at finished
    · cases Option.some.inj finished
      rfl
    · cases finished
  · cases finished

private theorem retained_packet_origin {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {state : State plan bound expected source}
    (balanced : state.Balanced) {pair : Committed}
    (published : pair ∈ retained plan bound expected state.log) :
    pair.1.job.Valid plan bound expected source ∧
      pair.1.finish? plan bound expected = some pair.2 := by
  obtain ⟨packet, logged, made⟩ := List.mem_filterMap.mp published
  unfold commit? at made
  cases finished : packet.finish? plan bound expected with
  | none => simp only [finished, Option.map_none] at made; cases made
  | some receipt =>
      simp only [finished, Option.map_some, Option.some.injEq] at made
      cases made
      obtain ⟨frame, _, member⟩ := List.mem_flatMap.mp (balanced.subset logged)
      obtain ⟨outcome, _, same⟩ := List.mem_map.mp member
      cases same
      exact ⟨frame.allocation.licensed, finished⟩

/-- An observed root-graph key is read from its actual valid retained
receipt. Allocation and receipt identities agree by the original finisher. -/
theorem two_route_retained_source_key {source : Pattern}
    {state : State twoRoutePlan [] (.base "Graph") source} (balanced : state.Balanced)
    {pair : Committed} (published : pair ∈ retained twoRoutePlan [] (.base "Graph") state.log) :
    pair.2.Valid twoRoutePlan [] (.base "Graph") (pair.1.job.presentedSource pair.1.prepared) ∧
      logicalKey pair = sourceLogicalKey pair.2 := by
  have valid := retained_receipt_valid balanced published
  obtain ⟨origin, finished⟩ := retained_packet_origin balanced published
  have fields := packet_finished_job finished
  have permissions : twoRoutePlan.permissions.sites = .rootOnly := rfl
  have packetLicense := origin.1.2
  have receiptLicense := valid.1.2
  rw [permissions] at packetLicense receiptLicense
  have shape : logicalSiteShape pair.1.job.origin.site = logicalSiteShape pair.2.job.site :=
    Eq.trans (root_licensed_logical_shape packetLicense) (Eq.symm (root_licensed_logical_shape receiptLicense))
  refine ⟨valid, ?_⟩
  simp only [logicalKey, sourceLogicalKey, LogicalKey.mk.injEq, and_true]
  refine ⟨?_, ?_, shape⟩
  · rw [fields]
    rfl
  · rw [fields]
    rfl

/-- Every key in an actual explored account has a licensed source receipt
at an equivalent representative of an actual reached node. This does not
require settlement. -/
theorem two_route_observed_key_source (source : Pattern) (work : Nat) {key : LogicalKey}
    (observed : key ∈ committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.publicationWithPackets node.run))) :
    ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∃ representative, Same node.state representative ∧ ∃ original : GeneralRuleJobs.Receipt,
        original.Valid twoRoutePlan [] (.base "Graph") representative ∧
          sourceLogicalKey original = key := by
  obtain ⟨pair, published, keyed⟩ := List.mem_map.mp (List.mem_toFinset.mp observed)
  obtain ⟨node, reached, published⟩ := List.mem_flatMap.mp published
  have running := (Complete.Explore.explore_good
    (CollectionOccurrenceSearch.search_lawful twoRoutePlan [] (.base "Graph") 0) source work).run node reached
  rw [running] at published
  let spent := (Complete.Explore.explore
    (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).round - node.born
  have balanced := (CollectionOccurrenceMachine.run_invariant 0 spent
    (CollectionOccurrenceMachine.begin_invariant (plan := twoRoutePlan) (bound := [])
      (expected := .base "Graph") (source := canon node.state) 0)).1
  change pair ∈ retained twoRoutePlan [] (.base "Graph") _ at published
  obtain ⟨valid, keySource⟩ := two_route_retained_source_key balanced published
  refine ⟨node, reached, pair.1.job.presentedSource pair.1.prepared, ?_, pair.2, valid,
    Eq.trans keySource.symm keyed⟩
  exact (show Same node.state (canon node.state) from (canon_idempotent node.state).symm).trans (retained_source_same balanced published)

/-- Settlement identifies the finite declared one-step source-key basis.
It does not enumerate unfolded proof trees or discard the full pair log. -/
theorem two_route_settled_source_key_iff (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        source work) = true) (key : LogicalKey) :
    key ∈ committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.publicationWithPackets node.run)) ↔
    ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∃ representative, Same node.state representative ∧ ∃ original : GeneralRuleJobs.Receipt,
        original.Valid twoRoutePlan [] (.base "Graph") representative ∧
          sourceLogicalKey original = key := by
  constructor
  · exact two_route_observed_key_source source work
  · rintro ⟨node, reached, representative, same, original, valid, rfl⟩
    exact two_route_settled_source_key_basis source work done node reached representative same original valid

/-- Fact-set membership forgets the separately completed one-step key
identity. It retains an actual valid source receipt as its soundness witness. -/
theorem two_route_settled_fact_iff (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        source work) = true) (fact : Pattern) :
    fact ∈ ((committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.publicationWithPackets node.run))).val.filterMap
          logicalEdge?).toFinset ↔
    ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∃ representative, Same node.state representative ∧ ∃ original : GeneralRuleJobs.Receipt,
        original.Valid twoRoutePlan [] (.base "Graph") representative ∧
          logicalEdge? (sourceLogicalKey original) = some fact := by
  simp only [Multiset.mem_toFinset, Multiset.mem_filterMap, Finset.mem_val]
  constructor
  · rintro ⟨key, observed, read⟩
    obtain ⟨node, reached, representative, same, original, valid, keyed⟩ :=
      (two_route_settled_source_key_iff source work done key).mp observed
    exact ⟨node, reached, representative, same, original, valid, keyed ▸ read⟩
  · rintro ⟨node, reached, representative, same, original, valid, read⟩
    exact ⟨sourceLogicalKey original,
      (two_route_settled_source_key_iff source work done (sourceLogicalKey original)).mpr
        ⟨node, reached, representative, same, original, valid, rfl⟩, read⟩

/-- The actual graph consumer earns a settled exact one-step source-key
basis. No completion of unfolded derivation histories follows from this. -/
theorem two_route_eventually_exact_source_key_basis (source : Pattern) :
    ∃ work,
      Complete.Settled.settled (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
        (Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
          source work) = true ∧
      ∀ key : LogicalKey,
        key ∈ committedKeys logicalKey
          ((Complete.Explore.explore (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0)
            source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.publicationWithPackets node.run)) ↔
        ∃ node ∈ (Complete.Explore.explore
            (CollectionOccurrenceSearch.search twoRoutePlan [] (.base "Graph") 0) source work).nodes,
          ∃ representative, Same node.state representative ∧ ∃ original : GeneralRuleJobs.Receipt,
            original.Valid twoRoutePlan [] (.base "Graph") representative ∧
              sourceLogicalKey original = key := by
  obtain ⟨work, done⟩ := two_route_eventually_settled source
  exact ⟨work, done, two_route_settled_source_key_iff source work done⟩

#print axioms two_route_retained_source_key
#print axioms two_route_observed_key_source
#print axioms two_route_settled_source_key_iff
#print axioms two_route_settled_fact_iff
#print axioms two_route_eventually_exact_source_key_basis

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open CollectionOccurrenceBatch
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner

private theorem initial_canonical_transitive_complete (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    {source : Pattern} (allocation : Allocation plan [] (.base "Graph") (canon source)) :
    (Frame.run 3 (Frame.initialCanonical allocation)).state.agenda = [] ∧
      (Frame.run 3 (Frame.initialCanonical allocation)).state.unresolved = [] := by
  obtain ⟨environment, selected, specified⟩ := allocation_transitive_fields plan singleton allocation
  have empty : allocation.request.rule.premises = [] := by rw [selected]; cbv
  apply RecursiveCollectionContinuation.canonical_unconditional_complete allocation.request allocation.canonical_seed empty
  apply transitive_projection_total_in allocation.request selected specified
  simpa only [environment] using role

private theorem initialized_canonical_transitive_clean (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    {source : Pattern} (frame : Frame plan [] (.base "Graph") (canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (initialized : CollectionOccurrenceMachine.InitializedWith
      (canonicalSeedProfile plan [] (.base "Graph") source) frame) : frame.state.unresolved = [] := by
  obtain ⟨elapsed, started⟩ := initialized
  have finished := initial_canonical_transitive_complete plan singleton role frame.allocation
  have shifted : Frame.run 3 frame = Frame.run elapsed
      (Frame.run 3 (Frame.initialWith (canonicalSeedProfile plan [] (.base "Graph") source) frame.allocation)) := by
    calc
      _ = Frame.run 3 (Frame.run elapsed
          (Frame.initialWith (canonicalSeedProfile plan [] (.base "Graph") source) frame.allocation)) :=
        congrArg (Frame.run 3) started
      _ = Frame.run (elapsed + 3)
          (Frame.initialWith (canonicalSeedProfile plan [] (.base "Graph") source) frame.allocation) :=
        (Frame.run_add ..).symm
      _ = _ := by rw [Nat.add_comm elapsed 3, Frame.run_add]
  have initialDone :
      (RecursiveCollectionContinuation.Canonical.run frame.allocation.request 3
        (RecursiveCollectionContinuation.Canonical.start frame.allocation.request frame.allocation.canonical_seed)).agenda = [] ∧
      (RecursiveCollectionContinuation.Canonical.run frame.allocation.request 3
        (RecursiveCollectionContinuation.Canonical.start frame.allocation.request frame.allocation.canonical_seed)).unresolved = [] := finished
  have laterClear : (Frame.run 3 frame).state.unresolved = [] := by
    rw [shifted]
    change (Scheduler.run (StructuralDescent.Scheduled.expand frame.allocation.request.environment
      frame.allocation.request.goal) elapsed (RecursiveCollectionContinuation.Canonical.run frame.allocation.request 3
        (RecursiveCollectionContinuation.Canonical.start frame.allocation.request frame.allocation.canonical_seed))).unresolved = []
    rw [Scheduler.run_idle _ elapsed _ initialDone.1]
    exact initialDone.2
  obtain ⟨suffix, joined⟩ := Scheduler.run_obligations_prefix
    (StructuralDescent.Scheduled.expand frame.allocation.request.environment frame.allocation.request.goal) 3 frame.state
  have empty : frame.state.unresolved ++ suffix = [] := by
    rw [← joined]
    exact laterClear
  exact (List.append_eq_nil_iff.mp empty).1

/-- The selected canonical Transitive loop earns local completion from
actual allocation seeds, finite matching, and total typed reduct projection.
It retains EqEvent histories and does not assert global explorer closure. -/
theorem canonical_transitive_runWith_eventually_complete (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    (source : Pattern) :
    ∃ work, CollectionOccurrenceSearch.statusWith
      (CollectionOccurrenceSearch.runWith plan [] (.base "Graph") (canonicalSeedProfile plan [] (.base "Graph"))
        0 source work) = .complete := by
  obtain ⟨work, matching, agendas⟩ := CollectionOccurrenceSearch.canonical_runWith_eventually_drained
    plan [] (.base "Graph") 0 source
  let executed := CollectionOccurrenceMachine.runWith (canonicalSeedProfile plan [] (.base "Graph") source) 0 work
    (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
      plan [] (.base "Graph") (canon source))
  have clean : ∀ frame ∈ executed.batch.frames, frame.state.unresolved = [] := by
    intro frame member
    exact initialized_canonical_transitive_clean plan singleton role frame
      (CollectionOccurrenceMachine.runWith_initialized (canonicalSeedProfile plan [] (.base "Graph") source)
        0 work frame member)
  have matchingBool : executed.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) = true :=
    List.all_eq_true.mpr matching
  have agendasBool : executed.batch.frames.all (fun frame => frame.state.agenda.isEmpty) = true :=
    List.all_eq_true.mpr (fun frame member => by simp only [agendas frame member, List.isEmpty_nil])
  have cleanBool : executed.batch.frames.all (fun frame => frame.state.unresolved.isEmpty) = true :=
    List.all_eq_true.mpr (fun frame member => by simp only [clean frame member, List.isEmpty_nil])
  refine ⟨work, ?_⟩
  change CollectionOccurrenceSearch.statusWith ⟨source, executed⟩ = .complete
  unfold CollectionOccurrenceSearch.statusWith
  rw [matchingBool, agendasBool, cleanBool]
  rfl

theorem canonical_reachability_runWith_eventually_complete (source : Pattern) :
    ∃ work, CollectionOccurrenceSearch.statusWith
      (CollectionOccurrenceSearch.runWith reachabilityPlan [] (.base "Graph")
        (canonicalSeedProfile reachabilityPlan [] (.base "Graph")) 0 source work) = .complete := by
  obtain ⟨singleton, role, _, _⟩ := reachability_completion_metadata
  exact canonical_transitive_runWith_eventually_complete reachabilityPlan singleton role source

theorem canonical_two_route_runWith_eventually_complete (source : Pattern) :
    ∃ work, CollectionOccurrenceSearch.statusWith
      (CollectionOccurrenceSearch.runWith twoRoutePlan [] (.base "Graph")
        (canonicalSeedProfile twoRoutePlan [] (.base "Graph")) 0 source work) = .complete := by
  obtain ⟨singleton, role, _, _⟩ := two_route_completion_metadata
  exact canonical_transitive_runWith_eventually_complete twoRoutePlan singleton role source

#print axioms canonical_transitive_runWith_eventually_complete
#print axioms canonical_reachability_runWith_eventually_complete
#print axioms canonical_two_route_runWith_eventually_complete

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner

/-- Actual canonical published receipts have object-typed targets in the
finite authored Graph carrier. Interpretation-relative validity is sufficient
for this typing result; no original-reference step theorem is inferred. -/
theorem canonical_search_target_in_carrier_of_signature (plan : GeneralExecutionAdmission.Plan)
    (free : plan.snapshot.free = FreeTypeContext.empty)
    (included : plan.snapshot.language.terms ⊆ twoRouteLanguage.terms) (source : Pattern) (work : Nat)
    (receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event)
    (published : receipt ∈ (CollectionOccurrenceSearch.canonicalSearch plan [] (.base "Graph") 0).publication
      ((CollectionOccurrenceSearch.canonicalSearch plan [] (.base "Graph") 0).run source work)) :
    canon receipt.target ∈ canonicalGraphCarrier := by
  obtain ⟨representative, _, valid⟩ :=
    (CollectionOccurrenceSearch.canonical_search_lawful plan [] (.base "Graph") 0).sound
      source work receipt published
  have sorted := (GeneralPlanEnvironment.typing_iff plan [] (.base "Graph") receipt.target).mp
    valid.2.2.2.2
  rw [free] at sorted
  exact canonical_graph_mem_carrier (HasType.of_terms_subset included sorted.1) rfl sorted.2.2.1

/-- Generic exploration preserves its raw initial node and all canonical
successors. Native standardized entry is obtained by choosing a canonical seed. -/
theorem canonical_explored_graph_in_carrier_of_signature (plan : GeneralExecutionAdmission.Plan)
    (free : plan.snapshot.free = FreeTypeContext.empty)
    (included : plan.snapshot.language.terms ⊆ twoRouteLanguage.terms) (source : Pattern) : ∀ work,
    ∀ node ∈ (Complete.Explore.explore
      (CollectionOccurrenceSearch.canonicalSearch plan [] (.base "Graph") 0) source work).nodes,
      node.state ∈ explorerCarrier source := by
  let S := CollectionOccurrenceSearch.canonicalSearch plan [] (.base "Graph") 0
  have lawful := CollectionOccurrenceSearch.canonical_search_lawful plan [] (.base "Graph") 0
  intro work
  induction work with
  | zero =>
      intro node member
      simp only [Complete.Explore.explore, Complete.Explore.begin, List.mem_singleton] at member
      subst node
      exact List.mem_cons_self
  | succ work ih =>
      intro node member
      change node ∈ (Complete.Explore.step S (Complete.Explore.explore S source work)).nodes at member
      simp only [Complete.Explore.step, List.mem_append] at member
      rcases member with kept | fresh
      · obtain ⟨pair, pairInside, rfl⟩ := List.mem_map.mp kept
        obtain ⟨old, oldInside, rfl⟩ := List.mem_map.mp pairInside
        exact ih old oldInside
      · have generated := Complete.Explore.fresh_subset _ _ node fresh
        obtain ⟨pair, pairInside, generated⟩ := List.mem_flatMap.mp generated
        obtain ⟨old, oldInside, rfl⟩ := List.mem_map.mp pairInside
        obtain ⟨receipt, released, rfl⟩ := List.mem_map.mp generated
        have published := List.mem_of_mem_drop released
        have good := Complete.Explore.explore_good lawful source work
        rw [good.run old oldInside, lawful.resume_run] at published
        have finite := canonical_search_target_in_carrier_of_signature plan free included old.state _ receipt published
        exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr finite)

/-- The actual canonical receipt-bearing graph settles from finite typed
states and separately proved genuine local completion. All receipt edges to
already visited states remain in the existing explorer account. -/
theorem canonical_transitive_explorer_eventually_settled (plan : GeneralExecutionAdmission.Plan)
    (singleton : plan.rules = [reachabilityPlan.rules[0]'(by cbv)])
    (role : SchemaTyping.checkSchemaType [] (GeneralPlanEnvironment.environment plan).language
      (FreeTypeContext.ofList actualRule.typeContext) [] actualRule.right (.base "Graph") = true)
    (free : plan.snapshot.free = FreeTypeContext.empty)
    (included : plan.snapshot.language.terms ⊆ twoRouteLanguage.terms)
    (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch plan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch plan [] (.base "Graph") 0) source work) = true := by
  apply Complete.Settled.eventually_settled_of_finite_carrier
    (CollectionOccurrenceSearch.canonical_search_lawful plan [] (.base "Graph") 0)
    (CollectionOccurrenceSearch.canonical_search_stable plan [] (.base "Graph") 0)
    source (explorerCarrier source) (canonical_explored_graph_in_carrier_of_signature plan free included source)
  intro state _
  exact canonical_transitive_runWith_eventually_complete plan singleton role state

theorem canonical_reachability_eventually_settled (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch reachabilityPlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch reachabilityPlan [] (.base "Graph") 0)
        source work) = true := by
  obtain ⟨singleton, role, free, included⟩ := reachability_completion_metadata
  exact canonical_transitive_explorer_eventually_settled reachabilityPlan singleton role free included source

theorem canonical_two_route_eventually_settled (source : Pattern) :
    ∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true := by
  obtain ⟨singleton, role, free, included⟩ := two_route_completion_metadata
  exact canonical_transitive_explorer_eventually_settled twoRoutePlan singleton role free included source

#print axioms canonical_search_target_in_carrier_of_signature
#print axioms canonical_explored_graph_in_carrier_of_signature
#print axioms canonical_transitive_explorer_eventually_settled
#print axioms canonical_reachability_eventually_settled
#print axioms canonical_two_route_eventually_settled

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open CollectionOccurrenceBatch CollectionCommittedObservation
open Mettapedia.GSLT.LanguageDef.WellSorted

local instance : DecidableEq RecursiveCollectionHandoff.canonicalMatchingExecution.Choice :=
  inferInstanceAs (DecidableEq EquationalScopedReceipts.Event)

private theorem two_route_interpreted_selected {Choice : Type} {meaning : MatchingInterpretation Choice}
    {source : Pattern} {receipt : GeneralRuleJobs.Receipt Choice}
    (valid : receipt.ValidInWith meaning DynamicProvider.empty twoRoutePlan [] (.base "Graph") source) :
    receipt.job.declaration.rule = actualRule ∧ receipt.job.declaration.binding.spec = actualSpec := by
  have singleton : twoRoutePlan.rules = [reachabilityPlan.rules[0]'(by cbv)] := by cbv
  have member := List.fst_mem_of_mem_zipIdx valid.1.1
  rw [singleton, List.mem_singleton] at member
  change receipt.job.declaration = reachabilityPlan.rules[0]'(by cbv) at member
  rw [member]
  exact ⟨rfl, rfl⟩

private theorem empty_interpreted_premises_history {Choice : Type} {meaning : MatchingInterpretation Choice}
    {environment : Environment} {context : Context} {captured completed : Assignment}
    {history : List (Event Choice)}
    (held : Interpreted.PremisesHold meaning environment context [] captured completed history) : history = [] := by
  cases held
  rfl

private theorem two_route_canonical_history_depth {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation
      DynamicProvider.empty twoRoutePlan [] (.base "Graph") source) :
    StructuralDescent.eventsDepth receipt.premiseHistory ≤ 0 := by
  have selected := two_route_interpreted_selected valid
  have declared := GeneralRuleJobs.Job.selected_rule valid.1
  cases valid.2.1 with
  | @fire localBound type localSource target index rule spec trace captured completed history declared' specified
      admitted sorted matched typed premises reduced targetTyped =>
    have ruleSame : rule = receipt.job.declaration.rule := Option.some.inj (declared'.symm.trans declared)
    have empty : rule.premises = [] := by rw [ruleSame, selected.1]; cbv
    rw [empty] at premises
    rw [empty_interpreted_premises_history premises]
    simpa only [StructuralDescent.eventsDepth] using Nat.zero_le 0

/-- A canonical source-receipt key reaches an actual retained canonical
pair, with the original completed bindings and complete EqEvent history. -/
theorem canonical_two_route_source_key_eventually_published {source : Pattern}
    {original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation
      DynamicProvider.empty twoRoutePlan [] (.base "Graph") source) :
    ∃ (work : Nat) (pair : Committed EquationalScopedReceipts.Event),
      pair ∈ CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
        (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph"))
        ((CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).run source work) ∧
      logicalKey pair = sourceLogicalKey original := by
  obtain ⟨work, packet, receipt, logged, finished, licensed, _, _, _, completed, history,
    _, _, ordinal, declaration, _, _, _⟩ :=
    CollectionOccurrenceMachine.canonical_receipt_eventually_published_with_bindings valid 0
      (two_route_canonical_history_depth valid)
  have permissions : twoRoutePlan.permissions.sites = .rootOnly := rfl
  have packetLicense := licensed.1.2
  have sourceLicense := valid.1.2
  rw [permissions] at packetLicense sourceLicense
  have shape : logicalSiteShape packet.job.origin.site = logicalSiteShape original.job.site :=
    Eq.trans (root_licensed_logical_shape packetLicense) (Eq.symm (root_licensed_logical_shape sourceLicense))
  refine ⟨work, (packet, receipt), ?_, ?_⟩
  · change (packet, receipt) ∈ retainedCanonical twoRoutePlan [] (.base "Graph") _
    apply List.mem_filterMap.mpr
    refine ⟨packet, logged, ?_⟩
    simp only [commitWith?, finished, Option.map_some]
  · simp only [logicalKey, sourceLogicalKey, LogicalKey.mk.injEq]
    refine ⟨ordinal, congrArg (fun selected => selected.declarationIndex) declaration, shape, ?_, ?_, ?_, ?_⟩
    · rw [completed]
    · rw [completed]
    · rw [completed]
    · rw [history]

/-- The actual canonical pair supplies its own interpreted valid source
receipt and the same declared graph key, independently of settlement. -/
theorem canonical_two_route_retained_source_key {source : Pattern}
    {state : State twoRoutePlan [] (.base "Graph") (canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution}
    (balanced : state.Balanced) {pair : Committed EquationalScopedReceipts.Event}
    (published : pair ∈ retainedCanonical twoRoutePlan [] (.base "Graph") state.log) :
    pair.2.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
        twoRoutePlan [] (.base "Graph") (pair.1.job.presentedSource pair.1.prepared) ∧
      Same source (pair.1.job.presentedSource pair.1.prepared) ∧
      logicalKey pair = sourceLogicalKey pair.2 := by
  obtain ⟨packet, logged, made⟩ := List.mem_filterMap.mp published
  unfold commitWith? at made
  cases finished : packet.finishCanonical? twoRoutePlan [] (.base "Graph") with
  | none => simp only [finished, Option.map_none] at made; cases made
  | some receipt =>
      simp only [finished, Option.map_some, Option.some.injEq] at made
      cases made
      obtain ⟨frame, _, member⟩ := List.mem_flatMap.mp (balanced.subset logged)
      have valid := Frame.publication_canonical_valid (source := source) frame member finished
      have origin : packet.job.Valid twoRoutePlan [] (.base "Graph") (canon source) := by
        obtain ⟨outcome, _, same⟩ := List.mem_map.mp member
        cases same
        exact frame.allocation.licensed
      have fields := (CollectionOccurrenceContinuation.Canonical.finish_payload finished).1
      have permissions : twoRoutePlan.permissions.sites = .rootOnly := rfl
      have packetLicense := origin.1.2
      have receiptLicense := valid.1.1.2
      rw [permissions] at packetLicense receiptLicense
      have shape : logicalSiteShape packet.job.origin.site = logicalSiteShape receipt.job.site :=
        Eq.trans (root_licensed_logical_shape packetLicense) (Eq.symm (root_licensed_logical_shape receiptLicense))
      refine ⟨valid.1, valid.2, ?_⟩
      simp only [logicalKey, sourceLogicalKey, LogicalKey.mk.injEq, and_true]
      refine ⟨?_, ?_, shape⟩
      · rw [fields]
        rfl
      · rw [fields]
        rfl

theorem canonical_two_route_observed_key_source (source : Pattern) (work : Nat)
    {key : LogicalKey EquationalScopedReceipts.Event}
    (observed : key ∈ committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) node.run))) :
    ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∃ representative, Same node.state representative ∧
        ∃ original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event,
          original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
            twoRoutePlan [] (.base "Graph") representative ∧ sourceLogicalKey original = key := by
  obtain ⟨pair, published, keyed⟩ := List.mem_map.mp (List.mem_toFinset.mp observed)
  obtain ⟨node, reached, published⟩ := List.mem_flatMap.mp published
  have running := (Complete.Explore.explore_good
    (CollectionOccurrenceSearch.canonical_search_lawful twoRoutePlan [] (.base "Graph") 0) source work).run node reached
  rw [running] at published
  let spent := (Complete.Explore.explore
    (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).round - node.born
  have balanced := (CollectionOccurrenceMachine.runWith_invariant
    (canonicalSeedProfile twoRoutePlan [] (.base "Graph") node.state) 0 spent
    (CollectionOccurrenceMachine.beginWith_invariant RecursiveCollectionHandoff.canonicalMatchingExecution
      (plan := twoRoutePlan) (bound := []) (expected := .base "Graph") (source := canon node.state) 0)).1
  change pair ∈ retainedCanonical twoRoutePlan [] (.base "Graph") _ at published
  obtain ⟨valid, same, keySource⟩ := canonical_two_route_retained_source_key (source := node.state) balanced published
  exact ⟨node, reached, pair.1.job.presentedSource pair.1.prepared, same, pair.2, valid,
    Eq.trans keySource.symm keyed⟩

theorem canonical_two_route_settled_source_key_basis (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true) :
    ∀ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∀ representative, Same node.state representative →
        ∀ original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event,
          original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
            twoRoutePlan [] (.base "Graph") representative →
              sourceLogicalKey original ∈ committedKeys logicalKey
                ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
                  source work).nodes.flatMap (fun reached => CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
                    (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) reached.run)) := by
  intro node present representative same original valid
  obtain ⟨rounds, pair, published, observed⟩ := canonical_two_route_source_key_eventually_published valid
  have presentations := CollectionOccurrenceSearch.canonical_committed_run_same
    twoRoutePlan [] (.base "Graph") 0 representative node.state rounds same.symm
  rw [presentations] at published
  have atNode := CollectionOccurrenceSearch.canonical_settled_node_committed_complete
    twoRoutePlan [] (.base "Graph") 0 source work done node present rounds pair published
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨pair, List.mem_flatMap.mpr ⟨node, present, atNode⟩, observed⟩

theorem canonical_two_route_settled_source_key_iff (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true) (key : LogicalKey EquationalScopedReceipts.Event) :
    key ∈ committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) node.run)) ↔
    ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∃ representative, Same node.state representative ∧
        ∃ original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event,
          original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
            twoRoutePlan [] (.base "Graph") representative ∧ sourceLogicalKey original = key := by
  constructor
  · exact canonical_two_route_observed_key_source source work
  · rintro ⟨node, reached, representative, same, original, valid, rfl⟩
    exact canonical_two_route_settled_source_key_basis source work done node reached representative same original valid

/-- The fact-set readout forgets one-step key multiplicity while retaining
an actual interpreted source receipt for each observed conclusion. -/
theorem canonical_two_route_settled_fact_iff (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work) = true) (fact : Pattern) :
    fact ∈ ((committedKeys logicalKey
      ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.committedWith
          (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
          (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) node.run))).val.filterMap
            logicalEdge?).toFinset ↔
    ∃ node ∈ (Complete.Explore.explore
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
      ∃ representative, Same node.state representative ∧
        ∃ original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event,
          original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
            twoRoutePlan [] (.base "Graph") representative ∧
              logicalEdge? (sourceLogicalKey original) = some fact := by
  simp only [Multiset.mem_toFinset, Multiset.mem_filterMap, Finset.mem_val]
  constructor
  · rintro ⟨key, observed, read⟩
    obtain ⟨node, reached, representative, same, original, valid, keyed⟩ :=
      (canonical_two_route_settled_source_key_iff source work done key).mp observed
    exact ⟨node, reached, representative, same, original, valid, keyed ▸ read⟩
  · rintro ⟨node, reached, representative, same, original, valid, read⟩
    exact ⟨sourceLogicalKey original,
      (canonical_two_route_settled_source_key_iff source work done (sourceLogicalKey original)).mpr
        ⟨node, reached, representative, same, original, valid, rfl⟩, read⟩

theorem canonical_two_route_eventually_exact_source_key_basis (source : Pattern) :
    ∃ work,
      Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
          source work) = true ∧
      ∀ key : LogicalKey EquationalScopedReceipts.Event,
        key ∈ committedKeys logicalKey
          ((Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
            source work).nodes.flatMap (fun node => CollectionOccurrenceSearch.committedWith (matcher := RecursiveCollectionHandoff.canonicalMatchingExecution)
              (fun packet => packet.finishCanonical? twoRoutePlan [] (.base "Graph")) node.run)) ↔
        ∃ node ∈ (Complete.Explore.explore
            (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) source work).nodes,
          ∃ representative, Same node.state representative ∧
            ∃ original : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event,
              original.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
                twoRoutePlan [] (.base "Graph") representative ∧ sourceLogicalKey original = key := by
  obtain ⟨work, done⟩ := canonical_two_route_eventually_settled source
  exact ⟨work, done, canonical_two_route_settled_source_key_iff source work done⟩

#print axioms canonical_two_route_source_key_eventually_published
#print axioms canonical_two_route_retained_source_key
#print axioms canonical_two_route_observed_key_source
#print axioms canonical_two_route_settled_source_key_basis
#print axioms canonical_two_route_settled_source_key_iff
#print axioms canonical_two_route_settled_fact_iff
#print axioms canonical_two_route_eventually_exact_source_key_basis

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem fact_carrier_source_collections (language : LanguageDef) {fact : Pattern}
    (member : fact ∈ factCarrier) : SourceCollections language fact := by
  obtain ⟨first, firstMember, later⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp member)
  obtain ⟨last, lastMember, rfl⟩ := List.mem_map.mp later
  obtain ⟨firstLabel, _, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨lastLabel, _, rfl⟩ := List.mem_map.mp lastMember
  apply SourceCollections.apply
  intro argument present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact .apply (by intro value member; cases member)
  · exact .apply (by intro value member; cases member)

/-- Every unordered occurrence in an actual closed typed graph has the
declared collection-data type used by its typing derivation. The finite
Node/Edge carrier supplies the collection-free children, not an assumed
kind-law or whole-equivalence certificate. -/
theorem typed_graph_source_collections_of_signature (language : LanguageDef)
    (included : language.terms ⊆ twoRouteLanguage.terms) {source : Pattern}
    (typed : OpenPatternWellSorted language FreeTypeContext.empty [] (.base "Graph") source) :
    SourceCollections language source := by
  have finite := canonical_graph_mem_carrier (HasType.of_terms_subset included typed.1) rfl typed.2.2.1
  obtain ⟨facts, present, represented⟩ := Finset.mem_image.mp finite
  have members := Finset.mem_powerset.mp present
  have same : Same source (graph facts.toList) := represented.symm
  have graphTyped : OpenPatternWellSorted language FreeTypeContext.empty [] (.base "Graph")
      (graph facts.toList) :=
    openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) typed
  obtain ⟨index, rule, declared, _, sorted⟩ := HasType.collection_type_origin graphTyped.1
  have good : SourceCollections language (graph facts.toList) := by
    apply SourceCollections.collection
    · exact Or.inr ⟨rule, List.mem_iff_getElem?.mpr ⟨index, declared⟩, sorted⟩
    · intro fact member
      exact fact_carrier_source_collections language (members (Finset.mem_toList.mp member))
  exact good.of_same same.symm

/-- Built-in canonical equality is licensed by the actual source collection
laws on this graph-typed domain. No arbitrary-set or open-term completeness
claim is used. -/
theorem typed_graph_same_reference_equivalent (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (included : language.terms ⊆ twoRouteLanguage.terms) {source target : Pattern}
    (typed : OpenPatternWellSorted language FreeTypeContext.empty [] (.base "Graph") source)
    (same : Same source target) : Equivalent relEnv language source target :=
  equivalent_of_same (typed_graph_source_collections_of_signature language included typed) same

theorem typed_graph_canon_reference_equivalent (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (included : language.terms ⊆ twoRouteLanguage.terms) {source : Pattern}
    (typed : OpenPatternWellSorted language FreeTypeContext.empty [] (.base "Graph") source) :
    Equivalent relEnv language source (canon source) :=
  typed_graph_same_reference_equivalent relEnv language included typed (canon_idempotent source).symm

#print axioms typed_graph_source_collections_of_signature
#print axioms typed_graph_same_reference_equivalent
#print axioms typed_graph_canon_reference_equivalent

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls


namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise CanonicalBags
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem transitive_find_readout {first second : Match.Bindings}
    (same : ∀ key, first.lookup key = second.lookup key) (key : String) :
    first.find? (fun entry => entry.1 == key) = second.find? (fun entry => entry.1 == key) := by
  cases left : first.find? (fun entry => entry.1 == key) with
  | none =>
    cases right : second.find? (fun entry => entry.1 == key) with
    | none => rfl
    | some entry =>
      have impossible := same key
      simp only [Match.Bindings.lookup, left, right, Option.map_none, Option.map_some] at impossible
      cases impossible
  | some firstEntry =>
    cases right : second.find? (fun entry => entry.1 == key) with
    | none =>
      have impossible := same key
      simp only [Match.Bindings.lookup, left, right, Option.map_none, Option.map_some] at impossible
      cases impossible
    | some secondEntry =>
      have firstKey : firstEntry.1 = key := beq_iff_eq.mp
        (List.find?_some (p := fun entry : String × Pattern => entry.1 == key) left)
      have secondKey : secondEntry.1 = key := beq_iff_eq.mp
        (List.find?_some (p := fun entry : String × Pattern => entry.1 == key) right)
      have bodies : firstEntry.2 = secondEntry.2 := Option.some.inj (by
        simpa only [Match.Bindings.lookup, left, right, Option.map_some] using same key)
      exact congrArg some (Prod.ext (firstKey.trans secondKey.symm) bodies)

private theorem transitive_rhs_readout {first second : Match.Bindings}
    (same : ∀ key, first.lookup key = second.lookup key) :
    Match.applyBindings first actualRule.right = Match.applyBindings second actualRule.right := by
  rw [actual_right]
  simp only [firstEdge, secondEdge, thirdEdge, Match.applyBindings, List.map_cons, List.map_nil,
    transitive_find_readout same]

private theorem transitive_rhs_notDeeper (sites : Pattern) :
    ReferenceStep.notDeeper sites 0 actualRule.right = true := by
  rw [actual_right]
  simp only [firstEdge, secondEdge, thirdEdge, ReferenceStep.notDeeper,
    ReferenceStep.notDeeperList]
  cases Match.captureDepth "x" 0 sites <;>
    cases Match.captureDepth "y" 0 sites <;>
    cases Match.captureDepth "z" 0 sites <;>
    cases Match.captureDepth "rest" 0 sites <;> rfl

private theorem transitive_left_binderFree : Match.binderFree actualRule.left = true := by
  rw [actual_left]
  rfl

private theorem transitive_right_binderFree : Match.binderFree actualRule.right = true := by
  rw [actual_right]
  rfl

private theorem transitive_premises_nil : actualRule.premises = [] := by cbv

/-- The actual transitive rule's canonical matcher gives a literal source
match at an equivalent presentation. Its right side is read from the same
captured values, including the actual collection rest. -/
theorem canonical_transitive_primitive_reference_with_bindings (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (operation : Pattern → Pattern → Pattern) {index : Nat} {authored : RewriteRule} {source target : Pattern}
    {trace : List EquationalScopedReceipts.Event} {captured : Assignment}
    (declared : language.rewrites[index]? = some authored)
    (left : authored.left = actualRule.left) (right : authored.right = actualRule.right)
    (empty : authored.premises = [])
    (matched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨actualRule, actualSpec, 0, .left, [], 0, [], actualRule.left, source⟩ trace captured)
    (roots : RootValues 0 captured)
    (reduced : reductWith? operation actualRule actualSpec 0 captured = some target) :
    ∃ (presented : Pattern) (bindings : Match.Bindings),
      Same source presented ∧
      ReferenceStep.StepValid relEnv language presented (.rule index bindings []) target ∧
      BindingAgreement actualRule.left.freeFvarNames captured bindings := by
  obtain ⟨presented, same, ordinary⟩ :=
    EquationalScopedMatching.meaning_has_ordinary_presentation matched.meaning
  have presentedSame : Same source presented := by
    simpa only [RecursiveCollectionHandoff.canonicalRequest, Same, canon_idempotent] using same
  obtain ⟨bindings, rawMatched, agreement⟩ :=
    binderFree_matching_bindingAgreement transitive_left_binderFree ordinary roots
  have rhs := binderFree_instantiation_readout transitive_right_binderFree roots reduced
  have readback : Match.applyBindings bindings actualRule.right = target :=
    (transitive_rhs_readout (fun key =>
      (agreement.lookups key).symm.trans (ordinary_lookup captured key).symm)).trans rhs
  have scopedRead : Match.applyBindingsScoped (ReferenceStep.captureSites authored)
      bindings 0 authored.right = target := by
    rw [right]
    exact (ReferenceStep.applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ _ _
      (transitive_rhs_notDeeper _)).trans readback
  refine ⟨presented, bindings, presentedSame, ?_, agreement⟩
  rw [← scopedRead]
  apply ReferenceStep.StepValid.rule declared
  · simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, left] using rawMatched
  · rw [empty]
    exact .nil bindings

/-- The original source-step soundness interface remains the projection
of the same primitive construction with binding readback. -/
theorem canonical_transitive_primitive_reference (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (operation : Pattern → Pattern → Pattern) {index : Nat} {authored : RewriteRule} {source target : Pattern}
    {trace : List EquationalScopedReceipts.Event} {captured : Assignment}
    (declared : language.rewrites[index]? = some authored)
    (left : authored.left = actualRule.left) (right : authored.right = actualRule.right)
    (empty : authored.premises = [])
    (matched : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨actualRule, actualSpec, 0, .left, [], 0, [], actualRule.left, source⟩ trace captured)
    (roots : RootValues 0 captured)
    (reduced : reductWith? operation actualRule actualSpec 0 captured = some target) :
    ∃ (presented : Pattern) (bindings : Match.Bindings),
      Same source presented ∧
      ReferenceStep.StepValid relEnv language presented (.rule index bindings []) target := by
  obtain ⟨presented, bindings, same, step, _⟩ :=
    canonical_transitive_primitive_reference_with_bindings relEnv language operation
      declared left right empty matched roots reduced
  exact ⟨presented, bindings, same, step⟩

/-- The original source declaration, including its authored metadata. -/
def transitiveAuthoredRule : RewriteRule := twoRouteLanguage.rewrites[0]'(by cbv)

private theorem two_route_reference_metadata :
    (GeneralPlanEnvironment.environment twoRoutePlan).language.rewrites = [actualRule] ∧
      specification? (GeneralPlanEnvironment.environment twoRoutePlan) 0 = some actualSpec ∧
      twoRouteLanguage.rewrites[0]? = some transitiveAuthoredRule ∧
      transitiveAuthoredRule.left = actualRule.left ∧
      transitiveAuthoredRule.right = actualRule.right ∧
      transitiveAuthoredRule.premises = [] ∧
      checkZeroDependencies actualSpec = true := by cbv

/-- Actual canonical interpreted root firings of the finite graph consumer
have a genuine original-source step modulo the graph's typed collection
laws. No internal equation policy is changed: this rule has no premises. -/
theorem canonical_two_route_root_source_modulo (relEnv : Engine.RelationEnv)
    {source target : Pattern} {index : Nat} {trace : List EquationalScopedReceipts.Event}
    {captured completed : Assignment} {history : List (Event EquationalScopedReceipts.Event)}
    (fired : Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      (GeneralPlanEnvironment.environment twoRoutePlan) [] (.base "Graph") source index trace
      captured completed history target) :
    ReferenceStep.StepModulo relEnv twoRouteLanguage source target := by
  obtain ⟨rows, actualSpecified, sourceDeclared, sourceLeft, sourceRight, sourceEmpty, zero⟩ :=
    two_route_reference_metadata
  cases fired with
  | @fire _ _ _ _ index rule spec trace captured completed history declared specified
      admitted sorted matched captureTyped premises reduced targetTyped =>
    have position := declared
    rw [rows] at position
    cases index with
    | succ index => simp only [List.getElem?_cons_succ, List.getElem?_nil] at position; cases position
    | zero =>
      have sameRule : rule = actualRule := Option.some.inj position.symm
      cases sameRule
      have sameSpec : spec = actualSpec := Option.some.inj (specified.symm.trans actualSpecified)
      cases sameSpec
      rw [transitive_premises_nil] at premises
      cases premises
      obtain ⟨presented, bindings, same, step⟩ := canonical_transitive_primitive_reference
        relEnv twoRouteLanguage _ sourceDeclared sourceLeft sourceRight sourceEmpty matched
        (captureTyped.rootValues zero) reduced
      have typed : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source := by
        exact (GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") source).mp sorted
      exact ⟨presented, target,
        typed_graph_same_reference_equivalent relEnv twoRouteLanguage (fun _ member => member) typed same,
        ⟨_, step⟩, Relation.EqvGen.refl _⟩

private theorem canonical_two_route_receipt_root {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation
      DynamicProvider.empty twoRoutePlan [] (.base "Graph") source) :
    Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      (GeneralPlanEnvironment.environment twoRoutePlan) [] (.base "Graph") source receipt.job.ordinal
      receipt.matcherTrace receipt.captured receipt.completed receipt.premiseHistory receipt.localTarget ∧
      receipt.target = receipt.localTarget := by
  have licensed := valid.1.2
  have member := GeneralTypedSites.generate_complete licensed
  have permissions : twoRoutePlan.permissions.sites = .rootOnly := rfl
  rw [permissions, GeneralTypedSites.generate_rootOnly] at member
  have site : receipt.job.site = GeneralTypedSites.SiteData.here [] (.base "Graph") source := by
    split at member
    · exact List.mem_singleton.mp member
    · cases member
  constructor
  · simpa only [site, GeneralTypedSites.SiteData.here, GeneralPlanEnvironment.environmentWith_empty]
      using valid.2.1
  · simpa only [site, GeneralTypedSites.SiteData.here, DerivedContexts.OneHoleContext.fill]
      using valid.2.2.2.1

theorem canonical_two_route_receipt_source_typed {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation
      DynamicProvider.empty twoRoutePlan [] (.base "Graph") source) :
    OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") source := by
  have rootFired := (canonical_two_route_receipt_root valid).1
  cases rootFired with
  | fire _ _ _ sorted _ _ _ _ _ =>
    exact (GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") source).mp sorted

/-- A retained graph receipt has an actual original-language rule witness
between source-equivalent presentations. Its full receipt is unchanged. -/
theorem canonical_two_route_receipt_source_modulo (relEnv : Engine.RelationEnv) {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation
      DynamicProvider.empty twoRoutePlan [] (.base "Graph") source) :
    ReferenceStep.StepModulo relEnv twoRouteLanguage source receipt.target := by
  obtain ⟨rootFired, targetRead⟩ := canonical_two_route_receipt_root valid
  rw [targetRead]
  exact canonical_two_route_root_source_modulo relEnv rootFired

/-- The canonical search's valid receipt view is source-sound, including
its explicit initial representative and canonical observed target. -/
theorem canonical_two_route_valid_source_modulo (relEnv : Engine.RelationEnv) {source : Pattern}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (valid : (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).Valid source receipt) :
    ReferenceStep.StepModulo relEnv twoRouteLanguage source (canon receipt.target) := by
  obtain ⟨representative, sourceSame, justified⟩ := valid
  have sourceTyped := canonical_two_route_receipt_source_typed justified
  have initialEquation := typed_graph_same_reference_equivalent relEnv twoRouteLanguage
    (fun _ member => member) sourceTyped sourceSame.symm
  have targetTyped : OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph") receipt.target := by
    apply (GeneralPlanEnvironment.typing_iff twoRoutePlan [] (.base "Graph") receipt.target).mp
    simpa only [GeneralPlanEnvironment.environmentWith_empty, GeneralPlanEnvironment.environment]
      using justified.2.2.2.2
  have targetEquation := typed_graph_canon_reference_equivalent relEnv twoRouteLanguage
    (fun _ member => member) targetTyped
  obtain ⟨redex, contractum, initial, stepped, final⟩ := canonical_two_route_receipt_source_modulo relEnv justified
  exact ⟨redex, contractum, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ initialEquation) initial,
    stepped, Relation.EqvGen.trans _ _ _ final targetEquation⟩

/-- Every receipt-bearing explored edge is a step of the actual original
source relation modulo its licensed collection laws, even before settlement. -/
theorem canonical_two_route_explored_edges_source_modulo (relEnv : Engine.RelationEnv)
    (source : Pattern) (work : Nat)
    {edge : Pattern × GeneralRuleJobs.Receipt EquationalScopedReceipts.Event × Pattern}
    (member : edge ∈ Complete.Graph.edges
      (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        source work)) :
    ReferenceStep.StepModulo relEnv twoRouteLanguage edge.1 edge.2.2 := by
  obtain ⟨valid, targetRead⟩ := Complete.Graph.edge_valid
    (CollectionOccurrenceSearch.canonical_search_lawful twoRoutePlan [] (.base "Graph") 0) source work edge member
  rw [targetRead]
  exact canonical_two_route_valid_source_modulo relEnv valid

private theorem transitive_increasing_spines : IncreasingSpines actualRule actualSpec := by
  have admitted : admittedFor actualRule actualSpec = true := by cbv
  have zero : checkZeroDependencies actualSpec = true := by cbv
  intro captureName site path arguments found depth indices spine
  have expanded := found
  unfold arguments? at expanded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at expanded
  obtain ⟨dependencies, dependency, _⟩ := expanded
  have noDependencies := checkZeroDependencies_sound actualSpec zero captureName dependencies dependency
  have dependencyEmpty : dependencies? actualSpec captureName = some [] := by
    simpa only [noDependencies] using dependency
  have actual : occurrenceDeclared actualRule ⟨captureName, site, path, []⟩ = true := by
    apply Bool.eq_true_of_not_eq_false
    intro refused
    unfold arguments? at found
    rw [dependencyEmpty] at found
    simp only [refused, guard, pure, Bool.false_eq_true, if_false] at found
    cases found
  have sameRead := arguments_empty_of_admitted admitted dependencyEmpty actual
  have empty : arguments = [] := Option.some.inj (found.symm.trans sameRead)
  cases empty
  change some [] = some indices at spine
  cases Option.some.inj spine
  exact .nil

private def canonicalSelfLoopJob : GeneralRuleJobs.Job :=
  ⟨0, twoRoutePlan.rules[0]'(by cbv),
    GeneralTypedSites.SiteData.here [] (.base "Graph") selfLoop⟩

private def canonicalSelfLoopReceipt (trace : List EquationalScopedReceipts.Event) :
    GeneralRuleJobs.Receipt EquationalScopedReceipts.Event :=
  ⟨canonicalSelfLoopJob, trace, selfLoopCaptured, selfLoopCaptured, [], selfLoopResult, selfLoopResult⟩

private theorem canonicalSelfLoop_licensed :
    canonicalSelfLoopJob.Valid twoRoutePlan [] (.base "Graph") selfLoop := by
  refine ⟨by cbv; exact .head _, .here (by rfl) (by rfl) ?_⟩
  exact (checkOpenPatternWellSorted_sound
    (language := (GeneralPlanEnvironment.environment twoRoutePlan).language)
    (free := twoRoutePlan.snapshot.free) (bound := []) (expected := .base "Graph")
    (pattern := selfLoop) (by cbv)).1

private theorem canonicalSelfLoop_finished (trace : List EquationalScopedReceipts.Event) :
    GeneralRuleJobs.finishWith? DynamicProvider.empty twoRoutePlan [] (.base "Graph") canonicalSelfLoopJob
      trace selfLoopCaptured selfLoopCaptured [] = some (canonicalSelfLoopReceipt trace) := by cbv

/-- The singleton-cycle control uses an actual ordinary duplicate presentation,
normalizes that match, and earns the canonical receipt through the real finisher. -/
theorem canonical_selfLoop_receipt_valid :
    ∃ receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event,
      receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation DynamicProvider.empty
        twoRoutePlan [] (.base "Graph") selfLoop ∧ receipt.premiseHistory = [] ∧ canon receipt.target = selfLoop := by
  have ordinary := GeneralScopedMatch.matchAt_sound selfLoop_matching
  have normalized := EquationalScopedMatching.ordinary_canonical transitive_increasing_spines ordinary
  obtain ⟨trace, matching⟩ := EquationalScopedReceipts.Meaning.traced normalized
  have canonicalCaptured : canonAssignment selfLoopCaptured = selfLoopCaptured := by cbv
  have canonicalSource : canon selfLoopPresentation = canon selfLoop := by cbv
  rw [canonicalCaptured, canonicalSource] at matching
  have matching' : RecursiveCollectionHandoff.canonicalMatchingInterpretation.Matches
      ⟨canonicalSelfLoopJob.declaration.rule, canonicalSelfLoopJob.declaration.binding.spec,
        canonicalSelfLoopJob.site.focusBound.length, .left, [], 0, [],
        canonicalSelfLoopJob.declaration.rule.left, canonicalSelfLoopJob.site.focus⟩ trace selfLoopCaptured := by
    have jobRule : canonicalSelfLoopJob.declaration.rule = actualRule := by cbv
    have jobSpec : canonicalSelfLoopJob.declaration.binding.spec = actualSpec := by cbv
    change EquationalScopedReceipts.Matches literalBodyComparison canonicalSelfLoopJob.declaration.rule
      canonicalSelfLoopJob.declaration.binding.spec 0 .left [] 0 [] canonicalSelfLoopJob.declaration.rule.left
      (canon selfLoop) trace selfLoopCaptured
    rw [jobRule, jobSpec]
    simpa only [canonAssignment, List.map_nil] using matching
  have held : Interpreted.PremisesHold RecursiveCollectionHandoff.canonicalMatchingInterpretation
      (GeneralPlanEnvironment.environmentWith twoRoutePlan DynamicProvider.empty) canonicalSelfLoopJob.context
      canonicalSelfLoopJob.declaration.rule.premises selfLoopCaptured selfLoopCaptured [] := by
    have empty : canonicalSelfLoopJob.declaration.rule.premises = [] := by cbv
    rw [empty]
    exact .nil
  have valid := GeneralRuleJobs.finishWith_interpreted_sound canonicalSelfLoop_licensed matching' held
    (canonicalSelfLoop_finished trace)
  exact ⟨canonicalSelfLoopReceipt trace, valid, rfl, by cbv⟩

/-- A real finite receipt has a source-level cyclic return. This asserts no
completion of its unfolded proof histories. -/
theorem canonical_selfLoop_source_return (relEnv : Engine.RelationEnv) :
    ReferenceStep.StepModulo relEnv twoRouteLanguage selfLoop selfLoop := by
  obtain ⟨receipt, valid, _, returns⟩ := canonical_selfLoop_receipt_valid
  have observed : (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).Valid selfLoop receipt :=
    ⟨selfLoop, rfl, valid⟩
  simpa only [returns] using canonical_two_route_valid_source_modulo relEnv observed

/-- The cycle reaches an actual joint log with its full allocation packet
and finished EqEvent receipt. It is not only a semantic matching witness. -/
theorem canonical_selfLoop_retained_return :
    ∃ (work : Nat) (packet : CollectionOccurrenceBatch.Publication EquationalScopedReceipts.Event)
        (receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event),
      packet ∈ (CollectionOccurrenceMachine.runCanonical 0 work
        (CollectionOccurrenceMachine.beginCanonical twoRoutePlan [] (.base "Graph") selfLoop)).batch.log ∧
      packet.finishCanonical? twoRoutePlan [] (.base "Graph") = some receipt ∧
      canon receipt.target = selfLoop := by
  obtain ⟨original, valid, history, returns⟩ := canonical_selfLoop_receipt_valid
  have bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ 0 := by
    simpa only [history, StructuralDescent.eventsDepth] using Nat.zero_le 0
  obtain ⟨work, packet, receipt, logged, finished, _, _, _, _, _, _, _, _, _, _, _, _, sameTarget⟩ :=
    CollectionOccurrenceMachine.canonical_receipt_eventually_published_with_bindings valid 0 bounded
  exact ⟨work, packet, receipt, logged, finished, Eq.trans (Eq.symm sameTarget) returns⟩

/-- The same existing public search dictionary publishes the cyclic return. -/
theorem canonical_selfLoop_has_published_return :
    ∃ work receipt,
      receipt ∈ (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).publication
        ((CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).run selfLoop work) ∧
      (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0).target receipt = selfLoop := by
  obtain ⟨work, packet, receipt, logged, finished, returns⟩ := canonical_selfLoop_retained_return
  refine ⟨work, receipt, ?_, returns⟩
  change receipt ∈ ((CollectionOccurrenceMachine.runCanonical 0 work
    (CollectionOccurrenceMachine.beginCanonical twoRoutePlan [] (.base "Graph") selfLoop)).batch.log.filterMap
    (fun candidate => candidate.finishCanonical? twoRoutePlan [] (.base "Graph")))
  exact List.mem_filterMap.mpr ⟨packet, logged, finished⟩

/-- Finite canonical exploration coexists with unbounded operational receipt
histories. No identification of those histories with logical proof trees is made. -/
theorem canonical_selfLoop_closed_graph_unbounded_histories :
    (∃ work, Complete.Settled.settled (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
      (Complete.Explore.explore (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0)
        selfLoop work) = true) ∧
    (∀ bound, ∃ states receipts,
      Mettapedia.Machines.ResumableSearchRunner.History
        (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) states receipts ∧
          bound < receipts.length) := by
  refine ⟨canonical_two_route_eventually_settled selfLoop, ?_⟩
  obtain ⟨work, receipt, published, returns⟩ := canonical_selfLoop_has_published_return
  have valid := (CollectionOccurrenceSearch.canonical_search_lawful twoRoutePlan [] (.base "Graph") 0).sound
    selfLoop work receipt published
  intro bound
  exact Complete.Graph.self_return_histories_unbounded
    (CollectionOccurrenceSearch.canonicalSearch twoRoutePlan [] (.base "Graph") 0) selfLoop receipt valid returns bound

/-- The finite graph source-law bridge excludes a bag in the graph carrier. -/
theorem wrong_kind_graph_source_refused :
    ¬ OpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph")
      (.collection .hashBag [edge "A" "A"] none) := by
  intro typed
  have checked := checkOpenPatternWellSorted_complete typed
  have refused : checkOpenPatternWellSorted twoRouteLanguage FreeTypeContext.empty [] (.base "Graph")
      (.collection .hashBag [edge "A" "A"] none) = false := by cbv
  rw [refused] at checked
  cases checked

#print axioms canonical_transitive_primitive_reference_with_bindings
#print axioms canonical_transitive_primitive_reference
#print axioms canonical_two_route_root_source_modulo
#print axioms canonical_two_route_receipt_source_typed
#print axioms canonical_two_route_receipt_source_modulo
#print axioms canonical_two_route_valid_source_modulo
#print axioms canonical_two_route_explored_edges_source_modulo
#print axioms canonical_selfLoop_receipt_valid
#print axioms canonical_selfLoop_source_return
#print axioms canonical_selfLoop_retained_return
#print axioms canonical_selfLoop_has_published_return
#print axioms canonical_selfLoop_closed_graph_unbounded_histories
#print axioms wrong_kind_graph_source_refused

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation.GraphControls
