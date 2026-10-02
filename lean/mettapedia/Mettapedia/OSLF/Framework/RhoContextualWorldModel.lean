import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy
import Mettapedia.OSLF.Framework.GSLTWorldModel
import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading

/-!
# Parallel environments as queryable world models

In `P | Q`, `Q` is an operational environment for `P`, and conversely.
This module connects that process-calculus observation to the WM calculus.
An epistemic state is a multiset of candidate environments; a query supplies
an agent and asks whether one communication can reach a specified observation.
The observation must respect the rho structural equations and be decidable.
The existing complete canonical stepper then decides the query exactly.

Three operations remain distinct:

* `par` composes interacting processes;
* addition pools environment samples, preserving multiplicity;
* `extendWorld` adds the same parallel partner to each sampled environment.

Pooling is additive evidence revision. Extending a world instead pulls back
the query by parallel composition with its agent. The latter square follows
from rho associativity and commutativity, not from evidence additivity.
Every contextual WM-calculus rewrite preserves the resulting query evidence.

This formalizes the interaction principle behind Meredith's description of
F1R3Score as giving programmable access to a world. It does not identify the
rho fragment with the full timed, graded score calculus or verify its player.

References:
* Meredith and Radestock, A Reflective Higher-order Calculus (2005).
* F1R3FLY, Scores as Processes and F1R3Score:
  https://github.com/F1R3FLY-io/F1R3Score
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoContextualWorldModel

open scoped ENNReal

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTWorldModel
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy

/-! ## Symmetric, compositional operational environments -/

theorem par_comm_equiv (left right : RhoProcess) :
    rhoLanguageDefGSLT.Equiv (par left right) (par right left) :=
  canonicalize_parallel_comm left.1 right.1

theorem par_assoc_equiv (first second third : RhoProcess) :
    rhoLanguageDefGSLT.Equiv (par (par first second) third)
      (par first (par second third)) :=
  canonicalize_parallel_assoc first.1 second.1 third.1

theorem par_equiv_right (left : RhoProcess) {right right' : RhoProcess}
    (same : rhoLanguageDefGSLT.Equiv right right') :
    rhoLanguageDefGSLT.Equiv (par left right) (par left right') :=
  (par_comm_equiv left right).trans
    ((par_equiv_left left same).trans (par_comm_equiv right' left))

/-- An observable outcome, with both a decision procedure and proof that
changing a process's structural representative cannot change the answer. -/
structure Observation where
  predicate : EquationPredicate rhoLanguageDefGSLT
  dec : DecidablePred predicate.1

instance (observation : Observation) : DecidablePred observation.predicate.1 :=
  observation.dec

/-- Observe that some step is possible, without inspecting its target. -/
def Observation.any : Observation where
  predicate := ⟨fun _ => True, by intro _ _ _; exact Iff.rfl⟩
  dec := fun _ => isTrue trivial

/-- Observe a specified structural-equation class of outcomes. -/
def Observation.exact (outcome : RhoProcess) : Observation where
  predicate := ⟨fun target => rhoLanguageDefGSLT.Equiv target outcome, by
    intro left right same
    exact ⟨fun h => same.symm.trans h, fun h => same.trans h⟩⟩
  dec := by
    intro target
    change Decidable (canonicalize target.1 = canonicalize outcome.1)
    infer_instance

/-- One actual rho step reaches an observable outcome. This is a may query:
it asserts an available interaction, not a scheduler or fairness guarantee. -/
def CanObserve (source : RhoProcess) (observation : Observation) : Prop :=
  ∃ target, rhoLanguageDefGSLT.Step source target ∧ observation.predicate.1 target

/-- The semantic query is decided by the complete finite successor list.
There is no bound on process syntax here, but the query looks one step ahead. -/
theorem canObserve_iff_enumerated (source : RhoProcess) (observation : Observation) :
    CanObserve source observation ↔
      ∃ target ∈ canonicalSuccessorList source, observation.predicate.1 target := by
  constructor
  · rintro ⟨target, step, observes⟩
    obtain ⟨representative, member, same⟩ := canonicalSuccessorList_complete source step
    exact ⟨representative, member, (observation.predicate.2 same).mp observes⟩
  · rintro ⟨target, member, observes⟩
    exact ⟨target, canonicalSuccessorList_sound member, observes⟩

instance (source : RhoProcess) (observation : Observation) :
    Decidable (CanObserve source observation) := by
  letI : Decidable (∃ target ∈ canonicalSuccessorList source, observation.predicate.1 target) :=
    @List.decidableBEx RhoProcess observation.predicate.1 observation.dec
      (canonicalSuccessorList source)
  exact decidable_of_iff
    (∃ target ∈ canonicalSuccessorList source, observation.predicate.1 target)
    (canObserve_iff_enumerated source observation).symm

theorem canObserve_equiv {left right : RhoProcess}
    (same : rhoLanguageDefGSLT.Equiv left right) (observation : Observation) :
    CanObserve left observation ↔ CanObserve right observation := by
  constructor
  · rintro ⟨target, step, observes⟩
    obtain ⟨target', step', sameTarget⟩ := rhoLanguageDefGSLT.rewrites_resp_left same step
    exact ⟨target', step', (observation.predicate.2 sameTarget).mp observes⟩
  · rintro ⟨target, step, observes⟩
    obtain ⟨target', step', sameTarget⟩ :=
      rhoLanguageDefGSLT.rewrites_resp_left same.symm step
    exact ⟨target', step', (observation.predicate.2 sameTarget).mp observes⟩

/-- Either component can be designated the agent: their joint observable
interaction is the same. This does not assert that their private observations
or knowledge are identical. -/
theorem mutual_world (agent environment : RhoProcess) (observation : Observation) :
    CanObserve (par agent environment) observation ↔
      CanObserve (par environment agent) observation :=
  canObserve_equiv (par_comm_equiv agent environment) observation

/-- A situated question includes the interacting agent, not just a predicate
of a passive world considered in isolation. -/
structure Query where
  agent : RhoProcess
  observation : Observation

def Answers (query : Query) (environment : RhoProcess) : Prop :=
  CanObserve (par query.agent environment) query.observation

instance (query : Query) : DecidablePred (Answers query) :=
  fun _ => inferInstanceAs (Decidable (CanObserve _ _))

theorem answers_equiv (query : Query) {left right : RhoProcess}
    (same : rhoLanguageDefGSLT.Equiv left right) :
    Answers query left ↔ Answers query right :=
  canObserve_equiv (par_equiv_right query.agent same) query.observation

def Query.asDecProp (query : Query) : DecProp RhoProcess where
  property := Answers query
  dec := inferInstance

/-! ## Evidence and the existing WM calculus -/

/-- Samples or candidate environments, with multiplicity. Addition is pooling,
not concurrent execution of all the sampled environments. No probability
distribution or independence assumption is inferred from these counts. -/
abbrev State := Multiset RhoProcess

noncomputable def evidence (state : State) (query : Query) : BinaryEvidence :=
  ensembleEvidence state query.asDecProp

theorem evidence_add (left right : State) (query : Query) :
    evidence (left + right) query = evidence left query + evidence right query :=
  ensembleEvidence_add left right query.asDecProp

theorem evidence_zero (query : Query) : evidence 0 query = 0 :=
  ensembleEvidence_zero query.asDecProp

noncomputable instance contextualWorldModel : BinaryWorldModel State Query where
  evidence := evidence
  evidence_add := evidence_add
  evidence_zero := evidence_zero

theorem evidence_singleton_yes (environment : RhoProcess) (query : Query)
    (answer : Answers query environment) :
    evidence {environment} query = ⟨1, 0⟩ :=
  ensembleEvidence_singleton_of_satisfies environment query.asDecProp answer

theorem evidence_singleton_no (environment : RhoProcess) (query : Query)
    (answer : ¬ Answers query environment) :
    evidence {environment} query = ⟨0, 1⟩ :=
  ensembleEvidence_singleton_of_refutes environment query.asDecProp answer

/-- Positive evidence has an actual interaction witness in a sampled world;
conversely, every such witness contributes positive evidence. -/
theorem positive_evidence_iff (state : State) (query : Query) :
    0 < (evidence state query).pos ↔
      ∃ environment ∈ state, ∃ target,
        rhoLanguageDefGSLT.Step (par query.agent environment) target ∧
          query.observation.predicate.1 target := by
  exact ensembleEvidence_pos_iff state query.asDecProp

noncomputable def reading (world : String → State) (query : String → Query) :
    WMReading State Query BinaryEvidence :=
  additiveReading world query

theorem reading_coreLaws (world : String → State) (query : String → Query) :
    (reading world query).CoreLaws :=
  additiveReading_coreLaws world query

/-- The bridge covers the full contextual closure of the existing WM calculus,
not just a newly written evaluator or the root evidence-addition equation. -/
theorem wm_rewrites_preserve_evidence (world : String → State) (query : String → Query)
    {source target : WMTerm .evidence} (steps : WMContextStepStar source target) :
    (reading world query).denote source = (reading world query).denote target :=
  additive_contextStepStar_agrees world query steps

/-! ## World extension and query transport -/

/-- Add one operational partner to every candidate environment. -/
def extendWorld (partner : RhoProcess) (state : State) : State :=
  state.map (fun environment => par environment partner)

/-- The same partner can be moved to the agent side of the interaction. -/
def Query.withPartner (query : Query) (partner : RhoProcess) : Query :=
  ⟨par query.agent partner, query.observation⟩

theorem answers_extend (query : Query) (environment partner : RhoProcess) :
    Answers query (par environment partner) ↔ Answers (query.withPartner partner) environment :=
  canObserve_equiv
    ((par_equiv_right query.agent (par_comm_equiv environment partner)).trans
      (par_assoc_equiv query.agent partner environment).symm) query.observation

/-- Pushing a world transformation through evidence is valid when its query
pullback preserves the actual interaction predicate pointwise. -/
theorem evidence_map (state : State) (transform : RhoProcess → RhoProcess)
    (query pulled : Query)
    (commutes : ∀ environment, Answers query (transform environment) ↔ Answers pulled environment) :
    evidence (state.map transform) query = evidence state pulled :=
  ensembleEvidence_map state transform query.asDecProp pulled.asDecProp commutes

/-- The environment/agent boundary is movable without changing any query
evidence, provided the query is transported with it. -/
theorem evidence_extendWorld (state : State) (partner : RhoProcess) (query : Query) :
    evidence (extendWorld partner state) query =
      evidence state (query.withPartner partner) :=
  evidence_map state _ query (query.withPartner partner) (fun _ => answers_extend query _ partner)

theorem extendWorld_add (partner : RhoProcess) (left right : State) :
    extendWorld partner (left + right) = extendWorld partner left + extendWorld partner right :=
  Multiset.map_add _ _ _

/-- The world-extension square continues to commute after evidence revision. -/
theorem evidence_extendWorld_revise (partner : RhoProcess) (left right : State) (query : Query) :
    evidence (extendWorld partner (left + right)) query =
      evidence left (query.withPartner partner) + evidence right (query.withPartner partner) := by
  rw [evidence_extendWorld, evidence_add]

/-- Agreement for all situated queries survives adding a parallel partner.
The proof uses closure of those queries under moving the partner into the
agent; an observer that only inspects isolated worlds need not have this law. -/
theorem extendWorld_respects_agree (world : String → State) (query : String → Query)
    {left right : State} (agree : (reading world query).Agree .state left right)
    (partner : RhoProcess) :
    (reading world query).Agree .state (extendWorld partner left) (extendWorld partner right) := by
  intro test
  change evidence (extendWorld partner left) test = evidence (extendWorld partner right) test
  rw [evidence_extendWorld, evidence_extendWorld]
  exact agree (test.withPartner partner)

end Mettapedia.OSLF.Framework.RhoContextualWorldModel
