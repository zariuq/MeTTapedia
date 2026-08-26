import Mettapedia.CognitiveArchitecture.GodelClaw.GateChain

/-!
# Epistemic resolve and non-bypass mediation

This module formalizes the five-clause account of epistemic resolve from
K. Crawford and P. Hammer, *Epistemic Resolve: Governed Uptake and the
Architecture of Mind*, AGI 2026, LNAI 16854, pp. 192–205.

The paper distinguishes two levels which must not be conflated:

* an adjudicative episode recruits standing commitments, couples them to the
  candidate information, writes the verdict back, and enforces it downstream;
* non-bypass is an architectural condition on *all* paths with the same durable
  change or an effect of equivalent force.

Accordingly, passing a local Boolean gate chain is not enough.  The strict
notion below quantifies over every durable update.  The later architectural
notion follows the qualification in Section 8 of the paper: the governed path
is canonical for normal updates, while abnormal drift is detected and routed
back through a governed corrective episode.

The relation-valued presentation is substrate-neutral.  It does not assume
that commitments, verdicts, or coupling are symbolic.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicResolve

universe uItem uState uPath uDurable uEffect uEpisode

/-- One candidate-information update, including the path by which it occurred. -/
structure Update (Item : Type uItem) (State : Type uState) (Path : Type uPath) where
  item : Item
  before : State
  after : State
  path : Path

/-- Architecture-neutral semantics for durable uptake.

`durableView` identifies the state component which survives to affect later
continuations.  `downstreamEffect` lets non-bypass compare paths which do not
write literally the same state but have an effect of equivalent force.
The remaining relations interpret the four episode-local clauses from
Crawford and Hammer's Definition 1. -/
structure UptakeArchitecture
    (Item : Type uItem) (State : Type uState) (Path : Type uPath)
    (Durable : Type uDurable) (Effect : Type uEffect) (Episode : Type uEpisode) where
  durableView : State → Durable
  downstreamEffect : Update Item State Path → Effect
  actual : Update Item State Path → Prop
  realizes : Episode → Update Item State Path → Prop
  recruited : Episode → Prop
  coupled : Episode → Prop
  wroteBack : Episode → Prop
  enforced : Episode → Prop

namespace UptakeArchitecture

variable {Item : Type uItem} {State : Type uState} {Path : Type uPath}
  {Durable : Type uDurable} {Effect : Type uEffect} {Episode : Type uEpisode}

/-- The durable component changed across an update. -/
def ChangesDurable (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  A.durableView u.before ≠ A.durableView u.after

/-- Two paths have the impact compared by Crawford–Hammer's non-bypass clause:
either the same durable-state change, or a downstream effect of equivalent
force. -/
def EquivalentImpact (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (u v : Update Item State Path) : Prop :=
  (A.durableView u.before = A.durableView v.before ∧
      A.durableView u.after = A.durableView v.after) ∨
    A.downstreamEffect u = A.downstreamEffect v

theorem equivalentImpact_refl
    (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : A.EquivalentImpact u u := by
  exact Or.inl ⟨rfl, rfl⟩

theorem equivalentImpact_symm
    {A : UptakeArchitecture Item State Path Durable Effect Episode}
    {u v : Update Item State Path} (h : A.EquivalentImpact u v) :
    A.EquivalentImpact v u := by
  rcases h with hstate | heffect
  · exact Or.inl ⟨hstate.1.symm, hstate.2.symm⟩
  · exact Or.inr heffect.symm

/-- The four clauses local to one adjudicative episode.  Non-bypass is kept
separate because it quantifies over the architecture's alternative paths. -/
def LocallyGoverned (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (e : Episode) (u : Update Item State Path) : Prop :=
  A.realizes e u ∧ A.recruited e ∧ A.coupled e ∧ A.wroteBack e ∧ A.enforced e

/-- An update has at least one episode in which all four local clauses hold. -/
def IsMediated (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  ∃ e, A.LocallyGoverned e u

/-- An update traverses a coupling episode, independently of whether the other
three local clauses hold. -/
def HasCoupledPath (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  ∃ e, A.realizes e u ∧ A.coupled e

/-- No actual path with equivalent impact skips coupling. -/
def NoBypass (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  ∀ v, A.actual v → A.EquivalentImpact v u → A.HasCoupledPath v

/-- All five Crawford–Hammer clauses for one update and episode. -/
def Resolves (A : UptakeArchitecture Item State Path Durable Effect Episode)
    (e : Episode) (u : Update Item State Path) : Prop :=
  A.LocallyGoverned e u ∧ A.NoBypass u

/-- The strict reading: every actual durable-state change occurs in an episode
which satisfies all five clauses. -/
def StrictResolve (A : UptakeArchitecture Item State Path Durable Effect Episode) : Prop :=
  ∀ u, A.actual u → A.ChangesDurable u → ∃ e, A.Resolves e u

/-- A durable update which is not fully mediated by a local episode. -/
def HasUngovernedUpdate
    (A : UptakeArchitecture Item State Path Durable Effect Episode) : Prop :=
  ∃ u, A.actual u ∧ A.ChangesDurable u ∧ ¬ A.IsMediated u

/-- A durable update which skips coupling specifically. -/
def HasCouplingBypass
    (A : UptakeArchitecture Item State Path Durable Effect Episode) : Prop :=
  ∃ u, A.actual u ∧ A.ChangesDurable u ∧ ¬ A.HasCoupledPath u

theorem strictResolve_mediates
    {A : UptakeArchitecture Item State Path Durable Effect Episode}
    (h : A.StrictResolve) {u : Update Item State Path}
    (hu : A.actual u) (hchange : A.ChangesDurable u) :
    A.IsMediated u := by
  obtain ⟨e, he⟩ := h u hu hchange
  exact ⟨e, he.1⟩

theorem strictResolve_no_ungoverned_update
    {A : UptakeArchitecture Item State Path Durable Effect Episode}
    (h : A.StrictResolve) : ¬ A.HasUngovernedUpdate := by
  rintro ⟨u, hu, hchange, hunmediated⟩
  exact hunmediated (strictResolve_mediates h hu hchange)

theorem strictResolve_no_coupling_bypass
    {A : UptakeArchitecture Item State Path Durable Effect Episode}
    (h : A.StrictResolve) : ¬ A.HasCouplingBypass := by
  rintro ⟨u, hu, hchange, hskip⟩
  obtain ⟨e, he⟩ := h u hu hchange
  exact hskip ⟨e, he.1.1, he.1.2.2.1⟩

theorem strictResolve_all_equivalent_paths_coupled
    {A : UptakeArchitecture Item State Path Durable Effect Episode}
    (h : A.StrictResolve) {u v : Update Item State Path}
    (hu : A.actual u) (hchange : A.ChangesDurable u)
    (hv : A.actual v) (himpact : A.EquivalentImpact v u) :
    A.HasCoupledPath v := by
  obtain ⟨e, he⟩ := h u hu hchange
  exact he.2 v hv himpact

end UptakeArchitecture

/-! ## Architectural resolve with detectable and correctable drift -/

/-- Additional structure for the paper's architectural, rather than perfect,
reading of epistemic resolve.  `normal` designates the structurally canonical
write paths; `detected` and `corrects` describe internal recovery from drift. -/
structure CorrectiveUptakeArchitecture
    (Item : Type uItem) (State : Type uState) (Path : Type uPath)
    (Durable : Type uDurable) (Effect : Type uEffect) (Episode : Type uEpisode)
    extends UptakeArchitecture Item State Path Durable Effect Episode where
  normal : Update Item State Path → Prop
  detected : Update Item State Path → Prop
  corrects : Update Item State Path → Update Item State Path → Prop

namespace CorrectiveUptakeArchitecture

variable {Item : Type uItem} {State : Type uState} {Path : Type uPath}
  {Durable : Type uDurable} {Effect : Type uEffect} {Episode : Type uEpisode}

/-- Non-bypass restricted to structurally normal paths.  Abnormal drift may
exist, but it cannot be the architecture's canonical route. -/
def NormalNoBypass
    (A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  ∀ v, A.actual v → A.normal v → A.toUptakeArchitecture.EquivalentImpact v u →
    A.toUptakeArchitecture.HasCoupledPath v

/-- A normal update has a locally governed episode and no equivalent normal
path which skips coupling. -/
def NormallyResolved
    (A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  (∃ e, A.toUptakeArchitecture.LocallyGoverned e u) ∧ A.NormalNoBypass u

/-- Drift is an actual durable update outside the architecture's normal path. -/
def IsDrift
    (A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  A.actual u ∧ A.toUptakeArchitecture.ChangesDurable u ∧ ¬ A.normal u

/-- A drift update is detected and routed to an actual normal corrective update
which itself receives a locally governed episode. -/
def DriftIsCorrected
    (A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode)
    (u : Update Item State Path) : Prop :=
  A.detected u ∧ ∃ v, A.actual v ∧ A.normal v ∧ A.corrects u v ∧
    A.toUptakeArchitecture.IsMediated v

/-- Crawford–Hammer's Section 8 architectural reading: normal durable writes
are resolved, and departures from the canonical path are internally detected
and corrected through a governed update. -/
def ArchitecturalResolve
    (A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode) : Prop :=
  (∀ u, A.actual u → A.normal u → A.toUptakeArchitecture.ChangesDurable u →
      A.NormallyResolved u) ∧
    (∀ u, A.IsDrift u → A.DriftIsCorrected u)

theorem architecturalResolve_normal_mediated
    {A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode}
    (h : A.ArchitecturalResolve) {u : Update Item State Path}
    (hu : A.actual u) (hnormal : A.normal u)
    (hchange : A.toUptakeArchitecture.ChangesDurable u) :
    A.toUptakeArchitecture.IsMediated u := by
  exact (h.1 u hu hnormal hchange).1

theorem architecturalResolve_drift_detected
    {A : CorrectiveUptakeArchitecture Item State Path Durable Effect Episode}
    (h : A.ArchitecturalResolve) {u : Update Item State Path}
    (hdrift : A.IsDrift u) : A.detected u :=
  (h.2 u hdrift).1

end CorrectiveUptakeArchitecture

/-! ## Finite positive and negative systems -/

namespace Canary

inductive Item where
  | claim
  deriving DecidableEq

inductive State where
  | open
  | accreted
  | committed
  deriving DecidableEq

inductive Path where
  | governed
  | bypass
  | corrective
  deriving DecidableEq

inductive Episode where
  | initialAdjudication
  | correctiveAdjudication
  | ungovernedIngestion
  deriving DecidableEq

inductive Effect where
  | noCommitment
  | commitment
  deriving DecidableEq

abbrev U := Update Item State Path

def governedUpdate : U :=
  ⟨.claim, .open, .committed, .governed⟩

def bypassUpdate : U :=
  ⟨.claim, .open, .accreted, .bypass⟩

def correctiveUpdate : U :=
  ⟨.claim, .accreted, .committed, .corrective⟩

def durableView : State → State := id

def downstreamEffect (u : U) : Effect :=
  match u.after with
  | .open => .noCommitment
  | .accreted | .committed => .commitment

def realizes : Episode → U → Prop
  | .initialAdjudication, u => u = governedUpdate
  | .correctiveAdjudication, u => u = correctiveUpdate
  | .ungovernedIngestion, u => u = bypassUpdate

def recruited : Episode → Prop
  | .initialAdjudication | .correctiveAdjudication => True
  | .ungovernedIngestion => False

def coupled : Episode → Prop
  | .initialAdjudication | .correctiveAdjudication => True
  | .ungovernedIngestion => False

def wroteBack : Episode → Prop
  | .initialAdjudication | .correctiveAdjudication | .ungovernedIngestion => True

def enforced : Episode → Prop
  | .initialAdjudication | .correctiveAdjudication | .ungovernedIngestion => True

theorem ungovernedIngestion_writes_without_coupling :
    wroteBack .ungovernedIngestion ∧ enforced .ungovernedIngestion ∧
      ¬ coupled .ungovernedIngestion := by
  simp [wroteBack, enforced, coupled]

/-- A closed architecture whose only actual write is adjudicative. -/
def governedArchitecture :
    UptakeArchitecture Item State Path State Effect Episode where
  durableView := durableView
  downstreamEffect := downstreamEffect
  actual := (· = governedUpdate)
  realizes := realizes
  recruited := recruited
  coupled := coupled
  wroteBack := wroteBack
  enforced := enforced

theorem governedArchitecture_strictResolve : governedArchitecture.StrictResolve := by
  intro u hu _
  subst u
  refine ⟨.initialAdjudication, ?_, ?_⟩
  · exact ⟨rfl, trivial, trivial, trivial, trivial⟩
  · intro v hv _
    subst v
    exact ⟨.initialAdjudication, rfl, trivial⟩

/-- An architecture with the same valid adjudicative path plus an actual path
which writes equivalent commitment force without any coupling episode. -/
def bypassArchitecture :
    UptakeArchitecture Item State Path State Effect Episode where
  durableView := durableView
  downstreamEffect := downstreamEffect
  actual := fun u => u = governedUpdate ∨ u = bypassUpdate
  realizes := realizes
  recruited := recruited
  coupled := coupled
  wroteBack := wroteBack
  enforced := enforced

theorem bypassArchitecture_hasCouplingBypass :
    bypassArchitecture.HasCouplingBypass := by
  refine ⟨bypassUpdate, Or.inr rfl, ?_, ?_⟩
  · simp [UptakeArchitecture.ChangesDurable, bypassArchitecture, durableView,
      bypassUpdate]
  · rintro ⟨e, he, hcoupled⟩
    cases e <;>
      simp_all [bypassArchitecture, realizes, bypassUpdate, governedUpdate,
        correctiveUpdate, coupled]

theorem bypassArchitecture_not_strictResolve :
    ¬ bypassArchitecture.StrictResolve := by
  intro h
  exact UptakeArchitecture.strictResolve_no_coupling_bypass h
    bypassArchitecture_hasCouplingBypass

/-- Every local gate may allow while an unrepresented parallel write path still
violates completeness of mediation. -/
theorem gate_passage_does_not_imply_complete_mediation :
    GateChain.chainAllows ([fun _ : Unit => true] : List (GateChain.Gate Unit)) () = true ∧
      ¬ bypassArchitecture.StrictResolve := by
  exact ⟨rfl, bypassArchitecture_not_strictResolve⟩

/-- The source's architectural qualification: the bypass is abnormal, detected,
and routed through a governed corrective adjudication. -/
def correctiveArchitecture :
    CorrectiveUptakeArchitecture Item State Path State Effect Episode where
  toUptakeArchitecture := {
    durableView := durableView
    downstreamEffect := downstreamEffect
    actual := fun u => u = governedUpdate ∨ u = bypassUpdate ∨ u = correctiveUpdate
    realizes := realizes
    recruited := recruited
    coupled := coupled
    wroteBack := wroteBack
    enforced := enforced
  }
  normal := fun u => u = governedUpdate ∨ u = correctiveUpdate
  detected := (· = bypassUpdate)
  corrects := fun u v => u = bypassUpdate ∧ v = correctiveUpdate

theorem correctiveArchitecture_architecturalResolve :
    correctiveArchitecture.ArchitecturalResolve := by
  constructor
  · intro u hu hnormal _
    rcases hnormal with rfl | rfl
    · constructor
      · exact ⟨.initialAdjudication, rfl, trivial, trivial, trivial, trivial⟩
      · intro v hv hvnormal _
        rcases hvnormal with rfl | rfl
        · exact ⟨.initialAdjudication, rfl, trivial⟩
        · exact ⟨.correctiveAdjudication, rfl, trivial⟩
    · constructor
      · exact ⟨.correctiveAdjudication, rfl, trivial, trivial, trivial, trivial⟩
      · intro v hv hvnormal _
        rcases hvnormal with rfl | rfl
        · exact ⟨.initialAdjudication, rfl, trivial⟩
        · exact ⟨.correctiveAdjudication, rfl, trivial⟩
  · intro u hdrift
    rcases hdrift with ⟨hu, _, hnormal⟩
    rcases hu with rfl | rfl | rfl
    · exact False.elim (hnormal (Or.inl rfl))
    · constructor
      · rfl
      · refine ⟨correctiveUpdate, Or.inr (Or.inr rfl), Or.inr rfl, ⟨rfl, rfl⟩, ?_⟩
        exact ⟨.correctiveAdjudication, rfl, trivial, trivial, trivial, trivial⟩
    · exact False.elim (hnormal (Or.inr rfl))

theorem correctiveArchitecture_not_strictResolve :
    ¬ correctiveArchitecture.toUptakeArchitecture.StrictResolve := by
  intro h
  have hBypass : correctiveArchitecture.toUptakeArchitecture.HasCouplingBypass := by
    refine ⟨bypassUpdate, Or.inr (Or.inl rfl), ?_, ?_⟩
    · simp [UptakeArchitecture.ChangesDurable, correctiveArchitecture, durableView,
        bypassUpdate]
    · rintro ⟨e, he, hcoupled⟩
      cases e <;>
        simp_all [correctiveArchitecture, realizes, bypassUpdate, governedUpdate,
          correctiveUpdate, coupled]
  exact UptakeArchitecture.strictResolve_no_coupling_bypass h hBypass

/-- Architectural resolve is strictly weaker than perfect strict resolve: it
can accommodate detected and corrected abnormal drift. -/
theorem architecturalResolve_does_not_imply_strictResolve :
    correctiveArchitecture.ArchitecturalResolve ∧
      ¬ correctiveArchitecture.toUptakeArchitecture.StrictResolve :=
  ⟨correctiveArchitecture_architecturalResolve,
    correctiveArchitecture_not_strictResolve⟩

end Canary

end Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicResolve

#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicResolve.Canary.governedArchitecture_strictResolve
#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicResolve.Canary.gate_passage_does_not_imply_complete_mediation
#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicResolve.Canary.architecturalResolve_does_not_imply_strictResolve
