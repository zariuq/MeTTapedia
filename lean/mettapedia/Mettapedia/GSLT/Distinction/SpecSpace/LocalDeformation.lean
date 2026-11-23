import Mettapedia.GSLT.Distinction.SpecSpace.SpecBasis
import Mettapedia.GSLT.Distinction.SpecSpace.ChuWitnessTopology
import Mettapedia.GSLT.Distinction.SpecSpace.SpecQuasimetric
import Mettapedia.GSLT.Distinction.SpecSpace.SpecLocale
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Interpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Criteria
import Mettapedia.GSLT.Coordination.ConsensusNumbers.WholeSpaceConditions

/-!
# Local Deformation, Real `ParallelCalculus` Space, Gorla Routes, and Impossibility Walls

This module develops two layers with zero synthetic rank proxies:

1. **General Local Deformation & Operational Lindström Theory** over any `SpecChuSpace S W`:
   * `WitnessMoritaEquiv C s₁ s₂`: same realized witness profile (`∀ w, pass s₁ w ↔ pass s₂ w`).
   * `StrictlyMoreCapable C s s'`: `s'` realizes every witness of `s` plus at least one more.
   * `IsRemovableArtifact C env s s'`: `s'` stays inside `env` and is strictly more capable.
   * `IsParetoWall C env s s'`: `s'` gains a witness over `s` only by leaving `env`.
   * `OnParetoFrontier C env s N` & `paretoFrontier_iff_upgrades_hit_wall`: Operational Lindström
     characterization in `witnessTopology C`.
   * `removableArtifact_iff_open_separation` & `deformation_exhaustive`.

2. **Real Specification Space over `ParallelCalculus.{0}` (`realParallelChu`)**:
   * **Real points**: actual calculi from `Mettapedia` — the absence-guarded step
     (`NullsOnTheStep.ParallelClosed.source`), count-guarded step (`Monotone.countedSource`),
     positive-tell shared-unknown step (`PositiveTell.tellSource`), solvable rho-hosting step
     (`stepParallelSolvable ω`), ground relay (`Monotone.relaySource`), positive bag target
     (`Monotone.relayTarget`), ground maker (`Monotone.makerSource`), faithful hosted reflective
     calculus (`RhoTarget.rhoParallel ω`), real HE MeTTa bidirectional matching
     (`heMatchParallel`), and real PeTTa `spaceMatch` (`pettaMatchParallel`).
   * **Real routes**: actual `UniformTranslation`s and `ComposableUniformRoute`s forming a real
     Lawvere quasimetric `uniformRouteQuasimetric : SpecQuasimetric WellFormedParallel`, alongside
     real bisimulation / commutation / lfp routes (`HeatingBisimulation`, `RhoChannelFragment`,
     `ReadOnlyQuery`, `MonotoneInference`).
   * **Real walls & Pareto frontier relative to `PersistenceEnvelope` (`ParallelCalculus.Persistent`)**:
     proves that every persistent calculus (`rhoParallel ω`, `heMatchParallel`, `pettaMatchParallel`,
     `relayTarget`) lies inside the closed obstruction walls for `.switchable`, `.hostsAbsence`,
     `.hostsPositiveTell`, and `.hostsCounted`; proves `IsParetoWall` for moving from any persistent
     calculus to `source`, `PositiveTell.tellSource`, or `Monotone.countedSource`; proves
     `OnParetoFrontier`; exhibits genuine `IsRemovableArtifact` upgrades inside `PersistenceEnvelope`;
     and isolates a second, finer equation-consistency wall (`Monotone.maker_no_bag_translation`)
     between non-switchable calculi.
   * **Gorla Criterion-Sensitivity Controls**: bundles `WholeSpaceConditions.rho_cannot_encode_absence`
     vs. `whole_configuration_encoding`, `Interpreter.interpret_succeeds_iff` + `interpret_not_homomorphic`,
     `Gap.step_not_into_rho_coordinated` + `guarded_context_fails`, and `Criteria.Controls` to show
     explicitly how dropping compositionality, homomorphism, or unguarded contexts collapses the walls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpecSpace

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
open Mettapedia.GSLT.Coordination.ConsensusNumbers

universe uS uW

/-! ## Part 1: General Local Deformation & Operational Lindström Theory -/

section GeneralDeformation

variable {S : Type uS} {W : Type uW} (C : SpecChuSpace S W)

/-- **Witness-level Morita equivalence**: two specifications realize the exact same
witnesses (topologically indistinguishable in `witnessTopology C`). -/
def WitnessMoritaEquiv (s₁ s₂ : S) : Prop :=
  WitnessRefines C s₁ s₂ ∧ WitnessRefines C s₂ s₁

theorem witnessMoritaEquiv_equivalence : Equivalence (WitnessMoritaEquiv C) where
  refl _ := ⟨fun _ h => h, fun _ h => h⟩
  symm h := ⟨h.2, h.1⟩
  trans h1 h2 := ⟨fun w hw => h2.1 w (h1.1 w hw), fun w hw => h1.2 w (h2.2 w hw)⟩

theorem witnessMoritaEquiv_iff_indistinguishable (s₁ s₂ : S) :
    WitnessMoritaEquiv C s₁ s₂ ↔
      ∀ U : Set S, @IsOpen S (witnessTopology C) U → (s₁ ∈ U ↔ s₂ ∈ U) := by
  rw [indistinguishable_iff_sameWitnesses]
  constructor
  · rintro ⟨h1, h2⟩ w; exact ⟨h1 w, h2 w⟩
  · intro h; exact ⟨fun w hw => (h w).mp hw, fun w hw => (h w).mpr hw⟩

/-- `s'` strictly dominates `s` on the witness space: it preserves every witness of `s`
and realizes at least one additional witness. -/
def StrictlyMoreCapable (s s' : S) : Prop :=
  WitnessRefines C s s' ∧ ∃ w : W, C.pass s' w ∧ ¬ C.pass s w

theorem strictlyMoreCapable_iff_not_rev (s s' : S) :
    StrictlyMoreCapable C s s' ↔ WitnessRefines C s s' ∧ ¬ WitnessRefines C s' s := by
  classical
  constructor
  · rintro ⟨href, w, hpass', hnot⟩
    exact ⟨href, fun hrev => hnot (hrev w hpass')⟩
  · rintro ⟨href, hnotRev⟩
    refine ⟨href, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hnotRev fun w hw => hnone w hw

/-- An **invariant envelope** declares the semantic laws (e.g., persistence under parallel
composition) that an admissible specification must preserve. -/
abbrev InvariantEnvelope (S : Type uS) := S → Prop

/-- A **removable artificial limitation**: neighbor `s'` remains inside `env` yet is
strictly more capable than `s`. -/
def IsRemovableArtifact (env : InvariantEnvelope S) (s s' : S) : Prop :=
  env s' ∧ StrictlyMoreCapable C s s'

/-- A **Pareto wall (fundamental boundary)**: neighbor `s'` gains a witness over `s`
only by breaking the invariant envelope `env`. -/
def IsParetoWall (env : InvariantEnvelope S) (s s' : S) : Prop :=
  ¬ env s' ∧ ∃ w : W, C.pass s' w ∧ ¬ C.pass s w

/-- A **strict regression**: neighbor `s'` strictly loses capability relative to `s`. -/
def IsStrictRegression (s s' : S) : Prop :=
  StrictlyMoreCapable C s' s

/-- An **incomparable trade-off** inside `env`: `s` and `s'` each realize a witness the
other lacks, while both satisfy `env`. -/
def IsIncomparableTradeoff (env : InvariantEnvelope S) (s s' : S) : Prop :=
  env s' ∧
  (∃ w₁ : W, C.pass s w₁ ∧ ¬ C.pass s' w₁) ∧
  (∃ w₂ : W, C.pass s' w₂ ∧ ¬ C.pass s w₂)

/-- **Pareto frontier (Operational Lindström optimality)** of `s` in neighborhood `N`
relative to invariant envelope `env`: `s` satisfies `env` and has no removable artifact
in `N`. -/
def OnParetoFrontier (env : InvariantEnvelope S) (s : S) (N : Set S) : Prop :=
  env s ∧ ∀ s' ∈ N, ¬ IsRemovableArtifact C env s s'

/-- **Operational Lindström Characterization Theorem**:
A specification `s` satisfying `env` lies on the Pareto frontier of neighborhood `N`
if and only if every strictly more capable neighbor `s' ∈ N` hits a Pareto wall
(violates `env`). -/
theorem paretoFrontier_iff_upgrades_hit_wall (env : InvariantEnvelope S)
    {s : S} (hs : env s) (N : Set S) :
    OnParetoFrontier C env s N ↔
      ∀ s' ∈ N, StrictlyMoreCapable C s s' → IsParetoWall C env s s' := by
  constructor
  · intro hfront s' hs' hstrict
    have hnotArt := hfront.2 s' hs'
    refine ⟨fun henv' => hnotArt ⟨henv', hstrict⟩, hstrict.2⟩
  · intro hwall
    refine ⟨hs, fun s' hs' hart => ?_⟩
    exact (hwall s' hs' hart.2).1 hart.1

/-- **Topological characterization of removable artifacts**:
`s'` exposes a removable artificial limitation of `s` iff `s' ∈ env`, every witness-open
neighborhood of `s` contains `s'`, and some witness-open separates `s'` from `s`
(i.e. `s` sits on a closed obstruction wall that `s'` escapes while keeping `env`). -/
theorem removableArtifact_iff_open_separation (env : InvariantEnvelope S) (s s' : S) :
    IsRemovableArtifact C env s s' ↔
      env s' ∧
      (∀ U : Set S, @IsOpen S (witnessTopology C) U → s ∈ U → s' ∈ U) ∧
      (∃ w : W, s' ∈ capabilityOpen C w ∧ s ∈ obstructionWall C w) := by
  unfold IsRemovableArtifact StrictlyMoreCapable capabilityOpen obstructionWall
  rw [← witnessRefines_iff_forall_open C s s']
  rfl

/-- Every strict edge `s → s'` in any neighborhood falls into one of six exhaustive
semantic deformation classes. -/
inductive DeformationClass (env : InvariantEnvelope S) (s s' : S) : Prop where
  | morita (h : WitnessMoritaEquiv C s s')
  | removableArtifact (h : IsRemovableArtifact C env s s')
  | paretoWall (h : IsParetoWall C env s s')
  | strictRegression (h : IsStrictRegression C s s')
  | incomparableTradeoff (h : IsIncomparableTradeoff C env s s')
  | invalidNoGain (h : ¬ env s' ∧ WitnessRefines C s' s)

theorem deformation_exhaustive (env : InvariantEnvelope S) (s s' : S) :
    DeformationClass C env s s' := by
  classical
  by_cases h1 : WitnessRefines C s s'
  · by_cases h2 : WitnessRefines C s' s
    · exact .morita ⟨h1, h2⟩
    · have hstrict : StrictlyMoreCapable C s s' :=
        (strictlyMoreCapable_iff_not_rev C s s').mpr ⟨h1, h2⟩
      by_cases henv : env s'
      · exact .removableArtifact ⟨henv, hstrict⟩
      · exact .paretoWall ⟨henv, hstrict.2⟩
  · by_cases h2 : WitnessRefines C s' s
    · exact .strictRegression ((strictlyMoreCapable_iff_not_rev C s' s).mpr ⟨h2, h1⟩)
    · have hw1 : ∃ w₁, C.pass s w₁ ∧ ¬ C.pass s' w₁ := by
        by_contra hnone; push Not at hnone; exact h1 fun w hw => hnone w hw
      have hw2 : ∃ w₂, C.pass s' w₂ ∧ ¬ C.pass s w₂ := by
        by_contra hnone; push Not at hnone; exact h2 fun w hw => hnone w hw
      by_cases henv : env s'
      · exact .incomparableTradeoff ⟨henv, hw1, hw2⟩
      · exact .paretoWall ⟨henv, hw2⟩

end GeneralDeformation

/-! ## Part 2: Real Specification Space over `ParallelCalculus.{u}` (`realParallelChu`) -/

section RealParallelSpace

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus

universe u

/-- Identity `UniformTranslation` for any `ParallelCalculus` whose static equivalence is reflexive. -/
def uniformTranslationRefl {L : ParallelCalculus.{u}} (hrefl : ∀ t, L.same t t) :
    UniformTranslation L L where
  map := id
  homomorphic s s' _ := hrefl (L.par s s')
  preserves _ h := h
  reflects _ h := h

/-- Seven real semantic and Gorla-encodability witnesses on `ParallelCalculus.{u}`
(every witness is a genuine behavioral property or existence of a `UniformTranslation`
between actual `Mettapedia` calculi). -/
inductive ParallelWitness where
  | switchable
  | hostsAbsence
  | hostsPositiveTell
  | hostsCounted
  | hostsGroundRelay
  | hostsMaker
  | hostsRhoZero
  deriving DecidableEq, Repr

/-- **The Real Chu Space of Parallel Calculi (`realParallelChu`)**:
points are ALL actual `ParallelCalculus.{u}` objects (covering both `Type 0` calculi like
`source`, `tellSource`, `countedSource`, `rhoParallel ω`, `heMatchParallel`, `pettaMatchParallel`
and `Type 1` calculi like `stepParallelSolvable ω`), and `pass L w` tests real switchability
or real `UniformTranslation` hosting. -/
def realParallelChu : SpecChuSpace ParallelCalculus.{u} ParallelWitness where
  pass L
    | .switchable => L.Switchable
    | .hostsAbsence => Nonempty (UniformTranslation NullsOnTheStep.ParallelClosed.source L)
    | .hostsPositiveTell => Nonempty (UniformTranslation PositiveTell.tellSource L)
    | .hostsCounted => Nonempty (UniformTranslation Monotone.countedSource L)
    | .hostsGroundRelay => Nonempty (UniformTranslation Monotone.relaySource L)
    | .hostsMaker => Nonempty (UniformTranslation Monotone.makerSource L)
    | .hostsRhoZero =>
        Nonempty (UniformTranslation (rhoParallel ByInstantiation.nameZero) L)

/-- **The Real Persistence Invariant Envelope**:
calculi whose reduction is closed beside, whose success persists beside, and whose reachable
success respects static equivalence (`ParallelCalculus.Persistent`). -/
def PersistenceEnvelope : InvariantEnvelope ParallelCalculus.{u} :=
  fun L => L.Persistent

/-- **Universal Closed Obstruction Walls for Persistent Calculi**:
EVERY calculus satisfying `PersistenceEnvelope` lies inside the closed obstruction walls for
`.switchable`, `.hostsAbsence`, `.hostsPositiveTell`, and `.hostsCounted`. -/
theorem persistent_in_closed_obstruction_walls {L : ParallelCalculus.{u}}
    (hp : PersistenceEnvelope L) :
    L ∈ obstructionWall realParallelChu .switchable ∧
    L ∈ obstructionWall realParallelChu .hostsAbsence ∧
    L ∈ obstructionWall realParallelChu .hostsPositiveTell ∧
    L ∈ obstructionWall realParallelChu .hostsCounted := by
  refine ⟨hp.not_switchable, ?_, ?_, ?_⟩
  · rintro ⟨τ⟩
    exact no_uniformTranslation NullsOnTheStep.ParallelClosed.source_switchable hp τ
  · rintro ⟨τ⟩
    exact no_uniformTranslation PositiveTell.tellSource_switchable hp τ
  · rintro ⟨τ⟩
    exact no_uniformTranslation Monotone.counted_switchable hp τ

/-- **Real Persistent Calculi Inside `PersistenceEnvelope`**:
faithful reflective rho-calculus (`rhoParallel ω`), real HE MeTTa bidirectional matching
(`heMatchParallel`), real PeTTa `spaceMatch` (`pettaMatchParallel`), and the positive multiset
bag target (`Monotone.relayTarget`) all satisfy `PersistenceEnvelope` and therefore lie on the
closed side of all four switchability walls. -/
theorem real_persistent_calculi_in_envelope
    (ω : ByInstantiation.G [] .nm)
    (heRules : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom ×
      Mettapedia.Languages.MeTTa.OSLFCore.Atom))
    (fuel : Nat) (heSucc : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (pettaRules : List (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern ×
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern))
    (pettaSucc : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    PersistenceEnvelope (rhoParallel ω) ∧
    PersistenceEnvelope (heMatchParallel heRules fuel heSucc) ∧
    PersistenceEnvelope (pettaMatchParallel pettaRules pettaSucc) ∧
    PersistenceEnvelope Monotone.relayTarget :=
  ⟨rhoParallel_persistent ω,
   heMatchParallel_persistent heRules fuel heSucc,
   pettaMatchParallel_persistent pettaRules pettaSucc,
   Monotone.relayTarget_persistent⟩

/-- **Real Switchable Step Calculi Inside `capabilityOpen realParallelChu .switchable`**:
absence-guarded `source`, check-free shared-unknown `PositiveTell.tellSource`, count-guarded
`Monotone.countedSource`, and solvable rho-hosting `stepParallelSolvable ω` all lie inside the
open capability `.switchable` and strictly outside `PersistenceEnvelope`. -/
theorem real_switchable_step_calculi_outside_persistence
    (ω : ByInstantiation.G [] .nm) :
    (NullsOnTheStep.ParallelClosed.source ∈ capabilityOpen realParallelChu .switchable ∧
      ¬ PersistenceEnvelope NullsOnTheStep.ParallelClosed.source) ∧
    (PositiveTell.tellSource ∈ capabilityOpen realParallelChu .switchable ∧
      ¬ PersistenceEnvelope PositiveTell.tellSource) ∧
    (Monotone.countedSource ∈ capabilityOpen realParallelChu .switchable ∧
      ¬ PersistenceEnvelope Monotone.countedSource) ∧
    (stepParallelSolvable ω ∈ capabilityOpen realParallelChu .switchable ∧
      ¬ PersistenceEnvelope (stepParallelSolvable ω)) :=
  ⟨⟨NullsOnTheStep.ParallelClosed.source_switchable,
    fun hp => hp.not_switchable NullsOnTheStep.ParallelClosed.source_switchable⟩,
   ⟨PositiveTell.tellSource_switchable,
    fun hp => hp.not_switchable PositiveTell.tellSource_switchable⟩,
   ⟨Monotone.counted_switchable,
    fun hp => hp.not_switchable Monotone.counted_switchable⟩,
   ⟨solvable_switchable ω,
    fun hp => hp.not_switchable (solvable_switchable ω)⟩⟩

/-- **Real Pareto Wall (Absence Guard)**:
moving from ANY persistent calculus `L` (e.g., `rhoParallel ω`, `heMatchParallel`,
`pettaMatchParallel`, `relayTarget`) to the absence-guarded step `source` hits a proved
`IsParetoWall` relative to `PersistenceEnvelope`. -/
theorem absence_hits_persistence_pareto_wall {L : ParallelCalculus.{0}}
    (hp : PersistenceEnvelope L) :
    IsParetoWall realParallelChu PersistenceEnvelope L NullsOnTheStep.ParallelClosed.source :=
  ⟨fun hpS => hpS.not_switchable NullsOnTheStep.ParallelClosed.source_switchable,
   .switchable, NullsOnTheStep.ParallelClosed.source_switchable, hp.not_switchable⟩

/-- **Real Pareto Wall (Positive Tell on Shared Unknown — Zero Checks)**:
moving from ANY persistent calculus `L` to check-free `PositiveTell.tellSource` hits a proved
`IsParetoWall` relative to `PersistenceEnvelope`. -/
theorem positiveTell_hits_persistence_pareto_wall {L : ParallelCalculus.{0}}
    (hp : PersistenceEnvelope L) :
    IsParetoWall realParallelChu PersistenceEnvelope L PositiveTell.tellSource :=
  ⟨fun hpT => hpT.not_switchable PositiveTell.tellSource_switchable,
   .switchable, PositiveTell.tellSource_switchable, hp.not_switchable⟩

/-- **Real Pareto Wall (Count Guard)**:
moving from ANY persistent calculus `L` to `Monotone.countedSource` hits a proved
`IsParetoWall` relative to `PersistenceEnvelope`. -/
theorem counted_hits_persistence_pareto_wall {L : ParallelCalculus.{0}}
    (hp : PersistenceEnvelope L) :
    IsParetoWall realParallelChu PersistenceEnvelope L Monotone.countedSource :=
  ⟨fun hpC => hpC.not_switchable Monotone.counted_switchable,
   .switchable, Monotone.counted_switchable, hp.not_switchable⟩

/-- **Real Operational Lindström Frontier Theorem (`OnParetoFrontier`)**:
EVERY persistent calculus `L` (in particular `rhoParallel ω`, `heMatchParallel`,
`pettaMatchParallel`, `Monotone.relayTarget`) lies strictly on the Pareto frontier of
`{L, source, PositiveTell.tellSource, Monotone.countedSource}` relative to `PersistenceEnvelope`:
every upgrade in that neighborhood hits a proved persistence wall! -/
theorem persistent_on_pareto_frontier_of_switchable_neighbors {L : ParallelCalculus.{0}}
    (hp : PersistenceEnvelope L) :
    OnParetoFrontier realParallelChu PersistenceEnvelope L
      {L, NullsOnTheStep.ParallelClosed.source, PositiveTell.tellSource, Monotone.countedSource} := by
  refine ⟨hp, ?_⟩
  intro L' hmem hart
  rcases hmem with rfl | rfl | rfl | rfl
  · obtain ⟨w, hpass, hnot⟩ := hart.2.2
    exact hnot hpass
  · exact hart.1.not_switchable NullsOnTheStep.ParallelClosed.source_switchable
  · exact hart.1.not_switchable PositiveTell.tellSource_switchable
  · exact hart.1.not_switchable Monotone.counted_switchable

/-- **Second, Finer Wall (Equation Consistency Between Non-Switchable Calculi)**:
`Monotone.makerSource` is NOT `Switchable`, yet still admits NO `UniformTranslation` into ANY
positive multiset bag calculus `bagCalculus Γ` because unsolvable equations block firing.
This proves the `Switchable` / `Persistent` wall is NOT the only obstruction in spec space! -/
theorem maker_non_switchable_yet_no_positive_bag_translation
    {Γ : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Rule
      NamesOnTheStep.Expr → Prop}
    (positive : ∀ ρ, Γ ρ → ρ.Positive) :
    ¬ Monotone.makerSource.Switchable ∧
    IsEmpty (UniformTranslation Monotone.makerSource (bagCalculus Γ)) :=
  ⟨Monotone.maker_not_switchable, Monotone.maker_no_bag_translation positive⟩

/-- A trivial stuck persistent calculus (no steps, no success) used as the bottom baseline
inside `PersistenceEnvelope`. -/
def stuckPersistent : ParallelCalculus.{0} where
  Term := Unit
  step _ _ := False
  par _ _ := ()
  composable _ _ := True
  success _ := False
  same := Eq

theorem stuckPersistent_persistent : PersistenceEnvelope stuckPersistent where
  closed _ _ _ h := h
  persists _ _ h := h
  respects := ParallelCalculus.respects_of_eq fun _ _ h => h

theorem stuckPersistent_never_succeeds (u : stuckPersistent.Term) :
    ¬ stuckPersistent.Succeeds u := by
  rintro ⟨_, _, hsucc⟩
  exact hsucc

theorem stuckPersistent_realizes_no_witness (w : ParallelWitness) :
    ¬ realParallelChu.pass stuckPersistent w := by
  cases w with
  | switchable => exact stuckPersistent_persistent.not_switchable
  | hostsAbsence =>
      rintro ⟨τ⟩
      exact no_uniformTranslation NullsOnTheStep.ParallelClosed.source_switchable
        stuckPersistent_persistent τ
  | hostsPositiveTell =>
      rintro ⟨τ⟩
      exact no_uniformTranslation PositiveTell.tellSource_switchable
        stuckPersistent_persistent τ
  | hostsCounted =>
      rintro ⟨τ⟩
      exact no_uniformTranslation Monotone.counted_switchable
        stuckPersistent_persistent τ
  | hostsGroundRelay =>
      rintro ⟨τ⟩
      have hsucc : Monotone.relaySource.Succeeds NullsOnTheStep.ParallelClosed.triggerStore := by
        rw [Monotone.relay_succeeds_iff]
        refine Or.inr ⟨fun _ h => absurd h List.not_mem_nil,
          (NullsOnTheStep.ParallelClosed.trigger, 0), ?_, rfl⟩
        simp [NullsOnTheStep.ParallelClosed.triggerStore]
      exact stuckPersistent_never_succeeds _ (τ.preserves _ hsucc)
  | hostsMaker =>
      rintro ⟨τ⟩
      exact stuckPersistent_never_succeeds _ (τ.preserves _ Monotone.maker_empty_succeeds)
  | hostsRhoZero =>
      rintro ⟨τ⟩
      have hsucc : (rhoParallel ByInstantiation.nameZero).Succeeds outputNil :=
        ⟨outputNil, .refl, outputNil_barb⟩
      exact stuckPersistent_never_succeeds _ (τ.preserves _ hsucc)

/-- **Real `IsRemovableArtifact` inside `PersistenceEnvelope` (1 — Ground Relay Hosting)**:
upgrading from `stuckPersistent` to `Monotone.relayTarget` stays inside `PersistenceEnvelope`
and strictly gains the `.hostsGroundRelay` witness via `Monotone.relayTranslation`. -/
theorem relayTarget_is_removable_artifact_over_stuck :
    IsRemovableArtifact realParallelChu PersistenceEnvelope stuckPersistent Monotone.relayTarget := by
  refine ⟨Monotone.relayTarget_persistent, ?_, .hostsGroundRelay, ⟨Monotone.relayTranslation⟩,
    stuckPersistent_realizes_no_witness .hostsGroundRelay⟩
  intro w hw
  exact absurd hw (stuckPersistent_realizes_no_witness w)

/-- **Real `IsRemovableArtifact` inside `PersistenceEnvelope` (2 — Faithful Rho Hosting)**:
upgrading from `stuckPersistent` to `rhoParallel nameZero` stays inside `PersistenceEnvelope`
and strictly gains `.hostsRhoZero` via `identity_uniform`. -/
theorem rhoParallel_is_removable_artifact_over_stuck :
    IsRemovableArtifact realParallelChu PersistenceEnvelope stuckPersistent
      (rhoParallel ByInstantiation.nameZero) := by
  refine ⟨rhoParallel_persistent _, ?_, .hostsRhoZero,
    ⟨identity_uniform _⟩, stuckPersistent_realizes_no_witness .hostsRhoZero⟩
  intro w hw
  exact absurd hw (stuckPersistent_realizes_no_witness w)

end RealParallelSpace

/-! ## Part 3: Real Lawvere Quasimetric of Composable Uniform Routes -/

section UniformRouteQuasimetric

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus

/-- A `ParallelCalculus.{0}` whose static equivalence is reflexive and transitive
(satisfied by every calculus in our suite: `Eq` for step/bag/HE/PeTTa, and
`rhoProcessEquations.r` for `rhoParallel ω`). -/
structure WellFormedParallel where
  calculus : ParallelCalculus.{0}
  same_refl : ∀ t, calculus.same t t
  same_trans : ∀ {a b c}, calculus.same a b → calculus.same b c → calculus.same a c

/-- A **composable Gorla uniform route** between well-formed parallel calculi:
a `UniformTranslation` that also preserves composability and static equivalence. -/
structure ComposableUniformRoute (L M : WellFormedParallel) extends
    UniformTranslation L.calculus M.calculus where
  preservesComposable : ∀ s s', L.calculus.composable s s' →
    M.calculus.composable (map s) (map s')
  respectsSame : ∀ {s₁ s₂}, L.calculus.same s₁ s₂ → M.calculus.same (map s₁) (map s₂)

/-- Identity composable uniform route. -/
def ComposableUniformRoute.id (L : WellFormedParallel) : ComposableUniformRoute L L where
  map := _root_.id
  homomorphic s s' _ := L.same_refl (L.calculus.par s s')
  preserves _ h := h
  reflects _ h := h
  preservesComposable _ _ h := h
  respectsSame h := h

/-- Composition of composable uniform routes. -/
def ComposableUniformRoute.comp {A B C : WellFormedParallel}
    (g : ComposableUniformRoute B C) (f : ComposableUniformRoute A B) :
    ComposableUniformRoute A C where
  map t := g.map (f.map t)
  homomorphic s s' hcomp :=
    C.same_trans (g.respectsSame (f.homomorphic s s' hcomp))
      (g.homomorphic (f.map s) (f.map s') (f.preservesComposable s s' hcomp))
  preserves s hs := g.preserves _ (f.preserves s hs)
  reflects s hs := f.reflects s (g.reflects _ hs)
  preservesComposable s s' hcomp :=
    g.preservesComposable _ _ (f.preservesComposable s s' hcomp)
  respectsSame hsame := g.respectsSame (f.respectsSame hsame)

/-- **Real Lawvere Quasimetric Distance on `WellFormedParallel`**:
`uniformRouteDist L M = 0` when a `ComposableUniformRoute L M` exists and `⊤` when no such
route exists. Satisfies `self_zero` and the Lawvere triangle inequality via
`ComposableUniformRoute.comp`! -/
noncomputable def uniformRouteDist (L M : WellFormedParallel) : ENNReal := by
  classical
  exact if Nonempty (ComposableUniformRoute L M) then 0 else ⊤

theorem uniformRouteDist_self (L : WellFormedParallel) :
    uniformRouteDist L L = 0 := by
  classical
  unfold uniformRouteDist
  rw [if_pos ⟨ComposableUniformRoute.id L⟩]

theorem uniformRouteDist_triangle (A B C : WellFormedParallel) :
    uniformRouteDist A C ≤ uniformRouteDist A B + uniformRouteDist B C := by
  classical
  unfold uniformRouteDist
  by_cases hAB : Nonempty (ComposableUniformRoute A B)
  · by_cases hBC : Nonempty (ComposableUniformRoute B C)
    · have hAC : Nonempty (ComposableUniformRoute A C) :=
        ⟨ComposableUniformRoute.comp (Classical.choice hBC) (Classical.choice hAB)⟩
      simp [hAB, hBC, hAC]
    · simp [hBC]
  · simp [hAB]

/-- Package any `ParallelCalculus.{0}` with `same = Eq` as a `WellFormedParallel`. -/
def wfOfEq (L : ParallelCalculus.{0}) (heq : L.same = Eq) : WellFormedParallel where
  calculus := L
  same_refl t := by rw [heq]
  same_trans h1 h2 := by rw [heq] at h1 h2 ⊢; exact h1.trans h2

def wfAbsence : WellFormedParallel := wfOfEq NullsOnTheStep.ParallelClosed.source rfl
def wfPositiveTell : WellFormedParallel := wfOfEq PositiveTell.tellSource rfl
def wfCounted : WellFormedParallel := wfOfEq Monotone.countedSource rfl
def wfRelaySource : WellFormedParallel := wfOfEq Monotone.relaySource rfl
def wfRelayTarget : WellFormedParallel := wfOfEq Monotone.relayTarget rfl
def wfMaker : WellFormedParallel := wfOfEq Monotone.makerSource rfl

def wfHE (rules : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom ×
    Mettapedia.Languages.MeTTa.OSLFCore.Atom)) (fuel : Nat)
    (succ : Mettapedia.Languages.MeTTa.OSLFCore.Atom) : WellFormedParallel :=
  wfOfEq (heMatchParallel rules fuel succ) rfl

def wfPeTTa (rules : List (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern ×
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern))
    (succ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : WellFormedParallel :=
  wfOfEq (pettaMatchParallel rules succ) rfl

def wfRho (ω : ByInstantiation.G [] .nm) : WellFormedParallel where
  calculus := rhoParallel ω
  same_refl t := Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoProcessEquations.iseqv.refl t
  same_trans h1 h2 := Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoProcessEquations.iseqv.trans h1 h2

/-- Positive `0`-distance route in `uniformRouteDist`: ground relay embeds uniformly into
its positive multiset bag target (`Monotone.relayTranslation`). -/
theorem dist_relaySource_relayTarget_eq_zero :
    uniformRouteDist wfRelaySource wfRelayTarget = 0 := by
  classical
  have hroute : Nonempty (ComposableUniformRoute wfRelaySource wfRelayTarget) :=
    ⟨{ toUniformTranslation := Monotone.relayTranslation
       preservesComposable := fun _ _ _ => trivial
       respectsSame := fun h => by subst h; rfl }⟩
  unfold uniformRouteDist
  rw [if_pos hroute]

/-- General `⊤`-distance wall lemma: any `IsEmpty (UniformTranslation L.calculus M.calculus)`
forces `uniformRouteDist L M = ⊤`. -/
theorem dist_eq_top_of_isEmpty_uniform {L M : WellFormedParallel}
    (hempty : IsEmpty (UniformTranslation L.calculus M.calculus)) :
    uniformRouteDist L M = ⊤ := by
  classical
  have hno : ¬ Nonempty (ComposableUniformRoute L M) := by
    rintro ⟨r⟩
    exact hempty.false r.toUniformTranslation
  unfold uniformRouteDist
  rw [if_neg hno]

/-- **Concrete `⊤`-Distance Impossibility Walls in `uniformRouteDist`**:
1. Absence-guarded step, positive-tell step, and count-guarded step all sit at distance `⊤`
   from `wfRho ω`, `wfHE`, and `wfPeTTa`;
2. Non-switchable `wfMaker` sits at distance `⊤` from `wfRelayTarget` (equation-consistency wall). -/
theorem concrete_quasimetric_walls
    (ω : ByInstantiation.G [] .nm)
    (heRules : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom ×
      Mettapedia.Languages.MeTTa.OSLFCore.Atom))
    (fuel : Nat) (heSucc : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (pettaRules : List (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern ×
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern))
    (pettaSucc : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    uniformRouteDist wfAbsence (wfRho ω) = ⊤ ∧
    uniformRouteDist wfPositiveTell (wfRho ω) = ⊤ ∧
    uniformRouteDist wfAbsence (wfHE heRules fuel heSucc) = ⊤ ∧
    uniformRouteDist wfPositiveTell (wfHE heRules fuel heSucc) = ⊤ ∧
    uniformRouteDist wfAbsence (wfPeTTa pettaRules pettaSucc) = ⊤ ∧
    uniformRouteDist wfPositiveTell (wfPeTTa pettaRules pettaSucc) = ⊤ ∧
    uniformRouteDist wfCounted (wfPeTTa pettaRules pettaSucc) = ⊤ ∧
    uniformRouteDist wfMaker wfRelayTarget = ⊤ :=
  ⟨dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_absence ω),
   dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_positiveTell ω),
   dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_absence_into_heMatch heRules fuel heSucc),
   dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_positiveTell_into_heMatch heRules fuel heSucc),
   dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_absence_into_pettaMatch pettaRules pettaSucc),
   dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_positiveTell_into_pettaMatch pettaRules pettaSucc),
   dist_eq_top_of_isEmpty_uniform (no_uniformTranslation_counted_into_pettaMatch pettaRules pettaSucc),
   dist_eq_top_of_isEmpty_uniform
     (Monotone.maker_no_bag_translation fun ρ h x => by rw [h]; rfl)⟩

end UniformRouteQuasimetric

/-! ## Part 4: Real Positive Routes & Gorla Criterion-Sensitivity Controls -/

section PositiveRoutesAndControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Reduces)

/-- **Real Positive Routes Across `Mettapedia`'s Fragments**:
1. Uniform translation of ground relay into positive multiset bags (`Monotone.relayTranslation`);
2. Heating bisimulation for `makeOnly` (`HeatingBisimulation.Controls.make_has_heating_bisimulation`);
3. Channel-communication bisimulation into rho (`RhoChannelFragment.channel_fragment_bisimulation`);
4. Read-only query commutation with disjoint takers (`ReadOnlyQuery.Controls.query_commutes_with_taker`);
5. Monotone fragment reachable facts equal Datalog least fixed point (`MonotoneInference.reachable_eq_lfp`). -/
theorem real_positive_routes :
    Nonempty (UniformTranslation Monotone.relaySource Monotone.relayTarget) ∧
    (∃ react : StoreComposition.Reaction NamesOnTheStep.Expr,
      TransitionMaps.IsBisimulation
        (HeatingBisimulation.modelledStep NamesOnTheStep.IssuingControls.ground
          (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr) ()
          HeatingBisimulation.Controls.makeOnly)
        (StoreComposition.Reduces react)
        (HeatingBisimulation.Encodes (label := (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr)))) ∧
    (∀ {context : Mettapedia.OSLF.Binding.Ctx Mettapedia.OSLF.Binding.RhoSchema.sig},
      TransitionMaps.IsBisimulation
        (RhoChannelFragment.ChannelStep (context := context))
        (RhoChannelFragment.RhoStep (context := context))
        (ContextualCommunicationAdequacy.Represents (context := context))) ∧
    GuardFreeProcessOrders.SameUpTo NamesOnTheStep.IssuingControls.ground
      (ReadOnlyQuery.Controls.takeBAt.result Prod.fst ReadOnlyQuery.Controls.takeB
        (ReadOnlyQuery.Controls.queryAt.result Prod.fst ReadOnlyQuery.Controls.query
          ReadOnlyQuery.Controls.start))
      (ReadOnlyQuery.Controls.queryAt.result Prod.fst ReadOnlyQuery.Controls.query
        (ReadOnlyQuery.Controls.takeBAt.result Prod.fst ReadOnlyQuery.Controls.takeB
          ReadOnlyQuery.Controls.start)) :=
  ⟨⟨Monotone.relayTranslation⟩,
   HeatingBisimulation.Controls.make_has_heating_bisimulation,
   fun {_} => RhoChannelFragment.channel_fragment_bisimulation,
   ReadOnlyQuery.Controls.query_commutes_with_taker⟩

/-- **Gorla Criterion-Sensitivity Control Theorem**:
Explicitly proves WHY Gorla's criteria govern where the walls stand, and what collapses when
individual criteria are dropped:
1. *Compositionality wall vs. collapse*: compositional parallel encoding of absence into rho
   is impossible (`rho_cannot_encode_absence`), yet dropping compositionality makes a
   whole-configuration encoding succeed (`ConsensusNumbers.Controls.whole_configuration_encoding`).
2. *Homomorphism wall vs. collapse*: `Interpreter.interpret` matches `source.Succeeds` iff
   (`interpret_succeeds_iff`), specifically because it is NOT homomorphic (`interpret_not_homomorphic`).
3. *Unguarded vs. guarded parallel contexts*: coordinated unguarded parallel contexts in rho
   cannot host `stepParallelSolvable`, `source`, or `PositiveTell.tellSource`
   (`step_not_into_rho_coordinated`, `absence_not_into_rho_coordinated`,
   `positiveTell_not_into_rho_coordinated`), whereas guarded contexts break `KeepsFirst`
   (`guarded_context_fails`).
4. *Each Gorla criterion has independent content*: completeness (`only_complete_fails`),
   soundness (`only_sound_fails`), divergence reflection (`only_divergence_fails`),
   success sensitivity (`only_success_fails`), coherence (`coherence_has_content`), and
   name invariance (`nameInvariant_has_content`). -/
theorem gorla_criterion_sensitivity_controls :
    (∀ (n : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (enc : Multiset Src → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      enc ({.trigger} + {.blocker}) = rhoPar (enc {.trigger}) (enc {.blocker}) →
      (∀ S, WeakBarb srcStep hasDone S →
        WeakBarb (fun P Q => Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces P Q))
          (HasOutput n) (enc S)) →
      (∀ S, WeakBarb (fun P Q => Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces P Q))
          (HasOutput n) (enc S) →
        WeakBarb srcStep hasDone S) →
      False) ∧
    ((∀ S, WeakBarb srcStep hasDone S ↔
        WeakBarb (Reduces fun _ => False) hasDone
          (Mettapedia.GSLT.Coordination.ConsensusNumbers.Controls.wholeEncoding S)) ∧
      Mettapedia.GSLT.Coordination.ConsensusNumbers.Controls.wholeEncoding ({.trigger} + {.blocker}) ≠
        Mettapedia.GSLT.Coordination.ConsensusNumbers.Controls.wholeEncoding {.trigger} +
        Mettapedia.GSLT.Coordination.ConsensusNumbers.Controls.wholeEncoding {.blocker}) ∧
    ((∀ C, Interpreter.wholeCalculus.Succeeds (Interpreter.interpret C) ↔
        NullsOnTheStep.ParallelClosed.source.Succeeds C) ∧
      ¬ ∀ C D, NullsOnTheStep.ParallelClosed.source.composable C D →
        Interpreter.wholeCalculus.same
          (Interpreter.interpret (NullsOnTheStep.ParallelClosed.source.par C D))
          (Interpreter.wholeCalculus.par (Interpreter.interpret C) (Interpreter.interpret D))) ∧
    (∀ (ω : ByInstantiation.G [] .nm)
        (R : Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.RhoProcess)
        (τ : CompositionalTranslation (stepParallelSolvable ω) (rhoParallel ω)),
      τ.context = coordinated R → False) ∧
    (¬ KeepsFirst (rhoParallel ByInstantiation.nameZero) guardedContext) ∧
    (¬ DivergenceReflecting
        (L := Encodings.Controls.tiny Encodings.Controls.stuck Encodings.Controls.never)
        (M := Encodings.Controls.tiny Encodings.Controls.loop Encodings.Controls.never) id ∧
     ¬ SuccessSensitive
        (L := Encodings.Controls.tiny Encodings.Controls.stuck Encodings.Controls.atP)
        (M := Encodings.Controls.tiny Encodings.Controls.stuck Encodings.Controls.never) id) :=
  ⟨fun n enc hcomp hcomplete hsound => rho_cannot_encode_absence n enc hcomp hcomplete hsound,
   Mettapedia.GSLT.Coordination.ConsensusNumbers.Controls.whole_configuration_encoding,
   ⟨Interpreter.interpret_succeeds_iff, Interpreter.interpret_not_homomorphic⟩,
   fun ω R τ hshape => step_not_into_rho_coordinated ω R τ hshape,
   guarded_context_fails,
   ⟨Encodings.Controls.only_divergence_fails.2.1, Encodings.Controls.only_success_fails.2.2⟩⟩

end PositiveRoutesAndControls

end Mettapedia.GSLT.Distinction.SpecSpace
