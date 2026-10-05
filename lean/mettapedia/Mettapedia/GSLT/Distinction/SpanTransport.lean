import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Logic.ObservationSpans
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Two-sided transport of reduction spans by relations

`ObservationSpans.SpanMap` observes a reduction span through a function; its
source lifting is exactly naturality of the future diamond
(`SpanMap.sourceLifts_iff_diamond`) and its target lifting exactly naturality of
the past box (`SpanMap.targetLifts_iff_box`).  `ProductiveBlocks.CostSimulation`
relates the actual states of two machines by a relation that need not be a
function, with forward and backward simulations as separate laws.  This module
joins the two: relations between reduction spans, with four separate lifting
laws.

* **The four laws of a state relation** (`SourceForth`, `SourceBack`,
  `TargetForth`, `TargetBack`).  Forth laws carry an event of the first span to
  a related event of the second, back laws lift an event of the second span;
  source laws match outgoing events, target laws incoming ones.  Each law is
  exactly one modal transfer (`sourceForth_iff_diamond`,
  `sourceBack_iff_diamond`, `targetForth_iff_box`, `targetBack_iff_box`), so
  preservation and reflection of the future diamond need the two source laws
  (`diamond_related`) and those of the past box the two target laws
  (`box_related`).  The laws hold for identities, compose, and exchange under
  the converse.
* **Functions are the special case** (`spanMap_sourceForth`,
  `spanMap_sourceBack_iff`, `spanMap_targetBack_iff`): for the graph of a
  `SpanMap` both forth laws hold, the source back law is `SourceLifts` and the
  target back law is `TargetLifts`; `SpanMap.diamond_pullback` is recovered
  through the relation (`spanMap_diamond`).
* **Event relations** (`SpanRelation`).  A relation of states together with a
  relation of event occurrences whose endpoints are related.  The occurrence
  laws imply the state laws.  Readings of events (labels, results, faults,
  provenance) are kept when related events read alike (`Keeps`); then every
  labelled tense formula, with future and past modalities, is preserved and
  reflected by the four occurrence laws (`sat_related`), and every future
  formula by the two source laws alone (`sat_related_future`).
* **Parallel occurrences** (`OutFibresMatch`, `outgoing_card_eq`).  A relation
  keeps the number of parallel occurrences with each reading exactly when the
  related outgoing fibres correspond one to one; the modal laws do not give
  this (the controls).
* **Contexts and substitutions** (`Congruent`): congruence of a relation for a
  pair of maps acting on both sides; it holds for identities, composes in both
  arguments, and carries related predicates to related predicates.  The
  quotient of the saturated relative behaviour is congruent for every
  admissible context and every respecting substitution
  (`relative_congruent_context`, `relative_congruent_substitution`).
* **The two-sided observation** (`twoSided`): each labelled action of a
  `HennessyMilner.System` observed forward and backward.  Its bisimulations are
  the bisimulations that also match pasts (`twoSided_isBisimulation_iff`); it
  branches finitely exactly when successors and predecessors both do
  (`twoSided_imageFiniteModulo_iff`), the two separate requirements of its
  Hennessy–Milner theorem (`twoSided_logicallyEquivalent_iff_bisimilar`).  With
  the explicit agreement of the system's actions with the GSLT's steps
  (`StepAgreement`), a bisimulation gives the two source laws on the GSLT's
  reduction span and a two-sided one also the two target laws
  (`sourceLaws_of_isBisimulation`, `targetLaws_of_twoSided`, `twoSided_gsltBox`).
* **Restriction-natural event observations** (`eventObservation_sourceLifts_iff`,
  `eventObservation_targetLifts_iff`): the lifting laws of
  `Presheaf.EventObservation` are the back laws at every stage.
* **Cost simulations** (`ProductiveBlocks.CostSimulation.run_related`).  A source
  run that does not end stuck is matched within `cost` times its fuel by a target
  run publishing the same events, with a related outcome (`OutcomeRel`): the same
  verdict, faults, the same request with related saved continuations, or related
  residuals; the observations are equal, not only prefixes (`observe_eq`).  On
  the segment spans of the two machines a simulation gives the source forth law
  and a simulation the other way the source back law
  (`segment_sourceForthOcc`, `segment_sourceBackOcc`), so every future formula
  over published events agrees (`future_related`).  No past law follows (the
  controls).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpanTransport

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.ObservationSpans

universe u v w e f g uA uL

/-! ## The four lifting laws of a state relation -/

section Endpoints

variable {X : Type u} {Y : Type v} {Z : Type w}
variable (A : ReductionSpan.{u, e} X) (B : ReductionSpan.{v, f} Y) (C : ReductionSpan.{w, g} Z)

/-- **Source forth**: every outgoing event at a related state of `A` is matched by
an outgoing event of `B`, with related targets. -/
def SourceForth (R : X → Y → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ a : A.Edge, A.source a = x →
    ∃ b : B.Edge, B.source b = y ∧ R (A.target a) (B.target b)

/-- **Source back**: every outgoing event at a related state of `B` lifts to an
outgoing event of `A`, with related targets. -/
def SourceBack (R : X → Y → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ b : B.Edge, B.source b = y →
    ∃ a : A.Edge, A.source a = x ∧ R (A.target a) (B.target b)

/-- **Target forth**: every incoming event at a related state of `A` is matched
by an incoming event of `B`, with related sources. -/
def TargetForth (R : X → Y → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ a : A.Edge, A.target a = x →
    ∃ b : B.Edge, B.target b = y ∧ R (A.source a) (B.source b)

/-- **Target back**: every incoming event at a related state of `B` lifts to an
incoming event of `A`, with related sources. -/
def TargetBack (R : X → Y → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∀ b : B.Edge, B.target b = y →
    ∃ a : A.Edge, A.target a = x ∧ R (A.source a) (B.source b)

variable {A B C}

/-- The relational image of a predicate. -/
def push (R : X → Y → Prop) (φ : X → Prop) : Y → Prop := fun y => ∃ x, R x y ∧ φ x

/-- The relational preimage of a predicate. -/
def pull (R : X → Y → Prop) (ψ : Y → Prop) : X → Prop := fun x => ∃ y, R x y ∧ ψ y

/-- **Source forth is exactly preservation of the future diamond.** -/
theorem sourceForth_iff_diamond (R : X → Y → Prop) :
    SourceForth A B R ↔ ∀ (φ : X → Prop) ⦃x y⦄, R x y →
      derivedDiamond A φ x → derivedDiamond B (push R φ) y := by
  constructor
  · rintro forth φ x y related ⟨a, sourceEq, holds⟩
    obtain ⟨b, sourceEq', relatedTargets⟩ := forth related a sourceEq
    exact ⟨b, sourceEq', show push R φ (B.target b) from ⟨A.target a, relatedTargets, holds⟩⟩
  · intro natural x y related a sourceEq
    obtain ⟨b, sourceEq', x', relatedTargets, same⟩ :=
      natural (fun x' => x' = A.target a) related ⟨a, sourceEq, rfl⟩
    exact ⟨b, sourceEq', same ▸ relatedTargets⟩

/-- **Source back is exactly reflection of the future diamond.** -/
theorem sourceBack_iff_diamond (R : X → Y → Prop) :
    SourceBack A B R ↔ ∀ (ψ : Y → Prop) ⦃x y⦄, R x y →
      derivedDiamond B ψ y → derivedDiamond A (pull R ψ) x := by
  constructor
  · rintro back ψ x y related ⟨b, sourceEq, holds⟩
    obtain ⟨a, sourceEq', relatedTargets⟩ := back related b sourceEq
    exact ⟨a, sourceEq', show pull R ψ (A.target a) from ⟨B.target b, relatedTargets, holds⟩⟩
  · intro natural x y related b sourceEq
    obtain ⟨a, sourceEq', y', relatedTargets, same⟩ :=
      natural (fun y' => y' = B.target b) related ⟨b, sourceEq, rfl⟩
    exact ⟨a, sourceEq', same ▸ relatedTargets⟩

/-- **Target forth is exactly reflection of the past box.** -/
theorem targetForth_iff_box (R : X → Y → Prop) :
    TargetForth A B R ↔ ∀ (ψ : Y → Prop) ⦃x y⦄, R x y →
      derivedBox B ψ y → derivedBox A (pull R ψ) x := by
  constructor
  · intro forth ψ x y related holds a targetEq
    obtain ⟨b, targetEq', relatedSources⟩ := forth related a targetEq
    exact ⟨B.source b, relatedSources, holds b targetEq'⟩
  · intro natural x y related a targetEq
    let incoming : Y → Prop := fun y' => ∃ b : B.Edge, B.target b = y ∧ B.source b = y'
    obtain ⟨y', relatedSources, b, targetEq', same⟩ :=
      natural incoming related (fun b targetEq' => ⟨b, targetEq', rfl⟩) a targetEq
    exact ⟨b, targetEq', same ▸ relatedSources⟩

/-- **Target back is exactly preservation of the past box.**  The necessity
direction tests the predicate of actual predecessors; no excluded middle is
used. -/
theorem targetBack_iff_box (R : X → Y → Prop) :
    TargetBack A B R ↔ ∀ (φ : X → Prop) ⦃x y⦄, R x y →
      derivedBox A φ x → derivedBox B (push R φ) y := by
  constructor
  · intro back φ x y related holds b targetEq
    obtain ⟨a, targetEq', relatedSources⟩ := back related b targetEq
    exact ⟨A.source a, relatedSources, holds a targetEq'⟩
  · intro natural x y related b targetEq
    let incoming : X → Prop := fun x' => ∃ a : A.Edge, A.target a = x ∧ A.source a = x'
    obtain ⟨x', relatedSources, a, targetEq', same⟩ :=
      natural incoming related (fun a targetEq' => ⟨a, targetEq', rfl⟩) b targetEq
    exact ⟨a, targetEq', same ▸ relatedSources⟩

/-- Two predicates that read alike on related states. -/
def Related (R : X → Y → Prop) (φ : X → Prop) (ψ : Y → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → (φ x ↔ ψ y)

/-- **The future diamond is preserved and reflected by the two source laws.** -/
theorem diamond_related {R : X → Y → Prop} (forth : SourceForth A B R) (back : SourceBack A B R)
    {φ : X → Prop} {ψ : Y → Prop} (related : Related R φ ψ) :
    Related R (derivedDiamond A φ) (derivedDiamond B ψ) := by
  intro x y relatedStates
  constructor
  · rintro ⟨a, sourceEq, holds⟩
    obtain ⟨b, sourceEq', relatedTargets⟩ := forth relatedStates a sourceEq
    exact ⟨b, sourceEq', show ψ (B.target b) from (related relatedTargets).mp holds⟩
  · rintro ⟨b, sourceEq, holds⟩
    obtain ⟨a, sourceEq', relatedTargets⟩ := back relatedStates b sourceEq
    exact ⟨a, sourceEq', show φ (A.target a) from (related relatedTargets).mpr holds⟩

/-- **The past box is preserved and reflected by the two target laws.** -/
theorem box_related {R : X → Y → Prop} (forth : TargetForth A B R) (back : TargetBack A B R)
    {φ : X → Prop} {ψ : Y → Prop} (related : Related R φ ψ) :
    Related R (derivedBox A φ) (derivedBox B ψ) := by
  intro x y relatedStates
  constructor
  · intro holds b targetEq
    obtain ⟨a, targetEq', relatedSources⟩ := back relatedStates b targetEq
    exact (related relatedSources).mp (holds a targetEq')
  · intro holds a targetEq
    obtain ⟨b, targetEq', relatedSources⟩ := forth relatedStates a targetEq
    exact (related relatedSources).mpr (holds b targetEq')

/-! ### Identity, composition and the converse -/

variable (A) in
theorem sourceForth_eq : SourceForth A A Eq := fun _ _ same a sourceEq =>
  ⟨a, sourceEq.trans same, rfl⟩

variable (A) in
theorem sourceBack_eq : SourceBack A A Eq := fun _ _ same b sourceEq =>
  ⟨b, sourceEq.trans same.symm, rfl⟩

variable (A) in
theorem targetForth_eq : TargetForth A A Eq := fun _ _ same a targetEq =>
  ⟨a, targetEq.trans same, rfl⟩

variable (A) in
theorem targetBack_eq : TargetBack A A Eq := fun _ _ same b targetEq =>
  ⟨b, targetEq.trans same.symm, rfl⟩

/-- Relational composition. -/
def compose (R : X → Y → Prop) (S : Y → Z → Prop) : X → Z → Prop :=
  fun x z => ∃ y, R x y ∧ S y z

theorem SourceForth.comp {R : X → Y → Prop} {S : Y → Z → Prop} (first : SourceForth A B R)
    (second : SourceForth B C S) : SourceForth A C (compose R S) := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ a sourceEq
  obtain ⟨b, sourceEq', relatedTargets⟩ := first relatedFirst a sourceEq
  obtain ⟨c, sourceEq'', relatedTargets'⟩ := second relatedSecond b sourceEq'
  exact ⟨c, sourceEq'', B.target b, relatedTargets, relatedTargets'⟩

theorem SourceBack.comp {R : X → Y → Prop} {S : Y → Z → Prop} (first : SourceBack A B R)
    (second : SourceBack B C S) : SourceBack A C (compose R S) := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ c sourceEq
  obtain ⟨b, sourceEq', relatedTargets'⟩ := second relatedSecond c sourceEq
  obtain ⟨a, sourceEq'', relatedTargets⟩ := first relatedFirst b sourceEq'
  exact ⟨a, sourceEq'', B.target b, relatedTargets, relatedTargets'⟩

theorem TargetForth.comp {R : X → Y → Prop} {S : Y → Z → Prop} (first : TargetForth A B R)
    (second : TargetForth B C S) : TargetForth A C (compose R S) := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ a targetEq
  obtain ⟨b, targetEq', relatedSources⟩ := first relatedFirst a targetEq
  obtain ⟨c, targetEq'', relatedSources'⟩ := second relatedSecond b targetEq'
  exact ⟨c, targetEq'', B.source b, relatedSources, relatedSources'⟩

theorem TargetBack.comp {R : X → Y → Prop} {S : Y → Z → Prop} (first : TargetBack A B R)
    (second : TargetBack B C S) : TargetBack A C (compose R S) := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ c targetEq
  obtain ⟨b, targetEq', relatedSources'⟩ := second relatedSecond c targetEq
  obtain ⟨a, targetEq'', relatedSources⟩ := first relatedFirst b targetEq'
  exact ⟨a, targetEq'', B.source b, relatedSources, relatedSources'⟩

/-- Forth and back laws exchange under the converse. -/
theorem sourceForth_iff_flip (R : X → Y → Prop) : SourceForth A B R ↔ SourceBack B A (flip R) :=
  ⟨fun forth _ _ related a sourceEq => forth related a sourceEq,
    fun back _ _ related a sourceEq => back related a sourceEq⟩

theorem targetForth_iff_flip (R : X → Y → Prop) : TargetForth A B R ↔ TargetBack B A (flip R) :=
  ⟨fun forth _ _ related a targetEq => forth related a targetEq,
    fun back _ _ related a targetEq => back related a targetEq⟩

/-! ### Functions: the graph of a span map -/

/-- The graph of a span map's state function. -/
def graph (map : SpanMap A B) : X → Y → Prop := fun x y => map.states x = y

theorem spanMap_sourceForth (map : SpanMap A B) : SourceForth A B (graph map) := by
  intro x y related a sourceEq
  refine ⟨map.events a, ?_, (map.target_comm a).symm⟩
  rw [map.source_comm, sourceEq]
  exact related

theorem spanMap_targetForth (map : SpanMap A B) : TargetForth A B (graph map) := by
  intro x y related a targetEq
  refine ⟨map.events a, ?_, (map.source_comm a).symm⟩
  rw [map.target_comm, targetEq]
  exact related

/-- **For a span map, source back is source lifting.** -/
theorem spanMap_sourceBack_iff (map : SpanMap A B) : SourceBack A B (graph map) ↔ map.SourceLifts := by
  constructor
  · intro back state event sourceEq
    exact back (rfl : graph map state (map.states state)) event sourceEq
  · rintro lifts x _ rfl b sourceEq
    exact lifts x b sourceEq

/-- **For a span map, target back is target lifting.** -/
theorem spanMap_targetBack_iff (map : SpanMap A B) : TargetBack A B (graph map) ↔ map.TargetLifts := by
  constructor
  · intro back state event targetEq
    exact back (rfl : graph map state (map.states state)) event targetEq
  · rintro lifts x _ rfl b targetEq
    exact lifts x b targetEq

/-- `SpanMap.diamond_pullback`, recovered through the relation. -/
theorem spanMap_diamond (map : SpanMap A B) (lifts : map.SourceLifts) (ψ : Y → Prop) (x : X) :
    derivedDiamond B ψ (map.states x) ↔ derivedDiamond A (ψ ∘ map.states) x :=
  ((diamond_related (spanMap_sourceForth map) ((spanMap_sourceBack_iff map).mpr lifts)
    (φ := ψ ∘ map.states) (ψ := ψ) (by rintro x _ rfl; exact Iff.rfl))
    (rfl : graph map x (map.states x))).symm

/-- `SpanMap.box_pullback`, recovered through the relation. -/
theorem spanMap_box (map : SpanMap A B) (lifts : map.TargetLifts) (ψ : Y → Prop) (x : X) :
    derivedBox B ψ (map.states x) ↔ derivedBox A (ψ ∘ map.states) x :=
  ((box_related (spanMap_targetForth map) ((spanMap_targetBack_iff map).mpr lifts)
    (φ := ψ ∘ map.states) (ψ := ψ) (by rintro x _ rfl; exact Iff.rfl))
    (rfl : graph map x (map.states x))).symm

/-! ### Contexts and substitutions -/

/-- A relation is a **congruence** for a pair of maps acting on its two sides,
such as an admissible context or a substitution applied to both. -/
def Congruent (R : X → Y → Prop) (onX : X → X) (onY : Y → Y) : Prop :=
  ∀ ⦃x y⦄, R x y → R (onX x) (onY y)

theorem congruent_id (R : X → Y → Prop) : Congruent R id id := fun _ _ related => related

theorem Congruent.comp {R : X → Y → Prop} {firstX secondX : X → X} {firstY secondY : Y → Y}
    (first : Congruent R firstX firstY) (second : Congruent R secondX secondY) :
    Congruent R (secondX ∘ firstX) (secondY ∘ firstY) :=
  fun _ _ related => second (first related)

theorem Congruent.compose {R : X → Y → Prop} {S : Y → Z → Prop} {onX : X → X} {onY : Y → Y}
    {onZ : Z → Z} (first : Congruent R onX onY) (second : Congruent S onY onZ) :
    Congruent (compose R S) onX onZ := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩
  exact ⟨onY y, first relatedFirst, second relatedSecond⟩

/-- Congruence is the lax naturality square of the relation and the two maps. -/
theorem congruent_iff_square (R : X → Y → Prop) (onX : X → X) (onY : Y → Y) :
    Congruent R onX onY ↔
      ∀ x y', compose R (fun y y' => onY y = y') x y' → compose (fun x x' => onX x = x') R x y' := by
  constructor
  · rintro congruent x _ ⟨y, related, rfl⟩
    exact ⟨onX x, rfl, congruent related⟩
  · intro square x y related
    obtain ⟨_, rfl, related'⟩ := square x (onY y) ⟨y, related, rfl⟩
    exact related'

/-- A congruence carries related predicates to related predicates after the
two maps. -/
theorem Congruent.related {R : X → Y → Prop} {onX : X → X} {onY : Y → Y}
    (congruent : Congruent R onX onY) {φ : X → Prop} {ψ : Y → Prop} (related : Related R φ ψ) :
    Related R (φ ∘ onX) (ψ ∘ onY) :=
  fun _ _ relatedStates => related (congruent relatedStates)

end Endpoints

/-! ### The saturated relative quotient: contexts and substitutions -/

section Relative

open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

variable {S : GSLT.{u}} {rules : ContextualRules.{uA, uL} S}
variable (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{w} S)

/-- The quotient of the saturated relative behaviour, as a relation. -/
def relativeGraph : S.Term → RelativeState A observations → Prop :=
  fun term state => relativeObserve A observations term = state

/-- **Admissible contexts commute with the relative observation.** -/
theorem relative_congruent_context (context : rules.Context) (admissible : A.Admissible context) :
    Congruent (relativeGraph A observations) (rules.plug context)
      (contextAction A observations context admissible) := by
  rintro term _ rfl
  rfl

/-- **Respecting substitutions commute with the relative observation.** -/
theorem relative_congruent_substitution (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (substitution left) (substitution right)) :
    Congruent (relativeGraph A observations) substitution
      (quotientSubstitution A observations substitution respects) := by
  rintro term _ rfl
  rfl

/-- The relative observation's source law is the proved future matching of
the saturated behaviour; no target law is claimed. -/
theorem relative_sourceBack :
    SourceBack (gsltSpan S) (relativeSpan A observations) (relativeGraph A observations) :=
  (spanMap_sourceBack_iff (relativeMap A observations)).mpr (relative_sourceLifts A observations)

end Relative

/-! ## Event relations -/

section Events

variable {X : Type u} {Y : Type v} {Z : Type w}
variable {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{v, f} Y} {C : ReductionSpan.{w, g} Z}

/-- **A relation of reduction spans**: related states and related event
occurrences, whose endpoints are related. -/
structure SpanRelation (A : ReductionSpan.{u, e} X) (B : ReductionSpan.{v, f} Y) where
  states : X → Y → Prop
  events : A.Edge → B.Edge → Prop
  source_rel : ∀ ⦃a b⦄, events a b → states (A.source a) (B.source b)
  target_rel : ∀ ⦃a b⦄, events a b → states (A.target a) (B.target b)

namespace SpanRelation

variable (R : SpanRelation A B)

/-- Every outgoing occurrence at a related state is matched by a related
outgoing occurrence. -/
def SourceForthOcc : Prop :=
  ∀ ⦃x y⦄, R.states x y → ∀ a : A.Edge, A.source a = x → ∃ b : B.Edge, B.source b = y ∧ R.events a b

def SourceBackOcc : Prop :=
  ∀ ⦃x y⦄, R.states x y → ∀ b : B.Edge, B.source b = y → ∃ a : A.Edge, A.source a = x ∧ R.events a b

def TargetForthOcc : Prop :=
  ∀ ⦃x y⦄, R.states x y → ∀ a : A.Edge, A.target a = x → ∃ b : B.Edge, B.target b = y ∧ R.events a b

def TargetBackOcc : Prop :=
  ∀ ⦃x y⦄, R.states x y → ∀ b : B.Edge, B.target b = y → ∃ a : A.Edge, A.target a = x ∧ R.events a b

variable {R}

theorem SourceForthOcc.endpoint (forth : R.SourceForthOcc) : SourceForth A B R.states :=
  fun _ _ related a sourceEq =>
    let ⟨b, sourceEq', matched⟩ := forth related a sourceEq
    ⟨b, sourceEq', R.target_rel matched⟩

theorem SourceBackOcc.endpoint (back : R.SourceBackOcc) : SourceBack A B R.states :=
  fun _ _ related b sourceEq =>
    let ⟨a, sourceEq', matched⟩ := back related b sourceEq
    ⟨a, sourceEq', R.target_rel matched⟩

theorem TargetForthOcc.endpoint (forth : R.TargetForthOcc) : TargetForth A B R.states :=
  fun _ _ related a targetEq =>
    let ⟨b, targetEq', matched⟩ := forth related a targetEq
    ⟨b, targetEq', R.source_rel matched⟩

theorem TargetBackOcc.endpoint (back : R.TargetBackOcc) : TargetBack A B R.states :=
  fun _ _ related b targetEq =>
    let ⟨a, targetEq', matched⟩ := back related b targetEq
    ⟨a, targetEq', R.source_rel matched⟩

variable (A) in
/-- The identity relation of a span. -/
def identity : SpanRelation A A where
  states := Eq
  events := Eq
  source_rel := by rintro a _ rfl; rfl
  target_rel := by rintro a _ rfl; rfl

/-- Composition of span relations. -/
def comp (first : SpanRelation A B) (second : SpanRelation B C) : SpanRelation A C where
  states := compose first.states second.states
  events a c := ∃ b, first.events a b ∧ second.events b c
  source_rel := by
    rintro a c ⟨b, matchedFirst, matchedSecond⟩
    exact ⟨B.source b, first.source_rel matchedFirst, second.source_rel matchedSecond⟩
  target_rel := by
    rintro a c ⟨b, matchedFirst, matchedSecond⟩
    exact ⟨B.target b, first.target_rel matchedFirst, second.target_rel matchedSecond⟩

/-- The converse of a span relation. -/
def converse (R : SpanRelation A B) : SpanRelation B A where
  states := flip R.states
  events := flip R.events
  source_rel _ _ matched := R.source_rel matched
  target_rel _ _ matched := R.target_rel matched

variable (A) in
theorem identity_sourceForthOcc : (identity A).SourceForthOcc :=
  fun _ _ same a sourceEq => ⟨a, sourceEq.trans same, rfl⟩

variable (A) in
theorem identity_sourceBackOcc : (identity A).SourceBackOcc :=
  fun _ _ same b sourceEq => ⟨b, sourceEq.trans same.symm, rfl⟩

variable (A) in
theorem identity_targetForthOcc : (identity A).TargetForthOcc :=
  fun _ _ same a targetEq => ⟨a, targetEq.trans same, rfl⟩

variable (A) in
theorem identity_targetBackOcc : (identity A).TargetBackOcc :=
  fun _ _ same b targetEq => ⟨b, targetEq.trans same.symm, rfl⟩

theorem SourceForthOcc.comp {first : SpanRelation A B} {second : SpanRelation B C}
    (forthFirst : first.SourceForthOcc) (forthSecond : second.SourceForthOcc) :
    (first.comp second).SourceForthOcc := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ a sourceEq
  obtain ⟨b, sourceEq', matched⟩ := forthFirst relatedFirst a sourceEq
  obtain ⟨c, sourceEq'', matched'⟩ := forthSecond relatedSecond b sourceEq'
  exact ⟨c, sourceEq'', b, matched, matched'⟩

theorem SourceBackOcc.comp {first : SpanRelation A B} {second : SpanRelation B C}
    (backFirst : first.SourceBackOcc) (backSecond : second.SourceBackOcc) :
    (first.comp second).SourceBackOcc := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ c sourceEq
  obtain ⟨b, sourceEq', matched'⟩ := backSecond relatedSecond c sourceEq
  obtain ⟨a, sourceEq'', matched⟩ := backFirst relatedFirst b sourceEq'
  exact ⟨a, sourceEq'', b, matched, matched'⟩

theorem TargetForthOcc.comp {first : SpanRelation A B} {second : SpanRelation B C}
    (forthFirst : first.TargetForthOcc) (forthSecond : second.TargetForthOcc) :
    (first.comp second).TargetForthOcc := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ a targetEq
  obtain ⟨b, targetEq', matched⟩ := forthFirst relatedFirst a targetEq
  obtain ⟨c, targetEq'', matched'⟩ := forthSecond relatedSecond b targetEq'
  exact ⟨c, targetEq'', b, matched, matched'⟩

theorem TargetBackOcc.comp {first : SpanRelation A B} {second : SpanRelation B C}
    (backFirst : first.TargetBackOcc) (backSecond : second.TargetBackOcc) :
    (first.comp second).TargetBackOcc := by
  rintro x z ⟨y, relatedFirst, relatedSecond⟩ c targetEq
  obtain ⟨b, targetEq', matched'⟩ := backSecond relatedSecond c targetEq
  obtain ⟨a, targetEq'', matched⟩ := backFirst relatedFirst b targetEq'
  exact ⟨a, targetEq'', b, matched, matched'⟩

theorem sourceForthOcc_iff_converse (R : SpanRelation A B) :
    R.SourceForthOcc ↔ R.converse.SourceBackOcc :=
  ⟨fun forth _ _ related a sourceEq => forth related a sourceEq,
    fun back _ _ related a sourceEq => back related a sourceEq⟩

theorem targetForthOcc_iff_converse (R : SpanRelation A B) :
    R.TargetForthOcc ↔ R.converse.TargetBackOcc :=
  ⟨fun forth _ _ related a targetEq => forth related a targetEq,
    fun back _ _ related a targetEq => back related a targetEq⟩

/-! ### Readings of events -/

/-- Related events read alike: labels, results, faults and provenance carried by
the reading are kept. -/
def Keeps {L : Sort*} (R : SpanRelation A B) (readA : A.Edge → L) (readB : B.Edge → L) : Prop :=
  ∀ ⦃a b⦄, R.events a b → readA a = readB b

variable (A) in
theorem keeps_identity {L : Sort*} (read : A.Edge → L) : (identity A).Keeps read read := by
  rintro a _ rfl
  rfl

theorem Keeps.comp {L : Sort*} {first : SpanRelation A B} {second : SpanRelation B C}
    {readA : A.Edge → L} {readB : B.Edge → L} {readC : C.Edge → L}
    (keepsFirst : first.Keeps readA readB) (keepsSecond : second.Keeps readB readC) :
    (first.comp second).Keeps readA readC := by
  rintro a c ⟨b, matched, matched'⟩
  exact (keepsFirst matched).trans (keepsSecond matched')

theorem Keeps.converse {L : Sort*} {R : SpanRelation A B} {readA : A.Edge → L}
    {readB : B.Edge → L} (keeps : R.Keeps readA readB) : R.converse.Keeps readB readA :=
  fun _ _ matched => (keeps matched).symm

/-! ### A span map as an event relation -/

/-- The graph of a span map on states and on events. -/
def ofSpanMap (map : SpanMap A B) : SpanRelation A B where
  states := graph map
  events a b := map.events a = b
  source_rel := by
    rintro a _ rfl
    exact (map.source_comm a).symm
  target_rel := by
    rintro a _ rfl
    exact (map.target_comm a).symm

theorem ofSpanMap_sourceForthOcc (map : SpanMap A B) : (ofSpanMap map).SourceForthOcc := by
  intro x y related a sourceEq
  refine ⟨map.events a, ?_, rfl⟩
  rw [map.source_comm, sourceEq]
  exact related

theorem ofSpanMap_targetForthOcc (map : SpanMap A B) : (ofSpanMap map).TargetForthOcc := by
  intro x y related a targetEq
  refine ⟨map.events a, ?_, rfl⟩
  rw [map.target_comm, targetEq]
  exact related

/-- **Occurrence back laws of a span map are its occurrence liftings.** -/
theorem ofSpanMap_sourceBackOcc_iff (map : SpanMap A B) :
    (ofSpanMap map).SourceBackOcc ↔ map.SourceOccurrenceLifts := by
  constructor
  · intro back state event sourceEq
    exact back (rfl : graph map state (map.states state)) event sourceEq
  · rintro lifts x _ rfl b sourceEq
    exact lifts x b sourceEq

theorem ofSpanMap_targetBackOcc_iff (map : SpanMap A B) :
    (ofSpanMap map).TargetBackOcc ↔ map.TargetOccurrenceLifts := by
  constructor
  · intro back state event targetEq
    exact back (rfl : graph map state (map.states state)) event targetEq
  · rintro lifts x _ rfl b targetEq
    exact lifts x b targetEq

/-- The endpoint relation of a state relation: events are related when their
endpoints are.  It forgets event identity and readings. -/
def endpoints (R : X → Y → Prop) : SpanRelation A B where
  states := R
  events a b := R (A.source a) (B.source b) ∧ R (A.target a) (B.target b)
  source_rel _ _ matched := matched.1
  target_rel _ _ matched := matched.2

theorem endpoints_sourceForthOcc_iff (R : X → Y → Prop) :
    (endpoints (A := A) (B := B) R).SourceForthOcc ↔ SourceForth A B R := by
  constructor
  · exact fun forth => forth.endpoint
  · intro forth x y related a sourceEq
    obtain ⟨b, sourceEq', relatedTargets⟩ := forth related a sourceEq
    exact ⟨b, sourceEq', by rw [sourceEq, sourceEq']; exact related, relatedTargets⟩

theorem endpoints_sourceBackOcc_iff (R : X → Y → Prop) :
    (endpoints (A := A) (B := B) R).SourceBackOcc ↔ SourceBack A B R := by
  constructor
  · exact fun back => back.endpoint
  · intro back x y related b sourceEq
    obtain ⟨a, sourceEq', relatedTargets⟩ := back related b sourceEq
    exact ⟨a, sourceEq', by rw [sourceEq, sourceEq']; exact related, relatedTargets⟩

theorem endpoints_targetForthOcc_iff (R : X → Y → Prop) :
    (endpoints (A := A) (B := B) R).TargetForthOcc ↔ TargetForth A B R := by
  constructor
  · exact fun forth => forth.endpoint
  · intro forth x y related a targetEq
    obtain ⟨b, targetEq', relatedSources⟩ := forth related a targetEq
    exact ⟨b, targetEq', relatedSources, by rw [targetEq, targetEq']; exact related⟩

theorem endpoints_targetBackOcc_iff (R : X → Y → Prop) :
    (endpoints (A := A) (B := B) R).TargetBackOcc ↔ TargetBack A B R := by
  constructor
  · exact fun back => back.endpoint
  · intro back x y related b targetEq
    obtain ⟨a, targetEq', relatedSources⟩ := back related b targetEq
    exact ⟨a, targetEq', relatedSources, by rw [targetEq, targetEq']; exact related⟩

/-! ### Parallel occurrences -/

/-- The related outgoing fibres correspond one to one through related events. -/
def OutFibresMatch (R : SpanRelation A B) : Prop :=
  ∀ ⦃x y⦄, R.states x y → ∃ matching : {a : A.Edge // A.source a = x} ≃ {b : B.Edge // B.source b = y},
    ∀ a, R.events a.1 (matching a).1

/-- The related incoming fibres correspond one to one through related events. -/
def InFibresMatch (R : SpanRelation A B) : Prop :=
  ∀ ⦃x y⦄, R.states x y → ∃ matching : {a : A.Edge // A.target a = x} ≃ {b : B.Edge // B.target b = y},
    ∀ a, R.events a.1 (matching a).1

theorem OutFibresMatch.sourceForthOcc (fibres : R.OutFibresMatch) : R.SourceForthOcc := by
  intro x y related a sourceEq
  obtain ⟨matching, matched⟩ := fibres related
  exact ⟨(matching ⟨a, sourceEq⟩).1, (matching ⟨a, sourceEq⟩).2, matched ⟨a, sourceEq⟩⟩

theorem OutFibresMatch.sourceBackOcc (fibres : R.OutFibresMatch) : R.SourceBackOcc := by
  intro x y related b sourceEq
  obtain ⟨matching, matched⟩ := fibres related
  refine ⟨(matching.symm ⟨b, sourceEq⟩).1, (matching.symm ⟨b, sourceEq⟩).2, ?_⟩
  have := matched (matching.symm ⟨b, sourceEq⟩)
  rwa [Equiv.apply_symm_apply] at this

theorem InFibresMatch.targetForthOcc (fibres : R.InFibresMatch) : R.TargetForthOcc := by
  intro x y related a targetEq
  obtain ⟨matching, matched⟩ := fibres related
  exact ⟨(matching ⟨a, targetEq⟩).1, (matching ⟨a, targetEq⟩).2, matched ⟨a, targetEq⟩⟩

theorem InFibresMatch.targetBackOcc (fibres : R.InFibresMatch) : R.TargetBackOcc := by
  intro x y related b targetEq
  obtain ⟨matching, matched⟩ := fibres related
  refine ⟨(matching.symm ⟨b, targetEq⟩).1, (matching.symm ⟨b, targetEq⟩).2, ?_⟩
  have := matched (matching.symm ⟨b, targetEq⟩)
  rwa [Equiv.apply_symm_apply] at this

end SpanRelation

end Events

/-! ## Labelled tense formulas -/

section Tense

variable {X : Type u} {Y : Type v}

/-- A reduction span whose events carry readings, with atomic observations of
states. -/
structure Labelled (X : Type u) (Atom : Type uA) (Label : Type uL) where
  span : ReductionSpan.{u, e} X
  read : span.Edge → Label
  observes : Atom → X → Prop

/-- Tense formulas: atoms, negation, conjunction, and a labelled future and past
diamond. -/
inductive Tense (Atom : Type uA) (Label : Type uL) : Type (max uA uL) where
  | top : Tense Atom Label
  | atom (atom : Atom) : Tense Atom Label
  | neg (inner : Tense Atom Label) : Tense Atom Label
  | conj (left right : Tense Atom Label) : Tense Atom Label
  | future (label : Label) (inner : Tense Atom Label) : Tense Atom Label
  | past (label : Label) (inner : Tense Atom Label) : Tense Atom Label

/-- The formulas without past modalities. -/
inductive Tense.IsFuture {Atom : Type uA} {Label : Type uL} : Tense Atom Label → Prop
  | top : IsFuture .top
  | atom (name : Atom) : IsFuture (.atom name)
  | neg {inner : Tense Atom Label} : IsFuture inner → IsFuture (.neg inner)
  | conj {left right : Tense Atom Label} : IsFuture left → IsFuture right →
      IsFuture (.conj left right)
  | future (label : Label) {inner : Tense Atom Label} : IsFuture inner →
      IsFuture (.future label inner)

variable {Atom : Type uA} {Label : Type uL}

/-- Satisfaction of a tense formula. -/
def Tense.sat (L : Labelled.{u, e} X Atom Label) : Tense Atom Label → X → Prop
  | .top, _ => True
  | .atom name, x => L.observes name x
  | .neg inner, x => ¬ sat L inner x
  | .conj left right, x => sat L left x ∧ sat L right x
  | .future label inner, x =>
      ∃ event, L.span.source event = x ∧ L.read event = label ∧ sat L inner (L.span.target event)
  | .past label inner, x =>
      ∃ event, L.span.target event = x ∧ L.read event = label ∧ sat L inner (L.span.source event)

/-- **Preservation and reflection of every labelled tense formula** by an event
relation that keeps readings and atoms and satisfies all four occurrence
laws. -/
theorem sat_related (L : Labelled.{u, e} X Atom Label) (M : Labelled.{v, f} Y Atom Label)
    (R : SpanRelation L.span M.span) (keeps : R.Keeps L.read M.read)
    (atoms : ∀ atom, Related R.states (L.observes atom) (M.observes atom))
    (sourceForth : R.SourceForthOcc) (sourceBack : R.SourceBackOcc)
    (targetForth : R.TargetForthOcc) (targetBack : R.TargetBackOcc) :
    ∀ formula : Tense Atom Label, Related R.states (Tense.sat L formula) (Tense.sat M formula)
  | .top => fun _ _ _ => Iff.rfl
  | .atom name => fun _ _ related => atoms name related
  | .neg inner => fun _ _ related =>
      not_congr (sat_related L M R keeps atoms sourceForth sourceBack targetForth targetBack inner related)
  | .conj left right => fun _ _ related =>
      and_congr (sat_related L M R keeps atoms sourceForth sourceBack targetForth targetBack left related)
        (sat_related L M R keeps atoms sourceForth sourceBack targetForth targetBack right related)
  | .future label inner => fun x y related => by
      have inner_related :=
        sat_related L M R keeps atoms sourceForth sourceBack targetForth targetBack inner
      constructor
      · rintro ⟨a, sourceEq, readEq, holds⟩
        obtain ⟨b, sourceEq', matched⟩ := sourceForth related a sourceEq
        exact ⟨b, sourceEq', (keeps matched).symm.trans readEq,
          (inner_related (R.target_rel matched)).mp holds⟩
      · rintro ⟨b, sourceEq, readEq, holds⟩
        obtain ⟨a, sourceEq', matched⟩ := sourceBack related b sourceEq
        exact ⟨a, sourceEq', (keeps matched).trans readEq,
          (inner_related (R.target_rel matched)).mpr holds⟩
  | .past label inner => fun x y related => by
      have inner_related :=
        sat_related L M R keeps atoms sourceForth sourceBack targetForth targetBack inner
      constructor
      · rintro ⟨a, targetEq, readEq, holds⟩
        obtain ⟨b, targetEq', matched⟩ := targetForth related a targetEq
        exact ⟨b, targetEq', (keeps matched).symm.trans readEq,
          (inner_related (R.source_rel matched)).mp holds⟩
      · rintro ⟨b, targetEq, readEq, holds⟩
        obtain ⟨a, targetEq', matched⟩ := targetBack related b targetEq
        exact ⟨a, targetEq', (keeps matched).trans readEq,
          (inner_related (R.source_rel matched)).mpr holds⟩

/-- **Future formulas need only the two source laws.** -/
theorem sat_related_future (L : Labelled.{u, e} X Atom Label) (M : Labelled.{v, f} Y Atom Label)
    (R : SpanRelation L.span M.span) (keeps : R.Keeps L.read M.read)
    (atoms : ∀ atom, Related R.states (L.observes atom) (M.observes atom))
    (sourceForth : R.SourceForthOcc) (sourceBack : R.SourceBackOcc) :
    ∀ {formula : Tense Atom Label}, formula.IsFuture →
      Related R.states (Tense.sat L formula) (Tense.sat M formula)
  | _, .top => fun _ _ _ => Iff.rfl
  | _, .atom name => fun _ _ related => atoms name related
  | _, .neg inner => fun _ _ related =>
      not_congr (sat_related_future L M R keeps atoms sourceForth sourceBack inner related)
  | _, .conj left right => fun _ _ related =>
      and_congr (sat_related_future L M R keeps atoms sourceForth sourceBack left related)
        (sat_related_future L M R keeps atoms sourceForth sourceBack right related)
  | _, .future label inner => fun x y related => by
      have inner_related := sat_related_future L M R keeps atoms sourceForth sourceBack inner
      constructor
      · rintro ⟨a, sourceEq, readEq, holds⟩
        obtain ⟨b, sourceEq', matched⟩ := sourceForth related a sourceEq
        exact ⟨b, sourceEq', (keeps matched).symm.trans readEq,
          (inner_related (R.target_rel matched)).mp holds⟩
      · rintro ⟨b, sourceEq, readEq, holds⟩
        obtain ⟨a, sourceEq', matched⟩ := sourceBack related b sourceEq
        exact ⟨a, sourceEq', (keeps matched).trans readEq,
          (inner_related (R.target_rel matched)).mpr holds⟩

/-- **Parallel occurrences**: when related outgoing fibres correspond one to one
and readings are kept, related states have equally many outgoing occurrences
with each reading. -/
theorem outgoing_card_eq {A : ReductionSpan.{u, u} X} {B : ReductionSpan.{v, v} Y}
    {L : Type*} {readA : A.Edge → L} {readB : B.Edge → L} (R : SpanRelation A B)
    (fibres : R.OutFibresMatch) (keeps : R.Keeps readA readB) {x : X} {y : Y}
    (related : R.states x y) (label : L) :
    Nat.card {a : A.Edge // A.source a = x ∧ readA a = label} =
      Nat.card {b : B.Edge // B.source b = y ∧ readB b = label} := by
  obtain ⟨matching, matched⟩ := fibres related
  refine Nat.card_congr (((Equiv.subtypeSubtypeEquivSubtypeInter
    (fun a => A.source a = x) (fun a => readA a = label)).symm.trans
      (Equiv.subtypeEquiv matching fun a => ?_)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun b => B.source b = y) (fun b => readB b = label)))
  rw [keeps (matched a)]

/-- The same for incoming occurrences. -/
theorem incoming_card_eq {A : ReductionSpan.{u, u} X} {B : ReductionSpan.{v, v} Y}
    {L : Type*} {readA : A.Edge → L} {readB : B.Edge → L} (R : SpanRelation A B)
    (fibres : R.InFibresMatch) (keeps : R.Keeps readA readB) {x : X} {y : Y}
    (related : R.states x y) (label : L) :
    Nat.card {a : A.Edge // A.target a = x ∧ readA a = label} =
      Nat.card {b : B.Edge // B.target b = y ∧ readB b = label} := by
  obtain ⟨matching, matched⟩ := fibres related
  refine Nat.card_congr (((Equiv.subtypeSubtypeEquivSubtypeInter
    (fun a => A.target a = x) (fun a => readA a = label)).symm.trans
      (Equiv.subtypeEquiv matching fun a => ?_)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun b => B.target b = y) (fun b => readB b = label)))
  rw [keeps (matched a)]

end Tense

/-! ## Two-sided observation from forward and backward actions -/

section TwoSided

open Mettapedia.GSLT.HennessyMilner

variable {S : GSLT.{u}} (M : System.{uA, uL} S)

/-- **The two-sided observation**: each labelled action is observed forward, and
backward from its target to its source. -/
def twoSided : System.{uA, uL} S where
  Atom := M.Atom
  observes := M.observes
  observes_resp := M.observes_resp
  Label := M.Label ⊕ M.Label
  act
    | .inl label => M.act label
    | .inr label => fun source target => M.act label target source
  act_resp_left := by
    intro label left right target equal acts
    cases label with
    | inl label => exact M.act_resp_left equal acts
    | inr label => exact ⟨target, M.act_resp_right acts equal, S.equations.iseqv.refl target⟩
  act_resp_right := by
    intro label source target target' acts equal
    cases label with
    | inl label => exact M.act_resp_right acts equal
    | inr label =>
        obtain ⟨source', acts', equal'⟩ := M.act_resp_left equal acts
        exact M.act_resp_right acts' (S.equations.iseqv.symm equal')

theorem twoSided_forward (label : M.Label) (x y : S.Term) :
    (twoSided M).act (.inl label) x y ↔ M.act label x y := Iff.rfl

theorem twoSided_backward (label : M.Label) (x y : S.Term) :
    (twoSided M).act (.inr label) x y ↔ M.act label y x := Iff.rfl

/-- A backward diamond of the two-sided observation is a labelled past diamond. -/
theorem twoSided_sat_backward (label : M.Label) (inner : Formula M.Atom (M.Label ⊕ M.Label))
    (x : S.Term) :
    (twoSided M).sat (.dia (.inr label) inner) x ↔
      ∃ y, M.act label y x ∧ (twoSided M).sat inner y := Iff.rfl

/-- Incoming actions of related states are matched, in both directions. -/
def PastMatching (R : S.Term → S.Term → Prop) : Prop :=
  (∀ ⦃x y⦄, R x y → ∀ (label : M.Label) ⦃x'⦄, M.act label x' x → ∃ y', M.act label y' y ∧ R x' y') ∧
    (∀ ⦃x y⦄, R x y → ∀ (label : M.Label) ⦃y'⦄, M.act label y' y → ∃ x', M.act label x' x ∧ R x' y')

/-- **A two-sided bisimulation is a bisimulation that also matches pasts.** -/
theorem twoSided_isBisimulation_iff (R : S.Term → S.Term → Prop) :
    (twoSided M).IsBisimulation R ↔ M.IsBisimulation R ∧ PastMatching M R := by
  constructor
  · rintro ⟨forth, back, atoms⟩
    exact ⟨⟨fun _ _ related label _ acts => forth related (.inl label) acts,
        fun _ _ related label _ acts => back related (.inl label) acts, atoms⟩,
      fun _ _ related label _ acts => forth related (.inr label) acts,
      fun _ _ related label _ acts => back related (.inr label) acts⟩
  · rintro ⟨⟨forth, back, atoms⟩, pastForth, pastBack⟩
    refine ⟨?_, ?_, atoms⟩
    · intro x y related label x' acts
      cases label with
      | inl label => exact forth related label acts
      | inr label => exact pastForth related label acts
    · intro x y related label y' acts
      cases label with
      | inl label => exact back related label acts
      | inr label => exact pastBack related label acts

theorem bisimilar_of_twoSided {x y : S.Term} (bisimilar : (twoSided M).Bisimilar x y) :
    M.Bisimilar x y := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  exact ⟨R, ((twoSided_isBisimulation_iff M R).mp bisimulation).1, related⟩

/-- Finitely many predecessor classes under each label. -/
def PredecessorFiniteModulo : Prop :=
  ∀ (label : M.Label) (term : S.Term), ∃ representatives : Set S.Term, representatives.Finite ∧
    ∀ ⦃source⦄, M.act label source term →
      ∃ representative ∈ representatives, S.Equiv source representative

/-- **The two-sided observation branches finitely exactly when both the
successors and the predecessors do.**  These are separate requirements. -/
theorem twoSided_imageFiniteModulo_iff :
    (twoSided M).ImageFiniteModulo ↔ M.ImageFiniteModulo ∧ PredecessorFiniteModulo M := by
  constructor
  · intro finite
    exact ⟨fun label term => finite (.inl label) term, fun label term => finite (.inr label) term⟩
  · rintro ⟨successors, predecessors⟩ label term
    cases label with
    | inl label => exact successors label term
    | inr label => exact predecessors label term

/-- **Two-sided Hennessy–Milner**, under finitely many successor classes and
finitely many predecessor classes. -/
theorem twoSided_logicallyEquivalent_iff_bisimilar (successors : M.ImageFiniteModulo)
    (predecessors : PredecessorFiniteModulo M) (x y : S.Term) :
    (twoSided M).LogicallyEquivalent x y ↔ (twoSided M).Bisimilar x y :=
  (twoSided M).logicallyEquivalent_iff_bisimilar
    ((twoSided_imageFiniteModulo_iff M).mpr ⟨successors, predecessors⟩) x y

/-- **The agreement of a system with its GSLT**: the steps are exactly the
labelled actions.  A `HennessyMilner.System` does not require it. -/
def StepAgreement : Prop := ∀ x y, S.Step x y ↔ ∃ label, M.act label x y

variable {M}

/-- A bisimulation of an agreeing system has both source laws on the GSLT's
reduction span. -/
theorem sourceLaws_of_isBisimulation (agree : StepAgreement M) {R : S.Term → S.Term → Prop}
    (bisimulation : M.IsBisimulation R) :
    SourceForth (gsltSpan S) (gsltSpan S) R ∧ SourceBack (gsltSpan S) (gsltSpan S) R := by
  constructor
  · intro x y related a sourceEq
    have step : S.Step x a.target := by
      rw [← sourceEq]
      exact a.step
    obtain ⟨label, acts⟩ := (agree x a.target).mp step
    obtain ⟨y', acts', related'⟩ := bisimulation.1 related label acts
    exact ⟨⟨y, y', (agree y y').mpr ⟨label, acts'⟩⟩, rfl, related'⟩
  · intro x y related b sourceEq
    have step : S.Step y b.target := by
      rw [← sourceEq]
      exact b.step
    obtain ⟨label, acts⟩ := (agree y b.target).mp step
    obtain ⟨x', acts', related'⟩ := bisimulation.2.1 related label acts
    exact ⟨⟨x, x', (agree x x').mpr ⟨label, acts'⟩⟩, rfl, related'⟩

/-- **A two-sided bisimulation of an agreeing system has both target laws** on
the GSLT's reduction span. -/
theorem targetLaws_of_twoSided (agree : StepAgreement M) {R : S.Term → S.Term → Prop}
    (bisimulation : (twoSided M).IsBisimulation R) :
    TargetForth (gsltSpan S) (gsltSpan S) R ∧ TargetBack (gsltSpan S) (gsltSpan S) R := by
  obtain ⟨_, pastForth, pastBack⟩ := (twoSided_isBisimulation_iff M R).mp bisimulation
  constructor
  · intro x y related a targetEq
    have step : S.Step a.source x := by
      rw [← targetEq]
      exact a.step
    obtain ⟨label, acts⟩ := (agree a.source x).mp step
    obtain ⟨y', acts', related'⟩ := pastForth related label acts
    exact ⟨⟨y', y, (agree y' y).mpr ⟨label, acts'⟩⟩, rfl, related'⟩
  · intro x y related b targetEq
    have step : S.Step b.source y := by
      rw [← targetEq]
      exact b.step
    obtain ⟨label, acts⟩ := (agree b.source y).mp step
    obtain ⟨x', acts', related'⟩ := pastBack related label acts
    exact ⟨⟨x', x, (agree x' x).mpr ⟨label, acts'⟩⟩, rfl, related'⟩

/-- A bisimulation of an agreeing system preserves and reflects the GSLT's
future diamond. -/
theorem bisimulation_gsltDiamond (agree : StepAgreement M) {R : S.Term → S.Term → Prop}
    (bisimulation : M.IsBisimulation R) {φ ψ : S.Term → Prop} (related : Related R φ ψ) :
    Related R (gsltDiamond S φ) (gsltDiamond S ψ) :=
  let ⟨forth, back⟩ := sourceLaws_of_isBisimulation agree bisimulation
  diamond_related forth back related

/-- **A two-sided bisimulation of an agreeing system preserves and reflects the
GSLT's past box.** -/
theorem twoSided_gsltBox (agree : StepAgreement M) {R : S.Term → S.Term → Prop}
    (bisimulation : (twoSided M).IsBisimulation R) {φ ψ : S.Term → Prop} (related : Related R φ ψ) :
    Related R (gsltBox S φ) (gsltBox S ψ) :=
  let ⟨forth, back⟩ := targetLaws_of_twoSided agree bisimulation
  box_related forth back related

end TwoSided

/-! ## Restriction-natural event observations, stage by stage -/

section Stages

open _root_.CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf

variable {C : Type u} [Category.{v} C]

/-- The reduction span of an event graph at one stage. -/
def stageSpan (A : EventGraph.{u, v, w} C) (X : C) : ReductionSpan.{w, w} (A.vertex.obj X) where
  Edge := A.edge.obj X
  source event := A.source.app X event
  target event := A.target.app X event

/-- A restriction-natural event observation at one stage. -/
def stageMap {A B : EventGraph.{u, v, w} C} (observation : Presheaf.EventObservation A B) (X : C) :
    SpanMap (stageSpan A X) (stageSpan B X) where
  states state := observation.states.app X state
  events event := observation.events.app X event
  source_comm := observation.source_comm X
  target_comm := observation.target_comm X

/-- **The source lifting of an event observation is the source back law at
every stage.** -/
theorem eventObservation_sourceLifts_iff {A B : EventGraph.{u, v, w} C}
    (observation : Presheaf.EventObservation A B) :
    observation.SourceLifts ↔
      ∀ X, SourceBack (stageSpan A X) (stageSpan B X) (graph (stageMap observation X)) := by
  simp only [spanMap_sourceBack_iff]
  exact Iff.rfl

/-- **The target lifting of an event observation is the target back law at
every stage.**  The presheaf box additionally ranges over restrictions; with this
law it is natural (`Presheaf.EventObservation.box_pullback`). -/
theorem eventObservation_targetLifts_iff {A B : EventGraph.{u, v, w} C}
    (observation : Presheaf.EventObservation A B) :
    observation.TargetLifts ↔
      ∀ X, TargetBack (stageSpan A X) (stageSpan B X) (graph (stageMap observation X)) := by
  simp only [spanMap_targetBack_iff]
  exact Iff.rfl

end Stages

end Mettapedia.GSLT.Distinction.SpanTransport

/-! ## Cost simulations as event relations -/

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Distinction.SpanTransport

/-- The outcomes of two finite runs, related through a state relation: one
verdict, faults, one request with related saved continuations, or related
residuals. -/
inductive OutcomeRel {Source Target Verdict Request : Type} (related : Source → Target → Prop) :
    Outcome Source Verdict Request → Outcome Target Verdict Request → Prop
  | finished (verdict : Verdict) : OutcomeRel related (.finished verdict) (.finished verdict)
  | faulted : OutcomeRel related .faulted .faulted
  | suspended (request : Request) {saved : Source} {saved' : Target} : related saved saved' →
      OutcomeRel related (.suspended request saved) (.suspended request saved')
  | exhausted {residual : Source} {residual' : Target} : related residual residual' →
      OutcomeRel related (.exhausted residual) (.exhausted residual')

section Outcomes

variable {Source Target Verdict Request : Type} {related : Source → Target → Prop}

theorem OutcomeRel.status_eq {outcome : Outcome Source Verdict Request}
    {outcome' : Outcome Target Verdict Request} (relatedOutcomes : OutcomeRel related outcome outcome') :
    outcome.status = outcome'.status := by
  cases relatedOutcomes <;> rfl

theorem OutcomeRel.exhausted_inv {residual : Source} {outcome' : Outcome Target Verdict Request}
    (relatedOutcomes : OutcomeRel related (.exhausted residual) outcome') :
    ∃ residual', outcome' = .exhausted residual' ∧ related residual residual' := by
  cases relatedOutcomes with
  | exhausted relatedResidual => exact ⟨_, rfl, relatedResidual⟩

end Outcomes

namespace CostSimulation

variable {Source Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {target : Machine Target Event Verdict Request}
  {related : Source → Target → Prop} {cost : ℕ}

/-- **Relation-level transport of complete runs.**  A source run that does not
end stuck is matched, within `cost` times its fuel, by a target run publishing
the same events whose outcome is related: the same verdict, faults, the same
request with related saved continuations, or related residuals. -/
theorem run_related (simulation : CostSimulation source target related cost) (fuel : ℕ) :
    ∀ {state : Source} {state' : Target}, related state state' →
      (∀ stuckAt, (source.run fuel state).2 ≠ .stuck stuckAt) →
      ∃ k ≤ cost * fuel, (target.run k state').1 = (source.run fuel state).1 ∧
        OutcomeRel related (source.run fuel state).2 (target.run k state').2 := by
  induction fuel with
  | zero =>
      intro state state' relatedStates _
      exact ⟨0, Nat.zero_le _, rfl, .exhausted relatedStates⟩
  | succ fuel ih =>
      intro state state' relatedStates notStuck
      have budget : ∀ k ≤ cost, ∀ k' ≤ cost * fuel, k + k' ≤ cost * (fuel + 1) := by
        intro k bound k' bound'
        rw [Nat.mul_succ]
        omega
      have single : ∀ k ≤ cost, k ≤ cost * (fuel + 1) := by
        intro k bound
        rw [Nat.mul_succ]
        omega
      cases found : source.step state with
      | none =>
          exact absurd (congrArg Prod.snd (source.run_succ_stuck (fuel := fuel) found))
            (notStuck state)
      | some transition =>
          cases transition with
          | silent next =>
              have ran := source.run_succ_silent (fuel := fuel) found
              obtain ⟨k₁, bound₁, next', ran₁, relatedNext⟩ := simulation.silent relatedStates found
              rw [ran] at notStuck ⊢
              obtain ⟨k₂, bound₂, events₂, outcome₂⟩ := ih relatedNext notStuck
              refine ⟨k₁ + k₂, budget k₁ bound₁ k₂ bound₂, ?_, ?_⟩
              · rw [target.run_add, ran₁]
                simpa [Machine.continueRun] using events₂
              · rw [target.run_add, ran₁]
                simpa [Machine.continueRun] using outcome₂
          | publish events next =>
              have ran := source.run_succ_publish (fuel := fuel) found
              obtain ⟨k₁, bound₁, next', ran₁, relatedNext⟩ := simulation.publish relatedStates found
              rw [ran] at notStuck ⊢
              obtain ⟨k₂, bound₂, events₂, outcome₂⟩ := ih relatedNext notStuck
              refine ⟨k₁ + k₂, budget k₁ bound₁ k₂ bound₂, ?_, ?_⟩
              · rw [target.run_add, ran₁]
                simp [Machine.continueRun, events₂]
              · rw [target.run_add, ran₁]
                simpa [Machine.continueRun] using outcome₂
          | finish verdict =>
              obtain ⟨k, bound, ran₁⟩ := simulation.finish relatedStates found
              rw [source.run_succ_finish found]
              exact ⟨k, single k bound, by rw [ran₁], by rw [ran₁]; exact .finished verdict⟩
          | fail events =>
              obtain ⟨k, bound, ran₁⟩ := simulation.fail relatedStates found
              rw [source.run_succ_fail found]
              exact ⟨k, single k bound, by rw [ran₁], by rw [ran₁]; exact .faulted⟩
          | call request saved =>
              obtain ⟨k, bound, saved', ran₁, relatedSaved⟩ := simulation.call relatedStates found
              rw [source.run_succ_call found]
              exact ⟨k, single k bound, by rw [ran₁], by rw [ran₁]; exact .suspended request relatedSaved⟩

/-- **A run that does not end stuck is matched with an equal observation**,
within `cost` times its fuel: not only a prefix. -/
theorem observe_eq (simulation : CostSimulation source target related cost) (fuel : ℕ)
    {state : Source} {state' : Target} (relatedStates : related state state')
    (notStuck : ∀ stuckAt, (source.run fuel state).2 ≠ .stuck stuckAt) :
    ∃ k ≤ cost * fuel, target.observe k state' = source.observe fuel state := by
  obtain ⟨k, bound, eventsEq, outcome⟩ := simulation.run_related fuel relatedStates notStuck
  refine ⟨k, bound, ?_⟩
  simp only [Machine.observe, eventsEq, outcome.status_eq]

/-- A run segment ending with its exact residual is matched by a target segment
publishing the same events, with related residuals. -/
theorem segment (simulation : CostSimulation source target related cost) {fuel : ℕ}
    {state residual : Source} {state' : Target} {events : List Event}
    (relatedStates : related state state') (ran : source.run fuel state = (events, .exhausted residual)) :
    ∃ k ≤ cost * fuel, ∃ residual', target.run k state' = (events, .exhausted residual') ∧
      related residual residual' := by
  obtain ⟨k, bound, eventsEq, outcome⟩ := simulation.run_related fuel relatedStates (by
    intro stuckAt stuck
    rw [ran] at stuck
    cases stuck)
  rw [ran] at eventsEq outcome
  obtain ⟨residual', outcomeEq, relatedResidual⟩ := outcome.exhausted_inv
  exact ⟨k, bound, residual', Prod.ext eventsEq outcomeEq, relatedResidual⟩

end CostSimulation

/-! ### The segment span of a machine -/

/-- A finite run segment that ends with its exact residual. -/
structure Segment {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request) where
  start : State
  fuel : ℕ
  events : List Event
  residual : State
  ran : machine.run fuel start = (events, .exhausted residual)

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- **The segment span** of a machine: run segments from their start to their
residual. -/
def segmentSpan : ReductionSpan State where
  Edge := Segment machine
  source := Segment.start
  target := Segment.residual

/-- The segment span with the published events as the readings of its
segments and the given atomic observations of states. -/
def segments {Atom : Type} (observes : Atom → State → Prop) : Labelled State Atom (List Event) where
  span := machine.segmentSpan
  read := Segment.events
  observes := observes

end Machine

/-- The segment relation of a state relation: segments are related when their
starts and residuals are related and they publish the same events. -/
def segmentRelation {Source Target Event Verdict Request : Type}
    (source : Machine Source Event Verdict Request) (target : Machine Target Event Verdict Request)
    (related : Source → Target → Prop) : SpanRelation source.segmentSpan target.segmentSpan where
  states := related
  events first second := related first.start second.start ∧
    related first.residual second.residual ∧ first.events = second.events
  source_rel _ _ matched := matched.1
  target_rel _ _ matched := matched.2.1

namespace CostSimulation

variable {Source Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {target : Machine Target Event Verdict Request}
  {related : Source → Target → Prop} {cost : ℕ}

theorem segmentRelation_keeps :
    (segmentRelation source target related).Keeps (Segment.events (machine := source))
      (Segment.events (machine := target)) :=
  fun _ _ matched => matched.2.2

/-- **A simulation gives the source forth law** of the segment relation. -/
theorem segment_sourceForthOcc (simulation : CostSimulation source target related cost) :
    (segmentRelation source target related).SourceForthOcc := by
  intro x y relatedStates first startEq
  have startEq' : first.start = x := startEq
  subst startEq'
  obtain ⟨k, _, residual', ran, relatedResidual⟩ := simulation.segment relatedStates first.ran
  exact ⟨⟨y, k, first.events, residual', ran⟩, rfl, relatedStates, relatedResidual, rfl⟩

/-- **A simulation the other way gives the source back law**, a separate law. -/
theorem segment_sourceBackOcc {cost' : ℕ}
    (backward : CostSimulation target source (fun state' state => related state state') cost') :
    (segmentRelation source target related).SourceBackOcc := by
  intro x y relatedStates second startEq
  have startEq' : second.start = y := startEq
  subst startEq'
  obtain ⟨k, _, residual, ran, relatedResidual⟩ :=
    backward.segment (relatedStates : (fun state' state => related state state') second.start x)
      second.ran
  exact ⟨⟨x, k, second.events, residual, ran⟩, rfl, relatedStates, relatedResidual, rfl⟩

/-- **With a simulation each way, every future formula over published events
agrees on related states**, for atoms that read alike on related states.  No
past formula is claimed. -/
theorem future_related {cost' : ℕ} (forward : CostSimulation source target related cost)
    (backward : CostSimulation target source (fun state' state => related state state') cost')
    {Atom : Type} (sourceObserves : Atom → Source → Prop) (targetObserves : Atom → Target → Prop)
    (atoms : ∀ atom, Related related (sourceObserves atom) (targetObserves atom))
    {formula : Tense Atom (List Event)} (future : formula.IsFuture) :
    Related related (Tense.sat (source.segments sourceObserves) formula)
      (Tense.sat (target.segments targetObserves) formula) :=
  sat_related_future (source.segments sourceObserves) (target.segments targetObserves)
    (segmentRelation source target related) segmentRelation_keeps atoms
    forward.segment_sourceForthOcc (segment_sourceBackOcc backward) future

end CostSimulation

end Mettapedia.GSLT.Distinction.ProductiveBlocks
