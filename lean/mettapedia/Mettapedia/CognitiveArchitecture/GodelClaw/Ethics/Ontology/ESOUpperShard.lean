import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.HyperseedBridge
import Mettapedia.CognitiveArchitecture.OpenPsi.FuzzyLogic

set_option autoImplicit false

/-!
# ESO Upper-Shard Semantics

This module adds an explicit semantics layer for the structured upper-shard
claims used by the ethics/WM bridge.

The goal is to avoid treating upper-shard ethics as a bag of disconnected tags.
Instead, we give a small model theory in which:

- value judgments are interpreted by a value semantics,
- deontic judgments are interpreted by a deontic semantics,
- universal-duty, relational, and epistemic-love claims are interpreted by
  dedicated predicates,
- and observation traces can be discussed at the ontology level before WM
  compilation.

This is still a small fragment, but it is already a more faithful landing zone
for an ESO-style upper shard than the bare atom encoder alone.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

open Mettapedia.Ethics
open Mettapedia.Ethics.Gewirth
open Mettapedia.Ethics.GewirthBridge
open Mettapedia.Hyperseed
open Mettapedia.CognitiveArchitecture.Values.Deontological
open Mettapedia.CognitiveArchitecture.Values.Relational
open Mettapedia.CognitiveArchitecture.OpenPsi
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicAbstract

universe u w x

/-- A typed ESO-style source of four-axis structured claims, prior to any
legacy upper-shard bundling or WM lowering. -/
structure StructuredESOTraceSource
    (Obs : Type x) (World : Type u) (Agent : Type u) where
  extract : Obs → Set (StructuredEthicalClaim World Agent)

/-- Frontier obtained from a structured ESO trace source by the primary
structured-claim WM lowering. -/
def StructuredESOTraceSource.frontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Atom : Type*}
    (source : StructuredESOTraceSource Obs World Agent)
    (enc : StructuredEthicsQueryEncoder World Agent Atom) :
    Obs → Set (ConstraintQuery Atom) :=
  structuredClaimFrontier source.extract enc

theorem StructuredESOTraceSource.mem_traceSeed_iff
    {Obs : Type x} {World : Type u} {Agent : Type u} {Atom : Type*}
    (source : StructuredESOTraceSource Obs World Agent)
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (σ : Multiset Obs) (q : ConstraintQuery Atom) :
    q ∈ traceSeed (source.frontier enc) σ ↔
      ∃ o, o ∈ σ ∧ ∃ claim ∈ source.extract o, q = claim.toQuery enc := by
  constructor
  · intro hq
    rcases hq with ⟨o, ho, hfront⟩
    rcases hfront with ⟨claim, hclaim, rfl⟩
    exact ⟨o, ho, claim, hclaim, rfl⟩
  · rintro ⟨o, ho, claim, hclaim, rfl⟩
    exact ⟨o, ho, claim, hclaim, rfl⟩

/-- A graded semantics for the structured upper-shard ontology claims.

Ethical ideals are **regulative**, not constitutive: no finite agent perfectly
realizes universal love, every duty, or every relation.  Instead, each ideal
has a degree of realization in `[0,1]` (using the existing `UnitValue` from
OpenPsi).  Satisfaction is `degree > 0`, giving a natural bridge to WM's
graded evidence.

The propositional/deontic/axiological cases remain boolean (they use
`valueSemantics` and `deonticSemantics` which are already properly
model-theoretic).  Only the dispositional, duty, and relational ideals
are graded. -/
structure ESOUpperShardModel (World : Type u) (Agent : Type u) (Label : Type w) where
  currentWorld : World
  valueSemantics : ValueSemantics World
  deonticSemantics : DeonticSemantics World
  /-- Degree to which epistemic universal love is realized (regulative ideal).
      0 = no realization, 1 = perfect realization. -/
  epistemicUniversalLoveDegree : Agent → UnitValue
  /-- Degree to which each universal duty is realized. -/
  universalDutyDegree : Agent → UniversalDuty → UnitValue
  /-- Degree to which each relational value is realized toward each target. -/
  relationDegree : Agent → Agent → RelationalValueType → UnitValue

/-- Satisfaction for the four-axis structured kernel.  This is the typed
extraction target for ESO-style observations before they are bundled back into
legacy upper-shard claims or lowered into WM queries. -/
def ESOUpperShardModel.SatStructured
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (claim : StructuredEthicalClaim World Agent) : Prop :=
  match claim.content, claim.presentation with
  | .propositional φ, .axiological tag =>
      m.valueSemantics.morally tag φ m.currentWorld
  | .propositional φ, .deontic tag =>
      m.deonticSemantics.deontic tag φ m.currentWorld
  | .propositional φ, .unmodalized =>
      φ m.currentWorld
  | .dispositional a, _ =>
      0 < (m.epistemicUniversalLoveDegree a).val
  | .relational a b r, _ =>
      0 < (m.relationDegree a b r).val

/-- Restricted adequacy hypothesis for the first structured-ethics correctness
theorem: any structured claim satisfied by the source model compiles to a WM
query whose atoms lie inside the chosen support region. -/
def ESOUpperShardModel.RegionSupportAdequate
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (m : ESOUpperShardModel World Agent Label)
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (Γ : Region Atom) : Prop :=
  ∀ claim, m.SatStructured claim → claim.supportedOn enc Γ

/-- First restricted compilation-correctness theorem: if a structured ethics
claim is satisfied in the source model, and the chosen WM support region is
adequate for all satisfied claims, then the compiled WM query has positive
support in the canonical region-support state. -/
theorem ESOUpperShardModel.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (m : ESOUpperShardModel World Agent Label)
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (Γ : Region Atom)
    (hAdequate : m.RegionSupportAdequate enc Γ)
    (claim : StructuredEthicalClaim World Agent)
    (hsat : m.SatStructured claim) :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom))
      (claim.toQuery enc) := by
  apply WMPositiveQuerySupport.of_regionSupportedConstraintQuery
  exact StructuredEthicalClaim.toQuery_supported enc Γ claim (hAdequate claim hsat)

theorem LabeledValueJudgmentSentence.sat_toStructuredClaim_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (role : EthicalRole)
    (s : LabeledValueJudgmentSentence World Agent Label) :
    m.SatStructured (LabeledValueJudgmentSentence.toStructuredClaim s role) ↔
      ValueSemantics.sat m.valueSemantics m.currentWorld s.sentence := by
  simp [LabeledValueJudgmentSentence.toStructuredClaim, ESOUpperShardModel.SatStructured,
    ValueSemantics.sat]

theorem LabeledDeonticSentence.sat_toStructuredClaim_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (role : EthicalRole)
    (s : LabeledDeonticSentence World Agent Label) :
    m.SatStructured (LabeledDeonticSentence.toStructuredClaim s role) ↔
      DeonticSemantics.sat m.deonticSemantics m.currentWorld s.sentence := by
  simp [LabeledDeonticSentence.toStructuredClaim, ESOUpperShardModel.SatStructured,
    DeonticSemantics.sat]

theorem RelationalClaim.sat_toStructuredClaim_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (role : EthicalRole)
    (r : RelationalClaim Agent) :
    m.SatStructured (RelationalClaim.toStructuredClaim (World := World) r role) ↔
      0 < (m.relationDegree r.source r.target r.relation).val := by
  cases r
  simp [RelationalClaim.toStructuredClaim, ESOUpperShardModel.SatStructured]

/-- Positive concrete corollary of the restricted correctness theorem for
deontic sentences. -/
theorem LabeledDeonticSentence.toStructuredClaim_wmPositive_of_sat_and_regionSupportAdequate
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (m : ESOUpperShardModel World Agent Label)
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (Γ : Region Atom)
    (hAdequate : m.RegionSupportAdequate enc Γ)
    (role : EthicalRole)
    (s : LabeledDeonticSentence World Agent Label)
    (hsat : DeonticSemantics.sat m.deonticSemantics m.currentWorld s.sentence) :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom))
      ((LabeledDeonticSentence.toStructuredClaim s role).toQuery enc) := by
  apply m.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate enc Γ hAdequate
  exact (LabeledDeonticSentence.sat_toStructuredClaim_iff m role s).2 hsat

/-- Positive concrete corollary of the restricted correctness theorem for
value-judgment sentences. -/
theorem LabeledValueJudgmentSentence.toStructuredClaim_wmPositive_of_sat_and_regionSupportAdequate
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (m : ESOUpperShardModel World Agent Label)
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (Γ : Region Atom)
    (hAdequate : m.RegionSupportAdequate enc Γ)
    (role : EthicalRole)
    (s : LabeledValueJudgmentSentence World Agent Label)
    (hsat : ValueSemantics.sat m.valueSemantics m.currentWorld s.sentence) :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom))
      ((LabeledValueJudgmentSentence.toStructuredClaim s role).toQuery enc) := by
  apply m.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate enc Γ hAdequate
  exact (LabeledValueJudgmentSentence.sat_toStructuredClaim_iff m role s).2 hsat

/-- Satisfaction for upper-shard claims in an `ESOUpperShardModel`. -/
def ESOUpperShardModel.Sat
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (claim : UpperShardEthicalClaim World Agent Label) : Prop :=
  match claim with
  | .disposition (.epistemicUniversalLove a) =>
      0 < (m.epistemicUniversalLoveDegree a).val
  | .normative n =>
      match n with
      | .presentedValue s =>
          ValueSemantics.sat m.valueSemantics m.currentWorld s.sentence
      | .presentedDeontic s =>
          DeonticSemantics.sat m.deonticSemantics m.currentWorld s.sentence
      | .groundedUniversalDuty a d =>
          0 < (m.universalDutyDegree a d).val
      | .groundedGewirthRight claim =>
          DeonticSemantics.sat m.deonticSemantics m.currentWorld claim.toDeonticSentence.sentence
  | .relational r =>
      0 < (m.relationDegree r.source r.target r.relation).val

/-- `Semantics` wrapper for the upper-shard claim type. -/
def esoUpperShardSemantics
    {World : Type u} {Agent : Type u} {Label : Type w} :
    Semantics (UpperShardEthicalClaim World Agent Label)
      (ESOUpperShardModel World Agent Label) :=
  ⟨fun m claim => m.Sat claim⟩

@[simp] theorem sat_epistemicUniversalLove_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label) (a : Agent) :
    m.Sat (.disposition (.epistemicUniversalLove a)) ↔ 0 < (m.epistemicUniversalLoveDegree a).val := by
  simp [ESOUpperShardModel.Sat]

@[simp] theorem sat_valueJudgment_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (s : LabeledValueJudgmentSentence World Agent Label) :
    m.Sat (.normative (.presentedValue s)) ↔
      ValueSemantics.sat m.valueSemantics m.currentWorld s.sentence := by
  simp [ESOUpperShardModel.Sat]

@[simp] theorem sat_deonticSentence_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (s : LabeledDeonticSentence World Agent Label) :
    m.Sat (.normative (.presentedDeontic s)) ↔
      DeonticSemantics.sat m.deonticSemantics m.currentWorld s.sentence := by
  simp [ESOUpperShardModel.Sat]

@[simp] theorem sat_universalDuty_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label) (a : Agent) (d : UniversalDuty) :
    m.Sat (.normative (.groundedUniversalDuty a d)) ↔ 0 < (m.universalDutyDegree a d).val := by
  simp [ESOUpperShardModel.Sat]

@[simp] theorem sat_relational_iff
    {World : Type u} {Agent : Type u} {Label : Type w}
    (m : ESOUpperShardModel World Agent Label)
    (a b : Agent) (r : RelationalValueType) :
    m.Sat (.relational { source := a, target := b, relation := r }) ↔
      0 < (m.relationDegree a b r).val := by
  simp [ESOUpperShardModel.Sat]

/-- A Gewirth-focused upper-shard model: deontic semantics from PGC, all
regulative ideals at zero (no realization of dispositional/duty/relational
ideals claimed — only the deontic obligation component is active). -/
noncomputable def ESOUpperShardModel.ofGewirth
    {Label : Type w} (I : PGCInterpretation) (c : I.Ctx) :
    ESOUpperShardModel (I.Ctx × I.World) I.Entity Label where
  currentWorld := (c, I.worldOf c)
  valueSemantics := { morally := fun _ _ _ => False }
  deonticSemantics := deonticSemanticsOfGewirthOi (Ctx := I.Ctx) I.ob I.pv
  epistemicUniversalLoveDegree := fun _ => UnitValue.zero
  universalDutyDegree := fun _ _ => UnitValue.zero
  relationDegree := fun _ _ _ => UnitValue.zero

/-- The Gewirth PGC bridge yields satisfaction of the corresponding structured
upper-shard claim in the canonical Gewirth-based upper-shard model. -/
theorem LabeledGewirthRightClaim.sat_toUpperShard_of_PPA
    {Label : Type w} {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (claim : LabeledGewirthRightClaim Label I)
    (hPPA : PPA I.ActsOnPurpose claim.agent claim.context (I.worldOf claim.context)) :
    (ESOUpperShardModel.ofGewirth (Label := Label) I claim.context).Sat claim.toUpperShard := by
  simpa [LabeledGewirthRightClaim.toUpperShard, ESOUpperShardModel.ofGewirth,
      ESOUpperShardModel.Sat] using
    claim.sat_toDeonticSentence_of_PPA h hPPA

theorem LabeledGewirthRightClaim.sat_toStructuredClaim_of_PPA
    {Label : Type w} {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (claim : LabeledGewirthRightClaim Label I)
    (hPPA : PPA I.ActsOnPurpose claim.agent claim.context (I.worldOf claim.context)) :
    (ESOUpperShardModel.ofGewirth (Label := Label) I claim.context).SatStructured
      claim.toStructuredClaim := by
  simpa [LabeledGewirthRightClaim.toStructuredClaim, LabeledDeonticSentence.toStructuredClaim,
      ESOUpperShardModel.ofGewirth, ESOUpperShardModel.SatStructured, DeonticSemantics.sat]
    using claim.sat_toDeonticSentence_of_PPA h hPPA

/-- An ontology-level trace source for structured upper-shard claims. -/
structure ESOUpperShardTraceSource
    (Obs : Type x) (World : Type u) (Agent : Type u) (Label : Type w) where
  extract : Obs → Set (UpperShardEthicalClaim World Agent Label)

/-- Frontier obtained from an ontology trace source by final WM lowering. -/
def ESOUpperShardTraceSource.frontier
    {Obs : Type x} {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (source : ESOUpperShardTraceSource Obs World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom) :
    Obs → Set (ConstraintQuery Atom) :=
  upperShardFrontier source.extract enc

/-- Trace-seed membership for an ontology trace source. -/
theorem ESOUpperShardTraceSource.mem_traceSeed_iff
    {Obs : Type x} {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (source : ESOUpperShardTraceSource Obs World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (σ : Multiset Obs) (q : ConstraintQuery Atom) :
    q ∈ traceSeed (source.frontier enc) σ ↔
      ∃ o, o ∈ σ ∧ ∃ claim ∈ source.extract o, q = claim.toQuery enc := by
  constructor
  · intro hq
    rcases hq with ⟨o, ho, hfront⟩
    rcases hfront with ⟨claim, hclaim, rfl⟩
    exact ⟨o, ho, claim, hclaim, rfl⟩
  · rintro ⟨o, ho, claim, hclaim, rfl⟩
    exact ⟨o, ho, claim, hclaim, rfl⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
