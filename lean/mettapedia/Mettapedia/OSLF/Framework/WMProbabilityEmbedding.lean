import Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
import Mettapedia.ProbabilityTheory.Hypercube.Taxonomy

/-!
# WM ↔ Probability-Hypercube Embedding/Projection

This module gives a concrete bridge between:

- the 4-axis WM hypercube vertex type (`WMVertex`) from `PLNWMHypercubeBasis`, and
- the full 13-axis probability-theory hypercube (`ProbabilityVertex`).

The bridge is intentionally explicit:

1. `wmToProbabilityVertex` embeds WM vertices into a canonical 13-axis slice.
2. `probabilityToWMVertex` projects 13-axis vertices to WM choices.
3. `probabilityToWMVertex ∘ wmToProbabilityVertex = id` (left inverse).
4. A round-trip theorem on the image slice (`wmToProbabilityVertex ∘ probabilityToWMVertex = id`)
   under explicit side conditions.
5. Monotonicity: WM axis-steps and WM cube paths transport to the probability
   strength order (`≤`) on `ProbabilityVertex`.
-/

namespace Mettapedia.OSLF.Framework.WMProbabilityEmbedding

open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.ProbabilityTheory.Hypercube

/-! ## Axis encoders/decoders -/

/-- WM logic axis embedded into probability distributivity axis. -/
def logicToDistributivity : WMLogic → DistributivityAxis
  | .boolean => .boolean
  | .heyting => .distributive

/-- Probability distributivity projected to WM logic axis. -/
def distributivityToWMLogic : DistributivityAxis → WMLogic
  | .boolean => .boolean
  | _ => .heyting

/-- WM truth-value axis embedded into probability precision axis. -/
def truthValueToPrecision : WMTruthValue → PrecisionAxis
  | .point => .precise
  | .bounds => .imprecise

/-- Probability precision projected to WM truth-value axis. -/
def precisionToTruthValue : PrecisionAxis → WMTruthValue
  | .precise => .point
  | .imprecise => .bounds

/-- WM interval-semantics axis embedded into probability additivity axis. -/
def intervalToAdditivity : WMIntervalSemantics → AdditivityAxis
  | .bayesNormal => .additive
  | .bayesExact => .derived
  | .walleyIDM => .subadditive

/-- Probability additivity projected to WM interval-semantics axis. -/
def additivityToWMInterval : AdditivityAxis → WMIntervalSemantics
  | .additive => .bayesNormal
  | .derived => .bayesExact
  | .subadditive => .walleyIDM

/-- WM typing axis embedded into probability support axis. -/
def typingToSupport : WMQueryTyping → SupportAxis
  | .untyped => .finite
  | .typedSigma => .countable

/-- Probability support projected to WM typing axis. -/
def supportToWMTyping : SupportAxis → WMQueryTyping
  | .finite => .untyped
  | _ => .typedSigma

lemma logicToDistributivity_distributivityToWMLogic_eq_of_bool_or_distributive
    {d : DistributivityAxis}
    (h : d = .boolean ∨ d = .distributive) :
    logicToDistributivity (distributivityToWMLogic d) = d := by
  rcases h with h | h <;> simp [h, distributivityToWMLogic, logicToDistributivity]

@[simp] lemma truthValueToPrecision_precisionToTruthValue (p : PrecisionAxis) :
    truthValueToPrecision (precisionToTruthValue p) = p := by
  cases p <;> rfl

@[simp] lemma intervalToAdditivity_additivityToWMInterval (a : AdditivityAxis) :
    intervalToAdditivity (additivityToWMInterval a) = a := by
  cases a <;> rfl

lemma typingToSupport_supportToWMTyping_eq_of_finite_or_countable
    {s : SupportAxis}
    (h : s = .finite ∨ s = .countable) :
    typingToSupport (supportToWMTyping s) = s := by
  rcases h with h | h <;> simp [h, supportToWMTyping, typingToSupport]

lemma logicToDistributivity_mono {x y : WMLogic}
    (h : wmAxisStep .logic x y) :
    logicToDistributivity x ≤ logicToDistributivity y := by
  cases x <;> cases y <;> simp [wmAxisStep, logicToDistributivity] at h ⊢
  · exact by decide

lemma truthValueToPrecision_mono {x y : WMTruthValue}
    (h : wmAxisStep .truthValue x y) :
    truthValueToPrecision x ≤ truthValueToPrecision y := by
  cases x <;> cases y <;> simp [wmAxisStep, truthValueToPrecision] at h ⊢
  · exact by decide

lemma intervalToAdditivity_mono {x y : WMIntervalSemantics}
    (h : wmAxisStep .interval x y) :
    intervalToAdditivity x ≤ intervalToAdditivity y := by
  cases x <;> cases y <;> simp [wmAxisStep, intervalToAdditivity] at h ⊢
  · exact by decide

lemma typingToSupport_mono {x y : WMQueryTyping}
    (h : wmAxisStep .typing x y) :
    typingToSupport x ≤ typingToSupport y := by
  cases x <;> cases y <;> simp [wmAxisStep, typingToSupport] at h ⊢
  · exact by decide

/-! ## Embedding/projection maps -/

/-- Embed a 4-axis WM vertex into a canonical 13-axis probability vertex. -/
def wmToProbabilityVertex (v : WMVertex) : ProbabilityVertex where
  commutativity := .commutative
  distributivity := logicToDistributivity (v .logic)
  precision := truthValueToPrecision (v .truthValue)
  orderAxis := .totalOrder
  density := .dense
  completeness := .conditionallyComplete
  separation := .ksSeparationStrict
  additivity := intervalToAdditivity (v .interval)
  invertibility := .monoid
  determinism := .probabilistic
  support := typingToSupport (v .typing)
  regularity := .borel
  independence := .tensor

/-- Project a 13-axis probability vertex to the WM 4-axis choices. -/
def probabilityToWMVertex (v : ProbabilityVertex) : WMVertex :=
  mkWMVertex
    (distributivityToWMLogic v.distributivity)
    (precisionToTruthValue v.precision)
    (additivityToWMInterval v.additivity)
    (supportToWMTyping v.support)

@[simp] theorem probabilityToWMVertex_wmToProbabilityVertex (v : WMVertex) :
    probabilityToWMVertex (wmToProbabilityVertex v) = v := by
  funext a
  cases a with
  | logic =>
      cases h : v .logic <;>
        simp [probabilityToWMVertex, wmToProbabilityVertex, mkWMVertex,
          logicToDistributivity, distributivityToWMLogic, h]
  | truthValue =>
      cases h : v .truthValue <;>
        simp [probabilityToWMVertex, wmToProbabilityVertex, mkWMVertex,
          truthValueToPrecision, precisionToTruthValue, h]
  | interval =>
      cases h : v .interval <;>
        simp [probabilityToWMVertex, wmToProbabilityVertex, mkWMVertex,
          intervalToAdditivity, additivityToWMInterval, h]
  | typing =>
      cases h : v .typing <;>
        simp [probabilityToWMVertex, wmToProbabilityVertex, mkWMVertex,
          typingToSupport, supportToWMTyping, h]

theorem wmToProbabilityVertex_injective : Function.Injective wmToProbabilityVertex := by
  intro v w h
  have h' := congrArg probabilityToWMVertex h
  simpa using h'

/-- Characterization of the canonical 13-axis slice used by `wmToProbabilityVertex`. -/
def IsInWMEmbeddingSlice (v : ProbabilityVertex) : Prop :=
  v.commutativity = .commutative ∧
  (v.distributivity = .boolean ∨ v.distributivity = .distributive) ∧
  (v.precision = .precise ∨ v.precision = .imprecise) ∧
  v.orderAxis = .totalOrder ∧
  v.density = .dense ∧
  v.completeness = .conditionallyComplete ∧
  v.separation = .ksSeparationStrict ∧
  (v.additivity = .additive ∨ v.additivity = .derived ∨ v.additivity = .subadditive) ∧
  v.invertibility = .monoid ∧
  v.determinism = .probabilistic ∧
  (v.support = .finite ∨ v.support = .countable) ∧
  v.regularity = .borel ∧
  v.independence = .tensor

theorem wmToProbabilityVertex_probabilityToWMVertex_eq_of_slice
    {v : ProbabilityVertex} (hv : IsInWMEmbeddingSlice v) :
    wmToProbabilityVertex (probabilityToWMVertex v) = v := by
  rcases hv with ⟨hComm, hDist, hPrec, hOrder, hDensity, hComp, hSep,
    hAdd, hInv, hDet, hSupport, hReg, hInd⟩
  ext
  · simp [wmToProbabilityVertex, hComm]
  · unfold probabilityToWMVertex wmToProbabilityVertex
    change logicToDistributivity (distributivityToWMLogic v.distributivity) = v.distributivity
    exact logicToDistributivity_distributivityToWMLogic_eq_of_bool_or_distributive hDist
  · unfold probabilityToWMVertex
    change truthValueToPrecision (precisionToTruthValue v.precision) = v.precision
    exact truthValueToPrecision_precisionToTruthValue v.precision
  · simp [wmToProbabilityVertex, hOrder]
  · simp [wmToProbabilityVertex, hDensity]
  · simp [wmToProbabilityVertex, hComp]
  · simp [wmToProbabilityVertex, hSep]
  · unfold probabilityToWMVertex
    change intervalToAdditivity (additivityToWMInterval v.additivity) = v.additivity
    exact intervalToAdditivity_additivityToWMInterval v.additivity
  · simp [wmToProbabilityVertex, hInv]
  · simp [wmToProbabilityVertex, hDet]
  · unfold probabilityToWMVertex wmToProbabilityVertex
    change typingToSupport (supportToWMTyping v.support) = v.support
    exact typingToSupport_supportToWMTyping_eq_of_finite_or_countable hSupport
  · simp [wmToProbabilityVertex, hReg]
  · simp [wmToProbabilityVertex, hInd]

/-! ## Order transport (WM step/path -> ProbabilityVertex `≤`) -/

theorem wmToProbabilityVertex_mono_axisStep {v w : WMVertex}
    (h : AxisStep wmAxes v w) :
    wmToProbabilityVertex v ≤ wmToProbabilityVertex w := by
  rcases h with ⟨axis, hStep, hUnchanged⟩
  cases axis with
  | logic =>
      have hTV : v .truthValue = w .truthValue := by
        exact hUnchanged .truthValue (by intro hEq; cases hEq)
      have hInterval : v .interval = w .interval := by
        exact hUnchanged .interval (by intro hEq; cases hEq)
      have hTyping : v .typing = w .typing := by
        exact hUnchanged .typing (by intro hEq; cases hEq)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [wmToProbabilityVertex]
      · exact logicToDistributivity_mono hStep
      · simp [wmToProbabilityVertex, hTV]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hInterval]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hTyping]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
  | truthValue =>
      have hLogic : v .logic = w .logic := by
        exact hUnchanged .logic (by intro hEq; cases hEq)
      have hInterval : v .interval = w .interval := by
        exact hUnchanged .interval (by intro hEq; cases hEq)
      have hTyping : v .typing = w .typing := by
        exact hUnchanged .typing (by intro hEq; cases hEq)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hLogic]
      · exact truthValueToPrecision_mono hStep
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hInterval]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hTyping]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
  | interval =>
      have hLogic : v .logic = w .logic := by
        exact hUnchanged .logic (by intro hEq; cases hEq)
      have hTV : v .truthValue = w .truthValue := by
        exact hUnchanged .truthValue (by intro hEq; cases hEq)
      have hTyping : v .typing = w .typing := by
        exact hUnchanged .typing (by intro hEq; cases hEq)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hLogic]
      · simp [wmToProbabilityVertex, hTV]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · exact intervalToAdditivity_mono hStep
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hTyping]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
  | typing =>
      have hLogic : v .logic = w .logic := by
        exact hUnchanged .logic (by intro hEq; cases hEq)
      have hTV : v .truthValue = w .truthValue := by
        exact hUnchanged .truthValue (by intro hEq; cases hEq)
      have hInterval : v .interval = w .interval := by
        exact hUnchanged .interval (by intro hEq; cases hEq)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hLogic]
      · simp [wmToProbabilityVertex, hTV]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex, hInterval]
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]
      · exact typingToSupport_mono hStep
      · simp [wmToProbabilityVertex]
      · simp [wmToProbabilityVertex]

theorem wmToProbabilityVertex_mono_path {v w : WMVertex}
    (π : CubePath wmAxes v w) :
    wmToProbabilityVertex v ≤ wmToProbabilityVertex w := by
  induction π with
  | refl _ => exact le_rfl
  | cons h t ih =>
      exact le_trans (wmToProbabilityVertex_mono_axisStep h) ih

theorem wmToProbabilityVertex_canonicalPath_monotone :
    wmToProbabilityVertex wmVertexClassicalFast ≤
      wmToProbabilityVertex wmVertexGeneralExact :=
  wmToProbabilityVertex_mono_path canonicalPathToGeneralExact

end Mettapedia.OSLF.Framework.WMProbabilityEmbedding
