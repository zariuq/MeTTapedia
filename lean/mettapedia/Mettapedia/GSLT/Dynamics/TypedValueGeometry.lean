import Mettapedia.GSLT.Dynamics.CandidateLocalResolution
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

/-!
# Typed optional values, geometry, symmetry, and choice

Candidate values need not be one scalar and need not be present on every
occurrence.  This module makes four boundaries explicit.

* `ValueGeometry` equips an arbitrary value carrier with a directed metric.
  Symmetry is an additional property rather than an assumption, so the same
  interface covers symmetric statistical distances and directed control cost.
* `OptionalValuation` makes absence a real case.  Attaching such values and
  erasing them recovers the exact occurrence list.
* `Guidance` derives a priority from present values and an authored fallback.
  It does not remove candidates.  `resolveMax` is a separate, bag-relative
  choice boundary.
* Equivariance and isometric actions state when a value channel respects a
  modeled symmetry.  A four-coordinate rank-two tensor is a routine value
  inhabitant; an invariant readout and a non-invariant coordinate probe show
  that tensor shape alone does not confer symmetry.

No representation field is added to atoms here.  The existing sparse typed
annotation rows can carry these values only where an application requests
them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.TypedValueGeometry

open Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
open Mettapedia.GSLT.Dynamics.CandidateLocalResolution

universe uCandidate uValue uPriority uTarget uCost

variable {Candidate : Type uCandidate} {Value : Type uValue}
  {Priority : Type uPriority} {Target : Type uTarget}

/-! ## Local geometric structure on a value carrier -/

/-- A directed real-valued pseudometric.  Omitting symmetry permits
asymmetric effort, reachability, and control geometries; `Symmetric` restores
the ordinary pseudometric case. -/
structure ValueGeometry (Value : Type uValue) where
  distance : Value → Value → ℝ
  nonnegative : ∀ first second, 0 ≤ distance first second
  self : ∀ value, distance value value = 0
  triangle : ∀ first middle last,
    distance first last ≤ distance first middle + distance middle last

namespace ValueGeometry

/-- The directed geometry happens to be symmetric. -/
def Symmetric (geometry : ValueGeometry Value) : Prop :=
  ∀ first second, geometry.distance first second =
    geometry.distance second first

/-- Every Mathlib pseudometric supplies a local value geometry.  Keeping the
instance inside this constructor permits several authored geometries on the
same value carrier elsewhere. -/
noncomputable def ofPseudoMetric (Value : Type uValue)
    [PseudoMetricSpace Value] : ValueGeometry Value where
  distance := dist
  nonnegative := fun _ _ => dist_nonneg
  self := dist_self
  triangle := dist_triangle

theorem ofPseudoMetric_symmetric (Value : Type uValue)
    [PseudoMetricSpace Value] :
    (ofPseudoMetric Value).Symmetric := by
  intro first second
  exact dist_comm first second

/-- Pull a geometry back along an arbitrary representation map.  Distinct
source values may become distance zero when the representation forgets their
difference, which is why the result remains a pseudometric interface. -/
def comap (geometry : ValueGeometry Target) (translate : Value → Target) :
    ValueGeometry Value where
  distance first second := geometry.distance (translate first) (translate second)
  nonnegative first second := geometry.nonnegative (translate first) (translate second)
  self value := geometry.self (translate value)
  triangle first middle last :=
    geometry.triangle (translate first) (translate middle) (translate last)

/-- A map preserves the complete geometric observation. -/
def Preserves (source : ValueGeometry Value)
    (target : ValueGeometry Target) (translate : Value → Target) : Prop :=
  ∀ first second,
    target.distance (translate first) (translate second) =
      source.distance first second

/-- The representation map preserves its own pulled-back geometry exactly. -/
theorem comap_preserves (geometry : ValueGeometry Target)
    (translate : Value → Target) :
    (geometry.comap translate).Preserves geometry translate := by
  intro first second
  rfl

theorem preserves_id (geometry : ValueGeometry Value) :
    geometry.Preserves geometry id := by
  intro first second
  rfl

theorem Preserves.comp
    {First : Type uValue} {Second : Type uTarget} {Third : Type uPriority}
    {firstGeometry : ValueGeometry First}
    {secondGeometry : ValueGeometry Second}
    {thirdGeometry : ValueGeometry Third}
    {firstMap : First → Second} {secondMap : Second → Third}
    (firstPreserves : firstGeometry.Preserves secondGeometry firstMap)
    (secondPreserves : secondGeometry.Preserves thirdGeometry secondMap) :
    firstGeometry.Preserves thirdGeometry (secondMap ∘ firstMap) := by
  intro first second
  rw [Function.comp_apply, Function.comp_apply,
    secondPreserves, firstPreserves]

end ValueGeometry

/-! ## Symmetry-compatible valuations -/

/-- A valuation transports the modeled action on candidates to the modeled
action on values. -/
def EquivariantValuation
    (Symmetry : Type uCost) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    (Value : Type uValue) [MulAction Symmetry Value]
    (valuation : Candidate → Value) : Prop :=
  ∀ (symmetry : Symmetry) candidate,
    valuation (symmetry • candidate) = symmetry • valuation candidate

/-- Every symmetry acts by isometries of the authored geometry. -/
def IsometricAction
    (Symmetry : Type uCost) [Group Symmetry]
    (Value : Type uValue) [MulAction Symmetry Value]
    (geometry : ValueGeometry Value) : Prop :=
  ∀ (symmetry : Symmetry) first second,
    geometry.distance (symmetry • first) (symmetry • second) =
      geometry.distance first second

/-- Transforming a candidate and the target together preserves geometric
guidance.  This is the elementary mind/world symmetry square. -/
theorem distance_guidance_equivariant
    (Symmetry : Type uCost) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    (Value : Type uValue) [MulAction Symmetry Value]
    (geometry : ValueGeometry Value) (valuation : Candidate → Value)
    (valuationEquivariant :
      EquivariantValuation Symmetry Candidate Value valuation)
    (actionIsometric : IsometricAction Symmetry Value geometry)
    (symmetry : Symmetry) (candidate : Candidate) (target : Value) :
    geometry.distance (valuation (symmetry • candidate))
        (symmetry • target) =
      geometry.distance (valuation candidate) target := by
  rw [valuationEquivariant symmetry candidate]
  exact actionIsometric symmetry (valuation candidate) target

/-! ## Optional values and guidance -/

/-- A candidate-local value that can be physically absent. -/
abbrev OptionalValuation (Candidate : Type uCandidate)
    (Value : Type uValue) := Candidate → Option Value

/-- No candidate carries this value channel. -/
def noValues (Candidate : Type uCandidate) (Value : Type uValue) :
    OptionalValuation Candidate Value :=
  fun _ => none

/-- Materialize the optional channel beside occurrences.  This is a semantic
view; a sparse sidecar may realize it without per-atom storage. -/
def attachOptionalValues
    (valuation : OptionalValuation Candidate Value)
    (occurrences : List Candidate) :
    List (ValuedOccurrence Candidate (Option Value)) :=
  attachValues valuation occurrences

/-- Values, including their absence, do not change the underlying occurrence
sequence. -/
@[simp] theorem erase_attachOptionalValues
    (valuation : OptionalValuation Candidate Value)
    (occurrences : List Candidate) :
    (attachOptionalValues valuation occurrences).map
        ValuedOccurrence.occurrence = occurrences := by
  exact erase_attachValues valuation occurrences

/-- Candidate-local advice.  Missing values use an authored fallback; no
candidate is selected or rejected by this structure. -/
structure Guidance (Candidate : Type uCandidate) (Value : Type uValue)
    (Priority : Type uPriority) where
  value : OptionalValuation Candidate Value
  priorityOf : Value → Priority
  fallback : Candidate → Priority

namespace Guidance

/-- Read a candidate's scheduling or resolution priority. -/
def priority (guidance : Guidance Candidate Value Priority)
    (candidate : Candidate) : Priority :=
  match guidance.value candidate with
  | some value => guidance.priorityOf value
  | none => guidance.fallback candidate

@[simp] theorem priority_present
    (guidance : Guidance Candidate Value Priority) (candidate : Candidate)
    (value : Value) (present : guidance.value candidate = some value) :
    guidance.priority candidate = guidance.priorityOf value := by
  simp [priority, present]

@[simp] theorem priority_absent
    (guidance : Guidance Candidate Value Priority) (candidate : Candidate)
    (absent : guidance.value candidate = none) :
    guidance.priority candidate = guidance.fallback candidate := by
  simp [priority, absent]

/-- Exact maximum is an explicit whole-bag resolver layered over guidance. -/
noncomputable def resolveMax (guidance : Guidance Candidate Value Nat) :
    Multiset Candidate → Multiset Candidate :=
  Mettapedia.GSLT.Core.maxSelector guidance.priority

/-- When priorities distinguish two candidates, exact maximum resolution is
not candidate-local.  The value wire therefore does not secretly grant a
local where-clause whole-race authority. -/
theorem resolveMax_not_candidateLocalizable
    (guidance : Guidance Candidate Value Nat)
    {low high : Candidate}
    (outweighed : guidance.priority low < guidance.priority high) :
    ¬ CandidateLocalizable guidance.resolveMax := by
  simpa [resolveMax] using
    (maxSelector_not_candidateLocalizable guidance.priority outweighed)

end Guidance

/-! ## A genuine four-coordinate tensor value -/

/-- A rank-two tensor over four coordinates.  This is the same carrier as a
four-by-four real matrix, written transparently as a finite function so its
ordinary product metric is available without imposing a tensor on atoms. -/
abbrev Tensor4 := Fin 4 → Fin 4 → ℝ

/-- Relabel both tensor indices by one coordinate symmetry. -/
def relabelTensor (symmetry : Equiv.Perm (Fin 4))
    (tensor : Tensor4) : Tensor4 :=
  fun first second => tensor (symmetry.symm first) (symmetry.symm second)

/-- Frobenius energy, used here as a simple invariant scalar readout. -/
noncomputable def tensorEnergy (tensor : Tensor4) : ℝ :=
  ∑ first, ∑ second, tensor first second ^ 2

/-- Coordinate relabeling preserves tensor energy. -/
theorem tensorEnergy_relabel
    (symmetry : Equiv.Perm (Fin 4)) (tensor : Tensor4) :
    tensorEnergy (relabelTensor symmetry tensor) = tensorEnergy tensor := by
  unfold tensorEnergy relabelTensor
  calc
    (∑ first, ∑ second,
        tensor (symmetry.symm first) (symmetry.symm second) ^ 2) =
        ∑ first, ∑ second, tensor (symmetry.symm first) second ^ 2 := by
      apply Finset.sum_congr rfl
      intro first _
      exact symmetry.symm.sum_comp
        (fun second => tensor (symmetry.symm first) second ^ 2)
    _ = ∑ first, ∑ second, tensor first second ^ 2 := by
      exact symmetry.symm.sum_comp
        (fun first => ∑ second, tensor first second ^ 2)

/-- The ordinary finite-product pseudometric is one possible geometry for
the tensor carrier.  Fisher, Lorentzian, or task-learned geometries are
different authored structures on the same carrier. -/
noncomputable def tensorProductGeometry : ValueGeometry Tensor4 :=
  ValueGeometry.ofPseudoMetric Tensor4

/-- A coordinate basis tensor. -/
def basisTensor (row column : Fin 4) : Tensor4 :=
  fun first second => if first = row ∧ second = column then 1 else 0

def swapZeroOne : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

/-- Negative control: a fixed raw-coordinate probe is not invariant under a
coordinate relabeling.  Carrying a tensor is therefore not enough; programs
that claim symmetry must prove it of their observations. -/
theorem fixed_coordinate_probe_not_invariant :
    (relabelTensor swapZeroOne (basisTensor 0 0)) 0 0 = 0 ∧
      (basisTensor 0 0) 0 0 = 1 := by
  norm_num [relabelTensor, swapZeroOne, basisTensor]

/-! ## Sparse heterogeneous channel witness -/

inductive CognitiveChannel
  | scalar
  | featureVector
  | tensor
  | evidence
deriving DecidableEq, Repr

/-- Scalars, vectors, tensors, and evidence coexist without conversion to one
untyped payload. -/
def cognitiveSchema : AnnotationSchema where
  Channel := CognitiveChannel
  Payload
    | .scalar => ℝ
    | .featureVector => Fin 4 → ℝ
    | .tensor => Tensor4
    | .evidence => Nat × Nat

/-- One occurrence may carry only a tensor channel. -/
def tensorOnlyRow (tensor : Tensor4) : AnnotationRow cognitiveSchema
  | .tensor => some tensor
  | _ => none

@[simp] theorem tensorOnlyRow_tensor (tensor : Tensor4) :
    tensorOnlyRow tensor .tensor = some tensor :=
  rfl

@[simp] theorem tensorOnlyRow_scalar_absent (tensor : Tensor4) :
    tensorOnlyRow tensor .scalar = none :=
  rfl

/-! ## Axiom audit -/

#print axioms ValueGeometry.Preserves.comp
#print axioms distance_guidance_equivariant
#print axioms erase_attachOptionalValues
#print axioms Guidance.resolveMax_not_candidateLocalizable
#print axioms tensorEnergy_relabel
#print axioms fixed_coordinate_probe_not_invariant

end Mettapedia.GSLT.Dynamics.TypedValueGeometry
