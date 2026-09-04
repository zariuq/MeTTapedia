import Mathlib.Data.Finset.Grade
import Mathlib.Topology.MetricSpace.PiNat
import Mettapedia.GSLT.Core.UltrainfiniteDoctrineFactorization
import Mettapedia.Logic.GunkyMereology

/-!
# Atomlessness generated from finite Boolean stages

Finite Boolean algebras are necessarily atomic.  Nevertheless, the clopen
algebra of Cantor space can be presented through finite prefix stages in which
every nonempty element acquires a strict nonempty refinement one stage later.

This module separates those two statements.  A stage is a finite set of
Boolean prefixes of one fixed length.  Advancing a stage admits both one-bit
extensions of every selected prefix.  Realization sends the finite stage to
the corresponding clopen union in Cantor space.  Realization is injective,
commutes with advance, preserves nonemptiness, and exposes genuinely new
next-stage elements.  Hence it forms a nontrivial
`GenerativeUnboundedGround`.

Every individual finite stage still contains singleton atoms.  The
atomlessness law is cross-stage: a singleton prefix at one level splits into
two children at the next.  The ambient Cantor-clopen algebra is independently
known to be gunky.  Thus finite presentation and atomless semantic ground are
compatible without pretending that any finite stage is itself atomless.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Ultrainfinite.GenerativeCantorAtomlessness

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.Ultrainfinite.DoctrineFactorization
open TopologicalSpace

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩

/-! ## Finite prefix stages -/

/-- Boolean observations at one finite prefix length. -/
abbrev Prefix (level : Nat) := Fin level → Bool

/-- A finite-stage Boolean region is a finite collection of prefixes. -/
abbrev FiniteBooleanStage (level : Nat) := Finset (Prefix level)

/-- Restrict a one-bit-longer prefix to its old coordinates. -/
def truncate {level : Nat} (bits : Prefix (level + 1)) : Prefix level :=
  fun coordinate => bits coordinate.castSucc

/-- Extend a prefix with one new final Boolean coordinate. -/
def extend {level : Nat} (bits : Prefix level) (last : Bool) :
    Prefix (level + 1) :=
  Fin.lastCases last bits

@[simp] theorem truncate_extend {level : Nat} (bits : Prefix level)
    (last : Bool) :
    truncate (extend bits last) = bits := by
  funext coordinate
  simp [truncate, extend]

@[simp] theorem extend_last {level : Nat} (bits : Prefix level)
    (last : Bool) :
    extend bits last (Fin.last level) = last := by
  simp [extend]

theorem extend_false_ne_true {level : Nat} (bits : Prefix level) :
    extend bits false ≠ extend bits true := by
  intro equalExtensions
  have equalLast := congrFun equalExtensions (Fin.last level)
  simp at equalLast

/-- Advance a finite region by admitting both children of every prefix. -/
def advance (level : Nat) (stage : FiniteBooleanStage level) :
    FiniteBooleanStage (level + 1) :=
  Finset.univ.filter fun bits => truncate bits ∈ stage

@[simp] theorem mem_advance {level : Nat}
    {stage : FiniteBooleanStage level} {bits : Prefix (level + 1)} :
    bits ∈ advance level stage ↔ truncate bits ∈ stage := by
  simp [advance]

/-! ## Realization as Cantor clopens -/

/-- Read the first `level` coordinates of one Cantor-space point. -/
def takePrefix (level : Nat) (world : Nat → Bool) : Prefix level :=
  fun coordinate => world coordinate.val

@[simp] theorem truncate_takePrefix (level : Nat) (world : Nat → Bool) :
    truncate (takePrefix (level + 1) world) = takePrefix level world := by
  rfl

/-- Extend a finite prefix to an infinite point by filling the tail with
`false`. -/
def worldOfPrefix {level : Nat} (bits : Prefix level) : Nat → Bool :=
  fun coordinate =>
    if inPrefix : coordinate < level then bits ⟨coordinate, inPrefix⟩
    else false

@[simp] theorem takePrefix_worldOfPrefix {level : Nat} (bits : Prefix level) :
    takePrefix level (worldOfPrefix bits) = bits := by
  funext coordinate
  simp [takePrefix, worldOfPrefix, coordinate.isLt]

theorem continuous_takePrefix (level : Nat) : Continuous (takePrefix level) := by
  apply continuous_pi
  intro coordinate
  exact continuous_apply coordinate.val

/-- A finite-stage region denotes the clopen set of infinite paths whose
prefix belongs to that region. -/
noncomputable def realize (level : Nat) (stage : FiniteBooleanStage level) :
    Clopens (Nat → Bool) :=
  ⟨takePrefix level ⁻¹' (stage : Set (Prefix level)),
    (isClopen_discrete (stage : Set (Prefix level))).preimage
      (continuous_takePrefix level)⟩

@[simp] theorem mem_realize {level : Nat}
    (stage : FiniteBooleanStage level) (world : Nat → Bool) :
    world ∈ (realize level stage : Set (Nat → Bool)) ↔
      takePrefix level world ∈ stage :=
  Iff.rfl

theorem realize_injective (level : Nat) :
    Function.Injective (realize level) := by
  intro first second equalRealizations
  apply Finset.ext
  intro bits
  have equalMembership :
      worldOfPrefix bits ∈ (realize level first : Set (Nat → Bool)) ↔
        worldOfPrefix bits ∈ (realize level second : Set (Nat → Bool)) := by
    rw [equalRealizations]
  change
    takePrefix level (worldOfPrefix bits) ∈ first ↔
      takePrefix level (worldOfPrefix bits) ∈ second at equalMembership
  simpa using equalMembership

theorem realize_advance (level : Nat) (stage : FiniteBooleanStage level) :
    realize (level + 1) (advance level stage) = realize level stage := by
  ext world
  simp [realize]

/-- The singleton all-false child cannot be an advanced stage: advanced
regions always contain either both children of a selected prefix or neither. -/
def freshStage (level : Nat) : FiniteBooleanStage (level + 1) :=
  {extend (fun _coordinate => false) false}

theorem advance_ne_freshStage (level : Nat)
    (stage : FiniteBooleanStage level) :
    advance level stage ≠ freshStage level := by
  let zero : Prefix level := fun _coordinate => false
  by_cases selected : zero ∈ stage
  · intro equalStages
    have trueChildSelected : extend zero true ∈ advance level stage := by
      simp [selected]
    rw [equalStages] at trueChildSelected
    have differentChildren : extend zero true ≠ extend zero false :=
      (extend_false_ne_true zero).symm
    exact differentChildren (by simpa [freshStage] using trueChildSelected)
  · intro equalStages
    have falseChildAbsent : extend zero false ∉ advance level stage := by
      simp [selected]
    apply falseChildAbsent
    rw [equalStages]
    simp [freshStage, zero]

theorem realize_nonempty_iff (level : Nat)
    (stage : FiniteBooleanStage level) :
    (realize level stage : Set (Nat → Bool)).Nonempty ↔ stage.Nonempty := by
  constructor
  · rintro ⟨world, worldIn⟩
    change takePrefix level world ∈ stage at worldIn
    exact ⟨takePrefix level world, worldIn⟩
  · rintro ⟨bits, bitsIn⟩
    refine ⟨worldOfPrefix bits, ?_⟩
    change takePrefix level (worldOfPrefix bits) ∈ stage
    simpa using bitsIn

/-! ## Exhaustivity of the finite presentation -/

/-- Every point of a clopen Cantor region has a cylinder neighbourhood whose
length may depend on the point. -/
theorem exists_cylinder_subset (region : Clopens (Nat → Bool))
    (world : Nat → Bool) (worldIn : world ∈ region) :
    ∃ level, PiNat.cylinder world level ⊆ (region : Set (Nat → Bool)) := by
  obtain ⟨neighbourhood, ⟨centre, level, neighbourhoodEq⟩,
      worldInNeighbourhood, neighbourhoodSubset⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : Nat => Bool)).exists_subset_of_mem_open
      worldIn region.isOpen
  subst neighbourhood
  refine ⟨level, ?_⟩
  rw [PiNat.mem_cylinder_iff_eq.mp worldInNeighbourhood]
  exact neighbourhoodSubset

/-- Compactness upgrades the point-dependent cylinder depths to one uniform
finite prefix length for the entire clopen region. -/
theorem exists_uniform_cylinder_subset (region : Clopens (Nat → Bool)) :
    ∃ level, ∀ world : Nat → Bool, world ∈ region →
      PiNat.cylinder world level ⊆ (region : Set (Nat → Bool)) := by
  classical
  choose radius radiusSubset using
    fun world : { world : Nat → Bool // world ∈ region } =>
      exists_cylinder_subset region world world.property
  have compactRegion : IsCompact (region : Set (Nat → Bool)) :=
    isCompact_univ.of_isClosed_subset region.isClosed (Set.subset_univ _)
  obtain ⟨centres, centresCover⟩ := compactRegion.elim_finite_subcover
    (fun world : { world : Nat → Bool // world ∈ region } =>
      PiNat.cylinder (world : Nat → Bool) (radius world))
    (fun world => PiNat.isOpen_cylinder (fun _ : Nat => Bool) world (radius world))
    (by
      intro world worldIn
      exact Set.mem_iUnion.mpr
        ⟨⟨world, worldIn⟩, PiNat.self_mem_cylinder world _⟩)
  let level := centres.sup radius
  refine ⟨level, ?_⟩
  intro world worldIn y yIn
  obtain ⟨centre, centreIn, worldNearCentre⟩ :=
    Set.mem_iUnion₂.mp (centresCover worldIn)
  apply radiusSubset centre
  rw [PiNat.mem_cylinder_iff]
  intro coordinate coordinateBelowRadius
  have coordinateBelowLevel : coordinate < level :=
    coordinateBelowRadius.trans_le (Finset.le_sup centreIn)
  exact
    (PiNat.mem_cylinder_iff.mp yIn coordinate coordinateBelowLevel).trans
      (PiNat.mem_cylinder_iff.mp worldNearCentre coordinate
        coordinateBelowRadius)

/-- Select exactly those prefixes whose canonical infinite extension belongs
to the clopen region. -/
noncomputable def stageFor (region : Clopens (Nat → Bool)) (level : Nat) :
    FiniteBooleanStage level := by
  classical
  exact Finset.univ.filter fun bits => worldOfPrefix bits ∈ region

/-- At a uniform cylinder depth, the selected finite stage realizes exactly
the original clopen region. -/
theorem realize_stageFor_of_uniform (region : Clopens (Nat → Bool))
    (level : Nat)
    (uniform : ∀ world : Nat → Bool, world ∈ region →
      PiNat.cylinder world level ⊆ (region : Set (Nat → Bool))) :
    realize level (stageFor region level) = region := by
  apply SetLike.ext
  intro world
  change takePrefix level world ∈ stageFor region level ↔ world ∈ region
  simp only [stageFor, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro representativeIn
    apply uniform (worldOfPrefix (takePrefix level world)) representativeIn
    rw [PiNat.mem_cylinder_iff]
    intro coordinate coordinateBelow
    simp [worldOfPrefix, takePrefix, coordinateBelow]
  · intro worldIn
    apply uniform world worldIn
    rw [PiNat.mem_cylinder_iff]
    intro coordinate coordinateBelow
    simp [worldOfPrefix, takePrefix, coordinateBelow]

/-- Every Cantor clopen is represented at some finite Boolean prefix stage. -/
theorem cantorGeneration_exhaustive (region : Clopens (Nat → Bool)) :
    ∃ level stage, realize level stage = region := by
  obtain ⟨level, uniform⟩ := exists_uniform_cylinder_subset region
  exact ⟨level, stageFor region level,
    realize_stageFor_of_uniform region level uniform⟩

/-- The finite-prefix presentation is a genuine generative-unbounded ground
of the Cantor clopen algebra.  Its local observation records nonemptiness. -/
noncomputable def cantorGeneration :
    GenerativeUnboundedGround
      (Clopens (Nat → Bool)) Prop FiniteBooleanStage where
  stageFinite := fun _level => inferInstance
  advance := advance
  realize := realize
  realize_injective := realize_injective
  realize_advance := realize_advance
  fresh := fun level => ⟨freshStage level, advance_ne_freshStage level⟩
  observeWhole := fun region => (region : Set (Nat → Bool)).Nonempty
  observeStage := fun _level stage => stage.Nonempty
  observe_realize := by
    intro level stage
    apply propext
    exact (realize_nonempty_iff level stage).symm

/-- The finite-prefix presentation is not only unbounded but exhaustive: its
filtered union is the entire Cantor-clopen semantic carrier. -/
noncomputable def exhaustiveCantorGeneration :
    ExhaustiveGenerativeGround
      (Clopens (Nat → Bool)) Prop FiniteBooleanStage where
  toGenerativeUnboundedGround := cantorGeneration
  exhaustive := cantorGeneration_exhaustive

/-! ## Stagewise atomicity versus cross-stage splitting -/

/-- Every finite stage is atomic; a singleton prefix is an explicit atom. -/
theorem finite_stage_has_atom (level : Nat) :
    ∃ atom : FiniteBooleanStage level, IsAtom atom :=
  ⟨{fun _coordinate => false}, Finset.isAtom_singleton _⟩

/-- Consequently no individual finite stage is gunky. -/
theorem finite_stage_not_gunky (level : Nat) :
    ¬ IsGunky (FiniteBooleanStage level) :=
  not_isGunky_of_finite

/-- One selected prefix has a nonempty child contained in the advanced
region. -/
def falseChild {level : Nat} (bits : Prefix level) :
    FiniteBooleanStage (level + 1) :=
  {extend bits false}

theorem falseChild_nonempty {level : Nat} (bits : Prefix level) :
    (falseChild bits).Nonempty := by
  simp [falseChild]

theorem falseChild_subset_advance {level : Nat}
    {stage : FiniteBooleanStage level} {bits : Prefix level}
    (selected : bits ∈ stage) :
    falseChild bits ⊆ advance level stage := by
  intro child childIn
  simp only [falseChild, Finset.mem_singleton] at childIn
  subst child
  simp [selected]

theorem falseChild_ne_advance {level : Nat}
    {stage : FiniteBooleanStage level} {bits : Prefix level}
    (selected : bits ∈ stage) :
    falseChild bits ≠ advance level stage := by
  intro equalStages
  have trueChildSelected : extend bits true ∈ advance level stage := by
    simp [selected]
  rw [← equalStages] at trueChildSelected
  have differentChildren : extend bits true ≠ extend bits false :=
    (extend_false_ne_true bits).symm
  exact differentChildren (by simpa [falseChild] using trueChildSelected)

/-- Every nonempty region receives a strict nonempty refinement one level
later.  This is the generative atomlessness law. -/
theorem next_stage_splits_every_nonempty (level : Nat)
    (stage : FiniteBooleanStage level) (nonempty : stage.Nonempty) :
    ∃ child : FiniteBooleanStage (level + 1),
      child.Nonempty ∧ child ⊆ advance level stage ∧
        child ≠ advance level stage := by
  obtain ⟨bits, selected⟩ := nonempty
  exact ⟨falseChild bits, falseChild_nonempty bits,
    falseChild_subset_advance selected,
    falseChild_ne_advance selected⟩

theorem realize_mono {level : Nat}
    {first second : FiniteBooleanStage level} (subset : first ⊆ second) :
    realize level first ≤ realize level second := by
  intro world worldIn
  change takePrefix level world ∈ first at worldIn
  change takePrefix level world ∈ second
  exact subset worldIn

/-- The cross-stage split is a genuine strict nonempty part after realization
in the ambient Cantor algebra. -/
theorem realized_next_stage_splits_every_nonempty (level : Nat)
    (stage : FiniteBooleanStage level) (nonempty : stage.Nonempty) :
    ∃ child : FiniteBooleanStage (level + 1),
      (realize (level + 1) child : Set (Nat → Bool)).Nonempty ∧
        realize (level + 1) child < realize level stage := by
  obtain ⟨child, childNonempty, childSubset, childNe⟩ :=
    next_stage_splits_every_nonempty level stage nonempty
  refine ⟨child, (realize_nonempty_iff (level + 1) child).mpr childNonempty, ?_⟩
  have belowAdvanced :
      realize (level + 1) child ≤
        realize (level + 1) (advance level stage) :=
    realize_mono childSubset
  have belowParent : realize (level + 1) child ≤ realize level stage := by
    simpa [realize_advance] using belowAdvanced
  refine lt_of_le_of_ne belowParent ?_
  intro equalRealizations
  apply childNe
  apply realize_injective (level + 1)
  exact equalRealizations.trans (realize_advance level stage).symm

/-- The independently selected whole is atomless even though every finite
presentation stage is atomic. -/
theorem ambient_is_gunky : IsGunky (Clopens (Nat → Bool)) :=
  isGunky_clopens_cantor

#print axioms truncate_extend
#print axioms extend_false_ne_true
#print axioms realize_injective
#print axioms realize_advance
#print axioms advance_ne_freshStage
#print axioms realize_nonempty_iff
#print axioms exists_cylinder_subset
#print axioms exists_uniform_cylinder_subset
#print axioms realize_stageFor_of_uniform
#print axioms cantorGeneration_exhaustive
#print axioms cantorGeneration
#print axioms exhaustiveCantorGeneration
#print axioms finite_stage_has_atom
#print axioms finite_stage_not_gunky
#print axioms next_stage_splits_every_nonempty
#print axioms realized_next_stage_splits_every_nonempty
#print axioms ambient_is_gunky

end Mettapedia.GSLT.Ultrainfinite.GenerativeCantorAtomlessness
