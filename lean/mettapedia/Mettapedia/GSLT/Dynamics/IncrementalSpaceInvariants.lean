import Mettapedia.GSLT.Dynamics.SymmetryAwareResolution
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Incremental space invariants

Space-wide properties need not imply a whole-space rescan after every local
transition.  This module isolates three exact cases where a small certificate
is sufficient:

* an additive summary is updated from the removed and inserted fragments;
* an equivariant deterministic evolution preserves symmetry-fixed states; and
* overlap coherence is rechecked only on edges incident to a changed region.

These are admission and maintenance laws, not a new space evaluator.  Monotone
closure, whole-family resolution, and genuinely global optimization remain
separate operations with their own observation and authority boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IncrementalSpaceInvariants

universe uItem uSummary uSymmetry uState uCell uValue

/-! ## Additive summaries over framed local updates -/

/-- The part removed from a space and the part inserted in its place. -/
structure FragmentUpdate (Item : Type uItem) where
  before : Multiset Item
  after : Multiset Item

/-- A local update together with its untouched frame and exact source/target
decompositions. -/
structure FramedUpdate (Item : Type uItem) where
  source : Multiset Item
  target : Multiset Item
  fragment : FragmentUpdate Item
  frame : Multiset Item
  source_eq : source = fragment.before + frame
  target_eq : target = fragment.after + frame

/-- A local rewrite is balanced for an authored additive summary when its old
and new fragments have exactly the same summary. -/
def Balanced
    {Item : Type uItem} {Summary : Type uSummary} [AddCommMonoid Summary]
    (summary : Multiset Item →+ Summary) (update : FragmentUpdate Item) : Prop :=
  summary update.before = summary update.after

/-- Revise a cached additive summary by inspecting only the changed fragment. -/
def reviseCached
    {Item : Type uItem} {Summary : Type uSummary} [AddCommGroup Summary]
    (summary : Multiset Item →+ Summary) (cached : Summary)
    (update : FragmentUpdate Item) : Summary :=
  cached - summary update.before + summary update.after

/-- The fragment-only cache revision is exactly the summary of the target
space.  The untouched frame is never rescanned. -/
theorem reviseCached_eq_targetSummary
    {Item : Type uItem} {Summary : Type uSummary} [AddCommGroup Summary]
    (summary : Multiset Item →+ Summary) (cached : Summary)
    (update : FramedUpdate Item)
    (cachedExact : cached = summary update.source) :
    reviseCached summary cached update.fragment = summary update.target := by
  rw [cachedExact, update.source_eq, update.target_eq, map_add, map_add]
  simp only [reviseCached]
  abel

/-- A balanced local rewrite preserves the global additive summary. -/
theorem summary_preserved_of_balanced
    {Item : Type uItem} {Summary : Type uSummary} [AddCommMonoid Summary]
    (summary : Multiset Item →+ Summary) (update : FramedUpdate Item)
    (balanced : Balanced summary update.fragment) :
    summary update.target = summary update.source := by
  rw [update.target_eq, update.source_eq, map_add, map_add]
  exact congrArg (fun fragmentSummary => fragmentSummary + summary update.frame)
    balanced.symm

/-- A named space-wide conservation law survives every balanced local
rewrite. -/
theorem invariant_preserved_of_balanced
    {Item : Type uItem} {Summary : Type uSummary} [AddCommMonoid Summary]
    (summary : Multiset Item →+ Summary) (required : Summary)
    (update : FramedUpdate Item)
    (sourceInvariant : summary update.source = required)
    (balanced : Balanced summary update.fragment) :
    summary update.target = required :=
  (summary_preserved_of_balanced summary update balanced).trans sourceInvariant

/-! ### Parallel families of balanced fragments -/

def totalBefore {Item : Type uItem} : List (FragmentUpdate Item) → Multiset Item
  | [] => 0
  | update :: rest => update.before + totalBefore rest

def totalAfter {Item : Type uItem} : List (FragmentUpdate Item) → Multiset Item
  | [] => 0
  | update :: rest => update.after + totalAfter rest

/-- If every fragment in a proposed wave is balanced, their aggregate removal
and insertion are balanced too. -/
theorem balanced_family
    {Item : Type uItem} {Summary : Type uSummary} [AddCommMonoid Summary]
    (summary : Multiset Item →+ Summary)
    (updates : List (FragmentUpdate Item))
    (eachBalanced : ∀ update ∈ updates, Balanced summary update) :
    summary (totalBefore updates) = summary (totalAfter updates) := by
  induction updates with
  | nil => simp [totalBefore, totalAfter]
  | cons update rest inductionHypothesis =>
      have headBalanced := eachBalanced update (by simp)
      have tailBalanced : ∀ candidate ∈ rest, Balanced summary candidate := by
        intro candidate member
        exact eachBalanced candidate (by simp [member])
      simp only [totalBefore, totalAfter, map_add]
      rw [headBalanced, inductionHypothesis tailBalanced]

/-- A wave of local fragment changes with one untouched common frame. -/
structure FramedWave (Item : Type uItem) where
  source : Multiset Item
  target : Multiset Item
  updates : List (FragmentUpdate Item)
  frame : Multiset Item
  source_eq : source = totalBefore updates + frame
  target_eq : target = totalAfter updates + frame

/-- Per-fragment balance is sufficient for exact global conservation across a
whole parallel wave. -/
theorem wave_summary_preserved
    {Item : Type uItem} {Summary : Type uSummary} [AddCommMonoid Summary]
    (summary : Multiset Item →+ Summary) (wave : FramedWave Item)
    (eachBalanced : ∀ update ∈ wave.updates, Balanced summary update) :
    summary wave.target = summary wave.source := by
  rw [wave.target_eq, wave.source_eq, map_add, map_add]
  exact congrArg (fun fragmentSummary => fragmentSummary + summary wave.frame)
    (balanced_family summary wave.updates eachBalanced).symm

/-! ## Static symmetry admission -/

/-- An explicitly authored group action, kept as data so several space kinds
may carry different symmetry policies over the same state representation. -/
structure AuthoredAction (Symmetry : Type uSymmetry) [Group Symmetry]
    (State : Type uState) where
  act : Symmetry → State → State
  identity : ∀ state, act 1 state = state
  composition : ∀ first second state,
    act (first * second) state = act first (act second state)

/-- A state is fixed by every authored symmetry. -/
def FixedByAll
    {Symmetry : Type uSymmetry} [Group Symmetry] {State : Type uState}
    (action : AuthoredAction Symmetry State) (state : State) : Prop :=
  ∀ symmetry, action.act symmetry state = state

/-- A deterministic evolution commutes with the authored action. -/
def EquivariantEvolution
    {Symmetry : Type uSymmetry} [Group Symmetry] {State : Type uState}
    (action : AuthoredAction Symmetry State) (evolve : State → State) : Prop :=
  ∀ symmetry state,
    evolve (action.act symmetry state) = action.act symmetry (evolve state)

/-- Equivariance is paid once at rule admission: every symmetry-fixed state
then evolves to another symmetry-fixed state without a runtime orbit scan. -/
theorem equivariantEvolution_preserves_fixed
    {Symmetry : Type uSymmetry} [Group Symmetry] {State : Type uState}
    (action : AuthoredAction Symmetry State) (evolve : State → State)
    (equivariant : EquivariantEvolution action evolve)
    {state : State} (fixed : FixedByAll action state) :
    FixedByAll action (evolve state) := by
  intro symmetry
  calc
    action.act symmetry (evolve state) =
        evolve (action.act symmetry state) :=
      (equivariant symmetry state).symm
    _ = evolve state := congrArg evolve (fixed symmetry)

/-! ## Boundary-local overlap coherence -/

/-- Two fields agree away from the explicitly touched region. -/
def AgreesOutside
    {Cell : Type uCell} [DecidableEq Cell] {Value : Type uValue}
    (touched : Finset Cell) (before after : Cell → Value) : Prop :=
  ∀ cell, cell ∉ touched → after cell = before cell

/-- An overlap edge is incident to a touched region when either endpoint was
changed. -/
def Incident
    {Cell : Type uCell} [DecidableEq Cell]
    (touched : Finset Cell) (edge : Cell × Cell) : Prop :=
  edge.1 ∈ touched ∨ edge.2 ∈ touched

/-- A field is coherent when every authored overlap edge satisfies its local
compatibility relation. -/
def Coherent
    {Cell : Type uCell} [DecidableEq Cell] {Value : Type uValue}
    (edges : Finset (Cell × Cell)) (compatible : Value → Value → Prop)
    (field : Cell → Value) : Prop :=
  ∀ edge ∈ edges, compatible (field edge.1) (field edge.2)

/-- Exact local-to-global maintenance: old coherence plus agreement outside
the touched region reduces the new global check to incident overlap edges. -/
theorem coherent_of_incident_checks
    {Cell : Type uCell} [DecidableEq Cell] {Value : Type uValue}
    (edges : Finset (Cell × Cell)) (compatible : Value → Value → Prop)
    (touched : Finset Cell) (before after : Cell → Value)
    (beforeCoherent : Coherent edges compatible before)
    (outside : AgreesOutside touched before after)
    (incidentChecks : ∀ edge ∈ edges, Incident touched edge →
      compatible (after edge.1) (after edge.2)) :
    Coherent edges compatible after := by
  intro edge member
  by_cases incident : Incident touched edge
  · exact incidentChecks edge member incident
  · have firstOutside : edge.1 ∉ touched := by
      intro firstTouched
      exact incident (Or.inl firstTouched)
    have secondOutside : edge.2 ∉ touched := by
      intro secondTouched
      exact incident (Or.inr secondTouched)
    rw [outside edge.1 firstOutside, outside edge.2 secondOutside]
    exact beforeCoherent edge member

/-! ## Positive and negative controls -/

namespace Canary

inductive Species where
  | atom
  | dimer
deriving DecidableEq, Repr

def mass : Species → ℤ
  | .atom => 1
  | .dimer => 2

def massSummary : Multiset Species →+ ℤ where
  toFun species := (species.map mass).sum
  map_zero' := by simp
  map_add' := by intro left right; simp

def dimerizationFragment : FragmentUpdate Species where
  before := {.atom, .atom}
  after := {.dimer}

def atomToDimerFragment : FragmentUpdate Species where
  before := {.atom}
  after := {.dimer}

theorem dimerization_balanced :
    Balanced massSummary dimerizationFragment := by
  norm_num [Balanced, massSummary, dimerizationFragment, mass]

/-- Negative control: a rewrite that mints one unit of mass is rejected by the
same local check. -/
theorem atomToDimer_not_balanced :
    ¬ Balanced massSummary atomToDimerFragment := by
  norm_num [Balanced, massSummary, atomToDimerFragment, mass]

def dimerizationUpdate : FramedUpdate Species where
  source := {.atom, .atom, .atom}
  target := {.dimer, .atom}
  fragment := dimerizationFragment
  frame := {.atom}
  source_eq := by decide
  target_eq := by decide

theorem dimerization_preserves_global_mass :
    massSummary dimerizationUpdate.target =
      massSummary dimerizationUpdate.source :=
  summary_preserved_of_balanced massSummary dimerizationUpdate
    dimerization_balanced

/-! ### Symmetric fields -/

/-- Relabel a Boolean-indexed field contravariantly. -/
def boolFieldAction : AuthoredAction (Equiv.Perm Bool) (Bool → Nat) where
  act symmetry field index := field (symmetry.symm index)
  identity := by
    intro field
    funext index
    rfl
  composition := by
    intro first second field
    funext index
    rw [show (first * second).symm = second.symm * first.symm by
      exact mul_inv_rev first second]
    rfl

def uniformField : Bool → Nat := fun _ => 3

def successorField (field : Bool → Nat) : Bool → Nat :=
  fun index => field index + 1

theorem uniformField_fixed : FixedByAll boolFieldAction uniformField := by
  intro symmetry
  funext index
  rfl

theorem successorField_equivariant :
    EquivariantEvolution boolFieldAction successorField := by
  intro symmetry field
  funext index
  rfl

theorem successorField_preserves_uniform_symmetry :
    FixedByAll boolFieldAction (successorField uniformField) :=
  equivariantEvolution_preserves_fixed boolFieldAction successorField
    successorField_equivariant uniformField_fixed

def bumpFalse (field : Bool → Nat) : Bool → Nat :=
  fun index => if index = false then field index + 1 else field index

/-- Negative control: a coordinate-specific update breaks relabeling
equivariance and therefore cannot use the static symmetry certificate. -/
theorem bumpFalse_not_equivariant :
    ¬ EquivariantEvolution boolFieldAction bumpFalse := by
  intro equivariant
  have atFalse := congrFun
    (equivariant SymmetryAwareResolution.boolSwap (fun _ => 0)) false
  norm_num [boolFieldAction, bumpFalse,
    SymmetryAwareResolution.boolSwap] at atFalse

/-! ### Local overlap coherence -/

inductive Cell where
  | left
  | middle
  | right
deriving DecidableEq, Fintype, Repr

def lineEdges : Finset (Cell × Cell) :=
  {(.left, .middle), (.middle, .right)}

def nondecreasing (first second : Nat) : Prop := first ≤ second

def originalField : Cell → Nat
  | .left => 0
  | .middle => 1
  | .right => 2

def touchedMiddle : Finset Cell := {.middle}

def coherentUpdate : Cell → Nat
  | .left => 0
  | .middle => 2
  | .right => 2

def brokenUpdate : Cell → Nat
  | .left => 0
  | .middle => 3
  | .right => 2

theorem originalField_coherent :
    Coherent lineEdges nondecreasing originalField := by
  intro edge member
  simp [lineEdges] at member
  rcases member with rfl | rfl <;>
    norm_num [nondecreasing, originalField]

theorem coherentUpdate_agreesOutside :
    AgreesOutside touchedMiddle originalField coherentUpdate := by
  intro cell outside
  cases cell <;>
    simp [touchedMiddle, originalField, coherentUpdate] at outside ⊢

theorem coherentUpdate_incidentChecks :
    ∀ edge ∈ lineEdges, Incident touchedMiddle edge →
      nondecreasing (coherentUpdate edge.1) (coherentUpdate edge.2) := by
  intro edge member _incident
  simp [lineEdges] at member
  rcases member with rfl | rfl <;>
    norm_num [nondecreasing, coherentUpdate]

theorem coherentUpdate_global :
    Coherent lineEdges nondecreasing coherentUpdate :=
  coherent_of_incident_checks lineEdges nondecreasing touchedMiddle
    originalField coherentUpdate originalField_coherent
    coherentUpdate_agreesOutside coherentUpdate_incidentChecks

/-- Checking only overlaps wholly inside the changed region is vacuous for a
single-cell update.  The unchecked boundary edge can violate coherence. -/
theorem internalOnly_checks_do_not_suffice :
    (∀ edge ∈ lineEdges,
      edge.1 ∈ touchedMiddle ∧ edge.2 ∈ touchedMiddle →
        nondecreasing (brokenUpdate edge.1) (brokenUpdate edge.2)) ∧
      ¬ Coherent lineEdges nondecreasing brokenUpdate := by
  constructor
  · rintro ⟨first, second⟩ member ⟨firstTouched, secondTouched⟩
    have firstEq : first = .middle := by
      simpa [touchedMiddle] using firstTouched
    have secondEq : second = .middle := by
      simpa [touchedMiddle] using secondTouched
    subst first
    subst second
    simp [lineEdges] at member
  · intro coherent
    have boundary := coherent (.middle, .right) (by simp [lineEdges])
    norm_num [nondecreasing, brokenUpdate] at boundary

end Canary

/-! ## Axiom audit -/

#print axioms reviseCached_eq_targetSummary
#print axioms summary_preserved_of_balanced
#print axioms balanced_family
#print axioms wave_summary_preserved
#print axioms equivariantEvolution_preserves_fixed
#print axioms coherent_of_incident_checks
#print axioms Canary.dimerization_preserves_global_mass
#print axioms Canary.atomToDimer_not_balanced
#print axioms Canary.bumpFalse_not_equivariant
#print axioms Canary.coherentUpdate_global
#print axioms Canary.internalOnly_checks_do_not_suffice

end Mettapedia.GSLT.Dynamics.IncrementalSpaceInvariants
