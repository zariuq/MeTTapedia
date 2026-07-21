import Mathlib

/-!
# Prime dependent world-model core

This module contains the narrow mathematical core ratified for Prime v0.69:

* the equivalence between additive dependent extractor families and additive
  homomorphisms into a dependent profile, with all monoid structures fixed;
* bag-valued producer outcomes with distinct May and Must predicates;
* branch-local revision, which maps alternatives without merging them;
* a persistent child record whose parent projection is unchanged; and
* a concrete counterexample to syntactic non-contamination.

It extends the existing OSLF world-model lane but does not identify OSLF states,
runtime spaces, dependent telescopes, or evidence carriers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PrimeDependentWorldModel

universe uW uQ uE uX uFault uReason uFragment uProv uDelta

/-! ## Fixed-structure dependent profile homomorphisms -/

/-- An additive dependent extractor over already fixed additive commutative
monoid structures.  Keeping the structures external is essential: the theorem
below compares extractors for the same `W`, `Q`, `E`, zero, and addition. -/
structure AdditiveExtractor (W : Type uW) (Q : Type uQ) (E : Q → Type uE)
    [AddCommMonoid W] [∀ q, AddCommMonoid (E q)] where
  extract : W → (q : Q) → E q
  extract_zero : extract 0 = 0
  extract_add : ∀ left right, extract (left + right) = extract left + extract right

namespace AdditiveExtractor

variable {W : Type uW} {Q : Type uQ} {E : Q → Type uE}
variable [AddCommMonoid W] [∀ q, AddCommMonoid (E q)]

/-- Extensionality for extractor families.  Proof fields are irrelevant after
the dependent profile functions agree pointwise. -/
@[ext]
theorem ext {left right : AdditiveExtractor W Q E}
    (h : ∀ world query, left.extract world query = right.extract world query) :
    left = right := by
  cases left with
  | mk leftExtract leftZero leftAdd =>
      cases right with
      | mk rightExtract rightZero rightAdd =>
          have hExtract : leftExtract = rightExtract := by
            funext world query
            exact h world query
          subst hExtract
          rfl

/-- Bundle an additive extractor family into one homomorphism whose codomain is
the dependent answer profile. -/
def toProfileHom (extractor : AdditiveExtractor W Q E) :
    W →+ ((q : Q) → E q) where
  toFun := extractor.extract
  map_zero' := extractor.extract_zero
  map_add' := extractor.extract_add

/-- Expose a dependent-profile homomorphism as an extractor family. -/
def ofProfileHom (hom : W →+ ((q : Q) → E q)) :
    AdditiveExtractor W Q E where
  extract := hom
  extract_zero := hom.map_zero
  extract_add := hom.map_add

/-- The extractor-to-profile-to-extractor round trip. -/
theorem ofProfileHom_toProfileHom (extractor : AdditiveExtractor W Q E) :
    ofProfileHom (toProfileHom extractor) = extractor := by
  apply AdditiveExtractor.ext
  intro world query
  rfl

/-- The profile-to-extractor-to-profile round trip. -/
theorem toProfileHom_ofProfileHom (hom : W →+ ((q : Q) → E q)) :
    toProfileHom (ofProfileHom hom) = hom := by
  ext world query
  rfl

/-- Fixed-structure dependent extractor families are equivalent to additive
homomorphisms into the pointwise dependent profile. -/
def equivProfileHom :
    AdditiveExtractor W Q E ≃ (W →+ ((q : Q) → E q)) where
  toFun := toProfileHom
  invFun := ofProfileHom
  left_inv := ofProfileHom_toProfileHom
  right_inv := toProfileHom_ofProfileHom

/-- Evaluation at one query recovers the corresponding pointwise additive
homomorphism. -/
def homAt (extractor : AdditiveExtractor W Q E) (query : Q) : W →+ E query :=
  (Pi.evalAddMonoidHom E query).comp extractor.toProfileHom

theorem homAt_apply (extractor : AdditiveExtractor W Q E)
    (query : Q) (world : W) :
    extractor.homAt query world = extractor.extract world query := by
  rfl

end AdditiveExtractor

/-! ### A heterogeneous positive canary -/

inductive DemoQuery where
  | count
  | binary
deriving DecidableEq, Repr

def DemoEvidence : DemoQuery → Type
  | .count => Nat
  | .binary => Nat × Nat

instance demoEvidenceAddCommMonoid (query : DemoQuery) :
    AddCommMonoid (DemoEvidence query) := by
  cases query <;> simp only [DemoEvidence] <;> infer_instance

abbrev DemoWorld := Nat × (Nat × Nat)

def demoExtractor : AdditiveExtractor DemoWorld DemoQuery DemoEvidence where
  extract world query :=
    match query with
    | .count => world.1
    | .binary => world.2
  extract_zero := by
    funext query
    cases query <;> rfl
  extract_add left right := by
    funext query
    cases query <;> rfl

example : demoExtractor.extract (3, (2, 1)) .count = (3 : Nat) := rfl
example : demoExtractor.extract (3, (2, 1)) .binary = ((2, 1) : Nat × Nat) := rfl

/--
error: Type mismatch
  demoExtractor.extract (3, 2, 1) DemoQuery.count
has type
  DemoEvidence DemoQuery.count
but is expected to have type
  DemoEvidence DemoQuery.binary
-/
#guard_msgs in
example : DemoEvidence .binary :=
  demoExtractor.extract (3, (2, 1)) .count

theorem demo_revision_pointwise
    (left right : DemoWorld) (query : DemoQuery) :
    demoExtractor.extract (left + right) query =
      demoExtractor.extract left query + demoExtractor.extract right query :=
  congrFun (demoExtractor.extract_add left right) query

/-! ## Honest producer outcomes -/

inductive Completion (Reason : Type uReason) (Fragment : Type uFragment) where
  | complete : Fragment → Completion Reason Fragment
  | incomplete : Reason → Completion Reason Fragment
deriving DecidableEq, Repr

inductive Branch (X : Type uX) (Fault : Type uFault) where
  | success : X → Branch X Fault
  | fault : Fault → Branch X Fault
deriving DecidableEq, Repr

structure ProducerOutcome (X : Type uX) (Fault : Type uFault)
    (Reason : Type uReason) (Fragment : Type uFragment) where
  branches : Multiset (Branch X Fault)
  completion : Completion Reason Fragment
deriving DecidableEq

namespace ProducerOutcome

variable {X : Type uX} {Fault : Type uFault}
variable {Reason : Type uReason} {Fragment : Type uFragment}

/-- May needs one observed successful branch.  It does not assert completion. -/
def May (predicate : X → Prop) (outcome : ProducerOutcome X Fault Reason Fragment) :
    Prop :=
  ∃ value, Branch.success value ∈ outcome.branches ∧ predicate value

/-- Must requires certified completion, a nonempty bag, and a satisfying success
at every branch.  In particular, a fault is not a vacuous success. -/
def Must (predicate : X → Prop) (outcome : ProducerOutcome X Fault Reason Fragment) :
    Prop :=
  (∃ fragment, outcome.completion = Completion.complete fragment) ∧
  outcome.branches ≠ 0 ∧
  ∀ branch ∈ outcome.branches,
    ∃ value, branch = Branch.success value ∧ predicate value

theorem incomplete_not_must (predicate : X → Prop)
    (outcome : ProducerOutcome X Fault Reason Fragment) (reason : Reason)
    (hIncomplete : outcome.completion = Completion.incomplete reason) :
    ¬ outcome.Must predicate := by
  intro hMust
  rcases hMust.1 with ⟨fragment, hComplete⟩
  rw [hIncomplete] at hComplete
  cases hComplete

theorem may_of_success_mem (predicate : X → Prop)
    (outcome : ProducerOutcome X Fault Reason Fragment) (value : X)
    (hMem : Branch.success value ∈ outcome.branches)
    (hPredicate : predicate value) : outcome.May predicate := by
  exact ⟨value, hMem, hPredicate⟩

theorem must_has_no_fault (predicate : X → Prop)
    (outcome : ProducerOutcome X Fault Reason Fragment)
    (hMust : outcome.Must predicate) (fault : Fault) :
    Branch.fault fault ∉ outcome.branches := by
  intro hFault
  rcases hMust.2.2 (Branch.fault fault) hFault with ⟨value, hEq, _⟩
  cases hEq

/-! ### Positive and negative May/Must canaries -/

def incompleteSuccess (value : X) (reason : Reason) :
    ProducerOutcome X Fault Reason Fragment where
  branches := {Branch.success value}
  completion := .incomplete reason

def completeSuccess (value : X) (fragment : Fragment) :
    ProducerOutcome X Fault Reason Fragment where
  branches := {Branch.success value}
  completion := .complete fragment

theorem incompleteSuccess_may (predicate : X → Prop) (value : X)
    (reason : Reason) (hPredicate : predicate value) :
    (incompleteSuccess (Fault := Fault) (Fragment := Fragment) value reason).May
      predicate := by
  apply may_of_success_mem predicate _ value
  · simp [incompleteSuccess]
  · exact hPredicate

theorem incompleteSuccess_not_must (predicate : X → Prop) (value : X)
    (reason : Reason) :
    ¬ (incompleteSuccess (Fault := Fault) (Fragment := Fragment) value reason).Must
      predicate := by
  apply incomplete_not_must predicate _ reason
  rfl

theorem completeSuccess_must (predicate : X → Prop) (value : X)
    (fragment : Fragment) (hPredicate : predicate value) :
    (completeSuccess (Fault := Fault) (Reason := Reason) value fragment).Must
      predicate := by
  refine ⟨⟨fragment, rfl⟩, ?_, ?_⟩
  · simp [completeSuccess]
  · intro branch hBranch
    have hEq : branch = Branch.success value := by
      simpa [completeSuccess] using hBranch
    exact ⟨value, hEq, hPredicate⟩

end ProducerOutcome

/-! ## Branch-local revision -/

structure ObservedDelta (X : Type uX) (Delta : Type uDelta)
    (Provenance : Type uProv) where
  value : X
  delta : Delta
  provenance : Provenance
deriving DecidableEq, Repr

def advanceBranch {W : Type uW} {X : Type uX} {Delta : Type uDelta}
    {Provenance : Type uProv} {Fault : Type uFault}
    (revise : W → Delta → W) (base : W) :
    Branch (ObservedDelta X Delta Provenance) Fault →
      Branch (ObservedDelta X W Provenance) Fault
  | .success observed =>
      .success
        { value := observed.value
          delta := revise base observed.delta
          provenance := observed.provenance }
  | .fault fault => .fault fault

def advanceOutcome {W : Type uW} {X : Type uX} {Delta : Type uDelta}
    {Provenance : Type uProv} {Fault : Type uFault}
    {Reason : Type uReason} {Fragment : Type uFragment}
    (revise : W → Delta → W) (base : W)
    (outcome : ProducerOutcome (ObservedDelta X Delta Provenance) Fault Reason Fragment) :
    ProducerOutcome (ObservedDelta X W Provenance) Fault Reason Fragment where
  branches := outcome.branches.map (advanceBranch revise base)
  completion := outcome.completion

theorem advanceOutcome_completion {W : Type uW} {X : Type uX}
    {Delta : Type uDelta} {Provenance : Type uProv} {Fault : Type uFault}
    {Reason : Type uReason} {Fragment : Type uFragment}
    (revise : W → Delta → W) (base : W)
    (outcome : ProducerOutcome (ObservedDelta X Delta Provenance) Fault Reason Fragment) :
    (advanceOutcome revise base outcome).completion = outcome.completion := by
  rfl

theorem advanceOutcome_card {W : Type uW} {X : Type uX}
    {Delta : Type uDelta} {Provenance : Type uProv} {Fault : Type uFault}
    {Reason : Type uReason} {Fragment : Type uFragment}
    (revise : W → Delta → W) (base : W)
    (outcome : ProducerOutcome (ObservedDelta X Delta Provenance) Fault Reason Fragment) :
    (advanceOutcome revise base outcome).branches.card = outcome.branches.card := by
  simp [advanceOutcome]

theorem success_mem_advanceOutcome {W : Type uW} {X : Type uX}
    {Delta : Type uDelta} {Provenance : Type uProv} {Fault : Type uFault}
    {Reason : Type uReason} {Fragment : Type uFragment}
    (revise : W → Delta → W) (base : W)
    (outcome : ProducerOutcome (ObservedDelta X Delta Provenance) Fault Reason Fragment)
    (observed : ObservedDelta X Delta Provenance)
    (hMem : Branch.success observed ∈ outcome.branches) :
    Branch.success
        { value := observed.value
          delta := revise base observed.delta
          provenance := observed.provenance } ∈
      (advanceOutcome revise base outcome).branches := by
  exact Multiset.mem_map.mpr ⟨Branch.success observed, hMem, rfl⟩

theorem fault_mem_advanceOutcome_iff {W : Type uW} {X : Type uX}
    {Delta : Type uDelta} {Provenance : Type uProv} {Fault : Type uFault}
    {Reason : Type uReason} {Fragment : Type uFragment}
    (revise : W → Delta → W) (base : W)
    (outcome : ProducerOutcome (ObservedDelta X Delta Provenance) Fault Reason Fragment)
    (fault : Fault) :
    Branch.fault fault ∈ (advanceOutcome revise base outcome).branches ↔
      Branch.fault fault ∈ outcome.branches := by
  constructor
  · intro hMem
    rcases Multiset.mem_map.mp hMem with ⟨branch, hBranch, hEq⟩
    cases branch with
    | success observed => simp [advanceBranch] at hEq
    | fault sourceFault =>
        simp [advanceBranch] at hEq
        subst hEq
        exact hBranch
  · intro hMem
    exact Multiset.mem_map.mpr ⟨Branch.fault fault, hMem, rfl⟩

/-! ## Persistent child scopes -/

/-- A child keeps its parent snapshot as a value and stores a local delta
separately.  No mutable alias is exposed by this structure. -/
structure PersistentChild (State : Type uW) (Delta : Type uDelta) where
  parent : State
  delta : Delta
deriving DecidableEq, Repr

def PersistentChild.extend {State : Type uW} {Delta : Type uDelta}
    (parent : State) (delta : Delta) : PersistentChild State Delta :=
  { parent, delta }

theorem PersistentChild.parent_extend {State : Type uW} {Delta : Type uDelta}
    (parent : State) (delta : Delta) :
    (PersistentChild.extend parent delta).parent = parent := by
  rfl

/-- Reading or transforming the child-local delta cannot change the stored
parent value. -/
theorem PersistentChild.mapLocal_parent {State : Type uW}
    {Delta : Type uDelta} {Delta' : Type*}
    (child : PersistentChild State Delta) (f : Delta → Delta') :
    ({ parent := child.parent, delta := f child.delta } :
      PersistentChild State Delta').parent = child.parent := by
  rfl

/-! ## Why syntactic nonoccurrence is insufficient -/

/-- A tiny dependency state: a hidden fact can entail the visible query even
though the query itself contains no hidden symbol. -/
structure DependencyState where
  hidden : Bool
  visible : Bool
deriving DecidableEq, Repr

def visibleQuery (state : DependencyState) : Bool :=
  state.visible || state.hidden

def addHidden (state : DependencyState) : DependencyState :=
  { state with hidden := true }

theorem syntactic_nonoccurrence_counterexample :
    visibleQuery { hidden := false, visible := false } = false ∧
    visibleQuery (addHidden { hidden := false, visible := false }) = true := by
  decide

/-! ## Axiom audit -/

#print axioms AdditiveExtractor.ofProfileHom_toProfileHom
#print axioms AdditiveExtractor.toProfileHom_ofProfileHom
#print axioms AdditiveExtractor.equivProfileHom
#print axioms ProducerOutcome.incomplete_not_must
#print axioms ProducerOutcome.completeSuccess_must
#print axioms advanceOutcome_card
#print axioms fault_mem_advanceOutcome_iff
#print axioms PersistentChild.mapLocal_parent
#print axioms syntactic_nonoccurrence_counterexample

end Mettapedia.OSLF.Framework.PrimeDependentWorldModel
