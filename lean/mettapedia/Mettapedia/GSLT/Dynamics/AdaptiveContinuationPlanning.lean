import Mettapedia.GSLT.Dynamics.CertifiedRepresentationPlanning

/-!
# Background planning at live continuation boundaries

A background worker proposes an executor change. At an atomic boundary in this
model, a checked partial converter reads the live residual. Refusal retains the
current engine and value. Finite preselected or realized traces of planning,
accepted or declined offers, source regions and source holes erase to the
original Region/Hole computation for one fixed realization family.

The state carrier is the existing engine-indexed `Result`, not a third transfer
format. Dependency snapshots store an explicit finite list of declaration/value
pairs. Currentness proves that a cached artifact equals a fresh compilation;
semantic preservation is a separate property of proposals for the fixed family.
Source-code mutation needs pinned or revision-indexed semantics. Exclusive
ownership, atomic validation and installation, and native lifetime enforcement
remain runtime obligations; no linear-type or concurrent-memory theorem is
asserted here. Declared compilation receipts are separate from source-language
operations. This finite execution theorem does not assert scheduler fairness,
physical resource bounds, or a speedup.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanning

open RegionHolePlan RepresentationSwitching CertifiedRepresentationPlanning
open OrderedOccurrenceBodyAlgebra (functionCategory)

universe uObj uRegion uHole uEngine uState uDeclaration uConfig

variable {Obj : Type uObj} {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole} {Engine : Type uEngine}
  {source : IndexedCategory Obj Region}
  {family : Family source Hole functionCategory.{uState} Engine}

/-- A checked proposal contains converters from supported live engines to
its destination. An unsupported source state is represented by refusal, not
by a fabricated empty result. -/
structure Proposal
    (family : Family source Hole functionCategory.{uState} Engine) (X : Obj) where
  destination : Engine
  converter : (origin : Engine) → GuardedTransfer
    ((family.decode origin).component X)
    ((family.decode destination).component X)

namespace Proposal

variable {X : Obj}

/-- Install against the live residual passed at commit time. The proposal
has no authority to restore an earlier captured branch image. -/
def install (proposal : Proposal family X) (live : Result family X) : Result family X :=
  match (proposal.converter live.1).attempt live.2 with
  | none => live
  | some next => ⟨proposal.destination, next⟩

theorem install_preserves (proposal : Proposal family X) (live : Result family X) :
    observeResult (proposal.install live) = observeResult live := by
  cases found : (proposal.converter live.1).attempt live.2 with
  | none => simp [install, found]
  | some next =>
      unfold install
      rw [found]
      exact (proposal.converter live.1).correct live.2 next found

theorem refusal_retains_live (proposal : Proposal family X) (live : Result family X)
    (refused : (proposal.converter live.1).attempt live.2 = none) :
    proposal.install live = live := by
  simp [install, refused]

/-- Any future observer, including execution of the pending continuation,
sees the same residual after installation. -/
theorem continue_install {Observation : Type*}
    (proposal : Proposal family X) (live : Result family X)
    (continuation : family.reference.objectMap X → Observation) :
    continuation (observeResult (proposal.install live)) =
      continuation (observeResult live) := by
  rw [install_preserves]

/-- A family of total certified transfers gives one concrete source of
checked proposals. State-dependent backends may instead refuse. -/
def ofTransfers (destination : Engine)
    (transfers : (origin : Engine) → Transfer family origin destination X) :
    Proposal family X where
  destination := destination
  converter origin := {
    attempt := fun state => some ((transfers origin).convert state)
    correct := by
      intro state next accepted
      have eqNext := Option.some.inj accepted
      rw [← eqNext]
      exact congrFun (transfers origin).commutes state }

end Proposal

/-- A finite trace may interleave arbitrarily much optimizer work with source
work. Only region and hole events belong to the language's source plan. -/
inductive Schedule
    (family : Family source Hole functionCategory.{uState} Engine) : Obj → Obj → Type
    (max uObj uRegion uHole uEngine uState) where
  | done (X : Obj) : Schedule family X X
  | region {X Y Z : Obj} (arrow : Region X Y)
      (rest : Schedule family Y Z) : Schedule family X Z
  | hole {X Y Z : Obj} (opening : Hole X Y)
      (rest : Schedule family Y Z) : Schedule family X Z
  | background {X Y : Obj} (work : Nat)
      (rest : Schedule family X Y) : Schedule family X Y
  | offer {X Y : Obj} (proposal : Proposal family X) (work : Nat)
      (rest : Schedule family X Y) : Schedule family X Y

namespace Schedule

def erase : {X Y : Obj} → Schedule family X Y → Plan Obj Region Hole X Y
  | _, _, .done X => .nil X
  | _, _, .region arrow rest => .region arrow rest.erase
  | _, _, .hole opening rest => .hole opening rest.erase
  | _, _, .background _ rest => rest.erase
  | _, _, .offer _ _ rest => rest.erase

def run : {X Y : Obj} → Schedule family X Y → Result family X → Result family Y
  | _, _, .done _, live => live
  | _, _, .region arrow rest, live =>
      rest.run ⟨live.1, (family.engine live.1).mapRegion arrow live.2⟩
  | _, _, .hole opening rest, live =>
      rest.run ⟨live.1, (family.engine live.1).mapHole opening live.2⟩
  | _, _, .background _ rest, live => rest.run live
  | _, _, .offer proposal _ rest, live => rest.run (proposal.install live)

/-- Local realization squares and checked offers compose into exactness of
the entire residual, even when the selected engine changes at runtime. -/
theorem run_exact {X Y : Obj} (schedule : Schedule family X Y)
    (live : Result family X) :
    observeResult (schedule.run live) =
      Plan.denote family.reference schedule.erase (observeResult live) := by
  induction schedule with
  | done => rfl
  | @region X Y Z arrow rest ih =>
      rw [run, ih]
      have square := congrFun ((family.decode live.1).region_naturality arrow) live.2
      change observeResult ⟨live.1, (family.engine live.1).mapRegion arrow live.2⟩ =
        family.reference.mapRegion arrow (observeResult live) at square
      rw [square]
      rfl
  | @hole X Y Z opening rest ih =>
      rw [run, ih]
      have square := congrFun ((family.decode live.1).hole_naturality opening) live.2
      change observeResult ⟨live.1, (family.engine live.1).mapHole opening live.2⟩ =
        family.reference.mapHole opening (observeResult live) at square
      rw [square]
      rfl
  | background work rest ih => exact ih live
  | offer proposal work rest ih =>
      rw [run, ih, Proposal.install_preserves]
      rfl

/-- Optimizer timing and strategy choices cannot change future observations
when they leave the source plan unchanged. -/
theorem same_plan_same_residual {X Y : Obj}
    (first second : Schedule family X Y)
    (same : first.erase = second.erase) (live : Result family X) :
    observeResult (first.run live) = observeResult (second.run live) := by
  rw [run_exact, run_exact, same]

def planningWork : {X Y : Obj} → Schedule family X Y → Nat
  | _, _, .done _ => 0
  | _, _, .region _ rest => rest.planningWork
  | _, _, .hole _ rest => rest.planningWork
  | _, _, .background work rest => work + rest.planningWork
  | _, _, .offer _ work rest => work + rest.planningWork

def planningEvents : {X Y : Obj} → Schedule family X Y → Nat
  | _, _, .done _ => 0
  | _, _, .region _ rest => rest.planningEvents
  | _, _, .hole _ rest => rest.planningEvents
  | _, _, .background _ rest => 1 + rest.planningEvents
  | _, _, .offer _ _ rest => 1 + rest.planningEvents

/-- Positive declared work receipts bound optimization/installation attempts.
Their calibration is a runtime obligation, and they are not extra grants of
source-language fuel. -/
def Charged : {X Y : Obj} → Schedule family X Y → Prop
  | _, _, .done _ => True
  | _, _, .region _ rest => rest.Charged
  | _, _, .hole _ rest => rest.Charged
  | _, _, .background work rest => 0 < work ∧ rest.Charged
  | _, _, .offer _ work rest => 0 < work ∧ rest.Charged

theorem planningEvents_le_work {X Y : Obj} (schedule : Schedule family X Y)
    (charged : schedule.Charged) : schedule.planningEvents ≤ schedule.planningWork := by
  induction schedule with
  | done => simp [planningEvents, planningWork]
  | region arrow rest ih | hole arrow rest ih => exact ih charged
  | background work rest ih | offer proposal work rest ih =>
      have smaller := ih charged.2
      have positive := charged.1
      simp only [planningEvents, planningWork]
      omega

theorem planningEvents_le_budget {X Y : Obj} (schedule : Schedule family X Y)
    (charged : schedule.Charged) (budget : Nat)
    (funded : schedule.planningWork ≤ budget) : schedule.planningEvents ≤ budget :=
  (planningEvents_le_work schedule charged).trans funded

end Schedule

/-! ## Finite dependency snapshots for asynchronous compilation -/

variable {Declaration : Type uDeclaration} [DecidableEq Declaration]
  {Config : Type uConfig} [DecidableEq Config] {Artifact : Type*}

/-- A finite dependency snapshot agrees with a configuration on every stored
declaration/value pair. The configuration itself is not stored as runtime data. -/
def SnapshotMatches (snapshot : List (Declaration × Config))
    (current : Declaration → Config) : Prop :=
  ∀ entry ∈ snapshot, entry.2 = current entry.1

/-- Executable comparison of the explicitly stored dependency values. -/
def dependenciesCurrent (snapshot : List (Declaration × Config))
    (current : Declaration → Config) : Bool :=
  snapshot.all fun entry => decide (entry.2 = current entry.1)

omit [DecidableEq Declaration] in
theorem dependenciesCurrent_exact (snapshot : List (Declaration × Config))
    (current : Declaration → Config) :
    dependenciesCurrent snapshot current = true ↔ SnapshotMatches snapshot current := by
  simp [dependenciesCurrent, SnapshotMatches]

/-- Runtime data consists of finite dependency pairs and the stored artifact.
The original compilation configuration occurs only under an existential proof,
which is erased. Lookup does not rerun the compiler. These are dependencies of
program knowledge; this structure does not capture the current branch store. -/
structure PreparedArtifact
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact) where
  dependencies : List (Declaration × Config)
  coverage : ∀ declaration,
    declaration ∈ plan.support ↔ ∃ value, (declaration, value) ∈ dependencies
  artifact : Artifact
  compiled : ∃ configuration : Declaration → Config,
    artifact = plan.run configuration ∧ SnapshotMatches dependencies configuration

/-- The supplied finite enumeration covers exactly the plan's support. It may
contain duplicates; neither minimal storage nor inferred support is claimed.
Compilation occurs once. The snapshot payload consists only of the listed
declaration/value pairs; the artifact has its own representation and costs. -/
def prepare (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact)
    (names : List Declaration)
    (coverage : ∀ declaration, declaration ∈ names ↔ declaration ∈ plan.support)
    (configuration : Declaration → Config) : PreparedArtifact plan where
  dependencies := names.map fun declaration => (declaration, configuration declaration)
  coverage := by
    intro declaration
    constructor
    · intro supported
      exact ⟨configuration declaration,
        List.mem_map.mpr ⟨declaration, (coverage declaration).mpr supported, rfl⟩⟩
    · rintro ⟨value, member⟩
      obtain ⟨original, originalMember, equalPair⟩ := List.mem_map.mp member
      have sameName : original = declaration := congrArg Prod.fst equalPair
      subst original
      exact (coverage declaration).mp originalMember
  artifact := plan.run configuration
  compiled := by
    refine ⟨configuration, rfl, ?_⟩
    intro entry member
    obtain ⟨declaration, _, rfl⟩ := List.mem_map.mp member
    rfl

omit [DecidableEq Config] in
/-- The snapshot's physical element count is the supplied finite enumeration's
length. No whole configuration function is part of the snapshot payload. -/
theorem prepare_dependency_count
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact)
    (names : List Declaration)
    (coverage : ∀ declaration, declaration ∈ names ↔ declaration ∈ plan.support)
    (configuration : Declaration → Config) :
    (prepare plan names coverage configuration).dependencies.length = names.length := by
  simp [prepare]

omit [DecidableEq Config] in
/-- The captured key set is exactly the plan's certified dependency support. -/
theorem prepared_dependency_key_support
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact)
    (saved : PreparedArtifact plan) :
    (saved.dependencies.map Prod.fst).toFinset = plan.support := by
  ext declaration
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨original, value⟩, member, equalName⟩
    dsimp at equalName
    subst original
    exact (saved.coverage declaration).mpr ⟨value, member⟩
  · intro supported
    obtain ⟨value, member⟩ := (saved.coverage declaration).mp supported
    exact ⟨(declaration, value), member, rfl⟩

omit [DecidableEq Config] in
/-- A duplicate-free supplied support enumeration captures one pair per
supported declaration, irrespective of the configuration's remaining domain. -/
theorem prepare_dependency_count_eq_card
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact)
    (names : List Declaration)
    (coverage : ∀ declaration, declaration ∈ names ↔ declaration ∈ plan.support)
    (nodup : names.Nodup) (configuration : Declaration → Config) :
    (prepare plan names coverage configuration).dependencies.length = plan.support.card := by
  rw [prepare_dependency_count]
  have support : names.toFinset = plan.support := by
    ext declaration
    simpa using coverage declaration
  rw [← support, List.toFinset_card_of_nodup nodup]

/-- Return the stored artifact only while its finite dependency snapshot is
current. The caller retains the current computation on refusal. -/
def reuse {plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact}
    (saved : PreparedArtifact plan) (current : Declaration → Config) : Option Artifact :=
  if dependenciesCurrent saved.dependencies current then some saved.artifact else none

theorem reuse_eq_fresh
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact)
    (saved : PreparedArtifact plan) (current : Declaration → Config) (artifact : Artifact)
    (accepted : reuse saved current = some artifact) :
    artifact = plan.run current := by
  unfold reuse at accepted
  split at accepted
  next valid =>
    have matchingValues := (dependenciesCurrent_exact _ _).mp valid
    obtain ⟨configuration, compiled, originalMatches⟩ := saved.compiled
    have agreement : Mettapedia.GSLT.AgreesOn plan.support configuration current := by
      intro declaration supported
      obtain ⟨value, member⟩ := (saved.coverage declaration).mp supported
      exact (originalMatches (declaration, value) member).symm.trans
        (matchingValues (declaration, value) member)
    have same := plan.stable agreement
    have stored := Option.some.inj accepted
    exact stored.symm.trans (compiled.trans same)
  next => contradiction

theorem changed_dependency_refuses
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config Artifact)
    (saved : PreparedArtifact plan) (current : Declaration → Config)
    (declaration : Declaration) (value : Config)
    (stored : (declaration, value) ∈ saved.dependencies)
    (changed : value ≠ current declaration) :
    reuse saved current = none := by
  have invalid : dependenciesCurrent saved.dependencies current ≠ true := by
    intro valid
    exact changed ((dependenciesCurrent_exact _ _).mp valid (declaration, value) stored)
  simp [reuse, invalid]

/-- A runtime guarded compilation result is installed into the present
residual, not into the branch image from which compilation was requested. -/
def installPrepared {X : Obj}
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config (Proposal family X))
    (saved : PreparedArtifact plan) (current : Declaration → Config)
    (live : Result family X) : Result family X :=
  match reuse saved current with
  | none => live
  | some proposal => proposal.install live

theorem installPrepared_preserves {X : Obj}
    (plan : Mettapedia.GSLT.FinitelySupportedPlan Declaration Config (Proposal family X))
    (saved : PreparedArtifact plan) (current : Declaration → Config)
    (live : Result family X) :
    observeResult (installPrepared plan saved current live) = observeResult live := by
  unfold installPrepared
  split
  · rfl
  · exact Proposal.install_preserves _ _

end Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanning
