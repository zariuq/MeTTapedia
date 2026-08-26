import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Relational reproducible builds

A reproducible build is not merely a deterministic function or a matching
hash.  This file begins with a proof-relevant build relation and separates four
properties:

* an execution exists;
* executions from one full source agree at a declared artifact observation;
* executions from sources with the same declared-input view agree at that
  observation; and
* the existence and agreement properties hold together.

This separation follows the distinction between rebuildability and bitwise
reproducibility measured by Malka, Zacchiroli, and Zimmermann (2025), while the
declared-input factorization expresses the uncontrolled-input boundary in Lamb
and Zacchiroli (2021).  The task/build/scheduler distinction and the relational
generalization of nondeterministic task correctness are informed by Mokhov,
Mitchell, and Peyton Jones, *Build Systems a la Carte* (2020).  Hatta's
AGI-oriented requirements (2026) are higher-level profiles over this core; in
particular, finite manifests, hashes, signed trajectories, and verification
budgets are not assumed here.

The ambient source, artifact, declaration, and observation types are arbitrary.
Functional builds, exact artifact identity, finite manifests, and tolerance
tests are recovered as explicit specializations.  Proof-relevant execution
identity is retained even when the selected artifact observation erases it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ReproducibleBuild

open Mettapedia.GSLT.LooseRelationEquipment

universe u uDeclared uObserved uCoarse

/-! ## Relational builds and their observations -/

/-- A build relation retains the witness for one execution from a full source
state to a produced artifact. -/
abbrev RelationalBuild (Source Artifact : Type u) :=
  Loose Source Artifact

/-- One proof-relevant build occurrence. -/
abbrev Occurrence {Source Artifact : Type u}
    (build : RelationalBuild Source Artifact) :=
  Sigma fun source => Sigma fun artifact => build source artifact

namespace Occurrence

variable {Source Artifact : Type u}
  {build : RelationalBuild Source Artifact}

/-- The full source state of one build occurrence. -/
def source (occurrence : Occurrence build) : Source :=
  occurrence.1

/-- The artifact produced by one build occurrence. -/
def artifact (occurrence : Occurrence build) : Artifact :=
  occurrence.2.1

/-- The retained execution witness of one build occurrence. -/
def witness (occurrence : Occurrence build) :
    build occurrence.source occurrence.artifact :=
  occurrence.2.2

end Occurrence

/-- A machine-readable view claimed to contain the source inputs relevant to a
build observation.  Sufficiency is a theorem about `project`, not a field. -/
structure InputView (Source : Type u) where
  View : Type uDeclared
  project : Source -> View

/-- A declared observation of produced artifacts.  Exact artifact identity is
one instance; coarser semantic, fault, receipt, or cost observations are other
instances and must not be silently identified. -/
structure ArtifactObservation (Artifact : Type u) where
  Observed : Type uObserved
  observe : Artifact -> Observed

namespace ArtifactObservation

/-- Exact artifact identity as an observation. -/
def identity (Artifact : Type u) : ArtifactObservation.{u, u} Artifact where
  Observed := Artifact
  observe := id

/-- Explicitly forget information from an artifact observation. -/
def map {Artifact : Type u}
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    {Coarse : Type uCoarse}
    (forget : observation.Observed -> Coarse) :
    ArtifactObservation.{u, uCoarse} Artifact where
  Observed := Coarse
  observe := forget ∘ observation.observe

@[simp] theorem map_observe {Artifact : Type u}
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    {Coarse : Type uCoarse}
    (forget : observation.Observed -> Coarse) (artifact : Artifact) :
    (observation.map forget).observe artifact =
      forget (observation.observe artifact) :=
  rfl

end ArtifactObservation

/-- A binary acceptance test for two artifacts.  No equivalence-relation laws
are assumed: numerical tolerances and statistical tests need not be transitive
or quotient-valued. -/
structure AgreementTest (Artifact : Type u) where
  Accepts : Artifact -> Artifact -> Prop

/-- An observation is sound for an agreement test when observational equality
is sufficient to pass the test.  This explicit law is required before an exact
or coarser reproducibility result may discharge a tolerance test. -/
def ObservationSoundForTest {Artifact : Type u}
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    (test : AgreementTest Artifact) : Prop :=
  forall {left right},
    observation.observe left = observation.observe right ->
      test.Accepts left right

/-! ## Occurrence projections and factorization -/

variable {Source Artifact : Type u} {Coarse : Type uCoarse}

/-- Project a build occurrence to its declared source-input view. -/
def declaredOccurrence (build : RelationalBuild Source Artifact)
    (view : InputView.{u, uDeclared} Source) :
    Occurrence build -> view.View :=
  fun occurrence => view.project occurrence.source

/-- Project a build occurrence to the selected artifact observation. -/
def observedOccurrence (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    Occurrence build -> observation.Observed :=
  fun occurrence => observation.observe occurrence.artifact

/-! ## Existence and agreement -/

/-- A source is rebuildable when at least one artifact and execution witness
exist for it. -/
def RebuildableAt (build : RelationalBuild Source Artifact)
    (source : Source) : Prop :=
  Nonempty (Sigma fun artifact => build source artifact)

/-- A build relation is rebuildable on every source in its declared domain. -/
def Rebuildable (build : RelationalBuild Source Artifact) : Prop :=
  forall source, RebuildableAt build source

/-- Rebuildability is exactly totality of the proof-relevant build relation. -/
theorem rebuildable_iff_total (build : RelationalBuild Source Artifact) :
    Rebuildable build <-> Total build :=
  Iff.rfl

/-- Executions from one full source agree at the selected observation. -/
def ObservationConsistentAt (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    (source : Source) : Prop :=
  forall {left right},
    build source left -> build source right ->
      observation.observe left = observation.observe right

/-- Every full source has observationally consistent executions. -/
def ObservationConsistent (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact) : Prop :=
  forall source, ObservationConsistentAt build observation source

/-- Per-source reproducibility requires both existence and agreement. -/
def ReproducibleAt (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact)
    (source : Source) : Prop :=
  RebuildableAt build source /\
    ObservationConsistentAt build observation source

/-- A build is reproducible at an observation when every source rebuilds and
all executions from each fixed full source agree at that observation. -/
def Reproducible (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact) : Prop :=
  Rebuildable build /\ ObservationConsistent build observation

theorem reproducible_iff_forall_reproducibleAt
    (build : RelationalBuild Source Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    Reproducible build observation <->
      forall source, ReproducibleAt build observation source := by
  constructor
  · rintro ⟨rebuildable, consistent⟩ source
    exact ⟨rebuildable source, consistent source⟩
  · intro pointwise
    exact ⟨fun source => (pointwise source).1,
      fun source => (pointwise source).2⟩

/-- Cross-source declaration sufficiency: once restricted to actual build
occurrences, the observed artifact is constant on fibres of the declared-input
view.  This is strictly stronger than agreement at one full source. -/
def DeclarationSufficient (build : RelationalBuild Source Artifact)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uObserved} Artifact) : Prop :=
  Function.FactorsThrough
    (observedOccurrence build observation)
    (declaredOccurrence build view)

/-- Reproducibility from the declared view requires that every full source can
be rebuilt and that the declaration erases no distinction used by the selected
artifact observation. -/
def DeclaredViewReproducible (build : RelationalBuild Source Artifact)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uObserved} Artifact) : Prop :=
  Rebuildable build /\ DeclarationSufficient build view observation

namespace DeclarationSufficient

/-- Cross-source declaration sufficiency implies consistency at each fixed full
source. -/
theorem observationConsistent
    {build : RelationalBuild Source Artifact}
    {view : InputView.{u, uDeclared} Source}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (sufficient : DeclarationSufficient build view observation) :
    ObservationConsistent build observation := by
  intro source left right leftBuild rightBuild
  let leftOccurrence : Occurrence build :=
    ⟨source, left, leftBuild⟩
  let rightOccurrence : Occurrence build :=
    ⟨source, right, rightBuild⟩
  exact sufficient
    (a := leftOccurrence) (b := rightOccurrence) rfl

end DeclarationSufficient

namespace DeclaredViewReproducible

/-- Declared-view reproducibility entails ordinary per-source
reproducibility. -/
theorem reproducible
    {build : RelationalBuild Source Artifact}
    {view : InputView.{u, uDeclared} Source}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (reproducible : DeclaredViewReproducible build view observation) :
    Reproducible build observation :=
  ⟨reproducible.1, reproducible.2.observationConsistent⟩

end DeclaredViewReproducible

/-! ## Explicit agreement tests -/

/-- All executions from a fixed source pass a declared binary artifact test. -/
def PassesTestAt (build : RelationalBuild Source Artifact)
    (test : AgreementTest Artifact) (source : Source) : Prop :=
  forall {left right},
    build source left -> build source right -> test.Accepts left right

/-- Every fixed-source execution pair passes a declared binary artifact test. -/
def PassesTest (build : RelationalBuild Source Artifact)
    (test : AgreementTest Artifact) : Prop :=
  forall source, PassesTestAt build test source

namespace ObservationConsistent

/-- Observational consistency discharges a tolerance or statistical test only
through an explicit soundness law. -/
theorem passesTest
    {build : RelationalBuild Source Artifact}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    {test : AgreementTest Artifact}
    (consistent : ObservationConsistent build observation)
    (sound : ObservationSoundForTest observation test) :
    PassesTest build test := by
  intro source left right leftBuild rightBuild
  exact sound (consistent source leftBuild rightBuild)

end ObservationConsistent

/-! ## Executable reproducers versus fibre constancy -/

/-- An executable reproducer computes the observed artifact from the declared
input view and agrees on every real build occurrence. -/
structure Reproducer (build : RelationalBuild Source Artifact)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uObserved} Artifact) where
  reproduce : view.View -> observation.Observed
  agrees : forall occurrence,
    reproduce (declaredOccurrence build view occurrence) =
      observedOccurrence build observation occurrence

namespace Reproducer

variable {build : RelationalBuild Source Artifact}
  {view : InputView.{u, uDeclared} Source}
  {observation : ArtifactObservation.{u, uObserved} Artifact}

/-- An executable reproducer is a constructive factorization. -/
def toFactors (reproducer : Reproducer build view observation) :
    NonFactorization.Factors
      (declaredOccurrence build view)
      (observedOccurrence build observation) :=
  ⟨reproducer.reproduce, reproducer.agrees⟩

/-- Extract a reproducer from an existential factorization.  This is
noncomputable because `Factors` deliberately records existence in `Prop`. -/
noncomputable def ofFactors
    (factors : NonFactorization.Factors
      (declaredOccurrence build view)
      (observedOccurrence build observation)) :
    Reproducer build view observation where
  reproduce := Classical.choose factors
  agrees := Classical.choose_spec factors

/-- Executable reproducers are exactly the inhabitants of the constructive
factorization proposition. -/
theorem nonempty_iff_factors :
    Nonempty (Reproducer build view observation) <->
      NonFactorization.Factors
        (declaredOccurrence build view)
        (observedOccurrence build observation) := by
  constructor
  · rintro ⟨reproducer⟩
    exact reproducer.toFactors
  · intro factors
    exact ⟨ofFactors factors⟩

/-- Any executable reproducer establishes declaration sufficiency. -/
theorem declarationSufficient
    (reproducer : Reproducer build view observation) :
    DeclarationSufficient build view observation := by
  exact reproducer.toFactors.constantOnFibers

/-- If the observation codomain has a declared default, fibre constancy can be
extended outside the realized declaration image to an executable reproducer. -/
noncomputable def ofDeclarationSufficient
    [Inhabited observation.Observed]
    (sufficient : DeclarationSufficient build view observation) :
    Reproducer build view observation where
  reproduce := Function.extend
    (declaredOccurrence build view)
    (observedOccurrence build observation)
    (fun _ => default)
  agrees := fun occurrence =>
    sufficient.extend_apply (fun _ => default) occurrence

end Reproducer

/-- Declaration sufficiency is exactly constant-on-fibres in the reusable
non-factorization theory. -/
theorem declarationSufficient_iff_constantOnFibers
    (build : RelationalBuild Source Artifact)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    DeclarationSufficient build view observation <->
      NonFactorization.ConstantOnFibers
        (declaredOccurrence build view)
        (observedOccurrence build observation) :=
  Iff.rfl

/-- A surjective declared source view and rebuildability make the occurrence
projection onto declared inputs surjective. -/
theorem declaredOccurrence_surjective
    {build : RelationalBuild Source Artifact}
    {view : InputView.{u, uDeclared} Source}
    (rebuildable : Rebuildable build)
    (viewSurjective : Function.Surjective view.project) :
    Function.Surjective (declaredOccurrence build view) := by
  intro declared
  obtain ⟨source, sourceDeclares⟩ := viewSurjective declared
  obtain ⟨⟨artifact, witness⟩⟩ := rebuildable source
  exact ⟨⟨source, artifact, witness⟩, sourceDeclares⟩

/-- Under exact reachability of the declaration codomain, declaration
sufficiency is equivalent to the existence of an executable reproducer. -/
theorem nonempty_reproducer_iff_declarationSufficient_of_surjective
    {build : RelationalBuild Source Artifact}
    {view : InputView.{u, uDeclared} Source}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (surjective : Function.Surjective (declaredOccurrence build view)) :
    Nonempty (Reproducer build view observation) <->
      DeclarationSufficient build view observation := by
  rw [Reproducer.nonempty_iff_factors]
  simpa [DeclarationSufficient, Function.FactorsThrough,
    NonFactorization.ConstantOnFibers] using
    (NonFactorization.factors_iff_constantOnFibers surjective
      (observedOccurrence build observation))

/-! ## Monotonicity under explicit observation loss -/

namespace ObservationConsistent

/-- Forgetting artifact information preserves per-source consistency. -/
theorem map
    {build : RelationalBuild Source Artifact}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (consistent : ObservationConsistent build observation)
    (forget : observation.Observed -> Coarse) :
    ObservationConsistent build (observation.map forget) := by
  intro source left right leftBuild rightBuild
  exact congrArg forget (consistent source leftBuild rightBuild)

end ObservationConsistent

namespace Reproducible

/-- Reproducibility is monotone from a finer artifact observation to an
explicitly coarser one. -/
theorem mapObservation
    {build : RelationalBuild Source Artifact}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (reproducible : Reproducible build observation)
    (forget : observation.Observed -> Coarse) :
    Reproducible build (observation.map forget) :=
  ⟨reproducible.1, reproducible.2.map forget⟩

end Reproducible

namespace DeclarationSufficient

/-- Forgetting artifact information preserves declaration sufficiency. -/
theorem mapObservation
    {build : RelationalBuild Source Artifact}
    {view : InputView.{u, uDeclared} Source}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (sufficient : DeclarationSufficient build view observation)
    (forget : observation.Observed -> Coarse) :
    DeclarationSufficient build view (observation.map forget) := by
  intro left right sameDeclaration
  exact congrArg forget (sufficient sameDeclaration)

end DeclarationSufficient

namespace DeclaredViewReproducible

/-- Declared-view reproducibility is monotone under an explicitly declared
observation quotient. -/
theorem mapObservation
    {build : RelationalBuild Source Artifact}
    {view : InputView.{u, uDeclared} Source}
    {observation : ArtifactObservation.{u, uObserved} Artifact}
    (reproducible : DeclaredViewReproducible build view observation)
    (forget : observation.Observed -> Coarse) :
    DeclaredViewReproducible build view (observation.map forget) :=
  ⟨reproducible.1, reproducible.2.mapObservation forget⟩

end DeclaredViewReproducible

/-! ## Functional and proof-relevantly deterministic specializations -/

/-- Proof-relevant determinism implies consistency at every artifact
observation.  The converse fails when an observation erases artifacts or when
distinct execution witnesses produce the same artifact. -/
theorem observationConsistent_of_deterministic
    {build : RelationalBuild Source Artifact}
    (deterministic : Deterministic build)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    ObservationConsistent build observation := by
  intro source left right leftBuild rightBuild
  have samePair :
      (⟨left, leftBuild⟩ : Sigma fun artifact => build source artifact) =
        ⟨right, rightBuild⟩ :=
    (deterministic source).allEq _ _
  exact congrArg (fun pair => observation.observe pair.1) samePair

/-- A represented loose build is reproducible at every artifact observation. -/
theorem reproducible_of_representation
    {build : RelationalBuild Source Artifact}
    (representation : Representation build)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    Reproducible build observation :=
  ⟨representation.total,
    observationConsistent_of_deterministic
      representation.deterministic observation⟩

/-- Every functional companion build is reproducible at every declared
artifact observation. -/
theorem companion_reproducible (build : Source -> Artifact)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    Reproducible (companion build) observation :=
  reproducible_of_representation
    (Representation.companionSelf build) observation

/-- Exact functional specialization: declaration sufficiency for a companion
build is precisely factorization of its observed result through the declared
source view. -/
theorem companion_declarationSufficient_iff
    (build : Source -> Artifact)
    (view : InputView.{u, uDeclared} Source)
    (observation : ArtifactObservation.{u, uObserved} Artifact) :
    DeclarationSufficient (companion build) view observation <->
      Function.FactorsThrough
        (observation.observe ∘ build) view.project := by
  constructor
  · intro sufficient left right sameDeclaration
    let leftOccurrence : Occurrence (companion build) :=
      ⟨left, build left, ⟨⟨rfl⟩⟩⟩
    let rightOccurrence : Occurrence (companion build) :=
      ⟨right, build right, ⟨⟨rfl⟩⟩⟩
    exact sufficient
      (a := leftOccurrence) (b := rightOccurrence) sameDeclaration
  · intro factors
    rintro ⟨leftSource, leftArtifact, leftWitness⟩
      ⟨rightSource, rightArtifact, rightWitness⟩ sameDeclaration
    have leftEq : build leftSource = leftArtifact :=
      leftWitness.down.down
    have rightEq : build rightSource = rightArtifact :=
      rightWitness.down.down
    calc
      observation.observe leftArtifact =
          observation.observe (build leftSource) :=
        congrArg observation.observe leftEq.symm
      _ = observation.observe (build rightSource) :=
        factors sameDeclaration
      _ = observation.observe rightArtifact :=
        congrArg observation.observe rightEq

/-! ## Positive and negative controls -/

namespace Canary

/-! ### Rebuildability, consistency, and observation refinement -/

/-- One source may produce either Boolean. -/
def branching : RelationalBuild Unit Bool :=
  fun _ _ => Unit

theorem branching_rebuildable : Rebuildable branching := by
  intro source
  exact ⟨⟨false, ()⟩⟩

theorem branching_not_exact_consistent :
    Not (ObservationConsistent branching
      (ArtifactObservation.identity Bool)) := by
  intro consistent
  have falseEqTrue :=
    consistent () (left := false) (right := true) () ()
  exact Bool.false_ne_true falseEqTrue

/-- Erasing both Boolean results makes the same relation consistent. -/
def collapsedBoolObservation : ArtifactObservation Bool :=
  (ArtifactObservation.identity Bool).map (fun _ => ())

theorem branching_collapsed_consistent :
    ObservationConsistent branching collapsedBoolObservation := by
  intro source left right leftBuild rightBuild
  rfl

theorem branching_collapsed_reproducible :
    Reproducible branching collapsedBoolObservation :=
  ⟨branching_rebuildable, branching_collapsed_consistent⟩

theorem branching_not_exact_reproducible :
    Not (Reproducible branching
      (ArtifactObservation.identity Bool)) := by
  intro reproducible
  exact branching_not_exact_consistent reproducible.2

/-- A relation with no executions is vacuously consistent but not
rebuildable. -/
def emptyBuild : RelationalBuild Unit Unit :=
  fun _ _ => Empty

theorem emptyBuild_consistent :
    ObservationConsistent emptyBuild
      (ArtifactObservation.identity Unit) := by
  intro source left right leftBuild rightBuild
  exact leftBuild.elim

theorem emptyBuild_not_rebuildable : Not (Rebuildable emptyBuild) := by
  intro rebuildable
  obtain ⟨⟨artifact, witness⟩⟩ := rebuildable ()
  exact witness.elim

theorem emptyBuild_not_reproducible :
    Not (Reproducible emptyBuild
      (ArtifactObservation.identity Unit)) := by
  intro reproducible
  exact emptyBuild_not_rebuildable reproducible.1

/-! ### Result agreement does not collapse proof fibres -/

/-- Two distinct execution witnesses produce the sole artifact. -/
def duplicateEvidence : RelationalBuild Unit Unit :=
  fun _ _ => Bool

theorem duplicateEvidence_rebuildable : Rebuildable duplicateEvidence := by
  intro source
  exact ⟨⟨(), false⟩⟩

theorem duplicateEvidence_exact_consistent :
    ObservationConsistent duplicateEvidence
      (ArtifactObservation.identity Unit) := by
  intro source left right leftBuild rightBuild
  rfl

theorem duplicateEvidence_exact_reproducible :
    Reproducible duplicateEvidence
      (ArtifactObservation.identity Unit) :=
  ⟨duplicateEvidence_rebuildable,
    duplicateEvidence_exact_consistent⟩

theorem duplicateEvidence_not_deterministic :
    Not (Deterministic duplicateEvidence) := by
  intro deterministic
  have samePair := (deterministic ()).allEq
    (⟨(), false⟩ : Sigma fun artifact => duplicateEvidence () artifact)
    (⟨(), true⟩ : Sigma fun artifact => duplicateEvidence () artifact)
  have falseEqTrue : false = true :=
    congrArg
      (fun pair : Sigma fun _ : Unit => Bool => pair.2)
      samePair
  exact Bool.false_ne_true falseEqTrue

/-! ### Complete declarations and a hidden environment bit -/

/-- A small but non-degenerate complete source state: source, toolchain, and
hardware inputs are independently represented. -/
structure BuildInputs where
  sourceBit : Bool
  toolchainBit : Bool
  hardwareBit : Bool
  deriving DecidableEq

/-- The produced payload depends on hardware as well as source; the toolchain
is retained in the artifact ABI tag. -/
structure BuildArtifact where
  payload : Bool
  abiTag : Bool
  deriving DecidableEq

def compileInputs (inputs : BuildInputs) : BuildArtifact where
  payload := if inputs.hardwareBit then !inputs.sourceBit else inputs.sourceBit
  abiTag := inputs.toolchainBit

def compiledBuild : RelationalBuild BuildInputs BuildArtifact :=
  companion compileInputs

def completeInputView : InputView BuildInputs where
  View := BuildInputs
  project := id

/-- This view incorrectly omits hardware. -/
def incompleteInputView : InputView BuildInputs where
  View := Bool × Bool
  project := fun inputs => (inputs.sourceBit, inputs.toolchainBit)

def exactArtifactObservation : ArtifactObservation BuildArtifact :=
  ArtifactObservation.identity BuildArtifact

theorem compiledBuild_reproducible :
    Reproducible compiledBuild exactArtifactObservation :=
  companion_reproducible compileInputs exactArtifactObservation

theorem completeInputView_sufficient :
    DeclarationSufficient compiledBuild completeInputView
      exactArtifactObservation := by
  change DeclarationSufficient (companion compileInputs) completeInputView
    exactArtifactObservation
  rw [companion_declarationSufficient_iff]
  intro left right sameInput
  exact congrArg compileInputs sameInput

theorem completeInputView_reproducible :
    DeclaredViewReproducible compiledBuild completeInputView
      exactArtifactObservation :=
  ⟨compiledBuild_reproducible.1, completeInputView_sufficient⟩

def noHardwareInput : BuildInputs :=
  ⟨false, false, false⟩

def hardwareInput : BuildInputs :=
  ⟨false, false, true⟩

theorem incompleteInputView_not_sufficient :
    Not (DeclarationSufficient compiledBuild incompleteInputView
      exactArtifactObservation) := by
  intro sufficient
  let noHardwareOccurrence : Occurrence compiledBuild :=
    ⟨noHardwareInput, compileInputs noHardwareInput, ⟨⟨rfl⟩⟩⟩
  let hardwareOccurrence : Occurrence compiledBuild :=
    ⟨hardwareInput, compileInputs hardwareInput, ⟨⟨rfl⟩⟩⟩
  have sameArtifact := sufficient
    (a := noHardwareOccurrence) (b := hardwareOccurrence) rfl
  have differentArtifact :
      compileInputs noHardwareInput ≠ compileInputs hardwareInput := by
    decide
  exact differentArtifact sameArtifact

/-- Per-source reproducibility does not establish that a proposed declaration
is complete. -/
theorem compiledBuild_reproducible_but_incompleteView :
    Reproducible compiledBuild exactArtifactObservation /\
      Not (DeclarationSufficient compiledBuild incompleteInputView
        exactArtifactObservation) :=
  ⟨compiledBuild_reproducible, incompleteInputView_not_sufficient⟩

/-! ### A tolerance test need not define a quotient -/

/-- Symmetric distance-at-most-one acceptance on naturals.  It is intentionally
used only as a binary test, not assumed to be transitive. -/
def distanceOneTest : AgreementTest Nat where
  Accepts left right := left <= right + 1 /\ right <= left + 1

theorem distanceOne_zero_one : distanceOneTest.Accepts 0 1 := by
  change 0 <= 1 + 1 /\ 1 <= 0 + 1
  decide

theorem distanceOne_one_two : distanceOneTest.Accepts 1 2 := by
  change 1 <= 2 + 1 /\ 2 <= 1 + 1
  decide

theorem distanceOne_not_zero_two :
    Not (distanceOneTest.Accepts 0 2) := by
  change Not (0 <= 2 + 1 /\ 2 <= 0 + 1)
  decide

theorem exactNat_soundFor_distanceOne :
    ObservationSoundForTest (ArtifactObservation.identity Nat)
      distanceOneTest := by
  intro left right same
  cases same
  exact ⟨Nat.le_succ _, Nat.le_succ _⟩

end Canary

#print axioms DeclarationSufficient.observationConsistent
#print axioms Reproducer.nonempty_iff_factors
#print axioms nonempty_reproducer_iff_declarationSufficient_of_surjective
#print axioms companion_declarationSufficient_iff
#print axioms Canary.branching_not_exact_reproducible
#print axioms Canary.duplicateEvidence_not_deterministic
#print axioms Canary.incompleteInputView_not_sufficient
#print axioms Canary.distanceOne_not_zero_two

end Mettapedia.GSLT.Core.ReproducibleBuild
