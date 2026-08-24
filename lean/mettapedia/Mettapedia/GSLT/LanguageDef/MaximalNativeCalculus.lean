import Mathlib.Order.Preorder.Finite
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# The maximal-native-calculus principle

NIK does not assign one universal proof/checking regime to every guest.
Instead, a guest analysis recognizes a finite family of already-admitted
calculus realizations and licenses the members whose structural requirements
the guest has discharged.  The selected realization is maximal relative to
the license order on that finite set.

"Maximal" is intentional.  A finite partial order need not have a greatest
licensed element, and maximal capability does not imply globally optimal
runtime cost.  The latter is independently blocked by the optimization
impossibility ladder; finite-fragment cost optimality remains available.
-/

namespace Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uIndex uCapability uArtifact

/-! ## Finite licensed families -/

/-- A finite recognized family of native calculus realizations.

Every `package index` is already an arrow in the common admission algebra,
so semantic preservation is carried by its type.  `licensed` records the
subset whose additional structural preconditions have been discharged for
the selected guest. -/
structure RecognizedFamily
    (Index : Type uIndex) [PartialOrder Index] [DecidableEq Index]
    (source target : AdmissionObject.{uArtifact}) where
  package : Index → (source ⟶ target)
  /-- Structural capabilities used to justify the license order. -/
  Capability : Type uCapability
  /-- The capabilities actually supported by each recognized realization. -/
  supports : Index → Capability → Prop
  /-- Moving upward in the license order never loses a capability. -/
  supports_mono : ∀ {weaker stronger}, weaker ≤ stronger →
    ∀ capability, supports weaker capability → supports stronger capability
  /-- A strict comparison must expose a real additional capability; arbitrary
  index orders cannot masquerade as calculus strength. -/
  strict_support_gain : ∀ {weaker stronger}, weaker < stronger →
    ∃ capability, supports stronger capability ∧ ¬ supports weaker capability
  recognized : Finset Index
  licensed : Finset Index
  licensed_subset_recognized : licensed ⊆ recognized
  licensed_nonempty : licensed.Nonempty

namespace RecognizedFamily

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject.{uArtifact}}

/-- Maximality is relative to the licensed set and its declared partial
order.  It says that no strictly stronger licensed package lies above the
selected one; it does not say that the selection dominates all licensed
packages. -/
def IsMaximalLicensed
    (family : RecognizedFamily Index source target) (chosen : Index) : Prop :=
  Maximal (· ∈ family.licensed) chosen

/-- A greatest licensed realization dominates every licensed alternative.
This is stronger than maximality and need not exist in a partial order. -/
def IsGreatestLicensed
    (family : RecognizedFamily Index source target) (chosen : Index) : Prop :=
  chosen ∈ family.licensed ∧
    ∀ candidate ∈ family.licensed, candidate ≤ chosen

/-- Licensed realizations are upward-directed when every pair has a licensed
common upgrade.  This is the exact additional condition under which a finite
maximal selection becomes a genuinely strongest licensed calculus. -/
def LicensedDirected
    (family : RecognizedFamily Index source target) : Prop :=
  ∀ first ∈ family.licensed, ∀ second ∈ family.licensed,
    ∃ upper ∈ family.licensed, first ≤ upper ∧ second ≤ upper

/-- A strongest licensed realization, when it exists, is unique in the
declared partial order. -/
theorem greatestLicensed_unique
    (family : RecognizedFamily Index source target) {first second : Index}
    (firstGreatest : family.IsGreatestLicensed first)
    (secondGreatest : family.IsGreatestLicensed second) :
    first = second :=
  le_antisymm
    (secondGreatest.2 first firstGreatest.1)
    (firstGreatest.2 second secondGreatest.1)

/-- Every nonempty finite licensed family has a maximal member. -/
theorem exists_maximalLicensed
    (family : RecognizedFamily Index source target) :
    ∃ chosen, family.IsMaximalLicensed chosen :=
  family.licensed.exists_maximal family.licensed_nonempty

/-- The maximal-native-calculus principle as a proof-relevant selection
object. -/
def MaximalNativeCalculusPrinciple
    (family : RecognizedFamily Index source target) :=
  { chosen : Index // family.IsMaximalLicensed chosen }

/-- Finiteness and nonempty licensing discharge the principle. -/
theorem principle_inhabited
    (family : RecognizedFamily Index source target) :
    Nonempty family.MaximalNativeCalculusPrinciple := by
  obtain ⟨chosen, maximal⟩ := family.exists_maximalLicensed
  exact ⟨⟨chosen, maximal⟩⟩

/-- A selected maximal package is still the original admitted operation;
selection introduces no replay layer or new semantic premise. -/
def selectedOperation
    (family : RecognizedFamily Index source target)
    (selection : family.MaximalNativeCalculusPrinciple) :
    source ⟶ target :=
  family.package selection.1

/-- The selected operation preserves the source meaning by its admission
type, independently of the maximality proof. -/
theorem selectedOperation_preserves
    (family : RecognizedFamily Index source target)
    (selection : family.MaximalNativeCalculusPrinciple)
    (input : source.Carrier) (meaningful : source.Meaning input) :
    target.Meaning (family.selectedOperation selection |>.run input) :=
  (family.selectedOperation selection).preserves input meaningful

/-- Every licensed package was genuinely recognized. -/
theorem maximal_is_recognized
    (family : RecognizedFamily Index source target)
    (selection : family.MaximalNativeCalculusPrinciple) :
    selection.1 ∈ family.recognized :=
  family.licensed_subset_recognized selection.2.1

/-- A maximal selection has no strictly stronger licensed competitor. -/
theorem no_licensed_strict_upgrade
    (family : RecognizedFamily Index source target)
    (selection : family.MaximalNativeCalculusPrinciple)
    {candidate : Index} (candidateLicensed : candidate ∈ family.licensed) :
    ¬ selection.1 < candidate := by
  intro strict
  have reverse : candidate ≤ selection.1 :=
    selection.2.2 candidateLicensed strict.le
  exact (not_le_of_gt strict) reverse

/-- In an upward-directed licensed family, maximality is not merely Pareto
optimality: the selected realization dominates every licensed package. -/
theorem maximal_is_greatest_of_licensedDirected
    (family : RecognizedFamily Index source target)
    (selection : family.MaximalNativeCalculusPrinciple)
    (directed : family.LicensedDirected) :
    family.IsGreatestLicensed selection.1 := by
  constructor
  · exact selection.2.1
  · intro candidate candidateLicensed
    obtain ⟨upper, upperLicensed, chosenLeUpper, candidateLeUpper⟩ :=
      directed selection.1 selection.2.1 candidate candidateLicensed
    exact candidateLeUpper.trans
      (selection.2.2 upperLicensed chosenLeUpper)

/-! ## Request-indexed licensed fibres -/

/-- A capability request cuts out the exact licensed fibre relevant to one
semantic task.  The request may encode a guest, judgment class, fragment,
trust boundary, and dependency revision; only its required capabilities and
the proved finite candidate set matter to generic selection.

The exactness field prevents a dispatcher from quietly omitting a stronger
licensed candidate.  All candidates still have the common source and target
of the surrounding family: modes with different semantic contracts belong in
different request fibres and are not compared by an arbitrary global rank. -/
structure CapabilityRequest
    (family : RecognizedFamily Index source target) where
  required : Set family.Capability
  candidates : Finset Index
  candidates_exact : ∀ candidate,
    candidate ∈ candidates ↔
      candidate ∈ family.licensed ∧
        ∀ capability ∈ required, family.supports candidate capability
  candidates_nonempty : candidates.Nonempty

namespace CapabilityRequest

variable {family : RecognizedFamily Index source target}

/-- Restrict a recognized family to the exact licensed fibre selected by a
request.  No operation, capability order, or semantic proof is changed. -/
def restrictedFamily (request : family.CapabilityRequest) :
    RecognizedFamily Index source target where
  package := family.package
  Capability := family.Capability
  supports := family.supports
  supports_mono := family.supports_mono
  strict_support_gain := family.strict_support_gain
  recognized := family.recognized
  licensed := request.candidates
  licensed_subset_recognized := by
    intro candidate candidateMember
    exact family.licensed_subset_recognized
      ((request.candidates_exact candidate).mp candidateMember).1
  licensed_nonempty := request.candidates_nonempty

/-- Every selected request candidate supports every requested capability. -/
theorem selected_supports_required
    (request : family.CapabilityRequest)
    (selection : request.restrictedFamily.MaximalNativeCalculusPrinciple)
    {capability : family.Capability}
    (required : capability ∈ request.required) :
    family.supports selection.1 capability :=
  ((request.candidates_exact selection.1).mp selection.2.1).2
    capability required

/-- Common-upgrade closure descends from the whole licensed family to every
nonempty exact capability-request fibre.  An upper realization retains the
requested capabilities by monotonicity. -/
theorem restricted_licensedDirected
    (request : family.CapabilityRequest)
    (directed : family.LicensedDirected) :
    request.restrictedFamily.LicensedDirected := by
  intro first firstMember second secondMember
  have firstData := (request.candidates_exact first).mp firstMember
  have secondData := (request.candidates_exact second).mp secondMember
  obtain ⟨upper, upperLicensed, firstLeUpper, secondLeUpper⟩ :=
    directed first firstData.1 second secondData.1
  have upperSupports :
      ∀ capability ∈ request.required,
        family.supports upper capability := by
    intro capability capabilityRequired
    exact family.supports_mono firstLeUpper capability
      (firstData.2 capability capabilityRequired)
  have upperMember : upper ∈ request.candidates :=
    (request.candidates_exact upper).mpr
      ⟨upperLicensed, upperSupports⟩
  exact ⟨upper, upperMember, firstLeUpper, secondLeUpper⟩

/-- A proof-relevant strongest realization for one capability request. -/
def StrongestNativeCalculusPrinciple
    (request : family.CapabilityRequest) :=
  { chosen : Index // request.restrictedFamily.IsGreatestLicensed chosen }

/-- When recognized licensed realizations admit common upgrades, every
feasible request whose own fibre admits common upgrades has a strongest
realization.  Global directedness is not required. -/
theorem strongestPrinciple_inhabited_of_restrictedDirected
    (request : family.CapabilityRequest)
    (directed : request.restrictedFamily.LicensedDirected) :
    Nonempty request.StrongestNativeCalculusPrinciple := by
  obtain ⟨selection⟩ := request.restrictedFamily.principle_inhabited
  exact ⟨⟨selection.1,
    RecognizedFamily.maximal_is_greatest_of_licensedDirected
      request.restrictedFamily selection directed⟩⟩

/-- Directedness of the whole licensed family is a convenient sufficient
condition for request-local strongest selection. -/
theorem strongestPrinciple_inhabited
    (request : family.CapabilityRequest)
    (directed : family.LicensedDirected) :
    Nonempty request.StrongestNativeCalculusPrinciple :=
  request.strongestPrinciple_inhabited_of_restrictedDirected
    (request.restricted_licensedDirected directed)

/-- The strongest realization for a request is unique.  This is the precise
condition under which NIK may expose one canonical "strongest kernel" rather
than a policy-selected maximal frontier. -/
theorem existsUnique_strongest_of_restrictedDirected
    (request : family.CapabilityRequest)
    (directed : request.restrictedFamily.LicensedDirected) :
    ∃! chosen, request.restrictedFamily.IsGreatestLicensed chosen := by
  obtain ⟨strongest⟩ :=
    request.strongestPrinciple_inhabited_of_restrictedDirected directed
  refine ⟨strongest.1, strongest.2, ?_⟩
  intro candidate candidateStrongest
  exact RecognizedFamily.greatestLicensed_unique request.restrictedFamily
    candidateStrongest strongest.2

/-- Whole-family common-upgrade closure supplies the request-local criterion. -/
theorem existsUnique_strongest
    (request : family.CapabilityRequest)
    (directed : family.LicensedDirected) :
    ∃! chosen, request.restrictedFamily.IsGreatestLicensed chosen :=
  request.existsUnique_strongest_of_restrictedDirected
    (request.restricted_licensedDirected directed)

/-- A strongest request realization is still the original admitted operation;
selection introduces no checker or certificate representation. -/
def strongestOperation
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple) :
    source ⟶ target :=
  family.package selection.1

theorem strongestOperation_preserves
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    (input : source.Carrier) (meaningful : source.Meaning input) :
    target.Meaning ((request.strongestOperation selection).run input) :=
  (request.strongestOperation selection).preserves input meaningful

/-- A strongest realization carries every capability required by its request. -/
theorem strongest_supports_required
    (request : family.CapabilityRequest)
    (selection : request.StrongestNativeCalculusPrinciple)
    {capability : family.Capability}
    (required : capability ∈ request.required) :
    family.supports selection.1 capability :=
  ((request.candidates_exact selection.1).mp selection.2.1).2
    capability required

end CapabilityRequest

end RecognizedFamily

/-! ## Positive canary: an actual admitted family -/

namespace Canary

open NIKMetalogic.AdmissionCanary

/-- A second nonidentity admitted operation on positive naturals. -/
def addTwo : positiveNaturals ⟶ positiveNaturals where
  run := fun (value : Nat) => Nat.succ (Nat.succ value)
  preserves := fun _ _ => Nat.succ_ne_zero _

/-- Two increasingly capable realizations in a linear license order. -/
def linearFamily :
    RecognizedFamily (Fin 2) positiveNaturals positiveNaturals where
  package
    | ⟨0, _⟩ => successor
    | ⟨1, _⟩ => addTwo
  Capability := Fin 2
  supports := fun realization capability => capability ≤ realization
  supports_mono := by
    intro weaker stronger related capability supported
    exact supported.trans related
  strict_support_gain := by
    intro weaker stronger strict
    exact ⟨stronger, le_rfl, not_le_of_gt strict⟩
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := Finset.univ_nonempty

/-- The stronger indexed package is a maximal licensed realization. -/
theorem one_is_maximal : linearFamily.IsMaximalLicensed (1 : Fin 2) := by
  constructor
  · simp [linearFamily]
  · intro candidate candidateLicensed oneLeCandidate
    omega

/-- The linear canary has common licensed upgrades, so its maximal choice is
also a genuine strongest realization. -/
theorem linearFamily_licensedDirected : linearFamily.LicensedDirected := by
  intro first firstLicensed second secondLicensed
  exact ⟨max first second, by simp [linearFamily],
    le_max_left first second, le_max_right first second⟩

theorem one_is_greatest : linearFamily.IsGreatestLicensed (1 : Fin 2) :=
  RecognizedFamily.maximal_is_greatest_of_licensedDirected linearFamily
    ⟨1, one_is_maximal⟩ linearFamily_licensedDirected

/-- A request for the second capability has exactly the stronger realization
in its licensed fibre. -/
def secondCapability : linearFamily.Capability := (1 : Fin 2)

def secondCapabilityRequest : linearFamily.CapabilityRequest where
  required := fun capability => capability = secondCapability
  candidates := {(1 : Fin 2)}
  candidates_exact := by
    intro candidate
    constructor
    · intro candidateMember
      have candidateEqual : candidate = (1 : Fin 2) := by
        simpa using candidateMember
      subst candidate
      constructor
      · simp [linearFamily]
      · intro capability capabilityRequired
        rcases capabilityRequired with rfl
        exact le_rfl
    · rintro ⟨_, supportsRequired⟩
      have supportsSecond := supportsRequired secondCapability rfl
      change (1 : Fin 2) ≤ candidate at supportsSecond
      fin_cases candidate
      · simp at supportsSecond
      · simp
  candidates_nonempty := by simp

/-- The request-indexed theorem selects one unique strongest realization. -/
theorem secondCapabilityRequest_uniqueStrongest :
    ∃! chosen,
      secondCapabilityRequest.restrictedFamily.IsGreatestLicensed chosen :=
  secondCapabilityRequest.existsUnique_strongest
    linearFamily_licensedDirected

/-- Its selected realization really carries the requested capability. -/
theorem secondCapabilityRequest_selected_supports
    (selection :
      secondCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple) :
    linearFamily.supports selection.1 secondCapability :=
  secondCapabilityRequest.selected_supports_required selection rfl

/-- The concrete family exercises selection on nonidentity operations and a
nonempty semantic fibre. -/
theorem concrete_maximal_operation_preserves :
    positiveNaturals.Meaning
      ((linearFamily.package (1 : Fin 2)).run (1 : Nat)) := by
  exact Nat.succ_ne_zero _

end Canary

/-! ## Negative canary: maximal need not mean greatest -/

namespace NoGreatestCanary

inductive Choice where
  | left
  | right
  deriving DecidableEq, Repr

/-- The discrete order makes the two choices incomparable. -/
instance : PartialOrder Choice where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ first second => first.trans second
  le_antisymm := fun _ _ forward _ => forward

def family :
    RecognizedFamily Choice
      NIKMetalogic.AdmissionCanary.positiveNaturals
      NIKMetalogic.AdmissionCanary.positiveNaturals where
  package
    | .left => NIKMetalogic.AdmissionCanary.successor
    | .right => Canary.addTwo
  Capability := Choice
  supports := Eq
  supports_mono := by
    intro weaker stronger related capability supported
    exact related.symm.trans supported
  strict_support_gain := by
    intro weaker stronger strict
    exact False.elim (strict.2 strict.1.symm)
  recognized := {.left, .right}
  licensed := {.left, .right}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.left, by simp⟩

theorem left_maximal : family.IsMaximalLicensed .left := by
  constructor
  · simp [family]
  · intro candidate licensed related
    exact related.symm

theorem right_maximal : family.IsMaximalLicensed .right := by
  constructor
  · simp [family]
  · intro candidate licensed related
    exact related.symm

theorem left_has_capability_right_lacks :
    family.supports .left .left ∧ ¬ family.supports .right .left := by
  constructor
  · rfl
  · simp [family]

theorem right_has_capability_left_lacks :
    family.supports .right .right ∧ ¬ family.supports .left .right := by
  constructor
  · rfl
  · simp [family]

/-- A finite licensed family may have multiple incomparable maximal members
and no greatest member.  Any slogan saying "the strongest calculus" must
therefore be read as maximal relative to the declared license order. -/
theorem no_greatest_licensed :
    ¬ ∃ chosen, chosen ∈ family.licensed ∧
      ∀ candidate ∈ family.licensed, candidate ≤ chosen := by
  rintro ⟨chosen, chosenLicensed, greatest⟩
  cases chosen with
  | left =>
      have rightLe : Choice.right ≤ Choice.left :=
        greatest .right (by simp [family])
      cases rightLe
  | right =>
      have leftLe : Choice.left ≤ Choice.right :=
        greatest .left (by simp [family])
      cases leftLe

/-- The negative family is not directed: its incomparable realizations have
no licensed common upgrade. -/
theorem not_licensedDirected : ¬ family.LicensedDirected := by
  intro directed
  obtain ⟨upper, upperLicensed, leftLe, rightLe⟩ :=
    directed .left (by simp [family]) .right (by simp [family])
  cases upper with
  | left => cases rightLe
  | right => cases leftLe

/-- Requiring no additional capability leaves both incomparable realizations
eligible.  A request fibre therefore need not have a strongest member. -/
def neutralRequest : family.CapabilityRequest where
  required := ∅
  candidates := {.left, .right}
  candidates_exact := by
    intro candidate
    constructor
    · intro candidateMember
      refine ⟨?_, ?_⟩
      · simpa [family] using candidateMember
      · intro capability capabilityMember
        simp at capabilityMember
    · rintro ⟨candidateLicensed, _⟩
      simpa [family] using candidateLicensed
  candidates_nonempty := ⟨.left, by simp⟩

theorem neutralRequest_no_strongest :
    ¬ ∃ chosen,
      neutralRequest.restrictedFamily.IsGreatestLicensed chosen := by
  rintro ⟨chosen, strongest⟩
  apply no_greatest_licensed
  refine ⟨chosen, ?_, ?_⟩
  · cases chosen <;> simp [family]
  · intro candidate _
    apply strongest.2 candidate
    cases candidate <;>
      simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        neutralRequest]

end NoGreatestCanary

/-! ## Connection to the computation/certificate and optimization bounds -/

/-- Whenever direct computation exists, it is already an exact authority;
maximal selection does not force a certificate representation onto it. -/
theorem direct_kernel_remains_certificate_free
    {Claim : Type*} {Meaning : Claim → Prop}
    (kernel : KernelAuthority.Checker.DecisionKernel Claim Meaning) :
    kernel.toChecker.Authority Meaning :=
  kernel.authority

/-- Finite evidence is nevertheless strictly necessary for some computable
exact trust boundaries: this is the middle band of the doctrine. -/
theorem evidence_can_exceed_computable_direct_decision :
    ((∃ checker : KernelAuthority.Checker Nat.Partrec.Code Nat,
        Computable (fun input : Nat.Partrec.Code × Nat =>
          checker.check input.1 input.2) ∧
        checker.Sound KernelAuthority.Checker.HaltingMeaning ∧
        checker.CertificateComplete KernelAuthority.Checker.HaltingMeaning) ∧
      ¬ ∃ kernel : KernelAuthority.Checker.DecisionKernel Nat.Partrec.Code
          KernelAuthority.Checker.HaltingMeaning,
        Computable kernel.decide) :=
  KernelAuthority.Checker.computable_certificate_authority_without_computable_decision

/-- Maximal capability selection does not imply a universally optimal
compiler.  Universal pointwise optimality fails in the admitted threshold
family, while an explicitly finite fragment has an optimal member. -/
theorem maximality_respects_optimization_boundary :
    (¬ ∃ chosen : Nat,
      NIKMetalogic.OptimizationLimits.PointwiseOptimal
        NIKMetalogic.OptimizationLimits.thresholdCompiler chosen) ∧
    (∃ chosen : Fin 2, ∀ candidate : Fin 2,
      NIKMetalogic.OptimizationLimits.fragmentCost
          (NIKMetalogic.OptimizationLimits.thresholdCompiler chosen.val)
          ({1, 2} : Finset Nat) ≤
        NIKMetalogic.OptimizationLimits.fragmentCost
          (NIKMetalogic.OptimizationLimits.thresholdCompiler candidate.val)
          ({1, 2} : Finset Nat)) :=
  ⟨NIKMetalogic.OptimizationLimits.NoUniversalOptimalCompiler,
    NIKMetalogic.OptimizationLimits.finiteThresholdFragment_has_optimal_compiler⟩

#print axioms RecognizedFamily.maximal_is_greatest_of_licensedDirected
#print axioms RecognizedFamily.greatestLicensed_unique
#print axioms RecognizedFamily.CapabilityRequest.existsUnique_strongest_of_restrictedDirected
#print axioms RecognizedFamily.CapabilityRequest.existsUnique_strongest
#print axioms RecognizedFamily.CapabilityRequest.strongestOperation_preserves
#print axioms Canary.one_is_greatest
#print axioms Canary.secondCapabilityRequest_uniqueStrongest
#print axioms NoGreatestCanary.not_licensedDirected
#print axioms NoGreatestCanary.neutralRequest_no_strongest

end Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
