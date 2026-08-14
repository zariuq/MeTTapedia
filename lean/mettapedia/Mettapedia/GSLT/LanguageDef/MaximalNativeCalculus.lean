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

end Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
