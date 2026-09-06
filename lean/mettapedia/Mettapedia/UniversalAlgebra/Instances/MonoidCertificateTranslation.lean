import Mettapedia.UniversalAlgebra.Instances.MonoidConservativeExtension
import Mettapedia.UniversalAlgebra.NIK.ConstructiveCertifiedTranslation

/-!
# Constructive certificate translation for a redundant monoid extension

The monoid equation system extended by the already derived equation
`(1 * x) * 1 = x` is translated back to the original system by concrete
certificates.  The added occurrence expands to a three-node base derivation.
The reverse translation embeds each original axiom occurrence into the
extension.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK.Monoid

open Mettapedia.Logic
open Mettapedia.UniversalAlgebra.Monoid
open AxiomCertificateTranslation

abbrev monoidInterface := equationalRuleInterface equationSystem

/-- The right-unit axiom instantiated at `1 * x`. -/
def rightUnitAtOneMulX : AcceptedCertificate monoidInterface
    (mul (mul one x) one, mul one x) := by
  let substitution : Nat → Term signature :=
    fun index => if index = 0 then mul one x else .var index
  exact AcceptedCertificate.node monoidInterface
    (.systemInstance
      (⟨2, by simp [equationSystem]⟩ : Fin equationSystem.equations.length)
      substitution)
    (mul (mul one x) one, mul one x) Fin.elim0 (by
      simp [monoidInterface, equationalRuleInterface,
        EquationalRuleWitness.isInstance, substitution, equationSystem,
        subst_mul, subst_one, x])
    (fun position => Fin.elim0 position)

@[simp] theorem rightUnitAtOneMulX_nodeCount :
    rightUnitAtOneMulX.nodeCount = 1 := rfl

/-- The listed left-unit axiom as a native accepted certificate. -/
def leftUnitCertificate : AcceptedCertificate monoidInterface
    (mul one x, x) := by
  exact AcceptedCertificate.node monoidInterface
    (.systemInstance
      (⟨1, by simp [equationSystem]⟩ : Fin equationSystem.equations.length)
      Term.var)
    (mul one x, x) Fin.elim0 (by
      simp [monoidInterface, equationalRuleInterface,
        EquationalRuleWitness.isInstance, equationSystem,
        Term.subst_variables])
    (fun position => Fin.elim0 position)

@[simp] theorem leftUnitCertificate_nodeCount :
    leftUnitCertificate.nodeCount = 1 := rfl

/-- The redundant equation expanded into right unit, left unit, and
transitivity. -/
def derivedEquationCertificate : AcceptedCertificate monoidInterface
    (mul (mul one x) one, x) := by
  let first : Equation signature := (mul (mul one x) one, mul one x)
  let second : Equation signature := (mul one x, x)
  let premises : Fin 2 → Equation signature := ![first, second]
  let children : (position : Fin 2) →
      AcceptedCertificate monoidInterface (premises position) := by
    intro position
    refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible =>
      Fin.elim0 impossible) tail) position
    · change AcceptedCertificate monoidInterface first
      exact rightUnitAtOneMulX
    · change AcceptedCertificate monoidInterface second
      exact leftUnitCertificate
  exact AcceptedCertificate.node monoidInterface
    (.trans (mul (mul one x) one) (mul one x) x)
    (mul (mul one x) one, x) premises (by
      simp only [monoidInterface, equationalRuleInterface,
        EquationalRuleWitness.isInstance, decide_eq_true_eq]
      constructor
      · rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
        rfl
      · trivial) children

@[simp] theorem derivedEquationCertificate_nodeCount :
    derivedEquationCertificate.nodeCount = 3 := by
  simp [derivedEquationCertificate, AcceptedCertificate.node_nodeCount,
    Fin.sum_univ_succ]

/-- Every occurrence of the redundant extension has a concrete certificate in
the original monoid system. -/
def extensionToMonoid :
    AxiomCertificateTranslation derivedExtension equationSystem where
  certificate occurrence := by
    change Fin 4 at occurrence
    refine Fin.cases ?_ (fun tail₁ => Fin.cases ?_ (fun tail₂ =>
      Fin.cases ?_ (fun tail₃ => Fin.cases ?_ (fun impossible =>
        Fin.elim0 impossible) tail₃) tail₂) tail₁) occurrence
    · simpa [derivedExtension, EquationSystem.extend, equationSystem] using
        (listedEquationCertificate equationSystem
          (⟨0, by simp [equationSystem]⟩ :
            Fin equationSystem.equations.length))
    · simpa [derivedExtension, EquationSystem.extend, equationSystem] using
        (listedEquationCertificate equationSystem
          (⟨1, by simp [equationSystem]⟩ :
            Fin equationSystem.equations.length))
    · simpa [derivedExtension, EquationSystem.extend, equationSystem] using
        (listedEquationCertificate equationSystem
          (⟨2, by simp [equationSystem]⟩ :
            Fin equationSystem.equations.length))
    · refine
        { certificate := derivedEquationCertificate.certificate
          accepted := derivedEquationCertificate.accepted
          concludes := ?_ }
      change derivedEquationCertificate.certificate.concl =
        (mul (mul one x) one, x)
      exact derivedEquationCertificate.concludes

/-- Every original monoid occurrence has its corresponding one-node
certificate in the redundant extension. -/
def monoidToExtension :
    AxiomCertificateTranslation equationSystem derivedExtension where
  certificate occurrence := by
    change Fin 3 at occurrence
    refine Fin.cases ?_ (fun tail₁ => Fin.cases ?_ (fun tail₂ =>
      Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail₂) tail₁)
      occurrence
    · simpa [derivedExtension, EquationSystem.extend, equationSystem] using
        (listedEquationCertificate derivedExtension
          (⟨0, by simp [derivedExtension, EquationSystem.extend,
            equationSystem]⟩ : Fin derivedExtension.equations.length))
    · simpa [derivedExtension, EquationSystem.extend, equationSystem] using
        (listedEquationCertificate derivedExtension
          (⟨1, by simp [derivedExtension, EquationSystem.extend,
            equationSystem]⟩ : Fin derivedExtension.equations.length))
    · simpa [derivedExtension, EquationSystem.extend, equationSystem] using
        (listedEquationCertificate derivedExtension
          (⟨2, by simp [derivedExtension, EquationSystem.extend,
            equationSystem]⟩ : Fin derivedExtension.equations.length))

/-- The constructive occurrence map gives an exact all-input native authority
translation back to monoids. -/
def extensionCertifiedTranslation :
    Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory.CertifiedTranslation
      (contract derivedExtension) (contract equationSystem) :=
  extensionToMonoid.authorityTranslation

/-- The exact authority route is conservative because concrete certificate
translations exist in both directions. -/
theorem extensionCertifiedTranslation_conservative :
    extensionCertifiedTranslation.toTheoryTranslation.Conservative :=
  extensionToMonoid.authorityTranslation_conservative monoidToExtension

/-- The fourth equation occurrence as a one-node source certificate. -/
def addedOccurrence : Fin derivedExtension.equations.length :=
  ⟨3, by simp [derivedExtension, EquationSystem.extend, equationSystem]⟩

def addedOccurrenceCertificate :
    AcceptedCertificate (equationalRuleInterface derivedExtension)
      (mul (mul one x) one, x) := by
  exact AcceptedCertificate.node (equationalRuleInterface derivedExtension)
    (.systemInstance addedOccurrence Term.var)
    (mul (mul one x) one, x) Fin.elim0 (by
      simp [equationalRuleInterface, EquationalRuleWitness.isInstance,
        addedOccurrence, derivedExtension, EquationSystem.extend,
        equationSystem, Term.subst_variables])
    (fun position => Fin.elim0 position)

@[simp] theorem addedOccurrenceCertificate_nodeCount :
    addedOccurrenceCertificate.nodeCount = 1 := rfl

@[simp] theorem replacementForAddedOccurrence_nodeCount :
    (extensionToMonoid.certificate addedOccurrence).nodeCount = 3 := by
  change derivedEquationCertificate.nodeCount = 3
  exact derivedEquationCertificate_nodeCount

/-- The structural compiler transports the added occurrence to a valid base
certificate with the same conclusion. -/
theorem compiled_addedOccurrence_valid :
    (extensionToMonoid.compile addedOccurrenceCertificate.certificate).valid
      monoidInterface = true := by
  rw [extensionToMonoid.compile_valid]
  exact addedOccurrenceCertificate.accepted

theorem compiled_addedOccurrence_concl :
    (extensionToMonoid.compile addedOccurrenceCertificate.certificate).concl =
      (mul (mul one x) one, x) := by
  calc
    (extensionToMonoid.compile addedOccurrenceCertificate.certificate).concl =
        addedOccurrenceCertificate.certificate.concl :=
      extensionToMonoid.compile_concl addedOccurrenceCertificate.certificate
    _ = (mul (mul one x) one, x) := addedOccurrenceCertificate.concludes

/-- Non-vacuous cost receipt: the one-node use of the redundant source axiom
is expanded by the generic compiler into the explicit three-node base proof. -/
theorem compiled_addedOccurrence_nodeCount :
    (extensionToMonoid.compile
      addedOccurrenceCertificate.certificate).nodeCount = 3 := by
  rw [extensionToMonoid.compile_nodeCount_of_valid
    addedOccurrenceCertificate.certificate
    addedOccurrenceCertificate.accepted]
  change (extensionToMonoid.certificate addedOccurrence).nodeCount = 3
  exact replacementForAddedOccurrence_nodeCount

/-- Negative control: the collapsing extension cannot provide concrete base
certificates for all of its axiom occurrences. -/
theorem no_collapsingExtensionToMonoid :
    ¬ Nonempty
      (AxiomCertificateTranslation collapsingExtension equationSystem) := by
  rintro ⟨translation⟩
  apply distinct_variables_not_consequence
  apply translation.preservesConsequence
  apply EquationalConsequence.of_mem
  change ((Term.var 0 : Term signature), Term.var 1) ∈
    collapsingExtension.equations
  simp [collapsingExtension, EquationSystem.extend]

end Mettapedia.UniversalAlgebra.NIK.Monoid
