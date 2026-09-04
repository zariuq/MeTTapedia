import Mettapedia.TypeTheory.DisplayedEvidence
import Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability

/-!
# Bridge from MeTTa gradual capabilities to displayed evidence

The gradual-dependent capability used by MeTTa is an instance of the general
displayed-evidence theory.  This module gives exact equivalences for its
families, proof-relevant refutations, live states, and precision relation.

The bridge leaves the product-specific demand, revision, and execution
machinery on the MeTTa side.  General observer factorization and evidence
variance laws live in `TypeTheory.DisplayedEvidence`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.DisplayedEvidenceBridge

universe uRaw uExact

/-- Forget only the product namespace; the raw carrier and exact fibres are
unchanged. -/
def family (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact}) :
    Mettapedia.TypeTheory.DisplayedEvidence.Family.{uRaw, uExact} where
  Raw := fibre.Raw
  Exact := fibre.Exact

/-- Prime's path-labelled refutation is exactly a displayed refutation with
`List Nat` as its proof-relevant reason. -/
def refutationEquiv (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact})
    (raw : fibre.Raw) :
    Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Refutation fibre raw ≃
      Mettapedia.TypeTheory.DisplayedEvidence.Refutation (family fibre) (List Nat) raw where
  toFun obstruction :=
    { reason := obstruction.path
      refutes := obstruction.refutes }
  invFun obstruction :=
    { path := obstruction.reason
      refutes := obstruction.refutes }
  left_inv obstruction := by cases obstruction; rfl
  right_inv obstruction := by cases obstruction; rfl

/-- Prime's three gradual states are exactly general displayed-evidence
states at the same raw index. -/
def statusEquiv (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact})
    (raw : fibre.Raw) :
    Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State fibre raw ≃
      Mettapedia.TypeTheory.DisplayedEvidence.Status (family fibre) (List Nat) raw where
  toFun
    | .suspended => .suspended
    | .exact evidence => .established evidence
    | .refuted obstruction =>
        .refuted ((refutationEquiv fibre raw).toFun obstruction)
  invFun
    | .suspended => .suspended
    | .established evidence => .exact evidence
    | .refuted obstruction =>
        .refuted ((refutationEquiv fibre raw).invFun obstruction)
  left_inv status := by
    cases status with
    | suspended => rfl
    | exact evidence => rfl
    | refuted obstruction => cases obstruction; rfl
  right_inv status := by
    cases status with
    | suspended => rfl
    | established evidence => rfl
    | refuted obstruction => cases obstruction; rfl

@[simp] theorem statusEquiv_suspended
    (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact}) (raw : fibre.Raw) :
    statusEquiv fibre raw .suspended = .suspended :=
  rfl

@[simp] theorem statusEquiv_exact
    (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact}) (raw : fibre.Raw)
    (evidence : fibre.Exact raw) :
    statusEquiv fibre raw (.exact evidence) = .established evidence :=
  rfl

/-- Prime refinement maps to general evidence refinement. -/
theorem refines_to_general (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact})
    (raw : fibre.Raw) {precise coarse : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State fibre raw}
    (precision : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Refines precise coarse) :
    Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines (statusEquiv fibre raw precise)
      (statusEquiv fibre raw coarse) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence =>
      exact @Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines.established_suspended
        (family fibre) (List Nat) raw evidence
  | refuted_suspended obstruction =>
      exact .refuted_suspended
        ((refutationEquiv fibre raw).toFun obstruction)

/-- General evidence refinement reflects back to Prime refinement. -/
theorem refines_from_general (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact})
    (raw : fibre.Raw) {precise coarse : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State fibre raw}
    (precision : Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines (statusEquiv fibre raw precise)
      (statusEquiv fibre raw coarse)) :
    Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Refines precise coarse := by
  cases precise with
  | suspended =>
      cases coarse with
      | suspended => exact .refl _
      | exact evidence => cases precision
      | refuted obstruction => cases precision
  | exact evidence =>
      cases coarse with
      | suspended => exact .exact_suspended evidence
      | exact otherEvidence =>
          have equal : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.exact evidence =
              Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.exact otherEvidence := by
            apply (statusEquiv fibre raw).injective
            exact Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines.established_rigid precision
          rw [equal]
          exact .refl _
      | refuted obstruction => cases precision
  | refuted obstruction =>
      cases coarse with
      | suspended => exact .refuted_suspended obstruction
      | exact evidence => cases precision
      | refuted otherObstruction =>
          have equal : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.refuted obstruction =
              Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.refuted otherObstruction := by
            apply (statusEquiv fibre raw).injective
            exact Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines.refuted_rigid precision
          rw [equal]
          exact .refl _

/-- The two precision relations agree exactly under the state equivalence. -/
theorem refines_iff (fibre : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.Fibre.{uRaw, uExact})
    (raw : fibre.Raw) {precise coarse : Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State fibre raw} :
    Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Refines precise coarse ↔
      Mettapedia.TypeTheory.DisplayedEvidence.Status.Refines (statusEquiv fibre raw precise)
        (statusEquiv fibre raw coarse) :=
  ⟨refines_to_general fibre raw, refines_from_general fibre raw⟩

/-! ## Axiom audit -/

#print axioms refutationEquiv
#print axioms statusEquiv
#print axioms refines_to_general
#print axioms refines_from_general
#print axioms refines_iff

end Mettapedia.Languages.MeTTa.Prime.DisplayedEvidenceBridge
