import Foundation.FirstOrder.Incompleteness.Second
import Mettapedia.Logic.Bridges.FoundationNIKAuthority

/-!
# Second incompleteness at an exact certificate authority

Foundation supplies arithmetized syntax, the diagonal lemma, and Gödel's
second incompleteness theorem.  The intrinsic Foundation authority supplies an
exact checker whose certificates are typed proof terms.  Combining them
locates the bootstrap boundary at the executable authority interface:

* diagonal self-reference has an accepted same-theory certificate;
* a consistent arithmetic theory has no accepted certificate for its own
  formal consistency sentence;
* adjoining that consistency sentence as an axiom gives a stronger theory
  with an explicit accepted certificate.

No claim is made about an untrusted byte representation.  This is the typed
proof-authority layer to which a concrete wire checker must separately refine.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.FoundationSecondIncompletenessAuthority

open LO.Entailment
open LO.FirstOrder LO.FirstOrder.Arithmetic
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.Logic.Bridges.FoundationNIKAuthority

variable (T : Theory ℒₒᵣ) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

omit [T.Δ₁] in
/-- The diagonal fixed-point equivalence is an ordinary theorem of the same
arithmetic theory and therefore has an accepted intrinsic certificate. -/
theorem diagonal_certificate_exists
    (θ : Semisentence ℒₒᵣ 1) :
    ∃ certificate : IntrinsicCertificate T,
      (IntrinsicCertificate.checker T).check
        (fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝]) certificate = true := by
  obtain ⟨proof⟩ := diagonal (T := T) θ
  exact ⟨⟨_, proof⟩, by simp [IntrinsicCertificate.checker]⟩

/-- Gödel's second incompleteness theorem appears directly as universal
rejection at the exact certificate boundary. -/
theorem self_consistency_certificate_rejected [Consistent T]
    (certificate : IntrinsicCertificate T) :
    (IntrinsicCertificate.checker T).check
      (↑T.consistent) certificate = false := by
  cases accepted : (IntrinsicCertificate.checker T).check
      (↑T.consistent) certificate with
  | false => rfl
  | true =>
      have provable : LO.Entailment.Provable T (↑T.consistent) :=
        (IntrinsicCertificate.checker_authority T).sound
          (↑T.consistent) certificate accepted
      exact False.elim ((consistent_unprovable T) provable)

/-- Equivalently, no intrinsic proof certificate for the theory's own formal
consistency statement exists. -/
theorem no_self_consistency_certificate [Consistent T] :
    ¬ ∃ certificate : IntrinsicCertificate T,
      (IntrinsicCertificate.checker T).check
        (↑T.consistent) certificate = true := by
  rintro ⟨certificate, accepted⟩
  rw [self_consistency_certificate_rejected T certificate] at accepted
  contradiction

/-- The next theory rung has a proof term for the lower theory's consistency
sentence because that sentence is one of its explicit axioms. -/
noncomputable def consistencyProofInExtension :
  LO.Entailment.Prf (T + T.Con) (↑T.consistent) :=
  LO.Entailment.byAxm (S := Theory ℒₒᵣ) (𝓢 := T + T.Con)
    (by simp [Theory.add_def])

/-- Package the extension proof as an intrinsic authority certificate. -/
noncomputable def consistencyCertificateInExtension :
    IntrinsicCertificate (T + T.Con) :=
  ⟨↑T.consistent, consistencyProofInExtension T⟩

omit [𝗜𝚺₁ ⪯ T] in
/-- Positive higher-rung control: the extension checker accepts the explicit
certificate of the lower theory's consistency sentence. -/
theorem extension_accepts_consistency_certificate :
    (IntrinsicCertificate.checker (T + T.Con)).check
      (↑T.consistent) (consistencyCertificateInExtension T) = true := by
  simp [IntrinsicCertificate.checker, consistencyCertificateInExtension]

/-- The same consistency sentence is rejected by every same-theory
certificate but accepted by one certificate at the stronger extension. -/
theorem theory_extension_separates_consistency_certification [Consistent T] :
    (¬ ∃ certificate : IntrinsicCertificate T,
        (IntrinsicCertificate.checker T).check
          (↑T.consistent) certificate = true) ∧
      ∃ certificate : IntrinsicCertificate (T + T.Con),
        (IntrinsicCertificate.checker (T + T.Con)).check
          (↑T.consistent) certificate = true := by
  constructor
  · exact no_self_consistency_certificate T
  · exact ⟨consistencyCertificateInExtension T,
      extension_accepts_consistency_certificate T⟩

end Mettapedia.Logic.Bridges.FoundationSecondIncompletenessAuthority
