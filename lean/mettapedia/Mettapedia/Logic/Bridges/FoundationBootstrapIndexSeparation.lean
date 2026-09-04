import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Logic.Bridges.FoundationSecondIncompletenessAuthority

/-!
# Bootstrap indices and arithmetic strength are independent orders

`LowerContract` indexes which lower checker or authority layer a claim is
about. Foundation's strict-weaker relation compares object theories by
derivability strength. These are different mathematical orders:

* lifting a bootstrap contract raises its host index without changing the
  object theory named by the contract;
* replacing `T` by `T + Con(T)` strictly strengthens the object theory
  under the hypotheses of second incompleteness, while both contracts may
  retain exactly the same bootstrap host and target indices.

The separation prevents a numerical bootstrap level from being mistaken for
a proof-theoretic strength comparison. Any correspondence between the two
must be supplied as additional structure and proved for the selected tower.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.FoundationBootstrapIndexSeparation

open LO.Entailment
open LO.FirstOrder LO.FirstOrder.Arithmetic
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Logic.Bridges.FoundationNIKAuthority
open Mettapedia.Logic.Bridges.FoundationSecondIncompletenessAuthority

/-- At every bootstrap target, the statement carrier may name an arithmetic
object theory. The constant family is deliberate: the bootstrap index alone
does not manufacture a different theory. -/
abbrev ArithmeticTheoryByLevel : Nat → Type :=
  fun _targetLevel => Theory ℒₒᵣ

/-- A lower-consistency contract naming an arithmetic object theory. Its
external meaning is supplied separately below. -/
def consistencyContract {hostLevel : Nat} (targetLevel : Fin hostLevel)
    (T : Theory ℒₒᵣ) : LowerContract ArithmeticTheoryByLevel hostLevel where
  targetLevel := targetLevel
  kind := .lowerConsistency
  statement := T

/-- The external semantic reading of a lower-consistency contract. Other
contract kinds are deliberately unsupported by this meaning face. -/
def ExternalConsistencyMeaning {hostLevel : Nat}
    (claim : LowerContract ArithmeticTheoryByLevel hostLevel) : Prop :=
  match claim.kind with
  | .lowerConsistency => Consistent claim.statement
  | _ => False

@[simp] theorem consistencyContract_kind {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (T : Theory ℒₒᵣ) :
    (consistencyContract targetLevel T).kind = .lowerConsistency :=
  rfl

@[simp] theorem consistencyContract_meaning_iff {hostLevel : Nat}
    (targetLevel : Fin hostLevel) (T : Theory ℒₒᵣ) :
    ExternalConsistencyMeaning (consistencyContract targetLevel T) ↔
      Consistent T :=
  Iff.rfl

/-- Positive index fact: the numerical host/target discipline is available
for every arithmetic theory, independently of whether that theory is
consistent. -/
def levelOneConsistencyContract (T : Theory ℒₒᵣ) :
    LowerContract ArithmeticTheoryByLevel 1 :=
  consistencyContract ⟨0, by decide⟩ T

@[simp] theorem levelOneConsistencyContract_target (T : Theory ℒₒᵣ) :
    (levelOneConsistencyContract T).targetLevel.val = 0 :=
  rfl

/-- Raising the bootstrap host index retains the same object theory. -/
@[simp] theorem lift_preserves_object_theory (T : Theory ℒₒᵣ) :
    (levelOneConsistencyContract T).lift.statement = T :=
  rfl

/-- Consequently, lifting a contract also retains its external consistency
meaning; no proof-theoretic strength has been added by the index operation. -/
theorem lift_preserves_external_consistency_meaning (T : Theory ℒₒᵣ) :
    ExternalConsistencyMeaning (levelOneConsistencyContract T).lift ↔
      ExternalConsistencyMeaning (levelOneConsistencyContract T) :=
  Iff.rfl

variable (T : Theory ℒₒᵣ) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Foundation's actual proof-theoretic order can change while the bootstrap
host and target indices remain fixed. -/
theorem strict_object_theory_extension_at_fixed_bootstrap_index
    [Consistent T] :
    (levelOneConsistencyContract T).targetLevel =
        (levelOneConsistencyContract (T + T.Con)).targetLevel ∧
      T ⪱ T + T.Con := by
  exact ⟨rfl, inferInstance⟩

/-- At that fixed bootstrap index, second incompleteness separates the two
intrinsic proof authorities: `T` rejects every certificate for its own formal
consistency sentence, whereas `T + Con(T)` accepts an explicit one. -/
theorem certificate_acceptance_changes_with_object_theory_not_index
    [Consistent T] :
    (levelOneConsistencyContract T).targetLevel =
        (levelOneConsistencyContract (T + T.Con)).targetLevel ∧
      (¬ ∃ certificate : IntrinsicCertificate T,
        (IntrinsicCertificate.checker T).check
          (↑T.consistent) certificate = true) ∧
      ∃ certificate : IntrinsicCertificate (T + T.Con),
        (IntrinsicCertificate.checker (T + T.Con)).check
          (↑T.consistent) certificate = true := by
  exact ⟨rfl, no_self_consistency_certificate T,
    ⟨consistencyCertificateInExtension T,
      extension_accepts_consistency_certificate T⟩⟩

/-- External consistency cannot be made into a complete same-theory proof
authority for the formal consistency sentence. This is the authority-level
form of the distinction between semantic truth and internal provability. -/
def OwnFormalConsistencyMeaning (formula : Sentence ℒₒᵣ) : Prop :=
  formula = ↑T.consistent ∧ Consistent T

theorem intrinsic_checker_not_complete_for_own_consistency [Consistent T] :
    ¬ (IntrinsicCertificate.checker T).CertificateComplete
      (OwnFormalConsistencyMeaning T) := by
  intro complete
  obtain ⟨certificate, accepted⟩ := complete (↑T.consistent)
    ⟨rfl, inferInstance⟩
  exact no_self_consistency_certificate T ⟨certificate, accepted⟩

theorem intrinsic_checker_not_authority_for_own_consistency [Consistent T] :
    ¬ (IntrinsicCertificate.checker T).Authority
      (OwnFormalConsistencyMeaning T) := by
  intro authority
  exact intrinsic_checker_not_complete_for_own_consistency T
    authority.complete

end Mettapedia.Logic.Bridges.FoundationBootstrapIndexSeparation
