import Mettapedia.TypeTheory.Calculi.NativeDependent.EquationInitiality
import Mettapedia.TypeTheory.Calculi.NativeDependent.Controls

/-!
# Exact quotient computation and retained declaration origins

The beta-qualified initial rule model computes in the actual native
Fin (n + 1) family. Generated beta identifies application with explicit
instantiation while retaining primitive declarations with equal values
as distinct origin-bearing certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.EquationControls

open Controls RuleInitiality EquationInitiality PresheafInterpretation

abbrev boundedClass (number : Nat) (origin : Bool) :
    JudgmentEquationInitiality.Presented (equations Primitive)
      ⟨0, .substitute input (ObjectSubstitution.instantiate (.constant number))⟩ :=
  Quotient.mk _ (encode Primitive (Proof.declaration (Primitive.closed number origin)))

theorem application_class_beta (number : Nat) :
    (Quotient.mk (JudgmentEquationInitiality.derivationSetoid (equations Primitive)
      ⟨0, .substitute input (ObjectSubstitution.instantiate (.constant number))⟩)
        (encode Primitive (applicationProof number))) =
    Quotient.mk _ (encode Primitive
      (Proof.substitute (Proof.declaration Primitive.boundedInput)
        (ObjectSubstitution.instantiate (.constant number)))) := by
  apply Quotient.sound
  exact proofEquation_generated Primitive (.beta (.declaration Primitive.boundedInput) (.constant number))

theorem initial_application_computes (number : Nat) :
    ((nativeEvaluation Primitive objects constants predicates declarations).map
      (Quotient.mk _ (encode Primitive (applicationProof number)))).val testPoint =
        (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) := by
  rw [nativeEvaluation_encode]
  exact application_computes number

theorem distinct_origins_survive (number : Nat) :
    boundedClass number false ≠ boundedClass number true := by
  intro same
  have origins := declaration_quotient_injective Primitive same
  cases origins

/-- The actual native result forgets an origin that the initial quotient
retains. Equality of interpreted values is therefore not presentation equality. -/
theorem native_values_do_not_separate_origins (number : Nat) :
    (nativeEvaluation Primitive objects constants predicates declarations).map
      (boundedClass number false) =
    (nativeEvaluation Primitive objects constants predicates declarations).map
      (boundedClass number true) := by
  change (nativeEvaluation Primitive objects constants predicates declarations).map
      (Quotient.mk _ (encode Primitive (Proof.declaration (Primitive.closed number false)))) =
    (nativeEvaluation Primitive objects constants predicates declarations).map
      (Quotient.mk _ (encode Primitive (Proof.declaration (Primitive.closed number true))))
  rw [nativeEvaluation_encode, nativeEvaluation_encode]
  exact declaration_values_agree number

end Mettapedia.TypeTheory.Calculi.NativeDependent.EquationControls
