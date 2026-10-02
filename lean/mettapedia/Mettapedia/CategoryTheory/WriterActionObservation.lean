import Mettapedia.CategoryTheory.WriterActionAdjunction
import Mathlib.Logic.Function.Basic

/-!
# Observations preserved by account actions

An observation on a free monoid action is invariant exactly when it factors
through account erasure.  Equivariant extension preserves such an observation
whenever the target action preserves it and the generator map agrees with it.
Thus multiplication can forget an account boundary while retaining an immutable
observation of the generator.

These are fixed-carrier account models.  The generator observation is not the
canonical key of an entire accounted syntax tree; no invariance under binding,
substitution, resource authorization, or authored Cost transformation is claimed.
-/

open CategoryTheory
open Mettapedia.CategoryTheory.WriterActionAdjunction

namespace Mettapedia.CategoryTheory.WriterActionObservation

set_option autoImplicit false

universe u v

variable (M : Type u) [Monoid M]

/-- The chosen observation does not change under the given account action. -/
def Invariant (target : Action (Type u) M) {O : Type v}
    (observe : target.V → O) : Prop :=
  ∀ account value, observe ((target.ρ account) value) = observe value

/-- Invariance on the free action is precisely dependence on its generator. -/
theorem free_invariant_iff_factorsThrough {X : Type u} {O : Type v}
    (observe : M × X → O) :
    Invariant M (freeObject M X) observe ↔
      Function.FactorsThrough observe (Prod.snd : M × X → X) := by
  constructor
  · intro invariant left right sameValue
    have atGenerator (pair : M × X) : observe pair = observe (1, pair.2) := by
      have acted := invariant pair.1 (1, pair.2)
      change observe (pair.1 * 1, pair.2) = observe (1, pair.2) at acted
      simpa only [mul_one] using acted
    rw [atGenerator left, atGenerator right, sameValue]
  · intro supported account pair
    exact supported rfl

/-- The factor is explicitly obtained by observing the unit-account generator;
no choice of values outside the image is needed. -/
theorem free_observation_eq_comp_erase {X : Type u} {O : Type v}
    (observe : M × X → O)
    (invariant : Invariant M (freeObject M X) observe) :
    observe = (fun value => observe (1, value)) ∘ (eraseAccount M).app X := by
  funext pair
  exact (free_invariant_iff_factorsThrough M observe).mp invariant rfl

/-- Any invariant observation of an independent target action is respected by
the free extension of a generator map that respects that observation. -/
theorem extend_preserves_observation {X : Type u} {O : Type v}
    (target : Action (Type u) M) (observe : target.V → O)
    (invariant : Invariant M target observe) (key : X → O)
    (generator : X ⟶ target.V)
    (onGenerators : ∀ value, observe (generator value) = key value)
    (pair : M × X) :
    observe ((extend M target generator).hom pair) = key pair.2 := by
  exact (invariant pair.1 (generator pair.2)).trans (onGenerators pair.2)

/-- Every generator observation yields an actual equivariant map from the free
action to an observation carrier on which accounts act trivially. -/
def payloadObservation {X K : Type u} (key : X → K) :
    freeObject M X ⟶ Action.trivial M K where
  hom := TypeCat.ofHom fun pair => key pair.2
  comm := fun _ => by ext pair; rfl

/-- The concrete equivariant observation retains precisely the supplied key on
unit-account generators. -/
@[simp]
theorem payloadObservation_restrict {X K : Type u} (key : X → K) :
    restrict M (payloadObservation M key) = TypeCat.ofHom key := rfl

/-- Arbitrary account changes preserve a fixed generator key. -/
theorem payload_invariant {X : Type u} {K : Type v} (key : X → K) :
    Invariant M (freeObject M X) (fun pair => key pair.2) := by
  intro account pair
  rfl

/-- The genuine multiplication induced by the action adjunction retains the
generator key while multiplying its two account coordinates. -/
theorem multiplication_preserves_payload {X : Type u} {K : Type v}
    (key : X → K) (nested : M × (M × X)) :
    key (((writerMonad M).μ.app X nested).2) = key nested.2.2 := rfl

/-- Noninjective multiplication and preservation of a chosen generator key
hold together on a free account object containing an actual generator. -/
theorem noninjective_multiplication_preserves_payload [Nontrivial M]
    {X : Type u} {K : Type v} (value : X) (key : X → K) :
    ¬ Function.Injective ((writerMonad M).μ.app X) ∧
      ∀ nested : M × (M × X),
        key (((writerMonad M).μ.app X nested).2) = key nested.2.2 :=
  ⟨multiplication_not_injective M value, multiplication_preserves_payload M key⟩

/-- Remembering the outer account detects a boundary that multiplication loses.
This observation therefore cannot be recovered from the flattened account. -/
theorem outerAccount_not_factorsThrough_multiplication [Nontrivial M]
    {X : Type u} (value : X) :
    ¬ Function.FactorsThrough (Prod.fst : M × (M × X) → M)
      ((writerMonad M).μ.app X) := by
  intro supported
  obtain ⟨account, account_ne⟩ := exists_ne (1 : M)
  have sameFlattened :
      (writerMonad M).μ.app X (1, (account, value)) =
        (writerMonad M).μ.app X (account, (1, value)) := by
    change (1 * account, value) = (account * 1, value)
    rw [one_mul, mul_one]
  exact account_ne (supported sameFlattened).symm

#print axioms free_invariant_iff_factorsThrough
#print axioms extend_preserves_observation
#print axioms payloadObservation
#print axioms noninjective_multiplication_preserves_payload
#print axioms outerAccount_not_factorsThrough_multiplication

end Mettapedia.CategoryTheory.WriterActionObservation
