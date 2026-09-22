import Mettapedia.TypeTheory.FamilyEnclosingUniverseTower
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Function.Basic

/-!
# Full dependent closure prohibits semantic universe self-coding

A Tarski level closed under full dependent products and sums, and containing
a Boolean type, cannot also code its own code carrier. A hypothetical self-code
would let Sigma form the total decoded carrier. Pi would then represent its
Boolean-valued function space, injecting that function space back into the
total carrier, in contradiction with Cantor's theorem.

This derives semantic rank separation from existing closure operations; it
does not store rank separation as an extra assumption. The result applies to
the full ambient-function and dependent-sum meanings in PiClosedAt and
SigmaClosedAt. It is not a theorem about restricted Henkin function domains,
nor a consistency or existence proof for any universe-forming operator.

The actual family-enclosing envelopes have a Boolean code: their sum of two
unit codes. Hence the conditionally constructed unbounded tower has derived
predicative ranks. The independently supplied small operator remains an
existence assumption; no runtime operation or host profile is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TarskiClosureRankObstruction

open TarskiUniverseCapabilities FamilyEnclosingUniverse UniverseClosureProfiles

universe uLevel uCode uEl u

/-- Cantor's obstruction uses only these actual full closure capabilities and
one Boolean decoding. No injectivity of the universe's code constructors is
required. -/
theorem no_selfCode_of_pi_sigma_bool
    (family : TarskiCodeFamily.{uLevel, uCode, uEl}) (level : family.Level)
    (products : family.PiClosedAt level) (sums : family.SigmaClosedAt level)
    (boolean : family.Code level) (decodeBoolean : family.El level boolean ≃ Bool) :
    ¬ family.CodesItselfAt level := by
  rintro ⟨selfCode, ⟨decodeSelf⟩⟩
  obtain ⟨totalCode, ⟨decodeTotal⟩⟩ := sums selfCode (fun index => decodeSelf index)
  let totalEquiv : family.El level totalCode ≃ Sigma (family.El level) :=
    decodeTotal.trans (Equiv.sigmaCongrLeft decodeSelf)
  obtain ⟨functionCode, ⟨decodeFunction⟩⟩ := products totalCode (fun _ => boolean)
  let functionEquiv :
      family.El level functionCode ≃ (family.El level totalCode → Bool) :=
    decodeFunction.trans (Equiv.piCongrRight fun _ => decodeBoolean)
  let injectFunctions :
      (family.El level totalCode → Bool) ↪ family.El level totalCode :=
    (functionEquiv.symm.toEmbedding.trans (Function.Embedding.sigmaMk functionCode)).trans
      totalEquiv.symm.toEmbedding
  let subsets : Set (family.El level totalCode) ≃ (family.El level totalCode → Bool) :=
    Equiv.piCongrRight fun _ => Equiv.propEquivBool
  exact Function.cantor_injective (injectFunctions ∘ subsets)
    (injectFunctions.injective.comp subsets.injective)

/-- The local obstruction yields rank separation at every level. -/
theorem predicativeRanks_of_pi_sigma_bool
    (family : TarskiCodeFamily.{uLevel, uCode, uEl})
    (products : family.PiClosed) (sums : family.SigmaClosed)
    (booleans : ∀ level, ∃ code : family.Code level, Nonempty (family.El level code ≃ Bool)) :
    family.PredicativeRanks := by
  intro level
  obtain ⟨boolean, ⟨decodeBoolean⟩⟩ := booleans level
  exact no_selfCode_of_pi_sigma_bool family level (products level) (sums level)
    boolean decodeBoolean

/-- A Boolean-bearing self-code has a concrete consequence: at least one of
these full closure claims must fail. It is not merely a disagreement about
the names of universe levels. -/
theorem selfCode_forces_failed_closure
    (family : TarskiCodeFamily.{uLevel, uCode, uEl}) (level : family.Level)
    (boolean : family.Code level) (decodeBoolean : family.El level boolean ≃ Bool)
    (selfCode : family.CodesItselfAt level) :
    ¬ (family.PiClosedAt level ∧ family.SigmaClosedAt level) := by
  rintro ⟨products, sums⟩
  exact no_selfCode_of_pi_sigma_bool family level products sums boolean decodeBoolean selfCode

/-! ## The existing family-enclosing operations supply all premises -/

variable {A : Type uEl} {B : A → Type uEl}

/-- Use the actual declared sum constructor, not a newly assumed Boolean
operation. The resulting code belongs to the original envelope. -/
def envelopeBooleanCode (envelope : ClosedTarskiUniverseOver.{uCode, uEl} A B) : envelope.Code :=
  envelope.sumCode envelope.unitCode envelope.unitCode

def decodeEnvelopeBoolean (envelope : ClosedTarskiUniverseOver.{uCode, uEl} A B) :
    envelope.El (envelopeBooleanCode envelope) ≃ Bool :=
  (envelope.elSum envelope.unitCode envelope.unitCode).trans
    ((Equiv.sumCongr envelope.elUnit envelope.elUnit).trans
      Equiv.boolEquivPUnitSumPUnit.symm)

/-- Full envelopes are predicatively ranked even when their code carrier
and decoded types inhabit the same ambient Lean universe. -/
theorem envelope_predicativeRanks
    (envelope : ClosedTarskiUniverseOver.{uCode, uEl} A B) :
    envelope.toCodeFamily.PredicativeRanks := by
  intro level
  cases level
  exact no_selfCode_of_pi_sigma_bool envelope.toCodeFamily PUnit.unit
    envelope.piClosedAt envelope.sigmaClosedAt
    (envelopeBooleanCode envelope) (decodeEnvelopeBoolean envelope)

/-- In particular, a closed envelope cannot represent its own actual code
carrier by any of its decoded types. -/
theorem envelope_no_selfCode
    (envelope : ClosedTarskiUniverseOver.{uCode, uEl} A B) :
    ¬ ∃ code : envelope.Code, Nonempty (envelope.El code ≃ envelope.Code) :=
  envelope_predicativeRanks envelope PUnit.unit

/-- The unbounded tower's rank separation is derived, not an additional
operator field. The small enclosing operator is still independently supplied. -/
theorem tower_predicativeRanks
    (operator : SmallFamilyEnclosingUniverseOperator.{u})
    (A : Type u) (B : A → Type u) :
    (FamilyEnclosingUniverseTower.family operator A B).PredicativeRanks := by
  intro level
  exact envelope_no_selfCode (FamilyEnclosingUniverseTower.envelope operator A B level)

/-! ## Scope controls -/

/-- The concrete nonconstant ambient envelope has full closure and derived
rank separation. The source family still has inequivalent fibres. This
control does not claim an inhabitant of the small-operator interface. -/
theorem varying_envelope_scope_control :
    varyingEnvelope.toCodeFamily.PiClosedAt PUnit.unit ∧
      varyingEnvelope.toCodeFamily.SigmaClosedAt PUnit.unit ∧
      Nonempty (varyingEnvelope.El (envelopeBooleanCode varyingEnvelope) ≃ Bool) ∧
      varyingEnvelope.toCodeFamily.PredicativeRanks ∧
      ¬ Nonempty (varyingEnvelope.El (varyingEnvelope.fibreCode false) ≃
        varyingEnvelope.El (varyingEnvelope.fibreCode true)) :=
  ⟨varyingEnvelope.piClosedAt, varyingEnvelope.sigmaClosedAt,
    ⟨decodeEnvelopeBoolean varyingEnvelope⟩, envelope_predicativeRanks varyingEnvelope,
    varyingEnvelope_fibres_distinct⟩

/-- The existing singleton self-code control pinpoints the Boolean premise:
its full products and sums cannot contain a Boolean type. It is only a
counterexample to dropping that premise, not a universe model for the native
language. -/
theorem singleton_selfCode_has_no_boolean :
    ¬ ∃ boolean : UnitClosed.family.Code PUnit.unit,
      Nonempty (UnitClosed.family.El PUnit.unit boolean ≃ Bool) := by
  rintro ⟨boolean, ⟨decodeBoolean⟩⟩
  exact no_selfCode_of_pi_sigma_bool UnitClosed.family PUnit.unit
    (UnitClosed.piClosed PUnit.unit) (UnitClosed.sigmaClosed PUnit.unit)
    boolean decodeBoolean UnitClosed.codesItself

/-- Conversely, predicative ranks alone still do not provide products; the
existing finite-rank family's concrete function-space obstruction remains. -/
theorem ranks_do_not_supply_products :
    FiniteRank.family.PredicativeRanks ∧ ¬ FiniteRank.family.PiClosedAt 3 :=
  ⟨FiniteRank.predicativeRanks, FiniteRank.not_piClosedAt_three⟩

#print axioms no_selfCode_of_pi_sigma_bool
#print axioms predicativeRanks_of_pi_sigma_bool
#print axioms selfCode_forces_failed_closure
#print axioms decodeEnvelopeBoolean
#print axioms envelope_predicativeRanks
#print axioms envelope_no_selfCode
#print axioms tower_predicativeRanks
#print axioms varying_envelope_scope_control
#print axioms singleton_selfCode_has_no_boolean
#print axioms ranks_do_not_supply_products

end Mettapedia.TypeTheory.TarskiClosureRankObstruction
