import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayInterpretation

/-!
# The interpreted identity fibre of an accepted replay certificate

Principal-view extraction retains the actual identity former beneath result
wrappers. Both endpoints check at the same carrier present in the raw subject.
Their exact assembled values determine the resulting truth code. No semantic
coherence premise, erased-term reconstruction or equality reflection for an
arbitrary heterogeneous relation is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- Assembly follows the principal-view receipt exactly, including the case
where cumulative or conversion wrappers surround the identity former. -/
theorem assemble_identity_principalView (code : Code Head ConversionCode n)
    (A left right displayed : Tm Head n) (level : Head)
    (formation leftCode rightCode : Code Head ConversionCode n)
    (tail : ResultTail Head ConversionCode n)
    (computed : code.principalView displayed =
      some ⟨.head level, .idForm level formation leftCode rightCode, tail⟩) :
    assemble heads constants code (.id A left right) displayed = (do
      let a ← assemble heads constants leftCode left A
      let b ← assemble heads constants rightCode right A
      pure (.plain (fun env => truthCode (a.value env = b.value env)))) := by
  rw [assemble_principalView heads constants code computed (.id A left right)]
  rfl

/-- Successful assembly recovers the two actual endpoint meanings. The
principal receipt fixes both endpoint displayed types to the raw carrier. -/
theorem assemble_identity_endpoints (code : Code Head ConversionCode n)
    (A left right displayed : Tm Head n) (level : Head)
    (formation leftCode rightCode : Code Head ConversionCode n)
    (tail : ResultTail Head ConversionCode n) (result : Meaning.{u} n)
    (computed : code.principalView displayed =
      some ⟨.head level, .idForm level formation leftCode rightCode, tail⟩)
    (assembled : assemble heads constants code (.id A left right) displayed = some result) :
    ∃ a b, assemble heads constants leftCode left A = some a ∧
      assemble heads constants rightCode right A = some b ∧
      result = .plain (fun env => truthCode (a.value env = b.value env)) := by
  rw [assemble_identity_principalView heads constants code A left right displayed level
    formation leftCode rightCode tail computed] at assembled
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at assembled
  obtain ⟨a, atA, b, atB, equal⟩ := assembled
  exact ⟨a, b, atA, atB, equal.symm⟩

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- The original checker acceptance and the original assembly receipt jointly
recover exact checked endpoint certificates and the identity truth fibre.
This theorem applies in particular to the no-conversion cumulative profile. -/
theorem checked_identity_generation (code : Code Head ConversionCode n)
    {context : Ctx Head n} {A left right displayed : Tm Head n} (result : Meaning.{u} n)
    (accepted : check R conversionCheck context (.id A left right) displayed code = true)
    (assembled : assemble heads constants code (.id A left right) displayed = some result) :
    ∃ level formation leftCode rightCode tail a b,
      code.principalView displayed =
        some ⟨.head level, .idForm level formation leftCode rightCode, tail⟩ ∧
      tail.fill (.idForm level formation leftCode rightCode) = code ∧
      R.isUniverse level ∧ check R conversionCheck context A (.head level) formation = true ∧
      check R conversionCheck context left A leftCode = true ∧
      check R conversionCheck context right A rightCode = true ∧
      assemble heads constants leftCode left A = some a ∧
      assemble heads constants rightCode right A = some b ∧
      result = .plain (fun env => truthCode (a.value env = b.value env)) := by
  obtain ⟨level, formation, leftCode, rightCode, tail, computed, reconstructed,
    isUniverse, formationChecked, leftChecked, rightChecked⟩ :=
    code.identity_generation R conversionCheck accepted
  obtain ⟨a, b, atA, atB, value⟩ := assemble_identity_endpoints heads constants code
    A left right displayed level formation leftCode rightCode tail result computed assembled
  exact ⟨level, formation, leftCode, rightCode, tail, a, b, computed, reconstructed,
    isUniverse, formationChecked, leftChecked, rightChecked, atA, atB, value⟩

/-- An accepted identity formation needs no separately assumed assembly
receipt: totality of the existing assembly algorithm supplies it. -/
theorem accepted_identity_assembles (code : Code Head ConversionCode n)
    {context : Ctx Head n} {A left right displayed : Tm Head n}
    (accepted : check R conversionCheck context (.id A left right) displayed code = true) :
    ∃ level formation leftCode rightCode tail a b,
      code.principalView displayed =
        some ⟨.head level, .idForm level formation leftCode rightCode, tail⟩ ∧
      tail.fill (.idForm level formation leftCode rightCode) = code ∧
      R.isUniverse level ∧ check R conversionCheck context A (.head level) formation = true ∧
      check R conversionCheck context left A leftCode = true ∧
      check R conversionCheck context right A rightCode = true ∧
      assemble heads constants leftCode left A = some a ∧
      assemble heads constants rightCode right A = some b ∧
      assemble heads constants code (.id A left right) displayed =
        some (.plain (fun env => truthCode (a.value env = b.value env))) := by
  obtain ⟨result, assembled, _⟩ := accepted_assembles heads constants R conversionCheck code accepted
  obtain ⟨level, formation, leftCode, rightCode, tail, a, b, computed, reconstructed,
    isUniverse, formationChecked, leftChecked, rightChecked, atA, atB, value⟩ :=
    checked_identity_generation heads constants R conversionCheck code result accepted assembled
  exact ⟨level, formation, leftCode, rightCode, tail, a, b, computed, reconstructed,
    isUniverse, formationChecked, leftChecked, rightChecked, atA, atB, value ▸ assembled⟩

/-- Membership in an accepted identity fibre forces equality of the two
meanings extracted from its actual, same-carrier endpoint certificates. -/
theorem checked_identity_membership (code : Code Head ConversionCode n)
    {context : Ctx Head n} {A left right displayed : Tm Head n} (result : Meaning.{u} n)
    (accepted : check R conversionCheck context (.id A left right) displayed code = true)
    (assembled : assemble heads constants code (.id A left right) displayed = some result)
    (env : Environment.{u} n) (witness : ZFSet.{u}) :
    ∃ leftCode rightCode a b,
      check R conversionCheck context left A leftCode = true ∧
      check R conversionCheck context right A rightCode = true ∧
      assemble heads constants leftCode left A = some a ∧
      assemble heads constants rightCode right A = some b ∧
      (witness ∈ result.value env ↔ witness = ∅ ∧ a.value env = b.value env) := by
  obtain ⟨_, _, leftCode, rightCode, _, a, b, _, _, _, _, leftChecked, rightChecked,
    atA, atB, value⟩ :=
    checked_identity_generation heads constants R conversionCheck code result accepted assembled
  refine ⟨leftCode, rightCode, a, b, leftChecked, rightChecked, atA, atB, ?_⟩
  rw [value]
  exact mem_truthCode _ _

#print axioms assemble_identity_principalView
#print axioms assemble_identity_endpoints
#print axioms checked_identity_generation
#print axioms accepted_identity_assembles
#print axioms checked_identity_membership

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
