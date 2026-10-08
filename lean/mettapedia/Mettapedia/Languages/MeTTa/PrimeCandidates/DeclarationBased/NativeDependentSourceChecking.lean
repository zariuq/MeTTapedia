import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceWire
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerNumbersWeakHead

/-!
# Checking native source wires at a constructed signature

The entry point receives physical native input and expected-type wires. It
checks the fixed constructed declaration inventory, restores each source's
scope, then runs annotated weak-head checking. Acceptance gives an actual
annotated judgment in the independently constructed natural-number model.
Changing the declaration header, even while keeping the same term, refuses
this interpretation. This is a checked reference procedure; equivalence to
the native provider's whole C implementation is not asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceChecking

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open Mettapedia.TypeTheory.UniverseLevel
open NativeDependentSourceWire

variable (level : LevelExpr Nat)

/-- The actual model inventory, newest declaration first. Earlier entries
provide all names appearing in the type of the recursor. -/
def declarations : List (DeclName × ATm Tower.Head 0) :=
  [(TowerNumbersModel.numRec, ATm.ofTm (recType TowerNumbersModel.num (.sort level)
    TowerNumbersModel.ctors)),
   (TowerNumbersModel.succ, ATm.ofTm (ctorType TowerNumbersModel.num [.recursive])),
   (TowerNumbersModel.zero, ATm.ofTm (ctorType TowerNumbersModel.num [])),
   (TowerNumbersModel.num, .head TowerNumbersModel.u)]

/-- Lookup through the lowered declaration entries is exactly the constant
type function used by the semantic model and checking procedure. -/
theorem declarations_lookup (name : DeclName) :
    declarationsLookup (declarations level) name = (TowerNumbersModel.rules level).constantType name := by
  by_cases hN : name = TowerNumbersModel.num
  · subst name
    simp [declarations, declarationsLookup, TowerNumbersModel.rules, TowerNumbersModel.constantType,
      TowerNumbersModel.num_ne_numRec, TowerNumbersModel.num_ne_succ, TowerNumbersModel.num_ne_zero,
      ATm.erase]
  by_cases hZ : name = TowerNumbersModel.zero
  · subst name
    simp [declarations, declarationsLookup, TowerNumbersModel.rules, TowerNumbersModel.constantType,
      TowerNumbersModel.zero_ne_numRec, TowerNumbersModel.zero_ne_succ, hN]
  by_cases hS : name = TowerNumbersModel.succ
  · subst name
    simp [declarations, declarationsLookup, TowerNumbersModel.rules, TowerNumbersModel.constantType,
      TowerNumbersModel.succ_ne_numRec, hN, hZ]
  by_cases hR : name = TowerNumbersModel.numRec
  · subst name
    simp [declarations, declarationsLookup, TowerNumbersModel.rules, TowerNumbersModel.constantType,
      hN, hZ, hS]
  simp [declarations, declarationsLookup, TowerNumbersModel.rules, TowerNumbersModel.constantType,
    hN, hZ, hS, hR]

/-- Lowering must succeed before the header can be interpreted. -/
def accepts (budget n : Nat) (input expected : Wire) : Bool :=
  match lowerDeclarations (declarations level) with
  | none => false
  | some header => match decodeInputOver header n input, decodeScoped n expected with
      | some (context, term), some type =>
          ExecutableTowerNumbersWeakHead.acceptsSource level budget context term type
      | _, _ => false

theorem accepts_sound {budget n : Nat} {input expected : Wire}
    (accepted : accepts level budget n input expected = true) :
    ∃ header context term type,
      lowerDeclarations (declarations level) = some header ∧
      decodeInputOver header n input = some (context, term) ∧
      decodeScoped n expected = some type ∧
      ExecutableWrittenChecking.SourceContext.Formed (TowerNumbersModel.rules level) context ∧
      (∃ head, (TowerNumbersModel.rules level).isUniverse head ∧
        TypedEquality.ATyped (TowerNumbersModel.rules level) context.erase type (.head head)) ∧
      TypedEquality.ATyped (TowerNumbersModel.rules level) context.erase term type.erase := by
  unfold accepts at accepted
  cases hd : lowerDeclarations (declarations level) with
  | none => simp only [hd, Bool.false_eq_true] at accepted
  | some header =>
      cases hi : decodeInputOver header n input with
      | none => simp only [hd, hi] at accepted; cases accepted
      | some source =>
          cases ht : decodeScoped n expected with
          | none => simp only [hd, hi, ht] at accepted; cases accepted
          | some type =>
              simp only [hd, hi, ht] at accepted
              obtain ⟨formed, expectedFormation⟩ :=
                ExecutableTowerNumbersWeakHead.acceptsSource_formation level accepted
              exact ⟨header, source.1, source.2, type, rfl, hi, rfl,
                formed, expectedFormation,
                ExecutableTowerNumbersWeakHead.acceptsSource_sound level accepted⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceChecking
