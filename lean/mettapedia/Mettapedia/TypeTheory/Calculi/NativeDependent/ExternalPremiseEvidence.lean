import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalHeaderFormation

/-!
# Constructive ordered evidence for external rule premises

The evidence list is indexed by the actual authored premise judgments. Its
position lookup eliminates the finite index as data, preserving proof-relevant
derivations without eliminating a proposition into a type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

universe u

variable {S : Symbols.{u}} {D : Signature S}

inductive PremiseEvidence (D : Signature S) : List (Judgment S) → Type u where
  | nil : PremiseEvidence D []
  | cons {judgment : Judgment S} {later : List (Judgment S)}
      (first : Derivation D judgment) (rest : PremiseEvidence D later) :
      PremiseEvidence D (judgment :: later)

def PremiseEvidence.at : {judgments : List (Judgment S)} → PremiseEvidence D judgments →
    (position : Fin judgments.length) → Derivation D (judgments.get position)
  | _, .nil, position => Fin.elim0 position
  | _, .cons first rest, position => Fin.cases first (fun prior => rest.at prior) position

def deriveList (rule : RuleCode D) (premises : PremiseEvidence D rule.premises) :
    Derivation D rule.conclusion := derive rule premises.at

def PremiseEvidence.before (bound : Nat) : {judgments : List (Judgment S)} →
    PremiseEvidence D judgments → Prop
  | _, .nil => True
  | _, .cons first rest => first.before bound ∧ rest.before bound

theorem PremiseEvidence.before_iff_at (bound : Nat) : ∀ {judgments : List (Judgment S)}
    (premises : PremiseEvidence D judgments),
    premises.before bound ↔ ∀ position, (premises.at position).before bound
  | _, .nil => by
      constructor
      · intro _ position; exact Fin.elim0 position
      · intro _; trivial
  | _, .cons first rest => by
      constructor
      · intro bounded position
        cases position using Fin.cases with
        | zero => exact bounded.1
        | succ position => exact (rest.before_iff_at bound).mp bounded.2 position
      · intro bounded
        exact ⟨bounded 0, (rest.before_iff_at bound).mpr (fun position => bounded position.succ)⟩

@[simp] theorem deriveList_before_iff (bound : Nat) (rule : RuleCode D)
    (premises : PremiseEvidence D rule.premises) :
    (deriveList rule premises).before bound ↔
      rule.conclusion.before D bound ∧ premises.before bound := by
  change (_ ∧ ∀ position : ULift (Fin rule.premises.length),
    Derivation.before bound (premises.at position.down)) ↔ _
  rw [premises.before_iff_at]
  constructor
  · intro bounded; exact ⟨bounded.1, fun position => bounded.2 ⟨position⟩⟩
  · intro bounded; exact ⟨bounded.1, fun position => bounded.2 position.down⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
