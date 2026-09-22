import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution

/-!
# Substitution of finite structural conversion certificates

The actual finite code is transformed recursively, preserving its selected
structural constructors and composition tree. Beneath a binder the existing
capture-avoiding substitution is lifted. Root-code substitution is an
explicit parameter, with its decoder and action laws supplied separately.

Accepted codes remain accepted at substituted endpoints. Rejected joins need
not remain rejected: a substitution can identify their different middle
terms. No certificate is reconstructed using existential completeness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionCode

variable {Head : Type} {RootCode : Nat → Type}
variable (substituteRoot : {n m : Nat} → Sub Head n m → RootCode n → RootCode m)

namespace StepCode

def substitute {n m : Nat} (σ : Sub Head n m) : StepCode Head RootCode n → StepCode Head RootCode m
  | .betaPi body argument => .betaPi (subst (liftSub σ) body) (subst σ argument)
  | .betaSigmaFst first second => .betaSigmaFst (subst σ first) (subst σ second)
  | .betaSigmaSnd first second => .betaSigmaSnd (subst σ first) (subst σ second)
  | .head left right => .head left right
  | .root code => .root (substituteRoot σ code)
  | .congPiDom code codomain => .congPiDom (code.substitute σ) (subst (liftSub σ) codomain)
  | .congPiCod domain code => .congPiCod (subst σ domain) (code.substitute (liftSub σ))
  | .congSigmaDom code codomain => .congSigmaDom (code.substitute σ) (subst (liftSub σ) codomain)
  | .congSigmaCod domain code => .congSigmaCod (subst σ domain) (code.substitute (liftSub σ))
  | .congIdTy code left right => .congIdTy (code.substitute σ) (subst σ left) (subst σ right)
  | .congIdLeft type code right => .congIdLeft (subst σ type) (code.substitute σ) (subst σ right)
  | .congIdRight type left code => .congIdRight (subst σ type) (subst σ left) (code.substitute σ)
  | .congLam code => .congLam (code.substitute (liftSub σ))
  | .congAppFun code argument => .congAppFun (code.substitute σ) (subst σ argument)
  | .congAppArg function code => .congAppArg (subst σ function) (code.substitute σ)
  | .congPairFst code second => .congPairFst (code.substitute σ) (subst σ second)
  | .congPairSnd first code => .congPairSnd (subst σ first) (code.substitute σ)
  | .congFst code => .congFst (code.substitute σ)
  | .congSnd code => .congSnd (code.substitute σ)
  | .congRefl code => .congRefl (code.substitute σ)

theorem substitute_ids (rootId : ∀ {n : Nat} (code : RootCode n), substituteRoot ids code = code)
    {n : Nat} (code : StepCode Head RootCode n) :
    code.substitute substituteRoot ids = code := by
  induction code <;> simp_all only [substitute, liftSub_ids, subst_ids]

theorem substitute_comp
    (rootComp : ∀ {n m k : Nat} (σ : Sub Head n m) (τ : Sub Head m k) (code : RootCode n),
      substituteRoot τ (substituteRoot σ code) = substituteRoot (subComp τ σ) code)
    {n m k : Nat} (σ : Sub Head n m) (τ : Sub Head m k) (code : StepCode Head RootCode n) :
    (code.substitute substituteRoot σ).substitute substituteRoot τ =
      code.substitute substituteRoot (subComp τ σ) := by
  induction code generalizing m k <;>
    simp_all only [substitute, subst_subComp, liftSub_subComp]

variable (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

/-- The root decoder's substitution square propagates through every
structural congruence position, including dependent codomains. -/
theorem decode_substitute
    (rootNatural : ∀ {n m : Nat} (σ : Sub Head n m) (code : RootCode n),
      decodeRoot (substituteRoot σ code) = mapEndpoints (subst σ) (decodeRoot code))
    {n m : Nat} (σ : Sub Head n m) (code : StepCode Head RootCode n) :
    decode headEq decodeRoot (code.substitute substituteRoot σ) =
      mapEndpoints (subst σ) (decode headEq decodeRoot code) := by
  induction code generalizing m <;>
    simp_all only [substitute, decode, mapEndpoints, Option.map_some,
      Option.map_map, Function.comp_def, subst, subst_inst0]
  case head left right => split <;> rfl

end StepCode

namespace Code

def substitute {n m : Nat} (σ : Sub Head n m) : Code Head RootCode n → Code Head RootCode m
  | .single step => .single (step.substitute substituteRoot σ)
  | .refl term => .refl (subst σ term)
  | .symm code => .symm (code.substitute σ)
  | .trans first second => .trans (first.substitute σ) (second.substitute σ)

theorem substitute_ids (rootId : ∀ {n : Nat} (code : RootCode n), substituteRoot ids code = code)
    {n : Nat} (code : Code Head RootCode n) : code.substitute substituteRoot ids = code := by
  induction code <;> simp_all only [substitute, StepCode.substitute_ids substituteRoot rootId, subst_ids]

theorem substitute_comp
    (rootComp : ∀ {n m k : Nat} (σ : Sub Head n m) (τ : Sub Head m k) (code : RootCode n),
      substituteRoot τ (substituteRoot σ code) = substituteRoot (subComp τ σ) code)
    {n m k : Nat} (σ : Sub Head n m) (τ : Sub Head m k) (code : Code Head RootCode n) :
    (code.substitute substituteRoot σ).substitute substituteRoot τ =
      code.substitute substituteRoot (subComp τ σ) := by
  induction code <;>
    simp_all only [substitute, StepCode.substitute_comp substituteRoot rootComp, subst_subComp]

variable [DecidableEq Head] (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

/-- Forward preservation retains this transformed certificate. A rejected
join may be repaired by identifying substitutions, so no converse is assumed. -/
theorem decode_substitute_of_some
    (rootNatural : ∀ {n m : Nat} (σ : Sub Head n m) (code : RootCode n),
      decodeRoot (substituteRoot σ code) = mapEndpoints (subst σ) (decodeRoot code))
    {n m : Nat} (σ : Sub Head n m) (code : Code Head RootCode n)
    {left right : Tm Head n} (decoded : decode headEq decodeRoot code = some (left, right)) :
    decode headEq decodeRoot (code.substitute substituteRoot σ) = some (subst σ left, subst σ right) := by
  induction code generalizing left right with
  | single step =>
      simp only [decode] at decoded
      simpa only [substitute, decode, decoded, mapEndpoints, Option.map_some] using
        StepCode.decode_substitute substituteRoot headEq decodeRoot rootNatural σ step
  | refl term =>
      cases Option.some.inj decoded
      rfl
  | symm code ih =>
      cases prior : decode headEq decodeRoot code with
      | none => simp [decode, prior, reverseEndpoints] at decoded
      | some endpoints =>
          rcases endpoints with ⟨a, b⟩
          simp only [decode, prior, reverseEndpoints, Option.map_some] at decoded
          have same : (b, a) = (left, right) := Option.some.inj decoded
          cases same
          simp only [substitute, decode, ih prior, reverseEndpoints, Option.map_some]
  | trans first second ihFirst ihSecond =>
      cases firstResult : decode headEq decodeRoot first with
      | none => simp [decode, firstResult, joinEndpoints] at decoded
      | some firstPair =>
          rcases firstPair with ⟨a, middle⟩
          cases secondResult : decode headEq decodeRoot second with
          | none => simp [decode, firstResult, secondResult, joinEndpoints] at decoded
          | some secondPair =>
              rcases secondPair with ⟨middle', b⟩
              simp only [decode, firstResult, secondResult, joinEndpoints] at decoded
              split at decoded
              · rename_i same
                subst middle'
                cases Option.some.inj decoded
                simp only [substitute, decode, ihFirst firstResult, ihSecond secondResult,
                  joinEndpoints, ↓reduceIte]
              · cases decoded

theorem check_substitute
    (rootNatural : ∀ {n m : Nat} (σ : Sub Head n m) (code : RootCode n),
      decodeRoot (substituteRoot σ code) = mapEndpoints (subst σ) (decodeRoot code))
    {n m : Nat} (σ : Sub Head n m) (code : Code Head RootCode n)
    {left right : Tm Head n} (accepted : check headEq decodeRoot code left right = true) :
    check headEq decodeRoot (code.substitute substituteRoot σ) (subst σ left) (subst σ right) = true := by
  apply decide_eq_true
  exact decode_substitute_of_some substituteRoot headEq decodeRoot rootNatural σ code
    (of_decide_eq_true accepted)

end Code

#print axioms StepCode.decode_substitute
#print axioms Code.substitute_ids
#print axioms Code.substitute_comp
#print axioms Code.check_substitute

end StructuralConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
