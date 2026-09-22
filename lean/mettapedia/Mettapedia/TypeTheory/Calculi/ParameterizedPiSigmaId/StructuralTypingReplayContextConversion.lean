import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution

/-!
# Executable context conversion of typing certificates

Changing the newest binder to a convertible type acts on the complete
supplied replay tree by the existing substitution algorithm. Its newest
variable image is an explicit cast to the independently formed old type;
older images remain variables. In particular, nested binding and conversion
premises use the same capture-avoiding action as ordinary substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {ConversionCode : Nat → Type}
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)

def newestImageCodes {n : Nat} (new : Tm Head n) (level : Head)
    (oldFormation : Code Head ConversionCode n) (backwards : ConversionCode n) :
    Fin (n + 1) → Code Head ConversionCode (n + 1) :=
  Fin.cases (.convert (rename wk new) level .var
    (oldFormation.rename renameConversion wk) (renameConversion wk backwards)) (fun _ => .var)

def Code.convertNewest {n : Nat} (new : Tm Head n) (level : Head)
    (oldFormation : Code Head ConversionCode n) (backwards : ConversionCode n)
    (subject type : Tm Head (n + 1)) (code : Code Head ConversionCode (n + 1)) :
    Code Head ConversionCode (n + 1) :=
  code.substitute renameConversion substituteConversion ids
    (newestImageCodes renameConversion new level oldFormation backwards) subject type

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)]
variable [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)]
variable [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (renamePreserves : ∀ {n m} (ρ : Ren n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (renameConversion ρ code) (Presentation.rename ρ left) (Presentation.rename ρ right) = true)
variable (substitutePreserves : ∀ {n m} (σ : Sub Head n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (substituteConversion σ code) (subst σ left) (subst σ right) = true)

include renamePreserves in
theorem newestImageCodes_checked {n : Nat} {context : Ctx Head n} {old new : Tm Head n}
    {level : Head} {oldFormation : Code Head ConversionCode n} {backwards : ConversionCode n}
    (formed : check R conversionCheck context old (.head level) oldFormation = true)
    (isUniverse : R.isUniverse level) (converted : conversionCheck backwards new old = true)
    (index : Fin (n + 1)) :
    check R conversionCheck (.snoc context new) (ids index)
      (subst ids (Ctx.lookup (.snoc context old) index))
      (newestImageCodes renameConversion new level oldFormation backwards index) = true := by
  rw [subst_ids]
  refine Fin.cases ?_ (fun index => ?_) index
  · have formation := check_rename renameConversion R conversionCheck renamePreserves oldFormation formed
        (target := .snoc context new) (rho := wk) (fun _ => rfl)
    have conversion := renamePreserves wk backwards converted
    simp only [newestImageCodes, Fin.cases_zero, ids, check, Ctx.lookup_snoc_zero,
      decide_true, Bool.and_eq_true]
    exact ⟨⟨⟨decide_eq_true isUniverse, True.intro⟩, formation⟩, conversion⟩
  · simp only [newestImageCodes, Fin.cases_succ, ids, check, Ctx.lookup_snoc_succ, decide_true]

include renamePreserves substitutePreserves in
theorem Code.convertNewest_checked {n : Nat} {context : Ctx Head n} {old new : Tm Head n}
    {level : Head} {oldFormation : Code Head ConversionCode n} {backwards : ConversionCode n}
    {subject type : Tm Head (n + 1)} {code : Code Head ConversionCode (n + 1)}
    (formed : check R conversionCheck context old (.head level) oldFormation = true)
    (isUniverse : R.isUniverse level) (converted : conversionCheck backwards new old = true)
    (accepted : check R conversionCheck (.snoc context old) subject type code = true) :
    check R conversionCheck (.snoc context new) subject type
      (Code.convertNewest renameConversion substituteConversion new level oldFormation backwards
        subject type code) = true := by
  simpa only [Code.convertNewest, subst_ids] using check_substitute renameConversion substituteConversion R conversionCheck
    renamePreserves substitutePreserves code accepted ids
    (newestImageCodes renameConversion new level oldFormation backwards)
    (newestImageCodes_checked renameConversion R conversionCheck renamePreserves formed isUniverse converted)

#print axioms newestImageCodes_checked
#print axioms Code.convertNewest_checked

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
