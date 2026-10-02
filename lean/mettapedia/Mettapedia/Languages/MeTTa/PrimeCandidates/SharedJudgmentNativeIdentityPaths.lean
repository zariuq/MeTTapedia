import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentIdentityRegions

/-!
# Native identity paths derived from the existing J declaration

Inversion, composition and cancellation below are actual object-language
proof terms. Their typing is constructed in the formation-sensitive native
judgment; no external route-family eliminator or new identity axiom is used.
The element and motive levels of J are instantiated at the same supplied
universe level. None of these propositional laws adds a conversion rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityPaths

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic
open FormationSensitiveBasedIdentity (doubleWeaken basedContext pointSub reflexivitySub)
open SharedJudgmentIdentityRegions (ofBody_point)

abbrev rules (level : LevelExpr Nat) (signature : Signature Tower.Head) :=
  NativeIdentityLevelInstantiation.rules (fun _ => level) signature

variable {n m : Nat} {level : LevelExpr Nat} {signature : Signature Tower.Head}
variable {context : Tower.Ctx n}

theorem based_formed {carrier left : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier) :
    ContextFormation (rules level signature) (basedContext context carrier left) :=
  .snoc (.snoc formed carrierTyped (.sort level))
    (.idForm carrierTyped.weaken (.sort level) leftTyped.weaken (.var 0)) (.sort level)

theorem twice_typed {carrier left term type : Tower.Tm n}
    (typed : Typing (rules level signature) context term type) :
    Typing (rules level signature) (basedContext context carrier left)
      (doubleWeaken term) (doubleWeaken type) :=
  typed.weaken.weaken

def inverseMotive (carrier left : Tower.Tm n) : Tower.Tm (n + 2) :=
  .id (doubleWeaken carrier) (.var 1) (doubleWeaken left)

def inverse (carrier left right path : Tower.Tm n) : Tower.Tm n :=
  identityEliminateApp carrier left (.lam (.lam (inverseMotive carrier left)))
    (.refl left) right path

@[simp] theorem inverseMotive_point (carrier left right path : Tower.Tm n) :
    subst (pointSub right path) (inverseMotive carrier left) = .id carrier right left := by
  simp only [inverseMotive, subst, FormationSensitiveBasedIdentity.pointSub_doubleWeaken]
  rfl

theorem inverse_typed {carrier left right path : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (rightTyped : Typing (rules level signature) context right carrier)
    (pathTyped : Typing (rules level signature) context path (.id carrier left right)) :
    Typing (rules level signature) context (inverse carrier left right path) (.id carrier right left) := by
  have bodyTyped : Typing (rules level signature) (basedContext context carrier left)
      (inverseMotive carrier left) (sortTm level) :=
    .idForm (twice_typed carrierTyped) (.sort level) (.var 1) (twice_typed leftTyped)
  have methodTyped : Typing (rules level signature) context (.refl left)
      (subst (reflexivitySub left) (inverseMotive carrier left)) := by
    change Typing _ _ _ (subst (pointSub left (.refl left)) _)
    rw [inverseMotive_point]
    exact .reflIntro leftTyped
  have result := ofBody_point formed carrierTyped leftTyped (inverseMotive carrier left)
    bodyTyped methodTyped rightTyped pathTyped
  simpa only [inverse, inverseMotive_point] using result.typing

theorem inverse_refl (carrier left : Tower.Tm n) :
    Conv (rules level signature).headEq (inverse carrier left left (.refl left))
      (.refl left) (rules level signature).computation :=
  .rel _ _ (.root (NativeIdentityLevelInstantiation.beta _ signature ..))

@[simp] theorem inverse_substitute (substitution : Sub Tower.Head n m)
    (carrier left right path : Tower.Tm n) :
    subst substitution (inverse carrier left right path) =
      inverse (subst substitution carrier) (subst substitution left)
        (subst substitution right) (subst substitution path) := by
  simp only [inverse, identityEliminateApp, subst, inverseMotive, doubleWeaken,
    subst_liftSub_wk, liftSub]
  rfl

def composeMotive (carrier left : Tower.Tm n) : Tower.Tm (n + 2) :=
  .id (doubleWeaken carrier) (doubleWeaken left) (.var 1)

/-- The first path goes left to middle; the second goes middle to right. -/
def compose (carrier left middle first right second : Tower.Tm n) : Tower.Tm n :=
  identityEliminateApp carrier middle (.lam (.lam (composeMotive carrier left)))
    first right second

@[simp] theorem composeMotive_point (carrier left right path : Tower.Tm n) :
    subst (pointSub right path) (composeMotive carrier left) = .id carrier left right := by
  simp only [composeMotive, subst, FormationSensitiveBasedIdentity.pointSub_doubleWeaken]
  rfl

theorem compose_typed {carrier left middle first right second : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (middleTyped : Typing (rules level signature) context middle carrier)
    (rightTyped : Typing (rules level signature) context right carrier)
    (firstTyped : Typing (rules level signature) context first (.id carrier left middle))
    (secondTyped : Typing (rules level signature) context second (.id carrier middle right)) :
    Typing (rules level signature) context (compose carrier left middle first right second)
      (.id carrier left right) := by
  have bodyTyped : Typing (rules level signature) (basedContext context carrier middle)
      (composeMotive carrier left) (sortTm level) :=
    .idForm (twice_typed carrierTyped) (.sort level) (twice_typed leftTyped) (.var 1)
  have methodTyped : Typing (rules level signature) context first
      (subst (reflexivitySub middle) (composeMotive carrier left)) := by
    change Typing _ _ _ (subst (pointSub middle (.refl middle)) _)
    rw [composeMotive_point]
    exact firstTyped
  have result := ofBody_point formed carrierTyped middleTyped (composeMotive carrier left)
    bodyTyped methodTyped rightTyped secondTyped
  simpa only [compose, composeMotive_point] using result.typing

theorem compose_refl (carrier left middle first : Tower.Tm n) :
    Conv (rules level signature).headEq (compose carrier left middle first middle (.refl middle))
      first (rules level signature).computation :=
  .rel _ _ (.root (NativeIdentityLevelInstantiation.beta _ signature ..))

@[simp] theorem compose_substitute (substitution : Sub Tower.Head n m)
    (carrier left middle first right second : Tower.Tm n) :
    subst substitution (compose carrier left middle first right second) =
      compose (subst substitution carrier) (subst substitution left)
        (subst substitution middle) (subst substitution first)
        (subst substitution right) (subst substitution second) := by
  simp only [compose, identityEliminateApp, subst, composeMotive, doubleWeaken,
    subst_liftSub_wk, liftSub]
  rfl

def cancellationMotive (carrier left : Tower.Tm n) : Tower.Tm (n + 2) :=
  .id (.id (doubleWeaken carrier) (.var 1) (.var 1))
    (compose (doubleWeaken carrier) (.var 1) (doubleWeaken left)
      (inverse (doubleWeaken carrier) (doubleWeaken left) (.var 1) (.var 0)) (.var 1) (.var 0))
    (.refl (.var 1))

def cancellation (carrier left right path : Tower.Tm n) : Tower.Tm n :=
  identityEliminateApp carrier left (.lam (.lam (cancellationMotive carrier left)))
    (.refl (.refl left)) right path

@[simp] theorem cancellationMotive_point (carrier left right path : Tower.Tm n) :
    subst (pointSub right path) (cancellationMotive carrier left) =
      .id (.id carrier right right)
        (compose carrier right left (inverse carrier left right path) right path) (.refl right) := by
  simp only [cancellationMotive, subst, compose_substitute, inverse_substitute,
    FormationSensitiveBasedIdentity.pointSub_doubleWeaken]
  rfl

theorem cancellationMotive_typed {carrier left : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier) :
    Typing (rules level signature) (basedContext context carrier left)
      (cancellationMotive carrier left) (sortTm level) := by
  have basedFormed := based_formed formed carrierTyped leftTyped
  have inverseTyped := inverse_typed basedFormed (twice_typed carrierTyped)
    (twice_typed leftTyped) (.var 1) (.var 0)
  have composeTyped := compose_typed basedFormed (twice_typed carrierTyped)
    (.var 1) (twice_typed leftTyped) (.var 1) inverseTyped (.var 0)
  exact .idForm (.idForm (twice_typed carrierTyped) (.sort level) (.var 1) (.var 1))
    (.sort level) composeTyped (.reflIntro (.var 1))

theorem cancellation_typed {carrier left right path : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (rightTyped : Typing (rules level signature) context right carrier)
    (pathTyped : Typing (rules level signature) context path (.id carrier left right)) :
    Typing (rules level signature) context (cancellation carrier left right path)
      (.id (.id carrier right right)
        (compose carrier right left (inverse carrier left right path) right path) (.refl right)) := by
  have bodyTyped := cancellationMotive_typed formed carrierTyped leftTyped
  have inverseTyped := inverse_typed formed carrierTyped leftTyped leftTyped (.reflIntro leftTyped)
  have compositionTyped := compose_typed formed carrierTyped leftTyped leftTyped leftTyped
    inverseTyped (.reflIntro leftTyped)
  have loopType := Typing.idForm carrierTyped (.sort level) leftTyped leftTyped
  have methodType := Typing.idForm loopType (.sort level) compositionTyped (.reflIntro leftTyped)
  have reduction : Conv (rules level signature).headEq
      (compose carrier left left (inverse carrier left left (.refl left)) left (.refl left))
      (.refl left) (rules level signature).computation :=
    .trans _ _ _ (compose_refl ..) (inverse_refl ..)
  have methodTyped : Typing (rules level signature) context (.refl (.refl left))
      (subst (reflexivitySub left) (cancellationMotive carrier left)) := by
    change Typing _ _ _ (subst (pointSub left (.refl left)) _)
    rw [cancellationMotive_point]
    exact .conv (.reflIntro (.reflIntro leftTyped)) methodType (.sort level)
      (Conv.congId (.refl _) reduction.symm (.refl _))
  have result := ofBody_point formed carrierTyped leftTyped (cancellationMotive carrier left)
    bodyTyped methodTyped rightTyped pathTyped
  simpa only [cancellation, cancellationMotive_point] using result.typing

@[simp] theorem cancellation_substitute (substitution : Sub Tower.Head n m)
    (carrier left right path : Tower.Tm n) :
    subst substitution (cancellation carrier left right path) =
      cancellation (subst substitution carrier) (subst substitution left)
        (subst substitution right) (subst substitution path) := by
  simp only [cancellation, identityEliminateApp, subst, cancellationMotive,
    compose_substitute, inverse_substitute, doubleWeaken, subst_liftSub_wk, liftSub]
  rfl

#print axioms inverse_typed
#print axioms compose_typed
#print axioms cancellation_typed
#print axioms cancellation_substitute

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityPaths
