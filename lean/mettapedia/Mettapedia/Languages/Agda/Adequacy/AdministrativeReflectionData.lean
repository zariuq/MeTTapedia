import Mettapedia.Languages.Agda.Adequacy.StaticSpineReflection
import Mettapedia.Languages.Agda.Structural.AdministrativeContextRegularity

/-!
# Conditional source interpretation of administrative spine equality

Core judgments and spine actions use their existing interpretation families.
Spine equality additionally records both successful spine observations and an
actual source equality transformer. It consumes a typed equality of heads;
it does not supply formation or either action endpoint by itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection

open Mettapedia.OSLF.Binding
open Structural.Statics (RawTm RawTy RawContext)
open Structural.AdministrativeStatics

structure EqualityResult {n : Nat} (Δ : StaticSpecification.RawContext n)
    (input : StaticSpecification.Ty n) (es fs : Structural.Spine (Structural.scope n)) (B : RawTy n) where
  first : StaticSpecification.Spine n
  second : StaticSpecification.Spine n
  output : StaticSpecification.Ty n
  firstObserved : Observation.spine es = some first
  secondObserved : Observation.spine fs = some second
  outputObserved : Observation.type B = some output
  proof : ∀ {f g : StaticSpecification.Term n}, StaticSpecification.TermEq Δ f g input →
    StaticSpecification.TermEq Δ (f.applySpine first) (g.applySpine second) output

def EqualityResult.at {n : Nat} {Δ : StaticSpecification.RawContext n} {input : StaticSpecification.Ty n}
    {es fs : Structural.Spine (Structural.scope n)} {B : RawTy n} (value : EqualityResult Δ input es fs B)
    {first second : StaticSpecification.Spine n} {output : StaticSpecification.Ty n}
    (left : Observation.spine es = some first) (right : Observation.spine fs = some second)
    (typeObserved : Observation.type B = some output) {f g : StaticSpecification.Term n}
    (heads : StaticSpecification.TermEq Δ f g input) :
    StaticSpecification.TermEq Δ (f.applySpine first) (g.applySpine second) output :=
  (Reflection.observed_unique value.firstObserved left) ▸
    (Reflection.observed_unique value.secondObserved right) ▸
    (Reflection.observed_unique value.outputObserved typeObserved) ▸ value.proof heads

def Interpretation : Judgment → Type
  | .core j => Reflection.Interpretation j
  | .spineAction Γ A es B => ∀ Δ, Observation.context Γ = some Δ →
      ∀ a, Observation.type A = some a → SpineReflection.ActionResult Δ a es B
  | .spineEquality Γ A es fs B => ∀ Δ, Observation.context Γ = some Δ →
      ∀ a, Observation.type A = some a → EqualityResult Δ a es fs B

def toPriorInterpretation {j : Structural.SpineStatics.CombinedJudgment}
    (value : Interpretation (mapPrior j)) : SpineReflection.Interpretation j := by
  cases j <;> exact value

def ofPriorInterpretation {j : Structural.SpineStatics.CombinedJudgment}
    (value : SpineReflection.Interpretation j) : Interpretation (mapPrior j) := by
  cases j <;> exact value

theorem observe_empty_prefix {n : Nat} (es : Structural.Spine (Structural.scope n)) :
    Observation.spine (Structural.append Structural.nil es) = Observation.spine es := by
  rw [Observation.append_eq, Observation.nil_eq]
  cases h : Observation.spine es <;> rfl

theorem observe_cons_prefix {n : Nat} (u : RawTm n) (es fs : Structural.Spine (Structural.scope n)) :
    Observation.spine (Structural.append (Structural.cons (Structural.apply u) es) fs) =
      Observation.spine (Structural.cons (Structural.apply u) (Structural.append es fs)) := by
  simp only [Observation.append_eq, Observation.cons_eq]
  cases hu : Observation.elim (Structural.apply u) <;>
    cases he : Observation.spine es <;> cases hf : Observation.spine fs <;> rfl

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection
