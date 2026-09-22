import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation

/-!
# The same HOL interpretation as terms in the set-coded contextual model

HOL valuations give contexts of the existing set-coded CwF. Context extension
is explicitly equivalent to its dependent comprehension, and source terms
are sections of their actual type-code families. Function codes coincide with
the CwF's graph products; application and lambda agree on the actual graph
values. These are interpretation laws, not an identification of source syntax
or native identity proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualInterpretation

open ZFSetHOLTypeInterpretation ZFSetHOLTermInterpretation ZFSetDependentProducts
open ZFSetUniverseClosure ZFSetUniverseInterpretation
open ZFSetContextualInterpretation (SetFamily Section Extension)

universe u

abbrev Context (Γ : Ctx Unit) := Valuation.{u} Γ

@[reducible] noncomputable def typeFamily (Γ : Ctx Unit) (A : Ty Unit) : SetFamily.{u + 1} (Context.{u} Γ) :=
  fun _ => typeCode A

noncomputable def termSection (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (term : UniverseExpr Γ A) :
    Section (typeFamily Γ A) := interpret (universeConstants h) term

noncomputable def contextSubstitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (θ : Subst UniverseSymbol Γ Δ) : Context Δ → Context Γ :=
  substValuation (universeConstants h) θ

noncomputable def extensionEquiv (Γ : Ctx Unit) (A : Ty Unit) :
    Context.{u} (A :: Γ) ≃ Extension (typeFamily Γ A) where
  toFun := fun ρ => ⟨fun {_} index => ρ (.vs index), ρ .vz⟩
  invFun := fun pair => extend pair.1 pair.2
  left_inv := by
    intro ρ
    funext B index
    cases index <;> rfl
  right_inv := by
    intro pair
    cases pair
    rfl

theorem extension_natural (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Context Δ) (x : Value A) :
    extensionEquiv Γ A (contextSubstitution h (Subst.lift θ) (extend ρ x)) =
      ZFSetContextualInterpretation.extensionSubstitution
        (contextSubstitution h θ) (typeFamily Γ A) ⟨ρ, x⟩ := by
  change extensionEquiv Γ A (substValuation (universeConstants h) (Subst.lift θ)
      (extend ρ x)) = _
  rw [universe_substValuation_lift]
  rfl

theorem type_substitution {Γ Δ : Ctx Unit} (θ : Context.{u} Δ → Context Γ)
    (A : Ty Unit) : typeFamily Γ A ∘ θ = typeFamily Δ A := rfl

theorem term_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (term : UniverseExpr Γ A)
    (θ : Subst UniverseSymbol Γ Δ) :
    termSection h (HOL.subst θ term) =
      (fun ρ => termSection h term (contextSubstitution h θ ρ)) := by
  funext ρ
  exact universe_substitution h term θ ρ

/-! ## The actual contextual graph product -/

theorem arrow_code (Γ : Ctx Unit) (A B : Ty Unit) :
    ZFSetContextualInterpretation.piFamily (typeFamily.{u} Γ A)
      (fun _ => typeCode B) = typeFamily Γ (A ⇒ B) := by
  funext ρ
  apply piSet_congr
  intro x member
  exact ZFSetContextualInterpretation.totalFamily_at (typeCode A)
    (fun _ => typeCode B) ⟨x, member⟩

noncomputable def toProduct {Γ : Ctx Unit} {A B : Ty Unit}
    (function : Section (typeFamily.{u} Γ (A ⇒ B))) :
    Section (ZFSetContextualInterpretation.piFamily (typeFamily Γ A) (fun _ => typeCode B)) :=
  fun ρ => ⟨(function ρ).1, by rw [arrow_code]; exact (function ρ).2⟩

noncomputable def fromProduct {Γ : Ctx Unit} {A B : Ty Unit}
    (function : Section (ZFSetContextualInterpretation.piFamily
      (typeFamily.{u} Γ A) (fun _ => typeCode B))) : Section (typeFamily Γ (A ⇒ B)) :=
  fun ρ => ⟨(function ρ).1,
    (congrArg (fun code : ZFSet => (function ρ).1 ∈ code)
      (congrFun (arrow_code Γ A B) ρ)).mp (function ρ).2⟩

theorem to_fromProduct {Γ : Ctx Unit} {A B : Ty Unit}
    (function : Section (ZFSetContextualInterpretation.piFamily
      (typeFamily.{u} Γ A) (fun _ => typeCode B))) :
    toProduct (fromProduct function) = function := by
  funext ρ
  rfl

private theorem cast_elements_value {a b : ZFSet.{u + 1}} (equal : a = b)
    (value : Elements a) :
    ((Equiv.cast (congrArg Elements equal)) value).1 = value.1 := by
  subst b
  rfl

private theorem piDecode_value {Γ : Type (u + 2)} (a : SetFamily.{u + 1} Γ)
    (b : SetFamily (Extension a)) (ρ : Γ)
    (function : Elements (ZFSetContextualInterpretation.piFamily a b ρ))
    (argument : Elements (a ρ)) :
    (ZFSetContextualInterpretation.piDecode a b ρ function argument).1 =
      (graphValue function argument).1 := by
  change ((Equiv.cast (congrArg Elements
    (ZFSetContextualInterpretation.totalFamily_at (a ρ) (fun x => b ⟨ρ, x⟩) argument)))
      (graphValue function argument)).1 = _
  exact cast_elements_value
    (ZFSetContextualInterpretation.totalFamily_at (a ρ) (fun x => b ⟨ρ, x⟩) argument) _

theorem application_agreement {Γ : Ctx Unit} {A B : Ty Unit}
    (function : Section (typeFamily.{u} Γ (A ⇒ B)))
    (argument : Section (typeFamily Γ A)) :
    ZFSetContextualInterpretation.app (toProduct function) argument =
      fun ρ => app (function ρ) (argument ρ) := by
  funext ρ
  apply Subtype.ext
  rw [ZFSetContextualInterpretation.app, piDecode_value]
  apply graphValue_unique (function ρ) (argument ρ)
  exact graphValue_pair_mem (toProduct function ρ) (argument ρ)

theorem lambda_agreement {Γ : Ctx Unit} {A B : Ty Unit}
    (body : Context.{u} Γ → Value A → Value B) :
    fromProduct (ZFSetContextualInterpretation.lam
      (a := typeFamily Γ A) (b := fun _ => typeCode B)
      (fun pair => body pair.1 pair.2)) =
        fun ρ => lam (body ρ) := by
  funext ρ
  apply (piEquiv (typeCode A) (fun _ => typeCode B)).injective
  funext x
  have evaluation := congrFun
    (application_agreement
      (fromProduct (ZFSetContextualInterpretation.lam
        (a := typeFamily Γ A) (b := fun _ => typeCode B)
        (fun pair => body pair.1 pair.2))) (fun _ => x)) ρ
  rw [to_fromProduct, ZFSetContextualInterpretation.app_lam] at evaluation
  change app _ x = app (lam (body ρ)) x
  rw [app_lam]
  exact evaluation.symm

theorem term_application (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A B : Ty Unit} (function : UniverseExpr Γ (A ⇒ B))
    (argument : UniverseExpr Γ A) :
    termSection h (.app function argument) =
      ZFSetContextualInterpretation.app (toProduct (termSection h function))
        (termSection h argument) :=
  (application_agreement (termSection h function) (termSection h argument)).symm

theorem term_lambda (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A B : Ty Unit} (body : UniverseExpr (A :: Γ) B) :
    termSection h (.lam body) =
      fromProduct (ZFSetContextualInterpretation.lam
        (a := typeFamily Γ A) (b := fun _ => typeCode B)
        (fun pair => termSection h body ((extensionEquiv Γ A).symm pair))) :=
  (lambda_agreement (fun ρ x => termSection h body (extend ρ x))).symm

namespace Controls

def identifyVariables : Subst UniverseSymbol [.prop, .prop] [.prop]
  | _, .vz => .var .vz
  | _, .vs .vz => .var .vz

theorem identified_context (h : CofinalInaccessibles.{u}) (p : Value .prop) :
    (contextSubstitution h identifyVariables (extend emptyValuation p) : Context [.prop, .prop]) =
      (extend (extend emptyValuation p) p : Context [.prop, .prop]) := by
  funext A index
  cases index with
  | vz => rfl
  | vs index => cases index with
    | vz => rfl
    | vs index => exact nomatch index

/-- An ordinary well-typed substitution need not be invertible: identifying
two variables cannot reproduce a context assigning them different truths. -/
theorem identified_context_not_surjective (h : CofinalInaccessibles.{u})
    (ρ : Context [.prop]) :
    (contextSubstitution h identifyVariables ρ : Context [.prop, .prop]) ≠
      (extend (extend emptyValuation (truth False)) (truth True) : Context [.prop, .prop]) := by
  intro equal
  have first := congrArg (fun ν : Context [.prop, .prop] => ν .vz) equal
  have second := congrArg (fun ν : Context [.prop, .prop] => ν (.vs .vz)) equal
  change ρ .vz = truth True at first
  change ρ .vz = truth False at second
  exact truth_false_ne_truth_true (second.symm.trans first)

end Controls

#print axioms extensionEquiv
#print axioms extension_natural
#print axioms term_substitution
#print axioms arrow_code
#print axioms application_agreement
#print axioms lambda_agreement
#print axioms term_application
#print axioms term_lambda
#print axioms Controls.identified_context
#print axioms Controls.identified_context_not_surjective

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLContextualInterpretation
