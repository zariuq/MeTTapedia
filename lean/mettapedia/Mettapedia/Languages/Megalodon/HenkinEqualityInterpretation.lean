import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.Logic.HOL.Semantics.Extensionality
import Mettapedia.Logic.HOL.Semantics.LogicalRelationModel

/-!
# The binary-relation definition of equality in Henkin models

Egal and Megalodon define equality at a simple type by
`eq x y := ∀ Q, Q x y → Q y x`, where `Q` is a binary predicate.
The intrinsic term below uses precisely those constructors and erases to the
native lambda-term. It does not interpret a prefix-polymorphic declaration.

Term closure supplies an equality-testing predicate, so this definition always
implies intrinsic extensional equality on admitted values. The converse needs
extensional argument congruence, not full function domains. Agreement at every
type characterizes the existing `FunctionsRespectEqv` condition exactly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The actual preamble definition, as an intrinsic HOL term. -/
def equality {Γ : Ctx Base} (σ : Ty Base) : Term Const Γ (σ ⇒ σ ⇒ .prop) :=
  .lam (.lam (.all (σ := σ ⇒ σ ⇒ .prop)
    (.imp
      (.app (.app (.var .vz) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))
      (.app (.app (.var .vz) (.var (.vs .vz))) (.var (.vs (.vs .vz)))))))

/-- Apply the binary-relation definition to two terms of the same type. -/
def equalityFormula {Γ : Ctx Base} {σ : Ty Base}
    (left right : Term Const Γ σ) : Formula Const Γ :=
  .app (.app (equality σ) left) right

/-- The relation quantified over by the native equality definition. -/
def RelationEquality (M : HenkinModel.{u, v, w} Base Const) (σ : Ty Base)
    (left right : Ty.denote M.Carrier σ) : Prop :=
  ∀ relation : Ty.denote M.Carrier (σ ⇒ σ ⇒ .prop),
    M.adm (σ ⇒ σ ⇒ .prop) relation →
      (relation left right).down → (relation right left).down

theorem denote_equality (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} (σ : Ty Base) (ρ : M.Valuation Γ)
    (left right : Ty.denote M.Carrier σ) :
    (M.denote (equality σ) ρ left right).down ↔ RelationEquality M σ left right :=
  Iff.rfl

theorem denote_equalityFormula (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (left right : Term Const Γ σ) :
    (M.denote (equalityFormula left right) ρ).down ↔
      RelationEquality M σ (M.denote left ρ) (M.denote right ρ) :=
  Iff.rfl

/-- Term closure, rather than a full predicate space, admits this separator. -/
theorem equalityTest_admissible (M : HenkinModel.{u, v, w} Base Const)
    {σ : Ty Base} {left : Ty.denote M.Carrier σ} (admitted : M.adm σ left) :
    M.adm (σ ⇒ σ ⇒ .prop) (fun value _ => ULift.up (M.Eqv σ left value)) := by
  let test : Term Const [σ] (σ ⇒ σ ⇒ .prop) :=
    .lam (.lam (.eq (.var (.vs (.vs .vz))) (.var (.vs .vz))))
  let empty : M.Valuation [] := fun v => nomatch v
  let valuation : M.Valuation [σ] := M.extend empty left
  have valuation_admitted : M.ValuationAdmissible valuation := by
    apply M.extend_admissible
    · intro _ v
      nomatch v
    · exact admitted
  exact M.term_closed test valuation valuation_admitted

/-- The defined equality cannot identify values that intrinsic equality
separates; lambda closure supplies the separating relation. -/
theorem eqv_of_relationEquality (M : HenkinModel.{u, v, w} Base Const)
    {σ : Ty Base} {left right : Ty.denote M.Carrier σ}
    (admitted : M.adm σ left) (equal : RelationEquality M σ left right) :
    M.Eqv σ left right :=
  equal _ (equalityTest_admissible M admitted) (M.eqv_refl admitted)

/-- Extensional argument congruence suffices for the converse; full domains
are not assumed. -/
theorem relationEquality_of_eqv (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {σ : Ty Base} {left right : Ty.denote M.Carrier σ}
    (left_admitted : M.adm σ left) (right_admitted : M.adm σ right)
    (equal : M.Eqv σ left right) : RelationEquality M σ left right := by
  intro relation relation_admitted holds
  have first : M.Eqv .prop (relation left right) (relation right right) :=
    respects relation_admitted left_admitted right_admitted equal right right_admitted
  have second : M.Eqv .prop (relation right right) (relation right left) :=
    respects (M.app_mem relation_admitted right_admitted)
      right_admitted left_admitted (M.eqv_symm equal)
  exact second.mp (first.mp holds)

theorem relationEquality_iff_eqv (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {σ : Ty Base} {left right : Ty.denote M.Carrier σ}
    (left_admitted : M.adm σ left) (right_admitted : M.adm σ right) :
    RelationEquality M σ left right ↔ M.Eqv σ left right :=
  ⟨eqv_of_relationEquality M left_admitted,
    relationEquality_of_eqv M respects left_admitted right_admitted⟩

/-- Agreement of the two formula interpretations at every admitted valuation. -/
theorem denote_equalityFormula_iff_eq (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {σ : Ty Base} (ρ : M.Valuation Γ)
    (valuation_admitted : M.ValuationAdmissible ρ)
    (left right : Term Const Γ σ) :
    (M.denote (equalityFormula left right) ρ).down ↔
      (M.denote (.eq left right) ρ).down :=
  relationEquality_iff_eqv M respects
    (M.denote_admissible valuation_admitted left)
    (M.denote_admissible valuation_admitted right)

/-- A definable relation can compare the images under any admitted function. -/
theorem imageEqualityTest_admissible (M : HenkinModel.{u, v, w} Base Const)
    {σ τ : Ty Base} {function : Ty.denote M.Carrier (σ ⇒ τ)}
    {left : Ty.denote M.Carrier σ}
    (function_admitted : M.adm (σ ⇒ τ) function) (left_admitted : M.adm σ left) :
    M.adm (σ ⇒ σ ⇒ .prop)
      (fun value _ => ULift.up (M.Eqv τ (function left) (function value))) := by
  let test : Term Const [σ, σ ⇒ τ] (σ ⇒ σ ⇒ .prop) :=
    .lam (.lam (.eq
      (.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))))
      (.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))))
  let empty : M.Valuation [] := fun v => nomatch v
  let valuation : M.Valuation [σ, σ ⇒ τ] :=
    M.extend (M.extend empty function) left
  have valuation_admitted : M.ValuationAdmissible valuation := by
    apply M.extend_admissible
    · apply M.extend_admissible
      · intro _ v
        nomatch v
      · exact function_admitted
    · exact left_admitted
  exact M.term_closed test valuation valuation_admitted

/-- All-type agreement is equivalent to the existing extensional congruence
condition. Thus the latter is an exact model-side boundary, not just a
convenient sufficient condition. -/
theorem functionsRespectEqv_iff_equality_agreement
    (M : HenkinModel.{u, v, w} Base Const) :
    M.FunctionsRespectEqv ↔
      ∀ (σ : Ty Base) (left right : Ty.denote M.Carrier σ),
        M.adm σ left → M.adm σ right →
          (RelationEquality M σ left right ↔ M.Eqv σ left right) := by
  constructor
  · intro respects σ left right left_admitted right_admitted
    exact relationEquality_iff_eqv M respects left_admitted right_admitted
  · intro agreement σ τ function left right function_admitted left_admitted right_admitted equal
    have native_equal := (agreement σ left right left_admitted right_admitted).mpr equal
    exact native_equal _ (imageEqualityTest_admissible M function_admitted left_admitted)
      (M.eqv_refl (M.app_mem function_admitted left_admitted))

section NativeErasure

open MathdataKernel HenkinTermInterpretation

/-- The native syntax of the equality body, with no prefix type binder. -/
def nativeEquality (type : Tp) : Tm :=
  .lam type (.lam type (.all (.arr type (.arr type .prop))
    (.imp (.app (.app (.db 0) (.db 2)) (.db 1))
      (.app (.app (.db 0) (.db 1)) (.db 2)))))

theorem erase_equality {environment : Environment} {Γ : Ctx HenkinTermInterpretation.Base}
    (σ : Ty HenkinTermInterpretation.Base) :
    erase (equality (Const := Constant environment) (Γ := Γ) σ) =
      some (nativeEquality (reifyType σ)) :=
  rfl

theorem erase_equalityFormula {environment : Environment}
    {Γ : Ctx HenkinTermInterpretation.Base} {σ : Ty HenkinTermInterpretation.Base}
    {left right : Term (Constant environment) Γ σ} {raw_left raw_right : Tm}
    (left_erased : erase left = some raw_left) (right_erased : erase right = some raw_right) :
    erase (equalityFormula left right) =
      some (.app (.app (nativeEquality (reifyType σ)) raw_left) raw_right) := by
  simp only [equalityFormula, erase, erase_equality, left_erased, right_erased]
  rfl

end NativeErasure

namespace Counterexample

open MonotoneBooleanModel

/-- This admitted relation observes behavior at an excluded argument. -/
def relation : Ty.denote.{0, 0} model.Carrier
    (endomapObservation ⇒ endomapObservation ⇒ .prop) :=
  fun value _ => observesNegation value

theorem relation_admissible :
    model.adm (endomapObservation ⇒ endomapObservation ⇒ .prop) relation := by
  intro _ _ _ _ _ _
  trivial

/-- A lambda-closed, non-full model separates the defined equality from
intrinsic equality. Its missing condition is extensional argument congruence. -/
theorem eqv_but_not_relationEquality :
    model.Eqv endomapObservation atFalse andEndpoints ∧
      ¬ RelationEquality model endomapObservation atFalse andEndpoints := by
  refine ⟨atFalse_eqv_andEndpoints, ?_⟩
  intro equal
  have impossible := equal relation relation_admissible rfl
  cases impossible

end Counterexample

#print axioms equalityTest_admissible
#print axioms relationEquality_iff_eqv
#print axioms denote_equalityFormula_iff_eq
#print axioms functionsRespectEqv_iff_equality_agreement
#print axioms erase_equalityFormula
#print axioms Counterexample.eqv_but_not_relationEquality

end Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation
