import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTypeInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTermInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual

/-!
# Uniform HOL arrows as contextual trace products

The uniform HOL trace interpretation and the dependent contextual trace
interpretation use the same Aczel trace sets. The contextual model totalizes
the codomain outside the domain; bounded products do not inspect those values.
This module identifies their actual set codes and applications. It does not
identify arbitrary dependent products with HOL arrows.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceContextualBridge

open ZFSetDependentProducts (Elements)
open ZFSetContextualInterpretation (SetFamily Section Extension totalFamily totalFamily_at)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open Mettapedia.Logic.HOL.UniformListInduction

universe u

/-- The recursive source interpreter exposes the body and argument of a HOL
beta redex without normalizing either term. -/
theorem interpret_app_lam {a : ZFSet.{u}} {gamma : Mettapedia.Logic.HOL.Ctx BaseSort}
    {A B : Mettapedia.Logic.HOL.Ty BaseSort}
    (body : Mettapedia.Logic.HOL.Term Symbol (A :: gamma) B)
    (argument : Mettapedia.Logic.HOL.Term Symbol gamma A)
    (valuation : Valuation a gamma) :
    interpret (Mettapedia.Logic.HOL.Term.app
      (Mettapedia.Logic.HOL.Term.lam body) argument) valuation =
      app (lam (fun x => interpret body (extend valuation x)))
        (interpret argument valuation) := rfl

/-- A constant-codomain contextual trace product has exactly the HOL arrow
code, even though its totalized codomain differs outside the domain. -/
theorem arrow_family_eq_piFamily {Γ : Type (u + 1)} (a : ZFSet.{u})
    (A B : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort) :
    (fun _ : Γ => typeCode a (.arr A B)) =
      ZFSetTraceContextual.piFamily (fun _ => typeCode a A)
        (fun _ : Extension (fun _ : Γ => typeCode a A) => typeCode a B) := by
  funext γ
  change ZFSetTraceProducts.tracePiSet (typeCode a A) (fun _ => typeCode a B) =
    ZFSetTraceProducts.tracePiSet (typeCode a A)
      (totalFamily (typeCode a A) (fun _ => typeCode a B))
  apply ZFSetTraceProducts.tracePiSet_congr
  intro x hx
  exact (totalFamily_at (typeCode a A) (fun _ => typeCode a B) ⟨x, hx⟩).symm

/-- Transport a HOL arrow into the literally equal contextual product fibre.
This changes its membership proof, not its underlying trace code. -/
noncomputable def toContext {Γ : Type (u + 1)} (a : ZFSet.{u})
    (A B : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (γ : Γ) (function : Value a (.arr A B)) :
    Elements (ZFSetTraceContextual.piFamily (fun _ : Γ => typeCode a A)
      (fun _ : Extension (fun _ : Γ => typeCode a A) => typeCode a B) γ) :=
  (Equiv.cast (congrArg Elements (congrFun (arrow_family_eq_piFamily a A B) γ)))
    function

private theorem cast_value {first second : ZFSet.{u}} (equal : first = second)
    (value : Elements first) :
    ((Equiv.cast (congrArg Elements equal)) value).1 = value.1 := by
  cases equal
  rfl

private theorem cast_section_apply {Γ : Type (u + 1)}
    {first second : SetFamily Γ} (equal : first = second)
    (value : Section first) (γ : Γ) :
    (equal ▸ value) γ =
      (Equiv.cast (congrArg Elements (congrFun equal γ))) (value γ) := by
  cases equal
  rfl

theorem toContext_section {Γ : Type (u + 1)} (a : ZFSet.{u})
    (A B : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (function : Γ → Value a (.arr A B)) :
    (arrow_family_eq_piFamily a A B ▸ function) =
      fun γ => toContext a A B γ (function γ) := by
  funext γ
  exact cast_section_apply (arrow_family_eq_piFamily a A B) function γ

theorem toContext_value {Γ : Type (u + 1)} (a : ZFSet.{u})
    (A B : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (γ : Γ) (function : Value a (.arr A B)) :
    (toContext a A B γ function).1 = function.1 := by
  exact cast_value (congrFun (arrow_family_eq_piFamily a A B) γ) function

/-- Contextual application agrees with HOL application as a typed value, not
only as an untyped raw set. -/
theorem app_agreement {Γ : Type (u + 1)} (a : ZFSet.{u})
    (A B : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (γ : Γ) (function : Value a (.arr A B)) (argument : Value a A) :
    ZFSetTraceContextual.piDecode (fun _ : Γ => typeCode a A)
      (fun _ : Extension (fun _ : Γ => typeCode a A) => typeCode a B)
      γ (toContext a A B γ function) argument = app function argument := by
  apply Subtype.ext
  rw [ZFSetTraceContextual.piDecode_value, toContext_value]
  rfl

/-- Transporting HOL abstraction to the contextual product gives the same
trace-coded section as contextual abstraction of the same body. -/
theorem lam_agreement {Γ : Type (u + 1)} (a : ZFSet.{u})
    (A B : Mettapedia.Logic.HOL.Ty Mettapedia.Logic.HOL.UniformListInduction.BaseSort)
    (body : (γ : Γ) → Value a A → Value a B) (γ : Γ) :
    toContext a A B γ (lam (body γ)) =
      ZFSetTraceContextual.lam (fun point : Extension
        (fun _ : Γ => typeCode a A) => body point.1 point.2) γ := by
  apply (ZFSetTraceContextual.piDecode (fun _ : Γ => typeCode a A)
    (fun _ : Extension (fun _ : Γ => typeCode a A) => typeCode a B) γ).injective
  funext x
  rw [app_agreement, app_lam]
  simp only [ZFSetTraceContextual.lam, Equiv.apply_symm_apply]

/-- A genuinely dependent family need not be the interpretation of any
constant-codomain HOL arrow. -/
theorem varying_codomain_not_constant :
    ¬ ∃ B : ZFSet.{u}, ∀ x : Elements ZFSetDependentProducts.Controls.two,
      ZFSetDependentProducts.Controls.varying x.1 = B := by
  rintro ⟨B, allEqual⟩
  have atZero := allEqual
    ⟨∅, ZFSetDependentProducts.Controls.empty_mem_two⟩
  have atOne := allEqual
    ⟨ZFSet.powerset ∅, ZFSetDependentProducts.Controls.power_empty_mem_two⟩
  exact ZFSetDependentProducts.Controls.varying_fibres_distinct
    (atZero.trans atOne.symm)

#print axioms arrow_family_eq_piFamily
#print axioms interpret_app_lam
#print axioms toContext_value
#print axioms toContext_section
#print axioms app_agreement
#print axioms lam_agreement
#print axioms varying_codomain_not_constant

end Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceContextualBridge
