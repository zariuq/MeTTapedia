import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTypeInterpretation

/-!
# Uniform-list HOL terms in the trace representation

This interpreter traverses the original intrinsically typed HOL syntax and
uses trace lambda/application at every arrow.  Decoding commutes with the
existing `ZFSetUniformListModel` denotation, so the two sides share one list
model and differ only in their function representation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTermInterpretation

open UniformListInduction
open ZFSetUniformListTraceTypeInterpretation
open ZFSetHOLTypeInterpretation (truth holds holds_truth)

universe u

abbrev Valuation (a : ZFSet.{u}) (Γ : Ctx BaseSort) :=
  ∀ {A}, Var Γ A → Value a A

abbrev RawValuation (a : ZFSet.{u}) (Γ : Ctx BaseSort) :=
  ∀ {A}, Var Γ A → Ty.denote.{0, u + 1} (ZFSetUniformListModel.carrier a) A

noncomputable def decodeValuation {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    (ρ : Valuation a Γ) : RawValuation a Γ :=
  fun {_} boundVar => decode a _ (ρ boundVar)

def extend {a : ZFSet.{u}} {Γ : Ctx BaseSort} {A : Ty BaseSort}
    (ρ : Valuation a Γ) (x : Value a A) : Valuation a (A :: Γ)
  | _, .vz => x
  | _, .vs boundVar => ρ boundVar

/-- Precompose a trace valuation with a typed variable renaming. -/
def renameVal {a : ZFSet.{u}} {Γ Δ : Ctx BaseSort}
    (ρ : Rename BaseSort Γ Δ) (ν : Valuation a Δ) : Valuation a Γ :=
  fun {_} boundVar => ν (ρ boundVar)

theorem renameVal_lift {a : ZFSet.{u}} {Γ Δ : Ctx BaseSort}
    {σ : Ty BaseSort} (ρ : Rename BaseSort Γ Δ) (ν : Valuation a Δ)
    (x : Value a σ) :
    (renameVal (Rename.lift (σ := σ) ρ) (extend ν x) : Valuation a (σ :: Γ)) =
      (extend (renameVal ρ ν) x : Valuation a (σ :: Γ)) := by
  funext type boundVar
  cases boundVar <;> rfl

theorem decodeValuation_extend {a : ZFSet.{u}} {Γ : Ctx BaseSort}
    {A : Ty BaseSort} (ρ : Valuation a Γ) (x : Value a A) :
    (decodeValuation (extend ρ x) : RawValuation a (A :: Γ)) =
      ((ZFSetUniformListModel.model a).extend (decodeValuation ρ) (decode a A x) :
        RawValuation a (A :: Γ)) := by
  funext B boundVar
  cases boundVar <;> rfl

noncomputable def interpret :
    {a : ZFSet.{u}} → {Γ : Ctx BaseSort} → {A : Ty BaseSort} →
      Term Symbol Γ A → Valuation a Γ → Value a A
  | _, _, _, .var boundVar, ρ => ρ boundVar
  | a, _, _, .const c, _ => constant a c
  | _, _, _, .app f x, ρ => app (interpret f ρ) (interpret x ρ)
  | _, _, _, .lam body, ρ => lam (fun x => interpret body (extend ρ x))
  | _, _, _, .top, _ => truth True
  | _, _, _, .bot, _ => truth False
  | _, _, _, .and p q, ρ => truth (holds (interpret p ρ) ∧ holds (interpret q ρ))
  | _, _, _, .or p q, ρ => truth (holds (interpret p ρ) ∨ holds (interpret q ρ))
  | _, _, _, .imp p q, ρ => truth (holds (interpret p ρ) → holds (interpret q ρ))
  | _, _, _, .not p, ρ => truth (¬ holds (interpret p ρ))
  | _, _, _, .eq x y, ρ => truth (interpret x ρ = interpret y ρ)
  | _, _, _, .all p, ρ => truth (∀ x, holds (interpret p (extend ρ x)))
  | _, _, _, .ex p, ρ => truth (∃ x, holds (interpret p (extend ρ x)))

/-- Trace interpretation is natural in the source context. -/
theorem interpret_rename {a : ZFSet.{u}} :
    ∀ {Γ Δ : Ctx BaseSort} {A : Ty BaseSort}
      (ρ : Rename BaseSort Γ Δ) (term : Term Symbol Γ A) (ν : Valuation a Δ),
      interpret (rename ρ term) ν = interpret term (renameVal ρ ν)
  | _, _, _, ρ, .var boundVar, ν => rfl
  | _, _, _, ρ, .const symbol, ν => rfl
  | _, _, _, ρ, .app function argument, ν => by
      simp only [rename, interpret, interpret_rename ρ function ν,
        interpret_rename ρ argument ν]
  | _, _, _, ρ, .lam body, ν => by
      simp only [rename, interpret]
      apply congrArg lam
      funext argument
      rw [interpret_rename (Rename.lift ρ) body (extend ν argument),
        renameVal_lift]
  | _, _, _, ρ, .top, ν => rfl
  | _, _, _, ρ, .bot, ν => rfl
  | _, _, _, ρ, .and left right, ν => by
      simp only [rename, interpret]
      apply congrArg truth
      apply propext
      simp only [interpret_rename ρ left ν, interpret_rename ρ right ν]
  | _, _, _, ρ, .or left right, ν => by
      simp only [rename, interpret]
      apply congrArg truth
      apply propext
      simp only [interpret_rename ρ left ν, interpret_rename ρ right ν]
  | _, _, _, ρ, .imp premise conclusion, ν => by
      simp only [rename, interpret]
      apply congrArg truth
      apply propext
      simp only [interpret_rename ρ premise ν,
        interpret_rename ρ conclusion ν]
  | _, _, _, ρ, .not formula, ν => by
      simp only [rename, interpret]
      apply congrArg truth
      apply propext
      simp only [interpret_rename ρ formula ν]
  | _, _, _, ρ, .eq left right, ν => by
      simp only [rename, interpret, interpret_rename ρ left ν,
        interpret_rename ρ right ν]
  | _, _, _, ρ, .all formula, ν => by
      simp only [rename, interpret]
      apply congrArg truth
      apply propext
      constructor <;> intro hypothesis argument
      · have body := hypothesis argument
        rw [interpret_rename (Rename.lift ρ) formula (extend ν argument),
          renameVal_lift] at body
        exact body
      · have body := hypothesis argument
        rw [interpret_rename (Rename.lift ρ) formula (extend ν argument),
          renameVal_lift]
        exact body
  | _, _, _, ρ, .ex formula, ν => by
      simp only [rename, interpret]
      apply congrArg truth
      apply propext
      constructor
      · rintro ⟨argument, body⟩
        refine ⟨argument, ?_⟩
        rw [interpret_rename (Rename.lift ρ) formula (extend ν argument),
          renameVal_lift] at body
        exact body
      · rintro ⟨argument, body⟩
        refine ⟨argument, ?_⟩
        rw [interpret_rename (Rename.lift ρ) formula (extend ν argument),
          renameVal_lift]
        exact body

theorem proposition_down {a : ZFSet.{u}}
    (value : Value a (.prop : Ty BaseSort)) :
    (decode a .prop value).down = holds value := rfl

/-- Independently evaluating a source term as traces and then decoding gives
the same value as evaluating it in the retained full-domain list model. -/
theorem term_agreement {a : ZFSet.{u}} {Γ : Ctx BaseSort} {A : Ty BaseSort}
    (term : Term Symbol Γ A) (ρ : Valuation a Γ) :
    decode a A (interpret term ρ) =
      (ZFSetUniformListModel.model a).denote term (decodeValuation ρ) := by
  induction term with
  | var => rfl
  | const c => exact decode_constant c
  | app f x ihf ihx =>
      rw [interpret, decode_app, ihf, ihx]
      rfl
  | @lam A B Γ body ih =>
      rw [interpret, decode_lam]
      funext x
      rw [ih, decodeValuation_extend, Equiv.apply_symm_apply]
      rfl
  | top => exact decode_truth True
  | bot => exact decode_truth False
  | and p q ihp ihq =>
      rw [interpret, decode_truth]
      apply ULift.ext
      exact propext (by rw [← proposition_down, ihp, ← proposition_down, ihq])
        |>.trans (by rfl)
  | or p q ihp ihq =>
      rw [interpret, decode_truth]
      apply ULift.ext
      exact propext (by rw [← proposition_down, ihp, ← proposition_down, ihq])
        |>.trans (by rfl)
  | imp p q ihp ihq =>
      rw [interpret, decode_truth]
      apply ULift.ext
      exact propext (by rw [← proposition_down, ihp, ← proposition_down, ihq])
        |>.trans (by rfl)
  | not p ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      exact propext (by rw [← proposition_down, ih])
        |>.trans (by rfl)
  | eq x y ihx ihy =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      rw [equality_decode, ihx, ihy]
      rfl
  | @all A Γ p ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change (∀ x : Value a A, holds (interpret p (extend ρ x))) ↔
        ∀ x : Ty.denote (ZFSetUniformListModel.carrier a) A,
          True → ((ZFSetUniformListModel.model a).denote p
            ((ZFSetUniformListModel.model a).extend (decodeValuation ρ) x)).down
      constructor
      · intro hp x _
        have value := hp ((decode a A).symm x)
        have agree := congrArg ULift.down (ih (extend ρ ((decode a A).symm x)))
        change holds (interpret p (extend ρ ((decode a A).symm x))) = _ at agree
        rw [decodeValuation_extend, Equiv.apply_symm_apply] at agree
        exact Eq.mp agree value
      · intro hp x
        have value := hp (decode a A x) trivial
        have agree := congrArg ULift.down (ih (extend ρ x))
        change holds (interpret p (extend ρ x)) = _ at agree
        rw [decodeValuation_extend] at agree
        exact Eq.mpr agree value
  | @ex A Γ p ih =>
      rw [interpret, decode_truth]
      apply ULift.ext
      apply propext
      change (∃ x : Value a A, holds (interpret p (extend ρ x))) ↔
        ∃ x : Ty.denote (ZFSetUniformListModel.carrier a) A,
          True ∧ ((ZFSetUniformListModel.model a).denote p
            ((ZFSetUniformListModel.model a).extend (decodeValuation ρ) x)).down
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨decode a A x, ?_⟩
        refine ⟨trivial, ?_⟩
        have agree := congrArg ULift.down (ih (extend ρ x))
        change holds (interpret p (extend ρ x)) = _ at agree
        rw [decodeValuation_extend] at agree
        exact Eq.mp agree hx
      · rintro ⟨x, _, hx⟩
        refine ⟨(decode a A).symm x, ?_⟩
        have agree := congrArg ULift.down (ih (extend ρ ((decode a A).symm x)))
        change holds (interpret p (extend ρ ((decode a A).symm x))) = _ at agree
        rw [decodeValuation_extend, Equiv.apply_symm_apply] at agree
        exact Eq.mpr agree hx

def emptyValuation {a : ZFSet.{u}} : Valuation a [] :=
  fun {_} boundVar => nomatch boundVar

#print axioms decodeValuation_extend
#print axioms renameVal_lift
#print axioms interpret_rename
#print axioms term_agreement

end Mettapedia.Logic.HOL.Embedding.ZFSetUniformListTraceTermInterpretation
