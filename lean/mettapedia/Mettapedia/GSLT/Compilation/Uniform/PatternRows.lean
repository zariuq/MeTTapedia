import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep

/-!
# Reading patterns off their rows

The row of a pattern (`RootRewritesOnTheStep.encode`) begins with the code of its constructor, so a row of a given
shape is the row of a pattern of the matching constructor, and its parts are the rows of the pattern's parts. The
same holds for lists of patterns and for numbers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.PatternRows

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode collectionCode_injective)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RootRewritesOnTheStep (encode encodeList labelCode numeral optionRow namesRow)

theorem numeral_zero_inv {m : ℕ} (same : Expr.sym 0 = numeral m) : m = 0 := by
  cases m with
  | zero => rfl
  | succ _ => simp [numeral] at same

theorem numeral_succ_inv {m : ℕ} {x : Expr} (same : Expr.app (.sym 1) x = numeral m) :
    ∃ m', m = m' + 1 ∧ x = numeral m' := by
  cases m with
  | zero => simp [numeral] at same
  | succ m' => simp only [numeral, Expr.app.injEq, true_and] at same; exact ⟨m', rfl, same⟩

theorem encode_bvar_inv {p : Pattern} {x : Expr} (same : Expr.app (.sym 0) x = encode p) :
    ∃ index, p = .bvar index ∧ x = numeral index := by
  cases p <;> simp_all [encode]

theorem encode_fvar_inv {p : Pattern} {x : Expr} (same : Expr.app (.sym 1) x = encode p) :
    ∃ name, p = .fvar name ∧ x = .sym (labelCode name) := by
  cases p <;> simp_all [encode]

theorem encode_apply_inv {p : Pattern} {a b : Expr} (same : Expr.app (.sym 2) (.app a b) = encode p) :
    ∃ label arguments, p = .apply label arguments ∧ a = .sym (labelCode label) ∧ b = encodeList arguments := by
  cases p <;> simp_all [encode]

theorem encode_lambda_inv {p : Pattern} {a b : Expr} (same : Expr.app (.sym 3) (.app a b) = encode p) :
    ∃ binder body, p = .lambda binder body ∧ a = optionRow binder ∧ b = encode body := by
  cases p <;> simp_all [encode]

theorem encode_multiLambda_inv {p : Pattern} {a b c : Expr}
    (same : Expr.app (.sym 4) (.app a (.app b c)) = encode p) :
    ∃ arity binders body, p = .multiLambda arity binders body ∧ a = numeral arity ∧ b = namesRow binders ∧
      c = encode body := by
  cases p <;> simp_all [encode]

theorem encode_subst_inv {p : Pattern} {a b : Expr} (same : Expr.app (.sym 5) (.app a b) = encode p) :
    ∃ body value, p = .subst body value ∧ a = encode body ∧ b = encode value := by
  cases p <;> simp_all [encode]

theorem encode_collection_inv {p : Pattern} {a b c : Expr}
    (same : Expr.app (.sym 6) (.app a (.app b c)) = encode p) :
    ∃ kind elements rest, p = .collection kind elements rest ∧ a = .sym (collectionCode kind) ∧
      b = encodeList elements ∧ c = optionRow rest := by
  cases p <;> simp_all [encode]

/-- A row of a collection with no rest is the row of one. -/
theorem encode_closed_inv {p : Pattern} {kind : CollType} {x : Expr}
    (same : Expr.app (.sym 6) (.app (.sym (collectionCode kind)) (.app x (.sym 0))) = encode p) :
    ∃ elements, p = .collection kind elements none ∧ x = encodeList elements := by
  obtain ⟨kind', elements, rest, rfl, kindIs, elementsIs, restIs⟩ := encode_collection_inv same
  obtain rfl := collectionCode_injective (Expr.sym.inj kindIs)
  cases rest with
  | none => exact ⟨elements, rfl, elementsIs⟩
  | some _ => simp [optionRow] at restIs

theorem encodeList_nil_inv {xs : List Pattern} (same : Expr.sym 0 = encodeList xs) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => simp [encodeList] at same

theorem encodeList_cons_inv {xs : List Pattern} {a b : Expr} (same : Expr.app a b = encodeList xs) :
    ∃ x rest, xs = x :: rest ∧ a = encode x ∧ b = encodeList rest := by
  cases xs with
  | nil => simp [encodeList] at same
  | cons x rest => simp only [encodeList, Expr.app.injEq] at same; exact ⟨x, rest, rfl, same.1, same.2⟩

end Mettapedia.GSLT.Compilation.Uniform.PatternRows
