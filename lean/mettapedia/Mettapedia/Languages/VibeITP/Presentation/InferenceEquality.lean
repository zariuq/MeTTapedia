import Mettapedia.Languages.VibeITP.Presentation.InferenceProgram

/-!
# Exact authored structural equality

The comparison executes the declared equations. It compares allocation
identities, literal bytes and every ordered argument. The result agrees with
the independent kernel's structural equality, including different lengths and
repeated children; it does not use a guest equality primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInference

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInstantiation
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => inferenceProgram
local notation "A" => inferenceEquations
local notation "H" => computationalHost

private theorem symbol_applies (left right : Spec.SymId) :
    Applies P H "vibe:symbol-eq" [encodeSymbol left, encodeSymbol right]
      (boolean (decide (left = right))) := by
  apply reuse_instantiation_call (by decide +kernel)
  apply reuse_substitution_call (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations H substitutionEquations_disjoint
    "vibe:symbol-eq" (by decide +kernel) _ _).mpr
  exact symbol_computes left right

private theorem eq_applies (left right : Nat) :
    Applies P H "nik:nat-eq" [natural left, natural right] (boolean (decide (left = right))) :=
  reuse_instantiation_call (by decide +kernel)
    (.primitive (by rfl) (naturalArithmeticHost_eq left right))

private theorem view_applies (items : List Term) :
    Applies P H "nik:list-view" [.list items] (listView items) :=
  reuse_instantiation_call (by decide +kernel)
    (.primitive (by rfl) (computationalHost_list_view items))

private theorem bytes_start (left right : List UInt8) (result : Bool)
    (viewed : Applies P H "vibe:bytes-eq-view"
      [listView (left.map encodeByte), listView (right.map encodeByte)] (boolean result)) :
    Applies P H "vibe:bytes-eq" [.list (left.map encodeByte), .list (right.map encodeByte)]
      (boolean result) := by
  refine inference_equation (equation := A[12])
    (environment := [("left", .list (left.map encodeByte)), ("right", .list (right.map encodeByte))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) viewed
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)

private theorem bytes_first (equal rest : Bool) (left right : List UInt8)
    (tail : Applies P H "vibe:bytes-eq" [.list (left.map encodeByte), .list (right.map encodeByte)]
      (boolean rest)) :
    Applies P H "vibe:bytes-eq-first" [boolean equal, .list (left.map encodeByte), .list (right.map encodeByte)]
      (boolean (equal && rest)) := by
  cases equal with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[17])
        (environment := [("left", .list (left.map encodeByte)), ("right", .list (right.map encodeByte))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

theorem bytes_equality_computes (left right : List UInt8) :
    Applies P H "vibe:bytes-eq" [.list (left.map encodeByte), .list (right.map encodeByte)]
      (boolean (decide (left = right))) := by
  apply bytes_start
  cases left with
  | nil => cases right <;> exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | cons first rest =>
      cases right with
      | nil => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | cons second tail =>
          refine inference_equation (equation := A[14])
            (environment := [("left", encodeByte first), ("left-rest", .list (rest.map encodeByte)),
              ("right", encodeByte second), ("right-rest", .list (tail.map encodeByte))])
            (by decide +kernel) (by rfl) (by rfl) ?_
          refine Evaluates.call (values := [boolean (decide (first.toNat = second.toNat)),
              .list (rest.map encodeByte), .list (tail.map encodeByte)]) (by simp [Special])
            (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (eq_applies _ _)
          · simpa only [UInt8.toNat_inj, List.cons.injEq, Bool.decide_and] using
              bytes_first (decide (first.toNat = second.toNat)) (decide (rest = tail)) rest tail
                (bytes_equality_computes rest tail)

private theorem terms_start (left right : List Spec.Term) (result : Bool)
    (viewed : Applies P H "vibe:terms-eq-view"
      [listView (encodeTerms left), listView (encodeTerms right)] (boolean result)) :
    Applies P H "vibe:terms-eq" [.list (encodeTerms left), .list (encodeTerms right)]
      (boolean result) := by
  refine inference_equation (equation := A[6])
    (environment := [("left", .list (encodeTerms left)), ("right", .list (encodeTerms right))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) viewed
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies _)

private theorem terms_first (equal rest : Bool) (left right : List Spec.Term)
    (tail : Applies P H "vibe:terms-eq" [.list (encodeTerms left), .list (encodeTerms right)] (boolean rest)) :
    Applies P H "vibe:terms-eq-first" [boolean equal, .list (encodeTerms left), .list (encodeTerms right)]
      (boolean (equal && rest)) := by
  cases equal with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[11])
        (environment := [("left", .list (encodeTerms left)), ("right", .list (encodeTerms right))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

private theorem term_app_start (leftHead rightHead : Spec.SymId) (left right : List Spec.Term) (result : Bool)
    (compared : Applies P H "vibe:term-eq-head"
      [boolean (decide (leftHead = rightHead)), .list (encodeTerms left), .list (encodeTerms right)]
      (boolean result)) :
    Applies P H "vibe:term-eq" [encode (.app leftHead left), encode (.app rightHead right)]
      (boolean result) := by
  refine inference_equation (equation := A[2])
    (environment := [("left-head", encodeSymbol leftHead), ("left-args", .list (encodeTerms left)),
      ("right-head", encodeSymbol rightHead), ("right-args", .list (encodeTerms right))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) compared
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (symbol_applies _ _)

private theorem term_app_head (equal rest : Bool) (left right : List Spec.Term)
    (compared : Applies P H "vibe:terms-eq" [.list (encodeTerms left), .list (encodeTerms right)] (boolean rest)) :
    Applies P H "vibe:term-eq-head" [boolean equal, .list (encodeTerms left), .list (encodeTerms right)]
      (boolean (equal && rest)) := by
  cases equal with
  | false => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine inference_equation (equation := A[5])
        (environment := [("left", .list (encodeTerms left)), ("right", .list (encodeTerms right))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) compared

mutual

theorem term_equality_computes (left right : Spec.Term) :
    Applies P H "vibe:term-eq" [encode left, encode right] (boolean (decide (left = right))) := by
  cases left with
  | bvar first =>
      cases right with
      | bvar second =>
          refine inference_equation (equation := A[0])
            (environment := [("i", natural first), ("j", natural second)]) (by decide +kernel) (by rfl) (by rfl) ?_
          exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (by simpa only [Spec.Term.bvar.injEq] using eq_applies first second)
      | lit _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | app _ _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | lit first =>
      cases right with
      | bvar _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | lit second =>
          refine inference_equation (equation := A[1])
            (environment := [("left", .list (first.map encodeByte)), ("right", .list (second.map encodeByte))])
            (by decide +kernel) (by rfl) (by rfl) ?_
          exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (by simpa only [Spec.Term.lit.injEq] using bytes_equality_computes first second)
      | app _ _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | app firstHead firstArgs =>
      cases right with
      | bvar _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | lit _ => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | app secondHead secondArgs =>
          apply term_app_start
          simpa only [Spec.Term.app.injEq, Bool.decide_and] using
            term_app_head (decide (firstHead = secondHead)) (decide (firstArgs = secondArgs)) firstArgs secondArgs
              (terms_equality_computes firstArgs secondArgs)

theorem terms_equality_computes (left right : List Spec.Term) :
    Applies P H "vibe:terms-eq" [.list (encodeTerms left), .list (encodeTerms right)]
      (boolean (decide (left = right))) := by
  apply terms_start
  cases left with
  | nil => cases right <;> exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
  | cons first rest =>
      cases right with
      | nil => exact ⟨1, by rw [inference_apply _ (by decide +kernel)]; rfl⟩
      | cons second tail =>
          refine inference_equation (equation := A[8])
            (environment := [("left", encode first), ("left-rest", .list (encodeTerms rest)),
              ("right", encode second), ("right-rest", .list (encodeTerms tail))])
            (by decide +kernel) (by rfl) (by rfl) ?_
          refine Evaluates.call (values := [boolean (decide (first = second)),
              .list (encodeTerms rest), .list (encodeTerms tail)]) (by simp [Special])
            (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
          · exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (term_equality_computes _ _)
          · simpa only [List.cons.injEq, Bool.decide_and] using
              terms_first (decide (first = second)) (decide (rest = tail)) rest tail
                (terms_equality_computes rest tail)

end

theorem term_equality_result_exact (left right : Spec.Term) (result : Term) :
    Applies P H "vibe:term-eq" [encode left, encode right] result ↔
      result = boolean (decide (left = right)) := by
  constructor
  · intro compared
    exact compared.deterministic (term_equality_computes left right)
  · intro same
    subst result
    exact term_equality_computes left right

theorem term_equality_accepts_iff (left right : Spec.Term) :
    Applies P H "vibe:term-eq" [encode left, encode right] (.sym "True") ↔ left = right := by
  rw [term_equality_result_exact]
  by_cases same : left = right <;> simp [same, boolean]

theorem term_equality_refuses_iff (left right : Spec.Term) :
    Applies P H "vibe:term-eq" [encode left, encode right] (.sym "False") ↔ left ≠ right := by
  rw [term_equality_result_exact]
  by_cases same : left = right <;> simp [same, boolean]

theorem term_equality_completed_exact (left right : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:term-eq" [encode left, encode right] ≠ .exhausted) :
    apply P H fuel "vibe:term-eq" [encode left, encode right] = .value (boolean (decide (left = right))) :=
  (term_equality_computes left right).completed fuel finished

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInference
