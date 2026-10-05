import Mettapedia.Languages.MM0.Presentation.FreshDummiesProgram

/-! # The authored freshness traversal checks complete occurrence support -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freshProgram
local notation "H" => computationalHost

theorem fresh_for_computes (target : Context) (image : Nat) (expression : Preterm) :
    Applies P H "mm0:fresh-for" [encodeContext target, natural image, encode expression]
      (boolean (Preterm.checkFreshFor target image expression)) := by
  refine Applies.equation (equation := P[79])
    (environment := [("target", encodeContext target), ("image", natural image), ("expression", encode expression)])
    (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ((natural_passive _ _ 0).evaluates _)
      (.cons (.variable (by rfl)) (.cons ((encodeBinder_passive _ _ (.regular 0 ∅)).evaluates _)
        (.cons ((natural_passive _ _ 0).evaluates _) (.cons (.variable (by rfl)) .nil))))))
    (pair_reused target image expression)

theorem fresh_for_accepts_iff (target : Context) (image : Nat) (expression : Preterm) :
    Applies P H "mm0:fresh-for" [encodeContext target, natural image, encode expression] (.sym "True") ↔
      Preterm.FreshFor target image expression := by
  rw [← Preterm.checkFreshFor_iff]
  constructor
  · intro run
    have same := run.deterministic (fresh_for_computes target image expression)
    cases checked : Preterm.checkFreshFor target image expression with
    | false => simp [checked, boolean] at same
    | true => rfl
  · intro checked
    simpa only [checked, boolean, ↓reduceIte] using fresh_for_computes target image expression

private theorem all_start (target : Context) (image : Nat) (arguments : List Preterm) (result : Term)
    (next : Applies P H "mm0:fresh-all-view"
      [listView (arguments.map encode), encodeContext target, natural image] result) :
    Applies P H "mm0:fresh-all" [encodeContext target, natural image, encodeExpressions arguments] result := by
  refine Applies.equation (equation := P[80])
    (environment := [("target", encodeContext target), ("image", natural image), ("arguments", encodeExpressions arguments)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem all_cons (target : Context) (image : Nat) (expression : Preterm)
    (arguments : List Preterm) (result : Term)
    (next : Applies P H "mm0:fresh-all-next"
      [boolean (Preterm.checkFreshFor target image expression), encodeContext target, natural image,
        encodeExpressions arguments] result) :
    Applies P H "mm0:fresh-all-view"
      [listView ((expression :: arguments).map encode), encodeContext target, natural image] result := by
  refine Applies.equation (equation := P[82])
    (environment := [("expression", encode expression), ("arguments", encodeExpressions arguments),
      ("target", encodeContext target), ("image", natural image)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (fresh_for_computes target image expression)

private theorem all_next (target : Context) (image : Nat) (arguments : List Preterm) (result : Term)
    (next : Applies P H "mm0:fresh-all" [encodeContext target, natural image, encodeExpressions arguments] result) :
    Applies P H "mm0:fresh-all-next"
      [.sym "True", encodeContext target, natural image, encodeExpressions arguments] result := by
  refine Applies.equation (equation := P[84])
    (environment := [("target", encodeContext target), ("image", natural image), ("arguments", encodeExpressions arguments)])
    (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next

theorem fresh_all_computes (target : Context) (image : Nat) (arguments : List Preterm) :
    Applies P H "mm0:fresh-all" [encodeContext target, natural image, encodeExpressions arguments]
      (boolean (arguments.all (Preterm.checkFreshFor target image))) := by
  induction arguments with
  | nil => exact all_start target image [] _ ⟨1, rfl⟩
  | cons expression arguments ih =>
      apply all_start
      apply all_cons
      cases checked : Preterm.checkFreshFor target image expression with
      | false => simp only [List.all_cons, checked, Bool.false_and, boolean]; exact ⟨1, rfl⟩
      | true =>
          simp only [List.all_cons, checked, Bool.true_and, boolean]
          exact all_next target image arguments _ ih

theorem fresh_all_accepts_iff (target : Context) (image : Nat) (arguments : List Preterm) :
    Applies P H "mm0:fresh-all" [encodeContext target, natural image, encodeExpressions arguments] (.sym "True") ↔
      ∀ expression ∈ arguments, Preterm.FreshFor target image expression := by
  have exactResult (result : Term) :
      Applies P H "mm0:fresh-all" [encodeContext target, natural image, encodeExpressions arguments] result ↔
      result = boolean (arguments.all (Preterm.checkFreshFor target image)) := by
    constructor
    · exact fun run => run.deterministic (fresh_all_computes target image arguments)
    · rintro rfl; exact fresh_all_computes target image arguments
  rw [exactResult]
  have truth (b : Bool) : Term.sym "True" = boolean b ↔ b = true := by cases b <;> simp [boolean]
  rw [truth, List.all_eq_true]
  simp only [Preterm.checkFreshFor_iff]

end Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies
