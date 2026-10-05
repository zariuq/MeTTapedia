import Mettapedia.Languages.MM0.Presentation.FreshnessCorrespondence

/-!
# Correspondence of authored MM0 dummy admission

The computation checks exact arity, bound-variable sorts and freshness against
the original arguments and all earlier dummy images. It computes its answer;
the caller supplies no freshness derivation or traversal trace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freshProgram
local notation "H" => computationalHost

private theorem bound_computes (target : Context) (image sort : Nat) :
    Applies P H "mm0:check-binder"
      [encodeTable [], encodeContext target, encode (.var image), encodeBinder (.bound sort)]
      (boolean (decide (target[image]? = some (.bound sort)))) := by
  have run := arguments_reused "mm0:check-binder" (by decide) _ _
    (binder_computes [] target (.var image) (.bound sort))
  cases lookup : target[image]? with
  | none => simpa [Preterm.checkBinder, Preterm.boundSort?, lookup] using run
  | some binder => cases binder <;> simpa [Preterm.checkBinder, Preterm.boundSort?, lookup] using run

private theorem dummies_start (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (result : Term) (next : Applies P H "mm0:dummies-view"
      [listView (sorts.map natural), listView (images.map natural), encodeContext target, encodeExpressions arguments] result) :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] result := by
  refine Applies.equation (equation := P[85])
    (environment := [("target", encodeContext target), ("arguments", encodeExpressions arguments),
      ("sorts", encodeNaturals sorts), ("images", encodeNaturals images)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))

private theorem dummies_cons (target : Context) (arguments : List Preterm) (sort image : Nat)
    (sorts images : List Nat) (result : Term)
    (next : Applies P H "mm0:dummy-sort"
      [boolean (decide (target[image]? = some (.bound sort))), encodeContext target, encodeExpressions arguments,
        encodeNaturals sorts, encodeNaturals images, natural image] result) :
    Applies P H "mm0:dummies-view"
      [listView ((sort :: sorts).map natural), listView ((image :: images).map natural),
        encodeContext target, encodeExpressions arguments] result := by
  refine Applies.equation (equation := P[89])
    (environment := [("sort", natural sort), ("sorts", encodeNaturals sorts), ("image", natural image),
      ("images", encodeNaturals images), ("target", encodeContext target), ("arguments", encodeExpressions arguments)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  refine Evaluates.call (by simp [Special])
    (.cons ⟨1, rfl⟩ (.cons (.variable (by rfl)) (.cons ?_ (.cons ⟨2, rfl⟩ .nil))))
    (bound_computes target image sort)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.constructor (by rfl) (by rfl))

private theorem sort_admitted (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (image : Nat) (result : Term)
    (next : Applies P H "mm0:dummy-fresh"
      [boolean (arguments.all (Preterm.checkFreshFor target image)), encodeContext target, encodeExpressions arguments,
        encodeNaturals sorts, encodeNaturals images, natural image] result) :
    Applies P H "mm0:dummy-sort"
      [.sym "True", encodeContext target, encodeExpressions arguments,
        encodeNaturals sorts, encodeNaturals images, natural image] result := by
  refine Applies.equation (equation := P[91])
    (environment := [("target", encodeContext target), ("arguments", encodeExpressions arguments),
      ("sorts", encodeNaturals sorts), ("images", encodeNaturals images), ("image", natural image)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (fresh_all_computes target image arguments)

private theorem fresh_admitted (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (image : Nat) (result : Term)
    (next : Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions (arguments ++ [.var image]), encodeNaturals sorts, encodeNaturals images]
      result) :
    Applies P H "mm0:dummy-fresh"
      [.sym "True", encodeContext target, encodeExpressions arguments,
        encodeNaturals sorts, encodeNaturals images, natural image] result := by
  refine Applies.equation (equation := P[93])
    (environment := [("target", encodeContext target), ("arguments", encodeExpressions arguments),
      ("sorts", encodeNaturals sorts), ("images", encodeNaturals images), ("image", natural image)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  have appended := append_reused (arguments.map encode) [encode (.var image)]
  simp only [← List.map_singleton, ← List.map_append] at appended
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) appended
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ⟨1, rfl⟩ .nil))
    (.primitive (by rfl) (computationalHost_list_cons _ []))
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.constructor (by rfl) (by rfl))

theorem dummies_computes (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images]
      (boolean (Definition.checkDummies target arguments sorts images)) := by
  induction sorts generalizing arguments images with
  | nil =>
      cases images with
      | nil => exact dummies_start target arguments [] [] _ ⟨1, rfl⟩
      | cons image images => exact dummies_start target arguments [] (image :: images) _ ⟨1, rfl⟩
  | cons sort sorts ih =>
      cases images with
      | nil => exact dummies_start target arguments (sort :: sorts) [] _ ⟨1, rfl⟩
      | cons image images =>
          apply dummies_start
          apply dummies_cons
          by_cases typed : target[image]? = some (.bound sort)
          · simp only [typed, decide_true, boolean]
            apply sort_admitted
            cases fresh : arguments.all (Preterm.checkFreshFor target image) with
            | false => simp only [Definition.checkDummies, typed, decide_true, fresh,
                Bool.and_false, Bool.false_and, boolean]; exact ⟨1, rfl⟩
            | true =>
                simp only [Definition.checkDummies, typed, decide_true, fresh, Bool.true_and, boolean]
                exact fresh_admitted target arguments sorts images image _ (ih _ _)
          · simp only [Definition.checkDummies, typed, decide_false, Bool.false_and, boolean]
            exact ⟨1, rfl⟩

theorem dummies_result_exact (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (result : Term) :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] result ↔
      result = boolean (Definition.checkDummies target arguments sorts images) := by
  constructor
  · exact fun run => run.deterministic (dummies_computes target arguments sorts images)
  · rintro rfl; exact dummies_computes target arguments sorts images

theorem dummies_accepts_iff (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] (.sym "True") ↔
      Definition.FreshDummies target arguments sorts images := by
  rw [dummies_result_exact, ← Definition.checkDummies_iff]
  cases Definition.checkDummies target arguments sorts images <;> simp [boolean]

theorem dummies_refuses_iff (target : Context) (arguments : List Preterm) (sorts images : List Nat) :
    Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] (.sym "False") ↔
      ¬ Definition.FreshDummies target arguments sorts images := by
  rw [dummies_result_exact, ← Definition.checkDummies_iff]
  cases Definition.checkDummies target arguments sorts images <;> simp [boolean]

theorem admitted_images_are_distinct (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (run : Applies P H "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] (.sym "True")) :
    images.Nodup := ((dummies_accepts_iff target arguments sorts images).mp run).distinct

theorem dummies_completed_result (target : Context) (arguments : List Preterm) (sorts images : List Nat)
    (fuel : Nat) (finished : apply P H fuel "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] ≠ .exhausted) :
    apply P H fuel "mm0:check-dummies"
      [encodeContext target, encodeExpressions arguments, encodeNaturals sorts, encodeNaturals images] =
      .value (boolean (Definition.checkDummies target arguments sorts images)) :=
  (dummies_computes target arguments sorts images).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies
