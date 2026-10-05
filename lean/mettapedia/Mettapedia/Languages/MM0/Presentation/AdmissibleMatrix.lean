import Mettapedia.Languages.MM0.Presentation.AdmissibleEntries

/-!
# Complete dependency-matrix traversal

Every bound image is checked against every supplied entry. The complete entry
list is retained separately from the remaining traversal, so an earlier
regular image is still constrained by a later bound image. Successful finite
runs compute the independent pair, row and complete-matrix Boolean checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible

open Kernel ComputationalContext ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissibleProgram
local notation "H" => computationalHost

private theorem pairs_start (target : Context) (formalBound targetBound : Nat)
    (entries : List Substitution.Entry) (result : Term)
    (next : Applies P H "mm0:pairs-view"
      [listView (entries.map encodeEntry), encodeContext target, natural formalBound, natural targetBound] result) :
    Applies P H "mm0:check-pairs"
      [encodeContext target, natural formalBound, natural targetBound, encodeEntries entries] result := by
  refine Applies.equation (equation := P[83])
    (environment := [("target", encodeContext target), ("formal-bound", natural formalBound),
      ("target-bound", natural targetBound), ("entries", encodeEntries entries)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem pairs_cons (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) (rest : List Substitution.Entry) (result : Term)
    (next : Applies P H "mm0:pairs-next"
      [boolean (Substitution.checkPair target formalBound targetBound ((binder, expression), position)),
        encodeContext target, natural formalBound, natural targetBound, encodeEntries rest] result) :
    Applies P H "mm0:pairs-view"
      [listView ((((binder, expression), position) :: rest).map encodeEntry), encodeContext target,
        natural formalBound, natural targetBound] result := by
  refine Applies.equation (equation := P[85])
    (environment := [("binder", encodeBinder binder), ("expression", encode expression), ("position", natural position),
      ("rest", encodeEntries rest), ("target", encodeContext target), ("formal-bound", natural formalBound),
      ("target-bound", natural targetBound)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))
    (pair_reused target formalBound targetBound binder position expression)

private theorem pairs_next (target : Context) (formalBound targetBound : Nat)
    (rest : List Substitution.Entry) (result : Term)
    (next : Applies P H "mm0:check-pairs"
      [encodeContext target, natural formalBound, natural targetBound, encodeEntries rest] result) :
    Applies P H "mm0:pairs-next"
      [.sym "True", encodeContext target, natural formalBound, natural targetBound, encodeEntries rest] result := by
  refine Applies.equation (equation := P[87])
    (environment := [("target", encodeContext target), ("formal-bound", natural formalBound),
      ("target-bound", natural targetBound), ("rest", encodeEntries rest)]) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next

theorem pairs_computes (target : Context) (formalBound targetBound : Nat) (entries : List Substitution.Entry) :
    Applies P H "mm0:check-pairs"
      [encodeContext target, natural formalBound, natural targetBound, encodeEntries entries]
      (boolean (entries.all (Substitution.checkPair target formalBound targetBound))) := by
  induction entries with
  | nil => exact pairs_start target formalBound targetBound [] _ ⟨1, rfl⟩
  | cons entry rest ih =>
    obtain ⟨⟨binder, expression⟩, position⟩ := entry
    refine pairs_start target formalBound targetBound _ _
      (pairs_cons target formalBound targetBound binder position expression rest _ ?_)
    cases checked : Substitution.checkPair target formalBound targetBound ((binder, expression), position) with
    | false => simp only [List.all_cons, checked, Bool.false_and]; exact ⟨1, rfl⟩
    | true =>
      simp only [List.all_cons, checked, Bool.true_and]
      exact pairs_next target formalBound targetBound rest _ ih

theorem row_computes (target : Context) (allEntries : List Substitution.Entry) (entry : Substitution.Entry) :
    Applies P H "mm0:check-row" [encodeContext target, encodeEntries allEntries, encodeEntry entry]
      (boolean (Substitution.checkRow target allEntries entry)) := by
  obtain ⟨⟨binder, expression⟩, position⟩ := entry
  cases binder with
  | regular sort dependencies => exact ⟨1, rfl⟩
  | bound sort =>
    cases expression with
    | term symbol => exact ⟨1, rfl⟩
    | app function argument => exact ⟨1, rfl⟩
    | var image =>
      refine Applies.equation (equation := P[88])
        (environment := [("target", encodeContext target), ("all", encodeEntries allEntries),
          ("sort", natural sort), ("image", natural image), ("position", natural position)]) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (pairs_computes target position image allEntries)

private theorem rows_start (target : Context) (allEntries entries : List Substitution.Entry) (result : Term)
    (next : Applies P H "mm0:rows-view"
      [listView (entries.map encodeEntry), encodeContext target, encodeEntries allEntries] result) :
    Applies P H "mm0:check-rows" [encodeContext target, encodeEntries allEntries, encodeEntries entries] result := by
  refine Applies.equation (equation := P[92])
    (environment := [("target", encodeContext target), ("all", encodeEntries allEntries),
      ("entries", encodeEntries entries)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem rows_cons (target : Context) (allEntries : List Substitution.Entry)
    (entry : Substitution.Entry) (rest : List Substitution.Entry) (result : Term)
    (next : Applies P H "mm0:rows-next"
      [boolean (Substitution.checkRow target allEntries entry), encodeContext target,
        encodeEntries allEntries, encodeEntries rest] result) :
    Applies P H "mm0:rows-view"
      [listView ((entry :: rest).map encodeEntry), encodeContext target, encodeEntries allEntries] result := by
  refine Applies.equation (equation := P[94])
    (environment := [("entry", encodeEntry entry), ("rest", encodeEntries rest),
      ("target", encodeContext target), ("all", encodeEntries allEntries)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
    (row_computes target allEntries entry)

private theorem rows_next (target : Context) (allEntries rest : List Substitution.Entry) (result : Term)
    (next : Applies P H "mm0:check-rows" [encodeContext target, encodeEntries allEntries, encodeEntries rest] result) :
    Applies P H "mm0:rows-next"
      [.sym "True", encodeContext target, encodeEntries allEntries, encodeEntries rest] result := by
  refine Applies.equation (equation := P[96])
    (environment := [("target", encodeContext target), ("all", encodeEntries allEntries), ("rest", encodeEntries rest)])
      (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next

theorem rows_computes (target : Context) (allEntries entries : List Substitution.Entry) :
    Applies P H "mm0:check-rows" [encodeContext target, encodeEntries allEntries, encodeEntries entries]
      (boolean (entries.all (Substitution.checkRow target allEntries))) := by
  induction entries with
  | nil => exact rows_start target allEntries [] _ ⟨1, rfl⟩
  | cons entry rest ih =>
    refine rows_start target allEntries _ _ (rows_cons target allEntries entry rest _ ?_)
    cases checked : Substitution.checkRow target allEntries entry with
    | false => simp only [List.all_cons, checked, Bool.false_and]; exact ⟨1, rfl⟩
    | true =>
      simp only [List.all_cons, checked, Bool.true_and]
      exact rows_next target allEntries rest _ ih

theorem rows_result_exact (target : Context) (allEntries entries : List Substitution.Entry) (result : Term) :
    Applies P H "mm0:check-rows" [encodeContext target, encodeEntries allEntries, encodeEntries entries] result ↔
      result = boolean (entries.all (Substitution.checkRow target allEntries)) := by
  constructor
  · exact fun run => run.deterministic (rows_computes target allEntries entries)
  · rintro rfl
    exact rows_computes target allEntries entries

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible
