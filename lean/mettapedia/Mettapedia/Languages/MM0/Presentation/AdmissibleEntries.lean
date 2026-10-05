import Mettapedia.Languages.MM0.Presentation.AdmissibleProgram

/-!
# Exact indexed entries for the dependency matrix

The authored traversal pairs formal binders with supplied expressions in order
and retains their unbounded natural positions. It computes zip followed by
indexed enumeration, including the truncated result on unequal lists. The
full admissibility operation checks exact arity before using these entries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible

open Kernel ComputationalContext ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissibleProgram
local notation "H" => computationalHost

private theorem entries_start (formal : Context) (expressions : List Preterm) (index : Nat) (result : Term)
    (next : Applies P H "mm0:entries-view"
      [listView (formal.map encodeBinder), listView (expressions.map encode), natural index] result) :
    Applies P H "mm0:entries" [encodeContext formal, encodeExpressions expressions, natural index] result := by
  refine Applies.equation (equation := P[79])
    (environment := [("formal", encodeContext formal), ("expressions", encodeExpressions expressions),
      ("index", natural index)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) .nil))) next
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
      (.primitive (by rfl) (computationalHost_list_view _))

private theorem entries_cons (binder : Kernel.Binder) (formal : Context)
    (expression : Preterm) (expressions : List Preterm) (index : Nat) (rest : List Substitution.Entry)
    (child : Applies P H "mm0:entries" [encodeContext formal, encodeExpressions expressions, natural (index + 1)]
      (encodeEntries rest)) :
    Applies P H "mm0:entries-view"
      [listView ((binder :: formal).map encodeBinder), listView ((expression :: expressions).map encode), natural index]
      (encodeEntries (((binder, expression), index) :: rest)) := by
  refine Applies.equation (equation := P[82])
    (environment := [("binder", encodeBinder binder), ("formal", encodeContext formal),
      ("expression", encode expression), ("expressions", encodeExpressions expressions), ("index", natural index)])
      (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil))
    (.primitive (by rfl) (computationalHost_list_cons (encodeEntry ((binder, expression), index)) (rest.map encodeEntry)))
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
      (.constructor (by rfl) (by rfl))
  · refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ .nil))) child
    exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ⟨1, rfl⟩ .nil))
      (.primitive (by rfl) (computationalHost_binary (operation := .add) rfl index 1 (by decide) (by decide)))

theorem indexed_entries_computes (formal : Context) (expressions : List Preterm) (index : Nat) :
    Applies P H "mm0:entries" [encodeContext formal, encodeExpressions expressions, natural index]
      (encodeEntries ((formal.zip expressions).zipIdx index)) := by
  induction formal generalizing expressions index with
  | nil => exact entries_start [] expressions index _ ⟨1, rfl⟩
  | cons binder formal ih =>
    refine entries_start (binder :: formal) expressions index _ ?_
    cases expressions with
    | nil => exact ⟨1, rfl⟩
    | cons expression expressions => exact entries_cons binder formal expression expressions index _ (ih _ _)

theorem entries_computes (formal : Context) (expressions : List Preterm) :
    Applies P H "mm0:entries" [encodeContext formal, encodeExpressions expressions, natural 0]
      (encodeEntries (Substitution.entries formal expressions)) :=
  indexed_entries_computes formal expressions 0

theorem entries_result_exact (formal : Context) (expressions : List Preterm) (index : Nat) (result : Term) :
    Applies P H "mm0:entries" [encodeContext formal, encodeExpressions expressions, natural index] result ↔
      result = encodeEntries ((formal.zip expressions).zipIdx index) := by
  constructor
  · exact fun run => run.deterministic (indexed_entries_computes formal expressions index)
  · rintro rfl
    exact indexed_entries_computes formal expressions index

theorem entry_order_is_retained :
    Applies P H "mm0:entries"
      [encodeContext [.regular 1 ∅, .bound 0], encodeExpressions [.term 4, .var 2], natural 0]
      (encodeEntries [((.regular 1 ∅, .term 4), 0), ((.bound 0, .var 2), 1)]) :=
  entries_computes _ _

theorem entry_indices_do_not_wrap :
    Applies P H "mm0:entries"
      [encodeContext [.bound 0, .bound 0], encodeExpressions [.var 1, .var 0], natural 18446744073709551615]
      (encodeEntries [((.bound 0, .var 1), 18446744073709551615), ((.bound 0, .var 0), 18446744073709551616)]) :=
  indexed_entries_computes _ _ _

theorem entry_truncation_is_not_arity_validation :
    Applies P H "mm0:entries" [encodeContext [.bound 0], encodeExpressions [], natural 0] (encodeEntries []) ∧
      Substitution.checkArguments (fun _ => none) [] [] [.bound 0] = false :=
  ⟨entries_computes _ _, rfl⟩

end Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible
