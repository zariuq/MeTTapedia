import Mettapedia.Languages.VibeITP.Presentation.SubstitutionProgram

/-!
# Authored simultaneous bound-variable substitution

The equation program traverses raw terms and replacement lists. Its finite
computations agree with the independent kernel, including default lookup,
reverse parameter order, pruning and each binder/word refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => substitutionProgram
local notation "A" => substitutionEquations
local notation "H" => computationalHost

private theorem add_applies (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  .primitive (by rfl) (naturalArithmeticHost_add left right)

private theorem monus_applies (left right : Nat) :
    Applies P H "nik:nat-monus" [natural left, natural right] (natural (left - right)) :=
  .primitive (by rfl) (naturalArithmeticHost_monus left right)

private theorem le_applies (left right : Nat) :
    Applies P H "nik:nat-le" [natural left, natural right] (boolean (decide (left ≤ right))) :=
  .primitive (by rfl) (naturalArithmeticHost_le left right)

private theorem lt_applies (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  .primitive (by rfl) (naturalArithmeticHost_lt left right)

private theorem zero_applies (value : Nat) :
    Applies P H "nik:nat-zero" [natural value] (.sym (if value = 0 then "True" else "False")) :=
  .primitive (by rfl) (computationalHost_zero value)

private theorem pred_applies (value : Nat) :
    Applies P H "nik:nat-pred" [natural value] (natural value.pred) :=
  .primitive (by rfl) (computationalHost_pred value)

private theorem view_applies (values : List Term) :
    Applies P H "nik:list-view" [.list values] (listView values) :=
  .primitive (by rfl) (computationalHost_list_view values)

private theorem length_start (values : List Term) (result : Nat)
    (next : Applies P H "vibe:length-view" [listView values] (natural result)) :
    Applies P H "vibe:list-length" [.list values] (natural result) := by
  refine Applies.equation (equation := A[0]) (environment := [("values", .list values)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies values)

private theorem length_cons (first : Term) (rest : List Term) (length : Nat)
    (tail : Applies P H "vibe:list-length" [.list rest] (natural length)) :
    Applies P H "vibe:length-view" [listView (first :: rest)] (natural (length + 1)) := by
  refine Applies.equation (equation := A[2])
    (environment := [("first", first), ("rest", .list rest)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.literal _ _ _ _) .nil)) (add_applies length 1)
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) tail

theorem listLength_computes (values : List Term) :
    Applies P H "vibe:list-length" [.list values] (natural values.length) := by
  induction values with
  | nil => exact length_start [] 0 ⟨1, rfl⟩
  | cons first rest ih => exact length_start _ _ (length_cons first rest _ ih)

private theorem get_start (values : List Term) (index : Nat) (default result : Term)
    (next : Applies P H "vibe:get-view" [listView values, natural index, default] result) :
    Applies P H "vibe:get-default" [.list values, natural index, default] result := by
  refine Applies.equation (equation := A[3])
    (environment := [("values", .list values), ("index", natural index), ("default", default)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies values)

private theorem get_cons (first : Term) (rest : List Term) (index : Nat) (default result : Term)
    (next : Applies P H "vibe:get-zero"
      [.sym (if index = 0 then "True" else "False"), first, .list rest, natural index, default] result) :
    Applies P H "vibe:get-view" [listView (first :: rest), natural index, default] result := by
  refine Applies.equation (equation := A[5])
    (environment := [("first", first), ("rest", .list rest), ("index", natural index), ("default", default)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (zero_applies index)

private theorem get_next (first : Term) (rest : List Term) (index : Nat) (default result : Term)
    (tail : Applies P H "vibe:get-default" [.list rest, natural index, default] result) :
    Applies P H "vibe:get-zero" [.sym "False", first, .list rest, natural (index + 1), default] result := by
  refine Applies.equation (equation := A[7])
    (environment := [("first", first), ("rest", .list rest), ("index", natural (index + 1)), ("default", default)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) .nil))) tail
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (pred_applies (index + 1))

/-- Lookup treats list elements as supplied values, never recursively executing them. -/
theorem getDefault_computes (values : List Term) (index : Nat) (default : Term) :
    Applies P H "vibe:get-default" [.list values, natural index, default] (values.getD index default) := by
  induction values generalizing index with
  | nil => exact get_start [] index default _ ⟨1, rfl⟩
  | cons first rest ih =>
      apply get_start
      apply get_cons
      cases index with
      | zero => exact ⟨1, rfl⟩
      | succ index => exact get_next first rest index default _ (ih index)

theorem encodeTerms_getD (values : List Spec.Term) (index : Nat) (default : Spec.Term) :
    (encodeTerms values).getD index (encode default) = encode (values.getD index default) := by
  induction values generalizing index with
  | nil => rfl
  | cons first rest ih => cases index with
    | zero => rfl
    | succ index => exact ih index

private theorem bvar_start (table : SignatureTable) (count offset index : Nat)
    (images : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-bvar-low"
      [boolean (decide (index + 1 ≤ offset)), encodeTable table, natural count,
        .list (encodeTerms images), natural offset, natural index] result) :
    Applies P H "vibe:subst-go"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset, encode (.bvar index)] result := by
  refine Applies.equation (equation := A[11])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("i", natural index)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) (le_applies (index + 1) offset)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (add_applies index 1)

private theorem bvar_high (table : SignatureTable) (count offset index : Nat)
    (images : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-bvar-param"
      [boolean (decide (index - offset < count)), encodeTable table, natural count,
        .list (encodeTerms images), natural offset, natural (index - offset)] result) :
    Applies P H "vibe:subst-bvar-low"
      [.sym "False", encodeTable table, natural count, .list (encodeTerms images),
        natural offset, natural index] result := by
  refine Applies.equation (equation := A[15])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("i", natural index)])
    (by rfl) (by rfl) ?_
  have relative : Evaluates P H [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("i", natural index)]
      (.expr [.sym "nik:nat-monus", .var "i", .var "offset"]) (natural (index - offset)) :=
    Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (monus_applies index offset)
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons relative .nil)))))) next
  exact Evaluates.call (by simp [Special])
    (.cons relative (.cons (.variable (by rfl)) .nil)) (lt_applies (index - offset) count)

private theorem bvar_parameter (table : SignatureTable) (count offset relative : Nat)
    (images : List Spec.Term) :
    Applies P H "vibe:subst-bvar-param"
      [.sym "True", encodeTable table, natural count, .list (encodeTerms images), natural offset, natural relative]
      (encodeResult (Spec.shift (signatureOf table) offset 0 (images.getD (count - 1 - relative) (.bvar 0)))) := by
  refine Applies.equation (equation := A[16])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("relative", natural relative)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil))))
    (shift_computes_in_substitution table offset 0 (images.getD (count - 1 - relative) (.bvar 0)))
  refine Evaluates.call (values := [.list (encodeTerms images), natural (count - 1 - relative), encode (.bvar 0)])
    (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ (.cons ?_ .nil))) ?_
  · refine Evaluates.call (by simp [Special])
      (.cons ?_ (.cons (.variable (by rfl)) .nil)) (monus_applies (count - 1) relative)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (monus_applies count 1)
  · exact (encoded_passive substitutionProgram_dataSeparated (.bvar 0)).evaluates _
  · simpa only [encodeTerms_getD] using
      getDefault_computes (encodeTerms images) (count - 1 - relative) (encode (.bvar 0))

private theorem bvar_above (table : SignatureTable) (count offset relative : Nat)
    (images : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-bvar-word"
      [boolean (decide (relative + 1 < Spec.wordBound)), natural relative] result) :
    Applies P H "vibe:subst-bvar-param"
      [.sym "False", encodeTable table, natural count, .list (encodeTerms images), natural offset, natural relative]
      result := by
  refine Applies.equation (equation := A[17])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("relative", natural relative)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.literal _ _ _ _) .nil))
    (lt_applies (relative + 1) Spec.wordBound)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (add_applies relative 1)

private theorem bvar_computes (table : SignatureTable) (count offset index : Nat) (images : List Spec.Term) :
    Applies P H "vibe:subst-go"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset, encode (.bvar index)]
      (encodeResult (Spec.substGo (signatureOf table) count images offset (.bvar index))) := by
  apply bvar_start
  by_cases low : index + 1 ≤ offset
  · simp only [Spec.substGo, low, boolean, decide_true, ↓reduceIte]
    exact ⟨3, rfl⟩
  · simp only [boolean, low, decide_false]
    apply bvar_high
    by_cases param : index - offset < count
    · simpa only [Spec.substGo, low, param, boolean, decide_true, ↓reduceIte] using
        bvar_parameter table count offset (index - offset) images
    · simp only [boolean, param, decide_false]
      apply bvar_above
      by_cases fits : index - offset + 1 < Spec.wordBound
      · simp only [Spec.substGo, low, param, fits, boolean, decide_true, ↓reduceIte]
        exact ⟨3, rfl⟩
      · simp only [Spec.substGo, low, param, fits, boolean, decide_false, ↓reduceIte]
        exact ⟨1, rfl⟩

private theorem app_start (table : SignatureTable) (count offset : Nat) (images : List Spec.Term)
    (symbol : Spec.SymId) (terms : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-app-closed"
      [boolean (decide (Spec.depth (signatureOf table) (.app symbol terms) ≤ offset)), encodeTable table,
        natural count, .list (encodeTerms images), natural offset, encodeSymbol symbol, .list (encodeTerms terms)]
      result) :
    Applies P H "vibe:subst-go"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset, encode (.app symbol terms)]
      result := by
  refine Applies.equation (equation := A[13])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset),
      ("symbol", encodeSymbol symbol), ("arguments", .list (encodeTerms terms))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (le_applies (Spec.depth (signatureOf table) (.app symbol terms)) offset)
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (depth_computes_in_substitution table (.app symbol terms))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (Applies.constructor (by rfl) (by rfl))

private theorem app_open (table : SignatureTable) (count offset : Nat) (images : List Spec.Term)
    (symbol : Spec.SymId) (terms : List Spec.Term) (result : Option (List Spec.Term))
    (arguments : Applies P H "vibe:subst-args"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders (bindersOf (signatureOf table) symbol), .list (encodeTerms terms)] (encodeTermsResult result)) :
    Applies P H "vibe:subst-app-closed"
      [.sym "False", encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeSymbol symbol, .list (encodeTerms terms)] (encodeResult (result.map (Spec.Term.app symbol))) := by
  refine Applies.equation (equation := A[21])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset),
      ("symbol", encodeSymbol symbol), ("arguments", .list (encodeTerms terms))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeSymbol symbol, encodeTermsResult result]) (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
  · refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) .nil)))))) arguments
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (binders_computes_in_substitution table symbol)
  · cases result with
    | none => exact ⟨1, rfl⟩
    | some terms' => exact ⟨3, rfl⟩

private theorem args_start (table : SignatureTable) (count offset : Nat) (images : List Spec.Term)
    (binders : List Nat) (terms : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-args-view"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, listView (encodeTerms terms)] result) :
    Applies P H "vibe:subst-args"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, .list (encodeTerms terms)] result := by
  refine Applies.equation (equation := A[24])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset),
      ("binders", encodeBinders binders), ("arguments", .list (encodeTerms terms))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ .nil)))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (encodeTerms terms))

private theorem args_cons (table : SignatureTable) (count offset : Nat) (images : List Spec.Term)
    (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-args-binder"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        listView (binders.map natural), encode first, .list (encodeTerms rest)] result) :
    Applies P H "vibe:subst-args-view"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, listView (encodeTerms (first :: rest))] result := by
  refine Applies.equation (equation := A[26])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("binders", encodeBinders binders),
      ("first", encode first), ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (binders.map natural))

private theorem args_binder (table : SignatureTable) (count offset : Nat) (images : List Spec.Term)
    (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-args-bound"
      [boolean (decide (offset + binders.headD 0 < Spec.wordBound)), encodeTable table, natural count,
        .list (encodeTerms images), natural offset, encodeBinders binders.tail,
        natural (offset + binders.headD 0), encode first, .list (encodeTerms rest)] result) :
    Applies P H "vibe:subst-args-binder"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        listView (binders.map natural), encode first, .list (encodeTerms rest)] result := by
  cases binders with
  | nil =>
      refine Applies.equation (equation := A[27])
        (environment := [("table", encodeTable table), ("count", natural count),
          ("images", .list (encodeTerms images)), ("offset", natural offset),
          ("first", encode first), ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (PassiveData.evaluates (.list (by simp)) _)
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (lt_applies offset Spec.wordBound)
  | cons bound tail =>
      refine Applies.equation (equation := A[28])
        (environment := [("table", encodeTable table), ("count", natural count),
          ("images", .list (encodeTerms images)), ("offset", natural offset),
          ("bound", natural bound), ("tail", encodeBinders tail),
          ("first", encode first), ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
      have sum : Evaluates P H [("table", encodeTable table), ("count", natural count),
          ("images", .list (encodeTerms images)), ("offset", natural offset),
          ("bound", natural bound), ("tail", encodeBinders tail),
          ("first", encode first), ("rest", .list (encodeTerms rest))]
          (.expr [.sym "nik:nat-add", .var "offset", .var "bound"]) (natural (offset + bound)) :=
        Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (add_applies offset bound)
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons sum (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons sum (.cons (.literal _ _ _ _) .nil)) (lt_applies (offset + bound) Spec.wordBound)

private theorem args_bound (table : SignatureTable) (count offset inside : Nat) (images : List Spec.Term)
    (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (middle result : Term)
    (child : Applies P H "vibe:subst-go"
      [encodeTable table, natural count, .list (encodeTerms images), natural inside, encode first] middle)
    (next : Applies P H "vibe:subst-args-first"
      [middle, encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, .list (encodeTerms rest)] result) :
    Applies P H "vibe:subst-args-bound"
      [.sym "True", encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, natural inside, encode first, .list (encodeTerms rest)] result := by
  refine Applies.equation (equation := A[30])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset), ("binders", encodeBinders binders),
      ("inside", natural inside), ("first", encode first), ("rest", .list (encodeTerms rest))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) child

private theorem args_first_some (table : SignatureTable) (count offset : Nat) (images : List Spec.Term)
    (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (middle result : Term)
    (tail : Applies P H "vibe:subst-args"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, .list (encodeTerms rest)] middle)
    (next : Applies P H "vibe:subst-args-rest" [encode first, middle] result) :
    Applies P H "vibe:subst-args-first"
      [encodeResult (some first), encodeTable table, natural count, .list (encodeTerms images),
        natural offset, encodeBinders binders, .list (encodeTerms rest)] result := by
  refine Applies.equation (equation := A[32])
    (environment := [("first", encode first), ("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("offset", natural offset),
      ("binders", encodeBinders binders), ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) tail

private theorem args_children (table : SignatureTable) (count offset inside : Nat) (images : List Spec.Term)
    (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term)
    (firstResult : Option Spec.Term) (restResult : Option (List Spec.Term))
    (head : Applies P H "vibe:subst-go"
      [encodeTable table, natural count, .list (encodeTerms images), natural inside, encode first]
      (encodeResult firstResult))
    (tail : Applies P H "vibe:subst-args"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, .list (encodeTerms rest)] (encodeTermsResult restResult)) :
    Applies P H "vibe:subst-args-bound"
      [.sym "True", encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, natural inside, encode first, .list (encodeTerms rest)]
      (encodeTermsResult (firstResult.bind (fun first' => restResult.map (List.cons first')))) := by
  refine args_bound table count offset inside images binders first rest _ _ head ?_
  cases firstResult with
  | none => exact ⟨1, rfl⟩
  | some first' =>
      refine args_first_some table count offset images binders first' rest _ _ tail ?_
      cases restResult with
      | none => exact ⟨1, rfl⟩
      | some rest' => exact ⟨3, rfl⟩

mutual

/-- The complete authored substitution traversal runs on every raw term;
count/list agreement and well-formedness are not imposed. -/
theorem substGo_computes (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (offset : Nat) (term : Spec.Term) :
    Applies P H "vibe:subst-go"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset, encode term]
      (encodeResult (Spec.substGo (signatureOf table) count images offset term)) := by
  cases term with
  | bvar index => exact bvar_computes table count offset index images
  | lit bytes => exact ⟨3, rfl⟩
  | app symbol terms =>
      apply app_start
      by_cases closed : Spec.depth (signatureOf table) (.app symbol terms) ≤ offset
      · simp only [Spec.substGo, closed, boolean, decide_true, ↓reduceIte]
        exact ⟨3, rfl⟩
      · have computation := app_open table count offset images symbol terms _
          (substList_computes table count images offset (bindersOf (signatureOf table) symbol) terms)
        simpa [Spec.substGo, closed, substGoArgs_eq, boolean] using computation

theorem substList_computes (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (offset : Nat) (binders : List Nat) (terms : List Spec.Term) :
    Applies P H "vibe:subst-args"
      [encodeTable table, natural count, .list (encodeTerms images), natural offset,
        encodeBinders binders, .list (encodeTerms terms)]
      (encodeTermsResult (substList (signatureOf table) count images offset binders terms)) := by
  cases terms with
  | nil => exact args_start table count offset images binders [] _ ⟨2, rfl⟩
  | cons first rest =>
      apply args_start
      apply args_cons
      apply args_binder
      by_cases fits : offset + binders.headD 0 < Spec.wordBound
      · have computation := args_children table count offset (offset + binders.headD 0) images
          binders.tail first rest _ _ (substGo_computes table count images (offset + binders.headD 0) first)
          (substList_computes table count images offset binders.tail rest)
        simp only [substList, boolean, fits, decide_true, ↓reduceIte]
        convert computation using 2
        cases headResult : Spec.substGo (signatureOf table) count images (offset + binders.headD 0) first <;>
          cases tailResult : substList (signatureOf table) count images offset binders.tail rest <;> rfl
      · simp only [substList, boolean, fits, decide_false, ↓reduceIte]
        exact ⟨1, rfl⟩

end

private theorem substitution_start (table : SignatureTable) (count offset : Nat)
    (images : List Spec.Term) (body : Spec.Term) (result : Term)
    (next : Applies P H "vibe:subst-zero"
      [.sym (if count = 0 then "True" else "False"), encodeTable table, natural count,
        .list (encodeTerms images), encode body, natural offset] result) :
    Applies P H "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset] result := by
  refine Applies.equation (equation := A[8])
    (environment := [("table", encodeTable table), ("count", natural count),
      ("images", .list (encodeTerms images)), ("body", encode body), ("offset", natural offset)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (zero_applies count)

theorem substitution_computes (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) :
    Applies P H "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset]
      (encodeResult (Spec.substBVars (signatureOf table) count images body offset)) := by
  apply substitution_start
  by_cases zero : count = 0
  · simp only [Spec.substBVars, zero, ↓reduceIte]
    exact ⟨2, rfl⟩
  · simp only [Spec.substBVars, zero, ↓reduceIte]
    refine Applies.equation (equation := A[10])
      (environment := [("table", encodeTable table), ("count", natural count),
        ("images", .list (encodeTerms images)), ("body", encode body), ("offset", natural offset)])
      (by rfl) (by rfl) ?_
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
      (substGo_computes table count images offset body)

theorem substitution_result_exact (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) (result : Term) :
    Applies P H "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset] result ↔
      result = encodeResult (Spec.substBVars (signatureOf table) count images body offset) := by
  constructor
  · intro computation
    exact computation.deterministic (substitution_computes table count images body offset)
  · intro same
    subst result
    exact substitution_computes table count images body offset

theorem substitution_accepts_iff (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (body result : Spec.Term) (offset : Nat) :
    Applies P H "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset]
      (encodeResult (some result)) ↔ Spec.substBVars (signatureOf table) count images body offset = some result := by
  rw [substitution_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem substitution_refuses_iff (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) :
    Applies P H "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset]
      (encodeResult none) ↔ Spec.substBVars (signatureOf table) count images body offset = none := by
  rw [substitution_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem substitution_completed_exact (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset fuel : Nat)
    (finished : apply P H fuel "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset] ≠ .exhausted) :
    apply P H fuel "vibe:subst"
      [encodeTable table, natural count, .list (encodeTerms images), encode body, natural offset] =
      .value (encodeResult (Spec.substBVars (signatureOf table) count images body offset)) :=
  (substitution_computes table count images body offset).completed fuel finished

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution
