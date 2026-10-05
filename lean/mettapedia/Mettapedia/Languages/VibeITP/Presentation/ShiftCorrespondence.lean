import Mettapedia.Languages.VibeITP.Presentation.ShiftProgram
import Mettapedia.Languages.VibeITP.Presentation.SpecFacts
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Authored Vibe lookup, depth and shift correspondence

The shared equation evaluator executes the declared traversal and guards.
The host supplies only scalar natural arithmetic and typed list views.
The reference results are the independent Vibe specification computations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalShift

open ComputationalData
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => shiftProgram
local notation "H" => computationalHost

private theorem add_applies (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  .primitive (by rfl) (naturalArithmeticHost_add left right)

private theorem monus_applies (left right : Nat) :
    Applies P H "nik:nat-monus" [natural left, natural right] (natural (left - right)) :=
  .primitive (by rfl) (naturalArithmeticHost_monus left right)

private theorem max_applies (left right : Nat) :
    Applies P H "nik:nat-max" [natural left, natural right] (natural (max left right)) :=
  .primitive (by rfl) (naturalArithmeticHost_max left right)

private theorem le_applies (left right : Nat) :
    Applies P H "nik:nat-le" [natural left, natural right] (boolean (decide (left ≤ right))) :=
  .primitive (by rfl) (naturalArithmeticHost_le left right)

private theorem lt_applies (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  .primitive (by rfl) (naturalArithmeticHost_lt left right)

private theorem eq_applies (left right : Nat) :
    Applies P H "nik:nat-eq" [natural left, natural right] (boolean (decide (left = right))) :=
  .primitive (by rfl) (naturalArithmeticHost_eq left right)

private theorem zero_applies (value : Nat) :
    Applies P H "nik:nat-zero" [natural value]
      (.sym (if value = 0 then "True" else "False")) :=
  .primitive (by rfl) (computationalHost_zero value)

private theorem view_applies (values : List Term) :
    Applies P H "nik:list-view" [.list values] (listView values) :=
  .primitive (by rfl) (computationalHost_list_view values)

private theorem cons_applies (first : Term) (rest : List Term) :
    Applies P H "nik:list-cons" [first, .list rest] (.list (first :: rest)) :=
  .primitive (by rfl) (computationalHost_list_cons first rest)

private theorem same_tag_symbols (tag : String) (left right : Nat) (equation : Equation)
    (selected : (P).select "vibe:symbol-eq"
      [.list [.sym tag, natural left], .list [.sym tag, natural right]] =
      some (equation, [("i", natural left), ("j", natural right)]))
    (body : equation.body = .expr [.sym "nik:nat-eq", .var "i", .var "j"]) :
    Applies P H "vibe:symbol-eq"
      [.list [.sym tag, natural left], .list [.sym tag, natural right]]
      (boolean (decide (left = right))) := by
  refine Applies.equation (equation := equation) (by rfl) selected ?_
  rw [body]
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (eq_applies left right)

theorem symbol_computes (left right : Spec.SymId) :
    Applies P H "vibe:symbol-eq" [encodeSymbol left, encodeSymbol right]
      (boolean (decide (left = right))) := by
  cases left with
  | builtin left =>
      cases right with
      | builtin right =>
          have computed := same_tag_symbols "Builtin" left.slot right.slot P[0] (by rfl) (by rfl)
          cases left <;> cases right <;> simpa [encodeSymbol, Spec.Builtin.slot, boolean] using computed
      | fresh right => exact ⟨1, rfl⟩
  | fresh left =>
      cases right with
      | builtin right => exact ⟨1, rfl⟩
      | fresh right =>
          simpa [encodeSymbol] using same_tag_symbols "Fresh" left right P[1] (by rfl) (by rfl)

private theorem lookup_start (table : SignatureTable) (symbol : Spec.SymId) (result : Term)
    (view : Applies P H "vibe:lookup-view" [listView (table.map encodeBinding), encodeSymbol symbol] result) :
    Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol] result := by
  refine Applies.equation (equation := P[4])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) view
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (table.map encodeBinding))

private theorem lookup_cons (key symbol : Spec.SymId) (info : Spec.SymInfo)
    (table : SignatureTable) (result : Term)
    (next : Applies P H "vibe:lookup-equal" [boolean (decide (symbol = key)),
      encodeKind info.kind, encodeBinders info.binders, encodeTable table, encodeSymbol symbol] result) :
    Applies P H "vibe:lookup-view"
      [listView (((key, info) :: table).map encodeBinding), encodeSymbol symbol] result := by
  refine Applies.equation (equation := P[6])
    (environment := [("key", encodeSymbol key), ("kind", encodeKind info.kind),
      ("binders", encodeBinders info.binders), ("tail", encodeTable table), ("symbol", encodeSymbol symbol)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (symbol_computes symbol key)

private theorem lookup_next (table : SignatureTable) (symbol : Spec.SymId)
    (info : Spec.SymInfo) (result : Term)
    (tail : Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol] result) :
    Applies P H "vibe:lookup-equal" [.sym "False", encodeKind info.kind,
      encodeBinders info.binders, encodeTable table, encodeSymbol symbol] result := by
  refine Applies.equation (equation := P[8])
    (environment := [("kind", encodeKind info.kind), ("binders", encodeBinders info.binders),
      ("tail", encodeTable table), ("symbol", encodeSymbol symbol)])
    (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

theorem lookup_computes (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol]
      (encodeInfoResult (signatureOf table symbol)) := by
  induction table with
  | nil => exact lookup_start [] symbol _ ⟨1, rfl⟩
  | cons binding table ih =>
      rcases binding with ⟨key, info⟩
      apply lookup_start
      apply lookup_cons
      by_cases same : symbol = key
      · subst symbol
        exact ⟨3, by simp only [signatureOf, ↓reduceIte]; rfl⟩
      · have next := lookup_next table symbol info _ ih
        simpa [signatureOf, same, boolean] using next

theorem binders_computes (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:binders" [encodeTable table, encodeSymbol symbol]
      (encodeBinders (bindersOf (signatureOf table) symbol)) := by
  refine Applies.equation (equation := P[9])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeInfoResult (signatureOf table symbol)])
    (by simp [Special]) (.cons ?_ .nil) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (lookup_computes table symbol)
  · cases found : signatureOf table symbol with
    | none => simp only [found, encodeInfoResult, bindersOf]; exact ⟨1, rfl⟩
    | some info => simp only [found, encodeInfoResult, bindersOf]; exact ⟨1, rfl⟩

private theorem depth_bvar (table : SignatureTable) (index : Nat) :
    Applies P H "vibe:depth" [encodeTable table, encode (.bvar index)] (natural (index + 1)) := by
  refine Applies.equation (equation := P[12])
    (environment := [("table", encodeTable table), ("i", natural index)])
    (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (add_applies index 1)

private theorem depth_app (table : SignatureTable) (symbol : Spec.SymId) (terms : List Spec.Term)
    (result : Nat)
    (arguments : Applies P H "vibe:depth-args" [encodeTable table, .list (encodeTerms terms),
      encodeBinders (bindersOf (signatureOf table) symbol)] (natural result)) :
    Applies P H "vibe:depth" [encodeTable table, encode (.app symbol terms)] (natural result) := by
  refine Applies.equation (equation := P[14])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ .nil))) arguments
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (binders_computes table symbol)

private theorem depth_args_start (table : SignatureTable) (binders : List Nat)
    (terms : List Spec.Term) (result : Nat)
    (view : Applies P H "vibe:depth-view"
      [encodeTable table, listView (encodeTerms terms), encodeBinders binders] (natural result)) :
    Applies P H "vibe:depth-args" [encodeTable table, .list (encodeTerms terms), encodeBinders binders]
      (natural result) := by
  refine Applies.equation (equation := P[15])
    (environment := [("table", encodeTable table), ("arguments", .list (encodeTerms terms)),
      ("binders", encodeBinders binders)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) .nil))) view
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (encodeTerms terms))

private theorem depth_args_cons (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (result : Nat)
    (binder : Applies P H "vibe:depth-binder" [encodeTable table, encode first, .list (encodeTerms rest),
      listView (binders.map natural)] (natural result)) :
    Applies P H "vibe:depth-view"
      [encodeTable table, listView (encodeTerms (first :: rest)), encodeBinders binders]
      (natural result) := by
  refine Applies.equation (equation := P[17])
    (environment := [("table", encodeTable table), ("first", encode first), ("rest", .list (encodeTerms rest)),
      ("binders", encodeBinders binders)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons ?_ .nil)))) binder
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (binders.map natural))

private theorem depth_under_binder (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (firstDepth restDepth : Nat)
    (head : Applies P H "vibe:depth" [encodeTable table, encode first] (natural firstDepth))
    (tail : Applies P H "vibe:depth-args"
      [encodeTable table, .list (encodeTerms rest), encodeBinders binders.tail] (natural restDepth)) :
    Applies P H "vibe:depth-binder"
      [encodeTable table, encode first, .list (encodeTerms rest), listView (binders.map natural)]
      (natural (max (firstDepth - binders.headD 0) restDepth)) := by
  cases binders with
  | nil =>
      refine Applies.equation (equation := P[18])
        (environment := [("table", encodeTable table), ("first", encode first),
          ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (max_applies (firstDepth - 0) restDepth)
      · refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.literal _ _ _ _) .nil)) (monus_applies firstDepth 0)
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) head
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (PassiveData.evaluates (.list (by simp)) _) .nil))) tail
  | cons bound binders =>
      refine Applies.equation (equation := P[19])
        (environment := [("table", encodeTable table), ("first", encode first),
          ("rest", .list (encodeTerms rest)), ("bound", natural bound), ("tail", encodeBinders binders)])
        (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (max_applies (firstDepth - bound) restDepth)
      · refine Evaluates.call (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) .nil)) (monus_applies firstDepth bound)
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) head
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) .nil))) tail

mutual

theorem depth_computes (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:depth" [encodeTable table, encode term]
      (natural (Spec.depth (signatureOf table) term)) := by
  cases term with
  | bvar index => exact depth_bvar table index
  | lit bytes => exact ⟨1, rfl⟩
  | app symbol terms =>
      rw [Presentation.depth_app]
      exact depth_app table symbol terms _
        (depth_args_computes table (bindersOf (signatureOf table) symbol) terms)

theorem depth_args_computes (table : SignatureTable) (binders : List Nat) (terms : List Spec.Term) :
    Applies P H "vibe:depth-args" [encodeTable table, .list (encodeTerms terms), encodeBinders binders]
      (natural (depthBinders (signatureOf table) binders terms)) := by
  cases terms with
  | nil => exact depth_args_start table binders [] _ ⟨1, rfl⟩
  | cons first rest =>
      exact depth_args_start table binders (first :: rest) _
        (depth_args_cons table binders first rest _
          (depth_under_binder table binders first rest _ _ (depth_computes table first)
            (depth_args_computes table binders.tail rest)))

end

private theorem shift_bvar_start (table : SignatureTable) (index amount cutoff : Nat) (result : Term)
    (next : Applies P H "vibe:shift-bvar-zero"
      [.sym (if amount = 0 then "True" else "False"), natural index, natural amount, natural cutoff] result) :
    Applies P H "vibe:shift" [encodeTable table, encode (.bvar index), natural amount, natural cutoff]
      result := by
  refine Applies.equation (equation := P[20])
    (environment := [("table", encodeTable table), ("i", natural index),
      ("amount", natural amount), ("cutoff", natural cutoff)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (zero_applies amount)

private theorem shift_bvar_nonzero (index amount cutoff : Nat) (result : Term)
    (next : Applies P H "vibe:shift-bvar-closed"
      [boolean (decide (index + 1 ≤ cutoff)), natural index, natural amount] result) :
    Applies P H "vibe:shift-bvar-zero"
      [.sym "False", natural index, natural amount, natural cutoff] result := by
  refine Applies.equation (equation := P[24])
    (environment := [("i", natural index), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) (le_applies (index + 1) cutoff)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (add_applies index 1)

private theorem shift_bvar_open (index amount : Nat) (result : Term)
    (next : Applies P H "vibe:shift-bvar-word"
      [boolean (decide (index + amount + 1 < Spec.wordBound)), natural (index + amount)] result) :
    Applies P H "vibe:shift-bvar-closed" [.sym "False", natural index, natural amount] result := by
  refine Applies.equation (equation := P[26])
    (environment := [("i", natural index), ("amount", natural amount)]) (by rfl) (by rfl) ?_
  have sum : Evaluates P H [("i", natural index), ("amount", natural amount)]
      (.expr [.sym "nik:nat-add", .var "i", .var "amount"]) (natural (index + amount)) :=
    Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (add_applies index amount)
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons sum .nil)) next
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.literal _ _ _ _) .nil))
    (lt_applies (index + amount + 1) Spec.wordBound)
  exact Evaluates.call (by simp [Special])
    (.cons sum (.cons (.literal _ _ _ _) .nil)) (add_applies (index + amount) 1)

private theorem shift_bvar_computes (table : SignatureTable) (index amount cutoff : Nat) :
    Applies P H "vibe:shift" [encodeTable table, encode (.bvar index), natural amount, natural cutoff]
      (encodeResult (Spec.shift (signatureOf table) amount cutoff (.bvar index))) := by
  apply shift_bvar_start
  by_cases zero : amount = 0
  · simp only [zero, ↓reduceIte, Spec.shift, true_or]
    exact ⟨3, rfl⟩
  · simp only [zero, ↓reduceIte]
    apply shift_bvar_nonzero
    by_cases closed : index + 1 ≤ cutoff
    · simp only [boolean, closed, decide_true, ↓reduceIte, Spec.shift, or_true]
      exact ⟨3, rfl⟩
    · simp only [boolean, closed, decide_false]
      apply shift_bvar_open
      by_cases fits : index + amount + 1 < Spec.wordBound
      · simp only [boolean, fits, decide_true, ↓reduceIte, Spec.shift, zero, closed, false_or]
        exact ⟨3, rfl⟩
      · simp only [boolean, fits, decide_false, ↓reduceIte, Spec.shift, zero, closed, false_or]
        exact ⟨1, rfl⟩

private theorem shift_app_start (table : SignatureTable) (symbol : Spec.SymId) (terms : List Spec.Term)
    (amount cutoff : Nat) (result : Term)
    (next : Applies P H "vibe:shift-app-zero"
      [.sym (if amount = 0 then "True" else "False"), encodeTable table, encodeSymbol symbol,
        .list (encodeTerms terms), natural amount, natural cutoff] result) :
    Applies P H "vibe:shift"
      [encodeTable table, encode (.app symbol terms), natural amount, natural cutoff] result := by
  refine Applies.equation (equation := P[22])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms)), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (zero_applies amount)

private theorem shift_app_nonzero (table : SignatureTable) (symbol : Spec.SymId) (terms : List Spec.Term)
    (amount cutoff : Nat) (result : Term)
    (next : Applies P H "vibe:shift-app-closed"
      [boolean (decide (Spec.depth (signatureOf table) (.app symbol terms) ≤ cutoff)),
        encodeTable table, encodeSymbol symbol, .list (encodeTerms terms), natural amount, natural cutoff]
      result) :
    Applies P H "vibe:shift-app-zero" [.sym "False", encodeTable table, encodeSymbol symbol,
      .list (encodeTerms terms), natural amount, natural cutoff] result := by
  refine Applies.equation (equation := P[30])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms)), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (le_applies (Spec.depth (signatureOf table) (.app symbol terms)) cutoff)
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ .nil)) (depth_computes table (.app symbol terms))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (Applies.constructor (by rfl) (by rfl))

private theorem shift_app_open (table : SignatureTable) (symbol : Spec.SymId) (terms : List Spec.Term)
    (amount cutoff : Nat) (result : Option (List Spec.Term))
    (arguments : Applies P H "vibe:shift-args"
      [encodeTable table, .list (encodeTerms terms), encodeBinders (bindersOf (signatureOf table) symbol),
        natural amount, natural cutoff] (encodeTermsResult result)) :
    Applies P H "vibe:shift-app-closed" [.sym "False", encodeTable table, encodeSymbol symbol,
      .list (encodeTerms terms), natural amount, natural cutoff]
      (encodeResult (result.map (Spec.Term.app symbol))) := by
  refine Applies.equation (equation := P[32])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms)), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeSymbol symbol, encodeTermsResult result])
    (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
  · refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) arguments
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (binders_computes table symbol)
  · cases result with
    | none => exact ⟨1, rfl⟩
    | some result => exact ⟨3, rfl⟩

private theorem shift_args_start (table : SignatureTable) (binders : List Nat) (terms : List Spec.Term)
    (amount cutoff : Nat) (result : Term)
    (view : Applies P H "vibe:shift-args-view"
      [encodeTable table, listView (encodeTerms terms), encodeBinders binders, natural amount, natural cutoff]
      result) :
    Applies P H "vibe:shift-args"
      [encodeTable table, .list (encodeTerms terms), encodeBinders binders, natural amount, natural cutoff]
      result := by
  refine Applies.equation (equation := P[35])
    (environment := [("table", encodeTable table), ("arguments", .list (encodeTerms terms)),
      ("binders", encodeBinders binders), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) view
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (encodeTerms terms))

private theorem shift_args_cons (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (amount cutoff : Nat) (result : Term)
    (next : Applies P H "vibe:shift-args-binder"
      [encodeTable table, encode first, .list (encodeTerms rest), listView (binders.map natural),
        natural amount, natural cutoff] result) :
    Applies P H "vibe:shift-args-view"
      [encodeTable table, listView (encodeTerms (first :: rest)), encodeBinders binders,
        natural amount, natural cutoff] result := by
  refine Applies.equation (equation := P[37])
    (environment := [("table", encodeTable table), ("first", encode first), ("rest", .list (encodeTerms rest)),
      ("binders", encodeBinders binders), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (view_applies (binders.map natural))

private theorem shift_args_binder (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (amount cutoff : Nat) (result : Term)
    (next : Applies P H "vibe:shift-args-bound"
      [boolean (decide (cutoff + binders.headD 0 < Spec.wordBound)), encodeTable table, encode first,
        .list (encodeTerms rest), encodeBinders binders.tail, natural amount, natural cutoff,
        natural (cutoff + binders.headD 0)] result) :
    Applies P H "vibe:shift-args-binder"
      [encodeTable table, encode first, .list (encodeTerms rest), listView (binders.map natural),
        natural amount, natural cutoff] result := by
  cases binders with
  | nil =>
      refine Applies.equation (equation := P[38])
        (environment := [("table", encodeTable table), ("first", encode first), ("rest", .list (encodeTerms rest)),
          ("amount", natural amount), ("cutoff", natural cutoff)]) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (PassiveData.evaluates (.list (by simp)) _)
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (lt_applies cutoff Spec.wordBound)
  | cons bound binders =>
      refine Applies.equation (equation := P[39])
        (environment := [("table", encodeTable table), ("first", encode first), ("rest", .list (encodeTerms rest)),
          ("bound", natural bound), ("tail", encodeBinders binders),
          ("amount", natural amount), ("cutoff", natural cutoff)]) (by rfl) (by rfl) ?_
      have sum : Evaluates P H [("table", encodeTable table), ("first", encode first),
          ("rest", .list (encodeTerms rest)), ("bound", natural bound), ("tail", encodeBinders binders),
          ("amount", natural amount), ("cutoff", natural cutoff)]
          (.expr [.sym "nik:nat-add", .var "cutoff", .var "bound"]) (natural (cutoff + bound)) :=
        Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (add_applies cutoff bound)
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons sum .nil)))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons sum (.cons (.literal _ _ _ _) .nil)) (lt_applies (cutoff + bound) Spec.wordBound)

private theorem shift_args_bound_true (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (amount cutoff inside : Nat) (middle result : Term)
    (child : Applies P H "vibe:shift" [encodeTable table, encode first, natural amount, natural inside] middle)
    (next : Applies P H "vibe:shift-args-first"
      [middle, encodeTable table, .list (encodeTerms rest), encodeBinders binders, natural amount, natural cutoff] result) :
    Applies P H "vibe:shift-args-bound"
      [.sym "True", encodeTable table, encode first, .list (encodeTerms rest), encodeBinders binders,
        natural amount, natural cutoff, natural inside] result := by
  refine Applies.equation (equation := P[41])
    (environment := [("table", encodeTable table), ("first", encode first), ("rest", .list (encodeTerms rest)),
      ("binders", encodeBinders binders), ("amount", natural amount), ("cutoff", natural cutoff),
      ("inside", natural inside)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) child

private theorem shift_args_first_some (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (amount cutoff : Nat) (middle result : Term)
    (tail : Applies P H "vibe:shift-args"
      [encodeTable table, .list (encodeTerms rest), encodeBinders binders, natural amount, natural cutoff] middle)
    (next : Applies P H "vibe:shift-args-rest" [encode first, middle] result) :
    Applies P H "vibe:shift-args-first"
      [encodeResult (some first), encodeTable table, .list (encodeTerms rest), encodeBinders binders,
        natural amount, natural cutoff] result := by
  refine Applies.equation (equation := P[43])
    (environment := [("first", encode first), ("table", encodeTable table), ("rest", .list (encodeTerms rest)),
      ("binders", encodeBinders binders), ("amount", natural amount), ("cutoff", natural cutoff)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) tail

private theorem shift_args_children (table : SignatureTable) (binders : List Nat)
    (first : Spec.Term) (rest : List Spec.Term) (amount cutoff inside : Nat)
    (firstResult : Option Spec.Term) (restResult : Option (List Spec.Term))
    (head : Applies P H "vibe:shift" [encodeTable table, encode first, natural amount, natural inside]
      (encodeResult firstResult))
    (tail : Applies P H "vibe:shift-args"
      [encodeTable table, .list (encodeTerms rest), encodeBinders binders, natural amount, natural cutoff]
      (encodeTermsResult restResult)) :
    Applies P H "vibe:shift-args-bound"
      [.sym "True", encodeTable table, encode first, .list (encodeTerms rest), encodeBinders binders,
        natural amount, natural cutoff, natural inside]
      (encodeTermsResult (firstResult.bind (fun first' => restResult.map (List.cons first')))) := by
  refine shift_args_bound_true table binders first rest amount cutoff inside _ _ head ?_
  cases firstResult with
  | none => exact ⟨1, rfl⟩
  | some first' =>
      refine shift_args_first_some table binders first' rest amount cutoff _ _ tail ?_
      cases restResult with
      | none => exact ⟨1, rfl⟩
      | some rest' => exact ⟨3, rfl⟩

mutual

/-- The authored shift program terminates on every encoded raw term. Early
pruning preserves even indices outside the operation's word range. -/
theorem shift_computes (table : SignatureTable) (amount cutoff : Nat) (term : Spec.Term) :
    Applies P H "vibe:shift" [encodeTable table, encode term, natural amount, natural cutoff]
      (encodeResult (Spec.shift (signatureOf table) amount cutoff term)) := by
  cases term with
  | bvar index => exact shift_bvar_computes table index amount cutoff
  | lit bytes => exact ⟨3, rfl⟩
  | app symbol terms =>
      apply shift_app_start
      by_cases zero : amount = 0
      · simp only [zero, ↓reduceIte, Spec.shift, true_or]
        exact ⟨3, rfl⟩
      · simp only [zero, ↓reduceIte]
        apply shift_app_nonzero
        by_cases closed : Spec.depth (signatureOf table) (.app symbol terms) ≤ cutoff
        · simp only [boolean, closed, decide_true, ↓reduceIte, Spec.shift, or_true]
          exact ⟨3, rfl⟩
        · have openRun := shift_app_open table symbol terms amount cutoff _
            (shiftList_computes table amount cutoff (bindersOf (signatureOf table) symbol) terms)
          simpa [Spec.shift, zero, closed, shiftArgs_eq, boolean] using openRun

/-- The full argument traversal includes each binder addition guard and both
child refusals; the host does not traverse or shift terms. -/
theorem shiftList_computes (table : SignatureTable) (amount cutoff : Nat)
    (binders : List Nat) (terms : List Spec.Term) :
    Applies P H "vibe:shift-args"
      [encodeTable table, .list (encodeTerms terms), encodeBinders binders, natural amount, natural cutoff]
      (encodeTermsResult (shiftList (signatureOf table) amount cutoff binders terms)) := by
  cases terms with
  | nil => exact shift_args_start table binders [] amount cutoff _ ⟨2, rfl⟩
  | cons first rest =>
      apply shift_args_start
      apply shift_args_cons
      apply shift_args_binder
      by_cases fits : cutoff + binders.headD 0 < Spec.wordBound
      · have computed := shift_args_children table binders.tail first rest amount cutoff
            (cutoff + binders.headD 0) _ _
            (shift_computes table amount (cutoff + binders.headD 0) first)
            (shiftList_computes table amount cutoff binders.tail rest)
        simp only [boolean, fits, decide_true, ↓reduceIte, shiftList]
        convert computed using 2
        cases headResult : Spec.shift (signatureOf table) amount (cutoff + binders.headD 0) first <;>
          cases tailResult : shiftList (signatureOf table) amount cutoff binders.tail rest <;> rfl
      · simp only [boolean, fits, decide_false, ↓reduceIte, shiftList]
        exact ⟨1, rfl⟩

end

/-- Every finite successful evaluator run has exactly the independently
specified result, including the explicit refusal result. -/
theorem shift_result_exact (table : SignatureTable) (amount cutoff : Nat) (term : Spec.Term)
    (result : Term) :
    Applies P H "vibe:shift" [encodeTable table, encode term, natural amount, natural cutoff] result ↔
      result = encodeResult (Spec.shift (signatureOf table) amount cutoff term) := by
  constructor
  · intro computation
    exact computation.deterministic (shift_computes table amount cutoff term)
  · intro same
    subst result
    exact shift_computes table amount cutoff term

theorem encodeResult_injective : Function.Injective encodeResult := by
  intro first second same
  cases first with
  | none => cases second <;> first | rfl | cases same
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have encoded : encode first = encode second := by
            simpa only [encodeResult, Term.expr.injEq, List.cons.injEq, and_true, true_and] using same
          exact congrArg some (encode_injective encoded)

theorem shift_accepts_iff (table : SignatureTable) (amount cutoff : Nat) (source result : Spec.Term) :
    Applies P H "vibe:shift" [encodeTable table, encode source, natural amount, natural cutoff]
      (encodeResult (some result)) ↔ Spec.shift (signatureOf table) amount cutoff source = some result := by
  rw [shift_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm,
    fun same => congrArg encodeResult same.symm⟩

theorem shift_refuses_iff (table : SignatureTable) (amount cutoff : Nat) (source : Spec.Term) :
    Applies P H "vibe:shift" [encodeTable table, encode source, natural amount, natural cutoff]
      (encodeResult none) ↔ Spec.shift (signatureOf table) amount cutoff source = none := by
  rw [shift_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm,
    fun same => congrArg encodeResult same.symm⟩

/-- An evaluator outcome distinct from exhaustion is the exact value; it
cannot be a failed evaluation or an invented shifted result. -/
theorem shift_completed_exact (table : SignatureTable) (amount cutoff fuel : Nat) (source : Spec.Term)
    (finished : apply P H fuel "vibe:shift"
      [encodeTable table, encode source, natural amount, natural cutoff] ≠ .exhausted) :
    apply P H fuel "vibe:shift" [encodeTable table, encode source, natural amount, natural cutoff] =
      .value (encodeResult (Spec.shift (signatureOf table) amount cutoff source)) :=
  (shift_computes table amount cutoff source).completed fuel finished

end Mettapedia.Languages.VibeITP.Presentation.ComputationalShift
