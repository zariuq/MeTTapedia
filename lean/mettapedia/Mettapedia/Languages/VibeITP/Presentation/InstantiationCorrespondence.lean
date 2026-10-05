import Mettapedia.Languages.VibeITP.Presentation.InstantiationProgram

/-!
# Authored free-variable occurrence and instantiation correspondence

Every guest traversal is executed by the same declared equation evaluator.
Signature queries, postorder instantiation and statement guards compose the
previously proved lookup, shift and simultaneous substitution computations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation

open ComputationalData ComputationalShift ComputationalSubstitution
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => instantiationProgram
local notation "A" => instantiationEquations
local notation "H" => computationalHost

private theorem option_bind_match {α β : Type} (value : Option α) (next : α → Option β) :
    value.bind next = match value with | none => none | some element => next element := by
  cases value <;> rfl

private theorem lookup_applies (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol]
      (encodeInfoResult (signatureOf table symbol)) := by
  apply reuse_substitution_call (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations H substitutionEquations_disjoint
    "vibe:lookup-symbol" (by decide +kernel) _ _).mpr
  exact lookup_computes table symbol

private theorem symbol_applies (first second : Spec.SymId) :
    Applies P H "vibe:symbol-eq" [encodeSymbol first, encodeSymbol second]
      (boolean (decide (first = second))) := by
  apply reuse_substitution_call (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations H substitutionEquations_disjoint
    "vibe:symbol-eq" (by decide +kernel) _ _).mpr
  exact symbol_computes first second

private theorem depth_applies (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:depth" [encodeTable table, encode term] (natural (Spec.depth (signatureOf table) term)) :=
  reuse_substitution_call (by decide +kernel) (depth_computes_in_substitution table term)

private theorem binders_applies (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:binders" [encodeTable table, encodeSymbol symbol]
      (encodeBinders (bindersOf (signatureOf table) symbol)) :=
  reuse_substitution_call (by decide +kernel) (binders_computes_in_substitution table symbol)

private theorem shift_applies (table : SignatureTable) (amount cutoff : Nat) (term : Spec.Term) :
    Applies P H "vibe:shift" [encodeTable table, encode term, natural amount, natural cutoff]
      (encodeResult (Spec.shift (signatureOf table) amount cutoff term)) :=
  reuse_substitution_call (by decide +kernel) (shift_computes_in_substitution table amount cutoff term)

private theorem subst_applies (table : SignatureTable) (count : Nat) (images : List Spec.Term)
    (term : Spec.Term) (offset : Nat) :
    Applies P H "vibe:subst" [encodeTable table, natural count, .list (encodeTerms images), encode term, natural offset]
      (encodeResult (Spec.substBVars (signatureOf table) count images term offset)) :=
  reuse_substitution_call (by decide +kernel) (substitution_computes table count images term offset)

private theorem length_applies (items : List Term) :
    Applies P H "vibe:list-length" [.list items] (natural items.length) :=
  reuse_substitution_call (by decide +kernel) (listLength_computes items)

private theorem view_applies (items : List Term) :
    Applies P H "nik:list-view" [.list items] (listView items) :=
  .primitive (by rfl) (computationalHost_list_view items)

private theorem add_applies (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  .primitive (by rfl) (naturalArithmeticHost_add left right)

private theorem le_applies (left right : Nat) :
    Applies P H "nik:nat-le" [natural left, natural right] (boolean (decide (left ≤ right))) :=
  .primitive (by rfl) (naturalArithmeticHost_le left right)

private theorem lt_applies (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  .primitive (by rfl) (naturalArithmeticHost_lt left right)

private theorem zero_applies (number : Nat) :
    Applies P H "nik:nat-zero" [natural number] (.sym (if number = 0 then "True" else "False")) :=
  .primitive (by rfl) (computationalHost_zero number)

theorem isFvar_computes (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:is-fvar" [encodeTable table, encodeSymbol symbol]
      (boolean (Spec.isFvarSym (signatureOf table) symbol)) := by
  refine Applies.equation (equation := A[0])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeInfoResult (signatureOf table symbol)]) (by simp [Special])
    (.cons ?_ .nil) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (lookup_applies table symbol)
  · cases found : signatureOf table symbol with
    | none => simp only [Spec.isFvarSym, found]; exact ⟨1, rfl⟩
    | some info =>
        simp only [Spec.isFvarSym, found]
        cases kind : info.kind <;> exact ⟨1, by simp only [encodeInfoResult, encodeInfo, kind, encodeKind]; rfl⟩

private theorem hasFvar_app_start (table : SignatureTable) (symbol : Spec.SymId)
    (terms : List Spec.Term) (result : Bool)
    (next : Applies P H "vibe:has-fvar-head"
      [boolean (Spec.isFvarSym (signatureOf table) symbol), encodeTable table, .list (encodeTerms terms)]
      (boolean result)) :
    Applies P H "vibe:has-fvar" [encodeTable table, encode (.app symbol terms)] (boolean result) := by
  refine Applies.equation (equation := A[6])
    (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (isFvar_computes table symbol)

private theorem hasFvar_head (table : SignatureTable) (terms : List Spec.Term) (first rest : Bool)
    (tail : Applies P H "vibe:has-fvar-args" [encodeTable table, .list (encodeTerms terms)] (boolean rest)) :
    Applies P H "vibe:has-fvar-head" [boolean first, encodeTable table, .list (encodeTerms terms)]
      (boolean (first || rest)) := by
  cases first with
  | true => exact ⟨1, rfl⟩
  | false =>
      refine Applies.equation (equation := A[8])
        (environment := [("table", encodeTable table), ("arguments", .list (encodeTerms terms))])
        (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

private theorem hasFvar_args_start (table : SignatureTable) (terms : List Spec.Term) (result : Bool)
    (next : Applies P H "vibe:has-fvar-view" [encodeTable table, listView (encodeTerms terms)] (boolean result)) :
    Applies P H "vibe:has-fvar-args" [encodeTable table, .list (encodeTerms terms)] (boolean result) := by
  refine Applies.equation (equation := A[9])
    (environment := [("table", encodeTable table), ("arguments", .list (encodeTerms terms))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (encodeTerms terms))

private theorem hasFvar_args_cons (table : SignatureTable) (first : Spec.Term) (rest : List Spec.Term)
    (firstValue restValue : Bool)
    (head : Applies P H "vibe:has-fvar" [encodeTable table, encode first] (boolean firstValue))
    (tail : Applies P H "vibe:has-fvar-args" [encodeTable table, .list (encodeTerms rest)] (boolean restValue)) :
    Applies P H "vibe:has-fvar-view" [encodeTable table, listView (encodeTerms (first :: rest))]
      (boolean (firstValue || restValue)) := by
  refine Applies.equation (equation := A[11])
    (environment := [("table", encodeTable table), ("first", encode first), ("rest", .list (encodeTerms rest))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean firstValue, encodeTable table, .list (encodeTerms rest)])
    (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) head
  · cases firstValue with
    | true => exact ⟨1, rfl⟩
    | false =>
        refine Applies.equation (equation := A[13])
          (environment := [("table", encodeTable table), ("rest", .list (encodeTerms rest))])
          (by rfl) (by rfl) ?_
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) tail

mutual

theorem hasFvar_computes (table : SignatureTable) (term : Spec.Term) :
    Applies P H "vibe:has-fvar" [encodeTable table, encode term]
      (boolean (Spec.hasFvar (signatureOf table) term)) := by
  cases term with
  | bvar _ => exact ⟨1, rfl⟩
  | lit _ => exact ⟨1, rfl⟩
  | app symbol terms =>
      exact hasFvar_app_start table symbol terms _
        (hasFvar_head table terms _ _ (hasFvarList_computes table terms))

theorem hasFvarList_computes (table : SignatureTable) (terms : List Spec.Term) :
    Applies P H "vibe:has-fvar-args" [encodeTable table, .list (encodeTerms terms)]
      (boolean (Spec.hasFvarList (signatureOf table) terms)) := by
  cases terms with
  | nil => exact hasFvar_args_start table [] false ⟨1, rfl⟩
  | cons first rest =>
      exact hasFvar_args_start table (first :: rest) _
        (hasFvar_args_cons table first rest _ _ (hasFvar_computes table first) (hasFvarList_computes table rest))

end

private theorem app_start (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (symbol : Spec.SymId) (terms : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-pruned"
      [boolean (Spec.hasFvar (signatureOf table) (.app symbol terms)), encodeTable table, encodeSymbol F,
        natural arity, encode value, natural offset, encodeSymbol symbol, .list (encodeTerms terms)] result) :
    Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encode (.app symbol terms)] result := by
  refine Applies.equation (equation := A[16])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("offset", natural offset), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) .nil)))))))) next
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (hasFvar_computes table (.app symbol terms))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (Applies.constructor (by rfl) (by rfl))

private theorem app_traverse (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (symbol : Spec.SymId) (terms : List Spec.Term) (middle result : Term)
    (children : Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders (bindersOf (signatureOf table) symbol), .list (encodeTerms terms)] middle)
    (next : Applies P H "vibe:inst-args-result" [middle, encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeSymbol symbol] result) :
    Applies P H "vibe:inst-pruned" [.sym "True", encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeSymbol symbol, .list (encodeTerms terms)] result := by
  refine Applies.equation (equation := A[18])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("offset", natural offset), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) next
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ (.cons (.variable (by rfl)) .nil))))))) children
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (binders_applies table symbol)

private theorem app_processed (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (symbol : Spec.SymId) (terms : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-head" [boolean (decide (symbol = F)), encodeTable table, encodeSymbol F,
      natural arity, encode value, natural offset, encodeSymbol symbol, .list (encodeTerms terms)] result) :
    Applies P H "vibe:inst-args-result" [encodeTermsResult (some terms), encodeTable table, encodeSymbol F,
      natural arity, encode value, natural offset, encodeSymbol symbol] result := by
  refine Applies.equation (equation := A[20])
    (environment := [("arguments", .list (encodeTerms terms)), ("table", encodeTable table), ("F", encodeSymbol F),
      ("arity", natural arity), ("value", encode value), ("offset", natural offset), ("symbol", encodeSymbol symbol)])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) .nil)))))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (symbol_applies symbol F)

private theorem app_target (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (symbol : Spec.SymId) (terms : List Spec.Term) :
    Applies P H "vibe:inst-head" [.sym "True", encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeSymbol symbol, .list (encodeTerms terms)]
      (encodeResult ((Spec.shift (signatureOf table) offset arity value).bind
        (fun shifted => Spec.substBVars (signatureOf table) arity terms shifted 0))) := by
  refine Applies.equation (equation := A[22])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("offset", natural offset), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeResult (Spec.shift (signatureOf table) offset arity value),
      encodeTable table, natural arity, .list (encodeTerms terms)]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) (shift_applies table offset arity value)
  · cases foundShift : Spec.shift (signatureOf table) offset arity value with
    | none => exact ⟨1, rfl⟩
    | some shifted =>
        refine Applies.equation (equation := A[24])
          (environment := [("value", encode shifted), ("table", encodeTable table),
            ("arity", natural arity), ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil))))) (subst_applies table arity terms shifted 0)

private theorem app_result (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (symbol : Spec.SymId) (terms : List Spec.Term) (processed : Option (List Spec.Term))
    (children : Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders (bindersOf (signatureOf table) symbol), .list (encodeTerms terms)]
      (encodeTermsResult processed)) :
    Applies P H "vibe:inst-pruned" [.sym "True", encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeSymbol symbol, .list (encodeTerms terms)]
      (encodeResult (processed.bind fun terms' => if symbol = F then
        (Spec.shift (signatureOf table) offset arity value).bind
          (fun shifted => Spec.substBVars (signatureOf table) arity terms' shifted 0)
        else some (.app symbol terms'))) := by
  refine app_traverse table F arity offset value symbol terms _ _ children ?_
  cases processed with
  | none => exact ⟨1, rfl⟩
  | some terms' =>
      simp only [option_bind_match]
      apply app_processed
      by_cases target : symbol = F
      · simpa only [target, boolean, decide_true, ↓reduceIte, option_bind_match] using app_target table F arity offset value symbol terms'
      · simp only [target, boolean, decide_false, ↓reduceIte]
        exact ⟨3, rfl⟩

private theorem args_start (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (binders : List Nat) (terms : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-args-view" [encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders binders, listView (encodeTerms terms)] result) :
    Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encodeBinders binders, .list (encodeTerms terms)] result := by
  refine Applies.equation (equation := A[25])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("offset", natural offset), ("binders", encodeBinders binders),
      ("arguments", .list (encodeTerms terms))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ .nil))))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (encodeTerms terms))

private theorem args_cons (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-args-binder" [encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, listView (binders.map natural), encode first, .list (encodeTerms rest)] result) :
    Applies P H "vibe:inst-args-view" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encodeBinders binders, listView (encodeTerms (first :: rest))] result := by
  refine Applies.equation (equation := A[27])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("offset", natural offset), ("binders", encodeBinders binders),
      ("first", encode first), ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (binders.map natural))

private theorem args_binder (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-args-bound"
      [boolean (decide (offset + binders.headD 0 < Spec.wordBound)), encodeTable table, encodeSymbol F,
        natural arity, encode value, natural offset, encodeBinders binders.tail,
        natural (offset + binders.headD 0), encode first, .list (encodeTerms rest)] result) :
    Applies P H "vibe:inst-args-binder" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, listView (binders.map natural), encode first, .list (encodeTerms rest)] result := by
  cases binders with
  | nil =>
      refine Applies.equation (equation := A[28])
        (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
          ("value", encode value), ("offset", natural offset), ("first", encode first),
          ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (PassiveData.evaluates (.list (by simp)) _) (.cons (.variable (by rfl))
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (lt_applies offset Spec.wordBound)
  | cons bound tail =>
      refine Applies.equation (equation := A[29])
        (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
          ("value", encode value), ("offset", natural offset), ("bound", natural bound),
          ("tail", encodeBinders tail), ("first", encode first), ("rest", .list (encodeTerms rest))])
        (by rfl) (by rfl) ?_
      have sum : Evaluates P H [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
          ("value", encode value), ("offset", natural offset), ("bound", natural bound),
          ("tail", encodeBinders tail), ("first", encode first), ("rest", .list (encodeTerms rest))]
          (.expr [.sym "nik:nat-add", .var "offset", .var "bound"]) (natural (offset + bound)) :=
        Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (add_applies offset bound)
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons sum (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons sum (.cons (.literal _ _ _ _) .nil)) (lt_applies (offset + bound) Spec.wordBound)

private theorem args_bound (table : SignatureTable) (F : Spec.SymId) (arity offset inside : Nat)
    (value : Spec.Term) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (middle result : Term)
    (child : Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural inside, encode first] middle)
    (next : Applies P H "vibe:inst-args-first" [middle, encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders binders, .list (encodeTerms rest)] result) :
    Applies P H "vibe:inst-args-bound" [.sym "True", encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders binders, natural inside, encode first, .list (encodeTerms rest)]
      result := by
  refine Applies.equation (equation := A[31])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("offset", natural offset), ("binders", encodeBinders binders),
      ("inside", natural inside), ("first", encode first), ("rest", .list (encodeTerms rest))])
    (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) .nil)))))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) child

private theorem args_first_some (table : SignatureTable) (F : Spec.SymId) (arity offset : Nat)
    (value : Spec.Term) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (middle result : Term)
    (tail : Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encodeBinders binders, .list (encodeTerms rest)] middle)
    (next : Applies P H "vibe:inst-args-rest" [encode first, middle] result) :
    Applies P H "vibe:inst-args-first" [encodeResult (some first), encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders binders, .list (encodeTerms rest)] result := by
  refine Applies.equation (equation := A[33])
    (environment := [("first", encode first), ("table", encodeTable table), ("F", encodeSymbol F),
      ("arity", natural arity), ("value", encode value), ("offset", natural offset),
      ("binders", encodeBinders binders), ("rest", .list (encodeTerms rest))]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))))) tail

private theorem args_children (table : SignatureTable) (F : Spec.SymId) (arity offset inside : Nat)
    (value : Spec.Term) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term)
    (firstResult : Option Spec.Term) (restResult : Option (List Spec.Term))
    (head : Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural inside, encode first] (encodeResult firstResult))
    (tail : Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encodeBinders binders, .list (encodeTerms rest)] (encodeTermsResult restResult)) :
    Applies P H "vibe:inst-args-bound" [.sym "True", encodeTable table, encodeSymbol F, natural arity,
      encode value, natural offset, encodeBinders binders, natural inside, encode first, .list (encodeTerms rest)]
      (encodeTermsResult (firstResult.bind (fun first' => restResult.map (List.cons first')))) := by
  refine args_bound table F arity offset inside value binders first rest _ _ head ?_
  cases firstResult with
  | none => exact ⟨1, rfl⟩
  | some first' =>
      refine args_first_some table F arity offset value binders first' rest _ _ tail ?_
      cases restResult with
      | none => exact ⟨1, rfl⟩
      | some rest' => exact ⟨3, rfl⟩

mutual

theorem instGo_computes (table : SignatureTable) (F : Spec.SymId) (arity : Nat) (value : Spec.Term)
    (offset : Nat) (term : Spec.Term) :
    Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encode term] (encodeResult (Spec.instGo (signatureOf table) F arity value offset term)) := by
  cases term with
  | bvar _ => exact ⟨3, rfl⟩
  | lit _ => exact ⟨3, rfl⟩
  | app symbol terms =>
      apply app_start
      cases present : Spec.hasFvar (signatureOf table) (.app symbol terms) with
      | false => simp only [Spec.instGo, present, ↓reduceIte]; exact ⟨3, rfl⟩
      | true =>
          have computed := app_result table F arity offset value symbol terms _
            (instList_computes table F arity value offset (bindersOf (signatureOf table) symbol) terms)
          simp only [Spec.instGo, present, Bool.true_eq_false, ↓reduceIte, instArgs_eq, List.drop_zero]
          cases processed : instList (signatureOf table) F arity value offset (bindersOf (signatureOf table) symbol) terms with
          | none => simpa only [processed, option_bind_match, boolean, ↓reduceIte] using computed
          | some terms' =>
              by_cases target : symbol = F
              · subst symbol
                cases shifted : Spec.shift (signatureOf table) offset arity value <;>
                  simpa only [processed, shifted, option_bind_match, boolean, ↓reduceIte] using computed
              · simpa only [processed, target, option_bind_match, boolean, ↓reduceIte] using computed

theorem instList_computes (table : SignatureTable) (F : Spec.SymId) (arity : Nat) (value : Spec.Term)
    (offset : Nat) (binders : List Nat) (terms : List Spec.Term) :
    Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encodeBinders binders, .list (encodeTerms terms)]
      (encodeTermsResult (instList (signatureOf table) F arity value offset binders terms)) := by
  cases terms with
  | nil => exact args_start table F arity offset value binders [] _ ⟨2, rfl⟩
  | cons first rest =>
      apply args_start
      apply args_cons
      apply args_binder
      by_cases fits : offset + binders.headD 0 < Spec.wordBound
      · have computed := args_children table F arity offset (offset + binders.headD 0) value binders.tail first rest _ _
          (instGo_computes table F arity value (offset + binders.headD 0) first)
          (instList_computes table F arity value offset binders.tail rest)
        simp only [instList, boolean, fits, decide_true, ↓reduceIte]
        convert computed using 2
        cases headResult : Spec.instGo (signatureOf table) F arity value (offset + binders.headD 0) first <;>
          cases tailResult : instList (signatureOf table) F arity value offset binders.tail rest <;> rfl
      · simp only [instList, boolean, fits, decide_false, ↓reduceIte]
        exact ⟨1, rfl⟩

end

private theorem statement_start (table : SignatureTable) (F : Spec.SymId)
    (value statement : Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-declaration"
      [encodeInfoResult (signatureOf table F), encodeTable table, encodeSymbol F, encode value, encode statement] result) :
    Applies P H "vibe:instantiate"
      [encodeTable table, encodeSymbol F, encode value, encode statement] result := by
  refine Applies.equation (equation := A[36])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F),
      ("value", encode value), ("statement", encode statement)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (lookup_applies table F)

private theorem statement_arity (table : SignatureTable) (F : Spec.SymId)
    (binders : List Nat) (value statement : Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-arity"
      [natural binders.length, encodeTable table, encodeSymbol F, encode value, encode statement] result) :
    Applies P H "vibe:inst-declaration"
      [.expr [.sym "Some", .expr [.sym "Vibe:SymInfo", .sym "Fvar", encodeBinders binders]],
        encodeTable table, encodeSymbol F, encode value, encode statement] result := by
  refine Applies.equation (equation := A[39])
    (environment := [("binders", encodeBinders binders), ("table", encodeTable table), ("F", encodeSymbol F),
      ("value", encode value), ("statement", encode statement)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [natural binders.length, encodeTable table, encodeSymbol F,
      encode value, encode statement]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) ?_
  simpa only [encodeBinders, List.length_map] using length_applies (binders.map natural)

private theorem statement_depth (table : SignatureTable) (F : Spec.SymId) (arity : Nat)
    (value statement : Spec.Term) (result : Term)
    (next : Applies P H "vibe:inst-value-depth"
      [boolean (decide (Spec.depth (signatureOf table) value ≤ arity)), encodeTable table,
        encodeSymbol F, natural arity, encode value, encode statement] result) :
    Applies P H "vibe:inst-arity"
      [natural arity, encodeTable table, encodeSymbol F, encode value, encode statement] result := by
  refine Applies.equation (equation := A[40])
    (environment := [("arity", natural arity), ("table", encodeTable table), ("F", encodeSymbol F),
      ("value", encode value), ("statement", encode statement)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (le_applies (Spec.depth (signatureOf table) value) arity)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (depth_applies table value)

private theorem statement_result (table : SignatureTable) (result : Option Spec.Term) :
    Applies P H "vibe:inst-statement-result" [encodeResult result, encodeTable table]
      (encodeResult (result.bind (fun output =>
        if Spec.depth (signatureOf table) output = 0 then some output else none))) := by
  cases result with
  | none => exact ⟨1, rfl⟩
  | some output =>
      simp only [option_bind_match]
      refine Applies.equation (equation := A[44])
        (environment := [("result", encode output), ("table", encodeTable table)]) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [.sym (if Spec.depth (signatureOf table) output = 0 then "True" else "False"),
          encode output]) (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (zero_applies (Spec.depth (signatureOf table) output))
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (depth_applies table output)
      · by_cases closed : Spec.depth (signatureOf table) output = 0
        · simp only [closed, ↓reduceIte]; exact ⟨3, rfl⟩
        · simp only [closed, ↓reduceIte]; exact ⟨1, rfl⟩

private theorem statement_valid (table : SignatureTable) (F : Spec.SymId) (arity : Nat)
    (value statement : Spec.Term) :
    Applies P H "vibe:inst-value-depth"
      [.sym "True", encodeTable table, encodeSymbol F, natural arity, encode value, encode statement]
      (encodeResult ((Spec.instGo (signatureOf table) F arity value 0 statement).bind
        (fun output => if Spec.depth (signatureOf table) output = 0 then some output else none))) := by
  refine Applies.equation (equation := A[42])
    (environment := [("table", encodeTable table), ("F", encodeSymbol F), ("arity", natural arity),
      ("value", encode value), ("statement", encode statement)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (statement_result table _)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) (.cons (.variable (by rfl)) .nil))))))
    (instGo_computes table F arity value 0 statement)

theorem instantiation_computes (table : SignatureTable) (F : Spec.SymId) (value statement : Spec.Term) :
    Applies P H "vibe:instantiate" [encodeTable table, encodeSymbol F, encode value, encode statement]
      (encodeResult (Spec.instantiateStatement (signatureOf table) F value statement)) := by
  apply statement_start
  cases declared : signatureOf table F with
  | none => simp only [Spec.instantiateStatement, declared]; exact ⟨1, rfl⟩
  | some info =>
      cases kind : info.kind with
      | constant =>
          simp only [Spec.instantiateStatement, declared, kind]
          exact ⟨1, by simp only [encodeInfoResult, encodeInfo, kind, encodeKind]; rfl⟩
      | fvar =>
          simp only [Spec.instantiateStatement, declared, kind, true_and]
          simp only [encodeInfoResult, encodeInfo, kind, encodeKind]
          apply statement_arity
          apply statement_depth
          simp only [Spec.SymInfo.arity]
          by_cases fits : Spec.depth (signatureOf table) value ≤ info.binders.length
          · simp only [fits, boolean, decide_true, ↓reduceIte]
            have computed := statement_valid table F info.binders.length value statement
            cases processed : Spec.instGo (signatureOf table) F info.binders.length value 0 statement <;>
              simpa only [processed, option_bind_match] using computed
          · simp only [fits, boolean, decide_false, ↓reduceIte]
            exact ⟨1, rfl⟩

theorem instantiation_result_exact (table : SignatureTable) (F : Spec.SymId)
    (value statement : Spec.Term) (result : Term) :
    Applies P H "vibe:instantiate" [encodeTable table, encodeSymbol F, encode value, encode statement] result ↔
      result = encodeResult (Spec.instantiateStatement (signatureOf table) F value statement) := by
  constructor
  · intro computed
    exact computed.deterministic (instantiation_computes table F value statement)
  · intro same
    subst result
    exact instantiation_computes table F value statement

theorem instantiation_accepts_iff (table : SignatureTable) (F : Spec.SymId)
    (value statement result : Spec.Term) :
    Applies P H "vibe:instantiate" [encodeTable table, encodeSymbol F, encode value, encode statement]
      (encodeResult (some result)) ↔ Spec.instantiateStatement (signatureOf table) F value statement = some result := by
  rw [instantiation_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem instantiation_refuses_iff (table : SignatureTable) (F : Spec.SymId) (value statement : Spec.Term) :
    Applies P H "vibe:instantiate" [encodeTable table, encodeSymbol F, encode value, encode statement]
      (encodeResult none) ↔ Spec.instantiateStatement (signatureOf table) F value statement = none := by
  rw [instantiation_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem instantiation_completed_exact (table : SignatureTable) (F : Spec.SymId)
    (value statement : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:instantiate"
      [encodeTable table, encodeSymbol F, encode value, encode statement] ≠ .exhausted) :
    apply P H fuel "vibe:instantiate" [encodeTable table, encodeSymbol F, encode value, encode statement] =
      .value (encodeResult (Spec.instantiateStatement (signatureOf table) F value statement)) :=
  (instantiation_computes table F value statement).completed fuel finished

theorem instGo_result_exact (table : SignatureTable) (F : Spec.SymId) (arity : Nat)
    (value : Spec.Term) (offset : Nat) (term : Spec.Term) (result : Term) :
    Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encode term] result ↔ result = encodeResult (Spec.instGo (signatureOf table) F arity value offset term) := by
  constructor
  · intro computed
    exact computed.deterministic (instGo_computes table F arity value offset term)
  · intro same
    subst result
    exact instGo_computes table F arity value offset term

theorem instGo_accepts_iff (table : SignatureTable) (F : Spec.SymId) (arity : Nat)
    (value : Spec.Term) (offset : Nat) (term result : Spec.Term) :
    Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encode term] (encodeResult (some result)) ↔
      Spec.instGo (signatureOf table) F arity value offset term = some result := by
  rw [instGo_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem instGo_refuses_iff (table : SignatureTable) (F : Spec.SymId) (arity : Nat)
    (value : Spec.Term) (offset : Nat) (term : Spec.Term) :
    Applies P H "vibe:inst-go" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encode term] (encodeResult none) ↔
      Spec.instGo (signatureOf table) F arity value offset term = none := by
  rw [instGo_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm, fun same => congrArg encodeResult same.symm⟩

theorem instList_result_exact (table : SignatureTable) (F : Spec.SymId) (arity : Nat)
    (value : Spec.Term) (offset : Nat) (binders : List Nat) (terms : List Spec.Term) (result : Term) :
    Applies P H "vibe:inst-args" [encodeTable table, encodeSymbol F, natural arity, encode value,
      natural offset, encodeBinders binders, .list (encodeTerms terms)] result ↔
      result = encodeTermsResult (instList (signatureOf table) F arity value offset binders terms) := by
  constructor
  · intro computed
    exact computed.deterministic (instList_computes table F arity value offset binders terms)
  · intro same
    subst result
    exact instList_computes table F arity value offset binders terms

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation
