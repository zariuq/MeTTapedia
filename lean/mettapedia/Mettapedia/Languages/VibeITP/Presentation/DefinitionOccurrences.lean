import Mettapedia.Languages.VibeITP.Presentation.DefinitionProgram

/-!
# Definition parameters, bounds and occurrence consumption

The authored traversal agrees with consuming the independent specification's
preorder occurrence list. It retains child order and multiplicity without
constructing that intermediate list during execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions

open ComputationalData ComputationalShift ComputationalSubstitution
open ComputationalInstantiation ComputationalInference ComputationalLiterals
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => definitionProgram
local notation "A" => definitionEquations
local notation "H" => productDivisionHost

theorem definition_view (items : List Term) :
    Applies P H "nik:list-view" [.list items] (listView items) :=
  .primitive (by decide +kernel) (computationalHost_list_view items)

theorem definition_cons (first : Term) (rest : List Term) :
    Applies P H "nik:list-cons" [first, .list rest] (.list (first :: rest)) :=
  .primitive (by decide +kernel) (computationalHost_list_cons first rest)

theorem definition_zero (value : Nat) :
    Applies P H "nik:nat-zero" [natural value] (boolean (decide (value = 0))) := by
  apply Applies.primitive (by decide +kernel)
  rw [productDivisionHost_prior _ _ (by rfl)]
  by_cases zero : value = 0 <;> simpa [zero, boolean] using computationalHost_zero value

theorem definition_pred (value : Nat) :
    Applies P H "nik:nat-pred" [natural value] (natural value.pred) :=
  .primitive (by decide +kernel) (computationalHost_pred value)

theorem definition_lt (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  .primitive (by decide +kernel) (naturalArithmeticHost_lt left right)

theorem definition_some (value : Term) :
    Applies P H "Some" [value] (.expr [.sym "Some", value]) :=
  .constructor (by decide +kernel) (by rfl)

theorem definition_length (values : List Term) :
    Applies P H "vibe:list-length" [.list values] (natural values.length) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  apply reuse_instantiation_call (by decide +kernel)
  apply reuse_substitution_call (by decide +kernel)
  exact listLength_computes values

theorem definition_lookup (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:lookup-symbol" [encodeTable table, encodeSymbol symbol]
      (encodeInfoResult (signatureOf table symbol)) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  apply reuse_instantiation_call (by decide +kernel)
  apply reuse_substitution_call (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations computationalHost
    substitutionEquations_disjoint "vibe:lookup-symbol" (by decide +kernel) _ _).mpr
  exact lookup_computes table symbol

theorem definition_symbol (left right : Spec.SymId) :
    Applies P H "vibe:symbol-eq" [encodeSymbol left, encodeSymbol right]
      (boolean (decide (left = right))) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  apply reuse_instantiation_call (by decide +kernel)
  apply reuse_substitution_call (by decide +kernel)
  apply (Applies.append_iff shiftProgram substitutionEquations computationalHost
    substitutionEquations_disjoint "vibe:symbol-eq" (by decide +kernel) _ _).mpr
  exact symbol_computes left right

theorem definition_fvar (table : SignatureTable) (symbol : Spec.SymId) :
    Applies P H "vibe:is-fvar" [encodeTable table, encodeSymbol symbol]
      (boolean (Spec.isFvarSym (signatureOf table) symbol)) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  apply reuse_instantiation_call (by decide +kernel)
  exact isFvar_computes table symbol

theorem parameterArities_eq (signature : Spec.Sig) (parameters : List Spec.SymId) :
    parameterArities signature parameters =
      if parameters.all (Spec.isFvarSym signature) then
        some (parameters.map (Spec.symArity signature)) else none := by
  induction parameters with
  | nil => rfl
  | cons parameter rest ih =>
      cases found : signature parameter with
      | none => simp [parameterArities, Spec.isFvarSym, found]
      | some info =>
          rcases info with ⟨kind, binders⟩
          cases kind with
          | constant => simp [parameterArities, Spec.isFvarSym, found]
          | fvar =>
              cases tail : rest.all (Spec.isFvarSym signature) <;>
                simp [parameterArities, Spec.isFvarSym, Spec.symArity, found, ih, tail]

private theorem arities_start (table : SignatureTable) (parameters : List Spec.SymId) (result : Term)
    (next : Applies P H "vibe:def-arities-view"
      [encodeTable table, listView (parameters.map encodeSymbol)] result) :
    Applies P H "vibe:def-arities" [encodeTable table, encodeSymbols parameters] result := by
  refine definition_equation (equation := A[0])
    (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)

theorem parameterArities_computes (table : SignatureTable) (parameters : List Spec.SymId) :
    Applies P H "vibe:def-arities" [encodeTable table, encodeSymbols parameters]
      (encodeNatResult (parameterArities (signatureOf table) parameters)) := by
  induction parameters with
  | nil =>
      apply arities_start
      refine definition_equation (equation := A[1]) (environment := [("table", encodeTable table)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (Evaluates.list .nil) .nil) (definition_some _)
  | cons parameter rest ih =>
      apply arities_start
      refine definition_equation (equation := A[2])
        (environment := [("table", encodeTable table), ("parameter", encodeSymbol parameter),
          ("rest", encodeSymbols rest)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encodeInfoResult (signatureOf table parameter),
          encodeTable table, encodeSymbols rest]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_lookup table parameter)
      · cases found : signatureOf table parameter with
        | none =>
            simp only [parameterArities, found, encodeNatResult, encodeInfoResult]
            exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
        | some info =>
            rcases info with ⟨kind, binders⟩
            cases kind with
            | constant =>
                simp only [parameterArities, found, encodeInfoResult, encodeInfo, encodeKind]
                change Applies P H "vibe:def-arity-info" [encodeInfoResult (some ⟨.constant, binders⟩),
                  encodeTable table, encodeSymbols rest] (.sym "None")
                exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
            | fvar =>
                simp only [parameterArities, found, encodeInfoResult, encodeInfo, encodeKind]
                change Applies P H "vibe:def-arity-info" [encodeInfoResult (some ⟨.fvar, binders⟩),
                  encodeTable table, encodeSymbols rest]
                  (encodeNatResult ((parameterArities (signatureOf table) rest).bind
                    fun arities => some (binders.length :: arities)))
                refine definition_equation (equation := A[5])
                  (environment := [("binders", encodeBinders binders),
                    ("table", encodeTable table), ("rest", encodeSymbols rest)])
                  (by decide +kernel) (by rfl) (by rfl) ?_
                refine Evaluates.call (values := [natural binders.length,
                    encodeNatResult (parameterArities (signatureOf table) rest)]) (by simp [Special])
                  (.cons ?_ (.cons ?_ .nil)) ?_
                · refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) ?_
                  simpa only [encodeBinders, List.length_map] using definition_length (binders.map natural)
                · exact Evaluates.call (by simp [Special])
                    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih
                · cases tail : parameterArities (signatureOf table) rest with
                  | none =>
                      exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
                  | some arities =>
                      refine definition_equation (equation := A[7])
                        (environment := [("arity", natural binders.length), ("rest", encodeBinders arities)])
                        (by decide +kernel) (by rfl) (by rfl) ?_
                      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (definition_some _)
                      exact Evaluates.call (by simp [Special])
                        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_cons _ _)

private theorem bounds_start (count : Nat) (hints : List Nat) (result : Bool)
    (next : Applies P H "vibe:def-bounds-view"
      [natural count, listView (hints.map natural)] (boolean result)) :
    Applies P H "vibe:def-bounds-go" [natural count, encodeBinders hints] (boolean result) := by
  refine definition_equation (equation := A[12])
    (environment := [("count", natural count), ("hints", encodeBinders hints)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)

theorem hintBounds_computes (count : Nat) (hints : List Nat) :
    Applies P H "vibe:def-bounds-go" [natural count, encodeBinders hints]
      (boolean (hints.all (· < count))) := by
  induction hints with
  | nil => apply bounds_start; exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | cons index rest ih =>
      apply bounds_start
      refine definition_equation (equation := A[14])
        (environment := [("count", natural count), ("index", natural index), ("rest", encodeBinders rest)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (index < count)), natural count, encodeBinders rest])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_lt index count)
      · by_cases bound : index < count
        · simp only [bound, decide_true, boolean, List.all_cons, Bool.true_and]
          refine definition_equation (equation := A[16])
            (environment := [("count", natural count), ("rest", encodeBinders rest)])
            (by decide +kernel) (by rfl) (by rfl) ?_
          exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih
        · simp only [bound, decide_false, boolean, List.all_cons, Bool.false_and]
          exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩

theorem parameterHintBounds_computes (parameters : List Spec.SymId) (hints : List Nat) :
    Applies P H "vibe:def-bounds" [encodeSymbols parameters, encodeBinders hints]
      (boolean (hints.all (· < parameters.length))) := by
  refine definition_equation (equation := A[11])
    (environment := [("parameters", encodeSymbols parameters), ("hints", encodeBinders hints)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [natural parameters.length, encodeBinders hints]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) .nil)) (hintBounds_computes _ _)
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) ?_
  simpa only [encodeSymbols, List.length_map] using definition_length (parameters.map encodeSymbol)

private theorem at_start (parameters : List Spec.SymId) (index : Nat) (result : Term)
    (next : Applies P H "vibe:def-at-view" [listView (parameters.map encodeSymbol), natural index] result) :
    Applies P H "vibe:def-at" [encodeSymbols parameters, natural index] result := by
  refine definition_equation (equation := A[17])
    (environment := [("parameters", encodeSymbols parameters), ("index", natural index)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)

theorem parameterAt_computes (parameters : List Spec.SymId) (index : Nat) :
    Applies P H "vibe:def-at" [encodeSymbols parameters, natural index]
      (encodeSymbolResult parameters[index]?) := by
  induction parameters generalizing index with
  | nil => apply at_start; exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | cons first rest ih =>
      apply at_start
      refine definition_equation (equation := A[19])
        (environment := [("first", encodeSymbol first), ("rest", encodeSymbols rest), ("index", natural index)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (decide (index = 0)), encodeSymbol first,
          encodeSymbols rest, natural index]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_zero index)
      · cases index with
        | zero =>
            refine definition_equation (equation := A[20])
              (environment := [("first", encodeSymbol first), ("rest", encodeSymbols rest), ("index", natural 0)])
              (by decide +kernel) (by rfl) (by rfl) ?_
            exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_some _)
        | succ index =>
            refine definition_equation (equation := A[21])
              (environment := [("first", encodeSymbol first), ("rest", encodeSymbols rest),
                ("index", natural (index + 1))]) (by decide +kernel) (by rfl) (by rfl) ?_
            exact Evaluates.call (by simp [Special])
              (.cons (.variable (by rfl)) (.cons (Evaluates.call (by simp [Special])
                (.cons (.variable (by rfl)) .nil) (definition_pred (index + 1))) .nil)) (ih index)

private theorem consume_args_start (table : SignatureTable) (parameters : List Spec.SymId)
    (hints : List Nat) (arguments : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:def-consume-view" [encodeTable table, encodeSymbols parameters,
      encodeBinders hints, listView (encodeTerms arguments)] result) :
    Applies P H "vibe:def-consume-args" [encodeTable table, encodeSymbols parameters,
      encodeBinders hints, .list (encodeTerms arguments)] result := by
  refine definition_equation (equation := A[33])
    (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
      ("hints", encodeBinders hints), ("arguments", .list (encodeTerms arguments))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons ?_ .nil)))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)

private theorem consume_constant (table : SignatureTable) (parameters : List Spec.SymId)
    (hints : List Nat) (symbol : Spec.SymId) (arguments : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:def-consume-args" [encodeTable table, encodeSymbols parameters,
      encodeBinders hints, .list (encodeTerms arguments)] result) :
    Applies P H "vibe:def-consume-kind" [.sym "False", encodeTable table, encodeSymbols parameters,
      encodeBinders hints, encodeSymbol symbol, .list (encodeTerms arguments)] result := by
  refine definition_equation (equation := A[25])
    (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
      ("hints", encodeBinders hints), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms arguments))]) (by decide +kernel) (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next

private theorem consume_fvar (table : SignatureTable) (parameters : List Spec.SymId)
    (hints : List Nat) (symbol : Spec.SymId) (arguments : List Spec.Term)
    (next : ∀ remaining, Applies P H "vibe:def-consume-args" [encodeTable table, encodeSymbols parameters,
      encodeBinders remaining, .list (encodeTerms arguments)]
        (encodeNatResult (consumeHints parameters (Spec.fvarOccurrencesList (signatureOf table) arguments) remaining))) :
    Applies P H "vibe:def-consume-kind" [.sym "True", encodeTable table, encodeSymbols parameters,
      encodeBinders hints, encodeSymbol symbol, .list (encodeTerms arguments)]
      (encodeNatResult (consumeHints parameters
        (symbol :: Spec.fvarOccurrencesList (signatureOf table) arguments) hints)) := by
  refine definition_equation (equation := A[26])
    (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
      ("hints", encodeBinders hints), ("symbol", encodeSymbol symbol),
      ("arguments", .list (encodeTerms arguments))]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeTable table, encodeSymbols parameters,
      listView (hints.map natural), encodeSymbol symbol, .list (encodeTerms arguments)]) (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) ?_
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)
  · cases hints with
    | nil => exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
    | cons index rest =>
        refine definition_equation (equation := A[28])
          (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
            ("index", natural index), ("rest", encodeBinders rest), ("symbol", encodeSymbol symbol),
            ("arguments", .list (encodeTerms arguments))]) (by decide +kernel) (by rfl) (by rfl) ?_
        refine Evaluates.call (values := [encodeSymbolResult parameters[index]?, encodeTable table,
            encodeSymbols parameters, encodeBinders rest, encodeSymbol symbol, .list (encodeTerms arguments)])
          (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (parameterAt_computes parameters index)
        · cases found : parameters[index]? with
          | none =>
              simp only [encodeSymbolResult, consumeHints, found, reduceCtorEq, ↓reduceIte, encodeNatResult]
              exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
          | some parameter =>
              simp only [encodeSymbolResult]
              refine definition_equation (equation := A[30])
                (environment := [("parameter", encodeSymbol parameter), ("table", encodeTable table),
                  ("parameters", encodeSymbols parameters), ("rest", encodeBinders rest),
                  ("symbol", encodeSymbol symbol), ("arguments", .list (encodeTerms arguments))])
                (by decide +kernel) (by rfl) (by rfl) ?_
              refine Evaluates.call (values := [boolean (decide (symbol = parameter)), encodeTable table,
                  encodeSymbols parameters, encodeBinders rest, .list (encodeTerms arguments)]) (by simp [Special])
                (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
                  (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) ?_
              · exact Evaluates.call (by simp [Special])
                  (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_symbol symbol parameter)
              · by_cases same : symbol = parameter
                · subst parameter
                  simp only [consumeHints, found, ↓reduceIte, decide_true, boolean]
                  refine definition_equation (equation := A[32])
                    (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
                      ("rest", encodeBinders rest), ("arguments", .list (encodeTerms arguments))])
                    (by decide +kernel) (by rfl) (by rfl) ?_
                  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
                    (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
                      (.cons (.variable (by rfl)) .nil)))) (next rest)
                · simp only [consumeHints, found, Option.some.injEq, Ne.symm same, ↓reduceIte,
                    same, decide_false, boolean, encodeNatResult]
                  exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩

mutual

theorem consume_computes (table : SignatureTable) (parameters : List Spec.SymId)
    (hints : List Nat) (body : Spec.Term) :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols parameters, encodeBinders hints, encode body]
      (encodeNatResult (consumeHints parameters (Spec.fvarOccurrences (signatureOf table) body) hints)) := by
  cases body with
  | bvar index =>
      refine definition_equation (equation := A[22])
        (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
          ("hints", encodeBinders hints), ("index", natural index)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_some _)
  | lit bytes =>
      refine definition_equation (equation := A[23])
        (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
          ("hints", encodeBinders hints), ("bytes", .list (bytes.map encodeByte))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_some _)
  | app symbol arguments =>
      refine definition_equation (equation := A[24])
        (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
          ("hints", encodeBinders hints), ("symbol", encodeSymbol symbol),
          ("arguments", .list (encodeTerms arguments))]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [boolean (Spec.isFvarSym (signatureOf table) symbol),
          encodeTable table, encodeSymbols parameters, encodeBinders hints, encodeSymbol symbol,
          .list (encodeTerms arguments)]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
      · exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_fvar table symbol)
      · cases free : Spec.isFvarSym (signatureOf table) symbol with
        | false =>
            simp only [free, boolean, Spec.fvarOccurrences]
            exact consume_constant table parameters hints symbol arguments _
              (consumeArgs_computes table parameters hints arguments)
        | true =>
            simp only [free, boolean, Spec.fvarOccurrences, ↓reduceIte, List.cons_append, List.nil_append]
            exact consume_fvar table parameters hints symbol arguments
              (fun remaining => consumeArgs_computes table parameters remaining arguments)

theorem consumeArgs_computes (table : SignatureTable) (parameters : List Spec.SymId)
    (hints : List Nat) (arguments : List Spec.Term) :
    Applies P H "vibe:def-consume-args" [encodeTable table, encodeSymbols parameters,
      encodeBinders hints, .list (encodeTerms arguments)]
      (encodeNatResult (consumeHints parameters (Spec.fvarOccurrencesList (signatureOf table) arguments) hints)) := by
  apply consume_args_start
  cases arguments with
  | nil =>
      refine definition_equation (equation := A[34])
        (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
          ("hints", encodeBinders hints)]) (by decide +kernel) (by rfl) (by rfl) ?_
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_some _)
  | cons first rest =>
      refine definition_equation (equation := A[35])
        (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters),
          ("hints", encodeBinders hints), ("first", encode first), ("rest", .list (encodeTerms rest))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encodeNatResult
          (consumeHints parameters (Spec.fvarOccurrences (signatureOf table) first) hints),
          encodeTable table, encodeSymbols parameters, .list (encodeTerms rest)]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
            (consume_computes table parameters hints first)
      · rw [fvarOccurrencesList_cons, consumeHints_append]
        cases consumed : consumeHints parameters (Spec.fvarOccurrences (signatureOf table) first) hints with
        | none =>
            simp only [encodeNatResult, Option.bind_none]
            exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
        | some remaining =>
            simp only [encodeNatResult, Option.bind_some]
            refine definition_equation (equation := A[37])
              (environment := [("hints", encodeBinders remaining), ("table", encodeTable table),
                ("parameters", encodeSymbols parameters), ("rest", .list (encodeTerms rest))])
              (by decide +kernel) (by rfl) (by rfl) ?_
            exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
                (consumeArgs_computes table parameters remaining rest)

end

theorem consume_result_exact (table : SignatureTable) (parameters : List Spec.SymId)
    (hints : List Nat) (body : Spec.Term) (result : Term) :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols parameters, encodeBinders hints, encode body]
      result ↔ result = encodeNatResult (consumeHints parameters (Spec.fvarOccurrences (signatureOf table) body) hints) := by
  constructor
  · exact fun run => run.deterministic (consume_computes table parameters hints body)
  · rintro rfl
    exact consume_computes table parameters hints body

end Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions
