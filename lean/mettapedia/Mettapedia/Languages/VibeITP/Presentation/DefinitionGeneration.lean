import Mettapedia.Languages.VibeITP.Presentation.DefinitionOccurrences

/-!
# Complete authored definition construction

Arity vectors and eta terms are data computations. The query additionally
checks the submitted body's formation, closedness and exact hint conditions.
Unrestricted natural arities are preserved in the constructed statement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions

open ComputationalData ComputationalShift ComputationalSubstitution
open ComputationalInstantiation ComputationalInference ComputationalLiterals
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => definitionProgram
local notation "A" => definitionEquations
local notation "H" => productDivisionHost

theorem definition_bvar (index : Nat) :
    Applies P H "Vibe:BVar" [natural index] (encode (.bvar index)) :=
  .constructor (by decide +kernel) (by rfl)

theorem definition_app (symbol : Spec.SymId) (arguments : List Spec.Term) :
    Applies P H "Vibe:App" [encodeSymbol symbol, .list (encodeTerms arguments)]
      (encode (.app symbol arguments)) :=
  .constructor (by decide +kernel) (by rfl)

theorem definition_depth (table : SignatureTable) (body : Spec.Term) :
    Applies P H "vibe:depth" [encodeTable table, encode body]
      (natural (Spec.depth (signatureOf table) body)) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  apply reuse_instantiation_call (by decide +kernel)
  apply reuse_substitution_call (by decide +kernel)
  exact depth_computes_in_substitution table body

theorem definition_formed (table : SignatureTable) (body : Spec.Term) :
    Applies P H "vibe:well-formed" [encodeTable table, encode body]
      (boolean (Spec.WellFormed (signatureOf table) body)) := by
  apply reuse_literal_call (by decide +kernel)
  apply reuse_inference_call (by decide +kernel)
  exact wellFormed_computes table body

theorem descending_computes (arity : Nat) :
    Applies P H "vibe:def-desc" [natural arity]
      (.list (encodeTerms ((List.range arity).reverse.map Spec.Term.bvar))) := by
  induction arity with
  | zero =>
      refine definition_equation (equation := A[38]) (environment := [("arity", natural 0)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [.sym "True", natural 0]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_zero 0)
      · exact ⟨2, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | succ arity ih =>
      refine definition_equation (equation := A[38]) (environment := [("arity", natural (arity + 1))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [.sym "False", natural (arity + 1)]) (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_zero (arity + 1))
      · refine definition_equation (equation := A[40]) (environment := [("arity", natural (arity + 1))])
          (by decide +kernel) (by rfl) (by rfl) ?_
        have descending : (List.range (arity + 1)).reverse.map Spec.Term.bvar =
            Spec.Term.bvar arity :: (List.range arity).reverse.map Spec.Term.bvar := by
          simp [List.range_succ]
        rw [descending, encodeTerms]
        refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (definition_cons _ _)
        · exact Evaluates.call (by simp [Special])
            (.cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
              (definition_pred (arity + 1))) .nil) (definition_bvar arity)
        · exact Evaluates.call (by simp [Special])
            (.cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
              (definition_pred (arity + 1))) .nil) ih

theorem etaTerms_computes (signature : Spec.Sig) (parameters : List Spec.SymId) :
    Applies P H "vibe:def-etas" [encodeSymbols parameters, encodeBinders (parameters.map (Spec.symArity signature))]
      (.list (encodeTerms (parameters.map fun parameter => Spec.etaFvar parameter (Spec.symArity signature parameter)))) := by
  induction parameters with
  | nil =>
      refine definition_equation (equation := A[41])
        (environment := [("parameters", encodeSymbols []), ("arities", encodeBinders [])])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [.sym "List:Nil", .sym "List:Nil"])
        (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view [])
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view [])
      · exact ⟨2, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | cons parameter rest ih =>
      refine definition_equation (equation := A[41])
        (environment := [("parameters", encodeSymbols (parameter :: rest)),
          ("arities", encodeBinders ((parameter :: rest).map (Spec.symArity signature)))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [listView ((parameter :: rest).map encodeSymbol),
          listView (((parameter :: rest).map (Spec.symArity signature)).map natural)]) (by simp [Special])
        (.cons ?_ (.cons ?_ .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (definition_view _)
      · refine definition_equation (equation := A[43])
          (environment := [("parameter", encodeSymbol parameter), ("rest", encodeSymbols rest),
            ("arity", natural (Spec.symArity signature parameter)),
            ("arities", encodeBinders (rest.map (Spec.symArity signature)))])
          (by decide +kernel) (by rfl) (by rfl) ?_
        simp only [List.map_cons, encodeTerms]
        refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons ?_ .nil)) (definition_cons _ _)
        · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
            (.cons (Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
              (descending_computes _)) .nil)) (definition_app _ _)
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih

theorem definitionInfo_computes (table : SignatureTable) (parameters : List Spec.SymId) :
    Applies P H "vibe:def-info" [encodeTable table, encodeSymbols parameters]
      (encodeInfoResult (if parameters.all (Spec.isFvarSym (signatureOf table)) then
        some (Spec.definitionInfo (signatureOf table) parameters) else none)) := by
  refine definition_equation (equation := A[8])
    (environment := [("table", encodeTable table), ("parameters", encodeSymbols parameters)])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeNatResult (parameterArities (signatureOf table) parameters)])
    (by simp [Special]) (.cons ?_ .nil) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (parameterArities_computes table parameters)
  · rw [parameterArities_eq]
    cases valid : parameters.all (Spec.isFvarSym (signatureOf table)) with
    | false => exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
    | true =>
        refine definition_equation (equation := A[10])
          (environment := [("binders", encodeBinders (parameters.map (Spec.symArity (signatureOf table))))])
          (by decide +kernel) (by rfl) (by rfl) ?_
        refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (definition_some _)
        exact Evaluates.call (by simp [Special])
          (.cons (.symbol _ _ _ _) (.cons (.variable (by rfl)) .nil))
          (.constructor (by decide +kernel) (by rfl))

theorem hintsAdmit_consumption (parameters : List Spec.SymId) (hints : List Nat) (occurrences : List Spec.SymId) :
    Spec.hintsAdmit parameters hints occurrences =
      (hints.all (· < parameters.length) && (consumeHints parameters occurrences hints).isSome) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using
    hintsAdmit_iff parameters hints occurrences

private theorem definition_result_stages (signature : Spec.Sig) (request : DefinitionRequest) :
    request.result signature =
      if Spec.WellFormed signature request.body then
        if Spec.depth signature request.body = 0 then
          (parameterArities signature request.parameters).bind fun _ =>
            if request.hints.all (· < request.parameters.length) then
              (consumeHints request.parameters (Spec.fvarOccurrences signature request.body) request.hints).map
                fun _ => Spec.definitionStatement signature request.constant request.parameters request.body
            else none
        else none
      else none := by
  rw [DefinitionRequest.result, Spec.definitionAdmissible, hintsAdmit_consumption, parameterArities_eq]
  cases formed : Spec.WellFormed signature request.body <;>
    by_cases closed : Spec.depth signature request.body = 0 <;>
    cases parameters : request.parameters.all (Spec.isFvarSym signature) <;>
    cases bounds : request.hints.all (· < request.parameters.length) <;>
    cases consumeHints request.parameters (Spec.fvarOccurrences signature request.body) request.hints <;>
    simp_all

private theorem definition_consumed (signature : Spec.Sig) (request : DefinitionRequest)
    (remaining : Option (List Nat)) :
    Applies P H "vibe:def-consumed" [encodeNatResult remaining, encodeSymbol request.constant,
      encodeSymbols request.parameters, encode request.body,
      encodeBinders (request.parameters.map (Spec.symArity signature))]
      (encodeResult (remaining.map fun _ =>
        Spec.definitionStatement signature request.constant request.parameters request.body)) := by
  cases remaining with
  | none => exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | some remaining =>
      refine definition_equation (equation := A[54])
        (environment := [("unused-hints", encodeBinders remaining), ("constant", encodeSymbol request.constant),
          ("parameters", encodeSymbols request.parameters), ("body", encode request.body),
          ("arities", encodeBinders (request.parameters.map (Spec.symArity signature)))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (definition_some _)
      refine Evaluates.call (by simp [Special])
        (.cons ((encodedSymbol_passive _ _ (.builtin .eq)).evaluates _) (.cons ?_ .nil)) (definition_app _ _)
      refine Evaluates.list (.cons ?_ (.cons (.variable (by rfl)) .nil))
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
        (.cons (Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (etaTerms_computes signature request.parameters)) .nil)) (definition_app _ _)

private def hintedResult (signature : Spec.Sig) (request : DefinitionRequest) : Option Spec.Term :=
  if request.hints.all (· < request.parameters.length) then
    (consumeHints request.parameters (Spec.fvarOccurrences signature request.body) request.hints).map
      fun _ => Spec.definitionStatement signature request.constant request.parameters request.body
  else none

private def parameterResult (signature : Spec.Sig) (request : DefinitionRequest) : Option Spec.Term :=
  (parameterArities signature request.parameters).bind fun _ => hintedResult signature request

private def closedResult (signature : Spec.Sig) (request : DefinitionRequest) : Option Spec.Term :=
  if Spec.depth signature request.body = 0 then parameterResult signature request else none

private theorem definition_hints (table : SignatureTable) (request : DefinitionRequest) :
    Applies P H "vibe:def-hints" [boolean (request.hints.all (· < request.parameters.length)),
      encodeTable table, encodeSymbol request.constant, encodeSymbols request.parameters,
      encodeBinders request.hints, encode request.body,
      encodeBinders (request.parameters.map (Spec.symArity (signatureOf table)))]
      (encodeResult (hintedResult (signatureOf table) request)) := by
  cases bounds : request.hints.all (· < request.parameters.length) with
  | false =>
      simp only [hintedResult, bounds, boolean, encodeResult]
      exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      simp only [hintedResult, bounds, boolean, ↓reduceIte]
      refine definition_equation (equation := A[52])
        (environment := [("table", encodeTable table), ("constant", encodeSymbol request.constant),
          ("parameters", encodeSymbols request.parameters), ("hints", encodeBinders request.hints),
          ("body", encode request.body),
          ("arities", encodeBinders (request.parameters.map (Spec.symArity (signatureOf table))))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
          (definition_consumed (signatureOf table) request _)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (consume_computes table request.parameters request.hints request.body)

private theorem definition_parameters (table : SignatureTable) (request : DefinitionRequest) :
    Applies P H "vibe:def-parameters"
      [encodeNatResult (parameterArities (signatureOf table) request.parameters), encodeTable table,
        encodeSymbol request.constant, encodeSymbols request.parameters, encodeBinders request.hints,
        encode request.body] (encodeResult (parameterResult (signatureOf table) request)) := by
  rw [parameterResult, parameterArities_eq]
  cases parameters : request.parameters.all (Spec.isFvarSym (signatureOf table)) with
  | false => exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      simp only [↓reduceIte, Option.bind_some, encodeNatResult]
      refine definition_equation (equation := A[50])
        (environment := [("arities", encodeBinders (request.parameters.map (Spec.symArity (signatureOf table)))),
          ("table", encodeTable table), ("constant", encodeSymbol request.constant),
          ("parameters", encodeSymbols request.parameters), ("hints", encodeBinders request.hints),
          ("body", encode request.body)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))
            (definition_hints table request)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (parameterHintBounds_computes request.parameters request.hints)

private theorem definition_closed (table : SignatureTable) (request : DefinitionRequest) :
    Applies P H "vibe:def-closed" [boolean (decide (Spec.depth (signatureOf table) request.body = 0)),
      encodeTable table, encodeSymbol request.constant, encodeSymbols request.parameters,
      encodeBinders request.hints, encode request.body]
      (encodeResult (closedResult (signatureOf table) request)) := by
  by_cases closed : Spec.depth (signatureOf table) request.body = 0
  · simp only [closedResult, closed, ↓reduceIte, decide_true, boolean]
    refine definition_equation (equation := A[48])
      (environment := [("table", encodeTable table), ("constant", encodeSymbol request.constant),
        ("parameters", encodeSymbols request.parameters), ("hints", encodeBinders request.hints),
        ("body", encode request.body)]) (by decide +kernel) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) .nil)))))) (definition_parameters table request)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
        (parameterArities_computes table request.parameters)
  · simp only [closedResult, closed, ↓reduceIte, decide_false, boolean, encodeResult]
    exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩

private theorem definition_formation (table : SignatureTable) (request : DefinitionRequest) :
    Applies P H "vibe:def-formed" [boolean (Spec.WellFormed (signatureOf table) request.body),
      encodeTable table, encodeSymbol request.constant, encodeSymbols request.parameters,
      encodeBinders request.hints, encode request.body]
      (encodeResult (if Spec.WellFormed (signatureOf table) request.body then
        closedResult (signatureOf table) request else none)) := by
  cases formed : Spec.WellFormed (signatureOf table) request.body with
  | false => exact ⟨1, by rw [definition_apply _ (by decide +kernel)]; rfl⟩
  | true =>
      refine definition_equation (equation := A[46])
        (environment := [("table", encodeTable table), ("constant", encodeSymbol request.constant),
          ("parameters", encodeSymbols request.parameters), ("hints", encodeBinders request.hints),
          ("body", encode request.body)]) (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) .nil)))))) (definition_closed table request)
      exact Evaluates.call (by simp [Special]) (.cons (Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (definition_depth table request.body)) .nil) (definition_zero _)

theorem definitionQuery_computes (table : SignatureTable) (request : DefinitionRequest) :
    Applies P H "vibe:definition-query" [encodeTable table, encodeSymbol request.constant,
      encodeSymbols request.parameters, encodeBinders request.hints, encode request.body]
      (encodeResult (request.result (signatureOf table))) := by
  rw [definition_result_stages]
  refine definition_equation (equation := A[44])
    (environment := [("table", encodeTable table), ("constant", encodeSymbol request.constant),
      ("parameters", encodeSymbols request.parameters), ("hints", encodeBinders request.hints),
      ("body", encode request.body)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) .nil)))))) (definition_formation table request)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (definition_formed table request.body)

end Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions
