import Mettapedia.Languages.Metamath.InferenceAssertionRawApplicationShape
import Mettapedia.Languages.Metamath.InferenceAssertionApplication

/-!
# Canonical decoding of raw assertion bodies

Raw projected assertion applications carry one uninterpreted body pattern per
authored mandatory hypothesis.  This module records the additional structural
evidence that those bodies are the canonical encodings of concrete Metamath
actuals.  The indexed relation preserves authored order, typecodes, and the
exact finite substitution contributed by floating hypotheses.

Once this evidence is present, the raw leading, essential, side, and complete
premise vectors coincide with the existing canonical assertion vectors.  This
is a static syntax theorem: it neither executes a checker nor reflects child
derivations.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection

/-! ## Authored-order raw-body decoding -/

/-- Raw hypothesis bodies decode to canonical actual formulas in exact
authored order.  A floating hypothesis contributes its exact ordered binding;
an essential hypothesis contributes no binding. -/
inductive RawHypothesisBodiesDecode :
    List HypothesisView → List Pattern → List ConstantHeadedFormula →
      FiniteSubstitution → Prop where
  | nil : RawHypothesisBodiesDecode [] [] [] []
  | floating {label typecode variableName : String} {body : Pattern}
      {actual : ConstantHeadedFormula} {hypotheses : List HypothesisView}
      {bodies : List Pattern} {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (body_eq : body = formulaBodyPattern actual)
      (typecode_eq : actual.typecode = typecode)
      (tail : RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
      RawHypothesisBodiesDecode
        (.floating label typecode variableName :: hypotheses)
        (body :: bodies) (actual :: actuals)
        (⟨variableName, actual⟩ :: substitution)
  | essential {label : String} {formula actual : ConstantHeadedFormula}
      {body : Pattern} {hypotheses : List HypothesisView}
      {bodies : List Pattern} {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (body_eq : body = formulaBodyPattern actual)
      (typecode_eq : actual.typecode = formula.typecode)
      (tail : RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
      RawHypothesisBodiesDecode
        (.essential label formula :: hypotheses)
        (body :: bodies) (actual :: actuals) substitution

/-- Forgetting raw body encodings leaves the canonical authored-order
hypothesis-instance relation. -/
theorem RawHypothesisBodiesDecode.toHypothesisInstances
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
    HypothesisInstances hypotheses actuals substitution := by
  induction decoding with
  | nil => exact .nil
  | floating _body_eq typecode_eq _tail ih =>
      exact .floating typecode_eq ih
  | essential _body_eq typecode_eq _tail ih =>
      exact .essential typecode_eq ih

/-- The raw body vector is exactly the pointwise canonical body encoding of
the actual vector. -/
theorem RawHypothesisBodiesDecode.bodies_eq_map_formulaBodyPattern
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
    bodies = actuals.map formulaBodyPattern := by
  induction decoding with
  | nil => rfl
  | floating body_eq _typecode_eq _tail ih => simp [body_eq, ih]
  | essential body_eq _typecode_eq _tail ih => simp [body_eq, ih]

@[simp] theorem rawFormulaPattern_formulaBodyPattern
    (formula : ConstantHeadedFormula) :
    rawFormulaPattern formula.typecode (formulaBodyPattern formula) =
      encodeFormula formula := by
  rfl

/-- A canonical body plus the authored typecode reconstructs the complete
canonical formula encoding. -/
theorem rawFormulaPattern_eq_encodeFormula_of_body_typecode
    {typecode : String} {body : Pattern}
    {formula : ConstantHeadedFormula}
    (hbody : body = formulaBodyPattern formula)
    (htypecode : formula.typecode = typecode) :
    rawFormulaPattern typecode body = encodeFormula formula := by
  subst body
  rw [← htypecode]
  exact rawFormulaPattern_formulaBodyPattern formula

/-! ## Leading premises and substitution -/

/-- Canonically decoded raw bodies yield exactly the canonical leading
`Proves` premise vector. -/
theorem RawHypothesisBodiesDecode.rawAssertionProvesPremises_eq
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
    rawAssertionProvesPremises hypotheses bodies =
      assertionProvesPremises actuals := by
  induction decoding with
  | nil => rfl
  | floating body_eq typecode_eq _tail ih =>
      simp [rawAssertionProvesPremises, assertionProvesPremises, body_eq,
        HypothesisView.typecode, HypothesisView.formula, ← typecode_eq, ih]
  | essential body_eq typecode_eq _tail ih =>
      simp [rawAssertionProvesPremises, assertionProvesPremises, body_eq,
        HypothesisView.typecode, HypothesisView.formula, ← typecode_eq, ih]

/-- The raw binding vector is exactly the canonical encoding of the indexed
finite substitution. -/
theorem RawHypothesisBodiesDecode.rawAssertionBindings_eq
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
    rawAssertionBindings hypotheses bodies =
      substitution.map encodeBinding := by
  induction decoding with
  | nil => rfl
  | floating body_eq typecode_eq _tail ih =>
      simp [rawAssertionBindings, encodeBinding, body_eq,
        ← typecode_eq, ih]
  | essential _body_eq _typecode_eq _tail ih =>
      simpa [rawAssertionBindings] using ih

private theorem encodeListWith_id_map
    {α : Type} (encode : α → Pattern) (values : List α) :
    encodeListWith id (values.map encode) = encodeListWith encode values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [encodeListWith, ih]

/-- The raw substitution syntax is the canonical encoding of the exact
ordered finite substitution indexed by the decoder. -/
theorem RawHypothesisBodiesDecode.rawAssertionSubstitution_eq
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
    rawAssertionSubstitution hypotheses bodies =
      encodeSubstitution substitution := by
  simp [rawAssertionSubstitution, encodeSubstitution,
    decoding.rawAssertionBindings_eq, encodeListWith_id_map]

/-! ## Essential and full premise canonicalization -/

/-- Body decoding canonicalizes essential checks for any common substitution.
The substitution is deliberately an explicit parameter because all essential
hypotheses are checked against the completed floating-hypothesis substitution,
not a tail-local prefix. -/
theorem RawHypothesisBodiesDecode.rawAssertionEssentialPremises_eq_with
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {decodedSubstitution : FiniteSubstitution}
    (decoding : RawHypothesisBodiesDecode hypotheses bodies actuals
      decodedSubstitution)
    (substitution : FiniteSubstitution) :
    rawAssertionEssentialPremises (encodeSubstitution substitution)
        hypotheses bodies =
      assertionEssentialPremises substitution hypotheses actuals := by
  induction decoding with
  | nil => rfl
  | floating _body_eq _typecode_eq _tail ih =>
      simpa [rawAssertionEssentialPremises,
        assertionEssentialPremises] using ih
  | essential body_eq typecode_eq _tail ih =>
      simp [rawAssertionEssentialPremises, assertionEssentialPremises,
        body_eq, ← typecode_eq, ih]

/-- Using the substitution decoded from floating hypotheses gives the exact
canonical essential-premise vector. -/
theorem RawHypothesisBodiesDecode.rawAssertionEssentialPremises_eq
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution) :
    rawAssertionEssentialPremises
        (rawAssertionSubstitution hypotheses bodies) hypotheses bodies =
      assertionEssentialPremises substitution hypotheses actuals := by
  rw [decoding.rawAssertionSubstitution_eq]
  exact decoding.rawAssertionEssentialPremises_eq_with substitution

/-- Adding a canonically encoded result body canonicalizes the complete raw
side-premise vector. -/
theorem RawHypothesisBodiesDecode.rawAssertionSidePremises_eq
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {bodies : List Pattern} {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution} {resultBody : Pattern}
    {result : ConstantHeadedFormula}
    (decoding : RawHypothesisBodiesDecode assertion.hypotheses bodies actuals
      substitution)
    (hresultBody : resultBody = formulaBodyPattern result)
    (hresultTypecode : result.typecode = assertion.formula.typecode) :
    rawAssertionSidePremises callerFrame assertion bodies resultBody =
      assertionSidePremises substitution callerFrame assertion actuals
        result := by
  have hresultFormula :
      rawFormulaPattern assertion.formula.typecode resultBody =
        encodeFormula result :=
    rawFormulaPattern_eq_encodeFormula_of_body_typecode
      hresultBody hresultTypecode
  simp only [rawAssertionSidePremises, assertionSidePremises]
  rw [decoding.rawAssertionSubstitution_eq]
  rw [decoding.rawAssertionEssentialPremises_eq_with substitution]
  rw [hresultFormula]

/-- Under the same result decoding, the entire raw assertion premise vector
is the existing canonical vector. -/
theorem RawHypothesisBodiesDecode.rawAssertionPremises_eq
    {callerFrame : RuntimeFrame} {assertion : AssertionView}
    {bodies : List Pattern} {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution} {resultBody : Pattern}
    {result : ConstantHeadedFormula}
    (decoding : RawHypothesisBodiesDecode assertion.hypotheses bodies actuals
      substitution)
    (hresultBody : resultBody = formulaBodyPattern result)
    (hresultTypecode : result.typecode = assertion.formula.typecode) :
    rawAssertionPremises callerFrame assertion bodies resultBody =
      assertionPremises substitution callerFrame assertion actuals result := by
  rw [rawAssertionPremises, assertionPremises,
    decoding.rawAssertionProvesPremises_eq,
    decoding.rawAssertionSidePremises_eq hresultBody hresultTypecode]

/-- The raw argument vector, including its final result-body slot, is exactly
the canonical generated assertion argument vector. -/
theorem RawHypothesisBodiesDecode.rawArguments_eq
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution} {resultBody : Pattern}
    {result : ConstantHeadedFormula}
    (decoding :
      RawHypothesisBodiesDecode hypotheses bodies actuals substitution)
    (hresultBody : resultBody = formulaBodyPattern result) :
    bodies ++ [resultBody] = assertionRuleArguments actuals result := by
  rw [decoding.bodies_eq_map_formulaBodyPattern, hresultBody]
  rfl

/-- A canonically encoded result body of the authored result typecode makes
the raw root conclusion exactly the canonical encoded `Proves` conclusion. -/
theorem rawAssertionConclusion_eq
    {assertion : AssertionView} {resultBody : Pattern}
    {result : ConstantHeadedFormula}
    (hresultBody : resultBody = formulaBodyPattern result)
    (hresultTypecode : result.typecode = assertion.formula.typecode) :
    rawAssertionConclusion assertion resultBody =
      proves (encodeFormula result) := by
  exact congrArg proves
    (rawFormulaPattern_eq_encodeFormula_of_body_typecode
      hresultBody hresultTypecode)

/-! ## Concrete boundaries -/

private def boundaryFloatingActual : ConstantHeadedFormula :=
  ⟨"wff", [.var "ph"]⟩

private def boundaryEssentialFormula : ConstantHeadedFormula :=
  ⟨"|-", [.var "ph"]⟩

private def boundaryEssentialActual : ConstantHeadedFormula :=
  ⟨"|-", [.const "T"]⟩

private def boundaryHypotheses : List HypothesisView :=
  [ .floating "wph" "wff" "ph"
  , .essential "eph" boundaryEssentialFormula ]

/-- Positive: one floating and one essential body decode in authored order,
while only the floating hypothesis contributes a binding. -/
example : RawHypothesisBodiesDecode boundaryHypotheses
    [ formulaBodyPattern boundaryFloatingActual
    , formulaBodyPattern boundaryEssentialActual ]
    [boundaryFloatingActual, boundaryEssentialActual]
    [⟨"ph", boundaryFloatingActual⟩] := by
  exact .floating rfl rfl (.essential rfl rfl .nil)

/-- Negative: a noncanonical raw body cannot decode as the chosen actual. -/
example : ¬ RawHypothesisBodiesDecode
    [.floating "wph" "wff" "ph"] [.fvar "not-a-formula-body"]
    [boundaryFloatingActual] [⟨"ph", boundaryFloatingActual⟩] := by
  intro decoding
  cases decoding with
  | floating body_eq _typecode_eq _tail =>
      simp [boundaryFloatingActual, formulaBodyPattern, encodeListWith,
        Builder.nil, Builder.cons] at body_eq

private def boundaryWrongTypecodeActual : ConstantHeadedFormula :=
  ⟨"|-", [.var "ph"]⟩

/-- Negative: even a canonical body fails when its actual has the wrong
authored typecode. -/
example : ¬ RawHypothesisBodiesDecode
    [.floating "wph" "wff" "ph"]
    [formulaBodyPattern boundaryWrongTypecodeActual]
    [boundaryWrongTypecodeActual]
    [⟨"ph", boundaryWrongTypecodeActual⟩] := by
  intro decoding
  cases decoding with
  | floating _body_eq typecode_eq _tail =>
      simp [boundaryWrongTypecodeActual] at typecode_eq

end Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
