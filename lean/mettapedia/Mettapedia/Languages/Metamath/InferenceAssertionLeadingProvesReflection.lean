import Mettapedia.Languages.Metamath.InferenceAssertionRawCanonicalization
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesTree

/-!
# Reflected leading premises of projected assertions

An arbitrary projected assertion root exposes raw bodies, while recursive
reflection of each leading `Proves` child exposes a concrete Metamath formula
and a source-pinned generated tree.  This module records the exact bridge
between those two views.

The bridge deliberately retains three distinct pieces of evidence for every
child: equality of the raw and canonical formula indices, the reflected tree,
and equality of the original and reflected raw proof artifacts.  Raw proof
erasure alone cannot recover a child's conclusion index, so none of these
fields may be inferred from erasure.

This is a static proof-relevant carrier for a later recursive reflection
theorem.  It does not claim that every generic derivation list has such a
reflection.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution

/-! ## Inverting a raw formula index -/

/-- A raw formula pattern is a canonical formula encoding exactly when its
body and authored typecode are the corresponding canonical components. -/
theorem rawFormulaPattern_eq_encodeFormula_iff
    (typecode : String) (body : Pattern)
    (actual : ConstantHeadedFormula) :
    rawFormulaPattern typecode body = encodeFormula actual ↔
      body = formulaBodyPattern actual ∧ actual.typecode = typecode := by
  constructor
  · intro heq
    have harguments :
        [encodeString typecode, body] =
          [encodeString actual.typecode, formulaBodyPattern actual] := by
      exact (Pattern.apply.inj heq).2
    have htypecodeEncoded :
        encodeString typecode = encodeString actual.typecode :=
      (List.cons.inj harguments).1
    have hbody : body = formulaBodyPattern actual :=
      (List.cons.inj (List.cons.inj harguments).2).1
    exact ⟨hbody, (encodeString_injective htypecodeEncoded).symm⟩
  · rintro ⟨hbody, htypecode⟩
    exact rawFormulaPattern_eq_encodeFormula_of_body_typecode
      hbody htypecode

/-! ## Exact reflected child vector -/

/-- Recursive reflection evidence for the leading `Proves` children of one
raw assertion application.

The indices enforce authored hypothesis order, the exact raw body vector,
the concrete actual formulas and floating-hypothesis substitution, and the
original dependent derivation list.  Each constructor stores the formula
index equality supplied by recursive reflection and preserves the exact raw
proof artifact of that child. -/
inductive ReflectedLeadingProvesChildren
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (hprojection : presentationOfProjection? projection = some target.1) :
    (hypotheses : List HypothesisView) →
      (bodies : List Pattern) →
      (actuals : List ConstantHeadedFormula) →
      (substitution : FiniteSubstitution) →
      DerivationList target
        (rawAssertionProvesPremises hypotheses bodies) → Type where
  | nil : ReflectedLeadingProvesChildren projection target hprojection
      [] [] [] [] .nil
  | floating {label typecode variableName : String} {body : Pattern}
      {actual : ConstantHeadedFormula} {hypotheses : List HypothesisView}
      {bodies : List Pattern} {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      {head : Derivation target
        (proves (rawFormulaPattern typecode body))}
      {tail : DerivationList target
        (rawAssertionProvesPremises hypotheses bodies)}
      (formula_eq :
        rawFormulaPattern typecode body = encodeFormula actual)
      (tree : GeneratedProvesTree projection target actual)
      (erase_eq :
        head.erase = (tree.toDerivation hprojection).erase)
      (tailReflection : ReflectedLeadingProvesChildren projection target
        hprojection hypotheses bodies actuals substitution tail) :
      ReflectedLeadingProvesChildren projection target hprojection
        (.floating label typecode variableName :: hypotheses)
        (body :: bodies) (actual :: actuals)
        (⟨variableName, actual⟩ :: substitution) (.cons head tail)
  | essential {label : String} {formula actual : ConstantHeadedFormula}
      {body : Pattern} {hypotheses : List HypothesisView}
      {bodies : List Pattern} {actuals : List ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      {head : Derivation target
        (proves (rawFormulaPattern formula.typecode body))}
      {tail : DerivationList target
        (rawAssertionProvesPremises hypotheses bodies)}
      (formula_eq :
        rawFormulaPattern formula.typecode body = encodeFormula actual)
      (tree : GeneratedProvesTree projection target actual)
      (erase_eq :
        head.erase = (tree.toDerivation hprojection).erase)
      (tailReflection : ReflectedLeadingProvesChildren projection target
        hprojection hypotheses bodies actuals substitution tail) :
      ReflectedLeadingProvesChildren projection target hprojection
        (.essential label formula :: hypotheses)
        (body :: bodies) (actual :: actuals) substitution (.cons head tail)

/-! ## Forgetful maps and exact preservation -/

/-- The reflected child vector supplies precisely the raw-body decoder needed
by assertion canonicalization. -/
theorem ReflectedLeadingProvesChildren.toRawHypothesisBodiesDecode
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {hprojection : presentationOfProjection? projection = some target.1}
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies)}
    (reflection : ReflectedLeadingProvesChildren projection target
      hprojection hypotheses bodies actuals substitution children) :
    RawHypothesisBodiesDecode hypotheses bodies actuals substitution := by
  induction reflection with
  | nil => exact .nil
  | floating formula_eq _tree _erase_eq _tailReflection ih =>
      rcases (rawFormulaPattern_eq_encodeFormula_iff _ _ _).mp formula_eq with
        ⟨hbody, htypecode⟩
      exact .floating hbody htypecode ih
  | essential formula_eq _tree _erase_eq _tailReflection ih =>
      rcases (rawFormulaPattern_eq_encodeFormula_iff _ _ _).mp formula_eq with
        ⟨hbody, htypecode⟩
      exact .essential hbody htypecode ih

/-- Forgetting the original derivations yields the exact ordered forest of
recursively reflected generated trees. -/
def ReflectedLeadingProvesChildren.toForest
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {hprojection : presentationOfProjection? projection = some target.1}
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies)}
    (reflection : ReflectedLeadingProvesChildren projection target
      hprojection hypotheses bodies actuals substitution children) :
    GeneratedProvesForest projection target actuals :=
  match reflection with
  | .nil => .nil
  | .floating _ tree _ tailReflection =>
      .cons tree tailReflection.toForest
  | .essential _ tree _ tailReflection =>
      .cons tree tailReflection.toForest

/-- The original leading child vector and the reflected forest assemble to
exactly the same ordered raw proof list. -/
theorem ReflectedLeadingProvesChildren.erase_eq_toForest
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {hprojection : presentationOfProjection? projection = some target.1}
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies)}
    (reflection : ReflectedLeadingProvesChildren projection target
      hprojection hypotheses bodies actuals substitution children) :
    children.erase =
      (reflection.toForest.toDerivationList hprojection).erase := by
  induction reflection with
  | nil => rfl
  | floating _formula_eq _tree erase_eq _tailReflection ih =>
      change _ :: _ = _ :: _
      exact congrArg₂ List.cons erase_eq ih
  | essential _formula_eq _tree erase_eq _tailReflection ih =>
      change _ :: _ = _ :: _
      exact congrArg₂ List.cons erase_eq ih

/-- The reflected vector therefore canonicalizes its complete leading premise
index, not merely the erased proof list. -/
theorem ReflectedLeadingProvesChildren.rawPremises_eq
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {hprojection : presentationOfProjection? projection = some target.1}
    {hypotheses : List HypothesisView} {bodies : List Pattern}
    {actuals : List ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    {children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies)}
    (reflection : ReflectedLeadingProvesChildren projection target
      hprojection hypotheses bodies actuals substitution children) :
    rawAssertionProvesPremises hypotheses bodies =
      assertionProvesPremises actuals :=
  reflection.toRawHypothesisBodiesDecode.rawAssertionProvesPremises_eq

/-! ## Constructive boundaries -/

private def boundaryFloating : HypothesisView :=
  .floating "wph" "wff" "ph"

/-- Positive: a genuine reflected active leaf inhabits the one-child bridge,
with its exact original raw proof artifact retained. -/
example {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    (hmember : boundaryFloating ∈ projection.activeHypotheses) :
    let actual := boundaryFloating.formula
    let tree : GeneratedProvesTree projection target actual :=
      .active boundaryFloating hmember
    ReflectedLeadingProvesChildren projection target hprojection
      [boundaryFloating] [formulaBodyPattern actual] [actual]
      [⟨"ph", actual⟩]
      (.cons (tree.toDerivation hprojection) .nil) := by
  exact .floating rfl _ rfl .nil

private def boundaryActual : ConstantHeadedFormula :=
  ⟨"wff", [.var "ph"]⟩

/-- Negative: no derivation artifact can make a noncanonical raw body into a
reflection of the fixed actual formula. -/
example {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    (head : Derivation target
      (proves (rawFormulaPattern "wff" (.fvar "not-a-body")))) :
    ¬ Nonempty (ReflectedLeadingProvesChildren projection target hprojection
      [.floating "wph" "wff" "ph"] [.fvar "not-a-body"] [boundaryActual]
      [⟨"ph", boundaryActual⟩] (.cons head .nil)) := by
  rintro ⟨reflection⟩
  have decoding := reflection.toRawHypothesisBodiesDecode
  cases decoding with
  | floating hbody _htypecode _tail =>
      simp [boundaryActual, formulaBodyPattern, encodeListWith,
        Builder.nil, Builder.cons] at hbody

end Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
