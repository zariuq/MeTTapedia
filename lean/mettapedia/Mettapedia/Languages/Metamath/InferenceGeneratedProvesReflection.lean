import Mettapedia.Languages.Metamath.InferenceActiveHypothesisReflection
import Mettapedia.Languages.Metamath.InferenceAssertionRootReflection

/-!
# Reflection of arbitrary projected `Proves` derivations

Every generic derivation of a projected `Proves` judgment is rooted in either
an active-hypothesis schema or an assertion schema.  This module follows that
classification recursively through the original leading assertion children.
It decodes the conclusion as a Metamath formula, constructs a source-pinned
`GeneratedProvesTree`, and preserves the complete raw proof erasure exactly.

The assertion-prefix helper walks the supplied dependent `DerivationList`
itself.  Its suffix is returned unchanged; no split proof list is recursively
rechecked or regenerated.  Assertion side evidence is reflected by the
standalone side-calculus bridge after all leading `Proves` children have been
consumed.

This is a static theorem about a successfully projected presentation.  It
does not import runtime execution or claim whole-source completeness.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceHypothesisStepAgreement
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication

private theorem sizeOf_children_lt_byRule
    {target : ValidatedPresentation} {premises : List Pattern}
    {conclusion : Pattern} (ruleInstance : RuleInstance)
    (application : RuleApplication target ruleInstance premises conclusion)
    (children : DerivationList target premises) :
    sizeOf children <
      sizeOf (Derivation.byRule ruleInstance application children) := by
  change sizeOf children <
    1 + sizeOf ruleInstance + sizeOf premises + sizeOf conclusion +
      sizeOf application + sizeOf children
  omega

private theorem sizeOf_head_lt_cons
    {target : ValidatedPresentation} {premise : Pattern}
    {premises : List Pattern} (head : Derivation target premise)
    (tail : DerivationList target premises) :
    sizeOf head < sizeOf (DerivationList.cons head tail) := by
  change sizeOf head <
    1 + sizeOf premise + sizeOf premises + sizeOf head + sizeOf tail
  omega

private theorem sizeOf_tail_lt_cons
    {target : ValidatedPresentation} {premise : Pattern}
    {premises : List Pattern} (head : Derivation target premise)
    (tail : DerivationList target premises) :
    sizeOf tail < sizeOf (DerivationList.cons head tail) := by
  change sizeOf tail <
    1 + sizeOf premise + sizeOf premises + sizeOf head + sizeOf tail
  omega

/-! ## Mutual reflection through original derivation artifacts -/

mutual

/-- Every generic derivation of a projected `Proves` judgment reflects to a
decoded Metamath formula and a source-pinned generated tree with exactly the
same raw proof erasure. -/
theorem provesDerivation_reflectsGeneratedTree
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulaPattern : Pattern}
    (derivation : Derivation target (proves formulaPattern)) :
    ∃ formula : ConstantHeadedFormula,
      formulaPattern = encodeFormula formula ∧
      ∃ tree : GeneratedProvesTree projection target formula,
        derivation.erase = (tree.toDerivation hprojection).erase := by
  cases hderivation : derivation with
  | byRule ruleInstance application children =>
      have hchildrenSize : sizeOf children < sizeOf derivation := by
        rw [hderivation]
        exact sizeOf_children_lt_byRule ruleInstance application children
      rcases ruleApplication_proves_cases projection target hprojection
          application with activeView | assertionView
      · let rootView : ActiveHypothesisDerivationRootView projection target
            (Derivation.byRule ruleInstance application children) :=
          .intro application children activeView
        rcases rootView.reflect hprojection
            (Derivation.byRule ruleInstance application children) with
          ⟨hypothesis, _hmember, hformula, tree, _htree, herase⟩
        exact ⟨hypothesis.formula, hformula, tree, herase⟩
      · have rawShape :=
          (assertionApplicationView_iff_rawShape projection target).mp
            assertionView
        rcases rawShape with
          ⟨assertion, bodies, resultBody, hassertion, _hlookup,
            _hargumentsValid, _hpremisesInstantiate,
            _hconclusionInstantiate, hruleId, harguments, hbodiesLength,
            hpremises, hformula⟩
        cases hpremises
        change DerivationList target
          (rawAssertionProvesPremises assertion.hypotheses bodies ++
            rawAssertionSidePremises projection.callerFrame assertion bodies
              resultBody) at children
        rcases rawAssertionProvesPrefix_reflectsGeneratedTrees hprojection
            assertion.hypotheses bodies hbodiesLength
            (rawAssertionSidePremises projection.callerFrame assertion bodies
              resultBody) children with
          ⟨actuals, substitution, leadingChildren, sideChildren,
            leadingReflection, hchildrenErase⟩
        rcases assertionRawShapeFields_reflect hprojection application children
            hassertion hruleId harguments rfl hformula leadingChildren
            sideChildren hchildrenErase leadingReflection with
          ⟨result, hresultFormula, _hresultBody, _hresultTypecode,
            _hsemantics, _hruleInstance, _node, tree, _htree, herase⟩
        exact ⟨result, hresultFormula, tree, herase⟩
termination_by sizeOf derivation
decreasing_by exact hchildrenSize

/-- Consume exactly the raw leading `Proves` prefix of an assertion's
original child vector.  The returned leading vector consists of those same
derivation objects, while the returned suffix is the untouched remainder of
the original vector. -/
theorem rawAssertionProvesPrefix_reflectsGeneratedTrees
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1) :
    (hypotheses : List HypothesisView) →
    (bodies : List Pattern) →
    bodies.length = hypotheses.length →
    (suffix : List Pattern) →
    (children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies ++ suffix)) →
      ∃ actuals : List ConstantHeadedFormula,
        ∃ substitution : FiniteSubstitution,
          ∃ leadingChildren : DerivationList target
              (rawAssertionProvesPremises hypotheses bodies),
            ∃ suffixChildren : DerivationList target suffix,
              ∃ _reflection : ReflectedLeadingProvesChildren projection target
                  hprojection hypotheses bodies actuals substitution
                  leadingChildren,
                children.erase =
                  leadingChildren.erase ++ suffixChildren.erase
  | [], [], _hlength, _suffix, children =>
      ⟨[], [], .nil, children, .nil, rfl⟩
  | [], _body :: _bodies, hlength, _suffix, _children => by
      simp at hlength
  | _hypothesis :: _hypotheses, [], hlength, _suffix, _children => by
      simp at hlength
  | hypothesis :: hypotheses, body :: bodies, hlength, suffix,
      .cons head tail => by
      have htailLength : bodies.length = hypotheses.length := by
        simp at hlength
        exact hlength
      rcases provesDerivation_reflectsGeneratedTree hprojection head with
        ⟨actual, hformula, tree, herase⟩
      rcases rawAssertionProvesPrefix_reflectsGeneratedTrees hprojection
          hypotheses bodies htailLength suffix tail with
        ⟨actuals, substitution, leadingChildren, suffixChildren,
          tailReflection, htailErase⟩
      cases hypothesis with
      | floating label typecode variableName =>
          let reflection : ReflectedLeadingProvesChildren projection target
              hprojection (.floating label typecode variableName :: hypotheses)
              (body :: bodies) (actual :: actuals)
              (⟨variableName, actual⟩ :: substitution)
              (.cons head leadingChildren) :=
            .floating hformula tree herase tailReflection
          refine ⟨actual :: actuals, ⟨variableName, actual⟩ :: substitution,
            .cons head leadingChildren, suffixChildren, reflection, ?_⟩
          simp [DerivationList.erase, htailErase]
      | essential label formula =>
          let reflection : ReflectedLeadingProvesChildren projection target
              hprojection (.essential label formula :: hypotheses)
              (body :: bodies) (actual :: actuals) substitution
              (.cons head leadingChildren) :=
            .essential hformula tree herase tailReflection
          refine ⟨actual :: actuals, substitution, .cons head leadingChildren,
            suffixChildren, reflection, ?_⟩
          simp [DerivationList.erase, htailErase]
termination_by hypotheses bodies _hlength suffix children => sizeOf children
decreasing_by
  all_goals
    first
    | exact sizeOf_head_lt_cons head tail
    | exact sizeOf_tail_lt_cons head tail

end

/-! ## Direct consequences -/

/-- The preserved erasure is the independently defined canonical raw proof
represented by the reflected generated tree. -/
theorem provesDerivation_reflectsCanonicalRawProof
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulaPattern : Pattern}
    (derivation : Derivation target (proves formulaPattern)) :
    ∃ formula : ConstantHeadedFormula,
      formulaPattern = encodeFormula formula ∧
      ∃ tree : GeneratedProvesTree projection target formula,
        derivation.erase = tree.canonicalRawProof := by
  rcases provesDerivation_reflectsGeneratedTree hprojection derivation with
    ⟨formula, hformula, tree, herase⟩
  exact ⟨formula, hformula, tree,
    herase.trans (tree.erase_toDerivation hprojection)⟩

/-- In particular, inhabitation of a projected generic `Proves` derivation
forces its apparent formula argument to decode as a canonical Metamath
formula encoding. -/
theorem provesDerivation_decodesFormula
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {formulaPattern : Pattern}
    (derivation : Derivation target (proves formulaPattern)) :
    ∃ formula : ConstantHeadedFormula,
      formulaPattern = encodeFormula formula := by
  rcases provesDerivation_reflectsGeneratedTree hprojection derivation with
    ⟨formula, hformula, _tree, _herase⟩
  exact ⟨formula, hformula⟩

/-! ## Constructive boundaries -/

/-- Positive boundary: an actual generated active-hypothesis leaf is covered
by the global reflection theorem and retains its raw artifact. -/
example {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1)
    {hypothesis : HypothesisView}
    (hmember : hypothesis ∈ projection.activeHypotheses) :
    ∃ formula : ConstantHeadedFormula,
      encodeFormula hypothesis.formula = encodeFormula formula ∧
      ∃ tree : GeneratedProvesTree projection target formula,
        (activeHypothesisDerivation projection target hprojection hmember).erase =
          (tree.toDerivation hprojection).erase :=
  provesDerivation_reflectsGeneratedTree hprojection
    (activeHypothesisDerivation projection target hprojection hmember)

private def malformedFormulaPattern : Pattern :=
  .apply "$mm.not-a-formula" []

/-- Negative boundary: a syntactically malformed formula payload cannot have
any projected generic `Proves` derivation. -/
theorem not_nonempty_provesDerivation_malformedFormula
    {projection : PrefixProjection} {target : ValidatedPresentation}
    (hprojection : presentationOfProjection? projection = some target.1) :
    ¬ Nonempty (Derivation target (proves malformedFormulaPattern)) := by
  rintro ⟨derivation⟩
  rcases provesDerivation_decodesFormula hprojection derivation with
    ⟨formula, hformula⟩
  simp [malformedFormulaPattern, encodeFormula, Builder.formula] at hformula

end Mettapedia.Languages.Metamath.InferenceProjection
