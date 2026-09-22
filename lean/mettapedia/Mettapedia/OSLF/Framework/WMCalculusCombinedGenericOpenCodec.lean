import Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification

/-!
# Comparing generic open erasure with supported WM terms

The declaration-derived open codec renders the existing intrinsically sorted
combined-WM first-order fragment in the same way as the WM-specific named
erasure. This is a compatibility theorem between two independently defined
presentations, not a second constructor declaration list.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedGenericOpenCodec

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder
open Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

set_option autoImplicit false

private abbrev CombinedLang : LanguageDef :=
  wmExtVertexLanguageDefGuarded combinedVertex

/-- The semantic-support data for an ordinary authored argument row. It is
derived below from the generic syntactic certificate, not from raw matching. -/
inductive CombinedFirstOrderArguments :
    {Γ : Ctx CombinedSignature} →
    {parameters : List TermParam} →
    {arity : List (List TypeExpr × TypeExpr)} →
    ParameterScopes parameters arity → Args CombinedSignature arity Γ → Type where
  | nil {Γ : Ctx CombinedSignature} :
      CombinedFirstOrderArguments (Γ := Γ) .nil (Args.nil (Γ := Γ))
  | cons {Γ : Ctx CombinedSignature}
      (parameterName : String) (sort : TypeExpr)
      {parameters : List TermParam}
      {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (head : Term CombinedSignature Γ sort)
      (tail : Args CombinedSignature arity Γ)
      (headSupported : FirstOrder head)
      (tailSupported : CombinedFirstOrderArguments scopes tail) :
      CombinedFirstOrderArguments
        (.cons (.simple parameterName sort) scopes) (.cons head tail)

mutual
  /-- The declaration-derived nonbinding fragment specializes to the
  existing semantic first-order fragment of the combined WM signature. -/
  def firstOrder_of_openFirstOrder
      {Γ : Ctx CombinedSignature} {sort : TypeExpr}
      {term : Term CombinedSignature Γ sort}
      (supported : OpenFirstOrder CombinedLang term) : FirstOrder term := by
    cases supported with
    | «variable» position => exact .variable position
    | constructor rule member ordinary scopes arguments argsSupported =>
        have rowSupported :=
          firstOrderArguments_of_openFirstOrderArguments argsSupported
        by_cases revised : rule = reviseDecl
        · subst rule
          cases rowSupported with
          | cons firstName firstSort restScopes first rest firstSupported restSupported =>
              cases restSupported with
              | cons secondName secondSort finalScopes second final
                  secondSupported finalSupported =>
                  cases finalSupported
                  change FirstOrder (revise first second)
                  exact .revise firstSupported secondSupported
        · by_cases extracted : rule = extractDecl
          · subst rule
            cases rowSupported with
            | cons worldName worldSort restScopes world rest worldSupported restSupported =>
                cases restSupported with
                | cons queryName querySort finalScopes query final
                    querySupported finalSupported =>
                    cases finalSupported
                    change FirstOrder (extract world query)
                    exact .extract worldSupported querySupported
          · by_cases combined : rule = combineDecl
            · subst rule
              cases rowSupported with
              | cons firstName firstSort restScopes first rest firstSupported restSupported =>
                  cases restSupported with
                  | cons secondName secondSort finalScopes second final
                      secondSupported finalSupported =>
                      cases finalSupported
                      change FirstOrder (combine first second)
                      exact .combine firstSupported secondSupported
            · by_cases zeroed : rule = evidenceZeroDecl
              · subst rule
                cases rowSupported
                change FirstOrder zero
                exact .zero
              · by_cases merged : rule = overlapMergeDecl
                · subst rule
                  cases rowSupported with
                  | cons firstName firstSort restScopes first rest firstSupported restSupported =>
                      cases restSupported with
                      | cons secondName secondSort finalScopes second final
                          secondSupported finalSupported =>
                          cases finalSupported
                          change FirstOrder (overlapMerge first second)
                          exact .overlapMerge firstSupported secondSupported
                · by_cases factored : rule = overlapFactorDecl
                  · subst rule
                    cases rowSupported with
                    | cons firstName firstSort restScopes first rest firstSupported restSupported =>
                        cases restSupported with
                        | cons secondName secondSort restScopes' second rest'
                            secondSupported restSupported' =>
                            cases restSupported' with
                            | cons queryName querySort finalScopes query final
                                querySupported finalSupported =>
                                cases finalSupported
                                change FirstOrder (overlapFactor first second query)
                                exact .overlapFactor firstSupported secondSupported
                                  querySupported
                  · by_cases corrected : rule = overlapCorrectDecl
                    · subst rule
                      cases rowSupported with
                      | cons firstName firstSort restScopes first rest firstSupported restSupported =>
                          cases restSupported with
                          | cons secondName secondSort restScopes' second rest'
                              secondSupported restSupported' =>
                              cases restSupported' with
                              | cons factorName factorSort finalScopes factor final
                                  factorSupported finalSupported =>
                                  cases finalSupported
                                  change FirstOrder (overlapCorrect first second factor)
                                  exact .overlapCorrect firstSupported secondSupported
                                    factorSupported
                    · by_cases forgotten : rule = forgetDecl
                      · subst rule
                        cases rowSupported with
                        | cons scopeName scopeSort restScopes scope rest scopeSupported restSupported =>
                            cases restSupported with
                            | cons worldName worldSort finalScopes world final
                                worldSupported finalSupported =>
                                cases finalSupported
                                change FirstOrder (forget scope world)
                                exact .forget scopeSupported worldSupported
                      · have impossible : False := by
                          rcases combined_declaration_cases member with
                            h | h | h | h | h | h | h | h
                          · exact revised h
                          · exact extracted h
                          · exact combined h
                          · exact zeroed h
                          · exact merged h
                          · exact factored h
                          · exact corrected h
                          · exact forgotten h
                        exact impossible.elim

  /-- Convert each generic ordinary-argument certificate into the exact
  WM-specific interpretation certificate for its intrinsic child term. -/
  def firstOrderArguments_of_openFirstOrderArguments
      {Γ : Ctx CombinedSignature}
      {parameters : List TermParam}
      {arity : List (List TypeExpr × TypeExpr)}
      {scopes : ParameterScopes parameters arity}
      {arguments : Args CombinedSignature arity Γ}
      (supported : OpenFirstOrderArguments CombinedLang scopes arguments) :
      CombinedFirstOrderArguments scopes arguments := by
    cases supported with
    | @nil context => exact CombinedFirstOrderArguments.nil (Γ := Γ)
    | cons parameterName sort scopes head tail headSupported tailSupported =>
        exact .cons parameterName sort scopes head tail
          (firstOrder_of_openFirstOrder headSupported)
          (firstOrderArguments_of_openFirstOrderArguments tailSupported)
end

/-- On every supported WM first-order term, the generic declaration-derived
named renderer and the existing WM renderer agree exactly. -/
theorem namedFirstOrderErase?_of_supported
    {Γ : Ctx CombinedSignature}
    (names : (sort : TypeExpr) → Var Γ sort → String)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    namedFirstOrderErase? names term = some (namedErase names fragment) := by
  induction fragment with
  | «variable» position => rfl
  | revise first second firstIH secondIH =>
      simp [namedErase, revise, combinedReviseOperator, coreReviseOperator,
        mapOperator, coreToCombined, ParameterScopes.map, ParameterScope.map,
        Mettapedia.GSLT.LanguageDef.mapGrammarRule_id,
        namedFirstOrderErase?, reviseDecl, pRevise]
      dsimp [Mettapedia.GSLT.LanguageDef.mapGrammarRule,
        Mettapedia.GSLT.LanguageDef.mapTermParam,
        Mettapedia.GSLT.LanguageDef.mapTypeExpr,
        Mettapedia.GSLT.LanguageDef.LanguageDefSymbolMap.id,
        mapArities, mapArity, List.map]
      simp [namedFirstOrderEraseArguments?, firstIH, secondIH]
  | extract world query worldIH queryIH =>
      simp [namedErase, extract, combinedExtractOperator, coreExtractOperator,
        mapOperator, coreToCombined, ParameterScopes.map, ParameterScope.map,
        Mettapedia.GSLT.LanguageDef.mapGrammarRule_id,
        namedFirstOrderErase?, extractDecl, pExtract]
      dsimp [Mettapedia.GSLT.LanguageDef.mapGrammarRule,
        Mettapedia.GSLT.LanguageDef.mapTermParam,
        Mettapedia.GSLT.LanguageDef.mapTypeExpr,
        Mettapedia.GSLT.LanguageDef.LanguageDefSymbolMap.id,
        mapArities, mapArity, List.map]
      simp [namedFirstOrderEraseArguments?, worldIH, queryIH]
  | combine first second firstIH secondIH =>
      simp [namedErase, combine, combinedCombineOperator, combineDecl, pCombine,
        namedFirstOrderErase?, namedFirstOrderEraseArguments?_simple_pair,
        firstIH, secondIH]
  | zero =>
      rfl
  | overlapMerge first second firstIH secondIH =>
      simp [namedErase, overlapMerge, overlapMergeOperator,
        namedFirstOrderErase?, namedFirstOrderEraseArguments?_simple_pair,
        overlapMergeDecl, pOverlapMerge, firstIH, secondIH]
  | overlapFactor first second query firstIH secondIH queryIH =>
      simp [namedErase, overlapFactor, overlapFactorOperator,
        namedFirstOrderErase?, namedFirstOrderEraseArguments?_simple_triple,
        overlapFactorDecl, pOverlapFactor, firstIH, secondIH, queryIH]
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simp [namedErase, overlapCorrect, overlapCorrectOperator,
        namedFirstOrderErase?, namedFirstOrderEraseArguments?_simple_triple,
        overlapCorrectDecl, pOverlapCorrect, firstIH, secondIH, factorIH]
  | forget scope world scopeIH worldIH =>
      simp [namedErase, forget, forgetOperator,
        namedFirstOrderErase?, namedFirstOrderEraseArguments?_simple_pair,
        forgetDecl, pForget, scopeIH, worldIH]

/-- Every image of a computed combined-WM constructor-tree substitution has
the existing WM-specific semantic support certificate. -/
def reifyOpenImages?_supported_WM
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings)
    (sourceEntries : List (String × TypeExpr))
    {sigma : Sub CombinedSignature (contextSorts sourceEntries)
      (contextSorts targetEntries)}
    (accepted : reifyOpenImages? CombinedLang targetEntries bindings
      sourceEntries = some sigma) :
    ∀ sort (position : Var (contextSorts sourceEntries) sort),
      FirstOrder (sigma sort position) := by
  intro sort position
  exact firstOrder_of_openFirstOrder
    (reifyOpenImages?_supported CombinedLang targetEntries bindings
      sourceEntries accepted sort position)

/-- A checked source is not only intrinsically constructed: its computed term
belongs to the pre-existing combined-WM semantic fragment and keeps the exact
authored pattern. -/
theorem checkedOpenAnswers_source_supported_computes
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let entries := fromUsed sourceFree pattern.freeFvarNames
    ∃ term : Term CombinedSignature (contextSorts entries) sort,
      reifyOpen? CombinedLang entries pattern sort = some term ∧
      ∃ fragment : FirstOrder term,
        namedErase (names entries) fragment = pattern := by
  let entries := fromUsed sourceFree pattern.freeFvarNames
  obtain ⟨term, computed, named⟩ :=
    checkedOpenAnswers_source_computes sourceFree targetFree pattern sort
      concrete bindings returned
  let fragment : FirstOrder term :=
    firstOrder_of_openFirstOrder (reifyOpen?_supported computed)
  have compatible := namedFirstOrderErase?_of_supported
    (names entries) fragment
  rw [compatible] at named
  exact ⟨term, computed, fragment, Option.some.inj named⟩

/-- The checked answer's *computed* constructor-tree substitution, rather
than an existentially selected substitute, now has semantic support and exact
WM named erasure for every captured source handle. -/
theorem checkedOpenAnswers_all_images_supported_receipt
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ sigma : Sub CombinedSignature
        (contextSorts sourceEntries) (contextSorts targetEntries),
      reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
        some sigma ∧
      ∃ supported : ∀ imageSort
          (position : Var (contextSorts sourceEntries) imageSort),
          FirstOrder (sigma imageSort position),
        ∀ imageSort
          (position : Var (contextSorts sourceEntries) imageSort),
          applyBindings bindings
            (.fvar (names sourceEntries imageSort position)) =
            namedErase (names targetEntries)
              (supported imageSort position) := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  obtain ⟨sigma, computed, named⟩ :=
    checkedOpenAnswers_all_images_receipt sourceFree targetFree pattern sort
      concrete bindings returned
  let supported : ∀ imageSort
      (position : Var (contextSorts sourceEntries) imageSort),
      FirstOrder (sigma imageSort position) :=
    reifyOpenImages?_supported_WM targetEntries bindings sourceEntries
      computed
  refine ⟨sigma, computed, supported, ?_⟩
  intro imageSort position
  have compatible := namedFirstOrderErase?_of_supported
    (names targetEntries) (supported imageSort position)
  have namedHere := named imageSort position
  rw [compatible] at namedHere
  exact (Option.some.inj namedHere).symm

/-- The checked executor's intrinsic source and substitution are certified
before choosing a reading or inhabiting any model environment. The target
certificate is the actual substitution of the source certificate. -/
theorem checkedOpenAnswers_computed_substitution
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (bindings : Bindings) (concrete : Pattern)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ sigma : Sub CombinedSignature
        (contextSorts sourceEntries) (contextSorts targetEntries),
      reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
        some sigma ∧
      ∃ term : Term CombinedSignature (contextSorts sourceEntries) sort,
        reifyOpen? CombinedLang sourceEntries pattern sort = some term ∧
        ∃ fragment : FirstOrder term,
          namedErase (names sourceEntries) fragment = pattern ∧
          ∃ supported : ∀ imageSort
              (position : Var (contextSorts sourceEntries) imageSort),
              FirstOrder (sigma imageSort position),
            namedErase (names targetEntries)
              (FirstOrder.substitute sigma supported fragment) = concrete := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  obtain ⟨term, termComputed, fragment, sourceNamed⟩ :=
    checkedOpenAnswers_source_supported_computes sourceFree targetFree pattern
      sort concrete bindings returned
  obtain ⟨sigma, sigmaComputed, supported, variableReceipt⟩ :=
    checkedOpenAnswers_all_images_supported_receipt sourceFree targetFree
      pattern sort concrete bindings returned
  obtain ⟨plan, _, _, compiled, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff sourceFree targetFree pattern sort concrete
      bindings).mp returned
  obtain ⟨ran, _⟩ :=
    (checkedPlanAnswersFromPattern_mem_iff sourceFree targetFree pattern plan
      concrete bindings).mp planReturned
  have matched : bindings ∈ matchPattern pattern concrete := by
    rw [← run_compilePattern? pattern concrete plan compiled]
    exact ran
  have matchedNamed : bindings ∈
      matchPattern (namedErase (names sourceEntries) fragment) concrete := by
    rw [sourceNamed]
    exact matched
  refine ⟨sigma, sigmaComputed, term, termComputed, fragment, sourceNamed,
    supported, ?_⟩
  rw [← matchPattern_namedErase_correct (names sourceEntries) fragment
    concrete bindings matchedNamed]
  exact (applyBindings_namedErase_eq_namedErase_substitute
    (names sourceEntries) (names targetEntries) bindings sigma supported
    variableReceipt fragment).symm

/-- The actual checked executor computes both the intrinsic source and its
constructor-tree substitution, and that very computed pair satisfies the
existing combined-WM denotational substitution law. -/
theorem checkedOpenAnswers_computed_denotes
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) {sort : TypeExpr}
    (bindings : Bindings) (concrete : Pattern)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts (fromUsed targetFree
        (capturedTargetNames
          (fromUsed sourceFree pattern.freeFvarNames) bindings))))
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ sigma : Sub CombinedSignature
        (contextSorts sourceEntries) (contextSorts targetEntries),
      reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
        some sigma ∧
      ∃ term : Term CombinedSignature (contextSorts sourceEntries) sort,
        reifyOpen? CombinedLang sourceEntries pattern sort = some term ∧
        ∃ fragment : FirstOrder term,
          namedErase (names sourceEntries) fragment = pattern ∧
          ∃ supported : ∀ imageSort
              (position : Var (contextSorts sourceEntries) imageSort),
              FirstOrder (sigma imageSort position),
            ∃ targetCertificate : FirstOrder (bind sigma term),
              namedErase (names targetEntries) targetCertificate = concrete ∧
              FirstOrder.denote reading environment targetCertificate =
                FirstOrder.denote reading
                  (fun imageSort position =>
                    FirstOrder.denote reading environment
                      (supported imageSort position)) fragment := by
  obtain ⟨sigma, sigmaComputed, term, termComputed, fragment, sourceNamed,
      supported, targetNamed⟩ :=
    checkedOpenAnswers_computed_substitution sourceFree targetFree pattern
      bindings concrete returned
  exact ⟨sigma, sigmaComputed, term, termComputed, fragment, sourceNamed,
    supported, FirstOrder.substitute sigma supported fragment, targetNamed,
    denote_substitute reading sigma supported environment fragment⟩

/-! ## Agreement with the earlier variable-image specialization -/

/-- On a variable leaf the earlier WM-specific reifier and the
declaration-derived open reifier compute the same intrinsic term. -/
theorem reifyOpenVariable?_agrees_with_generic
    (entries : List (String × TypeExpr)) (variableName : String) (sort : TypeExpr) :
    (reifyOpenVariable? entries variableName sort).map (fun receipt => receipt.1) =
      reifyOpen? CombinedLang entries (.fvar variableName) sort := by
  cases found : lookupPosition? entries variableName sort <;>
    simp [reifyOpenVariable?, reifyOpen?, found]

/-- For every finite source context whose captured images are variables,
forgetting the earlier first-order certificates gives exactly the
declaration-derived constructor-tree substitution, not merely one with the
same rendering. This is a comparison of two independently computed codecs. -/
theorem reifyVariableImages?_agrees_with_generic
    (targetEntries : List (String × TypeExpr)) (bindings : Bindings)
    (sourceEntries : List (String × TypeExpr))
    (variableImages : ∀ variableName sort, (variableName, sort) ∈ sourceEntries →
      ∃ targetName, applyBindings bindings (.fvar variableName) = .fvar targetName) :
    (reifyVariableImages? targetEntries bindings sourceEntries).map
        (fun receipt => receipt.1) =
      reifyOpenImages? CombinedLang targetEntries bindings sourceEntries := by
  induction sourceEntries with
  | nil =>
      simp only [reifyVariableImages?, reifyOpenImages?, Option.map_some,
        Option.some.injEq]
      funext sort position
      nomatch position
  | cons head rest inductionHypothesis =>
      obtain ⟨sourceName, sourceSort⟩ := head
      obtain ⟨targetName, image⟩ := variableImages sourceName sourceSort (by simp)
      have tailImages : ∀ variableName sort, (variableName, sort) ∈ rest →
          ∃ targetName, applyBindings bindings (.fvar variableName) = .fvar targetName := by
        intro variableName sort membership
        exact variableImages variableName sort (by simp [membership])
      have tailAgreement := inductionHypothesis tailImages
      cases lookup : lookupPosition? targetEntries targetName sourceSort with
      | none =>
          simp [reifyVariableImages?, reifyOpenImages?, reifyOpen?, image, lookup]
      | some targetPosition =>
          cases tail : reifyVariableImages? targetEntries bindings rest with
          | none =>
              have genericTail : reifyOpenImages? CombinedLang targetEntries
                  bindings rest = none := by simpa [tail] using tailAgreement.symm
              simp [reifyVariableImages?, reifyOpenImages?, reifyOpen?, image,
                lookup, tail, genericTail]
          | some tailReceipt =>
              have genericTail : reifyOpenImages? CombinedLang targetEntries
                  bindings rest = some tailReceipt.1 := by
                simpa [tail] using tailAgreement.symm
              simp [reifyVariableImages?, reifyOpenImages?, reifyOpen?,
                image, lookup, tail, genericTail]
              funext sort position
              cases position <;> rfl

/-- An actual checked answer on the variable-image fragment computes one
intrinsic substitution shared by the old specialized and the general codec.
The older receipt still retains its first-order support certificate. -/
theorem checkedOpenAnswers_variable_substitution_agrees
    (sourceFree targetFree : FreeTypeContext)
    (pattern : Pattern) (sort : TypeExpr) (concrete : Pattern)
    (bindings : Bindings)
    (returned : bindings ∈
      checkedOpenAnswers sourceFree targetFree pattern sort concrete)
    (variableImages : ∀ variableSort
      (position : Var
        (contextSorts (fromUsed sourceFree pattern.freeFvarNames)) variableSort),
      ∃ targetName,
        applyBindings bindings
          (.fvar (names (fromUsed sourceFree pattern.freeFvarNames)
            variableSort position)) = .fvar targetName) :
    let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
    let targetEntries := fromUsed targetFree
      (capturedTargetNames sourceEntries bindings)
    ∃ receipt : SupportedSubstitution sourceEntries targetEntries,
      reifyVariableImages? targetEntries bindings sourceEntries = some receipt ∧
        reifyOpenImages? CombinedLang targetEntries bindings sourceEntries =
          some receipt.1 := by
  let sourceEntries := fromUsed sourceFree pattern.freeFvarNames
  let targetEntries := fromUsed targetFree
    (capturedTargetNames sourceEntries bindings)
  have oldSome := checkedOpenAnswers_variable_substitution_computes
    sourceFree targetFree pattern sort concrete bindings returned variableImages
  change (reifyVariableImages? targetEntries bindings sourceEntries).isSome = true
    at oldSome
  have entriesVariable : ∀ variableName variableSort,
      (variableName, variableSort) ∈ sourceEntries →
      ∃ targetName,
        applyBindings bindings (.fvar variableName) = .fvar targetName := by
    intro variableName variableSort membership
    obtain ⟨position, named⟩ := member_has_position sourceEntries membership
    obtain ⟨targetName, image⟩ := variableImages variableSort position
    refine ⟨targetName, ?_⟩
    change applyBindings bindings (.fvar (nameAt sourceEntries position)) =
      .fvar targetName at image
    rw [named] at image
    exact image
  have agreement := reifyVariableImages?_agrees_with_generic targetEntries
    bindings sourceEntries entriesVariable
  cases oldResult : reifyVariableImages? targetEntries bindings sourceEntries with
  | none => simp [oldResult] at oldSome
  | some receipt =>
      exact ⟨receipt, oldResult, by simpa [oldResult] using agreement.symm⟩

/-- The generic codec strictly extends the variable-image routine: one
authored compound Evidence tree succeeds where the older restricted routine
must reject it. Both use the same source and target contexts. -/
theorem constructor_tree_extension_is_strict :
    (reifyVariableImages? []
      [("e", pCombine pEvidenceZero pEvidenceZero)]
      [("e", .base "BinaryEvidence")]).isSome = false ∧
    (reifyOpenImages? CombinedLang []
      [("e", pCombine pEvidenceZero pEvidenceZero)]
      [("e", .base "BinaryEvidence")]).isSome = true := by
  decide +kernel

#print axioms reifyOpenVariable?_agrees_with_generic
#print axioms reifyVariableImages?_agrees_with_generic
#print axioms checkedOpenAnswers_variable_substitution_agrees
#print axioms constructor_tree_extension_is_strict

end Mettapedia.OSLF.Framework.WMCalculusCombinedGenericOpenCodec
