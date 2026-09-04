import Mettapedia.GSLT.LanguageDef.TptpOfficialFofCnfSerializationPipelineAgreement

/-!
# Readiness of the official FOF-to-CNF serialization pipeline

The official decoder enforces source-level function and predicate shape.  This
module transports those obligations through binder resolution, NNF, prenex
normalization, Skolemization, and definitional naming.  Consequently the
source-derived lexical plan is sufficient for every clause produced by the
pipeline; no unrelated serialization hypothesis is required at the final
boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofCnfSerializationPipelineReadiness

open LO FirstOrder
open scoped LO.FirstOrder
open TptpFofCnfOfficialSerializationReadiness

abbrev NamedTerm := TptpFofBinderResolution.NamedTerm
abbrev NamedFormula := TptpFofBinderResolution.NamedFormula
abbrev ResolvedTerm := TptpFofNormalizationSemantics.Term
abbrev ResolvedFormula := TptpFofNormalizationSemantics.Formula
abbrev NnfFormula := TptpFofPrenexSemantics.Formula

def ResolvedTermOriginalReady {depth : Nat} : ResolvedTerm depth -> Prop
  | .bvar _ => True
  | .fvar impossible => nomatch impossible
  | .func function arguments =>
      OriginalFunctionReady function /\
        forall index, ResolvedTermOriginalReady (arguments index)

def ResolvedFormulaOriginalReady {depth : Nat} : ResolvedFormula depth -> Prop
  | .verum | .falsum => True
  | .predicate predicate arguments =>
      OriginalPredicateReady predicate /\
        forall index, ResolvedTermOriginalReady (arguments index)
  | .equal left right =>
      ResolvedTermOriginalReady left /\ ResolvedTermOriginalReady right
  | .not body => ResolvedFormulaOriginalReady body
  | .and left right | .or left right | .iff left right
  | .implies left right | .reverseImplies left right | .xor left right
  | .nor left right | .nand left right =>
      ResolvedFormulaOriginalReady left /\
        ResolvedFormulaOriginalReady right
  | .all body | .ex body => ResolvedFormulaOriginalReady body

def NnfFormulaOriginalReady {depth : Nat} : NnfFormula depth -> Prop
  | .verum | .falsum => True
  | .rel relation arguments | .nrel relation arguments =>
      (match relation with
        | .predicate predicate => OriginalPredicateReady predicate
        | .equality => True) /\
      forall index, ResolvedTermOriginalReady (arguments index)
  | .and left right | .or left right =>
      NnfFormulaOriginalReady left /\ NnfFormulaOriginalReady right
  | .all body | .ex body => NnfFormulaOriginalReady body

private structure ResolvedTermReadiness (source : NamedTerm) : Prop where
  exact : forall (environment : List String) (target : ResolvedTerm environment.length),
    NamedTermOriginalReady source ->
    TptpFofBinderResolution.resolveTerm? environment source = some target ->
      ResolvedTermOriginalReady target

private theorem resolvedTermReadinessStep (source : NamedTerm)
    (smaller : forall child, sizeOf child < sizeOf source ->
      ResolvedTermReadiness child) : ResolvedTermReadiness source := by
  constructor
  intro environment target sourceReady resolved
  cases source with
  | «variable» name =>
      simp only [TptpFofBinderResolution.resolveTerm?] at resolved
      rcases Option.map_eq_some_iff.mp resolved with ⟨index, _, equality⟩
      subst target
      trivial
  | «function» head arguments =>
      simp only [NamedTermOriginalReady] at sourceReady
      simp only [TptpFofBinderResolution.resolveTerm?] at resolved
      rcases Option.bind_eq_some_iff.mp resolved with
        ⟨targetArguments, argumentsResolved, equality⟩
      simp at equality
      subst target
      have targetArgumentsReady :
          forall index,
            ResolvedTermOriginalReady (targetArguments.get index) := by
        have mapReady : forall (sources : List NamedTerm)
            (targets : List (ResolvedTerm environment.length)),
            sources.mapM (TptpFofBinderResolution.resolveTerm? environment) =
                some targets ->
            (forall candidate, candidate ∈ sources -> candidate ∈ arguments) ->
            NamedTermsOriginalReady sources ->
            forall index, ResolvedTermOriginalReady (targets.get index) := by
          intro sources
          induction sources with
          | nil =>
              intro targets mapped _ _ index
              change (some [] : Option
                (List (ResolvedTerm environment.length))) = some targets at mapped
              cases mapped
              exact Fin.elim0 index
          | cons child children inductionHypothesis =>
              intro targets mapped included ready index
              simp only [List.mapM_cons] at mapped
              rcases Option.bind_eq_some_iff.mp mapped with
                ⟨targetChild, childResolved, remaining⟩
              rcases Option.bind_eq_some_iff.mp remaining with
                ⟨targetChildren, childrenResolved, equality⟩
              simp at equality
              subst targets
              refine Fin.cases ?_ (fun childIndex => ?_) index
              · have childMembership : child ∈ arguments := included child (by simp)
                have childBound := List.sizeOf_lt_of_mem childMembership
                have argumentsBound :
                    sizeOf arguments < sizeOf
                      (TptpFofBinderResolution.NamedTerm.function head arguments) := by
                  simp
                exact (smaller child (Nat.lt_trans childBound argumentsBound)).exact
                  environment targetChild (ready child (by simp)) childResolved
              · exact inductionHypothesis targetChildren childrenResolved
                  (fun candidate membership => included candidate (by simp [membership]))
                  (fun candidate membership => ready candidate (by simp [membership]))
                  childIndex
        exact mapReady arguments targetArguments argumentsResolved
          (fun candidate membership => membership) sourceReady.2
      constructor
      · cases head with
        | mk kind lexeme =>
            cases kind <;>
              simp_all [OriginalFunctionReady]
      · exact targetArgumentsReady

private theorem resolvedTermReadiness (source : NamedTerm) :
    ResolvedTermReadiness source := by
  refine WellFounded.induction (measure sizeOf).wf source ?_
  intro current inductionHypothesis
  apply resolvedTermReadinessStep current
  intro child smaller
  exact inductionHypothesis child smaller

theorem resolveTerm?_originalReady (environment : List String)
    (source : NamedTerm) (target : ResolvedTerm environment.length)
    (sourceReady : NamedTermOriginalReady source)
    (resolved : TptpFofBinderResolution.resolveTerm? environment source =
      some target) :
    ResolvedTermOriginalReady target :=
  (resolvedTermReadiness source).exact environment target sourceReady resolved

private theorem mapM_resolveTerm_length_exact (environment : List String) :
    forall (sources : List NamedTerm)
      (targets : List (ResolvedTerm environment.length)),
      sources.mapM (TptpFofBinderResolution.resolveTerm? environment) =
          some targets ->
        targets.length = sources.length
  | [], targets, mapped => by
      change (some [] : Option (List (ResolvedTerm environment.length))) =
        some targets at mapped
      cases mapped
      rfl
  | source :: sources, targets, mapped => by
      simp only [List.mapM_cons] at mapped
      rcases Option.bind_eq_some_iff.mp mapped with
        ⟨target, _, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨targetTail, tailMapped, equality⟩
      simp at equality
      subst targets
      simp [mapM_resolveTerm_length_exact environment sources targetTail tailMapped]

private theorem mapM_resolveTerm_originalReady (environment : List String) :
    forall (sources : List NamedTerm)
      (targets : List (ResolvedTerm environment.length)),
      NamedTermsOriginalReady sources ->
      sources.mapM (TptpFofBinderResolution.resolveTerm? environment) =
          some targets ->
      forall index, ResolvedTermOriginalReady (targets.get index)
  | [], targets, _, mapped => by
      change (some [] : Option (List (ResolvedTerm environment.length))) =
        some targets at mapped
      cases mapped
      exact fun index => Fin.elim0 index
  | source :: sources, targets, ready, mapped => by
      simp only [List.mapM_cons] at mapped
      rcases Option.bind_eq_some_iff.mp mapped with
        ⟨target, targetResolved, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨targetTail, tailResolved, equality⟩
      simp at equality
      subst targets
      intro index
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact resolveTerm?_originalReady environment source target
          (ready source (by simp)) targetResolved
      · exact mapM_resolveTerm_originalReady environment sources targetTail
          (fun candidate membership => ready candidate (by simp [membership]))
          tailResolved tailIndex

theorem resolveFormula?_originalReady :
    forall (source : NamedFormula) (environment : List String)
      (target : ResolvedFormula environment.length),
      NamedFormulaOriginalReady source ->
      TptpFofBinderResolution.resolveFormula? environment source = some target ->
        ResolvedFormulaOriginalReady target
  | .verum, _, target, _, resolved => by
      simp [TptpFofBinderResolution.resolveFormula?] at resolved
      subst target
      trivial
  | .falsum, _, target, _, resolved => by
      simp [TptpFofBinderResolution.resolveFormula?] at resolved
      subst target
      trivial
  | .predicate head arguments, environment, target, sourceReady, resolved => by
      simp only [NamedFormulaOriginalReady] at sourceReady
      simp only [TptpFofBinderResolution.resolveFormula?] at resolved
      rcases Option.bind_eq_some_iff.mp resolved with
        ⟨targetArguments, argumentsResolved, equality⟩
      simp at equality
      subst target
      have lengthExact := mapM_resolveTerm_length_exact environment arguments
        targetArguments argumentsResolved
      constructor
      · cases head with
        | mk kind lexeme =>
            cases kind with
            | plain | system => trivial
            | defined =>
                simp only [OriginalPredicateReady]
                rw [lengthExact]
                exact List.length_pos_of_ne_nil sourceReady.1
      · exact mapM_resolveTerm_originalReady environment arguments
          targetArguments sourceReady.2 argumentsResolved
  | .equal left right, environment, target, sourceReady, resolved => by
      simp only [NamedFormulaOriginalReady] at sourceReady
      simp only [TptpFofBinderResolution.resolveFormula?] at resolved
      rcases Option.bind_eq_some_iff.mp resolved with
        ⟨targetLeft, leftResolved, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨targetRight, rightResolved, equality⟩
      simp at equality
      subst target
      exact ⟨resolveTerm?_originalReady environment left targetLeft
          sourceReady.1 leftResolved,
        resolveTerm?_originalReady environment right targetRight
          sourceReady.2 rightResolved⟩
  | .not body, environment, target, sourceReady, resolved => by
      simp only [NamedFormulaOriginalReady] at sourceReady
      simp only [TptpFofBinderResolution.resolveFormula?] at resolved
      rcases Option.map_eq_some_iff.mp resolved with
        ⟨targetBody, bodyResolved, equality⟩
      subst target
      exact resolveFormula?_originalReady body environment targetBody
        sourceReady bodyResolved
  | .and left right, environment, target, sourceReady, resolved
  | .or left right, environment, target, sourceReady, resolved
  | .iff left right, environment, target, sourceReady, resolved
  | .implies left right, environment, target, sourceReady, resolved
  | .reverseImplies left right, environment, target, sourceReady, resolved
  | .xor left right, environment, target, sourceReady, resolved
  | .nor left right, environment, target, sourceReady, resolved
  | .nand left right, environment, target, sourceReady, resolved => by
      simp only [NamedFormulaOriginalReady] at sourceReady
      simp only [TptpFofBinderResolution.resolveFormula?] at resolved
      rcases Option.bind_eq_some_iff.mp resolved with
        ⟨targetLeft, leftResolved, remaining⟩
      rcases Option.bind_eq_some_iff.mp remaining with
        ⟨targetRight, rightResolved, equality⟩
      simp at equality
      subst target
      exact ⟨resolveFormula?_originalReady left environment targetLeft
          sourceReady.1 leftResolved,
        resolveFormula?_originalReady right environment targetRight
          sourceReady.2 rightResolved⟩
  | .all binder body, environment, target, sourceReady, resolved
  | .ex binder body, environment, target, sourceReady, resolved => by
      simp only [NamedFormulaOriginalReady] at sourceReady
      simp only [TptpFofBinderResolution.resolveFormula?] at resolved
      rcases Option.map_eq_some_iff.mp resolved with
        ⟨targetBody, bodyResolved, equality⟩
      subst target
      exact resolveFormula?_originalReady body (binder :: environment)
        targetBody sourceReady bodyResolved

theorem preparedInput_resolvedOriginalReady
    (input : TptpOfficialFofClausificationPipelineAgreement.PreparedInput) :
    ResolvedFormulaOriginalReady input.resolved := by
  have namedReady := decodeFormula?_originalReady input.official input.named
    input.decoded
  exact resolveFormula?_originalReady input.named [] input.resolved namedReady
    input.resolved_exact

theorem normalize_originalReady {depth : Nat} (polarity : Bool)
    (source : ResolvedFormula depth)
    (ready : ResolvedFormulaOriginalReady source) :
    NnfFormulaOriginalReady
      (TptpFofNormalizationSemantics.normalize polarity source) := by
  induction source generalizing polarity with
  | verum | falsum =>
      cases polarity <;>
        simp [TptpFofNormalizationSemantics.normalize,
          NnfFormulaOriginalReady]
  | predicate predicate arguments =>
      cases polarity <;>
        simpa [TptpFofNormalizationSemantics.normalize,
          NnfFormulaOriginalReady, ResolvedFormulaOriginalReady] using ready
  | equal left right =>
      cases polarity <;>
        simp_all [TptpFofNormalizationSemantics.normalize,
          NnfFormulaOriginalReady, ResolvedFormulaOriginalReady]
  | not body inductionHypothesis =>
      cases polarity <;>
        simp_all [TptpFofNormalizationSemantics.normalize,
          ResolvedFormulaOriginalReady]
  | and left right leftInduction rightInduction
  | or left right leftInduction rightInduction
  | iff left right leftInduction rightInduction
  | implies left right leftInduction rightInduction
  | reverseImplies left right leftInduction rightInduction
  | xor left right leftInduction rightInduction
  | nor left right leftInduction rightInduction
  | nand left right leftInduction rightInduction =>
      cases polarity <;>
        simp_all [TptpFofNormalizationSemantics.normalize,
          NnfFormulaOriginalReady, ResolvedFormulaOriginalReady]
  | all body inductionHypothesis
  | ex body inductionHypothesis =>
      cases polarity <;>
        simp_all [TptpFofNormalizationSemantics.normalize,
          NnfFormulaOriginalReady, ResolvedFormulaOriginalReady]

theorem batchInput_nnfOriginalReady
    (input : TptpOfficialFofClausificationBatchAgreement.BatchInput) :
    NnfFormulaOriginalReady input.nnfFormula :=
  normalize_originalReady input.polarity input.pipeline.resolved
    (preparedInput_resolvedOriginalReady input.pipeline)

private def RewritingOriginalReady {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew TptpFofNormalizationSemantics.language
      Empty sourceDepth Empty targetDepth) : Prop :=
  forall index, ResolvedTermOriginalReady (rewriting (Semiterm.bvar index))

theorem resolvedTermOriginalReady_rew {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew TptpFofNormalizationSemantics.language
      Empty sourceDepth Empty targetDepth)
    (term : ResolvedTerm sourceDepth)
    (rewritingReady : RewritingOriginalReady rewriting)
    (ready : ResolvedTermOriginalReady term) :
    ResolvedTermOriginalReady (rewriting term) := by
  induction term with
  | bvar index => exact rewritingReady index
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      rw [LO.FirstOrder.Rew.func]
      exact ⟨ready.1, fun index =>
        inductionHypothesis index (ready.2 index)⟩

private theorem bShift_originalReady {depth : Nat} :
    RewritingOriginalReady
      (LO.FirstOrder.Rew.bShift :
        LO.FirstOrder.Rew TptpFofNormalizationSemantics.language
          Empty depth Empty (depth + 1)) := by
  intro index
  simp [ResolvedTermOriginalReady]

private theorem RewritingOriginalReady.q {sourceDepth targetDepth : Nat}
    {rewriting : LO.FirstOrder.Rew TptpFofNormalizationSemantics.language
      Empty sourceDepth Empty targetDepth}
    (ready : RewritingOriginalReady rewriting) :
    RewritingOriginalReady rewriting.q := by
  intro index
  refine Fin.cases ?_ (fun predecessor => ?_) index
  · simp [ResolvedTermOriginalReady]
  · rw [LO.FirstOrder.Rew.q_bvar_succ]
    exact resolvedTermOriginalReady_rew LO.FirstOrder.Rew.bShift
      (rewriting (Semiterm.bvar predecessor)) bShift_originalReady
      (ready predecessor)

theorem nnfFormulaOriginalReady_rew {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew TptpFofNormalizationSemantics.language
      Empty sourceDepth Empty targetDepth)
    (formula : NnfFormula sourceDepth)
    (rewritingReady : RewritingOriginalReady rewriting)
    (ready : NnfFormulaOriginalReady formula) :
    NnfFormulaOriginalReady (rewriting ▹ formula) := by
  induction formula generalizing targetDepth with
  | verum | falsum => trivial
  | rel relation arguments =>
      rw [LO.FirstOrder.Semiformula.rew_rel]
      cases relation with
      | predicate predicate =>
          exact ⟨ready.1, fun index =>
            resolvedTermOriginalReady_rew rewriting (arguments index)
              rewritingReady (ready.2 index)⟩
      | equality =>
          exact ⟨trivial, fun index =>
            resolvedTermOriginalReady_rew rewriting (arguments index)
              rewritingReady (ready.2 index)⟩
  | nrel relation arguments =>
      rw [LO.FirstOrder.Semiformula.rew_nrel]
      cases relation with
      | predicate predicate =>
          exact ⟨ready.1, fun index =>
            resolvedTermOriginalReady_rew rewriting (arguments index)
              rewritingReady (ready.2 index)⟩
      | equality =>
          exact ⟨trivial, fun index =>
            resolvedTermOriginalReady_rew rewriting (arguments index)
              rewritingReady (ready.2 index)⟩
  | and left right leftInduction rightInduction =>
      exact ⟨leftInduction rewriting rewritingReady ready.1,
        rightInduction rewriting rewritingReady ready.2⟩
  | or left right leftInduction rightInduction =>
      exact ⟨leftInduction rewriting rewritingReady ready.1,
        rightInduction rewriting rewritingReady ready.2⟩
  | all body inductionHypothesis =>
      exact inductionHypothesis rewriting.q rewritingReady.q ready
  | ex body inductionHypothesis =>
      exact inductionHypothesis rewriting.q rewritingReady.q ready

private def PrenexFormOriginalReady {depth : Nat}
    (form : TptpFofPrenexSemantics.PrenexForm depth) : Prop :=
  NnfFormulaOriginalReady form.toFormula

private theorem prenexFormOriginalReady_rew {sourceDepth targetDepth : Nat}
    (rewriting : LO.FirstOrder.Rew TptpFofNormalizationSemantics.language
      Empty sourceDepth Empty targetDepth)
    (form : TptpFofPrenexSemantics.PrenexForm sourceDepth)
    (rewritingReady : RewritingOriginalReady rewriting)
    (ready : PrenexFormOriginalReady form) :
    PrenexFormOriginalReady (form.rew rewriting) := by
  unfold PrenexFormOriginalReady
  rw [TptpFofPrenexSemantics.PrenexForm.rew_toFormula_exact]
  exact nnfFormulaOriginalReady_rew rewriting form.toFormula rewritingReady ready

private theorem combine_originalReady {depth : Nat}
    (connective : TptpFofPrenexSemantics.Connective) :
    forall (left right : TptpFofPrenexSemantics.PrenexForm depth),
      PrenexFormOriginalReady left -> PrenexFormOriginalReady right ->
        PrenexFormOriginalReady
          (TptpFofPrenexSemantics.combine connective left right)
  | .all leftBody, right, leftReady, rightReady => by
      rw [TptpFofPrenexSemantics.combine]
      change NnfFormulaOriginalReady leftBody.toFormula at leftReady
      change PrenexFormOriginalReady
        (TptpFofPrenexSemantics.combine connective leftBody
          (right.rew LO.FirstOrder.Rew.bShift))
      exact combine_originalReady connective leftBody
        (right.rew LO.FirstOrder.Rew.bShift) leftReady
        (prenexFormOriginalReady_rew LO.FirstOrder.Rew.bShift right
          bShift_originalReady rightReady)
  | .ex leftBody, right, leftReady, rightReady => by
      rw [TptpFofPrenexSemantics.combine]
      change NnfFormulaOriginalReady leftBody.toFormula at leftReady
      change PrenexFormOriginalReady
        (TptpFofPrenexSemantics.combine connective leftBody
          (right.rew LO.FirstOrder.Rew.bShift))
      exact combine_originalReady connective leftBody
        (right.rew LO.FirstOrder.Rew.bShift) leftReady
        (prenexFormOriginalReady_rew LO.FirstOrder.Rew.bShift right
          bShift_originalReady rightReady)
  | .matrix leftFormula leftQuantifierFree, .all rightBody,
      leftReady, rightReady => by
      rw [TptpFofPrenexSemantics.combine]
      change NnfFormulaOriginalReady rightBody.toFormula at rightReady
      change PrenexFormOriginalReady
        (TptpFofPrenexSemantics.combine connective
          ((TptpFofPrenexSemantics.PrenexForm.matrix leftFormula
            leftQuantifierFree).rew LO.FirstOrder.Rew.bShift) rightBody)
      exact combine_originalReady connective
        ((TptpFofPrenexSemantics.PrenexForm.matrix leftFormula
          leftQuantifierFree).rew LO.FirstOrder.Rew.bShift) rightBody
        (prenexFormOriginalReady_rew LO.FirstOrder.Rew.bShift _
          bShift_originalReady leftReady)
        rightReady
  | .matrix leftFormula leftQuantifierFree, .ex rightBody,
      leftReady, rightReady => by
      rw [TptpFofPrenexSemantics.combine]
      change NnfFormulaOriginalReady rightBody.toFormula at rightReady
      change PrenexFormOriginalReady
        (TptpFofPrenexSemantics.combine connective
          ((TptpFofPrenexSemantics.PrenexForm.matrix leftFormula
            leftQuantifierFree).rew LO.FirstOrder.Rew.bShift) rightBody)
      exact combine_originalReady connective
        ((TptpFofPrenexSemantics.PrenexForm.matrix leftFormula
          leftQuantifierFree).rew LO.FirstOrder.Rew.bShift) rightBody
        (prenexFormOriginalReady_rew LO.FirstOrder.Rew.bShift _
          bShift_originalReady leftReady)
        rightReady
  | .matrix leftFormula leftQuantifierFree,
      .matrix rightFormula rightQuantifierFree, leftReady, rightReady => by
      rw [TptpFofPrenexSemantics.combine]
      change NnfFormulaOriginalReady
        (connective.apply leftFormula rightFormula)
      cases connective <;> exact ⟨leftReady, rightReady⟩
termination_by left right => left.quantifierCount + right.quantifierCount
decreasing_by
  all_goals
    simp [TptpFofPrenexSemantics.PrenexForm.quantifierCount,
      TptpFofPrenexSemantics.PrenexForm.rew_quantifierCount_exact]

theorem prenex_originalReady {depth : Nat} (formula : NnfFormula depth)
    (ready : NnfFormulaOriginalReady formula) :
    PrenexFormOriginalReady (TptpFofPrenexSemantics.prenex formula) := by
  induction formula with
  | verum | falsum | rel | nrel => exact ready
  | and left right leftInduction rightInduction =>
      exact combine_originalReady .and
        (TptpFofPrenexSemantics.prenex left)
        (TptpFofPrenexSemantics.prenex right)
        (leftInduction ready.1) (rightInduction ready.2)
  | or left right leftInduction rightInduction =>
      exact combine_originalReady .or
        (TptpFofPrenexSemantics.prenex left)
        (TptpFofPrenexSemantics.prenex right)
        (leftInduction ready.1) (rightInduction ready.2)
  | all body inductionHypothesis => exact inductionHypothesis ready
  | ex body inductionHypothesis => exact inductionHypothesis ready

theorem prenexNormalize_originalReady {depth : Nat}
    (formula : NnfFormula depth) (ready : NnfFormulaOriginalReady formula) :
    NnfFormulaOriginalReady (TptpFofPrenexSemantics.normalize formula) :=
  prenex_originalReady formula ready

private def SkolemEnvironmentOriginalReady {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      TptpFofSkolemizationSemantics.Term targetDepth) : Prop :=
  forall index, SourceTermOriginalReady (environment index)

private theorem sourceTermOriginalReady_bShift {depth : Nat}
    (term : TptpFofSkolemizationSemantics.Term depth)
    (ready : SourceTermOriginalReady term) :
    SourceTermOriginalReady (LO.FirstOrder.Rew.bShift term) := by
  induction term with
  | bvar => trivial
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      rw [LO.FirstOrder.Rew.func]
      cases function with
      | original sourceFunction =>
          exact ⟨ready.1, fun index =>
            inductionHypothesis index (ready.2 index)⟩
      | generated identity =>
          exact fun index => inductionHypothesis index (ready index)

private theorem translateTerm_originalReady {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      TptpFofSkolemizationSemantics.Term targetDepth)
    (environmentReady : SkolemEnvironmentOriginalReady environment)
    (term : ResolvedTerm sourceDepth)
    (ready : ResolvedTermOriginalReady term) :
    SourceTermOriginalReady
      (TptpFofSkolemizationSemantics.translateTerm environment term) := by
  induction term with
  | bvar index => exact environmentReady index
  | fvar impossible => exact nomatch impossible
  | func function arguments inductionHypothesis =>
      exact ⟨ready.1, fun index =>
        inductionHypothesis index (ready.2 index)⟩

private theorem underUniversal_originalReady {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      TptpFofSkolemizationSemantics.Term targetDepth)
    (ready : SkolemEnvironmentOriginalReady environment) :
    SkolemEnvironmentOriginalReady
      (TptpFofSkolemizationSemantics.underUniversal environment) := by
  intro index
  refine Fin.cases ?_ (fun predecessor => ?_) index
  · trivial
  · simpa [TptpFofSkolemizationSemantics.underUniversal] using
      sourceTermOriginalReady_bShift (environment predecessor)
        (ready predecessor)

private theorem generatedApplication_originalReady (targetDepth identity : Nat) :
    SourceTermOriginalReady
      (TptpFofSkolemizationSemantics.generatedApplication targetDepth identity) := by
  intro index
  trivial

private theorem underExistential_originalReady {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      TptpFofSkolemizationSemantics.Term targetDepth)
    (identity : Nat)
    (ready : SkolemEnvironmentOriginalReady environment) :
    SkolemEnvironmentOriginalReady
      (TptpFofSkolemizationSemantics.underExistential environment identity) := by
  intro index
  refine Fin.cases ?_ (fun predecessor => ?_) index
  · exact generatedApplication_originalReady targetDepth identity
  · exact ready predecessor

theorem skolemizeFrom_originalReady {sourceDepth targetDepth : Nat}
    (environment : Fin sourceDepth ->
      TptpFofSkolemizationSemantics.Term targetDepth)
    (source : NnfFormula sourceDepth) (frontier : Nat)
    (environmentReady : SkolemEnvironmentOriginalReady environment)
    (sourceReady : NnfFormulaOriginalReady source) :
    FormulaOriginalReady
      (TptpFofSkolemizationSemantics.skolemizeFrom environment source frontier).formula := by
  induction source generalizing targetDepth frontier with
  | verum => simp [TptpFofSkolemizationSemantics.skolemizeFrom,
      FormulaOriginalReady]
  | falsum => simp [TptpFofSkolemizationSemantics.skolemizeFrom,
      FormulaOriginalReady]
  | rel relation arguments =>
      cases relation with
      | predicate predicate =>
          simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
            FormulaOriginalReady] using
            And.intro sourceReady.1 (fun index =>
              translateTerm_originalReady environment environmentReady
                (arguments index) (sourceReady.2 index))
      | equality =>
          simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
            FormulaOriginalReady] using
            And.intro True.intro (fun index =>
              translateTerm_originalReady environment environmentReady
                (arguments index) (sourceReady.2 index))
  | nrel relation arguments =>
      cases relation with
      | predicate predicate =>
          simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
            FormulaOriginalReady] using
            And.intro sourceReady.1 (fun index =>
              translateTerm_originalReady environment environmentReady
                (arguments index) (sourceReady.2 index))
      | equality =>
          simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
            FormulaOriginalReady] using
            And.intro True.intro (fun index =>
              translateTerm_originalReady environment environmentReady
                (arguments index) (sourceReady.2 index))
  | and left right leftInduction rightInduction =>
      simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
        FormulaOriginalReady] using
        And.intro
          (leftInduction environment frontier environmentReady sourceReady.1)
          (rightInduction environment
            (TptpFofSkolemizationSemantics.skolemizeFrom environment left frontier).next
            environmentReady sourceReady.2)
  | or left right leftInduction rightInduction =>
      simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
        FormulaOriginalReady] using
        And.intro
          (leftInduction environment frontier environmentReady sourceReady.1)
          (rightInduction environment
            (TptpFofSkolemizationSemantics.skolemizeFrom environment left frontier).next
            environmentReady sourceReady.2)
  | all body inductionHypothesis =>
      simpa only [TptpFofSkolemizationSemantics.skolemizeFrom,
        FormulaOriginalReady] using
        inductionHypothesis
          (TptpFofSkolemizationSemantics.underUniversal environment) frontier
          (underUniversal_originalReady environment environmentReady) sourceReady
  | ex body inductionHypothesis =>
      simpa only [TptpFofSkolemizationSemantics.skolemizeFrom] using
        inductionHypothesis
          (TptpFofSkolemizationSemantics.underExistential environment frontier)
          (frontier + 1)
          (underExistential_originalReady environment frontier environmentReady)
          sourceReady

theorem batchInput_skolemFormulaReady
    (input : TptpOfficialFofClausificationBatchAgreement.BatchInput) :
    FormulaReady input.skolemOutput.next input.skolemOutput.formula := by
  have prenexReady : NnfFormulaOriginalReady
      (TptpFofPrenexSemantics.prenex input.nnfFormula).toFormula :=
    prenex_originalReady input.nnfFormula (batchInput_nnfOriginalReady input)
  have original := skolemizeFrom_originalReady
    (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0)
    (TptpFofPrenexSemantics.prenex input.nnfFormula).toFormula 0
    (fun index => Fin.elim0 index) prenexReady
  have generated :=
    TptpFofSkolemizationSemantics.skolemizeFrom_formulaGeneratedBelow
      (environment :=
        (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0))
      (TptpFofPrenexSemantics.prenex input.nnfFormula).toFormula 0
      (fun index => Fin.elim0 index)
  simpa [TptpOfficialFofClausificationBatchAgreement.BatchInput.skolemOutput,
    TptpFofClausificationPipelineAgreement.skolemOutput,
    TptpFofClausificationPipelineAgreement.prenexForm] using
      formulaReady_of_original_generated
        (TptpFofSkolemizationSemantics.skolemizeFrom
          (Fin.elim0 : Fin 0 -> TptpFofSkolemizationSemantics.Term 0)
          (TptpFofPrenexSemantics.prenex input.nnfFormula).toFormula 0).formula
        original generated

private theorem universalPrefix_opened_ready {depth bound : Nat}
    {formula : TptpFofDefinitionalNamingSemantics.Source.Formula depth}
    (evidence : TptpFofDefinitionalNamingSemantics.UniversalPrefix formula)
    (ready : FormulaReady bound formula) :
    FormulaReady bound evidence.opened.formula := by
  induction evidence with
  | matrix quantifierFree => exact ready
  | all bodyPrefix inductionHypothesis =>
      exact inductionHypothesis ready

theorem batchInput_openedFormulaReady
    (input : TptpOfficialFofClausificationBatchAgreement.BatchInput) :
    FormulaReady input.skolemOutput.next input.namingEvidence.opened.formula :=
  universalPrefix_opened_ready input.namingEvidence
    (batchInput_skolemFormulaReady input)

theorem batchInput_serializationReady
    (input : TptpOfficialFofClausificationBatchAgreement.BatchInput) :
    TptpOfficialFofCnfSerializationPipelineAgreement.BatchSerializationReady
      input :=
  TptpOfficialFofCnfSerializationPipelineAgreement.batchSerializationReady_of_openedReady
    input (batchInput_openedFormulaReady input)

theorem officialSerialization_exists
    (input : TptpOfficialFofClausificationBatchAgreement.BatchInput)
    (firstClause : Nat) :
    exists result,
      TptpOfficialFofCnfSerializationPipelineAgreement.officialSerialization?
        input firstClause = some result :=
  TptpOfficialFofCnfSerializationPipelineAgreement.officialSerialization_exists_of_openedReady
    input firstClause (batchInput_openedFormulaReady input)

theorem endToEndExact_exists
    (input : TptpOfficialFofClausificationBatchAgreement.BatchInput)
    (firstClause : Nat) :
    exists result,
      TptpOfficialFofCnfSerializationPipelineAgreement.officialSerialization?
          input firstClause = some result /\
        TptpOfficialFofCnfSerializationPipelineAgreement.EndToEndExact
          input firstClause result := by
  obtain ⟨result, serialized⟩ := officialSerialization_exists input firstClause
  exact ⟨result, serialized,
    TptpOfficialFofCnfSerializationPipelineAgreement.endToEndExact_of_serializes
      input firstClause result serialized⟩

namespace Canary

noncomputable def shadowingBatchInput :
    TptpOfficialFofClausificationBatchAgreement.BatchInput where
  occurrence :=
    TptpOfficialFofClausificationBatchAgreement.Canary.preparedAxiom.occurrence
  polarity := true
  pipeline :=
    TptpOfficialFofClausificationPipelineAgreement.Canary.shadowingInput
  namingFrontier := 0

theorem shadowing_has_exact_serialization :
    exists result,
      TptpOfficialFofCnfSerializationPipelineAgreement.officialSerialization?
          shadowingBatchInput 7 = some result /\
        TptpOfficialFofCnfSerializationPipelineAgreement.EndToEndExact
          shadowingBatchInput 7 result :=
  endToEndExact_exists shadowingBatchInput 7

def appliedIntegerTerm : ResolvedTerm 1 :=
  .func
    ({ name := "7", kind := .integer } :
      TptpFofNormalizationSemantics.FunctionSymbol 1)
    ![.bvar 0]

theorem applied_integer_is_not_originalReady :
    Not (ResolvedTermOriginalReady appliedIntegerTerm) := by
  simp [appliedIntegerTerm, ResolvedTermOriginalReady, OriginalFunctionReady]

def nullaryDefinedPredicate : ResolvedFormula 0 :=
  .predicate
    ({ name := "$less", kind := .defined } :
      TptpFofNormalizationSemantics.PredicateSymbol 0)
    ![]

theorem nullary_defined_predicate_is_not_originalReady :
    Not (ResolvedFormulaOriginalReady nullaryDefinedPredicate) := by
  simp [nullaryDefinedPredicate, ResolvedFormulaOriginalReady,
    OriginalPredicateReady]

end Canary

#print axioms resolveTerm?_originalReady
#print axioms resolveFormula?_originalReady
#print axioms normalize_originalReady
#print axioms prenexNormalize_originalReady
#print axioms skolemizeFrom_originalReady
#print axioms batchInput_openedFormulaReady
#print axioms officialSerialization_exists
#print axioms endToEndExact_exists
#print axioms Canary.shadowing_has_exact_serialization
#print axioms Canary.applied_integer_is_not_originalReady
#print axioms Canary.nullary_defined_predicate_is_not_originalReady

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofCnfSerializationPipelineReadiness
