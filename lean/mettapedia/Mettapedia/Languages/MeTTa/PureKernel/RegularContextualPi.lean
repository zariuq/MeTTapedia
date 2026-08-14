import Mettapedia.Languages.MeTTa.PureKernel.RegularContextualCandidates

/-!
# The dependent function candidate over realized contexts

This module constructs the genuinely dependent function candidate required by
the regular Pure fundamental lemma.  Its domain is interpreted in the current
realizing environment.  Its codomain is interpreted in the extended environment
formed from the actual argument and that same environment.

Argument reduction therefore changes the codomain environment.  The proof uses
both directions of contextual reduction coherence; no arbitrary backward
closure of strong normalization is assumed.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## Environment transport helpers -/

/-- Rename every image of a simultaneous environment. -/
def renameEnvironment (ρ : Ren m k) (environment : Sub n m) : Sub n k :=
  fun index => rename ρ (environment index)

theorem renameEnvironment_comp (later : Ren m k) (earlier : Ren n m)
    (environment : Sub l n) :
    renameEnvironment later (renameEnvironment earlier environment) =
      renameEnvironment (fun index => later (earlier index)) environment := by
  funext index
  exact rename_comp later earlier (environment index)

namespace SubRedStar

/-- Pointwise environment reduction survives renaming into a future scope. -/
theorem renameEnvironment {source target : Sub n m}
    (steps : SubRedStar source target) (ρ : Ren m k) :
    SubRedStar (PresentationBoundary.renameEnvironment ρ source)
      (PresentationBoundary.renameEnvironment ρ target) :=
  fun index => SubRedStar.rename ρ (steps index)

/-- Pointwise reduction of a head and tail combines into reduction of the
extended environment. -/
theorem cons {sourceHead targetHead : PureTm m}
    {sourceTail targetTail : Sub n m}
    (headSteps : RedStar sourceHead targetHead)
    (tailSteps : SubRedStar sourceTail targetTail) :
    SubRedStar (consSub sourceHead sourceTail)
      (consSub targetHead targetTail) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact headSteps
  · intro preceding
    exact tailSteps preceding

end SubRedStar

/-! ## The dependent function predicate -/

/-- A function belongs to the dependent function predicate when, after every
future renaming, it maps each domain member to the codomain selected in the
environment extended by that actual argument. -/
def contextualPiPred {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    (environment : Sub n m) (function : PureTm m) : Prop :=
  ∀ {k : Nat} (ρ : Ren m k) (argument : PureTm k),
    domain.pred (renameEnvironment ρ environment) argument →
      codomain.pred
        (consSub argument (renameEnvironment ρ environment))
        (.app (rename ρ function) argument)

/-- A realized base environment and a domain member form a realized extended
environment. -/
theorem contextualPi_extended_realizes
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {argument : PureTm m} (argumentCovered : domain.pred environment argument) :
    (context.extendContextual domain).Realizes
      (consSub argument environment) :=
  ⟨environmentRealized, argumentCovered⟩

/-- A contextual dependent function is strongly normalizing.  A fresh variable
probes the function without assuming injectivity of weakening. -/
theorem contextualPi_cr1
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {function : PureTm m}
    (covered : contextualPiPred domain codomain environment function) :
    ReductionAccessible function := by
  let futureEnvironment := renameEnvironment wk environment
  have futureRealized : context.Realizes futureEnvironment :=
    context.rename_realizes environment wk environmentRealized
  have argumentCovered :
      domain.pred futureEnvironment (.var (0 : Fin (m + 1))) := by
    apply domain.cr3 futureRealized (neutral_var 0)
    intro target step
    cases step
  have applicationCovered :=
    covered wk (.var 0) argumentCovered
  have extendedRealized :=
    contextualPi_extended_realizes domain futureRealized argumentCovered
  have renamedAccessible :=
    codomain.cr1 extendedRealized applicationCovered
  exact reductionAccessible_of_rename wk
    (reductionAccessible_app_left renamedAccessible)

/-- The dependent function predicate is closed under reduction of its
function. -/
theorem contextualPi_cr2
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {source target : PureTm m}
    (covered : contextualPiPred domain codomain environment source)
    (step : Red source target) :
    contextualPiPred domain codomain environment target := by
  intro k ρ argument argumentCovered
  have futureRealized :=
    context.rename_realizes environment ρ environmentRealized
  have extendedRealized :=
    contextualPi_extended_realizes domain futureRealized argumentCovered
  exact codomain.cr2 extendedRealized
    (covered ρ argument argumentCovered)
    (.congAppFun (red_rename step ρ))

/-- Closure under every finite reduction sequence. -/
theorem contextualPi_cr2_star
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {source target : PureTm m}
    (covered : contextualPiPred domain codomain environment source)
    (steps : RedStar source target) :
    contextualPiPred domain codomain environment target := by
  induction steps with
  | refl => exact covered
  | tail hxy finalStep ih =>
      exact contextualPi_cr2 domain codomain environmentRealized ih finalStep

/-- Neutral expansion for dependent functions.  When the tested argument
reduces, codomain coherence transports the induction result back from the new
argument-indexed environment. -/
theorem contextualPi_cr3
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {function : PureTm m} (functionNeutral : IsNeutral function)
    (functionReducts : ∀ target, Red function target →
      contextualPiPred domain codomain environment target) :
    contextualPiPred domain codomain environment function := by
  intro k ρ argument argumentCovered
  have futureRealized :=
    context.rename_realizes environment ρ environmentRealized
  have extendedRealized :=
    contextualPi_extended_realizes domain futureRealized argumentCovered
  have renamedNeutral := functionNeutral.rename ρ
  have argumentAccessible := domain.cr1 futureRealized argumentCovered
  induction argumentAccessible with
  | intro argument smallerArgument argumentIH =>
      apply codomain.cr3 extendedRealized (neutral_app renamedNeutral)
      intro target step
      rcases neutral_app_step renamedNeutral step with
        ⟨renamedFunction, functionStep, rfl⟩ |
          ⟨argument', argumentStep, rfl⟩
      · obtain ⟨sourceFunction, sourceStep, rfl⟩ :=
          red_rename_reflect ρ functionStep
        exact functionReducts sourceFunction sourceStep
          ρ argument argumentCovered
      · have argumentCovered' :=
          domain.cr2 futureRealized argumentCovered argumentStep
        have targetResult :=
          argumentIH argument' argumentStep argumentCovered'
        have targetExtendedRealized :=
          contextualPi_extended_realizes domain futureRealized
            argumentCovered'
        have environmentSteps :
            SubRedStar
              (consSub argument (renameEnvironment ρ environment))
              (consSub argument' (renameEnvironment ρ environment)) :=
          SubRedStar.cons (red_to_redStar argumentStep)
            (SubRedStar.refl _)
        exact (codomain.reduce_pred extendedRealized environmentSteps
          (.app (rename ρ function) argument')).2
            (targetResult targetExtendedRealized)

/-- Dependent function membership is stable under renaming of the source
scope. -/
theorem contextualPi_rename
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m}
    {function : PureTm m}
    (covered : contextualPiPred domain codomain environment function)
    (ξ : Ren m k) :
    contextualPiPred domain codomain
      (renameEnvironment ξ environment) (rename ξ function) := by
  intro l ρ argument argumentCovered
  have argumentCovered' :
      domain.pred
        (renameEnvironment (fun index => ρ (ξ index)) environment)
        argument := by
    simpa only [renameEnvironment_comp] using argumentCovered
  have mapped :=
    covered (fun index => ρ (ξ index)) argument argumentCovered'
  simpa only [renameEnvironment_comp, rename_comp] using mapped

/-- Reduction of the base environment leaves the dependent function predicate
invariant.  The two directions use the two directions of domain and codomain
coherence. -/
theorem contextualPi_reduce_iff
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {source target : Sub n m} (sourceRealized : context.Realizes source)
    (steps : SubRedStar source target) (function : PureTm m) :
    contextualPiPred domain codomain source function ↔
      contextualPiPred domain codomain target function := by
  constructor
  · intro covered k ρ argument argumentAtTarget
    have futureSteps := steps.renameEnvironment ρ
    have sourceFutureRealized :=
      context.rename_realizes source ρ sourceRealized
    have argumentAtSource :=
      (domain.reduce_pred sourceFutureRealized futureSteps argument).2
        argumentAtTarget
    have sourceResult := covered ρ argument argumentAtSource
    have sourceExtendedRealized :=
      contextualPi_extended_realizes domain sourceFutureRealized
        argumentAtSource
    have extendedSteps :
        SubRedStar
          (consSub argument (renameEnvironment ρ source))
          (consSub argument (renameEnvironment ρ target)) :=
      SubRedStar.cons (RedStar.refl argument) futureSteps
    exact (codomain.reduce_pred sourceExtendedRealized extendedSteps
      (.app (rename ρ function) argument)).1 sourceResult
  · intro covered k ρ argument argumentAtSource
    have futureSteps := steps.renameEnvironment ρ
    have sourceFutureRealized :=
      context.rename_realizes source ρ sourceRealized
    have targetFutureRealized :=
      context.reduce_realizes sourceFutureRealized futureSteps
    have argumentAtTarget :=
      (domain.reduce_pred sourceFutureRealized futureSteps argument).1
        argumentAtSource
    have targetResult := covered ρ argument argumentAtTarget
    have sourceExtendedRealized :=
      contextualPi_extended_realizes domain sourceFutureRealized
        argumentAtSource
    have extendedSteps :
        SubRedStar
          (consSub argument (renameEnvironment ρ source))
          (consSub argument (renameEnvironment ρ target)) :=
      SubRedStar.cons (RedStar.refl argument) futureSteps
    exact (codomain.reduce_pred sourceExtendedRealized extendedSteps
      (.app (rename ρ function) argument)).2 targetResult

/-! ## Exact head expansion -/

/-- A one-step reduction of an application which is itself neutral comes from
one of its two components.  This weaker premise is needed when the function is
an eliminator rather than a neutral term. -/
theorem neutral_application_step
    {function argument target : PureTm n}
    (neutral : IsNeutral (.app function argument))
    (step : Red (.app function argument) target) :
    (∃ function', Red function function' ∧
        target = .app function' argument) ∨
      (∃ argument', Red argument argument' ∧
        target = .app function argument') := by
  cases step with
  | betaPi body argument =>
      cases neutral
  | congAppFun functionStep =>
      exact .inl ⟨_, functionStep, rfl⟩
  | congAppArg argumentStep =>
      exact .inr ⟨_, argumentStep, rfl⟩

/-- A non-lambda head belongs to the dependent function predicate when all of
its immediate head reducts do.  Reduction of the later test argument is handled
by accessibility induction and codomain environment coherence. -/
theorem contextualPi_of_head_reducts
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {function : PureTm m}
    (applicationNeutral : ∀ {k : Nat} (ρ : Ren m k)
      (argument : PureTm k), IsNeutral (.app (rename ρ function) argument))
    (functionReducts : ∀ target, Red function target →
      contextualPiPred domain codomain environment target) :
    contextualPiPred domain codomain environment function := by
  intro k ρ argument argumentCovered
  have futureRealized :=
    context.rename_realizes environment ρ environmentRealized
  have extendedRealized :=
    contextualPi_extended_realizes domain futureRealized argumentCovered
  have argumentAccessible := domain.cr1 futureRealized argumentCovered
  induction argumentAccessible with
  | intro argument smallerArgument argumentIH =>
      have wholeNeutral := applicationNeutral ρ argument
      apply codomain.cr3 extendedRealized wholeNeutral
      intro target step
      rcases neutral_application_step wholeNeutral step with
        ⟨renamedFunction, functionStep, rfl⟩ |
          ⟨argument', argumentStep, rfl⟩
      ·
          obtain ⟨sourceFunction, sourceStep, rfl⟩ :=
            red_rename_reflect ρ functionStep
          exact functionReducts sourceFunction sourceStep
            ρ argument argumentCovered
      ·
          have argumentCovered' :=
            domain.cr2 futureRealized argumentCovered argumentStep
          have targetResult :=
            argumentIH _ argumentStep argumentCovered'
          have targetExtendedRealized :=
            contextualPi_extended_realizes domain futureRealized
              argumentCovered'
          have environmentSteps :
              SubRedStar
                (consSub argument (renameEnvironment ρ environment))
                (consSub _ (renameEnvironment ρ environment)) :=
            SubRedStar.cons (red_to_redStar argumentStep)
              (SubRedStar.refl _)
          exact (codomain.reduce_pred extendedRealized environmentSteps
            _).2 (targetResult targetExtendedRealized)

/-- Exact beta expansion for the dependent function predicate. -/
theorem contextualPi_beta_expansion
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {body : PureTm (m + 1)} {argument : PureTm m}
    (bodyAccessible : ReductionAccessible body)
    (argumentAccessible : ReductionAccessible argument)
    (contractumCovered :
      contextualPiPred domain codomain environment (inst0 argument body)) :
    contextualPiPred domain codomain environment
      (.app (.lam body) argument) := by
  induction bodyAccessible generalizing argument with
  | intro body bodySmaller bodyIH =>
      induction argumentAccessible with
      | intro argument argumentSmaller argumentIH =>
          apply contextualPi_of_head_reducts domain codomain
            environmentRealized
          · intro k ρ input
            change IsNeutral
              (.app
                (.app (.lam (rename (liftRen ρ) body))
                  (rename ρ argument))
                input)
            trivial
          · intro target step
            cases step with
            | betaPi =>
                exact contractumCovered
            | congAppFun lambdaStep =>
                cases lambdaStep with
                | congLam bodyStep =>
                    have reducedContractum :
                        contextualPiPred domain codomain environment
                          (inst0 argument _) :=
                      contextualPi_cr2_star domain codomain
                        environmentRealized contractumCovered
                        (redStar_inst0_body argument
                          (red_to_redStar bodyStep))
                    intro k ρ input inputCovered
                    exact bodyIH _ bodyStep
                      (argumentAccessible :=
                        Acc.intro argument argumentSmaller)
                      (contractumCovered := reducedContractum)
                      ρ input inputCovered
            | congAppArg argumentStep =>
                have reducedContractum :
                    contextualPiPred domain codomain environment
                      (inst0 _ body) :=
                  contextualPi_cr2_star domain codomain
                    environmentRealized contractumCovered
                    (redStar_inst0_argument body
                      (red_to_redStar argumentStep))
                intro k ρ input inputCovered
                exact argumentIH _ argumentStep
                  (contractumCovered := reducedContractum)
                  ρ input inputCovered

/-- Exact first-projection expansion for the dependent function predicate. -/
theorem contextualPi_fst_pair_expansion
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {first second : PureTm m}
    (firstCovered : contextualPiPred domain codomain environment first)
    (secondAccessible : ReductionAccessible second) :
    contextualPiPred domain codomain environment
      (.fst (.pair first second)) := by
  have firstAccessible :=
    contextualPi_cr1 domain codomain environmentRealized firstCovered
  induction firstAccessible generalizing second with
  | intro first firstSmaller firstIH =>
      induction secondAccessible with
      | intro second secondSmaller secondIH =>
          apply contextualPi_of_head_reducts domain codomain
            environmentRealized
          · intro k ρ input
            change IsNeutral
              (.app (.fst (.pair (rename ρ first) (rename ρ second))) input)
            trivial
          · intro target step
            cases step with
            | betaSigmaFst =>
                exact firstCovered
            | congFst pairStep =>
                cases pairStep with
                | congPairFst firstStep =>
                    have firstCovered' :
                        contextualPiPred domain codomain environment _ :=
                      contextualPi_cr2 domain codomain environmentRealized
                        firstCovered firstStep
                    intro k ρ input inputCovered
                    exact firstIH _ firstStep
                      firstCovered'
                      (Acc.intro second secondSmaller)
                      ρ input inputCovered
                | congPairSnd secondStep =>
                    intro k ρ input inputCovered
                    exact secondIH _ secondStep
                      ρ input inputCovered

/-- Exact second-projection expansion for the dependent function predicate. -/
theorem contextualPi_snd_pair_expansion
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {first second : PureTm m}
    (firstAccessible : ReductionAccessible first)
    (secondCovered : contextualPiPred domain codomain environment second) :
    contextualPiPred domain codomain environment
      (.snd (.pair first second)) := by
  have secondAccessible :=
    contextualPi_cr1 domain codomain environmentRealized secondCovered
  induction firstAccessible generalizing second with
  | intro first firstSmaller firstIH =>
      induction secondAccessible with
      | intro second secondSmaller secondIH =>
          apply contextualPi_of_head_reducts domain codomain
            environmentRealized
          · intro k ρ input
            change IsNeutral
              (.app (.snd (.pair (rename ρ first) (rename ρ second))) input)
            trivial
          · intro target step
            cases step with
            | betaSigmaSnd =>
                exact secondCovered
            | congSnd pairStep =>
                cases pairStep with
                | congPairFst firstStep =>
                    intro k ρ input inputCovered
                    exact firstIH _ firstStep
                      secondCovered
                      (Acc.intro second secondSmaller)
                      ρ input inputCovered
                | congPairSnd secondStep =>
                    have secondCovered' :
                        contextualPiPred domain codomain environment _ :=
                      contextualPi_cr2 domain codomain environmentRealized
                        secondCovered secondStep
                    intro k ρ input inputCovered
                    exact secondIH _ secondStep secondCovered'
                      ρ input inputCovered

/-! ## The packaged dependent function type -/

/-- The contextual dependent function type.  This is the first genuinely
dependent candidate over semantic contexts: the codomain is selected in the
extension by the actual tested argument. -/
def ContextualCandidateType.pi
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain)) :
    ContextualCandidateType context where
  pred := fun environment function =>
    contextualPiPred domain codomain environment function
  cr1 := by
    intro m environment function realized covered
    exact contextualPi_cr1 domain codomain realized covered
  cr2 := by
    intro m environment source target realized covered step
    exact contextualPi_cr2 domain codomain realized covered step
  cr3 := by
    intro m environment function realized neutral reducts
    exact contextualPi_cr3 domain codomain realized neutral reducts
  rename_mem := by
    intro m k environment ρ function realized covered
    exact contextualPi_rename domain codomain covered ρ
  reduce_pred := by
    intro m source target sourceRealized steps function
    exact contextualPi_reduce_iff domain codomain
      sourceRealized steps function
  beta_expansion := by
    intro m environment realized body argument bodyAccessible argumentAccessible
      contractumCovered
    exact contextualPi_beta_expansion domain codomain realized
      bodyAccessible argumentAccessible contractumCovered
  fst_pair_expansion := by
    intro m environment realized first second firstCovered secondAccessible
    exact contextualPi_fst_pair_expansion domain codomain realized
      firstCovered secondAccessible
  snd_pair_expansion := by
    intro m environment realized first second firstAccessible secondCovered
    exact contextualPi_snd_pair_expansion domain codomain realized
      firstAccessible secondCovered

theorem ContextualCandidateType.pi_pred
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    (environment : Sub n m) (function : PureTm m) :
    (domain.pi codomain).pred environment function ↔
      contextualPiPred domain codomain environment function :=
  Iff.rfl

/-! ## Positive and negative canaries -/

def contextualNormalizingPiDomain :
    ContextualCandidateType CoherentCandidateContext.empty :=
  ContextualCandidateType.normalizing CoherentCandidateContext.empty

def contextualNormalizingPiCodomain :
    ContextualCandidateType
      (CoherentCandidateContext.empty.extendContextual
        contextualNormalizingPiDomain) :=
  ContextualCandidateType.normalizing _

def contextualNormalizingPi :
    ContextualCandidateType CoherentCandidateContext.empty :=
  contextualNormalizingPiDomain.pi contextualNormalizingPiCodomain

/-- The identity lambda inhabits the contextual normalizing function type. -/
theorem contextual_identity_in_normalizing_pi :
    contextualNormalizingPi.pred (ids : Sub 0 0)
      (.lam (.var 0)) := by
  intro k ρ argument argumentCovered
  change ReductionAccessible
    (.app (.lam (.var (0 : Fin (k + 1)))) argument)
  exact reductionAccessible_identity_application argumentCovered

/-- The accessible delta function is rejected because applying it to itself
produces the non-accessible omega term. -/
theorem contextual_delta_not_in_normalizing_pi :
    ¬ contextualNormalizingPi.pred (ids : Sub 0 0) regularDelta := by
  intro covered
  have applicationCovered :=
    covered (fun index : Fin 0 => index) regularDelta
      regularDelta_reductionAccessible
  change ReductionAccessible regularOmega at applicationCovered
  exact omega_not_in_normalizing_candidate applicationCovered

/-! ## Axiom audit -/

#print axioms renameEnvironment_comp
#print axioms SubRedStar.renameEnvironment
#print axioms SubRedStar.cons
#print axioms contextualPi_cr1
#print axioms contextualPi_cr2
#print axioms contextualPi_cr3
#print axioms contextualPi_rename
#print axioms contextualPi_reduce_iff
#print axioms contextualPi_beta_expansion
#print axioms contextualPi_fst_pair_expansion
#print axioms contextualPi_snd_pair_expansion
#print axioms ContextualCandidateType.pi
#print axioms contextual_identity_in_normalizing_pi
#print axioms contextual_delta_not_in_normalizing_pi

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
