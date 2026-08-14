import Mettapedia.Languages.MeTTa.PureKernel.RegularContextualPi

/-!
# The dependent pair candidate over realized contexts

Dependent pairs are observed through their projections.  The first projection
belongs to the domain candidate in the current environment.  The second
projection belongs to the codomain candidate in the environment extended by
that first projection.  Reducing a pair therefore changes both the observed
second projection and the environment in which it is interpreted.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## Environment transport -/

theorem renameEnvironment_consSub (ρ : Ren m k) (head : PureTm m)
    (tail : Sub n m) :
    renameEnvironment ρ (consSub head tail) =
      consSub (rename ρ head) (renameEnvironment ρ tail) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro preceding
    rfl

/-! ## The dependent pair predicate -/

/-- A dependent pair is observed by its projections.  Its second projection is
interpreted in the codomain selected by its actual first projection. -/
def contextualSigmaPred {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    (environment : Sub n m) (pair : PureTm m) : Prop :=
  domain.pred environment (.fst pair) ∧
    codomain.pred (consSub (.fst pair) environment) (.snd pair)

/-- The dependent pair predicate is strongly normalizing. -/
theorem contextualSigma_cr1
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {pair : PureTm m}
    (covered : contextualSigmaPred domain codomain environment pair) :
    ReductionAccessible pair :=
  reductionAccessible_fst_argument
    (domain.cr1 environmentRealized covered.1)

/-- Pair reduction transports both projections and the codomain environment. -/
theorem contextualSigma_cr2
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {source target : PureTm m}
    (covered : contextualSigmaPred domain codomain environment source)
    (step : Red source target) :
    contextualSigmaPred domain codomain environment target := by
  have targetFirstCovered :=
    domain.cr2 environmentRealized covered.1 (.congFst step)
  have sourceExtendedRealized :=
    contextualPi_extended_realizes domain environmentRealized covered.1
  have targetSecondAtSource :=
    codomain.cr2 sourceExtendedRealized covered.2 (.congSnd step)
  have environmentSteps :
      SubRedStar
        (consSub (.fst source) environment)
        (consSub (.fst target) environment) :=
    SubRedStar.cons (red_to_redStar (.congFst step))
      (SubRedStar.refl environment)
  exact ⟨targetFirstCovered,
    (codomain.reduce_pred sourceExtendedRealized environmentSteps
      (.snd target)).1 targetSecondAtSource⟩

/-- Closure under every finite reduction sequence. -/
theorem contextualSigma_cr2_star
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {source target : PureTm m}
    (covered : contextualSigmaPred domain codomain environment source)
    (steps : RedStar source target) :
    contextualSigmaPred domain codomain environment target := by
  induction steps with
  | refl => exact covered
  | tail hxy finalStep ih =>
      exact contextualSigma_cr2 domain codomain environmentRealized ih finalStep

/-- Neutral dependent pairs are admitted when every immediate pair reduct is
admitted.  The codomain component uses backward environment coherence after
the first projection moves. -/
theorem contextualSigma_cr3
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {pair : PureTm m} (pairNeutral : IsNeutral pair)
    (pairReducts : ∀ target, Red pair target →
      contextualSigmaPred domain codomain environment target) :
    contextualSigmaPred domain codomain environment pair := by
  have firstCovered : domain.pred environment (.fst pair) := by
    apply domain.cr3 environmentRealized (neutral_fst pairNeutral)
    intro target step
    obtain ⟨pair', pairStep, rfl⟩ := neutral_fst_step pairNeutral step
    exact (pairReducts pair' pairStep).1
  have extendedRealized :=
    contextualPi_extended_realizes domain environmentRealized firstCovered
  refine ⟨firstCovered, ?_⟩
  apply codomain.cr3 extendedRealized (neutral_snd pairNeutral)
  intro target step
  obtain ⟨pair', pairStep, rfl⟩ := neutral_snd_step pairNeutral step
  have targetCovered := (pairReducts pair' pairStep).2
  have environmentSteps :
      SubRedStar
        (consSub (.fst pair) environment)
        (consSub (.fst pair') environment) :=
    SubRedStar.cons (red_to_redStar (.congFst pairStep))
      (SubRedStar.refl environment)
  exact (codomain.reduce_pred extendedRealized environmentSteps
    (.snd pair')).2 targetCovered

/-- Dependent pair membership is stable under renaming. -/
theorem contextualSigma_rename
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {pair : PureTm m}
    (covered : contextualSigmaPred domain codomain environment pair)
    (ρ : Ren m k) :
    contextualSigmaPred domain codomain
      (renameEnvironment ρ environment) (rename ρ pair) := by
  have firstCovered :=
    domain.rename_mem environment ρ environmentRealized covered.1
  have extendedRealized :=
    contextualPi_extended_realizes domain environmentRealized covered.1
  have secondCovered :=
    codomain.rename_mem (consSub (.fst pair) environment) ρ
      extendedRealized covered.2
  constructor
  · change domain.pred (fun index => rename ρ (environment index))
      (.fst (rename ρ pair))
    exact firstCovered
  · have environmentEq :
        (fun index => rename ρ (consSub (.fst pair) environment index)) =
          consSub (.fst (rename ρ pair)) (renameEnvironment ρ environment) := by
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro preceding
        rfl
    rw [← environmentEq]
    exact secondCovered

/-- Reduction of the base environment leaves dependent pair membership
invariant. -/
theorem contextualSigma_reduce_iff
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {source target : Sub n m} (sourceRealized : context.Realizes source)
    (steps : SubRedStar source target) (pair : PureTm m) :
    contextualSigmaPred domain codomain source pair ↔
      contextualSigmaPred domain codomain target pair := by
  constructor
  · intro covered
    have targetFirst :=
      (domain.reduce_pred sourceRealized steps (.fst pair)).1 covered.1
    have sourceExtendedRealized :=
      contextualPi_extended_realizes domain sourceRealized covered.1
    have extendedSteps :
        SubRedStar
          (consSub (.fst pair) source)
          (consSub (.fst pair) target) :=
      SubRedStar.cons (RedStar.refl _) steps
    exact ⟨targetFirst,
      (codomain.reduce_pred sourceExtendedRealized extendedSteps
        (.snd pair)).1 covered.2⟩
  · intro covered
    have sourceFirst :=
      (domain.reduce_pred sourceRealized steps (.fst pair)).2 covered.1
    have sourceExtendedRealized :=
      contextualPi_extended_realizes domain sourceRealized sourceFirst
    have extendedSteps :
        SubRedStar
          (consSub (.fst pair) source)
          (consSub (.fst pair) target) :=
      SubRedStar.cons (RedStar.refl _) steps
    exact ⟨sourceFirst,
      (codomain.reduce_pred sourceExtendedRealized extendedSteps
        (.snd pair)).2 covered.2⟩

/-! ## Exact head expansion -/

/-- If a first projection is neutral, its reduction can only reflect a
reduction of the projected term. -/
theorem neutral_fst_projection_step
    {pair target : PureTm n}
    (projectionNeutral : IsNeutral (.fst pair))
    (step : Red (.fst pair) target) :
    ∃ pair', Red pair pair' ∧ target = .fst pair' := by
  cases step with
  | betaSigmaFst first second =>
      cases projectionNeutral
  | congFst pairStep =>
      exact ⟨_, pairStep, rfl⟩

/-- If a second projection is neutral, its reduction can only reflect a
reduction of the projected term. -/
theorem neutral_snd_projection_step
    {pair target : PureTm n}
    (projectionNeutral : IsNeutral (.snd pair))
    (step : Red (.snd pair) target) :
    ∃ pair', Red pair pair' ∧ target = .snd pair' := by
  cases step with
  | betaSigmaSnd first second =>
      cases projectionNeutral
  | congSnd pairStep =>
      exact ⟨_, pairStep, rfl⟩

/-- A non-pair head belongs to the dependent pair predicate when all of its
immediate head reducts do.  The two projections may move together, so the
second component is transported back along reduction of the first projection. -/
theorem contextualSigma_of_head_reducts
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {pair : PureTm m}
    (firstNeutral : IsNeutral (.fst pair))
    (secondNeutral : IsNeutral (.snd pair))
    (pairReducts : ∀ target, Red pair target →
      contextualSigmaPred domain codomain environment target) :
    contextualSigmaPred domain codomain environment pair := by
  have firstCovered : domain.pred environment (.fst pair) := by
    apply domain.cr3 environmentRealized firstNeutral
    intro target step
    obtain ⟨pair', pairStep, rfl⟩ :=
      neutral_fst_projection_step firstNeutral step
    exact (pairReducts pair' pairStep).1
  have extendedRealized :=
    contextualPi_extended_realizes domain environmentRealized firstCovered
  refine ⟨firstCovered, ?_⟩
  apply codomain.cr3 extendedRealized secondNeutral
  intro target step
  obtain ⟨pair', pairStep, rfl⟩ :=
    neutral_snd_projection_step secondNeutral step
  have targetCovered := (pairReducts pair' pairStep).2
  have environmentSteps :
      SubRedStar
        (consSub (.fst pair) environment)
        (consSub (.fst pair') environment) :=
    SubRedStar.cons (red_to_redStar (.congFst pairStep))
      (SubRedStar.refl environment)
  exact (codomain.reduce_pred extendedRealized environmentSteps
    (.snd pair')).2 targetCovered

/-- Exact beta expansion for the dependent pair predicate. -/
theorem contextualSigma_beta_expansion
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {body : PureTm (m + 1)} {argument : PureTm m}
    (bodyAccessible : ReductionAccessible body)
    (argumentAccessible : ReductionAccessible argument)
    (contractumCovered :
      contextualSigmaPred domain codomain environment (inst0 argument body)) :
    contextualSigmaPred domain codomain environment
      (.app (.lam body) argument) := by
  induction bodyAccessible generalizing argument with
  | intro body bodySmaller bodyIH =>
      induction argumentAccessible with
      | intro argument argumentSmaller argumentIH =>
          apply contextualSigma_of_head_reducts domain codomain
            environmentRealized
          · trivial
          · trivial
          · intro target step
            cases step with
            | betaPi =>
                exact contractumCovered
            | congAppFun lambdaStep =>
                cases lambdaStep with
                | congLam bodyStep =>
                    have reducedContractum :=
                      contextualSigma_cr2_star domain codomain
                        environmentRealized contractumCovered
                        (redStar_inst0_body argument
                          (red_to_redStar bodyStep))
                    exact bodyIH _ bodyStep
                      (argumentAccessible :=
                        Acc.intro argument argumentSmaller)
                      (contractumCovered := reducedContractum)
            | congAppArg argumentStep =>
                have reducedContractum :=
                  contextualSigma_cr2_star domain codomain
                    environmentRealized contractumCovered
                    (redStar_inst0_argument body
                      (red_to_redStar argumentStep))
                exact argumentIH _ argumentStep
                  (contractumCovered := reducedContractum)

/-- Exact first-projection expansion for the dependent pair predicate. -/
theorem contextualSigma_fst_pair_expansion
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {first second : PureTm m}
    (firstCovered : contextualSigmaPred domain codomain environment first)
    (secondAccessible : ReductionAccessible second) :
    contextualSigmaPred domain codomain environment
      (.fst (.pair first second)) := by
  have firstAccessible :=
    contextualSigma_cr1 domain codomain environmentRealized firstCovered
  induction firstAccessible generalizing second with
  | intro first firstSmaller firstIH =>
      induction secondAccessible with
      | intro second secondSmaller secondIH =>
          apply contextualSigma_of_head_reducts domain codomain
            environmentRealized
          · trivial
          · trivial
          · intro target step
            cases step with
            | betaSigmaFst =>
                exact firstCovered
            | congFst pairStep =>
                cases pairStep with
                | congPairFst firstStep =>
                    have firstCovered' :=
                      contextualSigma_cr2 domain codomain
                        environmentRealized firstCovered firstStep
                    exact firstIH _ firstStep firstCovered'
                      (Acc.intro second secondSmaller)
                | congPairSnd secondStep =>
                    exact secondIH _ secondStep

/-- Exact second-projection expansion for the dependent pair predicate. -/
theorem contextualSigma_snd_pair_expansion
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {first second : PureTm m}
    (firstAccessible : ReductionAccessible first)
    (secondCovered : contextualSigmaPred domain codomain environment second) :
    contextualSigmaPred domain codomain environment
      (.snd (.pair first second)) := by
  have secondAccessible :=
    contextualSigma_cr1 domain codomain environmentRealized secondCovered
  induction firstAccessible generalizing second with
  | intro first firstSmaller firstIH =>
      induction secondAccessible with
      | intro second secondSmaller secondIH =>
          apply contextualSigma_of_head_reducts domain codomain
            environmentRealized
          · trivial
          · trivial
          · intro target step
            cases step with
            | betaSigmaSnd =>
                exact secondCovered
            | congSnd pairStep =>
                cases pairStep with
                | congPairFst firstStep =>
                    exact firstIH _ firstStep secondCovered
                      (Acc.intro second secondSmaller)
                | congPairSnd secondStep =>
                    have secondCovered' :=
                      contextualSigma_cr2 domain codomain
                        environmentRealized secondCovered secondStep
                    exact secondIH _ secondStep secondCovered'

/-! ## The packaged dependent pair type -/

/-- The contextual dependent pair type. -/
def ContextualCandidateType.sigma
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain)) :
    ContextualCandidateType context where
  pred := fun environment pair =>
    contextualSigmaPred domain codomain environment pair
  cr1 := by
    intro m environment pair realized covered
    exact contextualSigma_cr1 domain codomain realized covered
  cr2 := by
    intro m environment source target realized covered step
    exact contextualSigma_cr2 domain codomain realized covered step
  cr3 := by
    intro m environment pair realized neutral reducts
    exact contextualSigma_cr3 domain codomain realized neutral reducts
  rename_mem := by
    intro m k environment ρ pair realized covered
    exact contextualSigma_rename domain codomain realized covered ρ
  reduce_pred := by
    intro m source target sourceRealized steps pair
    exact contextualSigma_reduce_iff domain codomain sourceRealized steps pair
  beta_expansion := by
    intro m environment realized body argument bodyAccessible argumentAccessible
      contractumCovered
    exact contextualSigma_beta_expansion domain codomain realized
      bodyAccessible argumentAccessible contractumCovered
  fst_pair_expansion := by
    intro m environment realized first second firstCovered secondAccessible
    exact contextualSigma_fst_pair_expansion domain codomain realized
      firstCovered secondAccessible
  snd_pair_expansion := by
    intro m environment realized first second firstAccessible secondCovered
    exact contextualSigma_snd_pair_expansion domain codomain realized
      firstAccessible secondCovered

theorem ContextualCandidateType.sigma_pred
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    (environment : Sub n m) (pair : PureTm m) :
    (domain.sigma codomain).pred environment pair ↔
      contextualSigmaPred domain codomain environment pair :=
  Iff.rfl

/-- Dependent pair introduction.  The second component is initially known in
the environment selected by the written first component.  Exact projection
expansion and environment coherence transport it to the environment selected
by the pair's actual first projection. -/
theorem contextualSigma_pair_intro
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    (codomain : ContextualCandidateType (context.extendContextual domain))
    {environment : Sub n m} (environmentRealized : context.Realizes environment)
    {first second : PureTm m}
    (firstCovered : domain.pred environment first)
    (secondCovered : codomain.pred (consSub first environment) second) :
    contextualSigmaPred domain codomain environment (.pair first second) := by
  have firstAccessible := domain.cr1 environmentRealized firstCovered
  have firstExtendedRealized :=
    contextualPi_extended_realizes domain environmentRealized firstCovered
  have secondAccessible :=
    codomain.cr1 firstExtendedRealized secondCovered
  have projectedFirst :
      domain.pred environment (.fst (.pair first second)) :=
    domain.fst_pair_expansion environment environmentRealized
      firstCovered secondAccessible
  have projectedSecondAtFirst :
      codomain.pred (consSub first environment)
        (.snd (.pair first second)) :=
    codomain.snd_pair_expansion (consSub first environment)
      firstExtendedRealized firstAccessible secondCovered
  have projectedExtendedRealized :=
    contextualPi_extended_realizes domain environmentRealized projectedFirst
  have environmentSteps :
      SubRedStar
        (consSub (.fst (.pair first second)) environment)
        (consSub first environment) :=
    SubRedStar.cons
      (red_to_redStar (Red.betaSigmaFst first second))
      (SubRedStar.refl environment)
  exact ⟨projectedFirst,
    (codomain.reduce_pred projectedExtendedRealized environmentSteps
      (.snd (.pair first second))).2 projectedSecondAtFirst⟩

/-! ## Positive and negative canaries -/

def contextualNormalizingSigmaDomain :
    ContextualCandidateType CoherentCandidateContext.empty :=
  ContextualCandidateType.normalizing CoherentCandidateContext.empty

def contextualNormalizingSigmaCodomain :
    ContextualCandidateType
      (CoherentCandidateContext.empty.extendContextual
        contextualNormalizingSigmaDomain) :=
  ContextualCandidateType.normalizing _

def contextualNormalizingSigma :
    ContextualCandidateType CoherentCandidateContext.empty :=
  contextualNormalizingSigmaDomain.sigma contextualNormalizingSigmaCodomain

/-- A pair of normalizing components inhabits the normalizing dependent pair
candidate. -/
theorem contextual_u0_pair_in_normalizing_sigma :
    contextualNormalizingSigma.pred (ids : Sub 0 0)
      (.pair .u0 .u0) := by
  exact contextualSigma_pair_intro
    contextualNormalizingSigmaDomain contextualNormalizingSigmaCodomain
    trivial reductionAccessible_u0 reductionAccessible_u0

/-- A pair with a looping second component is rejected. -/
theorem contextual_omega_pair_not_in_normalizing_sigma :
    ¬ contextualNormalizingSigma.pred (ids : Sub 0 0)
      (.pair .u0 regularOmega) := by
  intro covered
  have projectionAccessible :
      ReductionAccessible (.snd (.pair (.u0 : PureTm 0) regularOmega)) :=
    covered.2
  have omegaAccessible :=
    projectionAccessible.of_red (Red.betaSigmaSnd .u0 regularOmega)
  exact omega_not_in_normalizing_candidate omegaAccessible

/-! ## Axiom audit -/

#print axioms renameEnvironment_consSub
#print axioms contextualSigma_cr1
#print axioms contextualSigma_cr2
#print axioms contextualSigma_cr3
#print axioms contextualSigma_rename
#print axioms contextualSigma_reduce_iff
#print axioms contextualSigma_beta_expansion
#print axioms contextualSigma_fst_pair_expansion
#print axioms contextualSigma_snd_pair_expansion
#print axioms ContextualCandidateType.sigma
#print axioms contextualSigma_pair_intro
#print axioms contextual_u0_pair_in_normalizing_sigma
#print axioms contextual_omega_pair_not_in_normalizing_sigma

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
