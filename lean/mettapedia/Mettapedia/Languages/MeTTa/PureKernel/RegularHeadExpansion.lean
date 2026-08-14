import Mettapedia.Languages.MeTTa.PureKernel.RegularCandidateCoherence

/-!
# Exact head expansion for regular reducibility

Lambda introduction does not follow from neutral expansion: a beta redex is not
neutral.  Nor is arbitrary reverse reduction sound for strong normalization,
because an erasing redex may hide a looping argument.  This module proves the
exact expansion principles required by the beta and pair-projection rules.  Each
principle carries accessibility of every component whose internal reductions can
still be chosen before the head step.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## Accessibility transport -/

/-- Strong normalization is inherited by every finite reduct. -/
theorem ReductionAccessible.of_redStar {source target : PureTm n}
    (sourceAccessible : ReductionAccessible source)
    (steps : RedStar source target) : ReductionAccessible target := by
  induction steps with
  | refl => exact sourceAccessible
  | tail hxy hyz ih => exact ih.of_red hyz

/-- Reducing a lambda body reduces its instantiation by the same finite path. -/
theorem redStar_inst0_body {body targetBody : PureTm (n + 1)}
    (argument : PureTm n) (steps : RedStar body targetBody) :
    RedStar (inst0 argument body) (inst0 argument targetBody) := by
  induction steps with
  | refl => exact RedStar.refl _
  | tail hxy hyz ih =>
      exact RedStar.tail ih (red_subst hyz (subst0 argument))

/-- Reducing the instantiating argument reduces every occurrence substituted
into a body.  A single source step may become several congruence steps when the
variable occurs more than once, hence the multi-step conclusion. -/
theorem redStar_inst0_argument {argument targetArgument : PureTm n}
    (body : PureTm (n + 1)) (steps : RedStar argument targetArgument) :
    RedStar (inst0 argument body) (inst0 targetArgument body) := by
  apply SubRedStar.subst
  intro index
  refine Fin.cases ?_ ?_ index
  · exact steps
  · intro preceding
    exact RedStar.refl (.var preceding)

/-! ## Exact constructor expansions -/

/-- Exact beta expansion for strong normalization.  Accessibility of the body
and argument is essential because either may reduce before the beta step. -/
theorem reductionAccessible_beta_expansion
    {body : PureTm (n + 1)} {argument : PureTm n}
    (bodyAccessible : ReductionAccessible body)
    (argumentAccessible : ReductionAccessible argument)
    (contractumAccessible : ReductionAccessible (inst0 argument body)) :
    ReductionAccessible (.app (.lam body) argument) := by
  induction bodyAccessible generalizing argument with
  | intro body bodySmaller bodyIH =>
      induction argumentAccessible with
      | intro argument argumentSmaller argumentIH =>
          constructor
          intro target step
          cases step with
          | betaPi => exact contractumAccessible
          | congAppFun functionStep =>
              cases functionStep with
              | congLam bodyStep =>
                  exact bodyIH _ bodyStep
                    (Acc.intro argument argumentSmaller)
                    (contractumAccessible.of_redStar
                      (redStar_inst0_body argument
                        (red_to_redStar bodyStep)))
          | congAppArg argumentStep =>
              exact argumentIH _ argumentStep
                (contractumAccessible.of_redStar
                  (redStar_inst0_argument body
                    (red_to_redStar argumentStep)))

/-- Exact first-projection expansion for strong normalization. -/
theorem reductionAccessible_fst_pair_expansion
    {first second : PureTm n}
    (firstAccessible : ReductionAccessible first)
    (secondAccessible : ReductionAccessible second) :
    ReductionAccessible (.fst (.pair first second)) := by
  induction firstAccessible generalizing second with
  | intro first firstSmaller firstIH =>
      induction secondAccessible with
      | intro second secondSmaller secondIH =>
          constructor
          intro target step
          cases step with
          | betaSigmaFst => exact Acc.intro first firstSmaller
          | congFst pairStep =>
              cases pairStep with
              | congPairFst firstStep =>
                  exact firstIH _ firstStep (Acc.intro second secondSmaller)
              | congPairSnd secondStep =>
                  exact secondIH _ secondStep

/-- Exact second-projection expansion for strong normalization. -/
theorem reductionAccessible_snd_pair_expansion
    {first second : PureTm n}
    (firstAccessible : ReductionAccessible first)
    (secondAccessible : ReductionAccessible second) :
    ReductionAccessible (.snd (.pair first second)) := by
  induction firstAccessible generalizing second with
  | intro first firstSmaller firstIH =>
      induction secondAccessible with
      | intro second secondSmaller secondIH =>
          constructor
          intro target step
          cases step with
          | betaSigmaSnd => exact Acc.intro second secondSmaller
          | congSnd pairStep =>
              cases pairStep with
              | congPairFst firstStep =>
                  exact firstIH _ firstStep (Acc.intro second secondSmaller)
              | congPairSnd secondStep =>
                  exact secondIH _ secondStep

/-! ## The candidate capability actually consumed by introductions -/

/-- A reducibility candidate equipped with the three computational head
expansions used by the regular Pure term constructors.  This is deliberately
not arbitrary backward closure. -/
structure HeadExpansionCandidate (n : Nat) extends ReductionCandidate n where
  beta_expansion : ∀ {body : PureTm (n + 1)} {argument : PureTm n},
    ReductionAccessible body →
      ReductionAccessible argument →
        pred (inst0 argument body) →
          pred (.app (.lam body) argument)
  fst_pair_expansion : ∀ {first second : PureTm n},
    pred first → ReductionAccessible second → pred (.fst (.pair first second))
  snd_pair_expansion : ∀ {first second : PureTm n},
    ReductionAccessible first → pred second → pred (.snd (.pair first second))

namespace HeadExpansionCandidate

/-- Strong normalization carries exactly the required head-expansion
capability. -/
def normalizing (n : Nat) : HeadExpansionCandidate n where
  toReductionCandidate := ReductionCandidate.normalizing n
  beta_expansion := fun bodyAccessible argumentAccessible contractumAccessible =>
    reductionAccessible_beta_expansion bodyAccessible argumentAccessible
      contractumAccessible
  fst_pair_expansion := fun firstAccessible secondAccessible =>
    reductionAccessible_fst_pair_expansion firstAccessible secondAccessible
  snd_pair_expansion := fun firstAccessible secondAccessible =>
    reductionAccessible_snd_pair_expansion firstAccessible secondAccessible

end HeadExpansionCandidate

/-! ## Head expansion over coherent semantic contexts -/

/-- A reduction-coherent semantic type whose fibres have the computational
head expansions required by term introduction.  The laws are required only on
realizing environments; no semantic content is assigned to malformed ones. -/
structure CoherentHeadExpansionType {n : Nat}
    (context : CoherentCandidateContext n)
    extends CoherentCandidateType context where
  beta_expansion : ∀ {m : Nat} (environment : Sub n m),
    context.Realizes environment →
      ∀ {body : PureTm (m + 1)} {argument : PureTm m},
        ReductionAccessible body →
          ReductionAccessible argument →
            (candidate environment).pred (inst0 argument body) →
              (candidate environment).pred (.app (.lam body) argument)
  fst_pair_expansion : ∀ {m : Nat} (environment : Sub n m),
    context.Realizes environment →
      ∀ {first second : PureTm m},
        (candidate environment).pred first →
          ReductionAccessible second →
            (candidate environment).pred (.fst (.pair first second))
  snd_pair_expansion : ∀ {m : Nat} (environment : Sub n m),
    context.Realizes environment →
      ∀ {first second : PureTm m},
        ReductionAccessible first →
          (candidate environment).pred second →
            (candidate environment).pred (.snd (.pair first second))

namespace CoherentHeadExpansionType

/-- The constant strong-normalization type carries coherent head expansion. -/
def normalizing (context : CoherentCandidateContext n) :
    CoherentHeadExpansionType context where
  toCoherentCandidateType := CoherentCandidateType.normalizing context
  beta_expansion := by
    intro m environment realized body argument bodyAccessible argumentAccessible
      contractumAccessible
    exact reductionAccessible_beta_expansion bodyAccessible argumentAccessible
      contractumAccessible
  fst_pair_expansion := by
    intro m environment realized first second firstAccessible secondAccessible
    exact reductionAccessible_fst_pair_expansion firstAccessible secondAccessible
  snd_pair_expansion := by
    intro m environment realized first second firstAccessible secondAccessible
    exact reductionAccessible_snd_pair_expansion firstAccessible secondAccessible

/-- Head expansion is stable under context extension/weakening. -/
def weaken {context : CoherentCandidateContext n}
    (type : CoherentHeadExpansionType context) :
    CoherentHeadExpansionType (context.extend type.toCoherentCandidateType) where
  toCoherentCandidateType := type.toCoherentCandidateType.weaken
  beta_expansion := by
    intro m environment realized body argument bodyAccessible argumentAccessible
      contractumCovered
    exact type.beta_expansion (tailSub environment) realized.1
      bodyAccessible argumentAccessible contractumCovered
  fst_pair_expansion := by
    intro m environment realized first second firstCovered secondAccessible
    exact type.fst_pair_expansion (tailSub environment) realized.1
      firstCovered secondAccessible
  snd_pair_expansion := by
    intro m environment realized first second firstAccessible secondCovered
    exact type.snd_pair_expansion (tailSub environment) realized.1
      firstAccessible secondCovered

/-- Head expansion is stable under semantic reindexing. -/
def reindex {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {σ : Sub n m}
    (type : CoherentHeadExpansionType source)
    (map : CandidateSubstitution source.toCandidateContext
      target.toCandidateContext σ) :
    CoherentHeadExpansionType target where
  toCoherentCandidateType := type.toCoherentCandidateType.reindex map
  beta_expansion := by
    intro k environment realized body argument bodyAccessible argumentAccessible
      contractumCovered
    exact type.beta_expansion (compSub environment σ)
      (map.maps_realizers environment realized)
      bodyAccessible argumentAccessible contractumCovered
  fst_pair_expansion := by
    intro k environment realized first second firstCovered secondAccessible
    exact type.fst_pair_expansion (compSub environment σ)
      (map.maps_realizers environment realized)
      firstCovered secondAccessible
  snd_pair_expansion := by
    intro k environment realized first second firstAccessible secondCovered
    exact type.snd_pair_expansion (compSub environment σ)
      (map.maps_realizers environment realized)
      firstAccessible secondCovered

end CoherentHeadExpansionType

/-! ## Negative control: arbitrary reverse reduction is unsound -/

/-- An erasing beta redex whose contractum is `U0` but whose argument loops. -/
def regularErasingOmega : PureTm 0 :=
  .app (.lam .u0) regularOmega

theorem regularErasingOmega_reduces_to_u0 :
    Red regularErasingOmega (.u0 : PureTm 0) := by
  simpa [regularErasingOmega, inst0, subst, subst0] using
    (Red.betaPi (.u0 : PureTm 1) regularOmega)

theorem regularErasingOmega_not_accessible :
    ¬ ReductionAccessible regularErasingOmega := by
  intro accessible
  exact omega_not_in_normalizing_candidate
    (reductionAccessible_app_right accessible)

/-- A strongly normalizing reduct does not make its source strongly normalizing.
The component-accessibility premises of exact beta expansion cannot be dropped. -/
theorem arbitrary_reverse_reduction_is_unsound :
    Red regularErasingOmega (.u0 : PureTm 0) ∧
      ReductionAccessible (.u0 : PureTm 0) ∧
        ¬ ReductionAccessible regularErasingOmega :=
  ⟨regularErasingOmega_reduces_to_u0,
    reductionAccessible_u0,
    regularErasingOmega_not_accessible⟩

/-! ## Axiom audit -/

#print axioms ReductionAccessible.of_redStar
#print axioms redStar_inst0_body
#print axioms redStar_inst0_argument
#print axioms reductionAccessible_beta_expansion
#print axioms reductionAccessible_fst_pair_expansion
#print axioms reductionAccessible_snd_pair_expansion
#print axioms HeadExpansionCandidate.normalizing
#print axioms CoherentHeadExpansionType.normalizing
#print axioms CoherentHeadExpansionType.weaken
#print axioms CoherentHeadExpansionType.reindex
#print axioms regularErasingOmega_reduces_to_u0
#print axioms arbitrary_reverse_reduction_is_unsound

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
