import Mettapedia.Languages.MeTTa.PureKernel.RegularCandidateSemantics

/-!
# Reduction-coherent semantic environments

Dependent candidates are indexed by environments.  Reducing an argument changes
the environment which selects the codomain candidate, so renaming stability alone
is insufficient for the fundamental lemma.  This module isolates the missing
law: pointwise reduction of an environment preserves context realization and
does not change membership in the candidate selected by a semantic type.

The construction is deliberately stronger than the preceding context layer but
still stops before interpreting syntactic type formers.  In particular, no
constant-candidate shortcut is presented as dependent normalization.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## Pointwise reduction of environments -/

/-- Every image of the first substitution reduces to the corresponding image
of the second. -/
def SubRedStar (source target : Sub n m) : Prop :=
  ∀ index, RedStar (source index) (target index)

namespace SubRedStar

theorem refl (environment : Sub n m) :
    SubRedStar environment environment :=
  fun _ => RedStar.refl _

theorem trans {first middle last : Sub n m}
    (firstToMiddle : SubRedStar first middle)
    (middleToLast : SubRedStar middle last) :
    SubRedStar first last :=
  fun index => RedStar.trans (firstToMiddle index) (middleToLast index)

/-- Multi-step reduction is preserved by variable renaming. -/
theorem rename (ρ : Ren m k) {source target : PureTm m}
    (steps : RedStar source target) :
    RedStar (Renaming.rename ρ source) (Renaming.rename ρ target) := by
  induction steps with
  | refl => exact RedStar.refl _
  | tail hxy hyz ih => exact RedStar.tail ih (red_rename hyz ρ)

/-- Lifting pointwise-related substitutions preserves the relation under a
binder. -/
theorem lift {source target : Sub n m}
    (steps : SubRedStar source target) :
    SubRedStar (liftSub source) (liftSub target) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact RedStar.refl _
  · intro preceding
    exact rename wk (steps preceding)

/-- Pointwise environment reduction acts functorially on every term. -/
theorem subst {source target : Sub n m}
    (steps : SubRedStar source target) :
    ∀ term : PureTm n, RedStar (Substitution.subst source term)
      (Substitution.subst target term) := by
  intro term
  induction term generalizing m with
  | var index => exact steps index
  | const name => exact RedStar.refl _
  | u0 => exact RedStar.refl _
  | u1 => exact RedStar.refl _
  | pi domain codomain ihDomain ihCodomain =>
      exact RedStar.trans
        (RedStar.congPiDom (ihDomain steps))
        (RedStar.congPiCod (ihCodomain steps.lift))
  | sigma domain codomain ihDomain ihCodomain =>
      exact RedStar.trans
        (RedStar.congSigmaDom (ihDomain steps))
        (RedStar.congSigmaCod (ihCodomain steps.lift))
  | id type left right ihType ihLeft ihRight =>
      exact RedStar.trans
        (RedStar.trans
          (RedStar.map (fun step => Red.congIdTy step) (ihType steps))
          (RedStar.map (fun step => Red.congIdLeft step) (ihLeft steps)))
        (RedStar.map (fun step => Red.congIdRight step) (ihRight steps))
  | lam body ihBody =>
      exact RedStar.congLam (ihBody steps.lift)
  | app function argument ihFunction ihArgument =>
      exact RedStar.trans
        (RedStar.congAppFun (ihFunction steps))
        (RedStar.congAppArg (ihArgument steps))
  | pair first second ihFirst ihSecond =>
      exact RedStar.trans
        (RedStar.congPairFst (ihFirst steps))
        (RedStar.congPairSnd (ihSecond steps))
  | fst pair ihPair => exact RedStar.congFst (ihPair steps)
  | snd pair ihPair => exact RedStar.congSnd (ihPair steps)
  | refl term ihTerm => exact RedStar.congRefl (ihTerm steps)

/-- Composing a pointwise reduction with a fixed source substitution preserves
pointwise reduction. -/
theorem compSub {source target : Sub m k} (steps : SubRedStar source target)
    (earlier : Sub n m) :
    SubRedStar (PresentationBoundary.compSub source earlier)
      (PresentationBoundary.compSub target earlier) :=
  fun index => steps.subst (earlier index)

/-- Taking the tail of an environment preserves pointwise reduction. -/
theorem tail {source target : Sub (n + 1) m}
    (steps : SubRedStar source target) :
    SubRedStar (tailSub source) (tailSub target) :=
  fun index => steps index.succ

end SubRedStar

namespace ReductionCandidate

/-- Candidate membership is closed under every finite reduction sequence. -/
theorem cr2_star (candidate : ReductionCandidate n)
    {source target : PureTm n} (covered : candidate.pred source)
    (steps : RedStar source target) : candidate.pred target := by
  induction steps with
  | refl => exact covered
  | tail hxy hyz ih => exact candidate.cr2 ih hyz

end ReductionCandidate

/-! ## Coherent contexts and types -/

/-- A semantic context whose realization relation survives pointwise reduction
of the realizing environment. -/
structure CoherentCandidateContext (n : Nat) extends CandidateContext n where
  reduce_realizes : ∀ {m : Nat} {source target : Sub n m},
    toCandidateContext.Realizes source →
      SubRedStar source target →
        toCandidateContext.Realizes target

namespace CoherentCandidateContext

def empty : CoherentCandidateContext 0 where
  toCandidateContext := CandidateContext.empty
  reduce_realizes := fun _ _ => trivial

end CoherentCandidateContext

/-- A semantic type whose selected candidate is invariant under reduction of
the environment index.  The equivalence is the coherence consumed by dependent
codomains when their arguments reduce. -/
structure CoherentCandidateType {n : Nat}
    (context : CoherentCandidateContext n)
    extends CandidateType context.toCandidateContext where
  reduce_candidate : ∀ {m : Nat} {source target : Sub n m},
    context.Realizes source →
      SubRedStar source target →
        ∀ term : PureTm m,
          (candidate source).pred term ↔ (candidate target).pred term

namespace CoherentCandidateType

/-- Strong normalization is a reduction-coherent constant semantic type. -/
def normalizing (context : CoherentCandidateContext n) :
    CoherentCandidateType context where
  toCandidateType := CandidateType.normalizing context.toCandidateContext
  reduce_candidate := fun _ _ _ => Iff.rfl

/-- The strict `U0`-avoiding candidate is likewise coherent when used
constantly over a context. -/
def avoidingU0 (context : CoherentCandidateContext n) :
    CoherentCandidateType context where
  toCandidateType := CandidateType.avoidingU0 context.toCandidateContext
  reduce_candidate := fun _ _ _ => Iff.rfl

end CoherentCandidateType

namespace CoherentCandidateContext

/-- Coherent dependent context extension. -/
def extend (context : CoherentCandidateContext n)
    (type : CoherentCandidateType context) :
    CoherentCandidateContext (n + 1) where
  toCandidateContext := context.toCandidateContext.extend type.toCandidateType
  reduce_realizes := by
    intro m source target sourceRealized steps
    have targetTailRealized := context.reduce_realizes sourceRealized.1 steps.tail
    constructor
    · exact targetTailRealized
    · have reducedHead :
          (type.candidate (tailSub source)).pred (target 0) :=
        (type.candidate (tailSub source)).cr2_star sourceRealized.2 (steps 0)
      exact (type.reduce_candidate sourceRealized.1 steps.tail (target 0)).1
        reducedHead

end CoherentCandidateContext

namespace CoherentCandidateType

/-- Weakening preserves reduction coherence. -/
def weaken {context : CoherentCandidateContext n}
    (type : CoherentCandidateType context) :
    CoherentCandidateType (context.extend type) where
  toCandidateType := type.toCandidateType.weaken
  reduce_candidate := by
    intro m source target sourceRealized steps term
    exact type.reduce_candidate sourceRealized.1 steps.tail term

/-- The newest variable realizes the coherently weakened type. -/
theorem head_realizes {context : CoherentCandidateContext n}
    (type : CoherentCandidateType context) :
    type.weaken.toCandidateType.RealizesTerm (.var 0) :=
  CandidateType.head_realizes type.toCandidateType

/-- Pullback along a candidate-respecting substitution preserves reduction
coherence. -/
def reindex {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {σ : Sub n m}
    (type : CoherentCandidateType source)
    (map : CandidateSubstitution source.toCandidateContext
      target.toCandidateContext σ) :
    CoherentCandidateType target where
  toCandidateType := type.toCandidateType.reindex map
  reduce_candidate := by
    intro k first last firstRealized steps term
    have sourceRealized := map.maps_realizers first firstRealized
    exact type.reduce_candidate sourceRealized (steps.compSub σ) term

end CoherentCandidateType

/-! ## Positive and negative canaries -/

def coherentEmptyNormalizingType :
    CoherentCandidateType CoherentCandidateContext.empty :=
  CoherentCandidateType.normalizing CoherentCandidateContext.empty

def coherentOneVariableContext : CoherentCandidateContext 1 :=
  CoherentCandidateContext.empty.extend coherentEmptyNormalizingType

/-- Context extension genuinely transports a reducible head from source to
target while preserving realization. -/
theorem coherent_extension_reduces_head
    {source target : PureTm 0}
    (sourceAccessible : ReductionAccessible source)
    (steps : RedStar source target) :
    coherentOneVariableContext.Realizes (consSub target ids) := by
  have sourceRealized :
      coherentOneVariableContext.Realizes (consSub source ids) := by
    constructor
    · trivial
    · exact sourceAccessible
  apply coherentOneVariableContext.reduce_realizes sourceRealized
  intro index
  refine Fin.cases ?_ ?_ index
  · exact steps
  · intro impossible
    exact Fin.elim0 impossible

/-- Coherence does not weaken the logical relation: the empty normalizing type
still rejects the looping omega term. -/
theorem omega_not_in_coherent_empty_normalizing :
    ¬ coherentEmptyNormalizingType.toCandidateType.RealizesTerm regularOmega :=
  omega_not_realized_in_empty_normalizing

/-! ## Axiom audit -/

#print axioms SubRedStar.subst
#print axioms SubRedStar.compSub
#print axioms ReductionCandidate.cr2_star
#print axioms CoherentCandidateContext.extend
#print axioms CoherentCandidateType.weaken
#print axioms CoherentCandidateType.reindex
#print axioms coherent_extension_reduces_head
#print axioms omega_not_in_coherent_empty_normalizing

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
