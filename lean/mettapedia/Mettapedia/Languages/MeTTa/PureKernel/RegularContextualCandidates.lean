import Mettapedia.Languages.MeTTa.PureKernel.RegularHeadExpansion

/-!
# Reducibility over realized contexts

A dependent semantic type is used only at substitutions which realize its
context.  Requiring a complete reduction candidate at every malformed
environment is therefore stronger than the fundamental lemma needs, and blocks
genuinely dependent candidate constructions whose closure proofs consume the
realization hypothesis.

This module packages candidate laws directly over realized environments.  Each
realized fibre recovers an ordinary reduction candidate with the exact
constructor head expansions.  Context extension, weakening, and reindexing are
then proved at this honest boundary.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## Contextual candidates -/

/-- A semantic type whose candidate laws are stated exactly where its context
has meaning: over realizing environments. -/
structure ContextualCandidateType {n : Nat}
    (context : CoherentCandidateContext n) where
  pred : {m : Nat} → Sub n m → PureTm m → Prop
  cr1 : ∀ {m : Nat} {environment : Sub n m} {term : PureTm m},
    context.Realizes environment →
      pred environment term →
        ReductionAccessible term
  cr2 : ∀ {m : Nat} {environment : Sub n m}
      {source target : PureTm m},
    context.Realizes environment →
      pred environment source →
        Red source target →
          pred environment target
  cr3 : ∀ {m : Nat} {environment : Sub n m} {term : PureTm m},
    context.Realizes environment →
      IsNeutral term →
        (∀ target, Red term target → pred environment target) →
          pred environment term
  rename_mem : ∀ {m k : Nat} (environment : Sub n m) (ρ : Ren m k)
      {term : PureTm m},
    context.Realizes environment →
      pred environment term →
        pred (fun index => rename ρ (environment index)) (rename ρ term)
  reduce_pred : ∀ {m : Nat} {source target : Sub n m},
    context.Realizes source →
      SubRedStar source target →
        ∀ term : PureTm m, pred source term ↔ pred target term
  beta_expansion : ∀ {m : Nat} (environment : Sub n m),
    context.Realizes environment →
      ∀ {body : PureTm (m + 1)} {argument : PureTm m},
        ReductionAccessible body →
          ReductionAccessible argument →
            pred environment (inst0 argument body) →
              pred environment (.app (.lam body) argument)
  fst_pair_expansion : ∀ {m : Nat} (environment : Sub n m),
    context.Realizes environment →
      ∀ {first second : PureTm m},
        pred environment first →
          ReductionAccessible second →
            pred environment (.fst (.pair first second))
  snd_pair_expansion : ∀ {m : Nat} (environment : Sub n m),
    context.Realizes environment →
      ∀ {first second : PureTm m},
        ReductionAccessible first →
          pred environment second →
            pred environment (.snd (.pair first second))

namespace ContextualCandidateType

/-- Every coherent head-expansion type embeds into the realized-context
interface.  This preserves the preceding development while permitting later
dependent constructions to use realization hypotheses in their candidate
laws. -/
def ofCoherent {context : CoherentCandidateContext n}
    (type : CoherentHeadExpansionType context) :
    ContextualCandidateType context where
  pred := fun environment term => (type.candidate environment).pred term
  cr1 := fun _ covered => (type.candidate _).cr1 covered
  cr2 := fun _ covered step => (type.candidate _).cr2 covered step
  cr3 := fun _ neutral reducts => (type.candidate _).cr3 neutral reducts
  rename_mem := type.rename_mem
  reduce_pred := type.reduce_candidate
  beta_expansion := type.beta_expansion
  fst_pair_expansion := type.fst_pair_expansion
  snd_pair_expansion := type.snd_pair_expansion

/-- A realized environment selects an ordinary candidate equipped with exact
head expansion.  The realization proof supplies laws, not membership data. -/
def fibre {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context)
    (environment : Sub n m) (realized : context.Realizes environment) :
    HeadExpansionCandidate m where
  pred := type.pred environment
  cr1 := type.cr1 realized
  cr2 := type.cr2 realized
  cr3 := type.cr3 realized
  beta_expansion := type.beta_expansion environment realized
  fst_pair_expansion := type.fst_pair_expansion environment realized
  snd_pair_expansion := type.snd_pair_expansion environment realized

/-- Strong normalization is a contextual type over every coherent context. -/
def normalizing (context : CoherentCandidateContext n) :
    ContextualCandidateType context where
  pred := fun _ term => ReductionAccessible term
  cr1 := fun _ covered => covered
  cr2 := fun _ covered step => covered.of_red step
  cr3 := fun _ _ reducts => Acc.intro _ reducts
  rename_mem := by
    intro m k environment ρ term realized covered
    exact reductionAccessible_rename ρ covered
  reduce_pred := fun _ _ _ => Iff.rfl
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

/-- The direct contextual normalizing type agrees pointwise with the embedded
coherent normalizing type. -/
theorem ofCoherent_normalizing_pred
    (context : CoherentCandidateContext n) (environment : Sub n m)
    (term : PureTm m) :
    (ofCoherent (CoherentHeadExpansionType.normalizing context)).pred
        environment term ↔
      (normalizing context).pred environment term :=
  Iff.rfl

end ContextualCandidateType

/-! ## Context extension at the realized boundary -/

namespace CoherentCandidateContext

/-- Extend a coherent context by a contextual type.  No candidate is requested
for a malformed tail environment. -/
def extendContextual (context : CoherentCandidateContext n)
    (type : ContextualCandidateType context) :
    CoherentCandidateContext (n + 1) where
  toCandidateContext :=
    { Realizes := fun environment =>
        context.Realizes (tailSub environment) ∧
          type.pred (tailSub environment) (environment 0)
      identity_realizes := by
        constructor
        · rw [tailSub_ids]
          exact context.rename_realizes ids wk context.identity_realizes
        · apply type.cr3
            (context.rename_realizes ids wk context.identity_realizes)
            (neutral_var 0)
          intro target step
          cases step
      rename_realizes := by
        intro m k environment ρ realized
        constructor
        · exact context.rename_realizes (tailSub environment) ρ realized.1
        · exact type.rename_mem (tailSub environment) ρ realized.1 realized.2 }
  reduce_realizes := by
    intro m source target sourceRealized steps
    have targetTailRealized :=
      context.reduce_realizes sourceRealized.1 steps.tail
    constructor
    · exact targetTailRealized
    · have reducedHead :
          type.pred (tailSub source) (target 0) :=
        (type.fibre (tailSub source) sourceRealized.1).cr2_star
          sourceRealized.2 (steps 0)
      exact (type.reduce_pred sourceRealized.1 steps.tail (target 0)).1
        reducedHead

end CoherentCandidateContext

/-! ## Weakening, reindexing, and term realization -/

namespace ContextualCandidateType

/-- Reuse a contextual type under the extension it generates. -/
def weaken {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context) :
    ContextualCandidateType (context.extendContextual type) where
  pred := fun environment term => type.pred (tailSub environment) term
  cr1 := fun realized => type.cr1 realized.1
  cr2 := fun realized => type.cr2 realized.1
  cr3 := fun realized => type.cr3 realized.1
  rename_mem := by
    intro m k environment ρ term realized covered
    exact type.rename_mem (tailSub environment) ρ realized.1 covered
  reduce_pred := by
    intro m source target sourceRealized steps term
    exact type.reduce_pred sourceRealized.1 steps.tail term
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

/-- Pull a contextual type back along a candidate-respecting substitution. -/
def reindex {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {σ : Sub n m}
    (type : ContextualCandidateType source)
    (map : CandidateSubstitution source.toCandidateContext
      target.toCandidateContext σ) :
    ContextualCandidateType target where
  pred := fun environment term =>
    type.pred (compSub environment σ) term
  cr1 := by
    intro k environment term realized covered
    exact type.cr1 (map.maps_realizers environment realized) covered
  cr2 := by
    intro k environment first last realized covered step
    exact type.cr2 (map.maps_realizers environment realized) covered step
  cr3 := by
    intro k environment term realized neutral reducts
    exact type.cr3 (map.maps_realizers environment realized) neutral reducts
  rename_mem := by
    intro k l environment ρ term realized covered
    have transported := type.rename_mem (compSub environment σ) ρ
      (map.maps_realizers environment realized) covered
    rw [rename_compSub] at transported
    exact transported
  reduce_pred := by
    intro k first last firstRealized steps term
    exact type.reduce_pred
      (map.maps_realizers first firstRealized)
      (steps.compSub σ) term
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

/-- A term realizes a contextual type when every realizing substitution maps it
into the corresponding contextual predicate. -/
def RealizesTerm {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context) (term : PureTm n) : Prop :=
  ∀ {m : Nat} (environment : Sub n m), context.Realizes environment →
    type.pred environment (subst environment term)

/-- The newest variable realizes the weakened contextual type. -/
theorem head_realizes {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context) :
    type.weaken.RealizesTerm (.var 0) := by
  intro m environment realized
  exact realized.2

end ContextualCandidateType

/-! ## Positive and negative canaries -/

def contextualEmptyNormalizingType :
    ContextualCandidateType CoherentCandidateContext.empty :=
  ContextualCandidateType.normalizing CoherentCandidateContext.empty

def contextualOneVariableContext : CoherentCandidateContext 1 :=
  CoherentCandidateContext.empty.extendContextual
    contextualEmptyNormalizingType

/-- The head variable is realized through contextual extension. -/
theorem contextual_head_realizes :
    contextualEmptyNormalizingType.weaken.RealizesTerm (.var 0) :=
  ContextualCandidateType.head_realizes contextualEmptyNormalizingType

/-- Restricting candidate laws to realized environments does not weaken the
logical relation: omega is still rejected in the empty context. -/
theorem omega_not_realized_in_contextual_empty :
    ¬ contextualEmptyNormalizingType.RealizesTerm regularOmega := by
  intro realized
  have covered := realized (ids : Sub 0 0) trivial
  exact omega_not_in_normalizing_candidate covered

/-! ## Axiom audit -/

#print axioms ContextualCandidateType.fibre
#print axioms ContextualCandidateType.ofCoherent
#print axioms ContextualCandidateType.normalizing
#print axioms ContextualCandidateType.ofCoherent_normalizing_pred
#print axioms CoherentCandidateContext.extendContextual
#print axioms ContextualCandidateType.weaken
#print axioms ContextualCandidateType.reindex
#print axioms ContextualCandidateType.head_realizes
#print axioms contextual_head_realizes
#print axioms omega_not_realized_in_contextual_empty

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
