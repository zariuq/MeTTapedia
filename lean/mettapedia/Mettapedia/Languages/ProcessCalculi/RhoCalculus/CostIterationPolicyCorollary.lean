import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationElaboratedCarrier

/-!
# The empowering face of the cost-layer iteration obstruction, for rho

The cost-layer iteration package proves a family of negatives: compact erasure is not
faithful, normalization does not factor through it, and no commuting
compactification exists.  This module states the *positive* consequence
those negatives license, instantiated at rho's own witness.

The generic criterion lives in `GSLT.Core.GSLTConstructions`
(§ Policy descent through erasure):

* `policy_factors_iff_fiberInvariant` — a policy runs on compact syntax
  **iff** it is constant on erasure fibres;
* `exists_policy_not_factoring` — a nontrivial fibre plus two
  distinguishable values yields a policy no compact policy reproduces.

Here the fibre is the set of proof-relevant elaborations over one compact
open term.  Because `rhoCostLayerFor_not_all_elaborationFibersSubsingleton`
exhibits a term whose fibre has at least two inhabitants, that fibre
carries an observation which **no function of the compact term can
express** — a compact-only policy is constant on the fibre by
construction, since the compact term is fixed there.

Read operationally: retaining elaboration provenance is not bookkeeping,
it is strictly more control.  Cache keys, replay certificates, and
scheduler policies defined on compact syntax cannot see distinctions that
policies on the elaborated carrier can act on.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL

/-- A policy on one elaboration fibre that is *not* constant.  Any policy
that factors through compact erasure must be constant on a fibre, because
the compact term is fixed there; so this observation is available on the
elaborated carrier and unavailable on compact syntax. -/
theorem rhoCostLayerFor_exists_nonconstant_fiber_policy
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ∃ (targetFree : WellSorted.FreeTypeContext)
      (targetBound : List TypeExpr)
      (targetSort : LangSort configuration.source.costWholeLanguage)
      (term : ReflectiveWellSorted.OpenTerm
        configuration.source.costWholeReflectionProfile
        configuration.source.costWholeLanguage targetFree targetBound
        targetSort)
      (policy : CostOpenElaboration configuration.source term → Bool),
      ¬ ∃ value : Bool, ∀ elaboration, policy elaboration = value := by
  classical
  have notAll :=
    rhoCostLayerFor_not_all_elaborationFibersSubsingleton configuration
      representative
  -- A fibre that is not a subsingleton contains two distinct elaborations.
  simp only [CIGSLT.CostElaborationFibersSubsingleton, not_forall] at notAll
  obtain ⟨targetFree, targetBound, targetSort, term, notSub⟩ := notAll
  have twoDistinct :
      ∃ left right : CostOpenElaboration configuration.source term,
        left ≠ right := by
    by_contra hcon
    push Not at hcon
    exact notSub ⟨fun left right => hcon left right⟩
  obtain ⟨left, right, distinct⟩ := twoDistinct
  refine ⟨targetFree, targetBound, targetSort, term,
    fun elaboration => decide (elaboration = left), ?_⟩
  rintro ⟨value, constant⟩
  have atLeft : decide (left = left) = value := constant left
  have atRight : decide (right = left) = value := constant right
  rw [decide_eq_true_eq.mpr rfl] at atLeft
  subst atLeft
  exact distinct (of_decide_eq_true atRight).symm

/-- The same statement read as the intended slogan: compact syntax is not
a complete key for policies over rho's Cost elaborations. -/
theorem rhoCostLayerFor_compact_key_incomplete
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ ∀ (targetFree : WellSorted.FreeTypeContext)
        (targetBound : List TypeExpr)
        (targetSort : LangSort configuration.source.costWholeLanguage)
        (term : ReflectiveWellSorted.OpenTerm
          configuration.source.costWholeReflectionProfile
          configuration.source.costWholeLanguage targetFree targetBound
          targetSort)
        (policy : CostOpenElaboration configuration.source term → Bool),
        ∃ value : Bool, ∀ elaboration, policy elaboration = value := by
  intro everyPolicyConstant
  obtain ⟨targetFree, targetBound, targetSort, term, policy, nonconstant⟩ :=
    rhoCostLayerFor_exists_nonconstant_fiber_policy configuration representative
  exact nonconstant
    (everyPolicyConstant targetFree targetBound targetSort term policy)

/-! ## The cost-layer iteration boundary package, bundled

The five boundary facts stated once, so that sealing cost layer instantiates
the whole cost-layer iteration story with a single application rather than five.  Four
are the nonfactorization negatives; the fifth is the positive control
consequence proved above. -/

/-- **The cost-layer iteration boundary package for rho, laws-free part.**  For any cost layer
configuration with the empty-parallel witness: normalization does not
factor through compact erasure; compact erasure is not faithful; not
every elaboration fibre is a subsingleton; and some fibre policy is not
expressible on compact syntax.

The fifth boundary fact — that no proof-relevant second-layer normalizer
admits a universally commuting compactification — needs elaborated
normalization laws as an input and is packaged separately as
`rhoCostLayerIteration_boundary_package_withLaws`. -/
theorem rhoCostLayerIteration_boundary_package
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration) :
    ¬ configuration.source.CostNormalizationFactorsThroughCompactErasure ∧
      ¬ configuration.source.CostCompactErasureFaithful ∧
      ¬ configuration.source.CostElaborationFibersSubsingleton ∧
      (∃ (targetFree : WellSorted.FreeTypeContext)
        (targetBound : List TypeExpr)
        (targetSort : LangSort configuration.source.costWholeLanguage)
        (term : ReflectiveWellSorted.OpenTerm
          configuration.source.costWholeReflectionProfile
          configuration.source.costWholeLanguage targetFree targetBound
          targetSort)
        (policy : CostOpenElaboration configuration.source term → Bool),
        ¬ ∃ value : Bool, ∀ elaboration, policy elaboration = value) :=
  ⟨rhoCostLayerFor_not_normalizationFactorsThroughCompactErasure configuration
      representative,
    rhoCostLayerFor_not_costCompactErasureFaithful configuration representative,
    rhoCostLayerFor_not_all_elaborationFibersSubsingleton configuration
      representative,
    rhoCostLayerFor_exists_nonconstant_fiber_policy configuration
      representative⟩

/-- **The full cost-layer iteration boundary package**, adding the conjunct that requires
elaborated normalization laws: even a completed proof-relevant second-layer
normalizer admits no universally commuting compactification.  With the four
laws-free facts this is the complete boundary — obstruction and its positive
control consequence together. -/
theorem rhoCostLayerIteration_boundary_package_withLaws
    (configuration : CostIterationObstruction.RhoCostLayerConfiguration)
    (representative :
      CostIterationObstruction.RhoEmptyParallelSourceRepresentative
        configuration)
    (semanticLaws : Cost.ElaboratedSection.Laws configuration.source) :
    ¬ configuration.source.CostNormalizationFactorsThroughCompactErasure ∧
      ¬ configuration.source.CostCompactErasureFaithful ∧
      ¬ configuration.source.CostElaborationFibersSubsingleton ∧
      ¬ Cost.SemanticSection.ReferenceErasureSemiconj
          semanticLaws.toElaboratedSection ∧
      (∃ (targetFree : WellSorted.FreeTypeContext)
        (targetBound : List TypeExpr)
        (targetSort : LangSort configuration.source.costWholeLanguage)
        (term : ReflectiveWellSorted.OpenTerm
          configuration.source.costWholeReflectionProfile
          configuration.source.costWholeLanguage targetFree targetBound
          targetSort)
        (policy : CostOpenElaboration configuration.source term → Bool),
        ¬ ∃ value : Bool, ∀ elaboration, policy elaboration = value) :=
  ⟨rhoCostLayerFor_not_normalizationFactorsThroughCompactErasure configuration
      representative,
    rhoCostLayerFor_not_costCompactErasureFaithful configuration representative,
    rhoCostLayerFor_not_all_elaborationFibersSubsingleton configuration
      representative,
    rhoCostLayerFor_no_normalizationCommutingCompactification configuration
      representative semanticLaws,
    rhoCostLayerFor_exists_nonconstant_fiber_policy configuration
      representative⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
