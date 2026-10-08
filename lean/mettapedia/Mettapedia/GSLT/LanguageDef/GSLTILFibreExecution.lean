import Mettapedia.GSLT.LanguageDef.GSLTIL
import Mettapedia.OSLF.MeTTaIL.PatternCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Set.Finite.Basic

/-!
# Qualified fibre execution for GSLT-ML

A finite answer list for each query does not require a finite global state
space. This module interprets the existing command rules with one selected
fibre query and no transport entries. A separate specification connects each
computed answer to an actual edge of the source GSLT. Both directions of that
specification yield local coverage, arbitrary finite-path reflection and
agreement of normal forms. Target steps cannot leave the encoded fibre.

The command syntax, rewrite rules and relation interface are unchanged.
This is an execution specialization, not another command calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

/-- Structural encoding of the command wrapper, independent of how the
fibre's state was produced. -/
def atPatternCode (stage : Pattern) (stateCode : Nat) : Nat :=
  Nat.pair 2 (Nat.pair (Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode "at")
    (Nat.succ (Nat.pair (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode stage)
      (Nat.succ (Nat.pair stateCode 0)))))

theorem atPatternCode_eq (stage state : Pattern) :
    atPatternCode stage (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode state) =
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (atPattern stage state) := rfl

theorem atPatternCode_primrec (stage : Pattern) : Primrec (atPatternCode stage) :=
  Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp
      (Primrec.const (Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode "at"))
      (Primrec.succ.comp (Primrec₂.natPair.comp
        (Primrec.const (Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode stage))
        (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const 0))))))

def relations (stage : Pattern) (successors : Pattern → List Pattern) : RelationEnv :=
  queryEnv (fun queried state => if queried = stage then successors state else [])
    (fun _ _ _ _ _ => [])

def theory (stage : Pattern) (successors : Pattern → List Pattern) : GSLT :=
  executionTheory (relations stage successors)

theorem equiv_iff_eq (stage : Pattern) (successors : Pattern → List Pattern)
    (left right : Pattern) :
    (theory stage successors).Equiv left right ↔ left = right :=
  Mettapedia.GSLT.LanguageDef.EquationSemantics.equationEquiv_iff_eq_of_no_generators
    (by rfl) left right

theorem at_injective (stage : Pattern) : Function.Injective (atPattern stage) := by
  intro left right same
  simpa [atPattern] using same

/-- Every outgoing command answer has the same stage and an actual query
answer. Reflection quantifies over all target patterns. -/
theorem step_at_iff (stage : Pattern) (successors : Pattern → List Pattern)
    (state target : Pattern) :
    (theory stage successors).Step (atPattern stage state) target ↔
      ∃ next ∈ successors state, target = atPattern stage next := by
  change (executionTheory (relations stage successors)).Step (atPattern stage state) target ↔ _
  rw [executionTheory_step_iff_mem_executor]
  change target ∈ rewriteStepWithPremisesUsing
    (queryEnv _ _) language (atPattern stage state) ↔ _
  rw [execute_at_using]
  simp [List.mem_map, eq_comm]

/-- Unsupported stages remain inert rather than acquiring another fibre's
transition or a fallback host result. -/
theorem other_stage_normal (stage other : Pattern) (successors : Pattern → List Pattern)
    (different : other ≠ stage) (state : Pattern) :
    (theory stage successors).IsNormalForm (atPattern other state) := by
  rintro ⟨target, step⟩
  have accepted := (executionTheory_step_iff_mem_executor (relations stage successors)
    (atPattern other state) target).mp step
  change target ∈ rewriteStepWithPremisesUsing
    (queryEnv _ _) language (atPattern other state) at accepted
  rw [execute_at_using] at accepted
  simp [different] at accepted
  exact List.not_mem_nil accepted

/-- An independently qualified successor query gives a behavioral cover of
the original fibre by actual authored command execution. -/
theorem stepCover (source : GSLT) (stage : Pattern)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (qualified : ∀ state answer, answer ∈ successors (encode state) ↔
      ∃ next, source.Step state next ∧ answer = encode next) :
    StepCover source (theory stage successors) (fun state => atPattern stage (encode state)) where
  mapStep := by
    intro state next step
    exact (step_at_iff stage successors _ _).mpr
      ⟨encode next, (qualified state (encode next)).mpr ⟨next, step, rfl⟩, rfl⟩
  liftStep := by
    intro state target step
    obtain ⟨answer, member, same⟩ := (step_at_iff stage successors _ _).mp step
    obtain ⟨next, sourceStep, encoded⟩ := (qualified state answer).mp member
    exact ⟨next, sourceStep, by rw [same, encoded]⟩

theorem normal_iff (source : GSLT) (stage : Pattern)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (cover : StepCover source (theory stage successors)
      (fun state => atPattern stage (encode state))) (state : source.Term) :
    source.IsNormalForm state ↔
      (theory stage successors).IsNormalForm (atPattern stage (encode state)) :=
  cover.normal_iff state

theorem path_preserved (source : GSLT) (stage : Pattern)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (cover : StepCover source (theory stage successors)
      (fun state => atPattern stage (encode state)))
    {initial final : source.Term} (path : source.MultiStep initial final) :
    (theory stage successors).MultiStep
      (atPattern stage (encode initial)) (atPattern stage (encode final)) :=
  cover.mapMultiStep path

/-- Arbitrary target paths from an encoded state retain a source endpoint;
the target carrier has not been restricted in advance. -/
theorem path_reflected (source : GSLT) (stage : Pattern)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (cover : StepCover source (theory stage successors)
      (fun state => atPattern stage (encode state)))
    (initial : source.Term) {target : Pattern}
    (path : (theory stage successors).MultiStep (atPattern stage (encode initial)) target) :
    ∃ final, target = atPattern stage (encode final) ∧ source.MultiStep initial final := by
  obtain ⟨final, same, sourcePath⟩ := cover.liftMultiStep path
  exact ⟨final, same.symm, sourcePath⟩

/-! ## LangDef fibres from their authored executor

These comparisons derive query qualification from the existing LangDef
matcher and premise executor. The source is the canonical `langGSLTUsing`,
not an independently supplied relation or a sampled finite edge catalog.
Recursive reduction premises and generated equation saturation require a
stronger complete query and are not silently erased by this specialization.
-/

open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis

theorem language_query_qualified
    (relations : RelationEnv) (lang : LanguageDef)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (source answer : Pattern) :
    answer ∈ rewriteStepWithPremisesUsing relations lang source ↔
      ∃ next, (langGSLTUsing relations lang).Step source next ∧ answer = next := by
  rw [mem_rootFrontier_iff_langGSLTUsing_step relations lang equationFree nonrecursive]
  constructor
  · intro step
    exact ⟨answer, step, rfl⟩
  · rintro ⟨next, step, same⟩
    exact same.symm ▸ step

/-- The actual `at` executor preserves and reflects the source language's
steps. Reflection ranges over every target Pattern, including candidates
outside the encoded fibre. -/
theorem language_stepCover
    (relations : RelationEnv) (lang : LanguageDef) (stage : Pattern)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises) :
    StepCover (langGSLTUsing relations lang)
      (theory stage (rewriteStepWithPremisesUsing relations lang)) (atPattern stage) :=
  stepCover (langGSLTUsing relations lang) stage id
    (rewriteStepWithPremisesUsing relations lang)
    (language_query_qualified relations lang equationFree nonrecursive)

/-- Equation preservation and local behavioral coverage in the existing
indexed operational category. Its `toBehavioralMorphism` supplies the
corresponding GSLT morphism. -/
def language_coveredTranslation
    (relations : RelationEnv) (lang : LanguageDef) (stage : Pattern)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises) :
    CoveredTranslation (langGSLTUsing relations lang)
      (theory stage (rewriteStepWithPremisesUsing relations lang)) where
  mapTerm := atPattern stage
  mapEquiv := by
    intro left right equivalent
    have same : left = right :=
      (gsltModuloEquations_equiv_iff_eq_of_no_generators equationFree left right).mp equivalent
    subst right
    exact (theory stage (rewriteStepWithPremisesUsing relations lang)).equations.refl _
  cover := language_stepCover relations lang stage equationFree nonrecursive

theorem language_step_iff
    (relations : RelationEnv) (lang : LanguageDef) (stage : Pattern)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (source target : Pattern) :
    (theory stage (rewriteStepWithPremisesUsing relations lang)).Step
      (atPattern stage source) target ↔
        ∃ next, (langGSLTUsing relations lang).Step source next ∧
          target = atPattern stage next := by
  rw [step_at_iff]
  constructor
  · rintro ⟨next, member, same⟩
    exact ⟨next, (mem_rootFrontier_iff_langGSLTUsing_step
      relations lang equationFree nonrecursive source next).mp member, same⟩
  · rintro ⟨next, step, same⟩
    exact ⟨next, (mem_rootFrontier_iff_langGSLTUsing_step
      relations lang equationFree nonrecursive source next).mpr step, same⟩

/-- An arbitrary command path reflects to the actual source endpoint. -/
theorem language_paths_reflect
    (relations : RelationEnv) (lang : LanguageDef) (stage : Pattern)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (initial : Pattern) {target : Pattern}
    (path : (theory stage (rewriteStepWithPremisesUsing relations lang)).MultiStep
      (atPattern stage initial) target) :
    ∃ final, target = atPattern stage final ∧
      (langGSLTUsing relations lang).MultiStep initial final :=
  path_reflected (langGSLTUsing relations lang) stage id _
    (language_stepCover relations lang stage equationFree nonrecursive) initial path

theorem language_paths_preserved
    (relations : RelationEnv) (lang : LanguageDef) (stage : Pattern)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    {initial final : Pattern}
    (path : (langGSLTUsing relations lang).MultiStep initial final) :
    (theory stage (rewriteStepWithPremisesUsing relations lang)).MultiStep
      (atPattern stage initial) (atPattern stage final) :=
  path_preserved (langGSLTUsing relations lang) stage id _
    (language_stepCover relations lang stage equationFree nonrecursive) path

theorem language_normal_iff
    (relations : RelationEnv) (lang : LanguageDef) (stage : Pattern)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (state : Pattern) :
    (langGSLTUsing relations lang).IsNormalForm state ↔
      (theory stage (rewriteStepWithPremisesUsing relations lang)).IsNormalForm
        (atPattern stage state) :=
  (language_stepCover relations lang stage equationFree nonrecursive).normal_iff state

/-- Infinitely many distinct enabled states cannot be covered by a catalog
of concrete edges. This concerns finite state support, not finite control:
a finite Turing table can still use the successor-query interpretation. -/
theorem finite_catalog_not_cover (source : GSLT) (stage : Pattern)
    (encode : source.Term → Pattern) (catalog : Catalog)
    (family : Nat → source.Term)
    (distinct : Function.Injective (fun index => encode (family index)))
    (enabled : ∀ index, ∃ next, source.Step (family index) next) :
    ¬ Nonempty (StepCover source (totalTheory catalog)
      (fun state => atPattern stage (encode state))) := by
  rintro ⟨cover⟩
  have supported : Set.range (fun index => encode (family index)) ⊆
      {state | state ∈ catalog.fibreRows.map FibreRow.source} := by
    rintro state ⟨index, rfl⟩
    obtain ⟨next, step⟩ := enabled index
    exact catalog_step_source_mem catalog stage _ _ (cover.mapStep step)
  exact (Set.infinite_range_of_injective distinct)
    ((catalog.fibreRows.map FibreRow.source).finite_toSet.subset supported)

end Mettapedia.GSLT.LanguageDef.GSLTIL.FibreExecution
