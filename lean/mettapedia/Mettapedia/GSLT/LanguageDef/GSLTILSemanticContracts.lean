import Mettapedia.GSLT.Core.IndexedCommandBlocks
import Mettapedia.GSLT.LanguageDef.GSLTILFibreExecution
import Mettapedia.OSLF.Framework.SuccessorFrontier

/-!
# Execution and observation contracts for authored GSLT commands

The existing command LanguageDef generates a GSLT under its chosen relation
environment. Its root executor is already proved adequate for that authored
step relation. The shared frontier lemmas therefore give exact Boolean
diamond, forward-box and quiescence observations of the same GSLT.

On a qualified guest fibre the Boolean diamond also agrees with the guest's
own step relation through its encoding. The encoding and query remain
explicit; choosing a relation environment supplies no independent guest or
native implementation correctness proof.

The imported completed-block comparison supplies the categorical contract for
the functional indexed fragment. Relational routes, contexts and occurrence
observations retain their existing separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticContracts

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.SuccessorFrontier

/-- The existing root executor, with the same authored command rules and
relation environment as its generated GSLT. -/
abbrev executorFrontier (relations : RelationEnv) (state : Pattern) :=
  rewriteStepWithPremisesUsing relations language state

/-- Every reported root successor is an authored step, and every authored
step is reported. -/
theorem executor_qualified (relations : RelationEnv) (state next : Pattern) :
    next ∈ executorFrontier relations state ↔
      (executionTheory relations).Step state next :=
  (executionTheory_step_iff_mem_executor relations state next).symm

/-- Existential frontier observation is exactly the generated GSLT diamond. -/
theorem executor_any_iff_diamond (relations : RelationEnv)
    (test : Pattern → Bool) (state : Pattern) :
    (executorFrontier relations state).any test = true ↔
      gsltDiamond (executionTheory relations) (fun next => test next = true) state :=
  any_iff_diamond (executionTheory relations) (executorFrontier relations)
    (executor_qualified relations) test state

/-- Universal frontier observation uses the forward box of the same GSLT. -/
theorem executor_all_iff_forwardBox (relations : RelationEnv)
    (test : Pattern → Bool) (state : Pattern) :
    (executorFrontier relations state).all test = true ↔
      derivedForwardBox (gsltSpan (executionTheory relations))
        (fun next => test next = true) state :=
  all_iff_forwardBox (executionTheory relations) (executorFrontier relations)
    (executor_qualified relations) test state

/-- Complete executor exhaustion means an actual normal form. -/
theorem executor_nil_iff_normal (relations : RelationEnv) (state : Pattern) :
    executorFrontier relations state = [] ↔
      (executionTheory relations).IsNormalForm state :=
  nil_iff_normal (executionTheory relations) (executorFrontier relations)
    (executor_qualified relations) state

/-- A guest query's diamond commutes with its qualified encoding. The
encoding may identify states; query qualification still forbids spurious
observations and missing successors. -/
theorem guest_query_any_iff_diamond (source : GSLT)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (qualified : ∀ state answer, answer ∈ successors (encode state) ↔
      ∃ next, source.Step state next ∧ answer = encode next)
    (test : Pattern → Bool) (state : source.Term) :
    (successors (encode state)).any test = true ↔
      gsltDiamond source (fun next => test (encode next) = true) state := by
  rw [List.any_eq_true, gsltDiamond_spec]
  constructor
  · rintro ⟨answer, member, satisfied⟩
    obtain ⟨next, step, same⟩ := (qualified state answer).mp member
    exact ⟨next, step, same ▸ satisfied⟩
  · rintro ⟨next, step, satisfied⟩
    exact ⟨encode next, (qualified state (encode next)).mpr ⟨next, step, rfl⟩,
      satisfied⟩

/-- Universal successor observation also commutes with a qualified guest
encoding, using the forward box rather than the predecessor modality. -/
theorem guest_query_all_iff_forwardBox (source : GSLT)
    (encode : source.Term → Pattern) (successors : Pattern → List Pattern)
    (qualified : ∀ state answer, answer ∈ successors (encode state) ↔
      ∃ next, source.Step state next ∧ answer = encode next)
    (test : Pattern → Bool) (state : source.Term) :
    (successors (encode state)).all test = true ↔
      derivedForwardBox (gsltSpan source)
        (fun next => test (encode next) = true) state := by
  rw [List.all_eq_true]
  simp only [derivedForwardBox, ui, pb, Function.comp, gsltSpan]
  constructor
  · intro universal ⟨origin, next, step⟩ same
    change origin = state at same
    subst origin
    exact universal (encode next)
      ((qualified state (encode next)).mpr ⟨next, step, rfl⟩)
  · intro universal answer member
    obtain ⟨next, step, same⟩ := (qualified state answer).mp member
    exact same.symm ▸ universal ⟨state, next, step⟩ rfl

/-! ## Observations of LangDef fibres -/

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The root query realizes the canonical language diamond once the
authored structure makes that query complete. -/
theorem language_frontier_any_iff_diamond
    (relations : RelationEnv) (lang : LanguageDef)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (test : Pattern → Bool) (state : Pattern) :
    (rewriteStepWithPremisesUsing relations lang state).any test = true ↔
      gsltDiamond (langGSLTUsing relations lang) (fun next => test next = true) state :=
  any_iff_diamond (langGSLTUsing relations lang)
    (rewriteStepWithPremisesUsing relations lang)
    (mem_rootFrontier_iff_langGSLTUsing_step relations lang equationFree nonrecursive)
    test state

theorem language_frontier_all_iff_forwardBox
    (relations : RelationEnv) (lang : LanguageDef)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (test : Pattern → Bool) (state : Pattern) :
    (rewriteStepWithPremisesUsing relations lang state).all test = true ↔
      derivedForwardBox (gsltSpan (langGSLTUsing relations lang))
        (fun next => test next = true) state :=
  all_iff_forwardBox (langGSLTUsing relations lang)
    (rewriteStepWithPremisesUsing relations lang)
    (mem_rootFrontier_iff_langGSLTUsing_step relations lang equationFree nonrecursive)
    test state

theorem language_frontier_nil_iff_normal
    (relations : RelationEnv) (lang : LanguageDef)
    (equationFree : lang.isEquationFree = true)
    (nonrecursive : ∀ rule ∈ lang.rewrites, NoncontextualPremises rule.premises)
    (state : Pattern) :
    rewriteStepWithPremisesUsing relations lang state = [] ↔
      (langGSLTUsing relations lang).IsNormalForm state :=
  nil_iff_normal (langGSLTUsing relations lang)
    (rewriteStepWithPremisesUsing relations lang)
    (mem_rootFrontier_iff_langGSLTUsing_step relations lang equationFree nonrecursive) state

namespace Controls

private def atom (name : String) : Pattern := .apply name []
private def stage : Pattern := atom "frontier-control"
private def ready : Pattern := atom "ready"
private def done : Pattern := atom "done"
private def query (state : Pattern) : List Pattern := if state = ready then [done] else []

/-- An actual execution of the authored at rule has the promised diamond. -/
theorem authored_command_diamond :
    gsltDiamond (FibreExecution.theory stage query)
      (fun result => result = atPattern stage done) (atPattern stage ready) := by
  apply (gsltDiamond_spec (FibreExecution.theory stage query) _ _).mpr
  refine ⟨atPattern stage done, ?_, rfl⟩
  apply (FibreExecution.step_at_iff stage query ready _).mpr
  exact ⟨done, by simp [query], rfl⟩

/-- A query registered at one stage supplies no execution at another stage. -/
theorem unsupported_stage_normal :
    (FibreExecution.theory stage query).IsNormalForm
      (atPattern (atom "unsupported") ready) :=
  FibreExecution.other_stage_normal stage (atom "unsupported") query
    (by simp [stage, atom]) ready

namespace AuthoredLanguage

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open FibreExecution

/-! These controls execute conditional rules on a declared binder/vector
language, retain duplicate answers, and reject omitted equation closure and
invented query results. The language passes the existing structural validator.
-/

private def atom (name : String) : Pattern := .apply name []
private def ready : Pattern := atom "Ready"
private def done : Pattern := atom "Done"
private def stage : Pattern := atom "LangDefControl"

private def advance : RewriteRule :=
  { name := "advance"
    typeContext := [("next", .base "State")]
    premises := [.relationQuery "Advance" [ready, .fvar "next"]]
    left := ready
    right := .fvar "next" }

private def vector (element : Pattern) : Pattern :=
  .apply "Vector"
    [.collection .vec [.apply "Bind" [.lambda none (.bvar 0)], element, element] none]

private def advanceVector : RewriteRule :=
  { advance with
    name := "advance-vector"
    left := vector ready
    right := vector (.fvar "next") }

private def guest : LanguageDef :=
  { name := "conditional-vector-binding-control"
    types := [TypeDecl.plain "State"]
    terms :=
      [{ label := "Ready", category := "State", params := [], syntaxPattern := [] },
       { label := "Done", category := "State", params := [], syntaxPattern := [] },
       { label := "Vector", category := "State",
         params := [.simple "elements" (.collection .vec (.base "State"))],
         syntaxPattern := [] },
       { label := "Bind", category := "State",
         params := [.abstraction "body" (.arrow (.base "State") (.base "State"))],
         syntaxPattern := [] }]
    equations := []
    rewrites := [advance, advanceVector] }

private def premises : RelationEnv where
  tuples name _ := if name = "Advance" then [[ready, done], [ready, done]] else []

theorem guest_equation_free : guest.isEquationFree = true := by decide +kernel

theorem guest_nonrecursive :
    ∀ rule ∈ guest.rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  simp only [guest, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  all_goals exact .relationQuery .nil

theorem duplicate_frontier :
    rewriteStepWithPremisesUsing premises guest ready = [done, done] := by decide +kernel

theorem conditional_binder_vector_frontier :
    rewriteStepWithPremisesUsing premises guest (vector ready) =
      [vector done, vector done] := by decide +kernel

theorem guest_validates : guest.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  intro rule member
  simp only [guest, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
      LanguageDef.validatePatternConstructors,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      LanguageDef.typeNames, guest, advance, advanceVector, vector, ready, atom]
  all_goals
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name member
    simpa [TypeExpr.baseNames, TypeDecl.plain] using member

theorem duplicate_command_answers :
    rewriteStepWithPremisesUsing
      (relations stage (rewriteStepWithPremisesUsing premises guest))
      language (atPattern stage ready) =
        [atPattern stage done, atPattern stage done] := by decide +kernel

private def bagGuest : LanguageDef :=
  { guest with terms := guest.terms ++
      [{ label := "Bag", category := "State",
         params := [.simple "elements" (.collection .hashBag (.base "State"))],
         syntaxPattern := [] }] }

theorem generated_collection_laws_not_equation_free :
    bagGuest.equations = [] ∧ bagGuest.isEquationFree = false := by decide +kernel

/-- Query qualification must exclude invented answers as well as omissions. -/
theorem spurious_query_adds_guest_step :
    (theory stage (fun _ => [done])).Step (atPattern stage ready) (atPattern stage done) ∧
      ¬ (langGSLTUsing RelationEnv.empty guest).Step ready done := by
  constructor
  · exact (step_at_iff stage (fun _ => [done]) ready _).mpr
      ⟨done, List.Mem.head _, rfl⟩
  · intro firing
    have primitive :=
      (langSemanticReducesUsing_iff_langReducesUsing_of_equation_free
        RelationEnv.empty guest_equation_free ready done).mp firing
    have root := (step_iff_rootStep_of_noncontextualRules guest_nonrecursive).mp primitive
    have member : done ∈ rewriteStepWithPremisesUsing RelationEnv.empty guest ready := by
      simpa [RootStep, rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing] using root
    have empty : rewriteStepWithPremisesUsing RelationEnv.empty guest ready = [] := by
      decide +kernel
    rw [empty] at member
    exact List.not_mem_nil member

private def stateAlias : Equation :=
  { name := "alias", typeContext := [], premises := [],
    left := atom "Alias", right := ready }

private def equationalGuest : LanguageDef :=
  { guest with equations := [stateAlias] }

theorem alias_root_empty :
    rewriteStepWithPremisesUsing premises equationalGuest (atom "Alias") = [] := by decide +kernel

private theorem alias_equivalent :
    EquationEquiv (engineBasePremises premises) equationalGuest (atom "Alias") ready := by
  apply equationInstance_equivalent
  refine ⟨0, .forward (equation := stateAlias) (initialBindings := [])
    (finalBindings := []) ?_ ?_ (.nil []) ?_⟩
  · exact List.Mem.head _
  · decide +kernel
  · simp [Mettapedia.OSLF.MeTTaIL.Match.applyBindings, stateAlias, ready, atom]

theorem equation_exposes_step_omitted_by_root :
    (langGSLTUsing premises equationalGuest).Step (atom "Alias") done ∧
      rewriteStepWithPremisesUsing premises equationalGuest (atom "Alias") = [] := by
  constructor
  · refine ⟨ready, done, alias_equivalent, ?_, Relation.EqvGen.refl _⟩
    apply step_of_rule (rule := advance) (initialBindings := [])
      (finalBindings := [("next", done)])
    · simp [equationalGuest, guest]
    · decide +kernel
    · exact .relationQuery .nil
    · decide +kernel
    · decide +kernel
  · exact alias_root_empty

end AuthoredLanguage

namespace RecursivePremise

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics

private def ready : Pattern := .apply "Ready" []
private def done : Pattern := .apply "Done" []
private def box (value : Pattern) : Pattern := .apply "Box" [value]
private def advance : RewriteRule :=
  { name := "advance", typeContext := [], premises := [], left := ready, right := done }
private def underBox : RewriteRule :=
  { name := "under-box", typeContext := [], premises := [.congruence ready done],
    left := box ready, right := box done }
private def guest : LanguageDef :=
  { name := "recursive-premise-control", types := ["State"],
    terms := [{ label := "Ready", category := "State", params := [], syntaxPattern := [] },
      { label := "Done", category := "State", params := [], syntaxPattern := [] },
      { label := "Box", category := "State", params := [.simple "value" (.base "State")],
        syntaxPattern := [] }],
    equations := [], rewrites := [advance, underBox] }

theorem guest_validates : guest.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  intro rule member
  simp only [guest, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  all_goals
    simp [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
      LanguageDef.validatePatternConstructors,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
      LanguageDef.premiseStepTypeExprs, LanguageDef.premiseLocallyScoped,
      Pattern.constructorRefs, Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      LanguageDef.typeNames, guest, advance, underBox, box, ready, done]

theorem guest_equation_free : guest.isEquationFree = true := by decide +kernel

theorem guest_is_recursive :
    ¬ (∀ rule ∈ guest.rewrites, NoncontextualPremises rule.premises) := by
  intro allRules
  have recursive := allRules underBox (by simp [guest])
  cases recursive

theorem root_box_empty :
    rewriteStepWithPremisesUsing RelationEnv.empty guest (box ready) = [] := by decide +kernel

theorem contextual_box_frontier :
    reductsUsing RelationEnv.empty guest 2 (box ready) = [box done] := by decide +kernel

/-- The root query misses a real step earned through a recursive premise. -/
theorem recursive_premise_exposes_step :
    (langGSLT guest).Step (box ready) (box done) ∧
      rewriteStepWithPremisesUsing RelationEnv.empty guest (box ready) = [] := by
  refine ⟨?_, root_box_empty⟩
  apply step_to_stepModuloEquations
  refine ⟨2, (mem_rewriteAt_iff_stepAt).mp ?_⟩
  exact (by decide +kernel)

end RecursivePremise

end Controls

end Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticContracts
