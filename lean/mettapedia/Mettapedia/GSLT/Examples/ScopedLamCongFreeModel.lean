import Mettapedia.OSLF.Syntax.ScopedOperationalCertification
import Mettapedia.GSLT.Examples.ScopedLamCongExecution
import Mettapedia.GSLT.Examples.ScopedLamCongStepShape

/-!
# The authored LamCong rule enters the fixed operational presentation

The real two-layer evaluator produces a constructor shape and a free
derivation at the judgment whose premise runs under the lambda binder. Its
positional decoder recovers the exact beta-child history. At fuel zero the
same bounded presentation has no constructor or derivation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongFreeModel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalFreeModel
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.GSLT.Examples.ScopedLamCongExecution
open Mettapedia.GSLT.Examples.ScopedLamCongStepShape

/-- The executable history classifier accepts only the rule-one firing
whose scoped child is rule-zero beta. -/
private theorem history_of_beta_indicator (history : RuleHistory)
    (indicated : lamCongBetaHistory history = true) :
    history = .fire 1 [.step 0 0 (.fire 0 [])] := by
  unfold lamCongBetaHistory at indicated
  split at indicated
  · rfl
  · cases indicated

/-- The running authored lambda language has a rule constructor at its
actual open-variable, two-layer reduction judgment. -/
theorem authored_lamCong_has_constructor :
    Nonempty ((authoredRules RelationEnv.empty language).rules.Shape ()
      ⟨2, 0, wrappedRedex, wrappedTarget⟩) := by
  obtain ⟨⟨history, target⟩, selected, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  dsimp at targetEq
  subst target
  exact runtime_has_constructor RelationEnv.empty language 1 0
    wrappedRedex wrappedTarget history selected

/-- The authored open-variable LamCong execution generates a complete
two-level derivation in the fixed free operational algebra. -/
theorem authored_lamCong_has_free_derivation :
    Nonempty ((presentation RelationEnv.empty language).Derivation ()
      ⟨2, 0, wrappedRedex, wrappedTarget⟩) := by
  obtain ⟨⟨history, target⟩, selected, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  dsimp at targetEq
  subst target
  exact runtime_to_free_derivation RelationEnv.empty language 2 0
    wrappedRedex wrappedTarget history selected

/-- The authored LamCong derivation remembers its actual beta child beneath
the binder, including the parent and child rule positions and child ordinal. -/
theorem authored_lamCong_exact_history_derivation :
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, 0, wrappedRedex, wrappedTarget⟩,
      decodeHistory? RelationEnv.empty language _ tree =
        some (.fire 1 [.step 0 0 (.fire 0 [])]) := by
  obtain ⟨⟨history, target⟩, selected, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  dsimp at targetEq
  subst target
  have mapped :
      (lamCongBetaHistory history, wrappedTarget == wrappedTarget) ∈
        (rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map
          (fun (event, result) =>
            (lamCongBetaHistory event, result == wrappedTarget)) :=
    List.mem_map.mpr ⟨(history, wrappedTarget), selected, rfl⟩
  rw [lamCong_tree_shape] at mapped
  have indicated : lamCongBetaHistory history = true :=
    congrArg Prod.fst (List.mem_singleton.mp mapped)
  have exactHistory := history_of_beta_indicator history indicated
  subst history
  exact runtime_to_free_with_history RelationEnv.empty language 2 0
    wrappedRedex wrappedTarget (.fire 1 [.step 0 0 (.fire 0 [])]) selected

/-- The same actual authored reduction supplies the oracle certificate at
both levels of its free derivation, with the exact nested beta history. -/
theorem authored_lamCong_certified_derivation :
    ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, 0, wrappedRedex, wrappedTarget⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        decodeHistory? RelationEnv.empty language _ tree =
          some (.fire 1 [.step 0 0 (.fire 0 [])]) := by
  obtain ⟨⟨history, target⟩, selected, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  dsimp at targetEq
  subst target
  have mapped :
      (lamCongBetaHistory history, wrappedTarget == wrappedTarget) ∈
        (rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map
          (fun (event, result) =>
            (lamCongBetaHistory event, result == wrappedTarget)) :=
    List.mem_map.mpr ⟨(history, wrappedTarget), selected, rfl⟩
  rw [lamCong_tree_shape] at mapped
  have indicated : lamCongBetaHistory history = true :=
    congrArg Prod.fst (List.mem_singleton.mp mapped)
  have exactHistory := history_of_beta_indicator history indicated
  subst history
  exact runtime_to_certified_tree RelationEnv.empty language 2 0
    wrappedRedex wrappedTarget (.fire 1 [.step 0 0 (.fire 0 [])])
      selected

/-- A candidate with the same endpoints but an unselected child ordinal
cannot be certified as this authored LamCong execution. -/
theorem wrong_child_ordinal_not_certified :
    ¬ ∃ tree : (presentation RelationEnv.empty language).Derivation ()
        ⟨2, 0, wrappedRedex, wrappedTarget⟩,
      CertifiedTree RelationEnv.empty language _ tree ∧
        decodeHistory? RelationEnv.empty language _ tree =
          some (.fire 1 [.step 0 1 (.fire 0 [])]) := by
  intro putative
  have executed := (certified_tree_iff_execution RelationEnv.empty
    language 2 0 wrappedRedex wrappedTarget
    (.fire 1 [.step 0 1 (.fire 0 [])])).mp putative
  have mapped : (false, true) ∈
      (rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map
        (fun (history, target) =>
          (lamCongBetaHistory history, target == wrappedTarget)) :=
    List.mem_map.mpr ⟨(.fire 1 [.step 0 1 (.fire 0 [])],
      wrappedTarget), executed, rfl⟩
  rw [lamCong_tree_shape] at mapped
  simp at mapped

/-- The authored LamCong step shape also admits a syntactic premise label
with ordinal one, while a one-result oracle has only ordinal zero. This
exhibits the local free-shape/certified-shape distinction independently of
the preceding non-execution theorem. -/
theorem unselected_premise_shape_exists :
    ∃ (spec : RuleBindingSpec) (captured completed :
        Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
      (shape : PremiseSkeleton RuleHistory RelationEnv.empty language
        lamCongRule spec 0 0 (.scopedStep localStep) captured completed),
      shape.child? ≠ none ∧
      ¬ PremiseSkeleton.Selected
        (fun _ _ => [(RuleHistory.fire 0 [], .bvar 0)]) shape
          (some (.fire 0 [])) := by
  obtain ⟨spec, captured, completed, stepShape, _, _, _⟩ :=
    authored_lamCong_has_step_shape
  have wellScoped : localStep.isWellScopedAt 0 = true := by
    decide +kernel
  let shape : PremiseSkeleton RuleHistory RelationEnv.empty language
      lamCongRule spec 0 0 (.scopedStep localStep) captured completed :=
    .scopedStep wellScoped 1 stepShape
  refine ⟨spec, captured, completed, shape, ?_, ?_⟩
  · simp [shape, PremiseSkeleton.child?]
  · simp [shape, PremiseSkeleton.Selected, List.zipIdx]

/-- The constructor obtained from that exact run has the authored LamCong
position and its sole recursive child in the lambda binder's context. -/
theorem authored_lamCong_constructor_has_scoped_child :
    ∃ shape : RuleSkeleton RuleHistory RelationEnv.empty language
        0 wrappedRedex wrappedTarget,
      shape.ruleIndex = 1 ∧
      ∃ childSource childTarget,
        shape.children = [(1, childSource, childTarget)] := by
  obtain ⟨⟨history, target⟩, executed, targetEq⟩ :=
    List.mem_map.mp lamCong_requires_two_layers.2
  dsimp at targetEq
  subst target
  have mapped :
      (lamCongBetaHistory history, wrappedTarget == wrappedTarget) ∈
        (rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map
          (fun (history, target) =>
            (lamCongBetaHistory history, target == wrappedTarget)) :=
    List.mem_map.mpr ⟨(history, wrappedTarget), executed, rfl⟩
  rw [lamCong_tree_shape] at mapped
  have indicated : lamCongBetaHistory history = true :=
    congrArg Prod.fst (List.mem_singleton.mp mapped)
  have exactHistory := history_of_beta_indicator history indicated
  obtain ⟨shape, premiseHistory, historyEq, _⟩ :=
    runtime_has_shape_with_history RelationEnv.empty language 1 0
      wrappedRedex wrappedTarget history executed
  have ruleIndex : shape.ruleIndex = 1 := by
    rw [exactHistory] at historyEq
    cases shape with
    | mk rule ruleIndex listed spec declared admitted captured selected
        completed premises reduct resultScoped =>
        cases historyEq
        rfl
  have listedRule : shape.rule = lamCongRule := by
    have listed := shape.listed
    simp [language, ruleIndex] at listed
    exact listed
  have single : shape.rule.premises = [.scopedStep localStep] := by
    rw [listedRule]
    rfl
  obtain ⟨childSource, childTarget, childEq⟩ :=
    shape.single_scoped_child single
  exact ⟨shape, ruleIndex, childSource, childTarget, by
    simpa [localStep] using childEq⟩

/-- The zero-fuel boundary contributes no spurious constructor for that
same authored source and target. -/
theorem zero_fuel_has_no_constructor :
    ¬ Nonempty ((authoredRules RelationEnv.empty language).rules.Shape ()
      ⟨0, 0, wrappedRedex, wrappedTarget⟩) := by
  rintro ⟨shape⟩
  exact shape.elim

/-- The same judgment at zero fuel has no free derivation, so the free
construction is sensitive to the recursive depth used by the evaluator. -/
theorem zero_fuel_has_no_free_derivation :
    ¬ Nonempty ((presentation RelationEnv.empty language).Derivation ()
      ⟨0, 0, wrappedRedex, wrappedTarget⟩) :=
  no_zero_fuel_derivation RelationEnv.empty language 0
    wrappedRedex wrappedTarget

end Mettapedia.GSLT.Examples.ScopedLamCongFreeModel
