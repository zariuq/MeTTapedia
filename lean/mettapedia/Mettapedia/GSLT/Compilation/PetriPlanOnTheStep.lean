import Mettapedia.GSLT.Compilation.BagRewritesOnTheStep
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSharedOutputControls
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-!
# The petri plan compiled to the transform step

`CollectionConsumers.petriPlan` fires at the root alone and has no equations, so
its step is exactly a root firing (`step_iff_rootFiring`). On a well-sorted
marking a root firing is an authored step, and the bag lowering carries that
step to one rewriting of the encoded rows (`planStep_iff_rewrites`).

The observation is which successors are possible. Order and the number of
matches are not preserved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.PetriPlanOnTheStep

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (providerRelEnv)
open Mettapedia.GSLT.LanguageDef.CollectionConsumers (petri)
open SharedOutputControls.BareReferenceControls (petriEnvironment petri_uniform_source_iff)

theorem aligned : ReferenceStep.ReferenceProfile petri := by
  intro rule member
  have all : petri.rewrites.all ReferenceStep.ruleAligned = true := by cbv
  exact List.all_eq_true.mp all rule member

theorem compiles : ∃ program, BagRewritesOnTheStep.compile petri = .ok program := by
  cases h : BagRewritesOnTheStep.compile petri with
  | ok program => exact ⟨program, rfl⟩
  | error reason =>
      have ok : (BagRewritesOnTheStep.compile petri).isOk = true := by cbv
      rw [h] at ok
      cases ok

/-- A root firing of the gate's petri plan, from a well-sorted marking, is one
rewriting of the encoded rows by the compiled program. -/
theorem rootFiring_iff_rewrites {program : List SRule}
    (compiled : BagRewritesOnTheStep.compile petri = .ok program) {bound : List TypeExpr}
    {members : List Pattern}
    (typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted petriEnvironment.language
      petriEnvironment.free bound (.base "Marking") (BagRewritesOnTheStep.bag members))
    (after : Multiset NamesOnTheStep.Expr) :
    (∃ result : List Pattern, after = BagRewritesOnTheStep.rows result ∧
      ∃ index trace captured completed history,
        RootFiring petriEnvironment bound (.base "Marking") (BagRewritesOnTheStep.bag members)
          index trace captured completed history (BagRewritesOnTheStep.bag result)) ↔
      Rewrites program (BagRewritesOnTheStep.rows members) after := by
  constructor
  · rintro ⟨result, rfl, fired⟩
    have reference := (petri_uniform_source_iff typed).mp fired
    obtain ⟨after, same, rewrites⟩ := BagRewritesOnTheStep.rewrites_of_step compiled
      ((ReferenceStep.contextualStep_iff_step _ _ aligned).mpr reference)
    cases same
    exact rewrites
  · intro rewrites
    obtain ⟨result, stepped, same⟩ := BagRewritesOnTheStep.step_of_rewrites
      (relEnv := providerRelEnv petriEnvironment.provider) compiled rewrites
    exact ⟨result, same, (petri_uniform_source_iff typed).mpr
      ((ReferenceStep.contextualStep_iff_step _ _ aligned).mp stepped)⟩

open GeneralTypedSites in
/-- A root-only plan without equations steps exactly by a root firing. -/
theorem step_iff_rootFiring {plan : GeneralExecutionAdmission.Plan}
    (root : plan.permissions.sites = .rootOnly) (equationFree : plan.equations = [])
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern} :
    (GeneralOccurrenceSemantics.gslt plan bound type).Step source target ↔
      ∃ index trace captured completed history,
        RootFiring (GeneralPlanEnvironment.environment plan) bound type source
          index trace captured completed history target := by
  constructor
  · rintro ⟨representative, receipt, before, fired, after⟩
    have sourceSame := GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
      (request := ⟨plan, bound, type, source⟩) equationFree before
    have targetSame := GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
      (request := ⟨plan, bound, type, source⟩) equationFree after
    subst representative
    have licensed := fired.1.2
    rw [root] at licensed
    have site := Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.rootOnly_site licensed
    have filled : receipt.target = receipt.localTarget := by
      simpa only [site, SiteData.here, DerivedContexts.OneHoleContext.fill] using fired.2.2.2.1
    refine ⟨receipt.job.ordinal, receipt.matcherTrace, receipt.captured, receipt.completed,
      receipt.premiseHistory, ?_⟩
    rw [← targetSame, filled]
    simpa only [site, SiteData.here, GeneralPlanEnvironment.environmentWith_empty] using fired.2.1
  · rintro ⟨index, trace, captured, completed, history, firing⟩
    have whole := firing
    cases firing with
    | fire declared _ _ sourceTyped _ _ _ _ sorted =>
      have row : (plan.rules.map GeneralExecutionAdmission.RulePlan.rule)[index]? = some _ := declared
      simp only [List.getElem?_map, Option.map_eq_some_iff] at row
      obtain ⟨declaration, selected, -⟩ := row
      let job : GeneralRuleJobs.Job := ⟨index, declaration, SiteData.here bound type source⟩
      have jobValid : job.Valid plan bound type source := by
        refine ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
        rw [root]
        exact .here rfl sourceTyped.2.2.1 sourceTyped.1
      let receipt : GeneralRuleJobs.Receipt := ⟨job, trace, captured, completed, history, target, target⟩
      exact ⟨source, receipt, .refl source, ⟨jobValid, whole, rfl, rfl, sorted⟩, .refl target⟩

open Mettapedia.GSLT.LanguageDef.CollectionConsumers (petriPlan) in
/-- **The gate's petri plan and its transform program.** From a well-sorted marking,
one step of the plan is one rewriting of the encoded rows. -/
theorem planStep_iff_rewrites {program : List SRule}
    (compiled : BagRewritesOnTheStep.compile petri = .ok program) {bound : List TypeExpr}
    {members : List Pattern}
    (typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted petriEnvironment.language
      petriEnvironment.free bound (.base "Marking") (BagRewritesOnTheStep.bag members))
    (after : Multiset NamesOnTheStep.Expr) :
    (∃ result : List Pattern, after = BagRewritesOnTheStep.rows result ∧
      (GeneralOccurrenceSemantics.gslt petriPlan bound (.base "Marking")).Step
        (BagRewritesOnTheStep.bag members) (BagRewritesOnTheStep.bag result)) ↔
      Rewrites program (BagRewritesOnTheStep.rows members) after :=
  Iff.trans (exists_congr fun _ => and_congr_right fun _ =>
      step_iff_rootFiring (plan := petriPlan) rfl (by cbv))
    (rootFiring_iff_rewrites compiled typed after)

open Mettapedia.GSLT.LanguageDef.CollectionConsumers (petriPlan) in
/-- Every successor of a well-sorted marking is a marking, so the iff misses no step. -/
theorem planStep_target {program : List SRule}
    (compiled : BagRewritesOnTheStep.compile petri = .ok program) {bound : List TypeExpr}
    {members : List Pattern} {target : Pattern}
    (typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted petriEnvironment.language
      petriEnvironment.free bound (.base "Marking") (BagRewritesOnTheStep.bag members))
    (stepped : (GeneralOccurrenceSemantics.gslt petriPlan bound (.base "Marking")).Step
      (BagRewritesOnTheStep.bag members) target) :
    ∃ result, target = BagRewritesOnTheStep.bag result := by
  have fired := (step_iff_rootFiring (plan := petriPlan) rfl (by cbv)).mp stepped
  obtain ⟨result, same, -⟩ := BagRewritesOnTheStep.rewrites_of_step compiled
    ((ReferenceStep.contextualStep_iff_step _ _ aligned).mpr ((petri_uniform_source_iff typed).mp fired))
  exact ⟨result, same⟩

/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.LanguageDef.CollectionConsumers (petriPlan token)
open BagRewritesOnTheStep (bag)
open BagRewritesOnTheStep.Controls (successors step_iff_successor)

/-- **Positive**: A and B together become C and D, by the plan's own step. -/
theorem consume_steps : (GeneralOccurrenceSemantics.gslt petriPlan [] (.base "Marking")).Step
    (bag [token "A", token "B"]) (bag [token "C", token "D"]) := by
  obtain ⟨program, compiled⟩ := compiles
  have typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted petriEnvironment.language
      petriEnvironment.free [] (.base "Marking") (bag [token "A", token "B"]) :=
    GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound (by cbv)
  have only : successors petri (bag [token "A", token "B"]) = [bag [token "C", token "D"]] := by cbv
  refine (step_iff_rootFiring (plan := petriPlan) rfl (by cbv)).mpr ((petri_uniform_source_iff typed).mpr
    ((ReferenceStep.contextualStep_iff_step _ _ aligned).mp ((step_iff_successor compiled _ _).mpr ?_)))
  rw [only]
  exact List.mem_singleton.mpr rfl

/-- **Negative**: A alone has no step. -/
theorem lone_token_stuck (target : Pattern) :
    ¬ (GeneralOccurrenceSemantics.gslt petriPlan [] (.base "Marking")).Step (bag [token "A"]) target := by
  intro stepped
  obtain ⟨program, compiled⟩ := compiles
  have typed : GSLT.LanguageDef.WellSorted.OpenPatternWellSorted petriEnvironment.language
      petriEnvironment.free [] (.base "Marking") (bag [token "A"]) :=
    GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound (by cbv)
  have none_ : successors petri (bag [token "A"]) = [] := by cbv
  have member := (step_iff_successor compiled _ _).mp ((ReferenceStep.contextualStep_iff_step _ _ aligned).mpr
    ((petri_uniform_source_iff typed).mp ((step_iff_rootFiring (plan := petriPlan) rfl (by cbv)).mp stepped)))
  rw [none_] at member
  cases member

end Controls

end Mettapedia.GSLT.Compilation.PetriPlanOnTheStep

#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.compiles
#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.step_iff_rootFiring
#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.rootFiring_iff_rewrites
#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.planStep_iff_rewrites
#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.planStep_target
#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.Controls.consume_steps
#print axioms Mettapedia.GSLT.Compilation.PetriPlanOnTheStep.Controls.lone_token_stuck
