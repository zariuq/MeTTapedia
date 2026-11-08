import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateControls

/-!
# Direct templates in the native step, and where publication leaves the raw target

An authored template instance is a native firing whose recipes are the template's pre-execution
recipes (`templateFiring`). The step publishes a pinned execution of its code as the template's own
target (`template_published`, from `publishedRows_from_recipes`).

**Negative control** (`PublicationBoundary`): at an actual mixed template execution, at every
budget, the published state and the raw target disagree (`published_differs_from_raw_target`), and
two native firings with the same execution data, one with the template's recipes and one without,
have different results in the candidate step (`native_result_depends_on_recipes`). The result of the
step is not a function of the raw execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalTemplateExecution (TemplateInstance CompiledTemplate)

section Template

variable {S : Signature} {Local Inner O : Type} (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
  [DecidableEq Local] [DecidableEq Inner] [DecidableEq O] [DecidableEq S.Srt]
  [∀ result, DecidableEq (S.Op result)] {Γ : Ctx S} {sort : S.Srt}

/-- The native state of a template-execution state. -/
def templateState
    (before : ContextualConditionalExecution.State (ContextualTemplateSource.Expanded locals inners) O Γ sort) :
    NativeState S O Γ sort :=
  ⟨Local ⊕ (Nat × Inner), inferInstance, ContextualTemplateSource.Expanded locals inners, before⟩

variable {locals inners}
  {before : ContextualConditionalExecution.State (ContextualTemplateSource.Expanded locals inners) O Γ sort}

/-- **The native firing of an authored template instance**, at a budget: its recipes are the
template's pre-execution recipes. -/
def templateFiring (authored : TemplateInstance locals inners before) (fuel : Nat) :
    NativeFiring (templateState locals inners before) :=
  ⟨authored.sourceRule.code.lower locals inners before.declarations, authored.selection, authored.outputs,
    authored.sourceRule.ordinaryFlags authored.selection.made, [], fuel, authored.recipes locals inners,
    fun occurrence missing => authored.recipes_none_of_not_made locals inners occurrence missing⟩

/-- **The step publishes a template's execution as the template's own target.** -/
theorem template_published (authored : TemplateInstance locals inners before)
    (record : ContextualConditionalExecution.Published (ContextualTemplateSource.Expanded locals inners) before
      (authored.sourceRule.code.lower locals inners before.declarations) authored.selection authored.outputs
      (.all (authored.sourceRule.ordinaryFlags authored.selection.made))) :
    publishRows (s := templateState locals inners before) (authored.recipes locals inners) record.firing =
      CompiledTemplate.publishedRows (⟨authored, record⟩ : CompiledTemplate locals inners before) := by
  funext occurrence
  rw [CompiledTemplate.publishedRows_from_recipes]
  dsimp only
  unfold publishRows
  cases authored.recipes locals inners occurrence with
  | none => rfl
  | some recipe => rfl

end Template

namespace PublicationControls

open ContextualConditionalTemplateControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

/-- **Negative control.** At an actual mixed template execution, at every budget, the published
state and the raw target disagree. -/
theorem published_differs_from_raw_target (fuel : Nat) :
    ∃ (authored : TemplateInstance locals inners before)
      (record : ContextualConditionalExecution.Published bank before
        (authored.sourceRule.code.lower locals inners before.declarations) authored.selection authored.outputs
        (.all (authored.sourceRule.ordinaryFlags authored.selection.made))),
      record.firing.fuel = fuel ∧
        publishedState (s := templateState locals inners before) (authored.recipes locals inners) record.firing ≠
          rawTarget (s := templateState locals inners before) record.firing := by
  obtain ⟨compiled, budget, differs⟩ := PublicationBoundary.an_actual_publication_differs_from_its_raw_target fuel
  refine ⟨compiled.1, compiled.2, budget, fun same => differs ?_⟩
  have rows := (publishedState_eq_rawTarget_iff (s := templateState locals inners before) _ compiled.2.firing).mp same
  rw [template_published compiled.1 compiled.2] at rows
  exact rows

/-- **The step's result is not a function of the raw execution**: two native firings with the same
execution data, one with the template's recipes and one without, have different results. -/
theorem native_result_depends_on_recipes (fuel : Nat) :
    ∃ (f g : NativeFiring (templateState locals inners before)) (realizedF : f.Realized) (realizedG : g.Realized),
      f.rule = g.rule ∧ f.selection = g.selection ∧ f.outputs = g.outputs ∧ f.reusable = g.reusable ∧
        f.queries = g.queries ∧ f.fuel = g.fuel ∧
          (native (S := base) (O := Nat) (Γ := []) (sort := ())).result f realizedF ≠
            (native (S := base) (O := Nat) (Γ := []) (sort := ())).result g realizedG := by
  obtain ⟨authored, record, budget, differs⟩ := published_differs_from_raw_target fuel
  let f : NativeFiring (templateState locals inners before) := templateFiring authored fuel
  let g : NativeFiring (templateState locals inners before) :=
    ⟨authored.sourceRule.code.lower locals inners before.declarations, authored.selection, authored.outputs,
      authored.sourceRule.ordinaryFlags authored.selection.made, [], fuel, fun _ => none, fun _ _ => rfl⟩
  have realizedF : f.Realized :=
    ⟨ContextualPredicateQueryAdmission.WithQueries.ofPlain _ record.firing, record.authored, record.selected,
      record.values, record.intents, budget, rfl⟩
  have realizedG : g.Realized :=
    ⟨ContextualPredicateQueryAdmission.WithQueries.ofPlain _ record.firing, record.authored, record.selected,
      record.values, record.intents, budget, rfl⟩
  refine ⟨f, g, realizedF, realizedG, rfl, rfl, rfl, rfl, rfl, rfl, fun same => differs ?_⟩
  have resultF : (native (S := base) (O := Nat) (Γ := []) (sort := ())).result f realizedF =
      publishedState (s := templateState locals inners before) (authored.recipes locals inners) record.firing :=
    native_published f realizedF record budget
  have resultG : (native (S := base) (O := Nat) (Γ := []) (sort := ())).result g realizedG =
      rawTarget (s := templateState locals inners before) record.firing :=
    (native_published g realizedG record budget).trans
      (publishedState_none (s := templateState locals inners before) record.firing)
  rw [← resultF, ← resultG]
  exact same

end PublicationControls

#print axioms template_published
#print axioms PublicationControls.published_differs_from_raw_target
#print axioms PublicationControls.native_result_depends_on_recipes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
