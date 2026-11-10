import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

/-!
# Exact HE minimal-chain activation and continuation

The source relation carries the context space, type service, live scope, caller
origin and binding frame. A chain first runs its source in the extended live
scope, materializes that source occurrence, then runs the substituted template.
The inversion laws below retain these indices; they do not identify this
read-only minimal profile with the state-writing HE evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEChainContexts

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Minimal

def chain (source : Atom) (name : String) (template : Atom) : Atom :=
  .expression [.symbol "chain", source, .var name, template]

theorem chain_step_exact
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {scope : List String} {typing : EvalTypeService} {caller : Option Atom}
    {source template : Atom} {name : String} {incoming : BindingFrame} {result : FrameResult} :
    CoreStepRel space dispatch live (chain source name template) incoming result
        (protectedScope := scope) (typing := typing) (caller := caller) ↔
      ∃ selected materialized,
        CoreRunRel space dispatch (chain source name template :: live) source incoming selected
          (protectedScope := scope) (typing := typing) (caller := some (chain source name template)) ∧
        BindingFrame.Materialization selected.2 selected.1 materialized ∧
        result = (substituteName name materialized template, selected.2) := by
  constructor
  · intro step
    generalize sourceEq : chain source name template = term at step
    cases step <;> simp_all [chain]
    rename_i atom' name' template' selected materialized materialization produced
    exact ⟨selected.1, produced, materialized, materialization, rfl⟩
  · rintro ⟨selected, materialized, produced, materialization, rfl⟩
    exact .chain _ _ _ _ _ _ _ produced materialization

/-- Both directions include the template's actual continuation and its reached frame. -/
theorem chain_run_exact
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {scope : List String} {typing : EvalTypeService} {caller : Option Atom}
    {source template : Atom} {name : String} {incoming : BindingFrame} {result : FrameResult} :
    CoreRunRel space dispatch live (chain source name template) incoming result
        (protectedScope := scope) (typing := typing) (caller := caller) ↔
      ∃ selected materialized,
        CoreRunRel space dispatch (chain source name template :: live) source incoming selected
          (protectedScope := scope) (typing := typing) (caller := some (chain source name template)) ∧
        BindingFrame.Materialization selected.2 selected.1 materialized ∧
        CoreRunRel space dispatch live (substituteName name materialized template) selected.2 result
          (protectedScope := scope) (typing := typing) (caller := caller) := by
  constructor
  · intro running
    cases running with
    | data _ _ _ terminal => simp [chain, embeddedInstruction] at terminal
    | instruction _ _ _ _ _ notChain _ => exact False.elim (notChain ⟨_, rfl⟩)
    | chain _ _ _ activated _ _ stepped continued =>
        obtain ⟨selected, materialized, produced, materialization, same⟩ := chain_step_exact.mp stepped
        subst activated
        exact ⟨selected, materialized, produced, materialization, continued⟩
  · rintro ⟨selected, materialized, produced, materialization, continued⟩
    exact .chain _ _ _ _ _ ⟨_, rfl⟩
      (chain_step_exact.mpr ⟨selected, materialized, produced, materialization, rfl⟩) continued

/-- If the materialized template is data, the continuation returns exactly that data and frame. -/
theorem chain_data_exact
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {scope : List String} {typing : EvalTypeService} {caller : Option Atom}
    {source template : Atom} {name : String} {incoming : BindingFrame} {result : FrameResult}
    (held : ∀ value, embeddedInstruction (substituteName name value template) = false) :
    CoreRunRel space dispatch live (chain source name template) incoming result
        (protectedScope := scope) (typing := typing) (caller := caller) ↔
      ∃ selected materialized,
        CoreRunRel space dispatch (chain source name template :: live) source incoming selected
          (protectedScope := scope) (typing := typing) (caller := some (chain source name template)) ∧
        BindingFrame.Materialization selected.2 selected.1 materialized ∧
        result = (substituteName name materialized template, selected.2) := by
  rw [chain_run_exact]
  constructor
  · rintro ⟨selected, materialized, produced, materialization, continued⟩
    refine ⟨selected, materialized, produced, materialization, ?_⟩
    cases continued with
    | data => rfl
    | instruction _ _ _ _ embedded _ _ => simp [held _] at embedded
    | chain _ _ _ _ _ isChain _ _ =>
        obtain ⟨tail, same⟩ := isChain
        have known := held materialized
        rw [same] at known
        simp [embeddedInstruction] at known
  · rintro ⟨selected, materialized, produced, materialization, rfl⟩
    exact ⟨selected, materialized, produced, materialization, .data _ _ _ (held _)⟩

end Mettapedia.Languages.MeTTa.ContextualTransform.HEChainContexts
