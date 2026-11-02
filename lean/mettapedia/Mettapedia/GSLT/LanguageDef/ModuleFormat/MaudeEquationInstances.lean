import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatching
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePreparation

/-! A source valuation produces an actual shared sorted equation instance.
The equation must be output by the row compiler and belong to the prepared
language. This constructs matching, substitution and sorting evidence; it
does not supply equation normalization or conditional-premise decisions. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem equation_unconditional {signature : Maude.Signature} {row : Maude.Row}
    {index : Nat} {equation : Equation} (empty : row.conditions = [])
    (produced : equation? signature index row = some equation) :
    equation.left = encode row.left ∧ equation.right = encode row.right ∧
      equation.premises = [] ∧ equation.bindings = none := by
  simp only [equation?, conditions?, empty, List.mapM_nil, Option.pure_def] at produced
  cases produced
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem unconditional_sorted_instance (base : BasePremiseEvaluator) (prepared : Prepared)
    (ambient : Maude.VariableContext) (row : Maude.Row) (assignment : Maude.Valuation)
    {index : Nat} {equation : Equation}
    (produced : equation? prepared.source.signature index row = some equation)
    (declared : equation ∈ prepared.language.equations)
    (empty : row.conditions = []) (checked : row.check prepared.source.signature = true)
    (inputs : row.inputsBound = true)
    (typed : Maude.TypedValuation prepared.source.signature ambient row.usedContext assignment) :
    OpenSortedEquationInstance (freeContext ambient) base prepared.language
      (encode (row.left.substitute assignment)) (encode (row.right.substitute assignment)) := by
  have bound : ∀ name ∈ row.right.variables, name ∈ row.left.variables := by
    have selected := inputs
    simp only [Maude.Row.inputsBound, List.all_eq_true, List.contains_iff_mem] at selected
    intro name member
    exact selected name (List.mem_append_left _ member)
  obtain ⟨bindings, matched, applied, compatible, _, domain⟩ := match_instance_readout assignment row.left row.right bound
  have sorted := matching_bindings_sorted prepared ambient row.usedContext assignment row.left compatible domain
    (usedContext_distinct checked) (fun _ _ member => usedContext_bound inputs member) typed
  obtain ⟨left, right, premises, raw⟩ := equation_unconditional empty produced
  refine ⟨0, OpenSortedEquationInstanceAt.forward (initialBindings := bindings) (finalBindings := bindings)
    declared (readsRaw_of_none raw) ?_ ?_ ?_ ?_⟩
  · rw [left]
    exact matched
  · rw [premises]
    exact PremisesAt.nil bindings
  · rw [equation_context produced]
    exact sorted
  · rw [right]
    exact applied

theorem unconditional_equation_equivalent (base : BasePremiseEvaluator) (prepared : Prepared)
    (ambient : Maude.VariableContext) (row : Maude.Row) (assignment : Maude.Valuation)
    {index : Nat} {equation : Equation}
    (produced : equation? prepared.source.signature index row = some equation)
    (declared : equation ∈ prepared.language.equations)
    (empty : row.conditions = []) (checked : row.check prepared.source.signature = true)
    (inputs : row.inputsBound = true)
    (typed : Maude.TypedValuation prepared.source.signature ambient row.usedContext assignment) :
    EquationEquiv base prepared.language
      (encode (row.left.substitute assignment)) (encode (row.right.substitute assignment)) :=
  equationEquiv_of_openSortedEquationInstance
    (unconditional_sorted_instance base prepared ambient row assignment produced declared empty checked inputs typed)

theorem prepared_unconditional_sorted_instance (base : BasePremiseEvaluator)
    {theory : Maude.Theory} {prepared : Prepared} (accepted : prepare theory = .ok prepared)
    (ambient : Maude.VariableContext) {row : Maude.Row} {index : Nat}
    (source : (row, index) ∈ theory.equations.zipIdx) (assignment : Maude.Valuation)
    (empty : row.conditions = []) (inputs : row.inputsBound = true)
    (typed : Maude.TypedValuation theory.signature ambient row.usedContext assignment) :
    OpenSortedEquationInstance (freeContext ambient) base prepared.language
      (encode (row.left.substitute assignment)) (encode (row.right.substitute assignment)) := by
  obtain ⟨equation, produced, declared⟩ := authored_equation_member accepted source
  have checked := authored_equation_checked accepted source
  have sourceExact := prepare_source accepted
  rw [← sourceExact] at produced checked typed
  exact unconditional_sorted_instance base prepared ambient row assignment produced declared empty checked inputs typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
