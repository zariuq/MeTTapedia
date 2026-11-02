import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation

/-! # Exact source judgment soundness of actual selected registered firings -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextSemantics

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic
open InferenceSchemaActivation (Tm action)
open InferenceSchemaKernel (Space Value locatedAction)
open HOLLightContextActivation

def ValidValue (policy : AxiomPolicy) (contexts : Nat → TheoryContext) (value : Tm) : Prop :=
  ∀ context fact, value = theoremPayload context fact → TheoryDerives policy (contexts context) fact

def ValidLocated (policy : AxiomPolicy) (contexts : Nat → TheoryContext) (value : Value) : Prop :=
  value.1 = .judgments → ValidValue policy contexts value.2

theorem valid_theorem (policy : AxiomPolicy) (contexts : Nat → TheoryContext)
    (context : Nat) (fact : Theorem) (derived : TheoryDerives policy (contexts context) fact) :
    ValidValue policy contexts (theoremPayload context fact) := by
  intro otherContext other same
  obtain ⟨rfl, rfl⟩ := theoremPayload_injective same
  exact derived

private theorem read_values {O : Type*} (policy : AxiomPolicy) (contexts : Nat → TheoryContext)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) (label : O → Value)
    {values : List Value} {selected : List O}
    (matched : List.Forall₂ (fun value occurrence => locatedAction.E (locatedAction.apply assignment value)
      (locatedAction.apply assignment (label occurrence))) values selected)
    (fixed : ∀ value ∈ values, FixedMatching.Fixed locatedAction value)
    (incoming : ∀ occurrence ∈ selected, ValidLocated policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ value ∈ values, ValidLocated policy contexts value := by
  induction matched with
  | nil => intro value member; cases member
  | @cons value occurrence values selected same rest earlier =>
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · have equal : locatedAction.apply assignment result = locatedAction.apply assignment (label occurrence) :=
          Prod.ext same.1 same.2
        rw [fixed result (by simp) assignment] at equal
        rw [equal]
        exact incoming occurrence (by simp)
      · exact earlier (fun value member => fixed value (List.mem_cons_of_mem _ member))
          (fun occurrence member => incoming occurrence (List.mem_cons_of_mem _ member)) result member

theorem output_valid {O : Type*} [DecidableEq O] (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (entries : Nat → Option (Entry contexts))
    (source : Nat) (cache : Array Theorem) {raw : RuleInstance Value}
    (computed : activate policy contexts entries source cache = some raw) (label : O → Value)
    {before : Configuration Value O} {picked : Selection O}
    (qualified : picked.Valid locatedAction label raw before)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0)
    (solved : locatedAction.Models assignment (picked.problem label raw before))
    (incoming : ∀ occurrence ∈ picked.read, ValidLocated policy contexts (locatedAction.apply assignment (label occurrence))) :
    ∀ occurrence ∈ picked.made, ValidLocated policy contexts (locatedAction.apply assignment (label occurrence)) := by
  obtain ⟨entry, output, parents, _, checked, selected, contextSame, rfl⟩ :=
    origin policy contexts entries source cache computed
  have sameReads := (Selection.models_problem locatedAction qualified solved).2.2.1
  have readValid := read_values policy contexts assignment label sameReads (by
    intro value member
    obtain ⟨fact, _, rfl⟩ := List.mem_map.mp member
    intro substitution
    change (Space.judgments, action.apply substitution (theoremPayload entry.before fact)) = _
    rw [theoremPayload_fixed]) incoming
  have prior : ∀ index ∈ entry.command.parents, ∀ fact,
      cache[index]? = some fact → TheoryDerives policy (contexts entry.before) fact := by
    intro index cited fact found
    have member := DerivationGraph.lookupPremises_cited cache selected index cited fact found
    exact readValid (.judgments, theoremPayload entry.before fact)
      (List.mem_map.mpr ⟨fact, member, rfl⟩) rfl entry.before fact rfl
  have sourceOutput := (HOLLightSelectedAdmission.check_sound_selected policy _ _ _ prior checked).2
  intro occurrence made
  have member : label occurrence ∈ (fromResult source entry cache parents output).produce := by
    rw [← qualified.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
  obtain ⟨fact, factMember, labelSame⟩ := List.mem_map.mp member
  rw [← labelSame]
  change Space.judgments = Space.judgments →
    ValidValue policy contexts (action.apply assignment (theoremPayload entry.after fact))
  rw [theoremPayload_fixed]
  intro _
  apply valid_theorem
  rw [← contextSame]
  exact sourceOutput fact factMember

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextSemantics
