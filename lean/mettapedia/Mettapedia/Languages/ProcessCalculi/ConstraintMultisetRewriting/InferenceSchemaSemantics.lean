import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaActivation

/-!
# Independent source derivations justify activated inference outputs

Every successful activation retains the existing declarative RuleApplication.
An ordinary firing reads exactly that application's ordered premise values.
The independent source derivation constructor then justifies its output; no
per-rule soundness callback or proof checker is assumed by the runtime step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open InferenceSchemaActivation

def ValidValue (definition : ValidatedCalculusLanguageDef) (value : Tm) : Prop :=
  ∀ pattern, value = judgment pattern → Nonempty (Derivation definition pattern)

theorem valid_judgment {definition : ValidatedCalculusLanguageDef} {pattern : Pattern}
    (derived : Nonempty (Derivation definition pattern)) : ValidValue definition (judgment pattern) := by
  intro other same
  have equal := judgment_injective same
  subst other
  exact derived

theorem valid_request (definition : ValidatedCalculusLanguageDef) (id : RuleId) (rule : RuleSchema)
    (arguments : List Pattern) : ValidValue definition (request id rule arguments) := by
  intro pattern same
  exact False.elim (request_ne_judgment id rule arguments pattern same)

private theorem derivationList_of_each (definition : ValidatedCalculusLanguageDef) (patterns : List Pattern)
    (supplied : ∀ pattern ∈ patterns, Nonempty (Derivation definition pattern)) :
    Nonempty (DerivationList definition patterns) := by
  induction patterns with
  | nil => exact ⟨.nil⟩
  | cons first rest earlier =>
      obtain ⟨head⟩ := supplied first (by simp)
      obtain ⟨tail⟩ := earlier (fun pattern member => supplied pattern (List.mem_cons_of_mem _ member))
      exact ⟨.cons head tail⟩

private theorem read_values {O : Type*} (definition : ValidatedCalculusLanguageDef)
    (assignment : ABTProtectedParameters.Assignment Head 0) (label : O → Tm)
    {values : List Tm} {selected : List O}
    (matched : List.Forall₂ (fun value occurrence => action.E (action.apply assignment value)
      (action.apply assignment (label occurrence))) values selected) :
    (∀ value ∈ values, FixedMatching.Fixed action value) →
    (∀ occurrence ∈ selected, ValidValue definition (action.apply assignment (label occurrence))) →
    ∀ value ∈ values, ValidValue definition value := by
  induction matched with
  | nil => intro _ _ value member; cases member
  | @cons value occurrence values selected same rest earlier =>
      intro fixed incoming result member
      rcases List.mem_cons.mp member with rfl | member
      · change action.apply assignment result = action.apply assignment (label occurrence) at same
        rw [fixed result (by simp) assignment] at same
        rw [same]
        exact incoming occurrence (by simp)
      · exact earlier (fun value member => fixed value (List.mem_cons_of_mem _ member))
          (fun occurrence member => incoming occurrence (List.mem_cons_of_mem _ member)) result member

theorem output_valid {O : Type*} [DecidableEq O] (definition : ValidatedCalculusLanguageDef)
    (id : RuleId) (arguments : List Pattern) {actual : RuleInstance Tm}
    (computed : activate definition id arguments = some actual) (label : O → Tm)
    {before : Configuration Tm O} {picked : Selection O}
    (qualified : picked.Valid action label actual before)
    (assignment : ABTProtectedParameters.Assignment Head 0)
    (solved : action.Models assignment (picked.problem label actual before))
    (incoming : ∀ occurrence ∈ picked.read, ValidValue definition (action.apply assignment (label occurrence))) :
    ∀ occurrence ∈ picked.made, ValidValue definition (action.apply assignment (label occurrence)) := by
  obtain ⟨rule, premises, conclusion, _, localResult, rfl⟩ := origin definition id arguments computed
  have applied : RuleApplication definition ⟨id, arguments⟩ premises conclusion :=
    instantiateRule?_eq_some_iff_application.mp localResult
  have scopes := application_scopes applied
  have sameReads := (Selection.models_problem action qualified solved).2.2.1
  have readValid := read_values definition assignment label sameReads
    (by
      intro value member
      obtain ⟨premise, present, rfl⟩ := List.mem_map.mp member
      exact judgment_fixed premise (scopes.1 premise present)) incoming
  have derivedPremises : ∀ premise ∈ premises, Nonempty (Derivation definition premise) := by
    intro premise present
    exact readValid (judgment premise) (List.mem_map.mpr ⟨premise, present, rfl⟩) premise rfl
  obtain ⟨children⟩ := derivationList_of_each definition premises derivedPremises
  have derived : Nonempty (Derivation definition conclusion) := ⟨.byRule ⟨id, arguments⟩ applied children⟩
  intro occurrence member
  have output : label occurrence = judgment conclusion := by
    have present : label occurrence ∈ picked.made.map label := List.mem_map.mpr ⟨occurrence, member, rfl⟩
    rw [qualified.outputs] at present
    exact List.mem_singleton.mp present
  rw [output, judgment_fixed conclusion scopes.2 assignment]
  exact valid_judgment derived

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaSemantics
