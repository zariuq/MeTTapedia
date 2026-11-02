import Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedRootControls

/-!
# Duplicate private license rows add distinct administrative selections

Both selections are valid for the actual activated source request and have
the same resulting configuration. Logical reachability identifies that result;
enumeration of selection witnesses still distinguishes the two. Canonical
metadata uniqueness is therefore an additional count-preservation obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedMultiplicityControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters.ContextControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (action)
open HOLLightContextActivation (theoremPayload)
open HOLLightLicensedActivation
open HOLLightLicensedExecution
open HOLLightLicensedRootControls (rootRequest rootRequestOccurrence)

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

def firstToken : Occurrence := (10, licenses, available 0)
def secondToken : Occurrence := (11, licenses, available 0)
def output : Occurrence := (12, judgments, theoremPayload 0 identityExistence)
def before : Configuration Value Occurrence := ⟨[], {rootRequestOccurrence, firstToken, secondToken}⟩
def raw : RuleInstance Value := ExactRequestExecution.rule (requests, rootRequest)
  [(licenses, available 0)] [(judgments, theoremPayload 0 identityExistence)]
def picked (token : Occurrence) : Selection Occurrence := ⟨[rootRequestOccurrence], [token], [output]⟩

theorem actual_source_activation : activate emptyAxiomPolicy HOLLightContextControls.TypeDefinition.contexts
    HOLLightLicensedRootControls.entries (.inl 0) (.inl #[]) = some raw :=
  HOLLightLicensedRootControls.root_activated

private theorem valid_at (token : Occurrence)
    (present : token ∈ before.present) (readback : label token = (licenses, available 0)) :
    (picked token).Valid locatedAction label raw before := by
  refine ⟨by simp [picked], by simp [picked], rfl, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨by simp [picked, Selection.commit, before], ?_, ?_, ?_, by simp [picked, Selection.commit]⟩
    · simpa [picked, Selection.commit] using present
    · apply Finset.disjoint_left.mpr
      intro occurrence taken read
      have atRequest : occurrence = rootRequestOccurrence := by simpa [picked, Selection.commit] using taken
      have atToken : occurrence = token := by simpa [picked, Selection.commit] using read
      have impossible : requests = licenses := by
        have same : label rootRequestOccurrence = label token := congrArg label (atRequest.symm.trans atToken)
        exact congrArg Prod.fst (same.trans readback)
      cases impossible
    · simp [picked, Selection.commit, before, output,
        rootRequestOccurrence, firstToken, secondToken]
  · refine ⟨action.identity, ?_⟩
    change locatedAction.Models action.identity ([] ++
      Selection.equations label [label rootRequestOccurrence] [rootRequestOccurrence] ++
      Selection.equations label [(licenses, available 0)] [token] ++ [])
    rw [← readback]
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, true_and, and_true]
    exact ⟨RequestActivation.self_equations locatedAction action.identity label [rootRequestOccurrence],
      RequestActivation.self_equations locatedAction action.identity label [token]⟩
  · intro check member
    cases member

theorem first_valid : (picked firstToken).Valid locatedAction label raw before :=
  valid_at firstToken (by simp [before]) rfl

theorem second_valid : (picked secondToken).Valid locatedAction label raw before :=
  valid_at secondToken (by simp [before]) rfl

theorem selections_are_distinct : (picked firstToken).read ≠ (picked secondToken).read := by
  intro same
  have equal : firstToken = secondToken := List.singleton_inj.mp same
  have impossible : (10 : Nat) = 11 := congrArg Prod.fst equal
  omega

theorem same_result : (picked firstToken).result label raw before = (picked secondToken).result label raw before := rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedMultiplicityControls
