import Mettapedia.OSLF.MeTTaIL.GeneralPremiseAdmission

/-! Ordered premise admission cannot make undeclared output names available.
Its final name set lies in the initial captures and the authored premise
outputs used by the language validator. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax

private theorem query_outputs_subset (arguments : List Pattern) (modes : List RelationArgMode) :
    queryOutputNames arguments modes ⊆ arguments.flatMap Pattern.freeFvarNames := by
  induction arguments generalizing modes with
  | nil => simp [queryOutputNames]
  | cons argument arguments ih =>
    cases modes with
    | nil => simp [queryOutputNames]
    | cons mode modes =>
      cases mode <;> simp only [queryOutputNames,List.zip_cons_cons,List.flatMap_cons]
      · intro name member
        exact List.mem_append_right _ (ih _ member)
      · intro name member
        rcases List.mem_append.mp member with first | later
        · exact List.mem_append_left _ first
        · exact List.mem_append_right _ (ih _ later)

theorem premiseFlow_available (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) (available : List String) (premise : Premise) :
    (premiseFlow language provider rule spec available premise).available ⊆
      available ++ LanguageDef.premiseProducedFvarNames [] premise := by
  cases premise with
  | relationQuery relation arguments =>
    cases found : signature? provider relation arguments.length with
    | none => simpa only [premiseFlow,found] using (List.subset_append_left available (LanguageDef.premiseProducedFvarNames [] (.relationQuery relation arguments)))
    | some signature =>
      intro name member
      simp only [premiseFlow,found] at member
      rcases List.mem_append.mp (List.mem_eraseDups.mp member) with output | old
      · apply List.mem_append_right
        simpa [LanguageDef.premiseProducedFvarNames,LanguageDef.patternFvarNames] using query_outputs_subset arguments signature.modes output
      · exact List.mem_append_left _ old
  | freshness _ => exact List.subset_append_left _ _
  | forAll _ _ _ => exact List.subset_append_left _ _
  | congruence source target =>
    intro name member
    rcases List.mem_append.mp (List.mem_eraseDups.mp member) with output | old
    · apply List.mem_append_right
      simpa [LanguageDef.premiseProducedFvarNames,LanguageDef.patternFvarNames] using output
    · exact List.mem_append_left _ old
  | scopedStep step =>
    intro name member
    rcases List.mem_append.mp (List.mem_eraseDups.mp member) with output | old
    · apply List.mem_append_right
      simpa [LanguageDef.premiseProducedFvarNames,LanguageDef.patternFvarNames] using output
    · exact List.mem_append_left _ old

theorem premisesFlow_available (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec) (available : List String) (premises : List Premise) :
    (premisesFlow language provider rule spec available premises).available ⊆
      available ++ premises.flatMap (LanguageDef.premiseProducedFvarNames []) := by
  induction premises generalizing available with
  | nil => intro _ member; exact List.mem_append_left _ member
  | cons premise premises ih =>
    intro name member
    have later := ih (premiseFlow language provider rule spec available premise).available member
    rcases List.mem_append.mp later with before | tail
    · have earlier := premiseFlow_available language provider rule spec available premise before
      rcases List.mem_append.mp earlier with old | output
      · exact List.mem_append_left _ old
      · exact List.mem_append_right _ (List.mem_append_left _ output)
    · exact List.mem_append_right _ (List.mem_append_right _ tail)

theorem validator_right_bound (language : LanguageDef) (provider : ProviderSnapshot)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (checked : rulePremisesAdmitted language provider rule spec = true) :
    ∀ name ∈ (LanguageDef.patternFvarNames [] rule.right).eraseDups,
      name ∈ LanguageDef.patternFvarNames [] rule.left ++
        rule.premises.flatMap (LanguageDef.premiseProducedFvarNames []) := by
  have available := (Bool.and_eq_true_iff.mp checked).2
  intro name member
  have used : name ∈ rule.right.freeFvarNames := by
    simpa [LanguageDef.patternFvarNames] using List.mem_eraseDups.mp member
  have bound := namesAvailable_sound _ _ available name used
  simpa [LanguageDef.patternFvarNames] using premisesFlow_available language provider rule spec rule.left.freeFvarNames rule.premises bound

#print axioms validator_right_bound

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
