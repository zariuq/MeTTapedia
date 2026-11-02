import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingBasicConversions
import Mettapedia.Languages.MM0.Kernel.DefinitionFreeConversion

/-! # Actual guarded rewriting conversion steps: shared reads and refused invalid conversions -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.ConversionControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open MM0ContextualSupport

def signature : TermSignature := fun _ => none
def definitions : Definition.Signature := fun _ => none
def theorems : TheoremSignature := fun _ => none
def sorts : SortSignature := fun _ => some {}
def context : Context := [.regular 0 ∅, .regular 0 ∅]

theorem context_formed : Context.WellFormed sorts context := by
  apply (Context.check_iff _ _).mp
  decide

theorem first_typed : Preterm.HasType signature context (.var 0) [] 0 := .var (binder := .regular 0 ∅) rfl
theorem second_typed : Preterm.HasType signature context (.var 1) [] 0 := .var (binder := .regular 0 ∅) rfl

theorem repeated_conversion_reads_share_one_occurrence :
    Step ContextualPatterns.layer (BasicConversion.transitivity.rule signature context 0 "trans")
      ({requestValue "trans" [encode context (.var 0), encode context (.var 0), encode context (.var 0)]} +
        {conversionValue context 0 (.var 0) (.var 0)})
      ({conversionValue context 0 (.var 0) (.var 0)} + {conversionValue context 0 (.var 0) (.var 0)}) := by
  exact transitivity_step context_formed "trans" (Converts.refl (definitions := definitions) first_typed)
    (.refl first_typed) _ (by simp) (by simp)

theorem mismatched_middle_cannot_publish_conversion :
    ¬Step ContextualPatterns.layer (BasicConversion.transitivity.rule signature context 0 "trans")
      ({requestValue "trans" [encode context (.var 0), encode context (.var 0), encode context (.var 1)]} +
        {conversionValue context 0 (.var 0) (.var 0), conversionValue context 0 (.var 1) (.var 1)})
      ({conversionValue context 0 (.var 0) (.var 0), conversionValue context 0 (.var 1) (.var 1)} +
        {conversionValue context 0 (.var 0) (.var 1)}) := by
  intro step
  have initial : ∀ value ∈ ({requestValue "trans"
        [encode context (.var 0), encode context (.var 0), encode context (.var 1)]} +
      {conversionValue context 0 (.var 0) (.var 0), conversionValue context 0 (.var 1) (.var 1)} : Multiset Tm),
      ValidValue signature definitions theorems context [] value := by
    intro value member
    have choices : value = requestValue "trans"
        [encode context (.var 0), encode context (.var 0), encode context (.var 1)] ∨
        value = conversionValue context 0 (.var 0) (.var 0) ∨
        value = conversionValue context 0 (.var 1) (.var 1) := by simpa [or_left_comm] using member
    rcases choices with rfl | rfl | rfl
    · exact valid_request _ _ _ _ _ _ _
    · exact valid_conversion (.refl first_typed)
    · exact valid_conversion (.refl second_typed)
  have final := BasicConversion.transitivity.preserves context_formed 0 "trans" initial step
    (conversionValue context 0 (.var 0) (.var 1)) (by simp)
  have impossible := (final.2 0 (.var 0) (.var 1) rfl).eq_of_no_definitions (fun _ => rfl)
  cases impossible

theorem reflexivity_cannot_certify_undeclared_constant :
    ¬Step ContextualPatterns.layer (BasicConversion.reflexivity.rule signature context 0 "refl")
      {requestValue "refl" [encode context (.term 0)]}
      {conversionValue context 0 (.term 0) (.term 0)} := by
  intro step
  have initial : ∀ value ∈ ({requestValue "refl" [encode context (.term 0)]} : Multiset Tm),
      ValidValue signature definitions theorems context [] value := by
    intro value member
    have same : value = requestValue "refl" [encode context (.term 0)] := by simpa using member
    subst value
    exact valid_request _ _ _ _ _ _ _
  have final := BasicConversion.reflexivity.preserves context_formed 0 "refl" initial step
    (conversionValue context 0 (.term 0) (.term 0)) (by simp)
  have typed := (final.2 0 (.term 0) (.term 0) rfl).typed.1
  have computed := typed.eval
  simp [Preterm.infer, signature] at computed

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.ConversionControls
