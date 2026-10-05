import Mettapedia.Languages.MM0.Presentation.ObligationGSLT
import Mettapedia.Languages.MM0.Presentation.KernelFormation

/-! # Ordered local resolution, completed refusals and no invented proofs -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalObligations.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open ComputationalProof ComputationalConversion ComputationalAdmission
open Mettapedia.GSLT Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def declaration : TheoremDecl := ⟨[], [.term 0, .term 0, .term 1], .term 2⟩
private def theory : Theory :=
  { sorts := [(0, { provable := true })]
    terms := [(0, ⟨[], 0, ∅⟩), (1, ⟨[], 0, ∅⟩), (2, ⟨[], 0, ∅⟩)]
    theorems := [(0, declaration)] }
private def context : Context := []
private def hypotheses : List Preterm := [.term 0, .term 1]
private def unfoldingTheory : Theory := { theory with definitions := [(0, ⟨[], .term 1⟩)] }

theorem theorem_step_retains_order_multiplicity_and_suffix (suffix : List Preterm) :
    Resolves theory context hypotheses (.term 2 :: suffix)
      (.term 0 :: .term 0 :: .term 1 :: suffix) := by
  exact .theoremApp ((theorem_query_exact _ 0 declaration).mpr rfl)
    ((instance_query_exact _ _ _ [] ⟨[.term 0, .term 0, .term 1], .term 2⟩).mpr
      ((TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp (by decide +kernel)))

theorem duplicate_premises_have_a_complete_finite_discharge :
    (obligationGSLT theory context hypotheses).MultiStep [.term 2] [] := by
  refine .step (theorem_step_retains_order_multiplicity_and_suffix []) ?_
  refine .step (.hypothesis ((hypothesis_query_exact _ 0 _).mpr rfl)) ?_
  refine .step (.hypothesis ((hypothesis_query_exact _ 0 _).mpr rfl)) ?_
  exact .step (.hypothesis ((hypothesis_query_exact _ 1 _).mpr rfl))
    (@GSLT.MultiStep.refl (obligationGSLT theory context hypotheses) [])

theorem conversion_is_local_and_retains_its_premise (suffix : List Preterm) :
    Resolves theory context hypotheses (.term 0 :: suffix) (.term 0 :: suffix) := by
  apply Resolves.conversion (witness := .refl (.term 0)) (sort := 0)
  apply (conversion_query_exact _ _ _ _ _ _).mpr
  exact .refl (by apply Preterm.infer_sound; decide +kernel)

theorem unfolding_resolves_a_distinct_goal_to_its_actual_premise :
    Resolves unfoldingTheory context [.term 0] [.term 1] [.term 0] ∧
      ¬ (obligationGSLT unfoldingTheory context [.term 0]).Equiv [.term 1] [.term 0] := by
  constructor
  · apply Resolves.conversion (witness := .unfold 0 [] []) (sort := 0)
    apply (conversion_query_exact _ _ _ _ _ _).mpr
    apply ConvWitness.conversion_sound (result := ⟨.term 0, .term 1, 0⟩)
    decide +kernel
  · intro same
    cases same

theorem changed_definition_does_not_authorize_old_conversion :
    ¬ Applies admissionProgram dataEqualityHost "mm0:conversion"
      [encodeTable theory.terms, encodeDefinitions [(0, ⟨[], .term 2⟩)], encodeContext context,
        ComputationalConversion.encodeWitness (.unfold 0 [] [])]
      (encodeConversion (some ⟨.term 0, .term 1, 0⟩)) := by
  intro accepted
  have computed := ((conversion_query_exact
    { theory with definitions := [(0, ⟨[], .term 2⟩)] } context (.unfold 0 [] []) _ _ _).mp accepted).eval
  have actual : ConvWitness.conversion? theory.termSignature
      (Theory.definitionSignature { theory with definitions := [(0, ⟨[], .term 2⟩)] })
      context (.unfold 0 [] []) = some ⟨.term 0, .term 2, 0⟩ := by decide +kernel
  change ConvWitness.conversion? theory.termSignature
      (Theory.definitionSignature { theory with definitions := [(0, ⟨[], .term 2⟩)] })
      context (.unfold 0 [] []) = some ⟨.term 0, .term 1, 0⟩ at computed
  rw [actual] at computed
  cases computed

theorem wrong_theorem_premise_order_is_not_authorized :
    ¬ Applies admissionProgram dataEqualityHost "mm0:instantiate-theorem"
      [encodeTable theory.terms, encodeContext context, encodeTheorem declaration, encodeExpressions []]
      (encodeInstance (some ⟨[.term 1, .term 0, .term 0], .term 2⟩)) := by
  intro accepted
  have computed := ((instance_query_exact _ _ _ _ _).mp accepted).eval
  have correct : declaration.instantiate? theory.termSignature context [] =
      some ⟨[.term 0, .term 0, .term 1], .term 2⟩ := by decide +kernel
  rw [correct] at computed
  cases computed

theorem missing_duplicate_premise_is_not_authorized :
    ¬ Applies admissionProgram dataEqualityHost "mm0:instantiate-theorem"
      [encodeTable theory.terms, encodeContext context, encodeTheorem declaration, encodeExpressions []]
      (encodeInstance (some ⟨[.term 0, .term 1], .term 2⟩)) := by
  intro accepted
  have computed := ((instance_query_exact _ _ _ _ _).mp accepted).eval
  have correct : declaration.instantiate? theory.termSignature context [] =
      some ⟨[.term 0, .term 0, .term 1], .term 2⟩ := by decide +kernel
  rw [correct] at computed
  cases computed

theorem foreign_theorem_lookup_is_not_authorized :
    ¬ Applies admissionProgram dataEqualityHost "nik:nat-table-get"
      [encodeTheorems ([] : TheoremTable), natural 0]
      (encodeLookupResult (some (encodeTheorem declaration))) := by
  intro accepted
  have lookup := (theorem_query_exact ({} : Theory) 0 declaration).mp accepted
  cases lookup

theorem discharged_state_cannot_invent_a_new_obligation (target : List Preterm) :
    ¬ Resolves theory context hypotheses [] target :=
  fun step => step.nonempty_source rfl

theorem empty_theory_cannot_discharge_an_unproved_goal (goal : Preterm) :
    ¬ (obligationGSLT {} [] []).MultiStep [goal] [] := by
  intro discharged
  have derived := (singleton_discharge_iff ({} : Theory) [] [] goal).mp discharged
  clear discharged
  induction derived using Derives.rec (motive_2 := fun goals _ => goals = []) with
  | hypothesis member => cases member
  | theoremApp lookup _ _ _ => cases lookup
  | conversion _ _ ih => exact ih
  | nil => rfl
  | cons _ _ impossible _ => exact False.elim impossible

theorem completed_discharge_has_the_generated_native_type :
    (gsltOSLF (obligationGSLT theory context hypotheses)).satisfies [.term 2]
      (derivableNativeType theory context hypotheses).pred :=
  duplicate_premises_have_a_complete_finite_discharge

theorem native_type_has_an_actual_checked_witness :
    ∃ proof, Applies admissionProgram dataEqualityHost "mm0:check-proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, encodeProof proof, encode (.term 2)] (.sym "True") :=
  (KernelFormation.checked_entry_derivable theory context hypotheses (.term 2)).mpr
    ((singleton_discharge_iff _ _ _ _).mp duplicate_premises_have_a_complete_finite_discharge)

end Mettapedia.Languages.MM0.Presentation.ComputationalObligations.Controls
