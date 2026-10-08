import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenControls

/-!
# Full categorical function, scope and collision controls

Actual categorical arrows read independent supplied return-sensitive
programs, a received argument and return pair, and a definition whose stored
value retains its original scope. A noninjective ambient substitution
identifies old names while leaving the return binder distinct. Whole source
scope equations are tested as natural-transformation equalities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler.Controls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation NamePassingConstructorInterpretation

abbrev Γ := NamePassingOpenInterpretation.Controls.sourceScope
abbrev Δ := NamePassingOpenInterpretation.Controls.targetScope
abbrev inputs := NamePassingOpenInterpretation.Controls.environment
abbrev first := NamePassingOpenInterpretation.Controls.firstHole
abbrev name := NamePassingOpenInterpretation.Controls.referenceName
abbrev returnName := NamePassingOpenInterpretation.Controls.secondReturn

def currentCall (term : NamePassing.Presentation.Program Γ) (result : Name Δ) : TermQ equations Δ .pr :=
  programsAtEquiv algebra .pr (stage Δ)
    (((meaning operations term).app (stage Δ) (contextPoint inputs)).app
      (stage Δ) (𝟙 _) (rawPoint result))

theorem actual_first_return :
    currentCall first NamePassingOpenInterpretation.Controls.firstReturn =
      Quotient.mk _ (out1 (.var .zero) (.var (.succ .zero))) := by
  rw [currentCall, current_readout, NamePassingOpenInterpretation.Controls.first_program_readout]

theorem actual_second_return :
    currentCall first returnName = Quotient.mk _ (out1 (.var (.succ .zero)) (.var (.succ .zero))) := by
  rw [currentCall, current_readout, NamePassingOpenInterpretation.Controls.changed_program_return]

/-- This calculation reads the entire supplied categorical return function,
not a selected immediate-return observation. -/
theorem actual_whole_program_body :
    scopedBodyEquiv algebra (stage Δ).unop [.nm] .pr
      ((meaning operations first).app (stage Δ) (contextPoint inputs)) =
      (Quotient.mk _ (out1 (.var .zero) (.var (.succ (.succ .zero)))) :
        TermQ equations (.nm :: Δ) .pr) := by
  rw [whole_body_readout]
  simp only [NamePassingOpenInterpretation.Controls.firstHole, interpret]
  rfl

def collision : Sub sig Δ Δ
  | _, .zero => .var .zero
  | _, .succ .zero => .var .zero

theorem actual_future_collision :
    programsAtEquiv algebra .pr (stage Δ)
      (((meaning operations first).app (stage Δ) (contextPoint inputs)).app
        (stage Δ) (rawChange collision) (rawPoint (.var .zero))) =
      Quotient.mk _ (out1 (.var .zero) (.var .zero)) := by
  rw [future_readout]
  simp only [NamePassingOpenInterpretation.Controls.firstHole, interpret]
  rfl

theorem actual_future_retains_return_binder :
    scopedBodyEquiv algebra (stage Δ).unop [.nm] .pr
      (operations.termObject.map (rawChange collision)
        ((meaning operations first).app (stage Δ) (contextPoint inputs))) =
      (Quotient.mk _ (out1 (.var .zero) (.var (.succ .zero))) : TermQ equations (.nm :: Δ) .pr) := by
  rw [meaning_substitution, whole_body_readout]
  simp only [NamePassingOpenInterpretation.Controls.firstHole, interpret]
  rfl

def expectedDefinition : Proc Δ :=
  nu (par (out1 (.var .zero) (.var (.succ (.succ .zero))))
    (rep (inp1 (.var .zero)
      (out1 (.var .zero) (.var (.succ (.succ (.succ .zero))))))))

theorem actual_stored_value_scope :
    currentCall (NamePassing.Presentation.definition first
      (NamePassing.Presentation.reference (.var .zero))) returnName =
      Quotient.mk _ expectedDefinition := by
  rw [currentCall, current_readout]
  simp only [NamePassing.Presentation.definition, NamePassing.Presentation.reference, interpret,
    NamePassingOpenInterpretation.Controls.firstHole]
  rfl

def expectedReceived : Proc (.nm :: .nm :: Δ) :=
  nu (par (out1 (.var .zero) (.var (.succ (.succ (.succ (.succ .zero))))))
    (out2 (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))))

theorem actual_both_received_positions :
    currentCall (NamePassing.Presentation.abstraction NamePassingOpenInterpretation.Controls.body) returnName =
      Quotient.mk _ (inp2 returnName expectedReceived) := by
  rw [currentCall, current_readout]
  simp only [NamePassing.Presentation.abstraction, NamePassingOpenInterpretation.Controls.body,
    NamePassing.Presentation.application, interpret]
  rfl

theorem ordered_names_distinct {context : Ctx sig} {first second : Name context}
    (different : first ≠ second) : rawPoint first ≠ rawPoint second := by
  intro same
  have classes := congrArg (programsAtEquiv algebra .nm (stage context)) same
  rw [rawPoint_readout, rawPoint_readout] at classes
  exact different ((AuthoredEquations.name_eqClosure_iff _ _).mp (Quotient.exact classes))

/-- The two received positions remain distinct in the actual name object. -/
theorem received_argument_not_return :
    rawPoint (.var .zero : Name (.nm :: .nm :: Δ)) ≠ rawPoint (.var (.succ .zero)) := by
  apply ordered_names_distinct
  intro same
  cases same

theorem identified_names :
    operations.names.map (rawChange collision) (rawPoint (.var .zero : Name Δ)) =
      operations.names.map (rawChange collision) (rawPoint (.var (.succ .zero) : Name Δ)) := by
  rw [rawPoint_substitution, rawPoint_substitution]
  rfl

/-- Genuine variable identification has no inverse on the actual old name
values; no origin decoder is claimed from their identified image. -/
theorem collision_has_no_name_decoder :
    ¬ ∃ decode : operations.names.obj (stage Δ) → operations.names.obj (stage Δ),
      ∀ value, decode (operations.names.map (rawChange collision) value) = value := by
  rintro ⟨decode, correct⟩
  have same := (correct (rawPoint (.var .zero : Name Δ))).symm.trans
    ((congrArg decode identified_names).trans (correct (rawPoint (.var (.succ .zero) : Name Δ))))
  exact ordered_names_distinct (by intro equal; cases equal) same

theorem return_not_old_name_after_collision :
    rawPoint (.var .zero : Name (.nm :: Δ)) ≠ rawPoint (.var (.succ .zero)) := by
  apply ordered_names_distinct
  intro same
  cases same

theorem actual_carrier_scope_equation :
    meaning operations (NamePassing.Presentation.application
      (NamePassing.Presentation.carrier name first first) name) =
      meaning operations (NamePassing.Presentation.carrier name first
        (NamePassing.Presentation.application first name)) :=
  static_arrow (.appCarrier _ _ _ _)

theorem actual_definition_scope_equation :
    meaning operations (NamePassing.Presentation.application
      (NamePassing.Presentation.definition first
        (NamePassing.Presentation.reference (.var .zero))) name) =
      meaning operations (NamePassing.Presentation.definition first
        (NamePassing.Presentation.application (NamePassing.Presentation.reference (.var .zero))
          (weaken name))) :=
  static_arrow (.appDefinition _ _ _)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler.Controls
