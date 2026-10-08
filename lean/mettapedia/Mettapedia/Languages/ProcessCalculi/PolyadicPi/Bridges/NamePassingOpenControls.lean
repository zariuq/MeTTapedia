import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenReduction
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenCompilerComparison

/-!
# Ordinary term holes and distinct call binders

Two independently supplied program bodies use their return name differently.
A full source substitution replaces one hole by an application of the other.
The computed target messages retain those uses, including beneath the received
reference binder. Swapping the argument and return names changes the actual
received process.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

abbrev sourceScope : Ctx NamePassing.Presentation.signature := [.tm, .tm, .nm]
abbrev targetScope : Ctx sig := [.nm, .nm]

def environment : Environment sourceScope targetScope where
  name := fun name => match name with
    | .succ (.succ .zero) => .var .zero
  program := fun term => match term with
    | .zero => out1 (.var .zero) (.var (.succ (.succ .zero)))
    | .succ .zero => out1 (.var (.succ .zero)) (.var .zero)

def firstHole : NamePassing.Presentation.Program sourceScope := .var .zero
def secondHole : NamePassing.Presentation.Program sourceScope := .var (.succ .zero)
def referenceName : NamePassing.Presentation.Name sourceScope := .var (.succ (.succ .zero))
def firstReturn : Name targetScope := .var .zero
def secondReturn : Name targetScope := .var (.succ .zero)

theorem first_program_readout :
    interpret firstHole environment firstReturn = out1 (.var .zero) (.var (.succ .zero)) := by
  simp only [firstHole, interpret]
  rfl

theorem changed_program_return :
    interpret firstHole environment secondReturn = out1 (.var (.succ .zero)) (.var (.succ .zero)) := by
  simp only [firstHole, interpret]
  rfl

theorem complete_program_body_uses_its_return :
    interpret firstHole environment firstReturn ≠ interpret firstHole environment secondReturn := by
  rw [first_program_readout, changed_program_return]
  intro same
  cases same

theorem second_program_readout :
    interpret secondHole environment secondReturn = out1 (.var .zero) (.var (.succ .zero)) := by
  simp only [secondHole, interpret]
  rfl

def filling : Sub NamePassing.Presentation.signature sourceScope sourceScope
  | _, .zero => NamePassing.Presentation.application secondHole referenceName
  | _, .succ .zero => secondHole
  | _, .succ (.succ .zero) => referenceName

def suppliedCall : Proc targetScope :=
  nu (par (out1 (.var (.succ .zero)) (.var .zero))
    (out2 (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))))

theorem filled_hole_readout :
    interpret (Mettapedia.OSLF.Binding.bind filling firstHole) environment secondReturn = suppliedCall := by
  simp only [firstHole, Mettapedia.OSLF.Binding.bind, filling, NamePassing.Presentation.application, secondHole, interpret]
  rfl

/-- The independently interpreted source substitution has the same complete
application process, including its fresh call name and supplied return. -/
theorem source_substitution_environment_readout :
    interpret firstHole (environment.sourceSubstitute filling) secondReturn = suppliedCall := by
  rw [← interpret_source_substitution]
  exact filled_hole_readout

def body : NamePassing.Presentation.Program (.nm :: sourceScope) :=
  NamePassing.Presentation.application (.var (.succ .zero)) (.var .zero)

theorem instantiated_source_readout :
    inst body referenceName = NamePassing.Presentation.application firstHole referenceName := rfl

def expectedBetaTarget : Proc targetScope :=
  nu (par (out1 (.var .zero) (.var (.succ (.succ .zero))))
    (out2 (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))))

theorem computed_beta_target :
    interpret (inst body referenceName) environment secondReturn = expectedBetaTarget := by
  rw [instantiated_source_readout]
  simp only [NamePassing.Presentation.application, firstHole, interpret]
  rfl

theorem actual_beta_firing :
    StepModulo (interpret (NamePassing.Presentation.application
      (NamePassing.Presentation.abstraction body) referenceName) environment secondReturn) expectedBetaTarget := by
  rw [← computed_beta_target]
  exact beta_preserved body referenceName environment secondReturn

theorem whole_received_body_readout :
    openPair (interpret body ((environment.substitute weakening).substitute weakening).lift (.var (.succ .zero)))
      (weaken (interpretName referenceName environment)) (weaken secondReturn) = weaken expectedBetaTarget := by
  rw [beta_endpoint, computed_beta_target]

def exchangedBetaTarget : Proc targetScope :=
  nu (par (out1 (.var .zero) (.var (.succ (.succ .zero))))
    (out2 (.var .zero) (.var (.succ (.succ .zero))) (.var (.succ .zero))))

theorem exchanged_names_have_different_readout : expectedBetaTarget ≠ exchangedBetaTarget := by
  intro same
  cases same

theorem real_fetch_of_supplied_program :
    Step (interpret (NamePassing.Presentation.carrier referenceName firstHole
        (NamePassing.Presentation.reference referenceName)) environment secondReturn)
      (out1 (.var (.succ .zero)) (.var (.succ .zero))) := by
  rw [← changed_program_return]
  exact fetch_preserved referenceName firstHole environment secondReturn

theorem ordinary_hole_is_not_a_reference :
    firstHole ≠ NamePassing.Presentation.reference referenceName := by
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation.Controls
