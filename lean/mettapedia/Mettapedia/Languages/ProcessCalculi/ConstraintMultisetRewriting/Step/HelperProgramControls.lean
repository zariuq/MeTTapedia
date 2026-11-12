import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperProgramBisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchangeControls

/-!
# Contextual event congruence with actual native histories

Two selected programs coexist beside the old forty-two declaration. Changing
the left output identity preserves the declared event observation and its
contextual bisimilarity. Both execution orders compile to actual native
two-event runs. The two initial event origins cannot be replaced by the
single pending event of any one selected local program.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ProgramControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open EventMultiplicity
open Helpers.Consumer (tiny start first constant)
open TensorInterchangeControls (second)

def initial : ContextProgram tiny Nat :=
  ⟨⟨start, TensorInterchangeControls.first⟩, ⟨ContextResultControls.context, second⟩,
    ContextResultControls.placed, TensorInterchangeControls.before_domain⟩

def leftHead : Program.Head initial.left := .cons first ResidualRunExchangeControls.first_admitted (.nil _)
def rightHead : Program.Head initial.right := .cons TensorRunsControls.rightFiring TensorRunsControls.right_allowed (.nil _)

def leftChoice : initial.Choice := initial.choiceEquiv (.inl leftHead)
def rightChoice : initial.Choice := initial.choiceEquiv (.inr rightHead)

theorem origins_distinct : leftChoice ≠ rightChoice := by
  intro same
  have origins := congrArg Subtype.val same
  cases origins

def alternateFiring : Firing start := ⟨4, ([], ()), constant 7, []⟩

theorem alternate_allowed : helperStep.Admits alternateFiring :=
  (admits_iff alternateFiring).mpr ⟨Helpers.Consumer.start_solvable, by decide, asks_nil⟩

def alternateRun : helperStep.Run start := .cons alternateFiring alternate_allowed (.nil _)

theorem alternate_domain : TensorDomain ContextResultControls.placed alternateRun second :=
  ⟨Or.inr ContextResultControls.placed_solvable,
    (outputsAvoid_iff_disjoint _ _).mpr (by decide), (outputsAvoid_iff_disjoint _ _).mpr (by decide)⟩

def alternate : ContextProgram tiny Nat :=
  ⟨⟨start, alternateRun⟩, initial.right, ContextResultControls.placed, alternate_domain⟩

theorem components_distinct : initial.left ≠ alternate.left := by
  intro same
  have ids := congrArg (fun program : Program tiny Nat => program.run.word.map (fun entry => entry.2.made)) same
  change [1] = [4] at ids
  cases ids

theorem contextual_congruence : Bisimilar ContextProgram.system initial ContextProgram.system alternate :=
  ContextProgram.parallel_congruence initial alternate (Program.bisimilar_of_word rfl) (Bisimilar.refl _ _)

def leftThenRight : (asynchronous Program.system Program.system).Execution 2 initial.project :=
  ⟨.inl leftHead, ⟨.inr rightHead, PUnit.unit⟩⟩

def rightThenLeft : (asynchronous Program.system Program.system).Execution 2 initial.project :=
  ⟨.inr rightHead, ⟨.inl leftHead, PUnit.unit⟩⟩

def nativeLeftRight := ContextProgram.realizeComponents leftThenRight
def nativeRightLeft := ContextProgram.realizeComponents rightThenLeft

theorem actual_native_lengths : nativeLeftRight.execution.word.length = 2 ∧ nativeRightLeft.execution.word.length = 2 :=
  ⟨nativeLeftRight.length_preserved, nativeRightLeft.length_preserved⟩

theorem native_left_right_word : helperWord nativeLeftRight.execution = [([], ()), ([()], ())] :=
  ContextProgram.component_word leftThenRight

theorem native_right_left_word : helperWord nativeRightLeft.execution = [([()], ()), ([], ())] :=
  ContextProgram.component_word rightThenLeft

theorem native_histories_distinct : nativeLeftRight.execution ≠ nativeRightLeft.execution := by
  intro same
  have words := congrArg helperWord same
  rw [native_left_right_word, native_right_left_word] at words
  have arities := congrArg (fun word => word.map (fun helper => helper.1.length)) words
  change [0, 1] = [1, 0] at arities
  cases arities

theorem two_origins_not_one_pending_program (program : Program tiny Nat) :
    ¬Bisimilar ContextProgram.system initial Program.system program := by
  rintro ⟨_, ⟨comparison⟩, related⟩
  exact origins_distinct ((comparison.choices related).injective (Program.Head.unique _ _))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ProgramControls
