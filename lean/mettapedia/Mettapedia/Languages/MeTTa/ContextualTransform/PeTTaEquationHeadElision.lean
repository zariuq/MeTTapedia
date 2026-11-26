import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStaticHeadElision
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables
import Mettapedia.Languages.TuringMachine.InputEncoding

/-!
# Static constructor elision with a finite PeTTa equation table

Take the project's deterministic universal table of PeTTa equations. Supply
an input and a bound. Starting from its initial configuration, install the
equation for `S` if the table reaches a terminal configuration within that
bound. This connects safety of the same residual program to the existing
PeTTa equation-step and halting judgments. Each bounded test takes at most
the supplied number of transitions followed by a terminal-state test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaEquationHeadElision

open Mettapedia.Languages.TuringMachine
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine
open PeTTaStaticHeadElision (SafeForAll safeForAll_iff)
open Nat.Partrec (Code)

def installsWithin (machine : Machine) (initial : Configuration) (bound : Nat) : Bool :=
  (machine.next? (machine.runFor bound initial)).isNone

private theorem reached_at_bound {machine : Machine} {first last : Configuration}
    (path : StateTransition.Reaches machine.next? first last) :
    ∃ bound, machine.runFor bound first = last := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head step _ ih =>
    obtain ⟨bound, reached⟩ := ih
    exact ⟨bound + 1, by simpa only [Machine.runFor, Option.mem_def.mp step] using reached⟩

/-- Eventual installation is exactly termination in the authored equation
kernel, including the case where the initial term is already terminal. -/
theorem installs_iff_equationHalts (machine : Machine) (deterministic : machine.Deterministic)
    (initial : Configuration) :
    (∃ bound, installsWithin machine initial bound = true) ↔
      Tables.EquationHalts machine initial.term := by
  rw [Tables.equationHalts_iff]
  constructor
  · rintro ⟨bound, observed⟩
    have stopped : machine.next? (machine.runFor bound initial) = none :=
      Option.isNone_iff_eq_none.mp observed
    exact ⟨_, machine.reaches_runFor bound initial, Machine.halted_of_next?_eq_none stopped⟩
  · rintro ⟨term, path, normal⟩
    obtain ⟨last, rfl, steps⟩ := MathlibBridge.reaches_next_reflect machine deterministic path
    obtain ⟨bound, reached⟩ := reached_at_bound steps
    refine ⟨bound, ?_⟩
    simp [installsWithin, reached, (MathlibBridge.next_none_iff_halted machine last).mpr normal]

noncomputable abbrev table := PartrecBridge.machine Mettapedia.Languages.PartrecMachine.universal

noncomputable abbrev input (editor : Code) :=
  PartrecBridge.inputConfiguration Mettapedia.Languages.PartrecMachine.universal [Encodable.encode editor, 0]

/-- Preparing the equation input from an editor code is effective. -/
theorem input_term_primitive_recursive :
    Primrec fun editor : Code => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (input editor).term :=
  (InputEncoding.inputConfiguration_patternCode_primrec _).comp
    (Primrec.list_cons.comp Primrec.encode (Primrec.const [0]))

def SafeOnInput (editor : Code) : Prop :=
  SafeForAll (.symbol "Z") (installsWithin table (input editor))

theorem safeOnInput_iff (editor : Code) :
    SafeOnInput editor ↔ ¬ Tables.EquationHalts table (input editor).term :=
  (safeForAll_iff _ _).trans
    (not_congr (installs_iff_equationHalts _ (PartrecBridge.deterministic _) _))

/-- The bounded equation simulation and the primitive-recursive editor
have exactly the same safe inputs. Their bounds need not coincide. -/
theorem same_safe_inputs (editor : Code) :
    SafeOnInput editor ↔ PeTTaStaticHeadElision.SafeToHoist editor := by
  rw [safeOnInput_iff, Tables.equationHalts_iff, PeTTaStaticHeadElision.safeToHoist_iff_nonhalting]
  apply not_congr
  rw [table, input, PartrecBridge.halts_iff, Mettapedia.Languages.PartrecMachine.universal_eval,
    Denumerable.ofNat_encode]
  rfl

/-- Even with one fixed finite equation program, one suspended constructor
and only the input varying, an exact computable hoisting classifier would
decide halting of the equation table. -/
theorem exact_equation_elision_undecidable : ¬ ComputablePred SafeOnInput :=
  fun decided => PeTTaStaticHeadElision.exact_elision_undecidable (decided.of_eq same_safe_inputs)

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaEquationHeadElision
