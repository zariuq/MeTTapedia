import Mettapedia.Languages.TuringMachine.FiniteControl
import Mettapedia.Languages.TuringMachine.FinitePostCompiler
import Mettapedia.Languages.PartrecMachine.Rice
import Mathlib.Computability.TuringMachine.ToPartrec
import Mettapedia.Computability.StateTransition

/-!
# Partial-recursive programs as finite authored Turing tables

Mathlib's partial-recursive stack machine is compiled through TM2, TM1 and TM0.
Its closed finite control support is made into the actual state type, then
compiled to write-and-move rows. The nonempty-path refinement carries source
results into terminal table configurations and reflects every terminal run
back to a source result. Every resulting table is deterministic. Input retains
the binary stack representation and its bottom marker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.PartrecBridge

open Turing
open Turing.ToPartrec

local instance stackFintype : Fintype PartrecToTM2.K' where
  elems := {.main, .rev, .aux, .stack}
  complete := by intro key; cases key <;> simp

abbrev Alphabet := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
abbrev TapeLabels := TM2to1.Λ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
  PartrecToTM2.Λ' (Option PartrecToTM2.Γ')

def tapeProgram : TapeLabels → TM1.Stmt Alphabet TapeLabels (Option PartrecToTM2.Γ') :=
  TM2to1.tr PartrecToTM2.tr

abbrev PostLabels := TM1to0.Λ' tapeProgram

@[instance_reducible] def initialLabels (program : Code) : Inhabited PartrecToTM2.Λ' :=
  ⟨PartrecToTM2.trNormal program .halt⟩

noncomputable def support (program : Code) : Finset PostLabels :=
  TM1to0.trStmts tapeProgram
    (TM2to1.trSupp PartrecToTM2.tr (PartrecToTM2.codeSupp program .halt))

theorem supported (program : Code) :
    letI := initialLabels program
    TM0.Supports (TM1to0.tr tapeProgram) (support program : Set PostLabels) := by
  let := initialLabels program
  exact TM1to0.tr_supports tapeProgram
    (TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports program .halt))

/-- The encoded tape starts with a stack-bottom marker and the binary list code. -/
def tapeInput (input : List Nat) : List Alphabet :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList input)

theorem tm2_init (program : Code) (input : List Nat) :
    letI := initialLabels program
    TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input) =
      PartrecToTM2.init program input := by
  let := initialLabels program
  simp only [TM2.init, PartrecToTM2.init]
  congr 1
  funext key
  cases key <;> simp [PartrecToTM2.K'.elim]

theorem native_eval_dom_iff (program : Code) (input : List Nat) :
    letI := initialLabels program
    (TM0.eval (TM1to0.tr tapeProgram) (tapeInput input)).Dom ↔
      (program.eval input).Dom := by
  let := initialLabels program
  rw [TM1to0.tr_eval tapeProgram]
  change (TM1.eval (TM2to1.tr PartrecToTM2.tr)
    (TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList input))).Dom ↔ _
  rw [TM2to1.tr_eval_dom PartrecToTM2.tr]
  change (StateTransition.eval (TM2.step PartrecToTM2.tr)
    (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList input))).Dom ↔ _
  rw [tm2_init program input, PartrecToTM2.tr_eval]
  rfl

noncomputable def encoding (program : Code) :
    FinitePostCompiler.Encoding Alphabet {label : PostLabels // label ∈ support program} := by
  classical
  letI := initialLabels program
  letI := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  exact FinitePostCompiler.finiteEncoding

noncomputable def machine (program : Code) : Machine := by
  classical
  letI := initialLabels program
  letI := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  exact FinitePostCompiler.table (encoding program)
    (FiniteControl.restrict (TM1to0.tr tapeProgram) (support program) (supported program))

noncomputable def inputConfiguration (program : Code) (input : List Nat) : Configuration := by
  letI := initialLabels program
  letI := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  exact FinitePostCompiler.initial (encoding program) (tapeInput input)

theorem input_state (program : Code) (input : List Nat) :
    (inputConfiguration program input).state = 0 := by
  classical
  simp [inputConfiguration, FinitePostCompiler.initial, encoding]

theorem deterministic (program : Code) : (machine program).Deterministic := by
  classical
  let := initialLabels program
  let := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  exact FinitePostCompiler.deterministic _ _

theorem halts_iff (program : Code) (input : List Nat) :
    HaltsFrom (machine program) (inputConfiguration program input).term ↔
      (program.eval input).Dom := by
  classical
  let := initialLabels program
  let := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  change HaltsFrom (FinitePostCompiler.table (encoding program)
    (FiniteControl.restrict (TM1to0.tr tapeProgram) (support program) (supported program)))
    (FinitePostCompiler.initial (encoding program) (tapeInput input)).term ↔ _
  rw [FinitePostCompiler.halts_iff,
    FiniteControl.input_eval_dom_iff (TM1to0.tr tapeProgram) (support program) (supported program)]
  exact native_eval_dom_iff program input

/-- The complete compiler relation retains the native stack contents, the
single tape and its finite-control representative. -/
def Represents (program : Code) (native : PartrecToTM2.Cfg')
    (configuration : Configuration) : Prop :=
  letI := initialLabels program
  letI := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  ∃ post : TM0.Cfg Alphabet PostLabels,
    (∃ tape : TM1.Cfg Alphabet TapeLabels (Option PartrecToTM2.Γ'),
      TM2to1.TrCfg native tape ∧ TM1to0.trCfg tapeProgram tape = post) ∧
    (∃ finite : TM0.Cfg Alphabet {label : PostLabels // label ∈ support program},
      FiniteControl.forget (support program) finite = post ∧
      FinitePostCompiler.Represents (encoding program) finite configuration)

theorem refinement (program : Code) :
    StateTransition.Respects (TM2.step PartrecToTM2.tr) (machine program).next?
      (Represents program) := by
  classical
  let := initialLabels program
  let := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  exact Mettapedia.Computability.StateTransition.respects_comp
    (Mettapedia.Computability.StateTransition.respects_comp
      (TM2to1.tr_respects PartrecToTM2.tr) (TM1to0.tr_respects tapeProgram))
    (Mettapedia.Computability.StateTransition.respects_comp
      (FiniteControl.reflects (TM1to0.tr tapeProgram) (support program) (supported program))
      (FinitePostCompiler.respects (encoding program) _))

theorem initial_represents (program : Code) (input : List Nat) :
    Represents program (PartrecToTM2.init program input) (inputConfiguration program input) := by
  let := initialLabels program
  let := FiniteControl.controlInhabited (TM1to0.tr tapeProgram) (support program) (supported program)
  refine ⟨TM0.init (tapeInput input), ⟨TM1.init (tapeInput input), ?_, rfl⟩,
    ⟨TM0.init (tapeInput input), rfl, FinitePostCompiler.initial_represents _ _⟩⟩
  rw [← tm2_init program input]
  exact TM2to1.trCfg_init _ _

/-- A source result is realized by a terminal table configuration with the
same encoded stack output. -/
theorem eval_preserved (program : Code) (input output : List Nat)
    (computed : output ∈ program.eval input) :
    ∃ final, final ∈ StateTransition.eval (machine program).next?
      (inputConfiguration program input) ∧
      Represents program (PartrecToTM2.halt output) final := by
  have nativeComputed : PartrecToTM2.halt output ∈
      StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init program input) := by
    rw [PartrecToTM2.tr_eval]
    exact Part.mem_map _ computed
  obtain ⟨final, represented, halted⟩ := StateTransition.tr_eval (refinement program)
    (initial_represents program input) nativeComputed
  exact ⟨final, halted, represented⟩

/-- Every terminal table execution has a genuine source output. -/
theorem eval_reflected (program : Code) (input : List Nat) {final : Configuration}
    (computed : final ∈ StateTransition.eval (machine program).next?
      (inputConfiguration program input)) :
    ∃ output, output ∈ program.eval input ∧
      Represents program (PartrecToTM2.halt output) final := by
  obtain ⟨nativeFinal, represented, nativeComputed⟩ :=
    StateTransition.tr_eval_rev (refinement program) (initial_represents program input) computed
  rw [PartrecToTM2.tr_eval] at nativeComputed
  obtain ⟨output, member, rfl⟩ := (Part.mem_map_iff _).mp nativeComputed
  exact ⟨output, member, represented⟩

end Mettapedia.Languages.TuringMachine.PartrecBridge
