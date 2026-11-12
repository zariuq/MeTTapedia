import Mettapedia.Languages.MeTTa.PeTTa.UnifyingAllocation

/-!
# Allocation support in running configurations

Controls, saved continuations, output and retained state cells carry logical
identities. Public rows, private clauses and unread input are templates: they
receive fresh identities at their existing import/use boundaries. This support
predicate does not scan those templates or impose reserved source spellings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def AnswerSupported (allowed : String → Prop) (answer : Answer) : Prop :=
  Supported allowed answer.value ∧ SupportedBindings allowed answer.bindings

def ControlSupported (allowed : String → Prop) : Control → Prop
  | .evaluate bindings expression => SupportedBindings allowed bindings ∧ Supported allowed expression
  | .dynamic bindings head values => SupportedBindings allowed bindings ∧ Supported allowed head ∧
      ∀ value ∈ values, Supported allowed value
  | .arguments bindings _ remaining values _ => SupportedBindings allowed bindings ∧
      (∀ value ∈ remaining, Supported allowed value) ∧ ∀ value ∈ values, Supported allowed value
  | .sequence pending answers => (∀ control ∈ pending, ControlSupported allowed control) ∧
      ∀ answer ∈ answers, AnswerSupported allowed answer
  | .returned answers => ∀ answer ∈ answers, AnswerSupported allowed answer
  | .fault _ => True

def FrameSupported (allowed : String → Prop) : Frame → Prop
  | .bind pattern body | .query pattern body => Supported allowed pattern ∧ Supported allowed body
  | .select cases => ∀ branch ∈ cases, Supported allowed branch.1 ∧ Supported allowed branch.2
  | .branch yes no => Supported allowed yes ∧ Supported allowed no
  | .collect bindings => SupportedBindings allowed bindings
  | .argument _ remaining values _ =>
      (∀ value ∈ remaining, Supported allowed value) ∧ ∀ value ∈ values, Supported allowed value
  | .sequence pending answers => (∀ control ∈ pending, ControlSupported allowed control) ∧
      ∀ answer ∈ answers, AnswerSupported allowed answer
  | .dispatch | .dynamicCall => True

def CellsSupported (allowed : String → Prop) (state : Effects.State) : Prop :=
  ∀ name value, state.cells name = some value → Supported allowed value

def ConfigurationSupported (allowed : String → Prop) (source : Configuration) : Prop :=
  ControlSupported allowed source.control ∧ (∀ frame ∈ source.frames, FrameSupported allowed frame) ∧
    CellsSupported allowed source.state ∧ ∀ output ∈ source.output, Supported allowed output

def WellScoped (source : Configuration) : Prop :=
  ConfigurationSupported (Mettapedia.ScopedString.Before source.uses) source

theorem AnswerSupported.mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {answer : Answer} (supported : AnswerSupported first answer) : AnswerSupported later answer :=
  ⟨supported.1.mono included,supported.2.mono included⟩

theorem ControlSupported.mono {first later : String → Prop} (included : ∀ key, first key → later key) :
    ∀ control : Control, ControlSupported first control → ControlSupported later control
  | .evaluate _ _, good => by
      simp only [ControlSupported] at good ⊢
      exact ⟨good.1.mono included,good.2.mono included⟩
  | .dynamic _ _ _, good => by
      simp only [ControlSupported] at good ⊢
      exact ⟨good.1.mono included,good.2.1.mono included,fun term member => (good.2.2 term member).mono included⟩
  | .arguments _ _ _ _ _, good => by
      simp only [ControlSupported] at good ⊢
      exact ⟨good.1.mono included,fun term member => (good.2.1 term member).mono included,
        fun term member => (good.2.2 term member).mono included⟩
  | .sequence _ _, good => by
      simp only [ControlSupported] at good ⊢
      exact ⟨fun control member => ControlSupported.mono included control (good.1 control member),
        fun answer member => (good.2 answer member).mono included⟩
  | .returned _, good => by
      simp only [ControlSupported] at good ⊢
      exact fun answer member => (good answer member).mono included
  | .fault _, _ => by simp only [ControlSupported]

theorem FrameSupported.mono {first later : String → Prop} (included : ∀ key, first key → later key)
    {frame : Frame} (supported : FrameSupported first frame) : FrameSupported later frame := by
  cases frame with
  | bind | query | branch => exact ⟨supported.1.mono included,supported.2.mono included⟩
  | select => exact fun branch member =>
      ⟨(supported branch member).1.mono included,(supported branch member).2.mono included⟩
  | collect => exact SupportedBindings.mono included supported
  | argument => exact ⟨fun term member => (supported.1 term member).mono included,
      fun term member => (supported.2 term member).mono included⟩
  | sequence => exact ⟨fun control member => ControlSupported.mono included control (supported.1 control member),
      fun answer member => (supported.2 answer member).mono included⟩
  | dispatch | dynamicCall => trivial

theorem ConfigurationSupported.mono {first later : String → Prop}
    (included : ∀ key, first key → later key) {source : Configuration}
    (supported : ConfigurationSupported first source) : ConfigurationSupported later source :=
  ⟨ControlSupported.mono included source.control supported.1,
    fun frame member => (supported.2.1 frame member).mono included,
    fun name value stored => (supported.2.2.1 name value stored).mono included,
    fun output member => (supported.2.2.2 output member).mono included⟩

theorem scoped_entry (scope : Nat) (code : List SpaceSemantics.Equation)
    (state : Effects.State) (expression : Atom)
    (cells : CellsSupported (Mettapedia.ScopedString.Before (scope + 1)) state) :
    WellScoped (ScopedSource.enter scope code state expression) := by
  dsimp only [WellScoped,ConfigurationSupported,ScopedSource.enter]
  rw [ControlSupported]
  refine ⟨⟨?_,ScopedSource.renamed_allocated scope expression⟩,by simp,cells,?_⟩
  · intro binding present; cases present
  · simp

theorem empty_cells_supported (allowed : String → Prop) : CellsSupported allowed Effects.empty := by
  intro name value stored
  cases stored

theorem loaded_cells_supported (allowed : String → Prop) (program : SpaceSemantics.Program) :
    CellsSupported allowed (Effects.loaded program) := by
  intro name value stored
  cases stored

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
