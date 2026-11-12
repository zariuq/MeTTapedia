import Mettapedia.Languages.MeTTa.PeTTa.UnifyingScopeInvariant
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingFrontierScopes

/-!
# Variable support of primitive replies and retained cells

These are constructor-level support laws for handles, byte strings, string
errors, membership answers and the closed sorting decoder. Retained-cell
support follows from the primitive table's actual update classification and
input support. The table's reply law is proved beside its definitions and
instantiated here. Parsing, enumeration and runtime matching retain their
separate source boundaries.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)

theorem handleValue_supported (allowed : String → Prop) (handle : NamedSpaces.Handle) :
    Supported allowed (Effects.handleValue handle) := StdLib.handle_variable_support allowed handle

theorem byteString_supported (allowed : String → Prop) (bytes : List UInt8) :
    Supported allowed (Mettapedia.Languages.MeTTa.OSLFCore.ByteString.encode bytes) :=
  StdLib.byte_string_variable_support allowed bytes

theorem metatype_supported (allowed : String → Prop) (state : Effects.State) (term : Atom) :
    Supported allowed (StdLib.metatype state term) := StdLib.metatype_variable_support allowed state term

theorem stringError_supported (allowed : String → Prop) (head : String) (arguments : List Atom)
    (good : ∀ term ∈ arguments, Supported allowed term) (reason : Atom) (reasonGood : Supported allowed reason) :
    Supported allowed (StdLib.stringError head arguments reason) :=
  StdLib.string_error_variable_support allowed head arguments good reason reasonGood

theorem stringOperation_supported (allowed : String → Prop) (head : String) (arguments : List Atom)
    (good : ∀ term ∈ arguments, Supported allowed term) :
    Supported allowed (StdLib.stringOperation head arguments) :=
  StdLib.string_operation_variable_support allowed head arguments good

theorem membershipAnswers_supported (allowed : String → Prop) (value : Atom) (items : List Atom) :
    ∀ answer ∈ StdLib.membershipAnswers value items, Supported allowed answer :=
  StdLib.membership_variable_support allowed value items

theorem sortClosed_supported (allowed : String → Prop) (items sorted : List Atom)
    (selected : StdLib.sortClosed items = some sorted) : ∀ term ∈ sorted, Supported allowed term :=
  StdLib.sorting_variable_support allowed items sorted selected

theorem CellsSupported.putCell {allowed : String → Prop} {state : Effects.State}
    (cells : CellsSupported allowed state) (name : String) (value : Atom) (good : Supported allowed value) :
    CellsSupported allowed (state.putCell name value) := by
  intro other stored found
  by_cases same : other = name
  · subst other
    rw [NamedSpaces.Store.cell_reads_back] at found
    cases found
    exact good
  · rw [NamedSpaces.Store.cell_read_other state name other value same] at found
    exact cells other stored found

/-- Derive retained-cell support from the primitive table's actual update
classification. No desired property of the returned store is assumed. -/
theorem primitive_cells_supported (allowed : String → Prop) (state after : Effects.State)
    (head : String) (arguments answers : List Atom)
    (inputs : ∀ term ∈ arguments, Supported allowed term) (cells : CellsSupported allowed state)
    (returned : StdLib.apply state head arguments = .ok (after,answers)) : CellsSupported allowed after := by
  rcases StdLib.successful_apply_cell_update returned with same | ⟨name,value,_,argumentsSame,rfl⟩
  · intro name value found
    rw [same] at found
    exact cells name value found
  · exact cells.putCell name value (inputs value (by rw [argumentsSame]; simp))

theorem ordinary_primitive_answers_supported (allowed : String → Prop) (state after : Effects.State)
    (head : String) (arguments answers : List Atom)
    (inputs : ∀ term ∈ arguments, Supported allowed term) (cells : CellsSupported allowed state)
    (notParse : head ≠ "parse") (notRows : head ≠ "get-atoms") (notMatch : head ≠ "match")
    (returned : StdLib.apply state head arguments = .ok (after,answers)) :
    ∀ answer ∈ answers, Supported allowed answer :=
  StdLib.successful_apply_variable_support allowed state after head arguments answers inputs cells
    notParse notRows notMatch returned

theorem primitive_inputs_supported (ceiling use : Nat) (head : String) (values : List Atom)
    (good : ∀ value ∈ values, Supported (Mettapedia.ScopedString.Before ceiling) value)
    (room : head = "change-state!" → use < ceiling) :
    ∀ value ∈ primitiveInputs head use values, Supported (Mettapedia.ScopedString.Before ceiling) value := by
  unfold primitiveInputs
  split
  · rename_i name value
    intro term member
    rcases List.mem_cons.mp member with rfl | member
    · exact good term (by simp)
    · simp only [List.mem_singleton] at member
      subst term
      exact renamed_supported_before ceiling use (room rfl) value
  · exact good

/-- Native preparation and its import-copy policy establish the reply's
scope bound from the actual counter increment and supplied source values. -/
theorem primitive_reply_supported (use : Nat) (state after : Effects.State) (head : String)
    (values answers : List Atom)
    (inputs : ∀ value ∈ values, Supported (Mettapedia.ScopedString.Before use) value)
    (cells : CellsSupported (Mettapedia.ScopedString.Before use) state)
    (notMatch : head ≠ "match")
    (returned : StdLib.apply state head (primitiveInputs head use values) = .ok (after,answers)) :
    CellsSupported (Mettapedia.ScopedString.Before (use + primitiveUses head answers)) after ∧
      ∀ answer ∈ primitiveOutputs head use answers,
        Supported (Mettapedia.ScopedString.Before (use + primitiveUses head answers)) answer := by
  let ceiling := use + primitiveUses head answers
  have included : ∀ key, Mettapedia.ScopedString.Before use key → Mettapedia.ScopedString.Before ceiling key :=
    fun _ old => Mettapedia.ScopedString.before_mono (by dsimp [ceiling]; omega) old
  have prepared := primitive_inputs_supported ceiling use head values
    (fun value member => (inputs value member).mono included)
    (by intro same; simp [ceiling,primitiveUses,same])
  have oldCells : CellsSupported (Mettapedia.ScopedString.Before ceiling) state :=
    fun name value stored => (cells name value stored).mono included
  refine ⟨primitive_cells_supported _ _ _ _ _ _ prepared oldCells returned,?_⟩
  by_cases copied : primitiveCopies head = true
  · have notChange : head ≠ "change-state!" := by rintro rfl; cases copied
    have increment : primitiveUses head answers = answers.length := by simp [primitiveUses,notChange,copied]
    simpa only [primitiveOutputs,copied,↓reduceIte,increment] using
      copyTerms_supported (use + answers.length) use answers (Nat.le_refl _)
  · have notParse : head ≠ "parse" := by rintro rfl; cases copied rfl
    have notRows : head ≠ "get-atoms" := by rintro rfl; cases copied rfl
    have ordinary := ordinary_primitive_answers_supported _ _ _ _ _ _ prepared oldCells
      notParse notRows notMatch returned
    simpa only [primitiveOutputs,copied,Bool.false_eq_true,↓reduceIte] using ordinary

theorem primitive_scoped_step (registry : SpaceSemantics.Program) (source : Configuration)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (head : String) (held answers : List Atom)
    (index : Nat) (after : Effects.State) (well : WellScoped source)
    (control : source.control = .arguments bindings (.function head) [] held index)
    (ordinary : Eval.ioHead head = false) (notRemove : head ≠ "remove-atom") (notMatch : head ≠ "match")
    (native : StdLib.known head = true)
    (returned : StdLib.apply source.state head
      (primitiveInputs head source.uses (held.map (resolve bindings))) = .ok (after,answers)) :
    step registry source = some {source with
      state := after
      control := .returned ((primitiveOutputs head source.uses answers).map fun value => ⟨value,bindings⟩)
      uses := source.uses + primitiveUses head answers} ∧
    WellScoped {source with
      state := after
      control := .returned ((primitiveOutputs head source.uses answers).map fun value => ⟨value,bindings⟩)
      uses := source.uses + primitiveUses head answers} := by
  refine ⟨transition_step (.primitive control ordinary notRemove notMatch native returned),?_⟩
  have initial := well
  unfold WellScoped at initial
  have before : SupportedBindings (Mettapedia.ScopedString.Before source.uses) bindings ∧
      ∀ value ∈ held, Supported (Mettapedia.ScopedString.Before source.uses) value := by
    simpa only [control,ControlSupported,List.not_mem_nil,false_implies,implies_true,true_and] using initial.1
  have valuesGood : ∀ value ∈ held.map (resolve bindings),
      Supported (Mettapedia.ScopedString.Before source.uses) value := by
    intro value member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact supported_resolve before.1 original (before.2 original present)
  have reply := primitive_reply_supported source.uses source.state after head _ answers
    valuesGood initial.2.2.1 notMatch returned
  have included : ∀ key, Mettapedia.ScopedString.Before source.uses key →
      Mettapedia.ScopedString.Before (source.uses + primitiveUses head answers) key :=
    fun _ old => Mettapedia.ScopedString.before_mono (by omega) old
  have later := initial.mono included
  refine ⟨?_,later.2.1,reply.1,later.2.2.2⟩
  simp only [ControlSupported]
  intro answer member
  obtain ⟨value,present,rfl⟩ := List.mem_map.mp member
  exact ⟨reply.2 value present,before.1.mono included⟩


end Mettapedia.Languages.MeTTa.PeTTa.Unifying
