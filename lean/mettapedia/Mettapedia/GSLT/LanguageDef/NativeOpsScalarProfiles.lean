import Mettapedia.GSLT.LanguageDef.NativeOpsFiniteStorage

/-!
# Declared scalar tags in live local cells

These predicates describe outer value tags. A record tag records its nominal
name, not the types of its fields; a reference tag grants neither ownership
nor pointee validity. Scalar operations need only these outer tags.

Local profiles follow actual bindings and cells. Declarations and parameter
initialization derive them from typed argument values and the local-position
invariant. No arbitrary allocator or external-call preservation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

inductive SourceOuterTag : NativeType → SourceValue → Prop where
  | unit : SourceOuterTag .unit .unit
  | word (value : NativeWord64.Word) : SourceOuterTag .word (.word value)
  | byte (value : NativeWord64.Byte) : SourceOuterTag .byte (.byte value)
  | bool (value : Bool) : SourceOuterTag .bool (.bool value)
  | record (name : String) (fields : List SourceValue) :
      SourceOuterTag (.named name) (.record name fields)
  | reference (element : NativeType) (address : Option Address) :
      SourceOuterTag (.ref element) (.reference address)
  | array (element : NativeType) (address : Option Address) (length : NativeWord64.Word) :
      SourceOuterTag (.array element) (.array element address length)

inductive TargetOuterTag : NativeType → TargetValue → Prop where
  | unit : TargetOuterTag .unit .unit
  | word (value : BitVec 64) : TargetOuterTag .word (.word value)
  | byte (value : BitVec 8) : TargetOuterTag .byte (.byte value)
  | bool (value : Bool) : TargetOuterTag .bool (.bool value)
  | record (name : String) (fields : List TargetValue) :
      TargetOuterTag (.named name) (.record name fields)
  | reference (element : NativeType) (address : Option Address) :
      TargetOuterTag (.ref element) (.reference address)
  | array (element : NativeType) (address : Option Address) (length : BitVec 64) :
      TargetOuterTag (.array element) (.array element address length)

theorem outer_tag_preservation {type : NativeType} {value : SourceValue}
    (tagged : SourceOuterTag type value) : TargetOuterTag type (encodeValue value) := by
  cases tagged <;> constructor

theorem outer_tag_reflection {type : NativeType} {value : TargetValue}
    (tagged : TargetOuterTag type value) : SourceOuterTag type (decodeValue value) := by
  cases tagged <;> constructor

theorem outer_tag_correspondence (type : NativeType) (value : SourceValue) :
    SourceOuterTag type value ↔ TargetOuterTag type (encodeValue value) := by
  constructor
  · exact outer_tag_preservation
  · intro tagged
    simpa only [decode_encode_value] using outer_tag_reflection tagged

theorem source_zero_outer_tag {interface : Interface} {type : NativeType} {value : SourceValue}
    (zero : SourceZero interface type value) : SourceOuterTag type value := by
  cases zero <;> constructor

theorem target_zero_outer_tag {interface : Interface} {type : NativeType} {value : TargetValue}
    (zero : TargetZero interface type value) : TargetOuterTag type value := by
  cases zero <;> constructor

theorem source_unary_typed_defined {operation : Unary} {input result : NativeType}
    {value : SourceValue} (typing : unaryType operation input = some result)
    (tagged : SourceOuterTag input value) :
    ∃ computed, sourceUnaryOp operation value = some computed ∧ SourceOuterTag result computed := by
  cases operation <;> cases tagged <;> simp only [unaryType, reduceCtorEq] at typing
  all_goals cases typing
  all_goals exact ⟨_, rfl, by constructor⟩

theorem source_binary_typed_defined {operation : Binary} {input result : NativeType}
    {left right : SourceValue} (typing : binaryType operation input = some result)
    (first : SourceOuterTag input left) (second : SourceOuterTag input right) :
    ∃ computed, sourceBinaryOp operation left right = some computed ∧
      ∀ value, computed = .ok value → SourceOuterTag result value := by
  cases operation with
  | word operation =>
      cases first <;> simp only [binaryType, reduceCtorEq] at typing
      rename_i leftWord
      cases second
      rename_i rightWord
      cases typing
      refine ⟨(NativeWord64.sourceBinary operation leftWord rightWord).map SourceValue.word, rfl, ?_⟩
      intro value computed
      cases resultOfOperation : NativeWord64.sourceBinary operation leftWord rightWord with
      | error fault => simp only [resultOfOperation, Except.map, reduceCtorEq] at computed
      | ok answer =>
          simp only [resultOfOperation, Except.map, Except.ok.injEq] at computed
          cases computed
          exact .word answer
  | compare comparison =>
      cases first <;> cases second <;> cases comparison <;>
        simp only [binaryType, reduceCtorEq] at typing
      all_goals cases typing
      all_goals refine ⟨_, rfl, ?_⟩
      all_goals intro value computed; cases computed; constructor
  | and =>
      cases first <;> simp only [binaryType, reduceCtorEq] at typing
      cases second
      cases typing
      refine ⟨_, rfl, ?_⟩
      intro value computed; cases computed; constructor
  | or =>
      cases first <;> simp only [binaryType, reduceCtorEq] at typing
      cases second
      cases typing
      refine ⟨_, rfl, ?_⟩
      intro value computed; cases computed; constructor

def SourceLocalsTagged (frame : SourceFrame) (memory : SourceMemory) : Prop :=
  ∀ binding ∈ frame.bindings, ∀ value,
    memory.cells frame.storage binding.position = some value → SourceOuterTag binding.type value

def TargetLocalsTagged (frame : TargetFrame) (memory : TargetMemory) : Prop :=
  ∀ binding ∈ frame.bindings, ∀ value,
    memory.cells frame.storage binding.position = some value → TargetOuterTag binding.type value

def SourceLocalsBelow (frame : SourceFrame) : Prop :=
  ∀ binding ∈ frame.bindings, binding.position < frame.nextLocal

def TargetLocalsBelow (frame : TargetFrame) : Prop :=
  ∀ binding ∈ frame.bindings, binding.position < frame.nextLocal

theorem locals_below_correspondence {source : SourceFrame} {target : TargetFrame}
    (frames : FrameRelated source target) : SourceLocalsBelow source ↔ TargetLocalsBelow target := by
  simp only [SourceLocalsBelow, TargetLocalsBelow, frames.bindings, frames.nextLocal]

theorem locals_tag_correspondence {sourceFrame : SourceFrame} {targetFrame : TargetFrame}
    {source : SourceMemory} {target : TargetMemory} (frames : FrameRelated sourceFrame targetFrame)
    (memory : MemoryRelated source target) :
    SourceLocalsTagged sourceFrame source ↔ TargetLocalsTagged targetFrame target := by
  constructor
  · intro tagged binding member value read
    rw [frames.bindings] at member
    rw [frames.storage, memory.1] at read
    obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp read
    cases same
    exact outer_tag_preservation (tagged binding member original selected)
  · intro tagged binding member value read
    have nativeMember : binding ∈ targetFrame.bindings := by rw [frames.bindings]; exact member
    have nativeRead : target.cells targetFrame.storage binding.position = some (encodeValue value) := by
      rw [frames.storage, memory.1, read]
      rfl
    exact (outer_tag_correspondence binding.type value).mpr
      (tagged binding nativeMember (encodeValue value) nativeRead)

theorem source_local_read_tag {World : Type} {frame : SourceFrame} {state : SourceState World}
    (tagged : SourceLocalsTagged frame state.memory) {name : String} {type : NativeType}
    {value : SourceValue} (typing : lookupVariable (sourceFrameScope frame) name = some type)
    (read : sourceLocalValue frame state name = some value) : SourceOuterTag type value := by
  have lookup : lookupVariable (sourceFrameScope frame) name =
      (frame.bindings.find? (fun binding => binding.name == name)).map LocalBinding.type := by
    simp only [lookupVariable, sourceFrameScope, List.find?_map, Option.map_map]
    rfl
  rw [lookup] at typing
  cases selected : frame.bindings.find? (fun binding => binding.name == name) with
  | none => simp only [selected, Option.map_none, reduceCtorEq] at typing
  | some binding =>
      have same : binding.type = type := by
        simpa only [selected, Option.map_some, Option.some.injEq] using typing
      have cell : state.memory.cells frame.storage binding.position = some value := by
        simpa only [sourceLocalValue, sourceLocalAddress, selected, bind, pure, Option.bind_some,
          sourceRead, sourceReadPath, Option.bind_fun_some] using read
      rw [← same]
      exact tagged binding (List.mem_of_find?_eq_some selected) value cell

theorem source_store_cell_tagged {frame : SourceFrame} {memory : SourceMemory}
    (tagged : SourceLocalsTagged frame memory) (storage position : Nat) (value : SourceValue)
    (compatible : ∀ binding ∈ frame.bindings, storage = frame.storage → position = binding.position →
      SourceOuterTag binding.type value) :
    SourceLocalsTagged frame (sourceStoreCell memory storage position value) := by
  intro binding member readValue read
  change (if frame.storage = storage ∧ binding.position = position then some value
    else memory.cells frame.storage binding.position) = some readValue at read
  by_cases selected : frame.storage = storage ∧ binding.position = position
  · rw [if_pos selected] at read
    cases Option.some.inj read
    exact compatible binding member selected.1.symm selected.2.symm
  · rw [if_neg selected] at read
    exact tagged binding member readValue read

theorem source_declare_local_below {World : Type} {frame : SourceFrame} {state : SourceState World}
    (below : SourceLocalsBelow frame) (name : String) (type : NativeType) (value : SourceValue) :
    SourceLocalsBelow (sourceDeclareLocal frame state name type value).1 := by
  intro binding member
  rcases List.mem_cons.mp member with same | old
  · cases same
    exact Nat.lt_succ_self frame.nextLocal
  · exact Nat.lt_succ_of_lt (below binding old)

theorem target_declare_local_below {World : Type} {frame : TargetFrame} {state : TargetState World}
    (below : TargetLocalsBelow frame) (name : String) (type : NativeType) (value : TargetValue) :
    TargetLocalsBelow (targetDeclareLocal frame state name type value).1 := by
  intro binding member
  rcases List.mem_cons.mp member with same | old
  · cases same
    exact Nat.lt_succ_self frame.nextLocal
  · exact Nat.lt_succ_of_lt (below binding old)

theorem source_declare_local_tagged {World : Type} {frame : SourceFrame} {state : SourceState World}
    (tagged : SourceLocalsTagged frame state.memory) (below : SourceLocalsBelow frame)
    (name : String) (type : NativeType) {value : SourceValue} (newTag : SourceOuterTag type value) :
    SourceLocalsTagged (sourceDeclareLocal frame state name type value).1
      (sourceDeclareLocal frame state name type value).2.memory := by
  intro binding member selected read
  rcases List.mem_cons.mp member with same | old
  · cases same
    have equal : value = selected := by
      simpa only [sourceDeclareLocal, sourceStoreCell, and_self, if_pos rfl, if_true,
        Option.some.injEq] using read
    cases equal
    exact newTag
  · have different : binding.position ≠ frame.nextLocal :=
      Nat.ne_of_lt (below binding old)
    have cell : state.memory.cells frame.storage binding.position = some selected := by
      simpa only [sourceDeclareLocal, sourceStoreCell, different, and_false, if_false] using read
    exact tagged binding old selected cell

theorem target_declare_local_tagged {World : Type} {frame : TargetFrame} {state : TargetState World}
    (tagged : TargetLocalsTagged frame state.memory) (below : TargetLocalsBelow frame)
    (name : String) (type : NativeType) {value : TargetValue} (newTag : TargetOuterTag type value) :
    TargetLocalsTagged (targetDeclareLocal frame state name type value).1
      (targetDeclareLocal frame state name type value).2.memory := by
  intro binding member selected read
  rcases List.mem_cons.mp member with same | old
  · cases same
    have equal : value = selected := by
      simpa only [targetDeclareLocal, targetStoreCell, if_pos rfl, if_true, Option.some.injEq] using read
    cases equal
    exact newTag
  · have different : binding.position ≠ frame.nextLocal :=
      Nat.ne_of_lt (below binding old)
    have cell : state.memory.cells frame.storage binding.position = some selected := by
      simpa only [targetDeclareLocal, targetStoreCell, if_pos rfl, if_true, if_neg different] using read
    exact tagged binding old selected cell

def SourceParameterTags : List Parameter → List SourceValue → Prop :=
  List.Forall₂ (fun parameter value => SourceOuterTag parameter.type value)

def TargetParameterTags : List Parameter → List TargetValue → Prop :=
  List.Forall₂ (fun parameter value => TargetOuterTag parameter.type value)

theorem source_bind_parameters_tagged {World : Type} (parameters : List Parameter)
    {arguments : List SourceValue} {frame outFrame : SourceFrame} {state outState : SourceState World}
    (tagged : SourceLocalsTagged frame state.memory) (below : SourceLocalsBelow frame)
    (values : SourceParameterTags parameters arguments)
    (bound : sourceBindParameters parameters arguments frame state = some (outFrame, outState)) :
    SourceLocalsTagged outFrame outState.memory ∧ SourceLocalsBelow outFrame := by
  induction values generalizing frame state with
  | nil =>
      have same : (frame, state) = (outFrame, outState) := Option.some.inj bound
      cases same
      exact ⟨tagged, below⟩
  | @cons parameter value parameters values head tail ih =>
      exact ih (source_declare_local_tagged tagged below parameter.name parameter.type head)
        (source_declare_local_below below parameter.name parameter.type value) bound

theorem target_bind_parameters_tagged {World : Type} (parameters : List Parameter)
    {arguments : List TargetValue} {frame outFrame : TargetFrame} {state outState : TargetState World}
    (tagged : TargetLocalsTagged frame state.memory) (below : TargetLocalsBelow frame)
    (values : TargetParameterTags parameters arguments)
    (bound : targetBindParameters parameters arguments frame state = some (outFrame, outState)) :
    TargetLocalsTagged outFrame outState.memory ∧ TargetLocalsBelow outFrame := by
  induction values generalizing frame state with
  | nil =>
      have same : (frame, state) = (outFrame, outState) := Option.some.inj bound
      cases same
      exact ⟨tagged, below⟩
  | @cons parameter value parameters values head tail ih =>
      exact ih (target_declare_local_tagged tagged below parameter.name parameter.type head)
        (target_declare_local_below below parameter.name parameter.type value) bound

theorem source_empty_frame_tagged (memory : SourceMemory) (storage : Nat) :
    SourceLocalsTagged ⟨storage, 0, []⟩ memory := by
  intro binding member
  cases member

theorem target_empty_frame_tagged (memory : TargetMemory) (storage : Nat) :
    TargetLocalsTagged (targetEmptyFrame storage) memory := by
  intro binding member
  cases member

theorem source_empty_frame_below (storage : Nat) : SourceLocalsBelow ⟨storage, 0, []⟩ := by
  intro binding member
  cases member

theorem target_empty_frame_below (storage : Nat) : TargetLocalsBelow (targetEmptyFrame storage) := by
  intro binding member
  cases member

end Mettapedia.GSLT.LanguageDef.NativeOps
