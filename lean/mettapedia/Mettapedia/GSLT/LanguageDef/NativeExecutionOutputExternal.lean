import Mettapedia.GSLT.LanguageDef.NativeExecutionMatchesExternal

/-!
The borrowed output view returned by the native execution-output interface.
Ownership lookup precedes all observation payload reads. A completed physical
observation has eight ABI fields: four pointers followed by four unsigned
lengths. Its output starts after the length header in output_storage. The
logical header extent is an explicit ABI parameter; its concrete sizeof and
pointer realization remain physical interface obligations. No copy or new
operational allocation is performed by this call.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionOutputExternal

open NativeOps (Address SourceMemory TargetMemory SourceValue TargetValue SourceState
  TargetState StateRelated MemoryRelated encodeValue encodeValues SourceExternalSemantics
  TargetExternalSemantics ExternalCorrespondence)
open NativeExecutionMatchesExternal (World)
open NativeWord64 (Word encode)

def sourcePointer : SourceValue → Option (Option Address)
  | .reference pointer => some pointer
  | _ => none

def targetPointer : TargetValue → Option (Option Address)
  | .reference pointer => some pointer
  | _ => none

def sourceLength : SourceValue → Option Word
  | .word length => some length
  | _ => none

def targetLength : TargetValue → Option (BitVec 64)
  | .word length => some length
  | _ => none

theorem pointer_correspondence (value : SourceValue) :
    targetPointer (encodeValue value) = sourcePointer value := by cases value <;> rfl

theorem length_correspondence (value : SourceValue) :
    targetLength (encodeValue value) = (sourceLength value).map encode := by cases value <;> rfl

theorem encoded_fields_length (fields : List SourceValue) :
    (encodeValues fields).length = fields.length := by
  induction fields with
  | nil => rfl
  | cons value rest ih => simp only [encodeValues, List.length_cons, ih]

def sourceFields : SourceValue → Option (List SourceValue)
  | .record name fields => if name = "Observation" ∧ fields.length = 8 then some fields else none
  | _ => none

def targetFields : TargetValue → Option (List TargetValue)
  | .record name fields => if fields.length = 8 then
      if name = "Observation" then some fields else none else none
  | _ => none

theorem fields_correspondence (value : SourceValue) :
    targetFields (encodeValue value) = (sourceFields value).map encodeValues := by
  cases value <;> try rfl
  case record name fields =>
    by_cases named : name = "Observation" <;> by_cases length : fields.length = 8 <;>
      simp only [encodeValue, targetFields, sourceFields, encoded_fields_length,
        named, length, and_self, and_true, and_false, if_true, if_false,
        Option.map_some, Option.map_none]

def sourceStoredOutput (header : Nat) (value : SourceValue) : Option SourceValue := do
  let fields ← sourceFields value
  let pointerValue ← fields[3]?
  let pointer ← sourcePointer pointerValue
  let lengthValue ← fields[7]?
  let length ← sourceLength lengthValue
  let base ← pointer
  some (.array .byte (some { base with element := base.element + header }) length)

def targetStoredOutput (header : Nat) (value : TargetValue) : Option TargetValue :=
  match targetFields value with
  | none => none
  | some fields =>
    match fields[3]? with
    | none => none
    | some pointerValue =>
      match targetPointer pointerValue with
      | none => none
      | some pointer =>
        match fields[7]? with
        | none => none
        | some lengthValue =>
          match targetLength lengthValue with
          | none => none
          | some length =>
            match pointer with
            | none => none
            | some base => some (.array .byte
                (some { base with element := base.element + header }) length)

theorem stored_output_correspondence (header : Nat) (value : SourceValue) :
    targetStoredOutput header (encodeValue value) =
      (sourceStoredOutput header value).map encodeValue := by
  simp only [targetStoredOutput, sourceStoredOutput, fields_correspondence]
  cases fields : sourceFields value with
  | none => rfl
  | some values =>
    simp only [Option.map_some, bind, Option.bind_some, NativeOps.encodeValues_getElem?]
    cases pointerValue : values[3]? with
    | none => rfl
    | some pointerCell =>
      simp only [Option.map_some, pointer_correspondence, Option.bind_some]
      cases pointer : sourcePointer pointerCell with
      | none => rfl
      | some base =>
        cases lengthValue : values[7]? with
        | none => rfl
        | some lengthCell =>
          simp only [Option.map_some, length_correspondence, Option.bind_some]
          cases length : sourceLength lengthCell with
          | none => rfl
          | some count => cases base <;> rfl

def sourceObservationOutput (header : Nat) (memory : SourceMemory) (handle : Address) :
    Option SourceValue := do
  let value ← NativeOps.sourceRead memory handle
  sourceStoredOutput header value

def targetObservationOutput (header : Nat) (memory : TargetMemory) (handle : Address) :
    Option TargetValue :=
  match NativeOps.targetRead memory handle with
  | none => none
  | some value => targetStoredOutput header value

theorem observation_output_correspondence (header : Nat) (source : SourceMemory)
    (target : TargetMemory) (related : MemoryRelated source target) (handle : Address) :
    targetObservationOutput header target handle =
      (sourceObservationOutput header source handle).map encodeValue := by
  simp only [targetObservationOutput, sourceObservationOutput,
    NativeOps.memory_read_correspondence source target related]
  cases read : NativeOps.sourceRead source handle with
  | none => rfl
  | some value =>
    simp only [Option.map_some, bind, Option.bind_some]
    exact stored_output_correspondence header value

def sourceCall (header : Nat) (memory : SourceMemory) (world : World) :
    List SourceValue → Option SourceValue
  | [.reference scopePointer, .reference observationPointer] => do
    let scope ← NativeExecutionMatchesExternal.sourceScope world scopePointer
    match NativeExecutionScope.sourceRead scope observationPointer with
    | none => some (.array .byte none 0)
    | some _ => do
      let handle ← observationPointer
      sourceObservationOutput header memory handle
  | _ => none

def targetCall (header : Nat) (memory : TargetMemory) (world : World) :
    List TargetValue → Option TargetValue
  | [.reference scopePointer, .reference observationPointer] =>
    match NativeExecutionMatchesExternal.targetScope world scopePointer with
    | none => none
    | some scope =>
      match NativeExecutionScope.targetRead scope observationPointer with
      | none => some (.array .byte none 0)
      | some _ => match observationPointer with
        | none => none
        | some handle => targetObservationOutput header memory handle
  | _ => none

theorem typed_call_correspondence (header : Nat) (source : SourceState World)
    (target : TargetState World) (related : StateRelated Eq source target)
    (scopePointer observationPointer : Option Address) :
    targetCall header target.memory target.external
      [.reference scopePointer, .reference observationPointer] =
      (sourceCall header source.memory source.external
        [.reference scopePointer, .reference observationPointer]).map encodeValue := by
  simp only [sourceCall, targetCall, ← related.external,
    NativeExecutionMatchesExternal.scope_correspondence, NativeExecutionScope.read_correspondence]
  cases found : NativeExecutionMatchesExternal.sourceScope source.external scopePointer with
  | none => rfl
  | some scope =>
    simp only [bind, Option.bind_some]
    cases read : NativeExecutionScope.sourceRead scope observationPointer with
    | none => rfl
    | some observation =>
      cases observationPointer with
      | none => rfl
      | some handle =>
        exact observation_output_correspondence header source.memory
          target.memory related.memory handle

theorem call_correspondence (header : Nat) (source : SourceState World)
    (target : TargetState World) (related : StateRelated Eq source target)
    (arguments : List SourceValue) :
    targetCall header target.memory target.external (encodeValues arguments) =
      (sourceCall header source.memory source.external arguments).map encodeValue := by
  rcases arguments with _ | ⟨scopeValue, rest⟩
  · rfl
  rcases rest with _ | ⟨observationValue, rest⟩
  · cases scopeValue <;> rfl
  rcases rest with _ | ⟨extra, rest⟩
  · cases scopeValue <;> try rfl
    case reference scopePointer =>
      cases observationValue <;> try rfl
      case reference observationPointer =>
        exact typed_call_correspondence header source target related scopePointer observationPointer
  · cases scopeValue <;> cases observationValue <;> rfl

def sourceExternal (header : Nat) : SourceExternalSemantics World :=
  ⟨fun name arguments pre raw post => name = "execution-output" ∧
    sourceCall header pre.memory pre.external arguments = some raw ∧ post = pre⟩

def targetExternal (header : Nat) : TargetExternalSemantics World :=
  ⟨fun name arguments pre raw post => name = "execution-output" ∧
    targetCall header pre.memory pre.external arguments = some raw ∧ post = pre⟩

theorem external_correspondence (header : Nat) :
    ExternalCorrespondence (sourceExternal header) (targetExternal header) Eq := by
  constructor
  · intro name arguments sourcePre targetPre sourceRaw sourcePost related called
    obtain ⟨named, executed, unchanged⟩ := called
    subst sourcePost
    refine ⟨targetPre, ⟨named, ?_, rfl⟩, related⟩
    rw [call_correspondence header sourcePre targetPre related arguments, executed]
    rfl
  · intro name arguments sourcePre targetPre targetRaw targetPost related called
    obtain ⟨named, executed, unchanged⟩ := called
    subst targetPost
    rw [call_correspondence header sourcePre targetPre related arguments] at executed
    cases result : sourceCall header sourcePre.memory sourcePre.external arguments with
    | none => simp only [result, Option.map_none] at executed; cases executed
    | some value =>
      have rawEqual : encodeValue value = targetRaw := by
        apply Option.some.inj
        simpa only [result, Option.map_some] using executed
      exact ⟨value, sourcePre, ⟨named, result, rfl⟩, rawEqual.symm, related⟩

theorem stored_output_shape (header : Nat) (value output : SourceValue)
    (returned : sourceStoredOutput header value = some output) :
    ∃ pointer length, output = .array .byte pointer length := by
  simp only [sourceStoredOutput] at returned
  cases fields : sourceFields value with
  | none => simp only [fields, bind, Option.bind_none] at returned; cases returned
  | some values =>
    simp only [fields, bind, Option.bind_some] at returned
    cases pointerValue : values[3]? with
    | none => simp only [pointerValue, Option.bind_none] at returned; cases returned
    | some pointerCell =>
      simp only [pointerValue, Option.bind_some] at returned
      cases pointer : sourcePointer pointerCell with
      | none => simp only [pointer, Option.bind_none] at returned; cases returned
      | some base =>
        simp only [pointer, Option.bind_some] at returned
        cases lengthValue : values[7]? with
        | none => simp only [lengthValue, Option.bind_none] at returned; cases returned
        | some lengthCell =>
          simp only [lengthValue, Option.bind_some] at returned
          cases length : sourceLength lengthCell with
          | none => simp only [length, Option.bind_none] at returned; cases returned
          | some count =>
            simp only [length, Option.bind_some] at returned
            cases base with
            | none => cases returned
            | some address =>
              exact ⟨some { address with element := address.element + header }, count,
                (Option.some.inj returned).symm⟩

theorem observation_output_shape (header : Nat) (memory : SourceMemory)
    (handle : Address) (output : SourceValue)
    (returned : sourceObservationOutput header memory handle = some output) :
    ∃ pointer length, output = .array .byte pointer length := by
  cases read : NativeOps.sourceRead memory handle with
  | none => simp only [sourceObservationOutput, read, bind, Option.bind_none] at returned
            cases returned
  | some value =>
    have projected : sourceStoredOutput header value = some output := by
      simpa only [sourceObservationOutput, read, bind, Option.bind_some] using returned
    exact stored_output_shape header value output projected

theorem typed_source_output_shape (header : Nat) (memory : SourceMemory)
    (world : World) (scopePointer observationPointer : Option Address) (output : SourceValue)
    (returned : sourceCall header memory world
      [.reference scopePointer, .reference observationPointer] = some output) :
    ∃ pointer length, output = .array .byte pointer length := by
  cases found : NativeExecutionMatchesExternal.sourceScope world scopePointer with
  | none => simp only [sourceCall, found, bind, Option.bind_none] at returned; cases returned
  | some scope =>
    simp only [sourceCall, found, bind, Option.bind_some] at returned
    cases read : NativeExecutionScope.sourceRead scope observationPointer with
    | none =>
      exact ⟨none, 0, (Option.some.inj (by simpa only [read] using returned)).symm⟩
    | some observation =>
      cases observationPointer with
      | none => simp only [read, Option.bind_none] at returned; cases returned
      | some handle =>
        have projected : sourceObservationOutput header memory handle = some output := by
          simpa only [read, Option.bind_some] using returned
        exact observation_output_shape header memory handle output projected

theorem target_checked_call (header : Nat) (source : SourceState World)
    (target post : TargetState World) (related : StateRelated Eq source target)
    (scopePointer observationPointer : Option Address) (raw : TargetValue)
    (called : (targetExternal header).call "execution-output"
      [.reference scopePointer, .reference observationPointer] target raw post)
    (contextChecked : (NativeOps.targetObserve post raw).result = .ok raw) :
    ∃ pointer length, raw = .array .byte pointer (encode length) ∧
      post = target ∧ target.fault = none := by
  obtain ⟨sourceRaw, sourcePost, sourceCalled, rawEqual, _⟩ :=
    (external_correspondence header).backward "execution-output"
      [.reference scopePointer, .reference observationPointer] source target raw post related called
  obtain ⟨pointer, length, shape⟩ := typed_source_output_shape header source.memory source.external
    scopePointer observationPointer sourceRaw sourceCalled.2.1
  have unchanged := called.2.2
  have clear := ((NativeOps.target_normal_result_iff post raw raw).mp contextChecked).1
  refine ⟨pointer, length, ?_, unchanged, unchanged ▸ clear⟩
  rw [rawEqual, shape]
  rfl

private def scopeAddress : Address := ⟨1, 0, []⟩
private def handle : Address := ⟨2, 0, []⟩
private def storage : Address := ⟨3, 0, []⟩
private def emptyMemory : SourceMemory := ⟨fun _ _ => none, fun _ => none⟩
private def emptyObservation : NativeExecutionScope.Observation := ⟨⟨⟨[], [], []⟩, 0⟩, []⟩
private def ownedWorld : World := ⟨[⟨scopeAddress, [⟨handle, emptyObservation⟩]⟩]⟩
private def observationRecord (length : Word) : SourceValue := .record "Observation"
  [.reference none, .reference none, .reference none, .reference (some storage),
    .word 0, .word 0, .word 0, .word length]
private def observationMemory : SourceMemory :=
  ⟨fun candidate index => if candidate = 2 ∧ index = 0 then
      some (observationRecord 0) else none, fun _ => none⟩

theorem owned_empty_output_preserves_its_borrowed_pointer :
    sourceCall 8 observationMemory ownedWorld [.reference (some scopeAddress),
      .reference (some handle)] = some (.array .byte (some ⟨3, 8, []⟩) 0) := rfl

theorem foreign_handle_returns_empty_before_reading_payload :
    sourceCall 8 emptyMemory ownedWorld [.reference (some scopeAddress),
      .reference (some ⟨9, 0, []⟩)] = some (.array .byte none 0) := rfl

theorem null_scope_returns_empty_before_reading_payload :
    sourceCall 8 emptyMemory ownedWorld [.reference none,
      .reference (some handle)] = some (.array .byte none 0) := rfl

theorem owned_missing_payload_is_undefined :
    sourceCall 8 emptyMemory ownedWorld [.reference (some scopeAddress),
      .reference (some handle)] = none := rfl

theorem incorrect_payload_shape_is_undefined :
    sourceStoredOutput 8 (.record "Observation" [.reference (some storage), .word 0]) = none := rfl

theorem null_output_storage_is_undefined :
    sourceStoredOutput 8 (.record "Observation"
      [.reference none, .reference none, .reference none, .reference none,
        .word 0, .word 0, .word 0, .word 0]) = none := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionOutputExternal
