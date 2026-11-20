import Mettapedia.Machines.TIsa.NativeImage

/-!
# Checked label resolution and relative-branch byte emission

Chunks are assembler input data. Literal instruction bytes retain their own
execution contracts. Labels contribute no bytes; near branches use the existing
signed-displacement encoder and fail when a label or its displacement is invalid.
The generated branch records use the established native-image format.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Assembler

abbrev Byte := BitVec 8
abbrev Labels := List (Nat × Nat)

def opcodeBytes : Option (Fin 16) → List Byte
  | none => [0xe9]
  | some condition => [0x0f,BitVec.ofNat 8 (128 + condition.val)]

def prefixLength : Option (Fin 16) → Nat
  | none => 1
  | some _ => 2

theorem prefix_length (condition : Option (Fin 16)) :
    (opcodeBytes condition).length = prefixLength condition := by cases condition <;> rfl

inductive Chunk where
  | bytes (data : List Byte)
  | label (name : Nat)
  | branch (condition : Option (Fin 16)) (target : Nat)
  deriving DecidableEq, Repr

def Chunk.width : Chunk → Nat
  | .bytes data => data.length
  | .label _ => 0
  | .branch condition _ => prefixLength condition + 4

def width : List Chunk → Nat
  | [] => 0
  | head :: tail => head.width + width tail

theorem width_append (first second : List Chunk) : width (first ++ second) = width first + width second := by
  induction first with
  | nil => simp [width]
  | cons head tail ih => simp only [List.cons_append,width,ih,Nat.add_assoc]

def markersAt : Nat → List Chunk → Labels
  | _,[] => []
  | cursor,.label name :: tail => (name,cursor) :: markersAt cursor tail
  | cursor,head :: tail => markersAt (cursor + head.width) tail

theorem markersAt_append (cursor : Nat) (first second : List Chunk) :
    markersAt cursor (first ++ second) = markersAt cursor first ++ markersAt (cursor + width first) second := by
  induction first generalizing cursor with
  | nil => simp [markersAt,width]
  | cons head tail ih =>
    cases head <;> simp [markersAt,width,Chunk.width,ih,Nat.add_assoc]

def labelsAt : Nat → List Chunk → Option Labels
  | _,[] => some []
  | cursor,.label name :: tail => do
      let labels ← labelsAt cursor tail
      if labels.any (fun entry => entry.1 == name) then none else some ((name,cursor) :: labels)
  | cursor,head :: tail => labelsAt (cursor + head.width) tail

def lookup (labels : Labels) (name : Nat) : Option Nat :=
  (labels.find? (fun entry => entry.1 == name)).map Prod.snd

theorem labels_inside (cursor : Nat) (chunks : List Chunk) (labels : Labels)
    (resolved : labelsAt cursor chunks = some labels) :
    ∀ entry ∈ labels, cursor ≤ entry.2 ∧ entry.2 ≤ cursor + width chunks := by
  induction chunks generalizing cursor labels with
  | nil =>
    simp only [labelsAt,Option.some.injEq] at resolved
    subst labels
    simp
  | cons head tail ih =>
    cases head with
    | label name =>
      simp only [labelsAt,Option.bind_eq_bind] at resolved
      cases later : labelsAt cursor tail with
      | none => simp [later] at resolved
      | some entries =>
        rw [later] at resolved
        simp only [Option.bind_some] at resolved
        by_cases duplicate : entries.any (fun entry => entry.1 == name) = true
        · simp only [duplicate,ite_true] at resolved
          cases resolved
        · rw [if_neg duplicate] at resolved
          cases resolved
          intro entry member
          rcases List.mem_cons.mp member with rfl | following
          · simp [width,Chunk.width]
          · simpa only [width,Chunk.width,Nat.zero_add] using ih cursor entries later entry following
    | bytes data =>
      have next : labelsAt (cursor + data.length) tail = some labels := resolved
      intro entry member
      have inside := ih (cursor + data.length) labels next entry member
      change cursor ≤ entry.2 ∧ entry.2 ≤ cursor + (data.length + width tail)
      omega
    | branch condition target =>
      have next : labelsAt (cursor + (prefixLength condition + 4)) tail = some labels := resolved
      intro entry member
      have inside := ih (cursor + (prefixLength condition + 4)) labels next entry member
      change cursor ≤ entry.2 ∧ entry.2 ≤ cursor + (prefixLength condition + 4 + width tail)
      omega

theorem lookup_member (labels : Labels) (name target : Nat) (found : lookup labels name = some target) :
    (name,target) ∈ labels := by
  unfold lookup at found
  obtain ⟨entry,selected,result⟩ := Option.map_eq_some_iff.mp found
  have named := List.find?_some selected
  have same : entry.1 = name := beq_iff_eq.mp named
  obtain ⟨actual,value⟩ := entry
  dsimp only at result same
  subst actual
  subst value
  exact List.mem_of_find?_eq_some selected

theorem labelsAt_exact (cursor : Nat) (chunks : List Chunk) (labels : Labels)
    (resolved : labelsAt cursor chunks = some labels) :
    labels = markersAt cursor chunks ∧ (labels.map Prod.fst).Nodup := by
  induction chunks generalizing cursor labels with
  | nil =>
    have same : labels = [] := Option.some.inj resolved.symm
    subst labels
    exact ⟨rfl,by simp⟩
  | cons head tail ih =>
    cases head with
    | bytes data => exact ih (cursor + data.length) labels resolved
    | branch condition name => exact ih (cursor + (prefixLength condition + 4)) labels resolved
    | label name =>
      simp only [labelsAt,Option.bind_eq_bind] at resolved
      cases later : labelsAt cursor tail with
      | none => simp [later] at resolved
      | some entries =>
        rw [later] at resolved
        simp only [Option.bind_some] at resolved
        by_cases duplicate : entries.any (fun entry => entry.1 == name) = true
        · simp only [duplicate,ite_true] at resolved
          cases resolved
        · rw [if_neg duplicate] at resolved
          have same := Option.some.inj resolved
          subst labels
          obtain ⟨exactTail,uniqueTail⟩ := ih cursor entries later
          refine ⟨by simp only [markersAt,exactTail],?_⟩
          simp only [List.map_cons,List.nodup_cons]
          refine ⟨?_,uniqueTail⟩
          intro present
          obtain ⟨entry,member,named⟩ := List.mem_map.mp present
          exact duplicate (List.any_eq_true.mpr ⟨entry,member,beq_iff_eq.mpr named⟩)

theorem lookup_of_member (labels : Labels) (name target : Nat)
    (unique : (labels.map Prod.fst).Nodup) (member : (name,target) ∈ labels) : lookup labels name = some target := by
  induction labels with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | later
    · subst head
      simp [lookup]
    · by_cases same : head.1 = name
      · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨(name,target),later,rfl⟩))
      · simpa [lookup,same] using ih unique.2 later

theorem label_lookup (cursor : Nat) (chunks : List Chunk) (labels : Labels)
    (resolved : labelsAt cursor chunks = some labels) (name point : Nat)
    (marker : (name,point) ∈ markersAt cursor chunks) : lookup labels name = some point := by
  obtain ⟨exactLabels,unique⟩ := labelsAt_exact cursor chunks labels resolved
  exact lookup_of_member labels name point unique (exactLabels ▸ marker)

structure Fixup where
  offset : Nat
  condition : Option (Fin 16)
  label : Nat
  target : Nat
  deriving DecidableEq, Repr

def Fixup.field (fixup : Fixup) : Nat := fixup.offset + prefixLength fixup.condition

def Fixup.bytes (fixup : Fixup) : List Byte :=
  opcodeBytes fixup.condition ++ RelativeBranch.encode32
    (BitVec.ofInt 32 (RelativeBranch.displacement fixup.field fixup.target))

def Fixup.patch (fixup : Fixup) : NativeImage.Patch where
  opcodeOffset := fixup.offset
  fieldOffset := fixup.field
  nextIp := fixup.field + 4
  target := fixup.target
  opcode := match fixup.condition with
    | none => 0xe9
    | some condition => BitVec.ofNat 8 (128 + condition.val)
  conditional := fixup.condition.isSome
  relative := RelativeBranch.displacement fixup.field fixup.target
  patched := true

theorem Fixup.bytes_length (fixup : Fixup) :
    fixup.bytes.length = prefixLength fixup.condition + 4 := by
  rw [bytes,List.length_append,prefix_length,RelativeBranch.encode32_length]

structure Emission where
  bytes : List Byte
  fixups : List Fixup
  deriving DecidableEq, Repr

def emitAt (labels : Labels) : Nat → List Chunk → Option Emission
  | _,[] => some ⟨[],[]⟩
  | cursor,.label _ :: tail => emitAt labels cursor tail
  | cursor,.bytes data :: tail => do
      let later ← emitAt labels (cursor + data.length) tail
      pure ⟨data ++ later.bytes,later.fixups⟩
  | cursor,.branch condition name :: tail => do
      let target ← lookup labels name
      let operand ← RelativeBranch.encodeNear? (cursor + prefixLength condition) target
      let later ← emitAt labels (cursor + (prefixLength condition + 4)) tail
      pure ⟨(opcodeBytes condition ++ operand) ++ later.bytes,⟨cursor,condition,name,target⟩ :: later.fixups⟩

def Emission.join (first second : Emission) : Emission :=
  ⟨first.bytes ++ second.bytes,first.fixups ++ second.fixups⟩

theorem emitAt_append (labels : Labels) (cursor : Nat) (first second : List Chunk) :
    emitAt labels cursor (first ++ second) = (do
      let left ← emitAt labels cursor first
      let right ← emitAt labels (cursor + width first) second
      pure (left.join right)) := by
  induction first generalizing cursor with
  | nil =>
    cases computed : emitAt labels cursor second <;>
      simp [emitAt,width,Emission.join,Option.bind_eq_bind,computed]
  | cons head tail ih =>
    cases head <;>
      simp [emitAt,width,Chunk.width,Emission.join,ih,Option.bind_eq_bind,
        Option.bind_assoc,List.append_assoc,Nat.add_assoc]

theorem emitAt_split (labels : Labels) (cursor : Nat) (first second : List Chunk) (emission : Emission)
    (emitted : emitAt labels cursor (first ++ second) = some emission) :
    ∃ left right, emitAt labels cursor first = some left ∧
      emitAt labels (cursor + width first) second = some right ∧ emission = left.join right := by
  rw [emitAt_append] at emitted
  change (emitAt labels cursor first).bind (fun left =>
    (emitAt labels (cursor + width first) second).bind (fun right => some (left.join right))) = some emission at emitted
  cases firstResult : emitAt labels cursor first with
  | none => simp [firstResult] at emitted
  | some left =>
    rw [firstResult] at emitted
    change (emitAt labels (cursor + width first) second).bind (fun right => some (left.join right)) = some emission at emitted
    cases secondResult : emitAt labels (cursor + width first) second with
    | none => simp [secondResult] at emitted
    | some right =>
      rw [secondResult] at emitted
      change some (left.join right) = some emission at emitted
      exact ⟨left,right,rfl,rfl,(Option.some.inj emitted).symm⟩

def assemble (chunks : List Chunk) : Option Emission := do
  let labels ← labelsAt 0 chunks
  emitAt labels 0 chunks

structure Fixup.Recorded (labels : Labels) (cursor : Nat) (bytes : List Byte) (fixup : Fixup) : Prop where
  found : lookup labels fixup.label = some fixup.target
  fits : RelativeBranch.Fits32 (RelativeBranch.displacement fixup.field fixup.target)
  lower : cursor ≤ fixup.offset
  upper : fixup.offset + fixup.bytes.length ≤ cursor + bytes.length
  reads : ∀ index < fixup.bytes.length,
    bytes[fixup.offset - cursor + index]? = fixup.bytes[index]?

theorem Fixup.Recorded.prepend {labels : Labels} {cursor : Nat} {tail : List Byte} {fixup : Fixup}
    (head : List Byte) (recorded : fixup.Recorded labels (cursor + head.length) tail) :
    fixup.Recorded labels cursor (head ++ tail) where
  found := recorded.found
  fits := recorded.fits
  lower := by have := recorded.lower; omega
  upper := by have := recorded.upper; rw [List.length_append]; omega
  reads index within := by
    have coordinate : fixup.offset - cursor + index =
        head.length + (fixup.offset - (cursor + head.length) + index) := by have := recorded.lower; omega
    rw [coordinate,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact recorded.reads index within

theorem Fixup.recorded_head (labels : Labels) (cursor : Nat) (condition : Option (Fin 16))
    (name target : Nat) (tail : List Byte) (found : lookup labels name = some target)
    (fits : RelativeBranch.Fits32 (RelativeBranch.displacement (cursor + prefixLength condition) target)) :
    (Fixup.mk cursor condition name target).Recorded labels cursor
      ((Fixup.mk cursor condition name target).bytes ++ tail) where
  found := found
  fits := fits
  lower := Nat.le_refl _
  upper := by simp only [List.length_append]; omega
  reads index within := by
    simp only [Nat.sub_self,Nat.zero_add]
    exact List.getElem?_append_left within

theorem emitAt_correct (labels : Labels) (cursor : Nat) (chunks : List Chunk) (emission : Emission)
    (emitted : emitAt labels cursor chunks = some emission) :
    emission.bytes.length = width chunks ∧ ∀ fixup ∈ emission.fixups, fixup.Recorded labels cursor emission.bytes := by
  induction chunks generalizing cursor emission with
  | nil =>
    simp only [emitAt,Option.some.injEq] at emitted
    subst emission
    exact ⟨rfl,by simp⟩
  | cons head tail ih =>
    cases head with
    | label name =>
      simpa only [width,Chunk.width,Nat.zero_add] using ih cursor emission emitted
    | bytes data =>
      change (do let later ← emitAt labels (cursor + data.length) tail
                 pure (Emission.mk (data ++ later.bytes) later.fixups)) = some emission at emitted
      cases computed : emitAt labels (cursor + data.length) tail with
      | none => simp [computed] at emitted
      | some later =>
        rw [computed] at emitted
        change some (Emission.mk (data ++ later.bytes) later.fixups) = some emission at emitted
        have same := Option.some.inj emitted
        cases same
        obtain ⟨length,records⟩ := ih (cursor + data.length) later computed
        refine ⟨?_,?_⟩
        · simpa only [width,Chunk.width,List.length_append] using congrArg (data.length + ·) length
        · intro fixup member
          exact (records fixup member).prepend data
    | branch condition name =>
      simp only [emitAt] at emitted
      cases found : lookup labels name with
      | none => simp [found] at emitted
      | some target =>
        rw [found] at emitted
        change (do
          let operand ← RelativeBranch.encodeNear? (cursor + prefixLength condition) target
          let later ← emitAt labels (cursor + (prefixLength condition + 4)) tail
          pure (Emission.mk ((opcodeBytes condition ++ operand) ++ later.bytes)
            (Fixup.mk cursor condition name target :: later.fixups))) = some emission at emitted
        cases encoded : RelativeBranch.encodeNear? (cursor + prefixLength condition) target with
        | none => simp [encoded] at emitted
        | some operand =>
          rw [encoded] at emitted
          change (do
            let later ← emitAt labels (cursor + (prefixLength condition + 4)) tail
            pure (Emission.mk ((opcodeBytes condition ++ operand) ++ later.bytes)
              (Fixup.mk cursor condition name target :: later.fixups))) = some emission at emitted
          cases computed : emitAt labels (cursor + (prefixLength condition + 4)) tail with
          | none => simp [computed] at emitted
          | some later =>
            rw [computed] at emitted
            change some (Emission.mk ((opcodeBytes condition ++ operand) ++ later.bytes)
              (Fixup.mk cursor condition name target :: later.fixups)) = some emission at emitted
            have same := Option.some.inj emitted
            cases same
            obtain ⟨fits,operandEq⟩ := (RelativeBranch.encodeNear?_iff _ _ _).mp encoded
            let fixup : Fixup := ⟨cursor,condition,name,target⟩
            have bytesEq : opcodeBytes condition ++ operand = fixup.bytes := by rw [operandEq]; rfl
            obtain ⟨length,records⟩ := ih (cursor + (prefixLength condition + 4)) later computed
            refine ⟨?_,?_⟩
            · change ((opcodeBytes condition ++ operand) ++ later.bytes).length =
                prefixLength condition + 4 + width tail
              rw [bytesEq,List.length_append,Fixup.bytes_length,length]
            · intro selected member
              rcases List.mem_cons.mp member with rfl | following
              · rw [bytesEq]
                exact Fixup.recorded_head labels cursor condition name target later.bytes found fits
              · rw [bytesEq]
                exact Fixup.Recorded.prepend (cursor := cursor) fixup.bytes
                  (by simpa only [Fixup.bytes_length] using records selected following)

theorem assemble_correct (chunks : List Chunk) (emission : Emission)
    (assembled : assemble chunks = some emission) :
    emission.bytes.length = width chunks ∧
      ∃ labels, labelsAt 0 chunks = some labels ∧
        ∀ fixup ∈ emission.fixups, fixup.Recorded labels 0 emission.bytes ∧ fixup.target ≤ emission.bytes.length := by
  unfold assemble at assembled
  cases resolved : labelsAt 0 chunks with
  | none => simp [resolved] at assembled
  | some labels =>
    rw [resolved] at assembled
    change emitAt labels 0 chunks = some emission at assembled
    obtain ⟨length,records⟩ := emitAt_correct labels 0 chunks emission assembled
    refine ⟨length,labels,rfl,?_⟩
    intro fixup member
    have record := records fixup member
    have inside := labels_inside 0 chunks labels resolved (fixup.label,fixup.target)
      (lookup_member labels fixup.label fixup.target record.found)
    exact ⟨record,by rw [length]; simpa only [Nat.zero_add] using inside.2⟩

def view (bytes : List Byte) : NativeImage.View := ⟨bytes.length,fun index => bytes[index]?⟩

theorem Fixup.Recorded.opcode_reads {labels : Labels} {bytes : List Byte} {fixup : Fixup}
    (recorded : fixup.Recorded labels 0 bytes) (index : Nat) (within : index < prefixLength fixup.condition) :
    (view bytes).read (fixup.offset + index) = (opcodeBytes fixup.condition)[index]? := by
  have got := recorded.reads index (by rw [Fixup.bytes_length]; omega)
  simp only [Nat.sub_zero] at got
  rw [Fixup.bytes,List.getElem?_append_left (by simpa only [prefix_length] using within)] at got
  exact got

theorem Fixup.Recorded.operand_reads {labels : Labels} {bytes : List Byte} {fixup : Fixup}
    (recorded : fixup.Recorded labels 0 bytes) (index : Nat) (within : index < 4) :
    (view bytes).read (fixup.field + index) =
      (RelativeBranch.encode32 (BitVec.ofInt 32 (RelativeBranch.displacement fixup.field fixup.target)))[index]? := by
  have got := recorded.reads (prefixLength fixup.condition + index) (by rw [Fixup.bytes_length]; omega)
  have coordinate : fixup.offset - 0 + (prefixLength fixup.condition + index) = fixup.field + index := by
    simp only [Fixup.field]
    omega
  rw [coordinate,Fixup.bytes,List.getElem?_append_right (by rw [prefix_length]; omega),prefix_length,
    Nat.add_sub_cancel_left] at got
  exact got

private theorem readFour_of_reads (image : NativeImage.View) (offset : Nat) (bytes : List Byte)
    (length : bytes.length = 4) (reads : ∀ index < 4, image.read (offset + index) = bytes[index]?) :
    NativeImage.readFour? image offset = some bytes := by
  obtain ⟨a,b,c,d,rfl⟩ := List.length_eq_four.mp length
  have first : image.read offset = some a := by simpa using reads 0 (by decide)
  have second : image.read (offset + 1) = some b := by simpa using reads 1 (by decide)
  have third : image.read (offset + 2) = some c := by simpa using reads 2 (by decide)
  have fourth : image.read (offset + 3) = some d := by simpa using reads 3 (by decide)
  rw [NativeImage.readFour?,first,second,third,fourth]
  rfl

theorem Fixup.Recorded.readFour {labels : Labels} {bytes : List Byte} {fixup : Fixup}
    (recorded : fixup.Recorded labels 0 bytes) :
    NativeImage.readFour? (view bytes) fixup.field = some
      (RelativeBranch.encode32 (BitVec.ofInt 32 (RelativeBranch.displacement fixup.field fixup.target))) :=
  readFour_of_reads (view bytes) fixup.field _ (RelativeBranch.encode32_length _) recorded.operand_reads

theorem Fixup.Recorded.prefix_checked {labels : Labels} {bytes : List Byte} {fixup : Fixup}
    (recorded : fixup.Recorded labels 0 bytes) : fixup.patch.prefixCheck (view bytes) = true := by
  obtain ⟨offset,condition,name,target⟩ := fixup
  cases condition with
  | none =>
    have first := recorded.opcode_reads 0 (by change (0 : Nat) < 1; decide)
    change bytes[offset]? = some (0xe9#8) at first
    simp [NativeImage.Patch.prefixCheck,Fixup.patch,Fixup.field,view,prefixLength,first]
  | some condition =>
    have first := recorded.opcode_reads 0 (by change (0 : Nat) < 2; decide)
    have second := recorded.opcode_reads 1 (by change (1 : Nat) < 2; decide)
    change bytes[offset]? = some (0x0f#8) at first
    change bytes[offset + 1]? = some (BitVec.ofNat 8 (128 + condition.val)) at second
    have decoded : (BitVec.ofNat 8 (128 + condition.val)).toNat = 128 + condition.val := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := condition.isLt; omega)]
    have range : 128 ≤ (BitVec.ofNat 8 (128 + condition.val)).toNat ∧
        (BitVec.ofNat 8 (128 + condition.val)).toNat < 144 := by
      rw [decoded]
      have := condition.isLt
      omega
    simpa [NativeImage.Patch.prefixCheck,Fixup.patch,Fixup.field,view,prefixLength,first,second] using range

theorem Fixup.Recorded.patch_checked {labels : Labels} {bytes : List Byte} {fixup : Fixup}
    (recorded : fixup.Recorded labels 0 bytes) (targetInside : fixup.target ≤ bytes.length) :
    fixup.patch.check (view bytes) 0 bytes.length = true := by
  have read := recorded.readFour
  have fieldEnd : fixup.field + 4 ≤ bytes.length := by
    have upper := recorded.upper
    rw [Fixup.bytes_length] at upper
    simp only [Fixup.field]
    omega
  have signed : (BitVec.ofInt 32 (RelativeBranch.displacement fixup.field fixup.target)).toInt =
      RelativeBranch.displacement fixup.field fixup.target :=
    BitVec.toInt_ofInt_eq_self (by decide) recorded.fits.1 recorded.fits.2
  have target := RelativeBranch.encoded_target_exact fixup.field fixup.target _
    ((RelativeBranch.encodeNear?_iff _ _ _).mpr ⟨recorded.fits,rfl⟩)
  unfold NativeImage.Patch.check
  change (match NativeImage.readFour? (view bytes) fixup.field with
    | none => false
    | some actual => true && fixup.patch.prefixCheck (view bytes) &&
        (fixup.field + 4 == fixup.field + 4) &&
        decide (0 ≤ fixup.offset ∧ fixup.field + 4 ≤ bytes.length ∧ 0 ≤ fixup.target ∧ fixup.target ≤ bytes.length) &&
        decide ((RelativeBranch.decode32 actual).toInt = RelativeBranch.displacement fixup.field fixup.target) &&
        decide (RelativeBranch.decodedTarget fixup.field actual = (fixup.target : Int))) = true
  rw [read]
  dsimp only
  rw [recorded.prefix_checked,RelativeBranch.decode_encode32,signed,target]
  simp only [beq_self_eq_true,Bool.true_and,Bool.and_true,decide_true,decide_eq_true_eq]
  exact ⟨Nat.zero_le _,fieldEnd,Nat.zero_le _,targetInside⟩

theorem assemble_checked (chunks : List Chunk) (emission : Emission)
    (assembled : assemble chunks = some emission) :
    emission.bytes.length = width chunks ∧
      ∀ fixup ∈ emission.fixups, fixup.patch.check (view emission.bytes) 0 emission.bytes.length = true := by
  obtain ⟨length,_labels,_resolved,records⟩ := assemble_correct chunks emission assembled
  exact ⟨length,fun fixup member => (records fixup member).1.patch_checked (records fixup member).2⟩

def relocationsAt : Nat → List Chunk → List (Nat × Nat)
  | _,[] => []
  | cursor,.label _ :: tail => relocationsAt cursor tail
  | cursor,.bytes data :: tail => relocationsAt (cursor + data.length) tail
  | cursor,.branch condition name :: tail =>
      (cursor + prefixLength condition,name) :: relocationsAt (cursor + (prefixLength condition + 4)) tail

def Patchable (labels : Labels) (cursor : Nat) (chunks : List Chunk) : Prop :=
  ∀ field name, (field,name) ∈ relocationsAt cursor chunks →
    ∃ target, lookup labels name = some target ∧ RelativeBranch.Fits32 (RelativeBranch.displacement field target)

theorem emitAt_succeeds (labels : Labels) (cursor : Nat) (chunks : List Chunk)
    (patchable : Patchable labels cursor chunks) : ∃ emission, emitAt labels cursor chunks = some emission := by
  induction chunks generalizing cursor with
  | nil => exact ⟨⟨[],[]⟩,rfl⟩
  | cons head tail ih =>
    cases head with
    | label name => exact ih cursor patchable
    | bytes data =>
      obtain ⟨later,emitted⟩ := ih (cursor + data.length) patchable
      refine ⟨⟨data ++ later.bytes,later.fixups⟩,?_⟩
      change (emitAt labels (cursor + data.length) tail).bind
        (fun later => some (Emission.mk (data ++ later.bytes) later.fixups)) = _
      rw [emitted]
      rfl
    | branch condition name =>
      obtain ⟨target,found,fits⟩ := patchable (cursor + prefixLength condition) name (List.mem_cons_self)
      have laterPatchable : Patchable labels (cursor + (prefixLength condition + 4)) tail := by
        intro field label member
        exact patchable field label (List.mem_cons_of_mem _ member)
      obtain ⟨later,emitted⟩ := ih _ laterPatchable
      let operand := RelativeBranch.encode32 (BitVec.ofInt 32 (RelativeBranch.displacement (cursor + prefixLength condition) target))
      have encoded : RelativeBranch.encodeNear? (cursor + prefixLength condition) target = some operand :=
        (RelativeBranch.encodeNear?_iff _ _ _).mpr ⟨fits,rfl⟩
      refine ⟨⟨(opcodeBytes condition ++ operand) ++ later.bytes,⟨cursor,condition,name,target⟩ :: later.fixups⟩,?_⟩
      change (lookup labels name).bind (fun target =>
        (RelativeBranch.encodeNear? (cursor + prefixLength condition) target).bind (fun actual =>
          (emitAt labels (cursor + (prefixLength condition + 4)) tail).bind (fun later =>
            some (Emission.mk ((opcodeBytes condition ++ actual) ++ later.bytes)
              (Fixup.mk cursor condition name target :: later.fixups))))) = _
      rw [found]
      dsimp only [Option.bind]
      rw [encoded]
      dsimp only [Option.bind]
      rw [emitted]

theorem assemble_succeeds (chunks : List Chunk) (labels : Labels)
    (resolved : labelsAt 0 chunks = some labels) (patchable : Patchable labels 0 chunks) :
    ∃ emission, assemble chunks = some emission := by
  obtain ⟨emission,emitted⟩ := emitAt_succeeds labels 0 chunks patchable
  refine ⟨emission,?_⟩
  unfold assemble
  rw [resolved]
  exact emitted

namespace Controls

def forward : List Chunk := [.branch none 1,.bytes [0x90],.label 1]
def forwardEmission : Emission := ⟨[0xe9,1,0,0,0,0x90],[⟨0,none,1,6⟩]⟩

theorem forward_assembled : assemble forward = some forwardEmission := by decide

theorem backward_assembled :
    assemble [.label 0,.bytes [0x90],.branch (some 4) 0] =
      some ⟨[0x90,0x0f,0x84,0xf9,0xff,0xff,0xff],[⟨1,some 4,0,0⟩]⟩ := by decide

theorem unknown_label_refused : assemble [.branch none 42] = none := by decide

theorem duplicate_label_refused : assemble [.label 1,.label 1] = none := by decide

theorem overflow_refused : emitAt [(1,2147483653)] 0 [.branch none 1] = none := by decide

theorem changed_target_byte_refused :
    (Fixup.mk 0 none 1 6).patch.check (view [0xe9,2,0,0,0,0x90]) 0 6 = false := by decide

end Controls

end Mettapedia.Machines.TIsa.X86Assembler
