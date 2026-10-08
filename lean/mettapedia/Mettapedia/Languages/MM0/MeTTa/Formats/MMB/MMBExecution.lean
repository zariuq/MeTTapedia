import Mettapedia.Languages.MM0.MeTTa.Formats.MMU.MMUResolution
import Mettapedia.Languages.MM0.Formats.MMB.Decode
import Mettapedia.Languages.MM0.Formats.MMB.Soundness

/-!
# Binary declaration metadata and execution correspondence

Source declarations retain explicit locality and byte intervals independently
of the reference machine's logical statements. Forgetting this metadata does
not reorder proof commands. Binary public and local identity remapping and the
native witness elaborator use the same independent specification service.

File and byte-string primitives are an explicit native boundary. The full MMB
proof-machine soundness theorem is separate from these decoder laws.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.MMBExecution

open Formats.MMB

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SpaceSemantics (Program)
open Eval
open Effects (boolean)
open Store (natural)
open scoped ProgramQuotation

def binarySource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/mmb.metta"
    sha256 "832e4e0da71881fd16752f99d79455b2b41eda0321bd4acea32e4b147f799aaa"

def program : Program := MMUResolution.program.append binarySource.program

/-- Constructor metadata uses the existing atom and natural codecs. It does
not encode raw binary bytes as a Unicode string. -/
def commandValue (opcode data start after : Nat) : Atom :=
  .expression [.symbol "MM0:MMBCode", natural opcode, natural data,
    natural start, natural after]

def decodeCommand : Atom → Option (Nat × Nat × Nat × Nat)
  | .expression [.symbol "MM0:MMBCode", opcode, data, start, after] => do
      let opcode ← MMUResolution.decodeNatural opcode
      let data ← MMUResolution.decodeNatural data
      let start ← MMUResolution.decodeNatural start
      let after ← MMUResolution.decodeNatural after
      pure (opcode, data, start, after)
  | _ => none

@[simp] theorem decodeCommand_commandValue (opcode data start after : Nat) :
    decodeCommand (commandValue opcode data start after) = some (opcode, data, start, after) := by
  simp [decodeCommand, commandValue, MMUResolution.decodeNatural, natural]

theorem decodeCommand_reflects (atom : Atom) (opcode data start after : Nat)
    (decoded : decodeCommand atom = some (opcode, data, start, after)) :
    atom = commandValue opcode data start after := by
  unfold decodeCommand at decoded
  split at decoded
  · rename_i rawOpcode rawData rawStart rawAfter
    obtain ⟨actualOpcode, opcodeRead, following⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨actualData, dataRead, following⟩ := Option.bind_eq_some_iff.mp following
    obtain ⟨actualStart, startRead, following⟩ := Option.bind_eq_some_iff.mp following
    obtain ⟨actualAfter, afterRead, output⟩ := Option.bind_eq_some_iff.mp following
    have same : (actualOpcode, actualData, actualStart, actualAfter) =
        (opcode, data, start, after) := Option.some.inj output
    rw [MMUResolution.decodeNatural_reflects rawOpcode actualOpcode opcodeRead,
      MMUResolution.decodeNatural_reflects rawData actualData dataRead,
      MMUResolution.decodeNatural_reflects rawStart actualStart startRead,
      MMUResolution.decodeNatural_reflects rawAfter actualAfter afterRead]
    cases same
    rfl
  · simp at decoded

theorem negative_command_position_rejected :
    decodeCommand (.expression [.symbol "MM0:MMBCode", natural 16, natural 0,
      .grounded (.int (-1)), natural 2]) = none := by decide

theorem malformed_command_constructor_rejected :
    decodeCommand (.expression [.symbol "MM0:MMBCode", natural 16, natural 0,
      natural 2]) = none := by decide

theorem u8_bounded (bytes : ByteArray) (at_ value : Nat)
    (read : Decode.u8 bytes at_ = some value) : at_ < bytes.size ∧ value < 256 := by
  obtain ⟨byte, found, rfl⟩ := Option.map_eq_some_iff.mp read
  have inside := (getElem?_eq_some_iff.mp found).choose
  exact ⟨inside, byte.toNat_lt⟩

theorem le_bounded (bytes : ByteArray) (at_ count value : Nat)
    (positive : 0 < count) (read : Decode.le bytes at_ count = some value) :
    at_ + count ≤ bytes.size := by
  induction count generalizing at_ value with
  | zero => omega
  | succ count ih =>
      cases low : Decode.u8 bytes at_ with
      | none => simp [Decode.le, low] at read
      | some first =>
          cases high : Decode.le bytes (at_ + 1) count with
          | none => simp [Decode.le, low, high] at read
          | some rest =>
              have firstInside := (u8_bounded bytes at_ first low).1
              by_cases empty : count = 0
              · omega
              · have restInside := ih (at_ + 1) rest (by omega) high
                omega

theorem command_bounded (bytes : ByteArray) (at_ opcode data size : Nat)
    (read : Decode.command bytes at_ = some (opcode, data, size)) :
    0 < size ∧ at_ + size ≤ bytes.size := by
  cases byteRead : Decode.u8 bytes at_ with
  | none => simp [Decode.command, byteRead] at read
  | some byte =>
      have inside := (u8_bounded bytes at_ byte byteRead).1
      have widths : byte / 64 = 0 ∨ byte / 64 = 1 ∨ byte / 64 = 2 ∨
          (byte / 64 ≠ 0 ∧ byte / 64 ≠ 1 ∧ byte / 64 ≠ 2) := by omega
      rcases widths with width | width | width | width
      all_goals simp_all [Decode.command, Decode.u16, Decode.u32, Option.bind_eq_some_iff]
      · omega
      · have next := (u8_bounded bytes (at_ + 1) data read.1).1
        omega
      · have next := le_bounded bytes (at_ + 1) 2 data (by decide) read.1
        omega
      · have next := le_bounded bytes (at_ + 1) 4 data (by decide) read.1
        omega

theorem proofStream_bounded (bytes : ByteArray) (fuel at_ after : Nat) (proof : List ProofCmd)
    (read : Decode.proofStream bytes fuel at_ = some (proof, after)) :
    at_ < after ∧ after ≤ bytes.size := by
  induction fuel generalizing at_ after proof with
  | zero => simp [Decode.proofStream] at read
  | succ fuel ih =>
      cases command : Decode.command bytes at_ with
      | none => simp [Decode.proofStream, command] at read
      | some value =>
          rcases value with ⟨opcode, data, size⟩
          have within := command_bounded bytes at_ opcode data size command
          by_cases stop : opcode = 0
          · simp [Decode.proofStream, command, stop] at read
            omega
          · cases cmd : Decode.proofCmd opcode data with
            | none => simp [Decode.proofStream, command, stop, cmd] at read
            | some first =>
                cases rest : Decode.proofStream bytes fuel (at_ + size) with
                | none => simp [Decode.proofStream, command, stop, cmd, rest] at read
                | some tail =>
                    rcases tail with ⟨tail, finish⟩
                    have following := ih (at_ + size) finish tail rest
                    simp [Decode.proofStream, command, stop, cmd, rest] at read
                    omega

theorem proofStream_pair_bounded (bytes : ByteArray) (fuel at_ : Nat)
    (value : List ProofCmd × Nat)
    (read : Decode.proofStream bytes fuel at_ = some value) :
    at_ < value.2 ∧ value.2 ≤ bytes.size :=
  proofStream_bounded bytes fuel at_ value.2 value.1 read

theorem proofStatements_length (source : List Decode.DecodedStatement) :
    (Decode.proofStatements source).length = source.length := by
  simp [Decode.proofStatements]

theorem proofStatements_append (first second : List Decode.DecodedStatement) :
    Decode.proofStatements (first ++ second) =
      Decode.proofStatements first ++ Decode.proofStatements second := by
  simp [Decode.proofStatements]

theorem proofStatements_getElem? (source : List Decode.DecodedStatement) (index : Nat) :
    (Decode.proofStatements source)[index]? = source[index]?.map (·.statement) := by
  simp [Decode.proofStatements]

theorem proofStatements_member_iff (source : List Decode.DecodedStatement) (statement : Statement) :
    statement ∈ Decode.proofStatements source ↔
      ∃ entry ∈ source, entry.statement = statement := by
  simp [Decode.proofStatements]

/-- Every source flag is determined by the explicit local declaration opcode. -/
def ExplicitLocality (entry : Decode.DecodedStatement) : Prop :=
  entry.isLocal = (entry.opcode == 0x0D || entry.opcode == 0x0E)

theorem statements_explicit_locality (bytes : ByteArray) (isDef : List Bool)
    (fuel at_ terms : Nat) (source : List Decode.DecodedStatement)
    (decoded : Decode.statements bytes isDef fuel at_ terms = some source) :
    ∀ entry ∈ source, ExplicitLocality entry := by
  induction fuel generalizing at_ terms source with
  | zero => simp [Decode.statements] at decoded
  | succ fuel ih =>
      cases command : Decode.command bytes at_ with
      | none => simp [Decode.statements, command] at decoded
      | some value =>
          rcases value with ⟨opcode, data, size⟩
          have alternatives : opcode = 0 ∨ opcode = 2 ∨ opcode = 4 ∨ opcode = 5 ∨
              opcode = 6 ∨ opcode = 13 ∨ opcode = 14 ∨
              (opcode ≠ 0 ∧ opcode ≠ 2 ∧ opcode ≠ 4 ∧ opcode ≠ 5 ∧
                opcode ≠ 6 ∧ opcode ≠ 13 ∧ opcode ≠ 14) := by omega
          rcases alternatives with op | op | op | op | op | op | op | other
          all_goals
            try subst opcode
            cases proof : Decode.proofStream bytes fuel (at_ + size)
          all_goals
            simp_all [Decode.statements, ExplicitLocality, Option.bind_eq_some_iff]
          all_goals
            repeat' (split at decoded <;>
              simp_all [Option.bind_eq_some_iff])
          all_goals grind

/-- Intervals are nonempty, bounded and adjacent in source order. The empty
suffix still starts at an in-bounds command, the final stream terminator. -/
def SourceIntervals (byteCount : Nat) : Nat → List Decode.DecodedStatement → Prop
  | at_, [] => at_ < byteCount
  | at_, entry :: rest => entry.start = at_ ∧ at_ < entry.after ∧
      entry.after ≤ byteCount ∧ SourceIntervals byteCount entry.after rest

theorem statements_source_intervals (bytes : ByteArray) (isDef : List Bool)
    (fuel at_ terms : Nat) (source : List Decode.DecodedStatement)
    (decoded : Decode.statements bytes isDef fuel at_ terms = some source) :
    SourceIntervals bytes.size at_ source := by
  induction fuel generalizing at_ terms source with
  | zero => simp [Decode.statements] at decoded
  | succ fuel ih =>
      cases command : Decode.command bytes at_ with
      | none => simp [Decode.statements, command] at decoded
      | some value =>
          rcases value with ⟨opcode, data, size⟩
          have within := command_bounded bytes at_ opcode data size command
          have alternatives : opcode = 0 ∨ opcode = 2 ∨ opcode = 4 ∨ opcode = 5 ∨
              opcode = 6 ∨ opcode = 13 ∨ opcode = 14 ∨
              (opcode ≠ 0 ∧ opcode ≠ 2 ∧ opcode ≠ 4 ∧ opcode ≠ 5 ∧
                opcode ≠ 6 ∧ opcode ≠ 13 ∧ opcode ≠ 14) := by omega
          rcases alternatives with op | op | op | op | op | op | op | other
          all_goals
            try subst opcode
            cases proof : Decode.proofStream bytes fuel (at_ + size)
          all_goals
            try have proofWithin := proofStream_pair_bounded bytes fuel (at_ + size) _ proof
          all_goals
            simp_all [Decode.statements, SourceIntervals, Option.bind_eq_some_iff]
          all_goals
            repeat' (split at decoded <;>
              simp_all [Option.bind_eq_some_iff])
          all_goals grind [SourceIntervals]

open Mettapedia.Languages.MM0.Kernel

/-- Extending the allocation store cannot change a previously decoded
expression. Recursion follows the actual strictly earlier child pointers. -/
theorem decode_append_preserves (store suffix : List Alloc) (position : Nat)
    (allocated : position < store.length) :
    Soundness.decode (store ++ suffix) position = Soundness.decode store position := by
  induction position using Nat.strong_induction_on with
  | h position ih =>
      conv_lhs => rw [Soundness.decode]
      conv_rhs => rw [Soundness.decode]
      rw [List.getElem?_append_left allocated]
      cases lookup : store[position]? with
      | none => simp
      | some alloc =>
          cases node : alloc.node with
          | var index => simp [node]
          | app term args =>
              simp only [node]
              split
              · rename_i earlier
                congr 2
                funext arg
                exact ih arg.1 (earlier arg.1 arg.2)
                  (Nat.lt_trans (earlier arg.1 arg.2) allocated)
              · rfl

theorem decode_alloc_preserves (state : Formats.MMB.State) (alloc : Alloc)
    (position : Nat) (allocated : position < state.store.length) :
    Soundness.decode (state.alloc alloc).1.store position =
      Soundness.decode state.store position := by
  exact decode_append_preserves state.store [alloc] position allocated

theorem decode_alloc_variable (state : Formats.MMB.State) (index : Nat) (type : ExprType) :
    Soundness.decode (state.alloc ⟨.var index, type⟩).1.store
      (state.alloc ⟨.var index, type⟩).2 = some (.var index) := by
  change Soundness.decode (state.store ++ [⟨.var index, type⟩]) state.store.length = _
  have lookup : (state.store ++ [⟨.var index, type⟩])[state.store.length]? =
      some (⟨.var index, type⟩ : Alloc) := by
    simp
  rw [Soundness.decode, lookup]

theorem decode_alloc_application (state : Formats.MMB.State) (term : Nat)
    (args : List Nat) (type : ExprType) (earlier : ∀ arg ∈ args, arg < state.store.length) :
    Soundness.decode (state.alloc ⟨.app term args, type⟩).1.store
      (state.alloc ⟨.app term args, type⟩).2 =
      (args.mapM (Soundness.decode state.store)).map (Preterm.applyArgs (.term term)) := by
  change Soundness.decode (state.store ++ [⟨.app term args, type⟩]) state.store.length = _
  have lookup : (state.store ++ [⟨.app term args, type⟩])[state.store.length]? =
      some (⟨.app term args, type⟩ : Alloc) := by
    simp
  rw [Soundness.decode, lookup]
  dsimp only
  rw [dif_pos earlier]
  rw [List.mapM_subtype (g := Soundness.decode state.store)]
  · simp
  · intro arg member
    exact decode_append_preserves state.store [⟨.app term args, type⟩] arg
      (earlier arg member)

private theorem loading_fold_shape
    (advance : Formats.MMB.State → ExprType × Nat → Option Formats.MMB.State)
    (advances : ∀ before row after, advance before row = some after →
      after.store = before.store ++ [⟨.var row.2, row.1⟩] ∧
      after.heap = before.heap ++ [.expr before.store.length] ∧
      after.stack = before.stack ∧ after.hyps = before.hyps ∧
      after.varCount = before.varCount + 1 ∧
      after.nextBound = before.nextBound + (if row.1.bound then 1 else 0))
    (rows : List (ExprType × Nat)) (before after : Formats.MMB.State)
    (loaded : rows.foldlM advance before = some after) :
    after.store = before.store ++ rows.map (fun row => ⟨.var row.2, row.1⟩) ∧
    after.heap = before.heap ++
      (List.range' before.store.length rows.length).map Elem.expr ∧
    after.stack = before.stack ∧ after.hyps = before.hyps ∧
    after.varCount = before.varCount + rows.length ∧
    after.nextBound = before.nextBound + (rows.filter (·.1.bound)).length := by
  induction rows generalizing before with
  | nil =>
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at loaded
      subst after
      simp
  | cons row rows ih =>
      change (advance before row).bind (fun middle => rows.foldlM advance middle) =
        some after at loaded
      obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp loaded
      obtain ⟨store, heap, stack, hyps, count, bound⟩ := advances before row middle first
      obtain ⟨stores, heaps, tailStack, hypotheses, counts, bounds⟩ := ih middle rest
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [stores, store, List.append_assoc]
      · simp [heaps, heap, store, List.range'_succ, List.append_assoc]
      · exact tailStack.trans stack
      · exact hypotheses.trans hyps
      · simp [counts, count, Nat.add_comm, Nat.add_left_comm]
      · cases rowBound : row.1.bound <;>
          simp [bounds, bound, rowBound]
        all_goals omega

/-- Successful descriptor loading allocates exactly the argument variables.
There are no hidden application edges, stack roots, or hypothesis roots. -/
theorem loadArgs_variable_shape (sorts : List SortInfo) (args : List ExprType)
    (state : Formats.MMB.State) (loaded : loadArgs sorts args = some state) :
    state.store = args.zipIdx.map (fun row => ⟨.var row.2, row.1⟩) ∧
    state.heap = (List.range args.length).map Elem.expr ∧
    state.stack = [] ∧ state.hyps = [] ∧ state.varCount = args.length ∧
    state.nextBound = (Statements.boundPositions args).length := by
  unfold loadArgs at loaded
  have shape := loading_fold_shape _ ?_ args.zipIdx ⟨[], [], [], [], 0, 0⟩ state loaded
  · simpa [List.range_eq_range', Statements.boundPositions] using shape
  · intro before row after step
    rcases row with ⟨type, position⟩
    cases sortRead : sorts[type.sort]? with
    | none => simp [sortRead] at step
    | some info =>
        change (sorts[type.sort]?).bind _ = some after at step
        rw [sortRead, Option.bind_some] at step
        split at step
        all_goals split at step
        all_goals simp_all [Formats.MMB.State.alloc]
        all_goals cases step
        all_goals simp_all

/-- The corrected term-proof initializer contains only public arguments.
The temporary return descriptor has no remaining root or allocation. -/
theorem termProof_initial_roots (sorts : List SortInfo) (args : List ExprType)
    (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded) :
    (loaded.forTermProof args.length).store =
      args.zipIdx.map (fun row => ⟨.var row.2, row.1⟩) ∧
    (loaded.forTermProof args.length).heap = (List.range args.length).map Elem.expr ∧
    (loaded.forTermProof args.length).stack = [] ∧
    (loaded.forTermProof args.length).hyps = [] ∧
    (loaded.forTermProof args.length).varCount = args.length := by
  obtain ⟨store, heap, stack, hyps, _⟩ :=
    loadArgs_variable_shape sorts (args ++ [ret]) loaded validated
  simp [Formats.MMB.State.forTermProof, store, heap, stack, hyps,
    List.zipIdx_append, List.range_succ, List.map_append]

/-- No variable node, root, or store lookup in the initial proof state can
reach the discarded return-validation cell. -/
theorem termProof_return_cell_unreachable (sorts : List SortInfo) (args : List ExprType)
    (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded) :
    (loaded.forTermProof args.length).store[args.length]? = none ∧
    (∀ allocation ∈ (loaded.forTermProof args.length).store,
      ∃ position < args.length, allocation.node = .var position) ∧
    (∀ root ∈ (loaded.forTermProof args.length).heap,
      ∃ position < args.length, root = .expr position) ∧
    (loaded.forTermProof args.length).stack = [] ∧
    (loaded.forTermProof args.length).hyps = [] := by
  obtain ⟨store, heap, stack, hyps, _⟩ := termProof_initial_roots sorts args ret loaded validated
  refine ⟨?_, ?_, ?_, stack, hyps⟩
  · simp [store]
  · intro allocation member
    rw [store] at member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact ⟨row.2, by simpa using List.snd_lt_of_mem_zipIdx rowMember, rfl⟩
  · intro root member
    rw [heap] at member
    obtain ⟨position, positionMember, rfl⟩ := List.mem_map.mp member
    exact ⟨position, List.mem_range.mp positionMember, rfl⟩

theorem termProof_argument_decode (sorts : List SortInfo) (args : List ExprType)
    (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded)
    (position : Nat) (inside : position < args.length) :
    Soundness.decode (loaded.forTermProof args.length).store position = some (.var position) := by
  obtain ⟨store, _⟩ := termProof_initial_roots sorts args ret loaded validated
  rw [store, Soundness.decode]
  have found : args[position]? = some (args[position]'inside) := List.getElem?_eq_getElem inside
  rw [List.getElem?_map, List.getElem?_zipIdx, found]
  simp only [Option.map_some, Nat.zero_add]

/-- Initial machine expressions have the declared kernel variable types;
this conclusion uses the existing declaration elaborator and typing rules. -/
theorem termProof_argument_hasType (signature : TermSignature) (sorts : List SortInfo)
    (args : List ExprType) (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded)
    (position : Nat) (inside : position < args.length) :
    ∃ expression, Soundness.decode (loaded.forTermProof args.length).store position =
      some expression ∧
      Preterm.HasType signature (Statements.context args) expression []
        (args[position]'inside).sort := by
  refine ⟨.var position, termProof_argument_decode sorts args ret loaded validated position inside,
    ?_⟩
  have found : args[position]? = some (args[position]'inside) := List.getElem?_eq_getElem inside
  have lookup : (Statements.context args)[position]? =
      some (Statements.binder (Statements.boundPositions args) (args[position]'inside)) := by
    simp only [Statements.context, List.getElem?_map, found, Option.map_some]
  have binderSort : (Statements.binder (Statements.boundPositions args)
      (args[position]'inside)).sort = (args[position]'inside).sort := by
    unfold Statements.binder
    split <;> rfl
  rw [← binderSort]
  exact .var lookup

/-- A regular return descriptor does not consume a bound-variable rank.
The next dummy therefore follows precisely the public bound arguments. -/
theorem termProof_initial_bound_rank (sorts : List SortInfo) (args : List ExprType)
    (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded)
    (regularReturn : ret.bound = false) :
    (loaded.forTermProof args.length).nextBound = (Statements.boundPositions args).length := by
  obtain ⟨_, _, _, _, _, ranks⟩ := loadArgs_variable_shape sorts (args ++ [ret]) loaded validated
  simp [Formats.MMB.State.forTermProof, ranks, Statements.boundPositions,
    List.zipIdx_append, regularReturn]

private theorem state_ext (first second : Formats.MMB.State)
    (store : first.store = second.store) (stack : first.stack = second.stack)
    (heap : first.heap = second.heap) (hyps : first.hyps = second.hyps)
    (ranks : first.nextBound = second.nextBound) (count : first.varCount = second.varCount) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Combined descriptor validation initializes exactly the state obtained by
loading only the public arguments. The return check is retained separately. -/
theorem validated_return_initializes_arguments
    (sorts : List SortInfo) (args : List ExprType) (ret : ExprType) (loaded : Formats.MMB.State)
    (validated : loadArgs sorts (args ++ [ret]) = some loaded)
    (regularReturn : ret.bound = false) :
    loadArgs sorts args = some (loaded.forTermProof args.length) := by
  have totalValidated := validated
  unfold loadArgs at validated
  rw [List.zipIdx_append, List.foldlM_append] at validated
  obtain ⟨argsState, argsRead, _⟩ := Option.bind_eq_some_iff.mp validated
  have argsLoaded : loadArgs sorts args = some argsState := argsRead
  obtain ⟨store, heap, stack, hyps, count, ranks⟩ :=
    loadArgs_variable_shape sorts args argsState argsLoaded
  obtain ⟨newStore, newHeap, newStack, newHyps, newCount⟩ :=
    termProof_initial_roots sorts args ret loaded totalValidated
  have newRanks := termProof_initial_bound_rank sorts args ret loaded totalValidated regularReturn
  have same : argsState = loaded.forTermProof args.length := by
    apply state_ext
    · exact store.trans newStore.symm
    · exact stack.trans newStack.symm
    · exact heap.trans newHeap.symm
    · exact hyps.trans newHyps.symm
    · exact ranks.trans newRanks.symm
    · exact count.trans newCount.symm
  exact argsLoaded.trans (congrArg some same)

private def dummyTables : Tables where
  sorts := [{ provable := true }, {}]
  terms := [
    ⟨0, [⟨1, false, ∅⟩, ⟨1, false, ∅⟩], ⟨0, false, ∅⟩, none⟩,
    ⟨0, [⟨1, true, {0}⟩, ⟨0, false, {0}⟩], ⟨0, false, ∅⟩, none⟩]
  thms := []

private def twoDummyEntry : TermEntry :=
  ⟨0, [], ⟨0, false, ∅⟩,
    some [.term 1, .dummy 1, .term 1, .dummy 1, .term 0, .ref 1, .ref 0]⟩

private def twoDummyProof : List ProofCmd :=
  [.dummy 1, .dummy 1, .ref 1, .ref 0, .term 0, .term 1, .term 1]

private def twoDummyResult : Option Formats.MMB.State := do
  let loaded ← loadArgs dummyTables.sorts (twoDummyEntry.args ++ [twoDummyEntry.ret])
  run dummyTables .definition (loaded.forTermProof twoDummyEntry.args.length) twoDummyProof

theorem definition_two_dummies_checked :
    checkTermDecl dummyTables twoDummyEntry twoDummyProof = true := by decide

/-- This observes the actual corrected initializer and executed allocations,
so an extra return variable would change both observed dummy positions. -/
theorem first_second_dummy_context_positions :
    twoDummyResult.map (fun state =>
      ((state.store[0]?).map (·.node), (state.store[1]?).map (·.node), state.varCount)) =
      some (some (.var 0), some (.var 1), 2) := by decide

theorem dummy_heap_reference_identity :
    twoDummyResult.map (fun state =>
      (state.heap[0]?, state.heap[1]?, (state.store[2]?).map (·.node))) =
      some (some (.expr 0), some (.expr 1), some (.app 0 [1, 0])) := by decide

theorem unresolved_dummy_reference_rejected :
    checkTermDecl dummyTables twoDummyEntry
      [.dummy 1, .dummy 1, .ref 2, .ref 0, .term 0, .term 1, .term 1] = false := by decide

private def localityBytes : ByteArray :=
  ⟨#[0x44, 2, 0x45, 2, 0x4D, 4, 0x10, 0, 0x4E, 5, 0x11, 0x14, 0, 0]⟩

theorem explicit_local_flags_control :
    (Decode.statements localityBytes [false, true] 20 0 0).map
      (fun entries => entries.map (fun entry => (entry.opcode, entry.isLocal))) =
      some [(4, false), (5, false), (13, true), (14, true)] := by decide

theorem adjacent_half_open_intervals_control :
    (Decode.statements localityBytes [false, true] 20 0 0).map
      (fun entries => entries.map (fun entry => (entry.start, entry.after))) =
      some [(0, 2), (2, 4), (4, 8), (8, 13)] := by decide

theorem malformed_statement_length_rejected :
    (Decode.statements ⟨#[0x44, 3, 0]⟩ [] 10 0 0).isSome = false := by decide

theorem sorry_opcode_rejected : Decode.proofCmd 0x20 0 = none := by decide

theorem nonzero_refl_data_rejected : Decode.proofCmd 0x18 1 = none := by decide

private def quotientEquation : SpaceSemantics.Equation :=
  binarySource.program.equations[0]'(by decide)

private def quotientEnvironment (number divisor : Nat) : Subst :=
  [("divisor", natural divisor), ("number", natural number)]

private theorem quotient_unique :
    program.equations.filter (fun row => row.head == "mm0:mmb:byte-quotient") =
      [quotientEquation] := by decide

private theorem quotient_formals : quotientEquation.arguments =
    [.var "number", .var "divisor"] := by decide

private theorem quotient_shape : quotientEquation.body =
    .expression [.symbol "if", .expression [.symbol "<", .var "number", .var "divisor"],
      natural 0, .expression [.symbol "+", natural 1,
        .expression [.symbol "mm0:mmb:byte-quotient",
          .expression [.symbol "-", .var "number", .var "divisor"], .var "divisor"]]] := by decide

private theorem quotient_clause (number divisor : Nat) :
    clauses program "mm0:mmb:byte-quotient" [natural number, natural divisor] =
      [.evaluate (quotientEnvironment number divisor) quotientEquation.body] := by
  rw [clauses_use_only_the_named_equations, quotient_unique]
  simp [quotient_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, quotientEnvironment]

private theorem quotient_body_returns (state : Effects.State) (number divisor : Nat)
    (positive : 0 < divisor) :
    PureReturns program (quotientEnvironment number divisor) state quotientEquation.body state
      (natural (number / divisor)) := by
  induction number using Nat.strong_induction_on with
  | h number ih =>
      rw [quotient_shape]
      apply if_returns program (quotientEnvironment number divisor) state state state _
        (boolean (decide (number < divisor))) _ _ _
      · apply native_variable_call_returns program _ state state "<" ["number", "divisor"] _
          (by decide) (by decide) _ (by decide)
        simp [quotientEnvironment, natural, applySubst, Subst.lookup, StdLib.apply]
      · by_cases small : number < divisor
        · simp only [small, decide_true, boolean, Nat.div_eq_of_lt small]
          exact grounded_returns program _ state (.int 0)
        · simp only [small, decide_false, boolean]
          rw [Nat.div_eq_sub_div positive (by omega), Nat.add_comm]
          apply native_binary_call_returns program _ state state state state "+"
            _ _ (natural 1) (natural ((number - divisor) / divisor)) _
            (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
          · exact grounded_returns program _ state (.int 1)
          · apply authored_binary_call_returns program _ (quotientEnvironment (number - divisor) divisor)
              state state state state "mm0:mmb:byte-quotient" _ _
              (natural (number - divisor)) (natural divisor) quotientEquation.body _
              (by decide) (by decide) (by decide) (by decide) (by decide) _ _
              (quotient_clause _ _) (ih (number - divisor) (by omega)) (by decide)
            · apply native_variable_call_returns program _ state state "-" ["number", "divisor"] _
                (by decide) (by decide) _ (by decide)
              simp [quotientEnvironment, natural, applySubst, Subst.lookup, StdLib.apply,
                Int.ofNat_sub (by omega : divisor ≤ number)]
            · simpa [quotientEnvironment, natural, applySubst, Subst.lookup] using
                variable_returns program (quotientEnvironment number divisor) state "divisor"
          · simp [StdLib.apply, natural]

/-- The retained arithmetic helper executes to mathematical quotient on
captured nonnegative integers and a positive divisor, without changing state. -/
theorem byte_quotient_captured_returns (bindings : Subst) (state : Effects.State)
    (number divisor : Nat) (positive : 0 < divisor) (numberName divisorName : String)
    (capturedNumber : applySubst bindings (.var numberName) = natural number)
    (capturedDivisor : applySubst bindings (.var divisorName) = natural divisor) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmb:byte-quotient", .var numberName, .var divisorName]) state
      (natural (number / divisor)) := by
  apply authored_variable_call_returns program bindings (quotientEnvironment number divisor)
    state state "mm0:mmb:byte-quotient" [numberName, divisorName] quotientEquation.body _
    (by decide) (by decide) (by decide) _ (quotient_body_returns state number divisor positive) (by decide)
  simpa only [List.map_cons, List.map_nil, capturedNumber, capturedDivisor] using
    quotient_clause number divisor

theorem byte_quotient_sufficient_fuel (bindings : Subst) (state : Effects.State)
    (number divisor : Nat) (positive : 0 < divisor) (numberName divisorName : String)
    (capturedNumber : applySubst bindings (.var numberName) = natural number)
    (capturedDivisor : applySubst bindings (.var divisorName) = natural divisor) :
    ∃ fuel, ∀ extra, Eval.run program (fuel + extra)
      { state
        control := .evaluate bindings
          (.expression [.symbol "mm0:mmb:byte-quotient", .var numberName, .var divisorName]) } =
      .complete state [natural (number / divisor)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _
    (byte_quotient_captured_returns bindings state number divisor positive numberName divisorName
      capturedNumber capturedDivisor)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state
    [natural (number / divisor)] [] [] completed⟩

end Mettapedia.Languages.MM0.MeTTa.MMBExecution
