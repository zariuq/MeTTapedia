import Mettapedia.Machines.TIsa.ImportedP1
import Mettapedia.Machines.TIsa.P1WordExecution
import Mettapedia.Machines.TIsa.RuleCompiler
import Mettapedia.Languages.Micromath.Kernel

/-!
# Micromath substitution in the exported p1 source

The seven comparisons use the borrowed premise rows. The terminal branch checks
the two capacity words, then writes the conclusion to the output capability.
The source term is taken from the checked export.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.P1Sub1Source

open P1Source P1WordExecution

abbrev Premises := Fin 4 → Fin 4 → Word

def region (row : Fin 4) : Region := ⟨row.val, by have := row.isLt; omega⟩
def pointer (row : Fin 4) : Reg := ⟨row.val + 1, by have := row.isLt; omega⟩
private def byteOffset (field : Fin 4) : BitVec 32 := BitVec.ofNat 32 (8 * field.val)

structure ReadRows (state : State) (words : Premises) : Prop where
  readable : ∀ row, (state.regions (region row)).mode ≠ .absent
  pointerAtBase : ∀ row, state.registers (pointer row) = (state.regions (region row)).base
  aligned : ∀ row, (state.regions (region row)).base.toNat % 8 = 0
  extent : ∀ row, 32 ≤ (state.regions (region row)).length.toNat
  fits : ∀ row, (state.regions (region row)).base.toNat + (state.regions (region row)).length.toNat < 2 ^ 64
  read : ∀ row field, state.memory ((state.regions (region row)).base.toNat + 8 * field.val) =
    some (words row field)

structure Held (before after : State) : Prop where
  registers : ∀ r : Reg, r.val < 6 → after.registers r = before.registers r
  regions : after.regions = before.regions
  memory : after.memory = before.memory
  frame : after.frame = before.frame
  charges : after.budget = before.budget ∧ after.spent = before.spent

private theorem Held.refl (state : State) : Held state state := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem Held.trans {s t u : State} (first : Held s t) (later : Held t u) : Held s u :=
  ⟨fun r bound => (later.registers r bound).trans (first.registers r bound),
    later.regions.trans first.regions, later.memory.trans first.memory, later.frame.trans first.frame,
    later.charges.1.trans first.charges.1, later.charges.2.trans first.charges.2⟩

private theorem Held.write (s : State) (r : Reg) (v : Word) (scratch : 6 ≤ r.val) : Held s (s.write r v) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  intro a before
  have different : a ≠ r := fun same => by subst a; omega
  exact Function.update_of_ne different ..

private theorem ReadRows.held {s t : State} {words : Premises} (inputs : ReadRows s words)
    (invariant : Held s t) : ReadRows t words := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [invariant.regions]
    exact inputs.readable
  · intro row
    rw [invariant.regions, invariant.registers _ (by change row.val + 1 < 6; have := row.isLt; omega)]
    exact inputs.pointerAtBase row
  · rw [invariant.regions]
    exact inputs.aligned
  · rw [invariant.regions]
    exact inputs.extent
  · rw [invariant.regions]
    exact inputs.fits
  · rw [invariant.regions, invariant.memory]
    exact inputs.read

private def load (row field : Fin 4) (destination : Reg) : Instr :=
  .load .u64 .word64 (region row) destination (pointer row) (byteOffset field)

private theorem read_word {s : State} {words : Premises} (inputs : ReadRows s words)
    (row field : Fin 4) (destination : Reg) :
    instruction s (load row field destination) = .ok (s.write destination (words row field)) := by
  let cap := s.regions (region row)
  have offset : (byteOffset field).toInt = (8 * field.val : Nat) := by
    fin_cases field <;> decide
  have enough : 8 * field.val + 8 ≤ cap.length.toNat := by
    have := inputs.extent row
    have := field.isLt
    change 8 * field.val + 8 ≤ (s.regions (region row)).length.toNat
    omega
  have pointerKnown := inputs.pointerAtBase row
  have within : Memory.access? cap.base cap.length (s.registers (pointer row))
      (byteOffset field).toInt 8 = some (cap.base.toNat + 8 * field.val) := by
    rw [pointerKnown]
    apply (P1Memory.access?_iff_inside cap.base cap.length cap.base _ 8 _
      (inputs.fits row) (Nat.le_refl _) (by omega)).mpr
    rw [offset]
    exact ⟨by omega, by omega, by omega⟩
  have aligned : (cap.base.toNat + 8 * field.val) % 8 = 0 := by
    have base : cap.base.toNat % 8 = 0 := inputs.aligned row
    omega
  simp only [load, instruction, inputs.readable row, if_false]
  change (match ((Memory.access? cap.base cap.length (s.registers (pointer row))
      (byteOffset field).toInt 8).bind (fun a => if a % 8 = 0 then some a else none)).bind s.memory with
    | some word => match P1Memory.checkedWord .u64 word with
      | some value => Except.ok (s.write destination value)
      | none => Except.error ExitStatus.invalidInput
    | none => Except.error ExitStatus.invalidInput) = .ok (s.write destination (words row field))
  simp [within, aligned, inputs.read, cap, P1Memory.checkedWord, P1Scalar.boolInputs, P1Scalar.normalize]

private structure Guard where
  leftRow : Fin 4
  leftField : Fin 4
  rightRow : Fin 4
  rightField : Fin 4

private def Guards : List Guard :=
  [⟨1,1,0,2⟩, ⟨2,1,0,3⟩, ⟨2,2,1,2⟩, ⟨2,3,1,3⟩, ⟨3,1,0,0⟩, ⟨3,2,1,2⟩, ⟨3,3,1,3⟩]

private def finish (code : ExitStatus) (word : Word) : Stmt :=
  .seq (.instruction (.immediate .u64 8 word)) (.ret code 8)

private def guarded (g : Guard) (rest : Stmt) : Stmt :=
  .seq (.seq (.seq (.instruction (load g.leftRow g.leftField 6))
    (.instruction (load g.rightRow g.rightField 8)))
    (.instruction (.compare .equal .u64 7 6 (.register 8))))
    (.branch 7 rest (finish .refused 0))

private def guardCode (guards : List Guard) (rest : Stmt) : Stmt :=
  guards.foldr guarded rest

private def agrees (words : Premises) (g : Guard) : Bool :=
  words g.leftRow g.leftField == words g.rightRow g.rightField

private def guardState (s : State) (words : Premises) (g : Guard) : State :=
  ((s.write 6 (words g.leftRow g.leftField)).write 8 (words g.rightRow g.rightField)).write 7
    (booleanWord (agrees words g))

private theorem guard_keeps (s : State) (words : Premises) (g : Guard) :
    Held s (guardState s words g) :=
  (Held.write s 6 _ (by decide)).trans
    ((Held.write _ 8 _ (by decide)).trans (Held.write _ 7 _ (by decide)))

private theorem guard_step {s : State} {words : Premises} (inputs : ReadRows s words)
    (g : Guard) (rest : Stmt) :
    execute s (guarded g rest) =
      if agrees words g then execute (guardState s words g) rest
      else .returned .refused 0 ((guardState s words g).write 8 0) := by
  let first := s.write 6 (words g.leftRow g.leftField)
  let both := first.write 8 (words g.rightRow g.rightField)
  have next : ReadRows first words := inputs.held (Held.write s 6 _ (by decide))
  have cmp : instruction both (.compare .equal .u64 7 6 (.register 8)) =
      .ok (guardState s words g) := by
    simp [instruction, scalarInstruction, Instr.destination?, Instr.reads, P1Scalar.evaluate, P1Scalar.compareWords,
      P1Scalar.narrow, Comparison.evaluate, guardState, agrees, State.write, first, both,
      Function.update]
  have left : instruction s (load g.leftRow g.leftField 6) = .ok first := read_word inputs g.leftRow g.leftField 6
  have right : instruction first (load g.rightRow g.rightField 8) = .ok both := read_word next g.rightRow g.rightField 8
  simp only [guarded, execute, Flow.thenContinue, left, right, cmp]
  cases accepted : agrees words g <;>
    simp [accepted, guardState, State.write, Function.update, booleanWord, finish,
      execute, instruction, scalarInstruction, Instr.destination?, Instr.reads, P1Scalar.evaluate, P1Scalar.normalize,
      Flow.thenContinue]

private theorem guards_run (guards : List Guard) (rest : Stmt) {s : State} {words : Premises}
    (inputs : ReadRows s words) :
    if guards.all (agrees words) then
      ∃ reached, Held s reached ∧ execute s (guardCode guards rest) = execute reached rest
    else
      ∃ stopped, Held s stopped ∧ execute s (guardCode guards rest) = .returned .refused 0 stopped := by
  induction guards generalizing s with
  | nil => exact ⟨s, Held.refl s, rfl⟩
  | cons g restGuards ih =>
    rw [List.all_cons]
    by_cases test : agrees words g = true
    · simp only [test, Bool.true_and, guardCode, List.foldr_cons, guard_step inputs]
      have kept := guard_keeps s words g
      have further := ih (inputs.held kept)
      by_cases following : restGuards.all (agrees words) = true <;> simp only [following, if_true] at *
      all_goals
        obtain ⟨after, agrees, ran⟩ := further
        exact ⟨after, kept.trans agrees, ran⟩
    · have falseTest : agrees words g = false := Bool.eq_false_iff.mpr test
      simp only [falseTest, Bool.false_and, guardCode, List.foldr_cons, guard_step inputs]
      exact ⟨_, (guard_keeps s words g).trans (Held.write _ 8 _ (by decide)), rfl⟩

structure Output (state : State) : Prop where
  usable : Usable (state.regions 4) 32
  pointerAtBase : state.registers 5 = (state.regions 4).base

private theorem Output.held {s t : State} (output : Output s) (invariant : Held s t) : Output t := by
  refine ⟨?_, ?_⟩
  · rw [invariant.regions]
    exact output.usable
  · rw [invariant.registers 5 (by decide), invariant.regions]
    exact output.pointerAtBase

private def store (field : Fin 4) (source : Reg) : Instr :=
  .store .word64 4 5 (byteOffset field) source

private theorem store_word {s : State} (output : Output s) (field : Fin 4) (source : Reg) :
    instruction s (store field source) =
      .ok (s.store ((s.regions 4).base.toNat + 8 * field.val) (s.registers source)) := by
  apply P1WordExecution.store_base s 4 32 (8 * field.val) output.usable
  · have := field.isLt
    omega
  · omega
  · fin_cases field <;> decide
  · exact output.pointerAtBase

private abbrev RowField := Fin 4 × Fin 4

private def publishFrom (first second third fourth : RowField) : Stmt :=
  [ .instruction (load second.1 second.2 7), .instruction (load third.1 third.2 8),
    .instruction (load fourth.1 fourth.2 9),
    .instruction (store 0 6), .instruction (store 1 7),
    .instruction (store 2 8), .instruction (store 3 9),
    .instruction (.immediate .u64 8 1), .ret .completed 8 ].foldl Stmt.seq
      (.instruction (load first.1 first.2 6))

private def publish : Stmt := publishFrom (3, 0) (0, 1) (1, 0) (2, 0)

private def gatherWords (words : Premises) (first second third fourth : RowField) : Fin 4 → Word :=
  ![words first.1 first.2, words second.1 second.2, words third.1 third.2, words fourth.1 fourth.2]

def conclusionWords (words : Premises) : Fin 4 → Word :=
  gatherWords words (3, 0) (0, 1) (1, 0) (2, 0)

private def writeRow (s : State) (words : Fin 4 → Word) : Nat → Option Word :=
  (List.finRange 4).foldl (fun m field => Function.update m
    ((s.regions 4).base.toNat + 8 * field.val) (some (words field))) s.memory

private theorem writeRow_at (s : State) (words : Fin 4 → Word) (field : Fin 4) :
    writeRow s words ((s.regions 4).base.toNat + 8 * field.val) = some (words field) := by
  have fields : List.finRange 4 = [0, 1, 2, 3] := by decide
  rw [writeRow, fields]
  fin_cases field <;> simp [Function.update]

private theorem writeRow_away (s : State) (words : Fin 4 → Word) (address : Nat)
    (outside : ∀ field : Fin 4, address ≠ (s.regions 4).base.toNat + 8 * field.val) :
    writeRow s words address = s.memory address := by
  unfold writeRow
  induction List.finRange 4 using List.reverseRecOn with
  | nil => rfl
  | append_singleton prior field ih =>
    rw [List.foldl_append]
    simpa only [List.foldl_cons, List.foldl_nil, Function.update_of_ne (outside field)] using ih

def outputMemory (s : State) (words : Premises) : Nat → Option Word :=
  writeRow s (conclusionWords words)

theorem outputMemory_at (s : State) (words : Premises) (field : Fin 4) :
    outputMemory s words ((s.regions 4).base.toNat + 8 * field.val) = some (conclusionWords words field) :=
  writeRow_at s (conclusionWords words) field

theorem outputMemory_away (s : State) (words : Premises) (address : Nat)
    (outside : ∀ field : Fin 4, address ≠ (s.regions 4).base.toNat + 8 * field.val) :
    outputMemory s words address = s.memory address :=
  writeRow_away s (conclusionWords words) address outside

private theorem publish_run {s : State} {words : Premises} (inputs : ReadRows s words) (output : Output s)
    (first second third fourth : RowField) :
    ∃ after, execute s (publishFrom first second third fourth) = .returned .completed 1 after ∧
      after.memory = writeRow s (gatherWords words first second third fourth) ∧ after.regions = s.regions ∧
      after.frame = s.frame ∧ after.budget = s.budget ∧ after.spent = s.spent := by
  let a := s.write 6 (words first.1 first.2)
  let b := a.write 7 (words second.1 second.2)
  let c := b.write 8 (words third.1 third.2)
  let d := c.write 9 (words fourth.1 fourth.2)
  have ha : Held s a := Held.write _ _ _ (by decide)
  have hb : Held s b := ha.trans (Held.write _ _ _ (by decide))
  have hc : Held s c := hb.trans (Held.write _ _ _ (by decide))
  have hd : Held s d := hc.trans (Held.write _ _ _ (by decide))
  have read0 : instruction s (load first.1 first.2 6) = .ok a := read_word inputs first.1 first.2 6
  have read1 : instruction a (load second.1 second.2 7) = .ok b := read_word (inputs.held ha) second.1 second.2 7
  have read2 : instruction b (load third.1 third.2 8) = .ok c := read_word (inputs.held hb) third.1 third.2 8
  have read3 : instruction c (load fourth.1 fourth.2 9) = .ok d := read_word (inputs.held hc) fourth.1 fourth.2 9
  let base := (s.regions 4).base.toNat
  let x := d.store (base + 8 * (0 : Fin 4).val) (words first.1 first.2)
  let y := x.store (base + 8 * (1 : Fin 4).val) (words second.1 second.2)
  let z := y.store (base + 8 * (2 : Fin 4).val) (words third.1 third.2)
  let w := z.store (base + 8 * (3 : Fin 4).val) (words fourth.1 fourth.2)
  have out : Output d := output.held hd
  have put0 : instruction d (store 0 6) = .ok x := by
    have step := store_word out 0 6
    have value : d.registers 6 = words first.1 first.2 := by simp [d, c, b, a, State.write, Function.update]
    simpa only [x, base, hd.regions, value] using step
  have put1 : instruction x (store 1 7) = .ok y := by
    have step := store_word (s := x) ⟨out.usable, out.pointerAtBase⟩ 1 7
    have value : x.registers 7 = words second.1 second.2 := by simp [x, d, c, b, State.store, State.write, Function.update]
    simpa only [y, base, show x.regions = s.regions from hd.regions, value] using step
  have put2 : instruction y (store 2 8) = .ok z := by
    have step := store_word (s := y) ⟨out.usable, out.pointerAtBase⟩ 2 8
    have value : y.registers 8 = words third.1 third.2 := by simp [y, x, d, c, State.store, State.write, Function.update]
    simpa only [z, base, show y.regions = s.regions from hd.regions, value] using step
  have put3 : instruction z (store 3 9) = .ok w := by
    have step := store_word (s := z) ⟨out.usable, out.pointerAtBase⟩ 3 9
    have value : z.registers 9 = words fourth.1 fourth.2 := by simp [z, y, x, d, State.store, State.write, Function.update]
    simpa only [w, base, show z.regions = s.regions from hd.regions, value] using step
  refine ⟨w.write 8 1, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [publishFrom, List.foldl_cons, List.foldl_nil, execute, Flow.thenContinue,
    read0, read1, read2, read3, put0, put1, put2, put3]
  simp [instruction, scalarInstruction, Instr.destination?, Instr.reads, P1Scalar.evaluate,
    P1Scalar.normalize, State.write, Function.update]

private def capacityFor (publication : Stmt) : Stmt :=
  .seq (.seq (.seq (.instruction (.loadFrame .u64 6 22)) (.instruction (.loadFrame .u64 8 23)))
    (.instruction (.compare .lessUnsigned .u64 7 6 (.register 8))))
    (.branch 7 publication (finish .unsupported 2))

private def capacity : Stmt := capacityFor publish

private theorem capacity_guard (s : State) (publication : Stmt) :
    if s.frame 22 < s.frame 23 then
      ∃ reached, Held s reached ∧ execute s (capacityFor publication) = execute reached publication
    else
      ∃ stopped, Held s stopped ∧ execute s (capacityFor publication) = .returned .unsupported 2 stopped := by
  let a := s.write 6 (s.frame 22)
  let b := a.write 8 (s.frame 23)
  let test := booleanWord (decide (s.frame 22 < s.frame 23))
  let entered := b.write 7 test
  have ha : instruction s (.loadFrame .u64 6 22) = .ok a := by
    simp [a, instruction, P1Memory.checkedWord, P1Scalar.boolInputs, P1Scalar.normalize]
  have hb : instruction a (.loadFrame .u64 8 23) = .ok b := by
    simp [b, a, instruction, State.write, P1Memory.checkedWord, P1Scalar.boolInputs, P1Scalar.normalize]
  have cmp : instruction b (.compare .lessUnsigned .u64 7 6 (.register 8)) = .ok entered := by
    simp [entered, test, a, b, instruction, scalarInstruction, Instr.destination?, Instr.reads,
      P1Scalar.evaluate, P1Scalar.compareWords, P1Scalar.narrow, Comparison.evaluate, State.write, Function.update]
  have kept : Held s entered :=
    (Held.write s 6 _ (by decide)).trans
      ((Held.write a 8 _ (by decide)).trans (Held.write b 7 _ (by decide)))
  by_cases room : s.frame 22 < s.frame 23
  · rw [if_pos room]
    refine ⟨entered, kept, ?_⟩
    have ready : entered.registers 7 = 1 := by simp [entered, test, room, booleanWord, State.write]
    simp [capacityFor, execute, ha, hb, cmp, ready, Flow.thenContinue]
  · rw [if_neg room]
    refine ⟨entered.write 8 2, kept.trans (Held.write _ 8 _ (by decide)), ?_⟩
    have full : entered.registers 7 = 0 := by simp [entered, test, room, booleanWord, State.write]
    simp only [capacityFor, execute, ha, hb, cmp, full, Flow.thenContinue]
    simp [finish, execute, Flow.thenContinue, instruction, scalarInstruction,
      Instr.destination?, Instr.reads, P1Scalar.evaluate, P1Scalar.normalize, State.write, Function.update]

private def guardStatus (s : State) (accepted : Bool) : ExitStatus :=
  if accepted then
    if s.frame 22 < s.frame 23 then .completed else .unsupported
  else .refused

private theorem guarded_publication (s : State) (words : Premises)
    (inputs : ReadRows s words) (output : Output s) (guards : List Guard) (a b c d : RowField) :
    let expected := guardStatus s (guards.all (agrees words))
    ∃ after, execute s (guardCode guards (capacityFor (publishFrom a b c d))) =
        .returned expected expected.word after ∧
      after.memory = (if expected = .completed then writeRow s (gatherWords words a b c d) else s.memory) ∧
      after.regions = s.regions ∧ after.frame = s.frame ∧ after.budget = s.budget ∧ after.spent = s.spent := by
  dsimp only
  have head := guards_run guards (capacityFor (publishFrom a b c d)) inputs
  by_cases accepted : guards.all (agrees words) = true
  · rw [if_pos accepted] at head
    obtain ⟨checked, kept, invoked⟩ := head
    have guarded := capacity_guard checked (publishFrom a b c d)
    rw [kept.frame] at guarded
    rw [invoked]
    by_cases room : s.frame 22 < s.frame 23
    · rw [if_pos room] at guarded
      obtain ⟨entered, ready, publishes⟩ := guarded
      have unchanged := kept.trans ready
      obtain ⟨after, runs, memory, regions, frame, budget, spent⟩ :=
        publish_run (inputs.held unchanged) (output.held unchanged) a b c d
      have memorySame : writeRow entered (gatherWords words a b c d) =
          writeRow s (gatherWords words a b c d) := by
        rw [writeRow, writeRow, unchanged.memory, unchanged.regions]
      refine ⟨after, ?_, ?_, regions.trans unchanged.regions, frame.trans unchanged.frame,
        budget.trans unchanged.charges.1, spent.trans unchanged.charges.2⟩
      · simpa [guardStatus, accepted, room, ExitStatus.word, publishes] using runs
      · simpa [guardStatus, accepted, room, memorySame] using memory
    · rw [if_neg room] at guarded
      obtain ⟨stopped, ready, runs⟩ := guarded
      have unchanged := kept.trans ready
      refine ⟨stopped, ?_, ?_, unchanged.regions, unchanged.frame, unchanged.charges.1, unchanged.charges.2⟩
      · simpa [guardStatus, accepted, room, ExitStatus.word] using runs
      · simpa [guardStatus, accepted, room] using unchanged.memory
  · rw [if_neg accepted] at head
    obtain ⟨after, kept, runs⟩ := head
    refine ⟨after, ?_, ?_, kept.regions, kept.frame, kept.charges.1, kept.charges.2⟩
    · simpa [guardStatus, accepted, ExitStatus.word] using runs
    · simpa [guardStatus, accepted] using kept.memory

private noncomputable def sub1 : P1Capture.Program := ImportedP1.programs[11]'(by rw [ImportedP1.exact_count.2]; decide)

theorem exported_body : sub1.source.body = guardCode Guards capacity := by kernel_reflexivity

open Algorithms.MeTTa.Simple.Parser (SExpr)

private def unique? {α : Type} : List α → Option α
  | [value] => some value
  | _ => none

private def declaration? (forms : List SExpr) (name : String) : Option SExpr :=
  unique? (forms.filterMap fun form => match form with
    | .list [.atom "=", .list [.atom key], value] => if key = name then some value else none
    | _ => none)

private def symbol? : SExpr → Option String
  | .atom symbol => some symbol
  | _ => none

private def boardPattern? (board : String) (fixed : List String) : SExpr → Option (List String)
  | .list (.atom head :: fields) => do
    if head != board || fields.length != 4 then none else
    let names ← fields.mapM symbol?
    if names.any fixed.contains then none else some names
  | _ => none

/-- Import the four-premise, four-word, all-variable fragment of the board
theory. Each occurrence of a symbol denotes the same source variable. -/
def theoryRule? (forms : List SExpr) (entry : String) : Option RuleTable.Rule := do
  let .atom board ← declaration? forms "theory-board" | none
  let .list names ← declaration? forms "theory-names" | none
  let fixed ← names.mapM symbol?
  let .list entries ← declaration? forms "theory-entries" | none
  let name ← unique? (entries.filterMap fun form => match form with
    | .list [.atom "entry", .atom key, .list [.atom "keeps", .atom name]] =>
      if key = entry then some name else none
    | _ => none)
  let .list rules ← declaration? forms "theory-rules" | none
  let (premises, conclusion) ← unique? (rules.filterMap fun form => match form with
    | .list [.atom "rule", .atom key, .list premises, conclusion] =>
      if key = name then some (premises, conclusion) else none
    | _ => none)
  if premises.length != 4 then none else
  let left ← premises.mapM (boardPattern? board fixed)
  let right ← boardPattern? board fixed conclusion
  let symbols := (left.flatten ++ right).eraseDups
  let pattern : List String → RuleTable.Pattern :=
    fun fields => ⟨0, fields.map fun symbol => .variable (symbols.idxOf symbol)⟩
  pure ⟨left.map pattern, pattern right⟩

private def rowField? : RuleTable.Source → Option RowField
  | .field source =>
    if row : source.premise < 4 then
      if field : source.field < 4 then some (⟨source.premise, row⟩, ⟨source.field, field⟩) else none
    else none
  | .literal _ => none

private def lowerGuard? (guard : RuleTable.Guard) : Option Guard := do
  let (leftRow, leftField) ← rowField? guard.left
  let (rightRow, rightField) ← rowField? guard.right
  pure ⟨leftRow, leftField, rightRow, rightField⟩

private def boardInputs : List RuleTable.Shape := List.replicate 4 ⟨0, 4⟩

def lowerPlan? (plan : RuleTable.Plan) : Option Stmt := do
  if plan.inputs = boardInputs ∧ plan.outputTag = 0 then
    let guards ← plan.guards.mapM lowerGuard?
    let [a, b, c, d] ← plan.outputFields.mapM rowField? | none
    pure (guardCode guards (capacityFor (publishFrom a b c d)))
  else none

def micromathTheory : List SExpr :=
  tisa_source_forms% "../../../tcalc/compiled/micromath.theory.metta"

def theoryBody? (forms : List SExpr) (entry : String) : Option Stmt := do
  let rule ← theoryRule? forms entry
  let plan := (rule.compile rule.discoverOrigins).pruneSelfGuards
  if rule.checkPlan plan then lowerPlan? plan else none

theorem theory_compiles_to_export : theoryBody? micromathTheory "mm_sub1" = some sub1.source.body := by
  kernel_reflexivity

private noncomputable def sub2 : P1Capture.Program := ImportedP1.programs[12]'(by rw [ImportedP1.exact_count.2]; decide)

theorem theory_sub2_compiles_to_export : theoryBody? micromathTheory "mm_sub2" = some sub2.source.body := by
  kernel_reflexivity

def theorySub1Rule : RuleTable.Rule :=
  (theoryRule? micromathTheory "mm_sub1").get (by kernel_reflexivity)

def theorySub2Rule : RuleTable.Rule :=
  (theoryRule? micromathTheory "mm_sub2").get (by kernel_reflexivity)

private def theorySub1Plan : RuleTable.Plan :=
  (theorySub1Rule.compile theorySub1Rule.discoverOrigins).pruneSelfGuards

def boardTuple (fields : Fin 4 → Word) : RuleTable.Tuple := ⟨0, [fields 0, fields 1, fields 2, fields 3]⟩

def premiseTuples (words : Premises) : List RuleTable.Tuple :=
  [boardTuple (words 0), boardTuple (words 1), boardTuple (words 2), boardTuple (words 3)]

private def planGuard (guard : Guard) : RuleTable.Guard :=
  ⟨.field ⟨guard.leftRow.val, guard.leftField.val⟩, .field ⟨guard.rightRow.val, guard.rightField.val⟩⟩

private def planField (field : RowField) : RuleTable.Source := .field ⟨field.1.val, field.2.val⟩

private theorem rowField_at (source : RuleTable.Source) (field : RowField)
    (lowered : rowField? source = some field) : planField field = source := by
  cases source with
  | literal => simp [rowField?] at lowered
  | field location =>
    rcases location with ⟨row, column⟩
    by_cases validRow : row < 4
    · by_cases validColumn : column < 4
      · simp only [rowField?, dif_pos validRow, dif_pos validColumn] at lowered
        cases lowered
        rfl
      · simp [rowField?, validRow, validColumn] at lowered
    · simp [rowField?, validRow] at lowered

private theorem guard_at (source : RuleTable.Guard) (guard : Guard)
    (lowered : lowerGuard? source = some guard) : planGuard guard = source := by
  simp only [lowerGuard?, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
  obtain ⟨⟨leftRow, leftField⟩, left, ⟨rightRow, rightField⟩, right, equal⟩ := lowered
  have shape : Guard.mk leftRow leftField rightRow rightField = guard := Option.some.inj equal
  subst guard
  cases source with
  | mk leftSource rightSource =>
    change RuleTable.Guard.mk (planField (leftRow, leftField)) (planField (rightRow, rightField)) =
      RuleTable.Guard.mk leftSource rightSource
    rw [rowField_at _ _ left, rowField_at _ _ right]

private theorem mapM_back {α β : Type} (lower : α → Option β) (raise : β → α)
    (back : ∀ source target, lower source = some target → raise target = source)
    {inputs : List α} {outputs : List β} (lowered : inputs.mapM lower = some outputs) :
    outputs.map raise = inputs := by
  induction inputs generalizing outputs with
  | nil =>
    have same : outputs = [] := (Option.some.inj lowered).symm
    simp [same]
  | cons source later ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
    obtain ⟨target, first, rest, following, equal⟩ := lowered
    have same : target :: rest = outputs := Option.some.inj equal
    rw [← same, List.map_cons, back source target first, ih following]

private theorem lowerPlan_view {plan : RuleTable.Plan} {body : Stmt}
    (lowered : lowerPlan? plan = some body) :
    ∃ guards a b c d,
      plan = ⟨boardInputs, guards.map planGuard, 0, [a, b, c, d].map planField⟩ ∧
      body = guardCode guards (capacityFor (publishFrom a b c d)) := by
  unfold lowerPlan? at lowered
  split at lowered
  next shape =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
    obtain ⟨guards, guardRows, output, outputRows, lowered⟩ := lowered
    rcases output with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩
    all_goals cases lowered
    refine ⟨guards, a, b, c, d, ?_, rfl⟩
    cases plan
    simp only [RuleTable.Plan.mk.injEq]
    exact ⟨shape.1, (mapM_back _ _ guard_at guardRows).symm, shape.2,
      (mapM_back _ _ rowField_at outputRows).symm⟩
  next => simp at lowered

private theorem planField_reads (words : Premises) (field : RowField) :
    (planField field).read (premiseTuples words) = some (words field.1 field.2) := by
  rcases field with ⟨row, field⟩
  fin_cases row <;> fin_cases field <;> rfl

private theorem planGuard_reads (words : Premises) (guard : Guard) :
    (planGuard guard).accepts (premiseTuples words) = agrees words guard := by
  change (match (planField (guard.leftRow, guard.leftField)).read (premiseTuples words),
      (planField (guard.rightRow, guard.rightField)).read (premiseTuples words) with
    | some left, some right => left == right
    | _, _ => false) = agrees words guard
  simp [planField_reads, agrees]

private theorem plan_run (words : Premises) (guards : List Guard) (a b c d : RowField) :
    (RuleTable.Plan.mk boardInputs (guards.map planGuard) 0 ([a,b,c,d].map planField)).run
      (premiseTuples words) =
      if guards.all (agrees words) then some (boardTuple (gatherWords words a b c d)) else none := by
  have shape : (premiseTuples words).map RuleTable.Tuple.shape = boardInputs := rfl
  simp [RuleTable.Plan.run, shape, RuleTable.gather, List.all_map, Function.comp_def,
    planGuard_reads, planField_reads, boardTuple, gatherWords]

/-- Accepted coordinate plans preserve the guards, the four gathered words,
the capacity stop, and the memory and allowance observed by their caller. -/
theorem lowerPlan_refines (s : State) (words : Premises) (inputs : ReadRows s words) (output : Output s)
    (plan : RuleTable.Plan) (body : Stmt) (lowered : lowerPlan? plan = some body) :
    let proposed := plan.run (premiseTuples words)
    let expected := if proposed.isNone then ExitStatus.refused
      else if s.frame 22 < s.frame 23 then .completed else .unsupported
    ∃ after, execute s body = .returned expected expected.word after ∧
      after.regions = s.regions ∧ after.frame = s.frame ∧ after.budget = s.budget ∧ after.spent = s.spent ∧
      (expected ≠ .completed → after.memory = s.memory) ∧
      ∀ candidate, proposed = some candidate → s.frame 22 < s.frame 23 →
        (∀ field : Fin 4, after.memory ((s.regions 4).base.toNat + 8 * field.val) =
          candidate.fields[field.val]?) ∧
        ∀ address, (∀ field : Fin 4, address ≠ (s.regions 4).base.toNat + 8 * field.val) →
          after.memory address = s.memory address := by
  obtain ⟨guards, a, b, c, d, rfl, rfl⟩ := lowerPlan_view lowered
  dsimp only
  rw [plan_run]
  obtain ⟨after, ran, memory, regions, frame, budget, spent⟩ :=
    guarded_publication s words inputs output guards a b c d
  have returnedStatus : (if (if guards.all (agrees words) then some (boardTuple (gatherWords words a b c d))
        else none).isNone then ExitStatus.refused
      else if s.frame 22 < s.frame 23 then .completed else .unsupported) =
        guardStatus s (guards.all (agrees words)) := by
    by_cases accepted : guards.all (agrees words) = true <;> simp [guardStatus, accepted]
  rw [returnedStatus]
  refine ⟨after, ran, regions, frame, budget, spent, fun stopped => by rw [memory, if_neg stopped], ?_⟩
  intro candidate present room
  have accepted : guards.all (agrees words) = true := by
    by_contra no
    simp [no] at present
  rw [if_pos accepted] at present
  have equal := Option.some.inj present
  subst candidate
  have completed : guardStatus s (guards.all (agrees words)) = .completed := by
    simp [guardStatus, accepted, room]
  rw [memory, if_pos completed]
  refine ⟨?_, writeRow_away s _⟩
  intro field
  rw [writeRow_at]
  fin_cases field <;> rfl

/-- The caller's observable result in terms of the original rule. -/
def ruleExecutionSpec (s : State) (words : Premises) (rule : RuleTable.Rule) (body : Stmt) : Prop :=
    let derives := RuleTable.Derives rule (premiseTuples words)
    ∃ status after, execute s body = .returned status status.word after ∧
      after.regions = s.regions ∧ after.frame = s.frame ∧ after.budget = s.budget ∧ after.spent = s.spent ∧
      (status = .refused ↔ ¬ ∃ candidate, derives candidate) ∧
      (status = .unsupported ↔ (∃ candidate, derives candidate) ∧ ¬ s.frame 22 < s.frame 23) ∧
      (status = .completed ↔ (∃ candidate, derives candidate) ∧ s.frame 22 < s.frame 23) ∧
      (status ≠ .completed → after.memory = s.memory) ∧
      ∀ candidate, derives candidate → s.frame 22 < s.frame 23 →
        (∀ field : Fin 4, after.memory ((s.regions 4).base.toNat + 8 * field.val) =
          candidate.fields[field.val]?) ∧
        ∀ address, (∀ field : Fin 4, address ≠ (s.regions 4).base.toNat + 8 * field.val) →
          after.memory address = s.memory address

theorem lowerCheckedRule_refines (s : State) (words : Premises) (inputs : ReadRows s words) (output : Output s)
    (rule : RuleTable.Rule) (plan : RuleTable.Plan) (body : Stmt)
    (checked : rule.checkPlan plan = true) (lowered : lowerPlan? plan = some body) :
    ruleExecutionSpec s words rule body := by
  unfold ruleExecutionSpec
  intro derives
  let proposed := plan.run (premiseTuples words)
  let status := if proposed.isNone then ExitStatus.refused
    else if s.frame 22 < s.frame 23 then ExitStatus.completed else ExitStatus.unsupported
  have correct (candidate : RuleTable.Tuple) : proposed = some candidate ↔ derives candidate :=
    RuleTable.Rule.checkPlan_correct rule plan checked (premiseTuples words) candidate
  have derivable : proposed.isNone = true ↔ ¬ ∃ candidate, derives candidate := by
    constructor
    · intro empty ⟨candidate, fact⟩
      simp [(correct candidate).mpr fact] at empty
    · intro empty
      cases result : proposed with
      | none => rfl
      | some candidate => exact False.elim (empty ⟨candidate, (correct candidate).mp result⟩)
  have hasDerivation : (∃ candidate, derives candidate) ↔ ¬ proposed.isNone = true := by
    rw [derivable, not_not]
  obtain ⟨after, ran, regions, frame, budget, spent, stopped, published⟩ :=
    lowerPlan_refines s words inputs output plan body lowered
  refine ⟨status, after, ran, regions, frame, budget, spent, ?_, ?_, ?_, stopped, ?_⟩
  · by_cases empty : proposed.isNone = true <;> by_cases room : s.frame 22 < s.frame 23 <;>
      simp [status, empty, room, hasDerivation]
  · by_cases empty : proposed.isNone = true <;> by_cases room : s.frame 22 < s.frame 23 <;>
      simp [status, empty, room, hasDerivation]
  · by_cases empty : proposed.isNone = true <;> by_cases room : s.frame 22 < s.frame 23 <;>
      simp [status, empty, room, hasDerivation]
  · exact fun candidate fact => published candidate ((correct candidate).mpr fact)

theorem theoryBody_admission {forms : List SExpr} {entry : String} {rule : RuleTable.Rule} {body : Stmt}
    (parsed : theoryRule? forms entry = some rule) (compiled : theoryBody? forms entry = some body) :
    let plan := (rule.compile rule.discoverOrigins).pruneSelfGuards
    rule.checkPlan plan = true ∧ lowerPlan? plan = some body := by
  simp only [theoryBody?, parsed, Option.bind_eq_bind, Option.bind_some] at compiled
  split at compiled
  next checked => exact ⟨checked, compiled⟩
  next => simp at compiled

theorem theory_sub1_admission : theorySub1Rule.checkPlan theorySub1Plan = true ∧
    lowerPlan? theorySub1Plan = some sub1.source.body :=
  theoryBody_admission (by kernel_reflexivity) theory_compiles_to_export

theorem theory_sub2_admission :
    let plan := (theorySub2Rule.compile theorySub2Rule.discoverOrigins).pruneSelfGuards
    theorySub2Rule.checkPlan plan = true ∧ lowerPlan? plan = some sub2.source.body :=
  theoryBody_admission (by kernel_reflexivity) theory_sub2_compiles_to_export

theorem theory_sub1_source_refinement (s : State) (words : Premises) (inputs : ReadRows s words)
    (output : Output s) : ruleExecutionSpec s words theorySub1Rule sub1.source.body :=
  lowerCheckedRule_refines s words inputs output _ _ _ theory_sub1_admission.1 theory_sub1_admission.2

theorem theory_sub2_source_refinement (s : State) (words : Premises) (inputs : ReadRows s words)
    (output : Output s) : ruleExecutionSpec s words theorySub2Rule sub2.source.body :=
  lowerCheckedRule_refines s words inputs output _ _ _ theory_sub2_admission.1 theory_sub2_admission.2

private theorem theory_sub1_plan : theorySub1Plan =
    ⟨boardInputs, Guards.map planGuard, 0, [(3, 0), (0, 1), (1, 0), (2, 0)].map planField⟩ := by
  kernel_reflexivity

private theorem theory_sub1_runs (words : Premises) : theorySub1Plan.run (premiseTuples words) =
    if Guards.all (agrees words) then some (boardTuple (conclusionWords words)) else none := by
  rw [theory_sub1_plan]
  exact plan_run words Guards (3, 0) (0, 1) (1, 0) (2, 0)

theorem wrong_tag_refused : lowerPlan? { theorySub1Plan with outputTag := 1 } = none := by
  kernel_reflexivity

theorem out_of_row_refused :
    lowerPlan? { theorySub1Plan with outputFields := [.field ⟨4, 0⟩, .field ⟨0, 1⟩, .field ⟨1, 0⟩,
      .field ⟨2, 0⟩] } = none := by
  kernel_reflexivity

open Mettapedia.Languages.Micromath (Claim Substitute1Guard substitute1?)

def claim (words : Premises) (row : Fin 4) : Claim :=
  ⟨(words row 0).toNat, (words row 1).toNat, (words row 2).toNat, (words row 3).toNat⟩

theorem checks_are_premises (words : Premises) :
    Guards.all (agrees words) = true ↔ Substitute1Guard (claim words 0) (claim words 1) (claim words 2) (claim words 3) := by
  have same (a b : Word) : a.toNat = b.toNat ↔ a = b := ⟨BitVec.eq_of_toNat_eq, congrArg BitVec.toNat⟩
  simp [Guards, agrees, claim, Substitute1Guard, same]

theorem theory_sub1_derives_iff (words : Premises) (candidate : RuleTable.Tuple) :
    RuleTable.Derives theorySub1Rule (premiseTuples words) candidate ↔
      Substitute1Guard (claim words 0) (claim words 1) (claim words 2) (claim words 3) ∧
      candidate = boardTuple (conclusionWords words) := by
  rw [← RuleTable.Rule.checkPlan_correct _ _ theory_sub1_admission.1, theory_sub1_runs, ← checks_are_premises]
  by_cases accepted : Guards.all (agrees words) = true <;> simp [accepted, eq_comm]

private def missingGuardWords (index : Fin 7) : Premises :=
  let guard := Guards[index.val]'(index.isLt)
  fun row field => if row = guard.leftRow ∧ field = guard.leftField then 1 else 0

theorem every_guard_is_needed (index : Fin 7) :
    let words := missingGuardWords index
    ((Guards.eraseIdx index.val).all (agrees words)) = true ∧
    substitute1? (claim words 0) (claim words 1) (claim words 2) (claim words 3) = none := by
  fin_cases index <;> constructor <;> kernel_reflexivity

theorem agreeing_example :
    let words : Premises := fun _ _ => 0
    substitute1? (claim words 0) (claim words 1) (claim words 2) (claim words 3) = some ⟨0, 0, 0, 0⟩ := by
  dsimp only
  kernel_reflexivity

theorem conclusionWords_readback (words : Premises) (conclusion : Claim)
    (checked : substitute1? (claim words 0) (claim words 1) (claim words 2) (claim words 3) = some conclusion)
    (field : Fin 4) :
    conclusionWords words field = BitVec.ofNat 64 (![conclusion.out, conclusion.f, conclusion.x, conclusion.y] field) := by
  unfold substitute1? at checked
  split at checked
  · cases checked
    fin_cases field <;> simp [conclusionWords, gatherWords, claim]
  · cases checked

def result (s : State) (words : Premises) : ExitStatus × Option Claim :=
  match substitute1? (claim words 0) (claim words 1) (claim words 2) (claim words 3) with
  | none => (.refused, none)
  | some proposed => if s.frame 22 < s.frame 23 then (.completed, some proposed) else (.unsupported, none)

def claimTuple (conclusion : Claim) : RuleTable.Tuple :=
  boardTuple fun field => BitVec.ofNat 64 (![conclusion.out, conclusion.f, conclusion.x, conclusion.y] field)

theorem result_theory_output (s : State) (words : Premises) (candidate : RuleTable.Tuple) :
    (result s words).2.map claimTuple = some candidate ↔
      s.frame 22 < s.frame 23 ∧ RuleTable.Derives theorySub1Rule (premiseTuples words) candidate := by
  rw [theory_sub1_derives_iff]
  by_cases valid : Substitute1Guard (claim words 0) (claim words 1) (claim words 2) (claim words 3)
  · let conclusion : Claim := ⟨(claim words 3).out, (claim words 0).f, (claim words 1).out, (claim words 2).out⟩
    have checked : substitute1? (claim words 0) (claim words 1) (claim words 2) (claim words 3) =
        some conclusion := by simp [substitute1?, valid, conclusion]
    have output : claimTuple conclusion = boardTuple (conclusionWords words) :=
      congrArg boardTuple (funext (conclusionWords_readback words conclusion checked)).symm
    by_cases room : s.frame 22 < s.frame 23 <;> simp [result, checked, room, valid, output, eq_comm]
  · simp [result, substitute1?, valid]

theorem source_refines_substitute1 (s : State) (words : Premises)
    (inputs : ReadRows s words) (output : Output s) :
    let expected := result s words
    ∃ after, execute s sub1.source.body = .returned expected.1 expected.1.word after ∧
      after.memory = (if expected.1 = .completed then outputMemory s words else s.memory) ∧
      after.regions = s.regions ∧ after.frame = s.frame ∧ after.budget = s.budget ∧ after.spent = s.spent := by
  dsimp only
  rw [exported_body]
  have status : (result s words).1 = guardStatus s (Guards.all (agrees words)) := by
    by_cases valid : Guards.all (agrees words) = true
    · have available := (checks_are_premises words).mp valid
      by_cases room : s.frame 22 < s.frame 23 <;> simp [result, substitute1?, available, guardStatus, valid, room]
    · have mismatch := mt (checks_are_premises words).mpr valid
      simp [result, substitute1?, mismatch, guardStatus, valid]
  rw [status]
  exact guarded_publication s words inputs output Guards (3, 0) (0, 1) (1, 0) (2, 0)

end Mettapedia.Machines.TIsa.P1Sub1Source

#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.exported_body
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_compiles_to_export
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_sub2_compiles_to_export
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.lowerPlan_refines
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.lowerCheckedRule_refines
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theoryBody_admission
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_sub1_admission
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_sub2_admission
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_sub1_source_refinement
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_sub2_source_refinement
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.theory_sub1_derives_iff
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.result_theory_output
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.source_refines_substitute1
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.outputMemory_away
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.conclusionWords_readback
#print axioms Mettapedia.Machines.TIsa.P1Sub1Source.every_guard_is_needed
