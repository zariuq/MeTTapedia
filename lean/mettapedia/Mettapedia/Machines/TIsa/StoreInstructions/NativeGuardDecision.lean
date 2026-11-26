import Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveTest
import Mettapedia.Machines.TIsa.StoreInstructions.SolverGuardTrichotomy

/-!
# One native solver classifies a normalized guard candidate

Failure returns impossible. Success reads the actual trail
count to distinguish possible from assured. This exit neither
decodes the full trail nor compares the term graphs again.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardDecision

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads footprint)
open X86PlacedScalar (Code CompareBranch)
open NativeArenaGeometry (Region)
open NativeTrailReserve (Descriptor)
open NativeBindingMemory (Geometry)
open NativeSolverResources (Budget)
open NativeSolverStep (Resident Writes Arrived)
open SolverGuardTrichotomy (Observation)
open NativeResolveTest (ReturnPlaced returnCode)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def word : Observation → Word
  | .impossible => 0
  | .possible => 1
  | .assured => 2

def countCode : List ℕ := X86DataLoad.code true 0 2 0
def countWire : NativeWords.Wiring := ⟨2, by decide, by decide, MemoryBinding.storeEncoding, 0, by decide, by decide⟩
def successCode (dst : Fin 16) (start next : ℕ) : List ℕ :=
  NativeTrailReserve.stackCode ++ (NativeTrailReserve.pointerCode ++ (countCode ++
    (NativeDecisions.compareBytes .equal 0 12 (start + 17) (start + 37) ++
      (returnCode dst 2 (start + 26) next ++ returnCode dst 1 (start + 37) next))))

theorem success_size (dst : Fin 16) (start next : ℕ) : (successCode dst start next).length = 48 := by
  simp only [successCode, List.length_append, NativeDecisions.compare_size, NativeResolveTest.return_size,
    show NativeTrailReserve.stackCode.length = 3 from rfl, show NativeTrailReserve.pointerCode.length = 7 from rfl,
    show countCode.length = 7 from rfl]

structure SuccessPlaced (image : NativeImage.View) (dst : Fin 16) (start next : ℕ) : Prop where
  extent : start + 48 ≤ image.size
  stack : Code image start NativeTrailReserve.stackCode
  pointer : Code image (start + 3) NativeTrailReserve.pointerCode
  count : Code image (start + 10) countCode
  check : CompareBranch image (start + 17) (start + 37) .equal 0 12
  certain : ReturnPlaced image dst 2 (start + 26) next
  possible : ReturnPlaced image dst 1 (start + 37) next

theorem success_placed (image : NativeImage.View) (dst : Fin 16) (start next : ℕ)
    (extent : start + 48 ≤ image.size) (target : next ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (successCode dst start next)) : SuccessPlaced image dst start next := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (NativeTrailReserve.stackCode ++ _) from code)
  obtain ⟨pointer, rest⟩ := NativeWords.code_append rest
  obtain ⟨count, rest⟩ := NativeWords.code_append rest
  change Code image (start + 17) _ at rest
  obtain ⟨compare, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨certain, possible⟩ := NativeWords.code_append rest
  rw [NativeResolveTest.return_size] at possible
  exact ⟨extent, stack, pointer, count, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) (by omega) short compare,
    NativeResolveTest.return_placed image _ _ _ _ (by omega) target short certain,
    NativeResolveTest.return_placed image _ _ _ _ (by omega) target short possible⟩

def exits (start exhausted malformed : ℕ) : NativeSolverImage.Exits :=
  ⟨NativeSolverImage.finish start, NativeSolverImage.finish start + 48, NativeSolverImage.finish start + 48, exhausted, malformed⟩

def emit (dst : Fin 16) (start next exhausted malformed : ℕ) : List ℕ :=
  NativeSolverImage.emit start (exits start exhausted malformed) ++
    (successCode dst (NativeSolverImage.finish start) next ++ returnCode dst 0 (NativeSolverImage.finish start + 48) next)

structure Placed (image : NativeImage.View) (dst : Fin 16) (start next exhausted malformed : ℕ) : Prop where
  solver : NativeSolverImage.Placed image start (exits start exhausted malformed)
  yes : SuccessPlaced image dst (NativeSolverImage.finish start) next
  no : ReturnPlaced image dst 0 (NativeSolverImage.finish start + 48) next

theorem placed_of_emitted (image : NativeImage.View) (dst : Fin 16) (start next exhausted malformed : ℕ)
    (extent : NativeSolverImage.finish start + 59 ≤ image.size) (target : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit dst start next exhausted malformed)) : Placed image dst start next exhausted malformed := by
  obtain ⟨body, rest⟩ := NativeWords.code_append
    (show Code image start (NativeSolverImage.emit start (exits start exhausted malformed) ++ _) from code)
  rw [NativeSolverImage.emit_size] at rest
  obtain ⟨yes, no⟩ := NativeWords.code_append rest
  rw [success_size] at no
  exact ⟨NativeSolverImage.placed_of_emitted image _ _ (by omega)
    ⟨by change NativeSolverImage.finish start ≤ image.size; omega,
      by change NativeSolverImage.finish start + 48 ≤ image.size; omega,
      by change NativeSolverImage.finish start + 48 ≤ image.size; omega, lack, bad⟩ short body,
    success_placed image _ _ _ (by omega) target short yes, NativeResolveTest.return_placed image _ _ _ _ (by omega) target short no⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
def replyClobbers (dst : Fin 16) : Finset Register := {.rax, .rdx, .rsi, .rflags, .rip} ∪ NativeResolveTest.returnClobbers dst
def clobbers (dst : Fin 16) : Finset Register := NativeSolverStep.clobbers ∪ replyClobbers dst

theorem fetched_success (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next : ℕ} {before : Native}
    (dst : Fin 16) (code : SuccessPlaced image dst start next) (point : At image before base start) (controls : Controls before)
    {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {records : PackedEquations.Arena}
    (frame : Descriptor) (stack : lookup before 4 = some frame.pointer)
    (trailPtr : Reads before (frame.cell 7).address layout.words.pointer) (zero : lookup before 12 = some 0)
    (ready : NativeAgendaRecords.Ready layout records before) (history : PackedWorklist.Words)
    (known : PackedEquations.readWords records (NativeBindingTrail.root records) = some history) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run before = .ok () after ∧
      X86StateFrame.Frame (replyClobbers dst) ∅ before after ∧
      lookup after dst = some (word (if history = [] then .assured else .possible)) ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  obtain ⟨a, moved, move, stackKnown, ⟨atPointer⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack code.stack
  have stackFrame := X86StateFrame.registerOnly move
  obtain ⟨b, followed, followedFrame, trailBase, ⟨atCount⟩⟩ := (NativeAgendaRead.fieldSource frame 7).fetch
    (handlers other extra) vector NativeTrailReserve.pointerWire layout.words.pointer atPointer
    (controls.transport stackFrame (by decide)) stackKnown (trailPtr.preserved stackFrame (by simp))
    (show start + 10 ≤ image.size by omega) code.pointer
  have afterPointer := stackFrame.trans followedFrame
  obtain ⟨c, read, countFrame, size, ⟨atCheck⟩⟩ := (NativeAgendaRead.fieldSource layout.header 0).fetch
    (handlers other extra) vector countWire (NativeBindingTrail.root records)
    (show At image b base (start + 10) from atCount) (controls.transport afterPointer (by decide))
    (layout.header_pointer.symm ▸ trailBase) (ready.count.preserved afterPointer (by simp))
    (show start + 17 ≤ image.size by omega) code.count
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at followed read
  have beforeCheck := afterPointer.trans countFrame
  obtain ⟨d, compared, compareFrame, ⟨branch⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 17) from atCheck) .equal 0 12 code.check _ _ size
    ((beforeCheck.lookup 12 (by decide)).trans zero)
  have empty := SolverGuardTrichotomy.packed_trail_empty_iff_zero records history known
  simp only [Comparison.evaluate, beq_iff_eq, ← empty] at branch
  have route := beforeCheck.trans (X86StateFrame.registerOnly compareFrame)
  have counted := X86FuelPrefix.fetches_then 3 2 before c d
    (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b moved followed) read) compared
  have finishTag (literal : BitVec 32) (position : ℕ) (arrival : At image d base position)
      (returnCode : ReturnPlaced image dst literal position next) :
      ∃ after, (X86FuelPrefix.fetches 7).run before = .ok () after ∧ X86StateFrame.Frame (replyClobbers dst) ∅ before after ∧
        lookup after dst = some (literal.zeroExtend 64) ∧ Nonempty (At image after base next) := by
    obtain ⟨after, ran, returned, tag, endpoint⟩ := NativeResolveTest.fetched_return other extra vector arrival dst literal returnCode
    have exactFrame : X86StateFrame.Frame ({.rax, .rdx, .rsi, .rflags, .rip} : Finset Register) ∅ before d :=
      route.mono (by decide) (by simp)
    exact ⟨after, X86FuelPrefix.fetches_then 5 2 before d after counted ran,
      (exactFrame.trans returned).mono (Finset.Subset.refl _) (by simp), tag, endpoint⟩
  by_cases isEmpty : history = []
  · rw [if_pos isEmpty] at branch ⊢
    exact finishTag 2 _ branch code.certain
  · rw [if_neg isEmpty] at branch ⊢
    exact finishTag 1 _ branch code.possible

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

private theorem trail_ptr_apart (space : Geometry term map frame agenda trail image base) {bytes : Finset ℕ}
    (writes : Writes term map frame agenda trail bytes) : Disjoint (footprint (frame.cell 7).address) bytes := by
  induction writes with
  | idle => simp
  | graph privateWrites => exact space.trailPointer_apart privateWrites
  | pending staged => exact NativePendingFill.Within.separate staged _ (fun i j _ _ =>
      NativeBindingMemory.frame_record space.agendaFrame 7 i j)
  | binding staged => exact NativePendingFill.Within.separate staged _ (fun i j _ _ =>
      NativeBindingMemory.frame_record space.trailFrame 7 i j)
  | header => exact NativeBindingMemory.frame_header space.agendaFrame 7
  | trailHeader => exact NativeBindingMemory.frame_header space.trailFrame 7
  | headers => exact space.publishGeometry.frame 7
  | union _ _ left right => exact Finset.disjoint_union_right.mpr ⟨left, right⟩

universe u p
variable {σ : LPSignature.{u,u,p,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem decoded_trail_empty (symbols : UnifierHeaders.Symbols σ) (terms : PackedTerms.Arena)
    (history : PackedWorklist.Words) (decoded : Derivation.FiniteUnifier.Trail σ)
    (read : PackedWorklist.readTrail symbols terms history = some decoded) : history = [] ↔ decoded = [] := by
  cases history with
  | nil => obtain rfl := Option.some.inj read; simp
  | cons head tail =>
    unfold PackedWorklist.readTrail at read
    rw [List.mapM_cons] at read
    obtain ⟨first, _, rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨carried, _, result⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := Option.some.inj (show some (first :: carried) = some decoded from result)
    simp

/-- This classifies one normalized pair using one fetched
solver run. A later scan can use the same returned class for
presence, absence and exact count. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start next exhausted malformed : ℕ} {before : Native}
    (dst : Fin 16) (code : Placed image dst start next exhausted malformed)
    (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail image base)
    (symbols : UnifierHeaders.Symbols σ) (terms : PackedTerms.Arena) (left right : Word) (l r : Term σ)
    (seed : Resident term map frame agenda trail ⟨terms, [(left, right)], []⟩ before)
    (leftRead : PackedTerms.lookup symbols terms left = some l) (rightRead : PackedTerms.lookup symbols terms right = some r)
    (fuel : ℕ) (wordBudget : PackedWorklist.Reserve fuel terms.nodes.size terms.children.size)
    (need : Budget) (plan : NativeSolverResources.planned fuel seed.equations.size seed.bindings.size
      (.working ⟨terms, [(left, right)], []⟩) = some need)
    (available : need.Within ⟨nc, ec, mc, ac, tc⟩) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers dst) bytes before after ∧ Writes term map frame agenda trail bytes ∧
      lookup after dst = some (word (SolverGuardTrichotomy.specification l r)) ∧
      NativeTermArena.Ready term terms after ∧ (dst ≠ 13 → lookup after 13 = some 1) ∧
      Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let work : PackedWorklist.Worklist := ⟨terms, [(left, right)], []⟩
  have decoded : PackedWorklist.read symbols (.working work) = some (Derivation.FiniteUnifier.start [(l, r)]) := by
    simp [work, PackedWorklist.read, PackedWorklist.readEquations, PackedWorklist.readTrail, PackedUnifierAction.pair,
      List.mapM_cons, leftRead, rightRead, Derivation.FiniteUnifier.start]
  have fits := NativeSolverResources.fitted symbols fuel seed.equations.size seed.bindings.size _ _ decoded wordBudget
    need ⟨nc, ec, mc, ac, tc⟩ plan available
  have input : Arrived term map frame agenda trail image base start (exits start exhausted malformed)
    seed.equations.size seed.bindings.size before (.working work) := ⟨seed, rfl, rfl, ⟨point⟩⟩
  obtain ⟨mid, count, bytes, _, _, outcome, ran, terminal, native, framed, effects, retained, one, arrived⟩ :=
    NativeSolverRun.fetched other extra vector code.solver space symbols fits input controls
  obtain ⟨observed, reference, read⟩ := PackedWorklist.run_exact symbols fuel (.working work) _ decoded wordBudget
  obtain rfl := Option.some.inj (reference.symm.trans ran)
  have finished := (PackedWorklist.terminal_read symbols observed _ read).symm.trans terminal
  have equality := SolverGuardTrichotomy.observe_finished fuel l r finished
  have controlsMid := controls.transport framed NativeSolverStep.clobbers_data
  have notReturn (different : dst ≠ 13) : key (13 : Fin 16) ∉ NativeResolveTest.returnClobbers dst := by
    simp only [NativeResolveTest.returnClobbers, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun e => different (key_injective e.symm), by decide⟩
  cases observed with
  | working work => cases terminal
  | inconsistent reason =>
    rw [← Option.some.inj read] at equality
    have tag : .impossible = SolverGuardTrichotomy.specification l r := Option.some.inj equality
    obtain ⟨atNo⟩ := arrived
    have no : At image mid base (NativeSolverImage.finish start + 48) := by cases reason <;> exact atNo
    obtain ⟨after, done, tailFrame, result, endpoint⟩ := NativeResolveTest.fetched_return other extra vector no dst 0 code.no
    refine ⟨after, count + 2, bytes, X86FuelPrefix.fetches_then count 2 before mid after native done,
      (framed.trans tailFrame).mono (by simp [clobbers, replyClobbers]) (by simp), effects, ?_,
      (retained terms rfl).preserved tailFrame,
      fun different => (tailFrame.lookup 13 (notReturn different)).trans (one.trans seed.live.dispatch.one), endpoint⟩
    rw [← tag]
    exact result
  | solved newTerms history =>
    obtain ⟨packed, _, ready, held, _, _, _, _, ⟨atYes⟩⟩ := arrived
    obtain ⟨decodedTrail, termRead, selected⟩ := Option.map_eq_some_iff.mp read
    rw [← selected] at equality
    have tag : (if history = [] then Observation.assured else Observation.possible) = SolverGuardTrichotomy.specification l r := by
      have known := decoded_trail_empty symbols newTerms history decodedTrail termRead
      cases decodedTrail with
      | nil =>
        rw [if_pos (known.mpr rfl)]
        exact Option.some.inj equality
      | cons first rest =>
        rw [if_neg (fun empty => List.cons_ne_nil _ _ (known.mp empty))]
        exact Option.some.inj equality
    have stack := frame.substitution_pointer ▸ seed.live.staged.pointer
    obtain ⟨after, done, tailFrame, result, endpoint⟩ := fetched_success other extra vector dst code.yes atYes controlsMid
      frame ((framed.lookup 4 (by decide)).trans stack)
      (seed.live.aux.trailPtr.preserved framed (trail_ptr_apart space effects))
      ((framed.lookup 12 (by decide)).trans seed.live.dispatch.zero) ready history held
    exact ⟨after, count + 7, bytes, X86FuelPrefix.fetches_then count 7 before mid after native done,
      (framed.trans tailFrame).mono (Finset.Subset.refl _) (by simp), effects, tag ▸ result,
      (retained terms rfl).preserved tailFrame, fun different =>
        (tailFrame.lookup 13 (by
          simp only [replyClobbers, Finset.mem_union, not_or]
          exact ⟨by decide, notReturn different⟩)).trans (one.trans seed.live.dispatch.one), endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardDecision
