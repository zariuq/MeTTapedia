import Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveReserve
import Mettapedia.Machines.TIsa.StoreInstructions.NativeResolveTest

/-!
# Preparing the native resolution agenda from two held chains

Both input chains use the newest-first packed representation.
The local chain is reversed into an empty suffix; the reversed
base is pushed on top of that. The result is therefore exactly
the base in its original order followed by the local equations
in issuance order. Their source chains never change.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeResolvePrepare

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads footprint)
open X86PlacedScalar (Code registerCode)
open NativeBindingMemory (Geometry)
open NativeBindingStep (Live)
open NativeSolverStep (Resident Writes)
open NativeTrailReserve (Descriptor)
open NativeArenaGeometry (Region)
open NativeAgendaLoop (Within)
open PackedWorklist (Words)
open PackedEquations (Arena readWords)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def baseCode : List ℕ := registerCode 0x89 7 11
def rootCode : List ℕ := registerCode 0x89 0 11
def termCode : List ℕ := X86DataLoad.code true 3 6 16
def termWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 3, by decide, by decide⟩

def emit (start next exhausted malformed : ℕ) : List ℕ :=
  NativeResolveReserve.emit start exhausted malformed ++
    (NativeEquationReverse.emit (start + 196) (start + 332) malformed ++
      (baseCode ++ (NativeEquationReverse.emit (start + 335) (start + 471) malformed ++
        (rootCode ++ (NativeTrailReserve.stackCode ++ (termCode ++ NativeAgendaPublish.emit (start + 484) next))))))

theorem emit_size (start next exhausted malformed : ℕ) : (emit start next exhausted malformed).length = 505 := by
  simp only [emit, List.length_append, NativeResolveReserve.emit_size, NativeEquationReverse.emit_size,
    NativeAgendaPublish.emit_size, show baseCode.length = 3 from rfl, show rootCode.length = 3 from rfl,
    show NativeTrailReserve.stackCode.length = 3 from rfl, show termCode.length = 7 from rfl]

structure Placed (image : NativeImage.View) (start next exhausted malformed : ℕ) : Prop where
  extent : start + 505 ≤ image.size
  reserve : NativeResolveReserve.Placed image start exhausted malformed
  newer : NativeEquationReverse.Placed image (start + 196) (start + 332) malformed
  base : Code image (start + 332) baseCode
  older : NativeEquationReverse.Placed image (start + 335) (start + 471) malformed
  root : Code image (start + 471) rootCode
  stack : Code image (start + 474) NativeTrailReserve.stackCode
  terms : Code image (start + 477) termCode
  publish : NativeAgendaPublish.Placed image (start + 484) next

theorem placed_of_emitted (image : NativeImage.View) (start next exhausted malformed : ℕ)
    (extent : start + 505 ≤ image.size) (finish : next ≤ image.size)
    (lack : exhausted ≤ image.size) (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start next exhausted malformed)) : Placed image start next exhausted malformed := by
  obtain ⟨reserve, rest⟩ := NativeWords.code_append (show Code image start (NativeResolveReserve.emit start exhausted malformed ++ _) from code)
  rw [NativeResolveReserve.emit_size] at rest
  obtain ⟨newer, rest⟩ := NativeWords.code_append rest
  rw [NativeEquationReverse.emit_size] at rest
  obtain ⟨base, rest⟩ := NativeWords.code_append rest
  obtain ⟨older, rest⟩ := NativeWords.code_append rest
  rw [NativeEquationReverse.emit_size] at rest
  obtain ⟨root, rest⟩ := NativeWords.code_append rest
  obtain ⟨stack, rest⟩ := NativeWords.code_append rest
  obtain ⟨terms, publish⟩ := NativeWords.code_append rest
  exact ⟨extent, NativeResolveReserve.placed_of_emitted image _ _ _ (by omega) lack bad short reserve,
    NativeEquationReverse.placed_of_emitted image _ _ _ (by omega) (by omega) bad short newer, base,
    NativeEquationReverse.placed_of_emitted image _ _ _ (by omega) (by omega) bad short older, root, stack, terms,
    NativeAgendaPublish.placed_of_emitted image _ _ (by omega) finish short publish⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := NativeResolveReserve.clobbers ∪ NativeEquationReverse.clobbers
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Descriptor}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}

private theorem retained_reads {old new : Arena} {tail head : Word} {inserted history : Words}
    (done : PackedEquations.prependWords old tail inserted = some (new, head))
    (known : readWords old tail = some history) (within : old.size + inserted.length < 2 ^ 64) :
    ∀ earlier, earlier.toNat ≤ old.size → readWords new earlier = readWords old earlier := by
  obtain ⟨saved, root, built, _, _, _, keep⟩ := PackedEquations.prepend_words_exact old tail inserted history known
    (PackedEquations.read_bound PackedEquations.wordCodes old tail known) within
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (done.symm.trans built))
  exact keep

/-- Run the physical preparation, or branch with no stores
when the combined suffix does not fit. The success exit is a
resident starting state of the packed resolution TEST. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next exhausted malformed : ℕ} {before : Native}
    (code : Placed image start next exhausted malformed) (point : At image before base start) (controls : Controls before)
    (space : Geometry term map frame agenda trail image base)
    (terms : PackedTerms.Arena) (source oldTrail : Arena) (newerRoot baseRoot : Word) (newer originalBase : Words)
    (live : Live term map frame agenda trail terms source newerRoot oldTrail before)
    (older : lookup before 7 = some baseRoot)
    (localChain : readWords source newerRoot = some newer) (baseChain : readWords source baseRoot = some originalBase.reverse)
    (emptyTrail : readWords oldTrail (NativeBindingTrail.root oldTrail) = some []) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers bytes before after ∧ Writes term map frame agenda trail bytes ∧
      if source.size + (newer.length + originalBase.length) ≤ ac then
        ∃ seed : Resident term map frame agenda trail ⟨terms, originalBase ++ newer.reverse, []⟩ after,
          seed.equations.size = source.size + (newer.length + originalBase.length) ∧ seed.bindings = oldTrail ∧
          (∀ earlier, earlier.toNat ≤ source.size → readWords seed.equations earlier = readWords source earlier) ∧
          PackedResolution.preparePacked terms source newerRoot originalBase =
            some (.working ⟨terms, originalBase ++ newer.reverse, []⟩) ∧ Nonempty (At image after base next)
      else bytes = ∅ ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  have input : NativeResolveReserve.Input agenda source newerRoot baseRoot before :=
    ⟨live.dispatch.agendaReady, live.dispatch.agendaBase, live.aux.agendaLimit, live.dispatch.cursor, older,
      live.dispatch.zero, live.dispatch.one⟩
  obtain ⟨a, first, planned, planFrame, _, baseKnown, reserve⟩ :=
    NativeResolveReserve.fetched other extra vector point controls code.reserve newerRoot baseRoot newer originalBase.reverse
      input localChain baseChain
  rw [List.length_reverse] at reserve
  by_cases fits : source.size + (newer.length + originalBase.length) ≤ ac
  · rw [if_pos fits] at reserve
    obtain ⟨_, init, ⟨atCopy⟩⟩ := reserve
    obtain ⟨b, mid, accumulated, firstBytes, copied, copyFrame, localOnly, accumulate, midSize, localBuilt, localRead, ⟨atBase⟩⟩ :=
      NativeEquationReverse.fetched_all other extra vector code.newer space.agendaCode source source newerRoot 0 newer []
        atCopy (controls.transport planFrame NativeResolveReserve.clobbers_data) init localChain rfl (Nat.le_refl _) (by omega)
    have firstRead : readWords mid accumulated = some newer.reverse := by simpa only [List.append_nil] using localRead
    obtain ⟨c, selected, selectFrame, atOlder, ⟨atSecond⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector atBase (by omega) 7 11 baseRoot ((copyFrame.lookup 7 (by decide)).trans baseKnown) code.base
    have selecting := X86StateFrame.registerOnly selectFrame
    have baseInput : NativeEquationReverse.Input agenda source mid baseRoot accumulated c :=
      ⟨accumulate.source.preserved selecting,
        ⟨accumulate.records.fits, fun i j => (accumulate.records.node i j).preserved selecting (by simp)⟩,
        (selectFrame.lookup 5 (by decide)).trans accumulate.base, atOlder,
        (selectFrame.lookup 14 (by decide)).trans accumulate.length, (selectFrame.lookup 0 (by decide)).trans accumulate.accumulated,
        (selectFrame.lookup 12 (by decide)).trans accumulate.zero, (selectFrame.lookup 13 (by decide)).trans accumulate.one⟩
    have throughSelect := (planFrame.trans copyFrame).trans selecting
    obtain ⟨d, out, root, more, admitted, addedFrame, olderOnly, staged, finalSize, merged, readyRead, ⟨atRoot⟩⟩ :=
      NativeEquationReverse.fetched_all other extra vector code.older space.agendaCode source mid baseRoot accumulated
        originalBase.reverse newer.reverse (show At image c base (start + 335) from atSecond)
        (controls.transport throughSelect (by decide)) baseInput baseChain firstRead (by omega)
        (by rw [List.length_reverse]; omega)
    have outSize : out.size = source.size + (newer.length + originalBase.length) := by
      rw [List.length_reverse] at finalSize
      omega
    have privateWrites : Within agenda source.size out.size (firstBytes ∪ more) := by
      intro byte changed
      rcases Finset.mem_union.mp changed with sourceWrite | inherited
      · obtain ⟨i, col, lower, upper, now⟩ := localOnly byte sourceWrite
        exact ⟨i, col, lower, by omega, now⟩
      · obtain ⟨i, col, lower, upper, now⟩ := olderOnly byte inherited
        exact ⟨i, col, by omega, upper, now⟩
    have throughCopy : X86StateFrame.Frame clobbers (firstBytes ∪ more) before d :=
      (throughSelect.trans addedFrame).mono (by decide) (by simp)
    have keptStack := NativeBindingMemory.keep_staged space.agendaFrame privateWrites throughCopy (by decide) live.staged
    have stackKnown : lookup d 4 = some frame.pointer := frame.substitution_pointer ▸ keptStack.pointer
    have savedAux := live.aux.throughAgenda space throughCopy privateWrites
    obtain ⟨e, rooted, rootFrame, rootKnown, ⟨atStack⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector atRoot (by omega) 0 11 root staged.accumulated code.root
    obtain ⟨f, stacked, stackFrame, pointer, ⟨atTerms⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector (show At image e base (start + 474) from atStack)
      (by omega) 4 6 frame.pointer ((rootFrame.lookup 4 (by decide)).trans stackKnown) code.stack
    have localFinish := X86StateFrame.registerOnly (rootFrame.trans stackFrame)
    have beforeTerms := throughCopy.trans localFinish
    have termWord : Reads d (frame.cell 2).address term.nodes.pointer := by
      have slot := keptStack.word 2
      rw [frame.substitution_cell] at slot
      exact slot
    obtain ⟨g, termBase, loaded, termRegister, ⟨atPublish⟩⟩ := (NativeAgendaRead.fieldSource frame 2).fetch
      (handlers other extra) vector termWire term.nodes.pointer (show At image f base (start + 477) from atTerms)
      (controls.transport beforeTerms (by decide)) pointer (termWord.preserved localFinish (by simp))
      (show start + 484 ≤ image.size by omega) code.terms
    have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
    rw [linked] at termBase
    have beforePublish := localFinish.trans loaded
    have finalRecords : NativeAgendaRecords.Records agenda out g :=
      ⟨staged.records.fits, fun i j => (staged.records.node i j).preserved beforePublish (by simp)⟩
    obtain ⟨after, ended, published, ready, tagTwo, endpoint⟩ :=
      NativeAgendaPublish.fetched other extra vector (show At image g base (start + 484) from atPublish)
        (controls.transport (throughCopy.trans beforePublish) (by decide)) code.publish finalRecords
        ((beforePublish.lookup 5 (by decide)).trans staged.base) ((beforePublish.lookup 14 (by decide)).trans staged.length)
        space.agendaHeader
    let header := NativeBindingPublish.header agenda
    have all : X86StateFrame.Frame clobbers (firstBytes ∪ more ∪ header) before after :=
      ((throughCopy.trans beforePublish).trans published).mono (by decide) (by
        simp only [Finset.union_empty, header, NativeBindingPublish.header]
        exact Finset.Subset.refl _)
    have afterStaged := beforePublish.trans published
    have writeOut : X86StateFrame.Frame (NativeAgendaPublish.clobbers ∪ NativeWords.touched termWire ∪
        ({.r11, .rsi, .rip} : Finset Register)) header d after :=
      afterStaged.mono (by decide) (by simp [header, NativeBindingPublish.header])
    have keptTerms := NativeBindingMemory.keep_terms space.substitute.agendaNode space.substitute.agendaEdge
      privateWrites throughCopy live.dispatch.termReady
    have protectedTerms := keptTerms.kept writeOut
      (fun i j => (Finset.disjoint_union_right.mp (space.publishGeometry.node i j)).2)
      (fun i => (Finset.disjoint_union_right.mp (space.publishGeometry.edge i)).2)
    have dispatch : NativeAgendaDispatch.Context agenda term out terms root after :=
      ⟨ready, protectedTerms, (all.lookup 5 (by decide)).trans live.dispatch.agendaBase,
        (published.lookup 3 (by decide)).trans termRegister,
        (((X86StateFrame.registerOnly stackFrame).trans loaded).trans published).lookup 11 (by decide) |>.trans rootKnown,
        (all.lookup 15 (by decide)).trans live.dispatch.termCount,
        (all.lookup 12 (by decide)).trans live.dispatch.zero, (all.lookup 13 (by decide)).trans live.dispatch.one, tagTwo⟩
    have protectedTrail := NativeBindingMemory.keep_ready space.trailAgenda privateWrites throughCopy live.trailReady
    have bindings : NativeAgendaRecords.Ready trail oldTrail after :=
      ⟨protectedTrail.fits, protectedTrail.count.preserved writeOut (NativeBindingMemory.header_apart space.trailAgenda),
        fun i j => (protectedTrail.node i j).preserved writeOut (NativeBindingMemory.record_header_apart space.trailAgenda _ j)⟩
    have frameReady := keptStack.kept writeOut (by decide) (fun j => by
      rw [frame.substitution_cell]
      exact NativeBindingMemory.frame_header space.agendaFrame _)
    have newLive : Live term map frame agenda trail terms out root oldTrail after :=
      ⟨dispatch, frameReady, bindings, savedAux.publishAgenda space writeOut⟩
    let seed : Resident term map frame agenda trail ⟨terms, originalBase ++ newer.reverse, []⟩ after :=
      ⟨out, oldTrail, root, newLive, by simpa only [List.reverse_reverse] using readyRead, emptyTrail⟩
    have dataBound := agenda.words.positive_room (show 0 < 3 * (ac + 1) by omega)
    have originalKept := retained_reads localBuilt (by rfl : readWords source 0 = some [])
      (by rw [List.length_reverse]; omega)
    have olderKept := retained_reads merged firstRead (by rw [List.reverse_reverse]; omega)
    have throughSecond := X86FuelPrefix.fetches_then _ _ before c d
      (X86FuelPrefix.fetches_then _ 1 before b c
        (X86FuelPrefix.fetches_then first _ before a b planned copied) selected) admitted
    have footer := X86FuelPrefix.fetches_then _ 4 before g after
      (X86FuelPrefix.fetches_then _ 1 before f g
        (X86FuelPrefix.fetches_then _ 1 before e f
          (X86FuelPrefix.fetches_then _ 1 before d e throughSecond rooted) stacked) termBase) ended
    refine ⟨after, _, _, footer, all, .union (.pending privateWrites) .header, ?_⟩
    rw [if_pos fits]
    refine ⟨seed, ?_, ?_, ?_, by simp [PackedResolution.preparePacked, localChain], endpoint⟩
    · change out.size = _
      exact outSize
    · rfl
    · intro earlier inside
      change readWords out earlier = readWords source earlier
      exact (olderKept earlier (by omega)).trans (originalKept earlier inside)
  · rw [if_neg fits] at reserve
    refine ⟨a, first, ∅, planned, planFrame.mono (by simp) (Finset.Subset.refl _), .idle, ?_⟩
    rw [if_neg fits]
    exact ⟨rfl, reserve.2⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeResolvePrepare
